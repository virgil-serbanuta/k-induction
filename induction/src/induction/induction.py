from __future__ import annotations

import subprocess
import sys
from pathlib import Path
from typing import TYPE_CHECKING, List, Tuple

from pyk.cterm import CTermSymbolic
from pyk.kast.att import _NONE, AttKey, Atts, KAtt
from pyk.kast.inner import KApply, KToken, KVariable, bottom_up
from pyk.kast.outer import KClaim, KDefinition, KFlatModule, KImport, KProduction, KRequire, KRule, KTerminal
from pyk.kcfg.explore import KCFGExplore
from pyk.kcfg.kcfg import KCFG
from pyk.kore.rpc import KoreClient, kore_server
from pyk.ktool.kompile import KompileBackend, kompile
from pyk.ktool.kprint import KPrint
from pyk.ktool.kprove import KProve
from pyk.prelude.kbool import andBool, notBool
from pyk.prelude.kint import INT, intToken
from pyk.prelude.ml import mlEqualsTrue
from pyk.prelude.string import pretty_string
from pyk.proof.reachability import APRProof, APRProver
from pyk.utils import BugReport

if TYPE_CHECKING:
    from pyk.kast.inner import KInner
    from pyk.kore.rpc import LogEntry
    from pyk.ktool.kprint import SymbolTable


ROOT = Path(subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).decode().strip())
K_DIR = ROOT / 'induction' / 'k-src'
K_SOURCE = K_DIR / 'imp.md'
K_SPEC = K_DIR / 'sum-to-n-spec.k'
BUILD_DIR = ROOT / '.build'
DEFINITION_PARENT = BUILD_DIR / 'definition'
DEFINITION_DIR = DEFINITION_PARENT / 'imp-kompiled'
NEW_SEMANTICS_NAME = 'induction-rules'
INDUCTION_DEFINITION_FILE = f'{NEW_SEMANTICS_NAME}.k'
WORK_DIR = BUILD_DIR / 'work'
BUG_REPORT_PATH = BUILD_DIR / 'bug-report'


DEBUG_SERVER = False
BUG_REPORT = True


def patch_symbol_table(symbol_table: SymbolTable) -> None:
    symbol_table['_|->_'] = lambda c1, c2: f'({c1} |-> {c2})'
    symbol_table['_Map_'] = lambda c1, c2: f'({c1} {c2})'

    symbol_table['notBool_'] = lambda c1: f'notBool ({c1})'
    symbol_table['_andBool_'] = lambda c1, c2: f'({c1}) andBool ({c2})'
    symbol_table['_orBool_'] = lambda c1, c2: f'({c1}) orBool ({c2})'
    symbol_table['_andThenBool_'] = lambda c1, c2: f'({c1}) andThenBool ({c2})'
    symbol_table['_xorBool_'] = lambda c1, c2: f'({c1}) xorBool ({c2})'
    symbol_table['_orElseBool_'] = lambda c1, c2: f'({c1}) orElseBool ({c2})'
    symbol_table['_impliesBool_'] = lambda c1, c2: f'({c1}) impliesBool ({c2})'

    symbol_table['~Int_'] = lambda c1: f'~Int ({c1})'
    symbol_table['_modInt_'] = lambda c1, c2: f'({c1}) modInt ({c2})'
    symbol_table['_*Int_'] = lambda c1, c2: f'({c1}) *Int ({c2})'
    symbol_table['_/Int_'] = lambda c1, c2: f'({c1}) /Int ({c2})'
    symbol_table['_%Int_'] = lambda c1, c2: f'({c1}) %Int ({c2})'
    symbol_table['_^Int_'] = lambda c1, c2: f'({c1}) ^Int ({c2})'
    symbol_table['_^%Int_'] = lambda c1, c2: f'({c1}) ^%Int ({c2})'
    symbol_table['_+Int_'] = lambda c1, c2: f'({c1}) +Int ({c2})'
    symbol_table['_-Int_'] = lambda c1, c2: f'({c1}) -Int ({c2})'
    symbol_table['_>>Int_'] = lambda c1, c2: f'({c1}) >>Int ({c2})'
    symbol_table['_<<Int_'] = lambda c1, c2: f'({c1}) <<Int ({c2})'
    symbol_table['_&Int_'] = lambda c1, c2: f'({c1}) &Int ({c2})'
    symbol_table['_xorInt_'] = lambda c1, c2: f'({c1}) xorInt ({c2})'
    symbol_table['_|Int_'] = lambda c1, c2: f'({c1}) |Int ({c2})'


def kompile_semantics() -> None:
    print('Kompiling...', flush=True)
    _ = kompile(
        K_SOURCE,
        output_dir=DEFINITION_DIR,
        backend=KompileBackend.HASKELL,
        main_module='IMP',
        syntax_module='IMP-SYNTAX',
        md_selector='k',
    )
    print('Kompile done.', flush=True)


def create_kprove(definition_dir: Path) -> KProve:
    print('Loading the definition...', flush=True)
    kprove = KProve(definition_dir, bug_report=None)
    print('Done loading.', flush=True)
    return kprove


def create_printer(definition_dir: Path) -> KPrint:
    print('Loading the definition...', flush=True)
    kprint = KPrint(definition_dir, bug_report=None, patch_symbol_table=patch_symbol_table)
    print('Done loading.', flush=True)
    return kprint


def load_claims(kprove: KProve) -> List[KClaim]:
    claims = kprove.get_claims(K_SPEC)
    return claims


def replace_var(term: KInner, var_name: str, replacement: KInner) -> KInner:
    def replace(term_: KInner) -> KInner:
        if type(term_) is KVariable and term_.name == var_name:
            return replacement
        return term_

    return bottom_up(replace, term)


def find_decreases(root: KInner) -> tuple[str, str, str]:
    result: tuple[str, str, str] | None = None

    def finder(node: KInner) -> KInner:
        if not isinstance(node, KApply):
            return node
        if node.label.name != 'decreasesInduction':
            return node

        nonlocal result
        assert not result
        assert node.arity == 3
        result_list: list[str] = []
        for child in node.args:
            assert isinstance(child, KToken), 'decreasesInduction should have three string arguments'
            assert child.sort.name == 'String', 'decreasesInduction should have three string arguments'
            result_list.append(pretty_string(child))
        assert len(result_list) == 3, 'decreasesInduction should have three string arguments'
        result = (result_list[0], result_list[1], result_list[2])
        return node

    bottom_up(finder, root)
    assert result, 'Decreases predicate not found'
    return result


NO_EVALUATORS = AttKey('no-evaluators', type=_NONE)


def create_induction_modules(
    claims: List[KClaim], temporary_directory: Path
) -> List[Tuple[KClaim, KDefinition, KFlatModule]]:
    assert len(claims) == 1
    claim = claims[0]
    (var_name, measure_name, lowest_value) = find_decreases(claim.requires)
    print((var_name, measure_name, lowest_value))

    symbol_name = f'symbol{var_name}'

    var_sort = INT  # find_variable_sort(var_name)
    lowest_value_term = intToken(int(lowest_value))
    symbol_term = KApply(symbol_name)

    var_constraints = mlEqualsTrue(
        andBool(
            [
                KApply(measure_name, (symbol_term, KVariable(var_name, var_sort))),
                notBool(KApply(measure_name, (lowest_value_term, KVariable(var_name, var_sort)))),
            ]
        )
    )

    symbol_syntax = KProduction(
        sort=INT,
        items=[KTerminal(symbol_name), KTerminal('('), KTerminal(')')],
        att=KAtt([Atts.FUNCTION(None), Atts.TOTAL(None), Atts.SYMBOL(symbol_name), NO_EVALUATORS(None)]),
    )
    assert isinstance(claim.body, KApply)
    inner_body = claim.body.args[0]
    # TODO: This is not a rule, since it's not something that takes 1 rewrite step.
    # This is a reachability claim and should be modelled as such.
    rule = KRule(
        body=inner_body,
        requires=andBool([claim.requires, var_constraints]),
        ensures=claim.ensures,
        att=KAtt([Atts.PRIORITY('1'), Atts.LABEL('induction-rule')]),
    )
    new_claim = KClaim(
        body=replace_var(claim.body, var_name, symbol_term),
        requires=replace_var(claim.requires, var_name, symbol_term),
        ensures=replace_var(claim.ensures, var_name, symbol_term),
        att=KAtt([Atts.LABEL('induction-claim')])
    )

    new_semantics_module_syntax = KFlatModule(
        name=f'{NEW_SEMANTICS_NAME.upper()}-SYNTAX', imports=[KImport('IMP-SYNTAX')], sentences=[symbol_syntax]
    )

    new_semantics_module = KFlatModule(
        name=NEW_SEMANTICS_NAME.upper(),
        imports=[KImport('IMP'), KImport(f'{NEW_SEMANTICS_NAME.upper()}-SYNTAX')],
        sentences=[rule],
    )

    new_claim_module = KFlatModule(
        name=f'{NEW_SEMANTICS_NAME.upper()}-SPEC', imports=[KImport(new_semantics_module.name)], sentences=[new_claim]
    )

    semantics_definition = KDefinition(
        new_semantics_module.name,
        requires=[KRequire(str(K_SOURCE))],
        all_modules=[new_semantics_module_syntax, new_semantics_module],
    )

    return [(new_claim, semantics_definition, new_claim_module)]


def kompile_induction(definition: KDefinition, printer: KPrint, temporary_directory: Path) -> Path:
    temporary_directory.mkdir(parents=True, exist_ok=True)
    definition_file = temporary_directory / INDUCTION_DEFINITION_FILE
    definition_file.write_text(printer.pretty_print(definition) + '\n\n')
    print(f'Kompiling induction module: {definition_file} ...', flush=True)
    kompiled_dir = kompile(
        definition_file,
        output_dir=temporary_directory / 'induction-kompile',
        backend=KompileBackend.HASKELL,
        main_module=NEW_SEMANTICS_NAME.upper(),
        syntax_module=f'{NEW_SEMANTICS_NAME.upper()}-SYNTAX',
    )
    print('Kompile done.', flush=True)
    return kompiled_dir


def run_induction_proof(claim: KClaim, definition_dir: Path) -> None:
    kprove = create_kprove(definition_dir)
    kprint = create_printer(definition_dir)
    # claims = kprove.get_claims(
    #     Path(spec_file), spec_module_name=spec_module, claim_labels=[f'{spec_module}.{claim_id}']
    # )
    claims = [claim]

    for current_claim in claims:
        with (
            kore_server(definition_dir, kprint.main_module) as k_server,
            KoreClient(
                'localhost',
                port=39425 if DEBUG_SERVER else k_server.port,
                bug_report=BugReport(BUG_REPORT_PATH) if BUG_REPORT else None,
            ) as kore_client,
        ):
            cterm_symbolic = CTermSymbolic(kore_client, kprint.definition, kprint.kompiled_kore)
            kcfg_explore = KCFGExplore(cterm_symbolic)

            print('Proving:')
            print(kprint.pretty_print(current_claim.body))
            print('requires ', kprint.pretty_print(current_claim.requires))
            print('ensures ', kprint.pretty_print(current_claim.ensures))
            print('With semantics:', definition_dir)
            (kcfg, init_id, target_id) = KCFG.from_claim(kprove.definition, current_claim)
            init = kcfg.node(init_id)
            new_init_term = cterm_symbolic.assume_defined(init.cterm, kprint.main_module)
            old_node = kcfg.get_node(init_id)
            assert old_node
            kcfg.replace_node(old_node.let(cterm=new_init_term))
            logs: dict[int, tuple[LogEntry, ...]] = {}
            proof = APRProof.from_claim(kprint.definition, claim, logs=logs)
            prover = APRProver(proof, kcfg_explore)
            prover.advance_proof(
                max_iterations=1000,
            )
            kcfg = proof.kcfg

            failed_nodes = [node for node in kcfg.leaves if not node.id == target_id]
            assert failed_nodes == 0


def main(args: List[str]) -> None:
    kompile_semantics()
    kprove = create_kprove(DEFINITION_DIR)
    printer = create_printer(DEFINITION_DIR)
    claims = load_claims(kprove)
    claims_with_modules = create_induction_modules(claims, WORK_DIR)
    for claim, definition, claim_module in claims_with_modules:
        (WORK_DIR / f'{NEW_SEMANTICS_NAME}-spec.k').write_text(printer.pretty_print(claim_module))
        definition_dir = kompile_induction(definition, printer, WORK_DIR)
        run_induction_proof(claim, definition_dir)


if __name__ == '__main__':
    main(sys.argv[1:])
