from __future__ import annotations

import subprocess
import sys
from pathlib import Path
from typing import TYPE_CHECKING, List, Tuple

from pyk.kast.inner import KApply, KVariable, bottom_up
from pyk.kast.outer import KAtt, KClaim, KDefinition, KFlatModule, KImport, KProduction, KRequire, KRule, KTerminal
from pyk.kcfg.explore import KCFGExplore
from pyk.kcfg.kcfg import KCFG
from pyk.ktool.kompile import KompileBackend, kompile
from pyk.ktool.kprint import KPrint, SymbolTable
from pyk.ktool.kprove import KProve
from pyk.prelude.kbool import andBool, notBool
from pyk.prelude.kint import INT, intToken
from pyk.prelude.ml import mlAnd, mlEqualsTrue
from pyk.proof.reachability import AGProof, AGProver

if TYPE_CHECKING:
    from pyk.kast.inner import KInner
    from pyk.ktool.kprint import KPrint


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


class MyKPrint(KPrint):
    def __init__(
        self,
        definition_dir: Path,
        use_directory: Optional[Path] = None,
        bug_report: Optional[BugReport] = None,
        extra_unparsing_modules: Iterable[KFlatModule] = (),
    ) -> None:
        super().__init__(definition_dir, use_directory, bug_report, extra_unparsing_modules)

    @classmethod
    def _patch_symbol_table(cls, symbol_table: SymbolTable) -> None:
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
    kprint = MyKPrint(definition_dir, bug_report=None)
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


def create_induction_modules(claims: List[KClaim], temporary_directory: Path) -> List[Tuple[KClaim, KDefinition]]:
    assert len(claims) == 1
    claim = claims[0]
    assert 'decreases' in claim.att, [claim.att]
    print(claim.att['decreases'])
    decreases = claim.att['decreases']
    pieces = tuple(a.strip() for a in decreases.split(','))
    (var_name, measure_name, lowest_value) = pieces
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
        klabel=symbol_name,
        att=KAtt(atts={'function': '', 'total': '', 'klabel': symbol_name, 'symbol': '', 'no-evaluators': ''}),
    )
    assert isinstance(claim.body, KApply)
    inner_body = claim.body.args[0]
    # TODO: This is not a rule, since it's not something that takes 1 rewrite step.
    # This is a reachability claim and should be modelled as such.
    rule = KRule(body=inner_body, requires=andBool([claim.requires, var_constraints]), ensures=claim.ensures, att=KAtt({'priority' : '1', 'label' : 'induction-rule'}))
    new_claim = KClaim(
        body=replace_var(claim.body, var_name, symbol_term),
        requires=replace_var(claim.requires, var_name, symbol_term),
        ensures=replace_var(claim.ensures, var_name, symbol_term),
    )

    new_semantics_module_syntax = KFlatModule(
        name=f'{NEW_SEMANTICS_NAME.upper()}-SYNTAX', imports=[KImport('IMP-SYNTAX')], sentences=[symbol_syntax]
    )

    new_semantics_module = KFlatModule(
        name=NEW_SEMANTICS_NAME.upper(),
        imports=[KImport('IMP'), KImport(f'{NEW_SEMANTICS_NAME.upper()}-SYNTAX')],
        sentences=[rule],
    )

    # new_claim_module = KFlatModule(
    #     name = f'{NEW_SEMANTICS_NAME.upper()}-SPEC',
    #     imports = [KImport(new_semantics_module.name)],
    #     sentences = [new_claim]
    # )

    semantics_definition = KDefinition(
        new_semantics_module.name,
        requires=[KRequire(str(K_SOURCE))],
        all_modules=[new_semantics_module_syntax, new_semantics_module],
    )

    return [(new_claim, semantics_definition)]


def kompile_induction(definition: KDefinition, printer: KPrint, temporary_directory: Path) -> Path:
    temporary_directory.mkdir(parents=True, exist_ok=True)
    definition_file = temporary_directory / INDUCTION_DEFINITION_FILE
    definition_file.write_text(printer.pretty_print(definition) + '\n\n')
    print('Kompiling induction module...', flush=True)
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
        kcfg_explore = KCFGExplore(kprove)
        print('Proving:')
        print(kprint.pretty_print(current_claim.body))
        print('requires ', kprint.pretty_print(current_claim.requires))
        print('ensures ', kprint.pretty_print(current_claim.ensures))
        kcfg = KCFG.from_claim(kprove.definition, current_claim)
        init = kcfg.get_unique_init()
        new_init_term = kcfg_explore.cterm_assume_defined(init.cterm)
        kcfg.replace_node(init.id, new_init_term)
        prover = AGProver(AGProof(kcfg))
        kcfg = prover.advance_proof(
            'induction',
            kcfg_explore,
            max_iterations=1000,
            execute_depth=100,
            terminal_rules=[],
        )

        failed_nodes = len(kcfg.frontier) + len(kcfg.stuck)
        assert failed_nodes == 0


def main(args: List[str]) -> None:
    kompile_semantics()
    kprove = create_kprove(DEFINITION_DIR)
    printer = create_printer(DEFINITION_DIR)
    claims = load_claims(kprove)
    claims_with_modules = create_induction_modules(claims, WORK_DIR)
    for claim, definition in claims_with_modules:
        definition_dir = kompile_induction(definition, printer, WORK_DIR)
        run_induction_proof(claim, definition_dir)


if __name__ == '__main__':
    main(sys.argv[1:])
