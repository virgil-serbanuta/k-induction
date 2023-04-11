from __future__ import annotations

import subprocess
import sys
from pathlib import Path
from typing import TYPE_CHECKING, List, Tuple

from pyk.kast.inner import KApply, KVariable, bottom_up
from pyk.kast.outer import KAtt, KClaim, KDefinition, KFlatModule, KImport, KProduction, KRequire, KRule, KTerminal
from pyk.ktool.kompile import KompileBackend, kompile
from pyk.ktool.kprove import KProve
from pyk.prelude.kbool import andBool, notBool
from pyk.prelude.kint import INT, intToken
from pyk.prelude.ml import mlAnd, mlEqualsTrue

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


def create_kprove() -> KProve:
    print('Loading the definition...', flush=True)
    kprove = KProve(DEFINITION_DIR, bug_report=None)
    print('Done loading.', flush=True)
    return kprove


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
    rule = KRule(body=claim.body, requires=mlAnd([claim.requires, var_constraints]), ensures=claim.ensures)
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
        output_dir=temporary_directory,
        backend=KompileBackend.HASKELL,
        main_module=NEW_SEMANTICS_NAME.upper(),
        syntax_module=f'{NEW_SEMANTICS_NAME.upper()}-SYNTAX',
    )
    print('Kompile done.', flush=True)
    return kompiled_dir


def run_induction_proof(claim: KClaim, definition_dir: Path) -> None:
    pass


def main(args: List[str]) -> None:
    kompile_semantics()
    kprove = create_kprove()
    printer = kprove
    claims = load_claims(kprove)
    claims_with_modules = create_induction_modules(claims, WORK_DIR)
    for claim, definition in claims_with_modules:
        definition_dir = kompile_induction(definition, printer, WORK_DIR)
        run_induction_proof(claim, definition_dir)


if __name__ == '__main__':
    main(sys.argv[1:])
