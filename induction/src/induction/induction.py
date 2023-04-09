import subprocess
import sys
from pathlib import Path
from typing import List

from pyk.ktool.kompile import KompileBackend, kompile
from pyk.ktool.kprove import KProve
from pyk.kast.inner import KApply, KVariable
from pyk.kast.outer import KClaim, KRule
from pyk.prelude.kbool import andBool, notBool
from pyk.prelude.kint import INT, intToken
from pyk.prelude.ml import mlAnd, mlEqualsTrue

ROOT = Path(subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).decode().strip())
K_DIR = ROOT / 'induction' / 'k-src'
K_SOURCE = K_DIR / 'imp.md'
K_SPEC = K_DIR / 'sum-to-n-spec.k'
BUILD_DIR = ROOT / '.build'
DEFINITION_PARENT = BUILD_DIR / 'definition'
DEFINITION_DIR = DEFINITION_PARENT / 'imp-kompiled'


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
  print('Loading the definition...', flush = True)
  kprove = KProve(DEFINITION_DIR, bug_report=None)
  print('Done loading.', flush = True)
  return kprove


def load_claims(kprove: KProve) -> List[KClaim]:
    claims = kprove.get_claims(K_SPEC)
    return claims


def create_induction_modules(claims: List[KClaim]):
    assert len(claims) == 1
    claim = claims[0]
    assert 'decreases' in claim.att, [claim.att]
    print(claim.att['decreases'])
    decreases = claim.att['decreases']
    pieces = tuple(a.strip() for a in decreases.split(','))
    (var_name, measure_name, lowest_value) = pieces
    print((var_name, measure_name, lowest_value))

    symbol_name = f'symbol{var_name}'

    var_sort = INT # find_variable_sort(var_name)
    lowest_value_term = intToken(int(lowest_value))

    var_constraints = mlEqualsTrue(
        andBool(
            [ KApply(measure_name, (KApply(symbol_name), KVariable(var_name, var_sort)))
            , notBool(KApply(measure_name, (lowest_value_term, KVariable(var_name, var_sort))))
            ]
        )
    )

    rule = KRule(body=claim.body, requires=mlAnd([claim.requires, var_constraints]), ensures=claim.ensures)

def main(args: List[str]) -> None:
  kompile_semantics()
  kprove = create_kprove()
  claims = load_claims(kprove)
  create_induction_modules(claims)
  kompile_induction()
  run_induction_proof()

if __name__ == '__main__':
  main(sys.argv[1:])