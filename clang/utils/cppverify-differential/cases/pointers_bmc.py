"""The pointer cases under bounded model checking. A bounded-safe verdict
covers the executions within the bound: a buffer of n elements takes n
iterations."""
import copy

from cases import pointers

CASES = []
for case in pointers.CASES:
    if case.domain != []:
        bounded = copy.copy(case)
        bounded.name = case.name + '_bmc'
        bounded.iterations = lambda inp: inp.get('n', 0)
        CASES.append(bounded)
CONFIGS = ('bmc10', 'bmc10bv')
