"""Compare every four-element family containing the required upper layers."""
from itertools import combinations
from math import comb


def enumerate_families(n, cutoff):
    cube = range(1 << n)
    required = {s for s in cube if s.bit_count() >= cutoff}
    optional = sorted(set(cube) - required)
    valid = violations = 0
    for choices in range(1 << len(optional)):
        family = required | {
            s for i, s in enumerate(optional) if choices & (1 << i)
        }
        if any(a | b not in family for a, b in combinations(family, 2)):
            continue
        valid += 1
        excess = sum(2 * s.bit_count() - n for s in family)
        violations += excess < 0
    return valid, violations


for cutoff, expected in [(2, (32, 0)), (3, (1090, 0)), (4, (4542, 98))]:
    valid, violations = enumerate_families(4, cutoff)
    assert (valid, violations) == expected
    bound = 3 * comb(2, cutoff - 2)
    prefix = sum(comb(3, j) for j in range(cutoff - 1))
    assert (bound >= prefix) == (violations == 0)
    print(f"K={cutoff}: {valid} families, {violations} averaging violations")
