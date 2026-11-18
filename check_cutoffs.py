"""Exact numerical consequences of the averaging criterion, using integers."""
from math import comb


def passing_cutoffs(n):
    total = 0
    passing = []
    for k in range(2, n + 1):
        total += comb(n - 1, k - 2)
        if (n - 1) * comb(n - 2, k - 2) >= total:
            passing.append(k)
    return passing


for dimension, last in [(4, 3), (100, 59), (1000, 536)]:
    assert passing_cutoffs(dimension) == list(range(2, last + 1))
    print(f"n={dimension}: exact passing cutoffs 2 through {last}")
