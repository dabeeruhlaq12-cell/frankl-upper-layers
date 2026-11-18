"""Test the signed counting identities of the padding argument on a small model."""
from itertools import product
from math import comb


def deficit(family, coordinate):
    return sum(1 - 2 * ((s >> coordinate) & 1) for s in family)


base = {1, 2, 3, 7}
block_width = 3
selectors = {a | (b << block_width) for a, b in product(base, repeat=2)}
restricted_blocks = {9: 0, 18: 1}
payload_width, dimension = 6, 12
family = set()
for selector, payload in product(selectors, range(1 << payload_width)):
    if selector in restricted_blocks:
        offset = block_width * restricted_blocks[selector]
        if ((payload >> offset) & 7) not in base:
            continue
    family.add((selector << payload_width) | payload)

assert len(family) == 960
assert all(a | b in family for a in family for b in family)
for bit in range(payload_width):
    expected = (1 << block_width) * deficit(base, bit % block_width)
    assert deficit(family, bit) == expected

for cutoff in range(1, dimension + 1):
    tail = {s for s in range(1 << dimension) if s.bit_count() >= cutoff}
    completed = family | tail
    boundary = comb(dimension - 1, cutoff - 1)
    for selector, block in restricted_blocks.items():
        exceptional = sum(s >> payload_width == selector for s in tail)
        for bit in range(block * block_width, (block + 1) * block_width):
            assert deficit(completed, bit) >= deficit(family, bit) - boundary - exceptional

print("960 members; closure, six signed identities and 72 threshold inequalities passed")
