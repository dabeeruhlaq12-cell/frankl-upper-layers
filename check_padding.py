from itertools import product
from math import comb
B = {1, 2, 3, 7}
b = 3
selectors = {a | (d << b) for a,d in product(B, repeat=2)}
special = {9: 0, 18: 1}
L, N = 6, 12
F = set()
for q,z in product(selectors, range(1 << L)):
    if q not in special or (z >> (b*special[q])) & 7 in B:
        F.add((q << L) | z)
assert all(a|d in F for a in F for d in F)
def balance(f,i):
    return sum(1-2*((a >> i) & 1) for a in f)
for j in range(L):
    assert balance(F,j) == (1<<b)*balance(B,j%b)
for K in range(1,N+1):
    tail = {a for a in range(1 << N) if a.bit_count() >= K}
    H = F | tail
    for q,t in special.items():
        exc = sum(a >> L == q for a in tail)
        for i in range(t*b,(t+1)*b):
            assert balance(H,i) >= balance(F,i)-comb(N-1,K-1)-exc
print(len(F), 'members; closure, six signed identities and 72 threshold inequalities passed')
