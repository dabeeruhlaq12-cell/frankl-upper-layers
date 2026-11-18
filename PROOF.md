# A transition at the upper layers of the Boolean cube

Working proof · 18 November 2026

Frankl's conjecture asks whether some ground element of every nontrivial finite union-closed family occurs in at least half its members. The results below concern families on [n] containing **every** set of size at least K. They give a sufficient range and a reduction in the other direction. They do not establish the unrestricted conjecture. The arguments have not undergone independent review, and priority is unverified.

Write log for the natural logarithm. For fixed c > 0 put

    K_c(n) = ceil(n/2 + c sqrt(n log n)).

**A.** For each c < 1/2 with c > 0 and all sufficiently large n, every such family with K = K_c(n) satisfies Frankl. In fact the average member has at least n/2 elements.

**B.** For each fixed c > 1/2, proving Frankl for all sufficiently large n and all such families with K = K_c(n) is equivalent to proving Frankl in general. Specifically, any counterexample can be converted into counterexamples in unbounded dimensions with this upper portion of the cube present.

These are statements for fixed constants on opposite sides of 1/2. No equivalence at c = 1/2 is asserted.

## A. The exact test for uniform averaging

Assume 2 ≤ K ≤ n, let F be union-closed, and let D consist of the subsets absent from F. Let d_i count the absent sets of size i. For an absent i-set A with i ≥ 2, at most one of its immediate subsets belongs to F: two distinct ones would have union A. Count the incidences between absent sets on consecutive levels. This gives

    (i−1)d_i ≤ (n−i+1)d_{i−1}.

Consequently d_i / binom(n−1,i−1) is nonincreasing for i ≥ 1. On levels 1 through K−1, start with weights binom(n−1,i−1) and reweight by these nonincreasing ratios. This can only lower the mean of i. Explicitly, for a random level I with the original weights and an independent copy J, (I−J)(w(I)−w(J)) ≤ 0, giving nonpositive covariance. A missing empty set can only lower the mean further. The cases of no missing sets or only the empty set missing are immediate.

It follows that the mean size of a missing set is at most

    μ = 1 + E[Y | Y ≤ K−2],     Y ~ Binomial(n−1, 1/2).

This is attained when D consists of all sets containing one fixed point and having size below K. Its complement is union-closed: the union of two members either omits the point or already contains a member of size at least K.

The complete cube has average size n/2. Therefore every F satisfying the upper-layer hypothesis has average size at least n/2 **if and only if** μ ≤ n/2. Whenever this holds, counting incidences in F gives an element in at least half its members. By the binomial identity j binom(m,j) = m binom(m−1,j−1), the exact criterion is

    (n−1) binom(n−2,K−2) ≥ sum_{j=0}^{K−2} binom(n−1,j).

For example, the exact largest successful K is 59 for n=100 and 536 for n=1000.

At K = K_c(n), the sum on the right is (1−o(1))2^(n−1). Stirling's formula makes the ratio of left to right n^(1/2−2c²+o(1)). This proves A and, for c > 1/2, gives explicit families where uniform averaging fails. Failure of uniform averaging by itself is insufficient to prove B.

## B. Padding a hypothetical counterexample

For a family S write Δ_i(S) = |S| − 2|{A ∈ S : i ∈ A}|. A counterexample has strictly positive Δ_i at every ground coordinate. A product below takes sets independently on disjoint grounds.

**1. A base with high logarithmic rate.** Start from a hypothetical counterexample. Square it by a direct product. Each deficit is multiplied by the size of the original family, at least two. Remove the empty set if present, losing at most one unit of each deficit. The resulting empty-set-free counterexample E has strictly positive deficits. Append t new coordinates, unrestricted above each row of E, and add back the single globally empty set. This gives a union-closed family B. Old deficits are 2^t Δ_i(E)+1, and new deficits are exactly one. If b is its ground size and M its number of rows, then M = 1+2^t |E| and b = t+|ground(E)|. Hence b/log₂ M tends to one as t grows. For the specified c > 1/2, fix t large enough that

    a = b/log₂ M < 1/2 + 2c².

Let δ = min_i Δ_i(B)/M > 0. All these base parameters are now fixed. B contains the empty set and has positive average row size u.

**2. Many inclusion-minimal selector rows, with all coordinates still rare.** Take ℓ tending to infinity through multiples of M. Set p = ceil(ℓ^(2/3)) and h = ℓ+p. In B^h retain tuples of total size at least R = ℓu. This is integer because ℓ is a multiple of M. The retained family Q is union-closed. Under the uniform product measure the total size has mean hu and variance O(h). Chebyshev's inequality bounds the proportion deleted by O(h/p²) = o(1). Each coordinate of Q therefore has deficit at least (δ/2)M^h for all large ℓ.

There are at least M^ℓ/(ℓ+1)^M minimal rows of Q. Take p initial empty entries and then all words of length ℓ containing each B-row exactly ℓ/M times. Each has total size exactly R, so is minimal. The balanced type has maximum multinomial coefficient (moving one count from a larger to a smaller part proves this), and there are at most (ℓ+1)^M types.

Choose k = floor(M^ℓ/(ℓ+1)^(M+2)) distinct such rows q₁,…,q_k. In particular k = o(M^h) and log₂ k = h log₂ M − o(h).

**3. The larger family before completion.** Attach k disjoint payload blocks of b points each. Their total length is L=bk and the overall dimension is N=bh+L. Over each selector row allow arbitrary payloads, except that over q_j the j-th block must be a member of B. Call the family G. A union landing over q_j must use that same minimal selector in each input. Closure of B then gives closure of G.

Before these restrictions each selector deficit was at least (δ/2)M^h 2^L. The k restrictions can remove at most k 2^L rows altogether. For large ℓ the remaining deficit is at least (δ/4) M^h 2^L. A payload coordinate i in block j has exactly

    Δ_i(G) = 2^(L−b) Δ_i(B) ≥ 2^(L−b),

where on the right i denotes the corresponding coordinate of B. At every selector other than q_j this bit is free and its contributions cancel in pairs. At q_j the formula follows by counting the other free bits.

**4. Fill the entire upper portion.** Put K = K_c(N) and add every subset of size at least K. The resulting H is union-closed. From the growth of k we have 2^(bh)=N^(a+o(1)) and M^h=N^(1+o(1)). The loss of a selector deficit is at most the number of added sets, bounded by the standard fair-binomial tail inequality

    2^N exp(−2(K−N/2)²/N) ≤ 2^N N^(−2c²).

The available selector deficit is at least 2^N N^(1−a+o(1)) times a positive constant. It dominates this loss.

For a payload coordinate i in block j, distinguish two cases. Away from q_j, whether a set belongs to G is independent of its i-bit when all other bits are fixed. On such a two-point pair the new upper portion can contribute a net negative deficit only if the lower set has size K−1 and the upper one has size K. There are at most binom(N−1,K−1) such pairs across the cube. Stirling's formula gives

    binom(N−1,K−1) = 2^N N^(−1/2−2c²+o(1)).

At the exceptional selector q_j, bound the loss by counting every payload that reaches the threshold. Since bh = O(log N) and |q_j| ≤ bh, the cutoff K−|q_j| exceeds L/2 by at least c sqrt(N log N)−O(log N). The fair-binomial tail bound thus gives o(2^L) such payloads. The initial deficit is at least 2^(L−b), a fixed positive fraction of 2^L. The exceptional loss is smaller in order, and so is the ordinary boundary term since 2^L = 2^N N^(−a+o(1)) and a < 1/2+2c². Every coordinate of H still has positive deficit.

This completes the construction for unbounded N and proves B by contraposition. The asymmetry in the last step matters: charging every added set to every payload coordinate would give a weaker constant. Most added sets cancel with their one-bit partners.

## Checks and limits

The attached-in-text Python checks are independent of the asymptotic proof. The first enumerates every qualifying family on four points and tests the exact criterion. At K=2,3,4 it finds 32, 1090, and 4542 qualifying families, respectively, of which 0, 0, and 98 fail uniform averaging. The second checks union closure and the signed boundary accounting for a concrete 960-member construction. Its base is an ordinary union-closed family with mixed signs, so it tests the identities without assuming a counterexample to Frankl exists.

```python
from math import comb
from itertools import combinations
n=4; cube=list(range(1<<n))
for K in range(2,n+1):
    s=sum(comb(n-1,j) for j in range(K-1))
    crit=(n-1)*comb(n-2,K-2)>=s
    tail=[a for a in cube if a.bit_count()>=K]
    low=sorted(set(cube)-set(tail))
    count=0;fails=0
    for flags in range(1<<len(low)):
        F=set(tail)|{a for j,a in enumerate(low) if flags>>j&1}
        if any(a|b not in F for a,b in combinations(F,2)):continue
        count+=1
        fails+=sum(2*a.bit_count()-n for a in F)<0
    assert crit==(fails==0)
    print(K,count,fails)
```
```python
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
```

## Context

- [Douglas B. West, Union-Closed Sets Conjecture](https://www.dwest.web.illinois.edu/openp/unionclos.html), statement and equivalent forms.
- [Bjorn Poonen, Union-closed families](https://www.sciencedirect.com/science/article/pii/0097316592900686), earlier equivalences and restricted cases.
- [Local Configurations in Union-Closed Families](https://www.tandfonline.com/doi/full/10.1080/10586458.2024.2410964), related work on forcing abundance through prescribed members.
- [On averaging Frankl's conjecture for large union-closed-sets](https://www.sciencedirect.com/science/article/pii/S0097316508001040), related work on the averaged property.

The exact criterion concerns averaging on the specified ground; a claim of novelty would require a deeper comparison with this literature. The unresolved mathematical step is an abundance argument above the averaging threshold, or a different proof encompassing all families.
