# Upper layers in Frankl’s union-closed sets conjecture

When does the presence of every large subset force one element to occur in at least half the family? This AI-assisted working note studies that question through an exact counting criterion and an asymptotic reduction. The unrestricted conjecture remains open. Historical priority and independent mathematical review are pending.

**Example.** On 100 elements, containing every set of size at least 59 guarantees the conclusion by uniform averaging. At cutoff 60 an explicit family defeats that averaging argument.

[Read the statements and proofs](PROOF.md).

## Verification coverage

| Claim | Available evidence |
|---|---|
| Exact averaging criterion for arbitrary dimensions | Written incidence count, weighted comparison, and extremal example |
| Cutoffs on 100 and 1,000 points | Exact integer checks, all admissible cutoffs tested |
| Finite sanity checks | Exhaustive four-point enumeration and a 960-member construction |
| Lean targets | Candidate proofs for the unique-deletion, adjacent-rank counting and weighted-sum lemmas, fast binomial computation, and the numerical criterion at 59 and 60. See the Lean job for compilation status. |
| Equivalence above the asymptotic threshold | Written proof; full Lean formalization outstanding |

## Reproduce

Python 3.10 or newer, standard library only. Run with assertions enabled.

~~~sh
python3 check_cutoffs.py
python3 check_ranks.py
python3 check_padding.py
~~~

For the formal targets, use Lean and mathlib v4.19.0. With elan installed:

~~~sh
lake update
lake exe cache get
lake build
lake env lean -DwarningAsError=true UpperLayers.lean
~~~

The module prints the axiom dependencies for each named result. A successful build certifies only those formal statements. In particular, the two numerical Lean goals evaluate a binomial inequality; the logical passage from that inequality to all qualifying families is in the paper proof.

[Verification workflow](.github/workflows/verify.yml)
