# Polynomial visibility: an elementary proof

The result concerns square density in the positive lattice. For every **nonzero**
`F : Polynomial ℤ` with two distinct complex roots, the proportion of points in
`{1,…,N} × {1,…,N}` visible along rational multiples of `F` tends to one.

The nonzero assumption is necessary in the standalone wording: the zero
polynomial vanishes at two distinct complex numbers and has no visible points.
`literal_conjecture_false` formalizes that counterexample separately.

Verification completed successfully: `lake build` and `lake env lean Audit.lean`
both return exit code 0. The main theorem depends only on `propext`,
`Classical.choice`, and `Quot.sound`; there are no admitted proofs or additional
mathematical axioms.

## Files

- `paper.tex`: the short, self-contained mathematical proof.
- `output/pdf/polynomial_visibility.pdf`: the compiled paper.
- `Visibility/Main.lean`: the full nonzero theorem, `visibility_density_one`.
- `Visibility/Definitions.lean`: the exact rational visibility definition and
  the real limit defining square density.
- `Audit.lean`: prints the main theorem's type and its axiom dependencies.
- `verification.txt`: saved verification output.

## Proof idea

Let `g = gcd(F(a), h)` on a positive, increasing tail. A point hidden by an
earlier abscissa `u` satisfies `F(u) = (r/g) F(a)` for some `1 ≤ r < g`.

The random gcd `g` is bounded outside a set of arbitrarily small density,
uniformly in the square size. Indeed, a common prime `p` outside a fixed finite
set has probability at most `2 deg(F)/p²`. Large powers of the remaining small
primes can be excluded just by counting divisibility of the height.

After fixing a bound on `g`, only finitely many ratios remain. For each fixed
ratio `q` in `(0,1)`, polynomial coefficient comparisons give
`u = αa + β + o(1)`, where `α^deg(F) = q`. An irrational `α` eventually forbids
every fixed positive gap between admissible abscissae, forcing density zero.
A rational `α` makes `β` rational; the approximation eventually becomes an
exact affine equality. Infinitely many such equalities would make a strict
affine contraction permute a finite root set containing two distinct points,
which is impossible.

The order of limits matters: the gcd cutoff is fixed before the square grows.
No uniform theorem about varying-ratio algebraic curves is used.

## Lean modules

| Module | Verified ingredient |
| --- | --- |
| `Arithmetic` | Exact blocker criterion and the bounded-gcd ratio reduction |
| `Tightness`, `TightnessBound` | Prime-power cutoff, residue counts, and full gcd tightness |
| `Affine`, `Asymptote` | Affine coefficients, polynomial barriers, and the shrinking error |
| `Sparse`, `DensityZero` | Irrational spacing, rational discreteness, and density bookkeeping |
| `Rigidity` | A finite root set cannot be preserved by a strict affine contraction |
| `Growth`, `Sign`, `RootHypotheses` | Growth threshold, sign invariance, and degree bound |
| `FixedRatio`, `RatioColumns` | Density zero for the actual finite collection of polynomial ratios |
| `Density`, `Main` | Exact count decomposition and the final density-one theorem |

The finite bound used in Lean is slightly coarser than the bound displayed in
the paper. It gives, with `M = (K!)^E`, a normalized exceptional count at most
`4 deg(F)/(K+1) + (K+1)/(E+1)`. This proves the same uniform tightness lemma.

## Reproduce

The project pins Lean **4.28.0** and mathlib **v4.28.0**, commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`. With `elan` installed, run:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The local `.lake/packages` link reuses an existing installation for this
workspace. It is excluded from the portable source archive. The included
Lake manifest pins all dependencies for a fresh checkout.

To compile the paper:

```sh
mkdir -p output/pdf
pdflatex -halt-on-error -jobname=polynomial_visibility -output-directory=output/pdf paper.tex
pdflatex -halt-on-error -jobname=polynomial_visibility -output-directory=output/pdf paper.tex
```

## Provenance

The mathematical argument is the bounded-height-gcd proof developed for this
request. The prior conjectures and proper-power result are cited in the paper.
`Growth.lean` adapts the existing local `VDC/GrowthBound.lean` development;
it is independently compiled here and imports no VDC modules. All other
project modules were developed for this proof.
