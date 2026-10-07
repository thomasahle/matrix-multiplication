# Design of the algebraic-complexity formalization

## Purpose

This repository has two related goals:

1. build a reusable Lean library for algebraic complexity, designed so that its stable core could
   be contributed to [CSLib](https://github.com/leanprover/cslib); and
2. use that library to formalize classical and current matrix-multiplication results.

These goals determine the main architectural rule:

> General definitions and theorems belong in the reusable core. Named constructions, published
> bounds, optimization data, and paper certificates belong in downstream clients.

The core must make sense without Coppersmith--Winograd, Alman-style laser analyses, or any one
paper. Conversely, clients should exercise the public core API rather than reach into its proof
internals. Strassen and classical Coppersmith--Winograd are intended to be permanent regression
clients.

This document is the design contract for contributors, human or AI. Update it when a substantial
design decision changes.

## Abstraction-first proof discipline

Every paper proof is also a design test for the reusable library. Before adding a construction or
proof local to a named client, ask whether its real content is a paper-independent statement about
tensor relations, products, reindexing, finite probability, entropy, or asymptotic growth. When a
generic formulation makes the client shorter or has another plausible use, prove that formulation
in the lowest appropriate layer and make the client a specialization.

Prefer strengthening along semantic boundaries that the mathematics already respects: arbitrary
finite alphabets over enumerated CW addresses, equivalences over definitional identifications,
relation-parametric extraction over zeroing-only APIs, and explicit finite certificates over
unattained optimizer functions. Do not generalize merely for maximal generality: an abstraction
should remove duplication, expose a reusable law, or prevent a real class of mistakes. In
particular, if generalization introduces casts or auxiliary interfaces that make both the theorem
and its only client harder to understand, keep the local lemma until a second use clarifies the
right API.

## Repository boundaries

The intended long-term layout is:

```text
AlgebraicComplexity/          reusable, potential CSLib contribution
AlgebraicComplexity/Adapters/ translations from optional external libraries
AlgebraicComplexityClients/   named classical results and regression clients
                              (intended; the clients currently live under
                              AlgebraicComplexity/Examples/, exposed through this library target)
MatrixMultiplication/         the current paper and its certificate checker
papers/                       local source material; ignored and never distributed
tmp/                          disposable experiments and dependency audits; ignored
```

The tree is in transition. In particular, the Strassen and Coppersmith--Winograd clients currently
live under `AlgebraicComplexity/Examples/`. They are downstream clients semantically and are
already exposed through the separate `AlgebraicComplexityClients` library target and umbrella
import. Their eventual physical move to `AlgebraicComplexityClients/` should be a coordinated
refactor; do not move a module while another contributor is editing it.

The top-level `MatrixMultiplication/` library is paper-specific. Its definitions may be promoted
to the reusable core only after they have a paper-independent statement, useful documentation,
and at least one client other than the paper that motivated them.

## Layering

Imports should follow the layers below. A lower layer must never import a higher one.

The tree does not yet meet this rule everywhere. The debt is recorded, not hidden. Five
pre-existing Tensor-to-layer-2 bridge edges are grandfathered by name in
`scripts/check_tensor_boundary.sh`, which fails on any sixth:

```text
Tensor.TypeExtraction            -> Combinatorics.WordType
Tensor.IndependenceBlockEntropy  -> Analysis.Subexponential
Tensor.IndependenceBlockEntropy  -> Combinatorics.WordType
Tensor.IndependenceBlockEntropy  -> Probability.EntropyValue
Tensor.IndependenceBlockEntropy  -> Probability.Finite
```

Two layer-2-to-layer-3 edges are standing debt that no gate catches, because
`check_tensor_boundary.sh` scans only sources physically under `Tensor/`:
`Combinatorics/RecursiveSplitMarginalCounting.lean:7` imports
`MatrixMultiplication.RecursiveChildType`, and
`Probability/ComplementaryProductProjectionParentLaw.lean:7` imports
`MatrixMultiplication.InterfaceTensor`. Extending the gate to the `Combinatorics/`, `Probability/`
and `Analysis/` roots, with those two as its grandfather list, is owed.

Both lists may only shrink. A new edge of either kind is a design error, not a new entry.

One deliberate exception to the directory naming sits below all of them: the
`AlgebraicComplexity/Asymptotics{Defs,}.lean` pair is a layer-0 shared analysis leaf. Apart from
each other they import only Mathlib, and they provide the growth-rate interface consumed by
layers 1--3 (currently `Tensor/AsymptoticRank.lean`,
`Tensor/AsymptoticIndependenceNumber.lean`, `Analysis/Subexponential.lean`,
`Combinatorics/BinomialTail.lean`, and
`MatrixMultiplication/Exponent.lean`). Keep the pair free of tensor, combinatorial, and
matrix-multiplication imports.

### 1. Tensor algebra

`AlgebraicComplexity/Tensor/`

- `Basic`: three-legged tensors, pure tensors, leg maps, and permutations;
- `Restriction`: exact restriction and legwise isomorphism;
- `Product`, `DirectSum`, `IndexedDirectSum`, `IndexedProduct`, `Power`: structural operations;
- `Rank`, `Concise`, `Polynomial`, `Degeneration`, `BorderRank`, `AsymptoticRank`: complexity
  relations, flattening lower bounds, and invariants;
- `Coordinates`: basis-dependent bridges for explicit finite certificates;
- `Monomial`, `Partitioned`, `PartitionedMonomial`, `PartitionedPermutation`,
  `PolynomialInterpolation`:
  reusable structured-tensor machinery. `PartitionedMonomial` is the basis-free block-weight
  interface for minimum-weight/antidiagonal degeneration; paper clients must use it instead of
  rebuilding coordinate-level matrix-to-scalar weights;
- `PartitionedExtraction`, `CompatibilityZeroing`, `PartitionedDirectSum`, `HoleRepair`, and
  `HoleRepairTree`:
  projection-closed variable zeroing, compatibility-isolation cleanup, exact conversion of
  legwise-independent support to an indexed direct sum, the coefficient-independent eight-box
  repair identity, and certified compilation of finite recursive repair plans. The former
  transitional `Tensor/Interpolation.lean` is now `Tensor/PolynomialInterpolation.lean`; the old
  name is gone;
- `Relation`, `IndexedDegeneration`, `BorderRankTransport`, `RankCompression`: the
  parameter-generic relation and recursive-stage calculus, composition of an exact restriction with
  a degeneration, indexed-family degenerations, and transport of rank/border-rank witnesses along
  them;
- `SliceRank`, `SliceRankDegeneration`, `SliceRankSaturation`, `SliceRankBlockEntropy`,
  `AsymptoticSliceRank`, `Subrank`, `KoszulFlattening`, `MatrixFlattening`,
  `MatrixFlatteningDirectSum`, `BorderConcise`, `StrassenEquations`,
  `SubstitutionMethod`, `SubstitutionMethodScale`: lower-bound invariants and the flattening,
  substitution, commutation-equation, and slice-rank machinery that supports them;
- `IndependenceNumber`, `AsymptoticIndependenceNumber`, `IndependenceMeasure`,
  `IndependenceSplitting`, `IndependenceBlockEntropy`, `MonomialIndependence`,
  `AsymptoticInvariant`, `AsymptoticRankCalculus`, `FreeLunchSpeedup`: the abstract-measure/barrier
  vocabulary — the independence number and its Fekete-style asymptotic version, the generic
  asymptotic-invariant engine shared by asymptotic rank/border rank/subrank/slice rank, the
  minimum-weight monomial degenerations that feed the asymptotic independence number, and the
  Alman--Li free-lunch speedup;
- `PartitionedPower`, `PartitionedPowerRelabeling`, `PartitionedProduct`, `PartitionedReindex`,
  `PartitionedRelabeling`, `PartitionedBoxRetyping`, `PartitionedCoarsening`,
  `PartitionedCoarseningInterface`, `PartitionedCoarseningPower`, `PartitionedGroupingBoxes`,
  `GroupedCompatibilityZeroing`, `LocalizedCoarsenedSelection`, `CoordinateBlockWord`: the
  structural calculus of partitioned tensors — powers, products, reindexing and relabeling, box
  coarsening and retyping, support-aware component extraction, and the word addressing of blocks;
- `PositiveExternalPower`, `DirectSumPower`, `IteratedProduct`, `PowerCoherence`, `PowerFamily`,
  `PowerZeroUnit`, `IndexedSubfamily`, `TypeExtraction`: coherence laws
  for iterated products and powers, the binomial direct-sum-power calculus, subfamily selection,
  and generic type extraction from a power;
- `Leg`, `GroupTensor`, `GroupCoefficients`: the leg index type, the structural tensor of a finite
  group algebra, and its coefficient table feeding the independence-number calculus.

This layer must not mention a named matrix-multiplication construction or a numerical bound.

### 2. Generic combinatorics, probability, and analysis

`AlgebraicComplexity/Combinatorics/`, `Probability/`, and `Analysis/`

This layer contains finite probability, entropy and logarithm lemmas, word types, multinomial
counting, hashing, progression-free sets, and asymptotic growth estimates. Statements should be
usable outside the laser method whenever practical.

The affine-hashing implementation is split into algebra, exact fiber counts, finite isolation and
averaging, and legal-triple extraction. The bridge from legal triples to partitioned tensors lives
one layer higher in `MatrixMultiplication/HashingExtraction.lean`; tensor foundations must not
import the combinatorics layer. Two carriers predate that rule and are grandfathered by name in
`scripts/check_tensor_boundary.sh` — `Tensor/TypeExtraction.lean` and
`Tensor/IndependenceBlockEntropy.lean`, five edges between them (see Layering above). No third may
be added, and neither is a precedent.

### 3. Matrix-multiplication theory

`AlgebraicComplexity/MatrixMultiplication.lean` and
`AlgebraicComplexity/MatrixMultiplication/`

This layer contains the rectangular matrix-multiplication tensor, product and symmetry laws, the
bilinear-algorithm/rank correspondence, matrix-multiplication exponent, Bini interpolation,
Schönhage's asymptotic sum inequality, tensor substitution/compression, and generic
laser/extraction interfaces.  The public laser abstraction is a **relation-parametric value
engine**: symmetrize a tensor by multiplying its three cyclic orientations, take powers, extract
direct sums of matrix-multiplication tensors, and regularize the resulting weighted sums.  Its
standard CW90 specialization uses exact legwise restrictions; a stronger extension uses
polynomial degenerations.  Schönhage's inequality is the soundness bridge from a value lower
bound to an upper bound on `omega`; it is not a competing extraction method.  `CTensor.lean` contains the
paper-independent cyclic C-tensor and
matrix-to-scalar antidiagonal degeneration, including its quadratic independent subfamily; named
CW constituents only instantiate this API downstream. `CTensorExtraction.lean` is the semantic
adapter from a fixed-Z partition fiber with injective X/Y labels to that uniform C-tensor API. Its
certificate deliberately permits constituent-dependent maps on X and Y but requires one shared Z
map, so clients cannot accidentally apply incompatible transformations to a common variable.
Bini's transfer lives in
`BiniInterpolation.lean` (renamed from the transitional `Interpolation.lean`, which is gone),
distinct from polynomial coefficient interpolation in the tensor
layer. Schönhage's inequality belongs here
because it is reusable theory, not a CW-specific result.

The value API has two deliberately separate levels, following the library's general
certificate/semantic split:

1. a finite value certificate is parameterized by an extraction relation and records a concrete
   extraction of a power of
   the three-orientation product to a finite direct sum
   `⊕_i ⟨m_i,n_i,p_i⟩`, together with its weight
   `∑_i (m_i*n_i*p_i)^τ`;
2. an asymptotic lower-bound relation regularizes such certificates and states `V_τ(T) ≥ v`
   without assuming that a supremum or limit is attained.

Typed leaves are shared input data for this engine, not a second value formalism.
`RationalTypedLeaf` owns the finite integral profile, visible-coordinate maps, entropy data, and
matrix-dimension data.  Orientation constructions should extend that same API: in particular,
`RationalTypedLeaf.cyclicProduct` forms the independent product with the two cyclic leg rotations,
rather than introducing a CW-specific symmetric-leaf structure.  It is kept in a separate module
only to quarantine its product-entropy imports from the basic typed-leaf file.  A client then
supplies, separately, a semantic proof that the tensor constituents described by the leaf extract
to the recorded matrix-multiplication tensors.

The extraction relation must therefore not be stored inside `RationalTypedLeaf`.  The finite value
certificate takes it as a parameter, so the same profile and dimension calculation can be reused
with partitioned zeroing, arbitrary exact restrictions, or polynomial degenerations.  This is the
key boundary: typed leaves describe **what is counted**, while the relation-parametric value layer
proves **how the counted pieces are obtained from the source tensor**.

Relation-parametric adapters must state their semantic endpoint explicitly.  The finite hashing
theorem in `RationalTypedLeafRelation.lean` accepts an arbitrary client relation whose witnesses
produce exact constituent restrictions; this covers zeroing and other structured restriction
certificates and then promotes the assembled direct sum to polynomial degeneration.  A
degeneration-only constituent certificate is strictly weaker and must use a separate theorem that
proves compatibility of polynomial degeneration with the relevant constituent powers.  It must
not be passed to an exact-restriction theorem by hiding the distinction inside the leaf or the
relation name.

The conventional noncomputable function `V_τ` (using exact restriction) and the polynomial-
degeneration extension may be exposed once their supremum/limit laws are proved, but clients
should continue to consume certificate-backed lower-bound relations.  The
existing `HasCyclicLaserExtractionRate` is the logarithmic, `τ = omega/3` specialization of this
semantic interface and should be connected to the value API rather than duplicated.  Required
generic laws include monotonicity under degeneration, invariance under legwise isomorphism and
cyclic orientation, superadditivity for direct sums, supermultiplicativity for tensor products,
and the appropriately hypothesized value-to-exponent theorem.  Its standard literature form is
stated in terms of asymptotic rank; a border-rank bound supplies a convenient stronger premise for
CW clients.  Equality and scalar-only edge cases must be checked against the primary theorem
rather than inferred from an expository slide.

```text
asymptoticRank(T) ≤ r  and  r < V_τ(T)  ==>  omega < 3*τ
```

The non-strict form `V_τ(T) ≥ asymptoticRank(T) ==> omega ≤ 3*τ` is **false**: for
`T = ⟨1,1,1⟩` every power is `⟨1,1,1⟩`, so `V_τ(T) = 1 = asymptoticRank(T)` for every real
`τ`, including `τ = 0`.  The comparison `Σ v_h^τ` against `Σ v_h^{omega/3}` carries information
only when one side is strictly larger, which is why [CoppersmithWinograd1990] solve their auxiliary
equation for the root of a strictly increasing function of `τ` and take a limit.  The generic
calculus and this theorem are proved in `MatrixMultiplication/TauValue.lean`
(`omega_lt_three_mul_of_certificate`, with an ε-robust variant for subexponential-loss sequences
and a `CyclicDegenerationCertificate` adapter for the CW clients); the certificate-wise soundness
half `V_{omega/3}(T) ≤ asymptoticRank(T)` is unconditional.

Definitions of value must state which finite operations are optimized over.  In particular, the
zeroing operation appearing in common Williams talk presentations is a certificate calculus for a
chosen partition, not the definition of the standard CW90 tensor value.  Modern sources define
that value using restrictions of powers of the cyclic symmetrization; some recursive-value sources
use polynomial degeneration instead.  The reusable
API distinguishes

```text
partitioned zeroing value  <=  exact-restriction value  <=  polynomial-degeneration value.
```

Each inequality must be a proved promotion of finite certificates.  Hashing clients normally build a
partitioned zeroing certificate; explicit algorithms may build a general restriction or
polynomial degeneration directly.  As of 2026-09-05 only the two upper rungs are instantiated in
Lean:
the exact-restriction and polynomial-degeneration values exist and their promotion is proved, while
the partitioned-zeroing rung is a documented intention with no Lean instantiation — there is no
zeroing-specific value relation and no zeroing-to-restriction promotion theorem, so hashing clients
currently land on the exact-restriction or degeneration rung directly.
Literature-facing modules may retain the conventional name
`V_τ` for the exact-restriction specialization used by their source.  The stronger intrinsic
extension should be named `degenerationValue`, not silently identified with conventional `V_τ`.

Keep lower-bound-only dependencies out of the basic tensor module. In particular,
`MatrixMultiplication/Concise.lean` imports both the basic matrix-multiplication tensor and
`Tensor/Concise`; `MatrixMultiplication.lean` itself does not import finite-dimensional
conciseness. This prevents changes to flattening lower bounds from invalidating every
matrix-multiplication definition and upper-bound client.

### 4. Regression and paper clients

Clients may import every lower layer. Examples include:

- Strassen's rank-seven decomposition;
- the Coppersmith--Winograd tensor and its `q + 2` border-rank degeneration;
- classical first-power and tensor-square CW analyses;
- Alman-style recursive frameworks;
- the repeated-region-orientation paper and its numerical certificate.

A client's constants, support tables, optimizer schema, or theorem-specific indexing conventions
must not leak into the reusable layers.

The dependency direction is therefore:

```text
Mathlib / stable CSLib APIs
            |
            v
Tensor core --> generic combinatorics/analysis --> MM theory
                                                    |
                                                    v
                                      regression and paper clients
```

## Reference theorem ladder

[He and Williams's CS 6810 notes](https://www.cs.cornell.edu/courses/cs6810/2023fa/Matrix.pdf)
give a useful short route through the classical theory: bilinear algorithms, tensors, border rank,
Bini interpolation, Schönhage's asymptotic sum inequality, and the two Coppersmith--Winograd
constructions. We use that order as a pedagogical roadmap and as a checklist for regression
results.

The notes are not the normative source for theorem statements. Some displayed claims use
expository shorthand or contain typographical errors. In particular, the reusable library must
prove submultiplicativity of general tensor rank and border rank, not assume multiplicativity; the
stronger identities needed for matrix-multiplication tensors come from explicit reindexing
equivalences. Exact hypotheses and constants are checked against the primary papers. For
Schönhage's inequality, Theorem 7.1 of the original paper is authoritative: total rectangular
matrix-multiplication tensors work over arbitrary fields, while genuinely partial multiplication
pieces require the separate infinite-field hypothesis.

The intended theorem ladder is below. Status describes the repository today: **proved** means the
literature-facing theorem has no project proof obligation; **partial** means reusable pieces or a
conditional client exist; **planned** means the row is deliberately still absent; and **not
adopted** marks an expository claim or historical detour that should not become a library theorem
in the form stated in the notes. Keeping this crosswalk current is part of the design contract.

| Notes | Stage | Reusable result or regression theorem | Status | Intended home |
| --- | --- | --- | --- | --- |
| Definitions 2.2--2.4, Fact 2.9 | Semantics | Bilinear maps, length-`r` bilinear algorithms, and their equivalence with rank-`r` trilinear tensor decompositions | Proved, both directions, over a commutative semiring, including the matrix-multiplication corollary | `MatrixMultiplication/BilinearAlgorithm.lean` |
| Proposition 2.7 | Semantics | Equivalence between the arithmetic-complexity definition of `omega` and the tensor-rank growth definition used internally | Proved in both directions. Forward: recursive block compilation with exact multiplication counts, padding, and the exponent-level statement (any `tau > omega` admits straight-line programs of total cost `O(n^tau)`). Converse, over an infinite field: a program with `M` multiplication gates gives a bilinear algorithm of length at most `2M`, so `omega_le_iff_exists_straightline` is the equivalence | `MatrixMultiplication/RankComplexity.lean`, `MatrixMultiplication/RankComplexityRecursion.lean`, `MatrixMultiplication/RankComplexityConverse.lean` |
| Lemma 2.6 | Semantics | Conciseness and the maximum-dimension lower bound for tensor rank on all three legs | Proved basis-free through dual contractions | `Tensor/Concise.lean` |
| Definition 2.11, Lemma 2.8 | Exact algorithms | Matrix-multiplication tensor definition, all leg permutations, rectangular external-product law, restriction by dimension, and rank submultiplicativity | Proved | existing tensor and matrix-multiplication modules |
| Proposition 2.1, Theorem 2.12 | Exact algorithms | A rank-`r` algorithm for `⟨q,q,q⟩` implies `omega <= log r / log q`; rectangular symmetrization gives the corresponding `(m*n*p)^(omega/3)` inequality | Proved for the rank-based `omega` | `MatrixMultiplication/Exponent.lean` |
| Section 2.1 | Exact client | Strassen's seven-term decomposition and exponent bound | Proved | `AlgebraicComplexityClients/Strassen/` (intended; currently `Examples/Strassen.lean`) |
| Lemma 2.13, Section 2.5 | Historical clients | Trilinear aggregation/Pan and other concise exact decompositions | Planned, after the semantic bridge | downstream clients |
| Definition 3.1, Theorem 3.3 | Approximation | Constructive polynomial degeneration, degree-aware border rank, powering, coefficient interpolation, and Bini's transfer from border rank to `omega` | Proved | tensor degeneration modules and `MatrixMultiplication/BiniInterpolation.lean` |
| Section 3.1 examples | Approximation clients | Bini's five-term partial `2 x 2` degeneration and, later, the 21-term `3 x 3` APA algorithm | Proved for the five-term client end to end: the Bini--Capovani--Romani--Lotti border certificate (`BorderRankLEAt 5 1`), the exact-rank-six upper certificate, the zeroing degeneration from the total tensor, and via Schönhage's partial τ-theorem the unconditional exponent bound `omega < 2.695` over any infinite field; the 21-term APA client remains | `Examples/Bini.lean`, `MatrixMultiplication/PartialAsymptoticSum.lean` |
| Proposition 3.2 | Approximation semantics | Comparison of exact rank with border rank in a fixed ambient space | Not adopted verbatim: the notes suppress the dependence of the comparison constant and the hypotheses needed to obtain a uniform degree bound; the constructive degree-aware interpolation theorem used by Bini is proved | tensor interpolation modules; revisit only against a primary source |
| Theorem 3.4 | Lower bounds | A concise degeneration has border rank at least the largest leg dimension | Proved: border-rank certificates bound every concise leg dimension via a determinant-free leading-coefficient span argument, with matrix-multiplication border-rank corollaries | `Tensor/BorderConcise.lean` and `MatrixMultiplication/BorderConcise.lean` |
| Beyond the notes | Lower bounds | Substitution-method rank lower bounds, culminating in Winograd/Hopcroft--Kerr `rank ⟨2,2,2⟩ = 7` over every field; slice rank with Tao's diagonal lemma as the finite core of laser-method barrier arguments | Proved: `⟨2,2,2⟩` bounds `≥ 5`, `≥ 6`, and the exact `= 7` (via the Bläser--Christandl--Zuiddam substitution argument), general `rank ⟨n,n,n⟩ ≥ 2n² − n`, Koszul flattenings, border-rank conciseness, the slice-rank calculus with `sliceRank(diag n) = n`, and the AVW barrier program (1810.08671): the independence number and its asymptotic version as an instance of the Fekete engine, Lemma 4.3, Lemma 4.4 (`Ī⟨m,n,p⟩ = mnp/max`), the Galactic method with Schönhage soundness, Theorem 4.1 / Corollary 4.3 (for the coordinate galactic exponent — AVW conflate it with the abstract one), Theorems 5.1--5.3 and Corollary 5.1, Lemma 6.1, the Sawin-conditional Theorem 6.1, Theorem 7.2, Lemma 7.2 for all `q ≥ 6`, and Theorem 7.1 in full: a universal constant `c ≥ 2 + 1/15000` below which the Galactic method cannot push `omega` through any generalized CW tensor, sharpened to `c ≥ 2 + 27/1000` by the entropy bound (`two_add_le_avwTheoremSevenOneConstant`, `two_add_le_avwTheoremSevenOneSharpConstant`; tracked in `BARRIER_FRAMEWORK.md`) | `Tensor/SubstitutionMethod.lean`, `Tensor/SliceRank.lean`, `Examples/SmallMatrixLowerBounds.lean`, `Examples/WinogradLowerBound.lean`; the AVW barrier program lives in `Examples/GeneralizedCoppersmithWinograd{Barrier,SharpBarrier,UniversalBarrier,GalacticUpper}.lean`, `Examples/{LowerTriangular,GroupTensor}Barrier.lean`, `Examples/CoppersmithWinogradDepthOneRateBarrier{,Arithmetic}.lean`, and `MatrixMultiplication/{GalacticMethod,IndependenceBarrier,CornerBarrier,UniversalSliceRankBarrier}.lean` |
| Beyond the notes | Universal method | `MatrixMultiplication/UniversalMethod.lean`: `universalExponent` (ω_u, single square target, all degenerations), `ω ≤ ω_u ≤ ω_g^{sq}`, Proposition 4.3 (one MM tensor w.l.o.g.), and Theorem 5.1 / Corollary 5.2 (`2/s ≤ ω_u`) of Alman's thesis in abstract-measure form, instantiated at S̃ in `MatrixMultiplication/UniversalSliceRankBarrier.lean` (unconditional: the named obligation `SliceRankDegenerationMonotone` is discharged over every field by `Tensor.sliceRankDegenerationMonotone_holds` in `Tensor/SliceRankDegeneration.lean`); Theorem 5.3 for S̃ in `Tensor/SliceRankBlockEntropy.lean`; Theorem 5.7 proved for `CW_{q,σ}` with certified constant `13/6` (thesis 2.16805), in `Examples/GeneralizedCoppersmithWinogradUniversalBarrier.lean`. Proved. |
| Fact 3.5, Theorem 3.6 | Historical direct sums | A concrete border-rank nonadditivity example and the old conditional argument from exact-rank additivity | Not adopted as a dependency: exact-rank additivity is false in the intended generality; a small explicit nonadditivity example may still be a downstream regression client | optional historical clients |
| Proof of Theorem 3.7 | Direct sums | Independent indexed sums, type extraction, full cyclic symmetrization, and tensor substitution/compression | Proved | tensor indexed modules and `MatrixMultiplication/Compression.lean` |
| Theorem 3.7 | Direct sums | Schönhage's asymptotic sum inequality with proved field hypotheses and no rank-additivity assumption | Proved | `MatrixMultiplication/AsymptoticSum.lean` |
| End of Section 3.3 | Direct-sum client | Schönhage's displayed `⟨3,1,3⟩ + ⟨1,4,1⟩` ten-term degeneration and `omega < 2.6` consequence | Proved | `AlgebraicComplexityClients/Schonhage/` (intended; currently `Examples/Schonhage.lean`) |
| CW90 value formalism | Regularized extraction | A relation-parametric finite weighted direct-sum engine for powers of the three-orientation symmetrization; separate partitioned-zeroing, conventional exact-restriction `V_τ`, and polynomial-degeneration values with promotion theorems; direct-sum and tensor-product lower bounds; and the precisely hypothesized value-to-`omega` theorem | Partial: the normalized semantic polynomial-degeneration relation, finite cyclic extraction sequences, and Schönhage soundness are proved; the conventional `τ`-parameterized wrappers, promotion maps, and generic algebraic laws are being factored out | `MatrixMultiplication/CyclicLaserVolume.lean`, `MatrixMultiplication/Laser.lean`, and the planned value-facing module |
| Section 4 prerequisites | Laser foundations | Partitioned supports, projection-closed zeroing, word types, multinomial counts, entropy estimates, finite affine hashing, progression-free filtering, good-seed averaging, isolated targets, and the legwise-independent direct-sum interface | Proved for the classical CW clients; the generic recursive interface/hole-repair machinery is proved, while its concrete paper instantiations remain downstream work | reusable tensor, combinatorics, probability, analysis, and generic MM layers |
| Theorem 4.1 | First laser client | The three-constituent easy tensor, border rank `q + 2`, extraction, and the classical bound near `2.41` | Proved: the finite extraction, balanced multinomial lower bound, prime-field Behrend hashing, explicit subexponential loss removal, scalar rate inequality, and exact-rational `q = 8` conclusion `omega < 2.41` are checked | `AlgebraicComplexity/Examples/CoppersmithWinogradEasyHashing.lean` |
| Theorem 4.2 | CW client | The six-constituent `CW_q`, border rank `q + 2`, first-power extraction, and the classical bound near `2.3872` | Proved: exact rational joint/marginal types, semantic zeroing, typed-fiber competitor bound, prime-field Behrend hashing, direct-sum extraction, Schönhage inequality, proportional multinomial estimate, subexponential loss removal, and exact-rational conclusion `omega < 2.3872` | `Examples/CoppersmithWinogradFirstPowerHashing.lean` and `Examples/CoppersmithWinogradFirstPower.lean` |
| CW journal Sections 6--7 | Classical tensor-square client | The exceptional `112` value estimate used in the original `omega < 2.375477` theorem | Proved for the endpoint: `Examples/CoppersmithWinograd2375477.lean:343` `coppersmithWinograd_square_omega_lt_2375477 : omega K < 2375477 / 1000000`, asserted in `AxiomAudit/CoppersmithWinograd2375477.lean`. It follows the modern value formulation: form the product of all three cyclic orientations, impose the product profile on its exact 64-address support, and apply ordinary three-leg hashing; visible entropy `H(X)+H(Y)+H(Z) = 2+H(Z)` gives the required `side^2 * Z` value lower bound, and Schoenhage's inequality converts it. The supporting pieces are proved too: the four checked base constituents; the exact `L,L,G,G` word dimensions and entropy rates; two-leg prime hashing; simultaneous shared-Z grouping; and the generic cyclic C-tensor-to-matrix-multiplication degeneration. The older shared-Z flattened route --- copy base `side^2 / Z`, hence shared-Z entropy with a minus sign, and unable to prove even `omega < 2.38` --- remains a verified explanatory client, not the public formulation of the endpoint. | `Examples/CoppersmithWinograd2375477{,Arithmetic}.lean`, `Examples/CoppersmithWinograd112SymmetricProfile.lean`, `Examples/CoppersmithWinogradSquare{,Counting,Entropy,Symmetry,SymmetryDefs,Assembly,Constituents,Hashing,OrdinarySymmetry,OuterCounting,OuterGrowth,TauValueAssembly,TauValueGrowth,112TauValue,112TauValueGrowth,211TypedLeaf}.lean`, `Examples/CoppersmithWinograd112{Counting,CTensor,Global,GlobalCounting,TypedLeaf,LeafInterface,Asymptotic,CyclicValue,CyclicValueFormula}.lean`, `MatrixMultiplication/CyclicLaserVolume.lean`, and `MatrixMultiplication/CTensor*.lean` |
| Beyond the notes | DWZ level two | Duan--Wu--Zhou 2023, section 6.3: the second-power bound from the squared Coppersmith--Winograd tensor `CW_6^{otimes 2}` | Proved, unconditionally and over any field: `Examples/DuanWuZhouLevelTwoOmegaBound.lean:159` `omega_lt_2374631 (K : Type u) [Field K] : omega K < 2374631 / 1000000` | `AlgebraicComplexity/DuanWuZhouLevelTwo.lean` (umbrella; its own `lean_lib` target, see Build performance) and `Examples/DuanWuZhouLevelTwo*.lean` |
| Beyond the notes | Later clients | CW tensor-square analyses, recursive laser frameworks, combination-loss analyses, and current certificate-driven bounds | Partial: complete-split distributions, exact profiles, canonical child concatenation, parent mixtures, exact profile selection, basis-free power flattening, heterogeneous family assembly, full sample permutations, generic and paper-cell compatibility soundness, pooled-all cancellation, arbitrary-orientation transport, native recursive CW block legality, sparse parent consistency, exact conditional-type factorization, arbitrary-alphabet proportional multinomial entropy bounds, all binary interface-division multiplicity cases, finite recursive division-tree assembly, finite three-leg shuffling, exact repair trees with copy count at most `7^height`, and subexponential repair loss are proved; generated `Split_avg` realization, cell-wise selector matching, identification of concrete hashing competitors, certificate-specific division-tree instantiation, and paper-specific repair plans remain downstream obligations | `Tensor/PowerCoherence.lean`, `Tensor/PowerFamily.lean`, `Tensor/PartitionedPowerRelabeling.lean`, `Tensor/CompatibilityZeroing.lean`, `Tensor/HoleRepair*.lean`, `Combinatorics/ConditionalWordType.lean`, `Analysis/ProportionalMultinomial.lean`, `Combinatorics/HoleRepair.lean`, `Analysis/HoleRepairGrowth.lean`, `Probability/SparseParentConsistency.lean`, `MatrixMultiplication/InterfaceTensor*.lean`, `MatrixMultiplication/MoreAsymmetryCompatibility*.lean`, and downstream clients |

The exact-rank additivity conjecture is useful historical motivation in the notes, but it is false
in the generality once hoped for and is not an assumption in this library. Schönhage's theorem is
the reusable replacement. Likewise, a numerical bound in the notes becomes a regression theorem
only after its displayed degeneration, extraction count, analytic limit, and final arithmetic are
all checked in Lean.

The missing rows in this table are an intentional regression backlog, not hidden prerequisites for
the current paper client.  In particular, the bilinear-algorithm bridge and Bini's small displayed
APA example are high-value tests of the public API; Pan-style historical decompositions should be
added only after that semantic bridge is stable.  Conversely, recursive CW and combination-loss
work stays on the paper-client path even though it lies beyond the scope of the notes.

Coverage follows the notes selectively, not mechanically. Reusable semantic theorems and compact,
self-contained decompositions become library milestones or regression clients. Conditional
arguments with a now-false premise, claims whose displayed hypotheses are incomplete, and the
Section 5 optimization leaderboard do not automatically become proof obligations. They are added
only when they test a reusable API or when a later paper client actually needs them.

## Core representation choices

### Abstract tensors for structural theorems

The canonical representation is

```lean
inductive Leg
  | X | Y | Z
  deriving DecidableEq, Fintype

Tensor3 K V := PiTensorProduct K V
```

where `V : Leg -> Type*`. The leg spaces stay in the type. Structural theorems use abstract tensor
products so that change of basis, functoriality, direct sums, and tensor powers remain natural.
Coordinate permutations use the single general type `Equiv.Perm Leg`; named cycles and swaps are
only convenience values. This is already the representation used by the current core.

Trilinear tensors should not be rebuilt as raw coefficient arrays. Mathlib supplies the tensor
product and direct-sum algebra.

### Coordinates for explicit certificates

Concrete decompositions and degenerations may use finite coordinate spaces and explicit lists of
terms. Coordinate results must cross into the abstract API through proved linear equivalences or
restriction/degeneration certificates. A computation over arrays is not by itself a theorem about
the abstract tensor.

### Constructive degeneration

The primary notion of border degeneration is a polynomial one-parameter certificate with an
explicit leading coefficient. We avoid defining degeneration first as Zariski-orbit closure: the
constructive form matches published CW certificates, supports evaluation, and avoids unnecessary
algebraic geometry.

Degree-aware certificates are retained when powers or interpolation depend on the leading degree.

### Relations and direction

`Restricts T S` means that maps on the three legs carry source `T` to result `S`. The optional
notation `S ⪯ T` follows the order-theoretic direction. APIs must document the direction rather
than relying on notation alone.

Use the weakest mathematically correct relation:

- `Isomorphic` for invertible changes of coordinates;
- `Restricts` for exact legwise maps;
- `PolynomialDegeneratesAt d` when leading degree matters;
- `PolynomialDegenerates` when it does not;
- `RankLE` and `BorderRankLE` for constructive upper-bound witnesses.

Do not replace one relation by a stronger assumption merely because it shortens a proof.

## API principles

### General hypotheses

Use the weakest algebraic assumptions supported by the proof. Basic tensor algebra is generally
over a commutative semiring. Cancellation, subtraction, interpolation, and asymptotic theorems may
require rings, domains, or fields. Field and positivity assumptions in Schönhage-style results
must be explicit.

Avoid global finite-dimensional assumptions. Introduce `Fintype`, bases, or finite-dimensionality
only in modules that need coordinates, cardinalities, or optimization.

### Semantic theorem versus certificate

Separate three things:

1. the semantic mathematical statement;
2. a reusable certificate structure sufficient to prove it; and
3. a concrete certificate instance for a named result.

For example, a generic laser theorem consumes an extraction-rate witness; a CW client constructs
that witness. This keeps theorem statements readable and prevents optimizer data from becoming
part of the foundational API.

### Named proof obligations

An unproved deep result may be represented as a `Prop` definition so downstream interfaces can be
designed, but it must be described as a proof obligation. It must not be introduced with `axiom`,
hidden in a typeclass instance, or reported as proved, and it must not be parked on a gate's
grandfather list instead of being proved: those lists record debt that predates the rule, every one
of them is append-blocked and may only shrink, and adding an entry needs the same review as
changing the rule. The final theorem should expose every such hypothesis.

### Stable declarations

Public definitions should have:

- a docstring explaining mathematical meaning and direction;
- predictable namespace-qualified names;
- arguments ordered from ambient data to objects to witnesses;
- simp lemmas for constructors and maps where they terminate reliably;
- relation-level corollaries in namespaces such as `Restricts`, `Isomorphic`, `RankLE`, and
  `BorderRankLE`.

Generic names are checked before they are written. Before adding a lemma at `Tensor/` or
`Combinatorics/` level, scan the whole tree for its intended fully qualified name with
`git grep --untracked -w <name>`; plain `git grep` skips every file not yet committed, which is
exactly where collisions hide. Two failures recur: the same public name declared in two files, which
breaks the build the moment a module imports both, and one short name in two namespaces that a third
module opens, which yields an ambiguous term. `scripts/check_declaration_collisions.sh` reports
both, but CI runs it at WARN level and it never fails the build, so it catches a collision only for
whoever reads the log. Prefer instantiating a committed lemma to restating a special case of it; a
name that collides is usually a lemma that already exists.

Prefer small composable theorems over a theorem whose statement bakes in a paper's full pipeline.
Avoid project-wide notation unless it is conventional and locally scoped.

### Documentation and proof narration

Documentation is part of the public API, rather than a cleanup step to postpone until the proof is
finished. Every Lean source file should begin with a module doc comment (`/-! ... -/`) that tells a
mathematical reader:

- what objects the file defines;
- which principal results it proves;
- how it fits into the layer and dependency structure above;
- the main proof or certificate strategy when that is not immediate; and
- important non-goals or obligations deliberately left to a later module.

Every public theorem or lemma should have a doc comment immediately before its declaration. The
comment must include a human-readable mathematical statement, even when the Lean statement is
already short. A routine computation or simp lemma needs only one sentence. A substantial theorem
should additionally include a short `Proof sketch:` paragraph explaining the main reductions,
invariant, reindexing, or explicit certificate. Proof sketches should explain the mathematics and
the structure of the formal argument; they should not merely narrate tactic calls line by line.

Private or local helper lemmas also need a comment when their purpose or proof idea is not obvious
from the surrounding proof. In particular, comments should spell out the direction of relations
such as restriction and degeneration, identify which tensor is the source and which is the target,
and distinguish a proved theorem from a conditional interface or named proof obligation. Comments
must be updated when a statement's hypotheses, scope, or proof status changes.

Documentation review is therefore part of the acceptance test for a new module:

1. the module overview gives a useful map of its definitions and results;
2. theorem comments can be read independently of Lean syntax;
3. nontrivial proofs have a mathematical proof sketch; and
4. no comment claims more than the checked declaration proves.

### Imports

Import the narrowest module that provides the needed declarations. Every file should compile on
its own. Umbrella modules may collect a layer, but implementation files should not import an
umbrella module merely for convenience.

Cycles between tensor algebra, matrix-multiplication theory, and examples are design errors.

### Build performance

Use the smallest relevant target while developing, then run the public targets at a coherent
milestone. The default target intentionally excludes regression and paper clients:

```text
lake build AlgebraicComplexity.Tensor.Concise
lake build AlgebraicComplexity.MatrixMultiplication.AsymptoticSum
lake build
lake build AlgebraicComplexityClients MatrixMultiplication
lake build AlgebraicComplexity.DuanWuZhouLevelTwo  # leaf umbrella; see below
lake build MatrixMultiplicationCertificate  # opt-in generated exact tables
```

`AlgebraicComplexity.DuanWuZhouLevelTwo` is a `lean_lib` target of its own because its umbrella is
a leaf that no other library imports. Without a target its modules would be compiled only as a
side effect of the focused `AxiomAudit/` companions, which puts them inside the build but outside
every `#axiom_census` closure; `AxiomAudit/CensusAll.lean` therefore names it explicitly, as it
does `Frontier`.

When a module is slow, profile it before changing tactics, through
`scripts/lean_check_lowmem.sh path/to/File.lean --profile`: it caps the compiler and serializes on
the worktree build lock, where a bare `lake env lean --profile` keeps a resident Lake process
beside the compiler and competes with whatever else this tree is building. Import time and proof
elaboration are reported separately. Prefer narrow imports; one
broad normed-asymptotics import previously dominated `Exponent.lean` despite sub-second tactic
time. For small finite identities over a generic ring, prefer a finite certificate over `Int`
plus a proved scalar-cast bridge over dozens of repeated symbolic `simp` branches. Use
kernel-checked `decide` for genuinely tiny closed finite facts. Introduce `native_decide` only
after profiling demonstrates a material need, and record its trust impact in the axiom audit; the
current `AlgebraicComplexity` tree needs neither `grind` nor `native_decide`.

Large generated paper certificates belong in a separate opt-in umbrella.  The current
`MatrixMultiplicationCertificate` checker uses synchronous elaboration and row-local `norm_num`
proofs to keep peak memory bounded and to avoid the native-decide soundness axiom.  The target
imports the level-four analytic tables, about 10,500 generated modules, so its cold build takes many
hours; it is not part of the default or ordinary paper-library targets, and CI builds only a slice of
the certificate tier on each push (`scripts/certificate_smoke_targets.sh`).

Avoid asking definitional equality to normalize a `Finset.filter` whose predicate computes over a
symbolic word length. In dependent APIs, expose membership lemmas such as `mem_select_support` and
name the exact indexed family expected by a theorem. This prevents type checking from expanding
the whole decidability program merely to discover that two support subtypes coincide. Lake's
reported job count includes cached transitive dependencies; distinguish that count from modules
actually marked `Built` before diagnosing a rebuild.

Every timing and memory figure in this document is a measurement, not a property of the code: it is
quoted only with the host and the date it was taken on, and re-measured before it is cited
anywhere else. As a baseline measured in August 2026 — re-measure before quoting it; the tree has
grown a great deal since — profiling the complete first-power CW extraction after its completion
reports roughly 30 seconds in import initialization, 1.6 seconds in all tactics, and 0.4 seconds
in elaboration; its slowest individual tactic is a 0.4-second `nlinarith`. The numeric
client likewise spends about 24 seconds importing and 1.6 seconds in exact `norm_num`. There are no
`grind` or `native_decide` calls in the project; the nine `native_decide` occurrences a source scan
finds are all prose explaining why it is not used. Optimize the dependency graph before rewriting
these proofs. A fully warm default build on the same machine is about five seconds; a changed
umbrella or high-fan-out module must pay Lean's import initialization cost again.

`decide` splits by tree. In the `AlgebraicComplexity` tree its calls are closed facts over tiny
types and are not visible in the profile. **The generated certificate tree is different**, and the
difference is memory rather than time: `MatrixMultiplication/Generated/` carries `decide +kernel`
reductions whose cost sets the machine requirement for the build. One of them, in
`Generated/SimplifiedVolumeRecurrenceZeroFour1.lean`, measured 133 GB, and the
`SimplifiedVolumeRecurrenceEdge*` family 7.3--19.6 GB per module; each was discovered by running a
16 GB machine out of memory, hours in, rather than by any gate. They are governed by "Reduction and
elaboration budgets" below and gated by `scripts/check_decide_budget.sh`. A scan for that cost has
to read proof bodies rather than declaration lines: the generated `opaque … Checked` declarations
carry their kernel work in `· decide` bullets several lines below the `opaque` keyword — see
`MatrixMultiplication/Generated/LevelFourTopRaw0.lean:17` — so a grep for `:= by decide` finds none
of them, and no `decide` is small until it has been measured.

### Reduction and elaboration budgets

These limits are normative for new modules, and both are mechanically gated.

- **No `set_option maxHeartbeats 0`, and no raise of the bound, without a recorded measurement.**
  A module that needs more than the default records the figure it measured — elapsed time and peak
  resident size, from one Lean process — in a comment beside the option.
  `scripts/check_heartbeat_governor.sh` fails any tracked `.lean` file whose text sets
  `maxHeartbeats` to an all-zero numeral; the existing carriers are listed in
  `scripts/heartbeat_governor_grandfathered.txt` so that only a new one fails.
- **No single `decide`, `decide +kernel`, or `decide_cbv` may become the project's memory
  boundary.** A reduction whose cost sets the machine requirement for building a paper is a design
  error however small its source file: `Generated/SimplifiedVolumeRecurrenceZeroFour1.lean` is 2 KB
  and needed 133 GB, because its proof inlines sixteen payload modules before reducing.
  `scripts/check_decide_budget.sh` enforces this two ways. Where a measurement exists it is
  authoritative: `scripts/decide_memory_budget.tsv` records real per-module peak resident size, and
  a module over the budget fails (default 6000 MB, half a 16 GB runner, because CI elaborates two
  modules at once). Where none exists the proxy is the literal numeric payload one reduction drags
  into its goal *through imports*, over a 12,000-digit threshold. The 62 pre-existing violations
  are listed in `scripts/decide_budget_grandfathered.txt`.
- **A memory figure is measured with exactly one Lean process on the machine.** A peak-resident
  number taken while another build was running is not a measurement. Produce it with
  `scripts/lean_check_lowmem.sh` (or `scripts/lake_serial.sh`) and append it to
  `scripts/decide_memory_budget.tsv`. Ordinary development may run several compilers at once
  (`lake -j 4`, say, on a 16 GB machine); that is the concurrency a budget measurement must be
  taken *outside* of, not inside.
- **Case splits over large finite types go through the smallest computable address type**, not
  through tensor-level `fin_cases`. Decide a statement about words, indices, or block addresses;
  do not ask the kernel to enumerate the tensor built over them.
- **Measurement (the reference build machine, 2026-09-06, Lean v4.33.0-rc1, one process):**
  `opaque inputs_eq` in
  `MatrixMultiplication/Generated/TotalQuotientExponentLevelTwoRecurrenceChunk0.lean`, as then
  generated, failed with `(kernel) excessive memory consumption` at `-M 4000` and compiled in
  19.6 s at `-M 32000`, the cap then used for the certificate-tier census. A certificate-tier
  census must run at that cap; a 4 GB cap is not enough for the generated tables. The table has
  since been regenerated in grouped form and elaborates at `-M 4000`; its sibling
  `TotalQuotientExponentLevelTwoRecurrenceChunk1.lean` has not been split and still needs the
  higher cap.

Both grandfather lists are append-blocked and may only shrink. An entry that no longer violates is
reported as a stale-entry notice, never a failure, so the commit that pays debt down is not the
commit that goes red; an entry that gets measurably worse fails. Adding a line to silence a gate on
new work is a policy violation, not a workaround.

### Build traps

Each of these has cost a real build cycle in this repository.

- **`LEAN_PATH` roots resolve by directory presence.** An olean seed cannot be consumed as a second
  `LEAN_PATH` entry once the output tree already contains the same top-level directory: the first
  root carrying that directory wins and the seed is silently invisible, with no error. A seed must
  live *inside* the consuming output tree. Copy it (`cp -a`/`rsync`) or symlink a pristine seed;
  never hard-link a package or toolchain tree that another build uses.
- **Plain `lean` needs an explicit `--root`.** Without `--root`, Lean derives the main module name
  from the current directory (`Lean/Util/Path.lean`, `Lean/Shell.lean`), and that name is the base
  of the deterministic serialization of generated names, so an OLean compiled from a scratch
  directory differs byte-for-byte from the same source compiled at the package root even though
  every input is identical. Every invocation meant to reproduce a Lake-built OLean passes
  `--root` set to the source root.
- **The universes of a powered source are not the universes of its source.**
  `Tensor.power T (stride * r)` has type `Tensor3.{u, max v u} K (PowerSpace K Source …)`, not
  `Tensor3.{u, v}`. A structure that packages a powered tensor must leave its universes implicit:
  an explicit `Foo.{u, v, z}` fails with an application type mismatch or "too many explicit
  universe levels". Mirror the sibling declaration and do not annotate. The same trap has a design
  half: independent factor universes leave a product-family level underdetermined, so fix the
  universe explicitly at the point of *definition*, where the choice is visible and callers can
  take the maximum. A named `Prop` obligation that quantifies over a `Type u` family cannot be
  silently re-universed once clients have instantiated it, so its universe-explicit packaging may
  have to survive even after the polymorphic statement is proved.
- **A memory figure is measured with exactly one Lean process** — the unit of the decide budget;
  see "Reduction and elaboration budgets" above.

## Dependency policy

Mathlib is the foundational dependency. Existing CSLib APIs may be used where they are a natural
fit; this local repository currently uses `Cslib.Probability.PMF` in an optional hashing bridge.
Code intended for contribution to CSLib must be organized so it can live inside CSLib without a
dependency cycle.

Optional external libraries sit behind explicit adapter modules, preferably under:

```text
AlgebraicComplexity/Adapters/PFR/
AlgebraicComplexity/Adapters/LeanCert/
AlgebraicComplexity/Adapters/CompPoly/
AlgebraicComplexity/Adapters/CSLib/
```

An adapter translates an external representation or theorem into a local semantic statement.
Downstream theory should consume that local statement rather than depend on details of the
external API. `Combinatorics/HashingProbability.lean` now consumes CSLib through
`Adapters/CSLib/ProbabilityPMF.lean` rather than importing it directly.

External research libraries are adopted selectively:

- PFR is a likely source for Shannon entropy, conditional entropy, mutual information, and KL
  divergence during the hashing proof;
- LeanCert may be useful for proof-producing numerical bounds, subject to declaration-by-
  declaration axiom audits;
- CompPoly is useful if its executable polynomial layer adds functionality beyond the existing
  constructive degeneration API;
- CSLib's PMF library is useful for probabilistic hashing formulations.

An external dependency should be added only when it removes a meaningful body of maintenance or
provides a substantially stronger verified API. Record the exact compatible tag and audit the
specific imported declarations. Optional paper clients may carry dependencies that would be
inappropriate for the upstreamable core.

## Trust and verification policy

Committed Lean source must contain no project `sorry`, `admit`, declared `axiom`, or `opaque`
stand-in for a theorem. There is no exemption.

`opaque` itself is a definitional-opacity mechanism and may be acceptable
for an intentionally opaque computable definition after review. Run the hard failure scan and the
separate review scan:

```bash
rg -n '\b(sorry|admit|axiom)\b' \
  AlgebraicComplexity AlgebraicComplexityClients.lean MatrixMultiplication -g '*.lean'
rg -n '\bopaque\b' \
  AlgebraicComplexity AlgebraicComplexityClients.lean MatrixMultiplication -g '*.lean'
lake build
```

Prose occurrences explaining that something is not an axiom are harmless and should be reviewed
manually.

One blessed `opaque` pattern is in active use and is *not* a stand-in for a theorem. The generated
certificate tables under `MatrixMultiplication/Generated/` carry roughly 6,460 declarations of the
form `opaque <name> : <statement> := by <proof>` — mostly exact normalization equations such as
`LogLinearForm.normalize (...) = expectedForm`, plus bundled `ExactNatArray` literals whose size and
checksum fields are proved in place. In every case a real term is supplied and is elaborated and
kernel-checked at build time exactly as a `theorem` or `def` would be; `opaque` only seals the
result so that downstream elaboration never unfolds a multi-thousand-entry literal while checking
an aggregate. No axiom is introduced, and the `AxiomAuditCertificate` target covers these
declarations. The pattern is permitted only under `Generated/`, and only with a term supplied: a
bodiless `opaque foo : P` *is* an unproved postulate and remains forbidden. The
`rg -n '\bopaque\b'` scan above is therefore advisory rather than a hard failure — its hits under
`Generated/` are expected, and are cleared by confirming that each has a `:= by` body.

The census closes the one hole a source scan cannot: `scripts/trust_scan.sh` matches `axiom` only
in declaration position, i.e. anchored at the start of a line, and Lean's command parser is
whitespace-insensitive. Both `/-- docstring -/ axiom sneaky : False` and
`theorem harmless : True := trivial axiom sneaky : False` therefore elaborate as ordinary axiom
declarations while starting their line with something else; each was compiled against the scan to
confirm it passes. `AxiomAudit/Census.lean` defines `#axiom_census`, which walks
`Environment.constants` and fails elaboration if any constant whose originating module belongs to
this repository is an `axiom`, or depends on one outside the allowlist. `AxiomAudit/CensusAll.lean`
runs it over the ordinary targets and `AxiomAuditCertificate/Census.lean` over the generated
certificate cone; `AxiomAuditCertificate/CensusQ20.lean` is the second recognized certificate-tier
root, censusing the q20 Total-Weight companions alone so that they can be rebuilt and checked
without the whole generated library in the closure.  `scripts/check_source_coverage.sh` additionally
fails if a module a library target builds lies outside every census closure, so the census's scope
cannot silently fall behind the build's. **The census is the authority for this policy and the grep
is a fast pre-filter** — a regex over source text can always be evaded, a walk over what the kernel
accepted cannot. The census prints its own coverage — declarations, project modules, elapsed time,
peak resident — on every run; read the figure there rather than from a frozen number here, and
regenerate its roots with `scripts/regen_census_roots.sh`. For scale, the tree tracks about 13,600
`.lean` files, about 11,350 of them under `MatrixMultiplication/Generated/`. The only axioms reached
are the three allowlisted ones.

For important imported theorems, use `#print axioms` in an audit file or scratch file and record
the result when it affects the trusted base. `Classical.choice`, quotient soundness, and standard
Mathlib axioms are different from an unproved project postulate; reports should distinguish them.

The standing audit is enforcing: `AxiomAudit.lean` uses the `#assert_axioms` command (defined in
`AxiomAudit/Command.lean`), which fails elaboration whenever an audited declaration depends on an
axiom outside `propext`, `Classical.choice`, and `Quot.sound`. Run it with `lake build
AxiomAudit`; the declarations living inside the generated certificate are covered by
the separate opt-in `lake build AxiomAuditCertificate`.

**Every declaration of a new module gets an `#assert_axioms` line in its `AxiomAudit/` companion —
theorems, defs, and instances.** An instance is the easy one to forget and the easy one to smuggle
an obligation through, because a theorem-only sweep never looks at it. The gate is narrower than
the rule: `scripts/check_assert_axioms_targets.sh` fails an assertion that names a constant which
does not exist, but it cannot see a declaration with no assertion at all. Coverage of the
declaration set is therefore a review obligation, not a mechanical one. Private declarations
cannot be named from a companion, so they are covered by the assertion of every public
declaration that references them (the axiom cone is transitive): the reviewer checks that each
private declaration is reachable from an asserted public one, and a private declaration reachable
from none is dead code and is removed before merge. The textual scan of `scripts/trust_scan.sh`
and the environment-wide `#axiom_census` cover every declaration regardless of visibility.

The companion lands in the same change as its module rather than as a follow-up: "green" means a
from-scratch rebuild of the module *and* its companion. Deleting or renaming one has a second
effect that is easy to miss — for a client tier that no library imports, the focused audits can be
the only roots that reach it, so the modules end up inside the build and outside every census
closure. The cure is a `lean_lib` target for the tier, not a companion doing duty as a build root;
`AlgebraicComplexity.DuanWuZhouLevelTwo` exists for exactly this reason, and
`scripts/check_source_coverage.sh` fails the remaining gap between what a target builds and what a
census covers.

Numerical claims require exact arithmetic or a proved enclosure. Floating-point or Python output
may generate a certificate, but Lean must verify the certificate and all rounding directions before
the result is called formalized.

Every named regression client should eventually provide:

- a theorem with the literature-facing statement;
- a source citation in its module documentation;
- a small axiom-audit smoke test;
- a targeted build command; and
- no dependence on unpublished or nonredistributable input data.

Every major semantic operation should also have a deliberately tiny client: zeroing one term of a
two-term tensor, multiplying rank-one tensors, summing one-dimensional tensors, a degree-one
polynomial degeneration, `⟨1,1,1⟩`, and small `CW_1`/`CW_2` instances. These tests catch relation
direction, associator, and leg-permutation errors before they are hidden inside a large proof.

Locally obtained papers belong in `papers/`, which is gitignored. Do not quote or commit material
that the repository has no right to distribute. For an older scan that is repeatedly used, prefer
adding a project-owned theorem-oriented companion under `papers/notes/`: a paraphrased `.tex` file
with normalized notation, precise printed-page references, proof dependencies, and a map to Lean
declarations or named remaining obligations. It is a research index, not a verbatim transcription
or a replacement for checking the primary source. Compile it once after edits so malformed formulas
do not silently accumulate; because `papers/` is ignored, neither source scan nor companion is part
of the distributable library.

## Module hygiene

These are the per-module requirements for new work, and most of them are mechanically gated. The
tree does not meet all of them everywhere; each gate carries a grandfather list recording the
standing debt, and every list is append-blocked and may only shrink.

Every new module carries:

- the four-line CSLib Apache-2.0 copyright header, starting at byte zero;
- a `/-! ... -/` module docstring that cites the paper it formalizes by `[BibKey]`;
- `set_option autoImplicit false`;
- an `AxiomAudit/` companion asserting every declaration, instances included, carrying the header
  and the guard itself;
- no `sorry`, no `native_decide`, no `decide` over a non-tiny type, no `set_option maxHeartbeats 0`
  without a recorded measurement, and no reduction that becomes the memory boundary (see "Reduction
  and elaboration budgets").

`set_option autoImplicit false` is the one item on that list with no gate behind it, and it earns
its place: an auto-bound implicit turns a missing import into a fresh universe-polymorphic
variable, so the module elaborates on its own and fails only when a real consumer appears. The
guard belongs in every new module and in every `AxiomAudit/` companion. The right long-term form is
a package-level `[leanOptions]` table in `lakefile.toml` setting `autoImplicit` and
`relaxedAutoImplicit` to false — the CSLib settings — rather than several hundred per-file lines;
that table does not exist today, so the per-file guard stands and review is what enforces it.

Run the `scripts/check_*.sh` gates before committing, and shrink a grandfather list rather than
grow it.

| gate | enforces | list, with entries at the time of writing |
| --- | --- | --- |
| `check_copyright_headers.sh` | the four-line CSLib header on every hand-written source | `copyright_headers_grandfathered.txt` (244) |
| `check_module_docs.sh` | a `/-!` overview on every hand-written source; `Generated/` excluded | none |
| `check_tensor_boundary.sh` | the `Tensor/` import boundary, both umbrella and directory | in-script: the five bridge edges above |
| `check_decide_budget.sh` | no reduction becomes the memory boundary (measurement first, payload proxy second) | `decide_budget_grandfathered.txt` (64), against `decide_memory_budget.tsv` |
| `check_heartbeat_governor.sh` | no all-zero `maxHeartbeats` in a tracked source | `heartbeat_governor_grandfathered.txt` (330) |
| `check_source_coverage.sh` | no module a library target builds falls outside every census closure | `source_coverage_grandfathered.txt` (150) |
| `check_assert_axioms_targets.sh` | every `#assert_axioms` target names a declaration that exists | `assert_axioms_dark_grandfathered.txt` (0) |
| `check_certificate_table_wiring.sh` | a module's quoted certificate agrees with the tables its proofs reference | `certificate_table_wiring_grandfathered.txt` (0) |
| `check_artifact_provenance.sh` | no tracked source imports a quarantined generated artifact | `artifact_provenance_quarantine.txt` |
| `check_frontier_improvement.sh` | a PR moving `frontierConstant` moves it down by at least `Frontier.recordDelta` | none |
| `check_declaration_collisions.sh` | declaration-name collisions; warn level, never fails the build | none |
| `trust_scan.sh` | no project `sorry`, `admit`, or declared `axiom`; advisory `opaque` review | none |

`scripts/heavy_audit_grandfathered.txt` (10) additionally records audit companions exempted from
the light-audit budget. Two checkers are Python — `check_decide_budget.py` and
`check_assert_axioms_targets.py` — and they are what the matching `.sh` wrappers run. Most gates
read only tracked files (`git ls-files`) or the committed tree itself (`git archive`, `git show`),
so an untracked or uncommitted local file is never scored as repository state; `trust_scan.sh`,
`check_module_docs.sh`, `check_tensor_boundary.sh`, and `check_declaration_collisions.sh` read the
files on disk, so run them on a clean checkout.

A module a gate reads as its root must therefore be tracked. A gate whose root is untracked passes
vacuously on a clean checkout, which is worse than no gate. The same discipline governs every module
path named in this document — a path that resolves only in a local working tree is scratch, not
library, and `ls` is not evidence. Nothing checks these inventories: a `check_design_inventory.sh`
diffing the backticked module names here against `git ls-files` is owed.

## Build and review workflow

The default build checks the reusable core and is deliberately kept quick enough for the normal
edit--compile loop:

```bash
lake build
```

The regression clients and current paper are independent targets. The ordinary check is:

```bash
lake build AlgebraicComplexity AlgebraicComplexityClients MatrixMultiplication
lake build AxiomAudit
```

It is not the full check. `lakefile.toml` declares eight `lean_lib` targets, and three of them are
outside the two lines above: `AlgebraicComplexity.DuanWuZhouLevelTwo` (a leaf no library imports),
`Frontier` (built by CI on every record PR, and also a leaf by design), and `AxiomAuditCertificate`
(the generated certificate cone). The full check adds:

```bash
lake build AlgebraicComplexity.DuanWuZhouLevelTwo Frontier
lake build AxiomAuditCertificate
```

During development, compile the edited file and then its client layer:

```bash
lake env lean AlgebraicComplexity/Tensor/IndexedDirectSum.lean
lake build AlgebraicComplexity
lake build AlgebraicComplexityClients
lake build MatrixMultiplication
```

On memory-constrained machines, prefer these targeted builds over rebuilding all three umbrellas
at once. Lean elaboration is memory-intensive, and several independent Lake jobs can otherwise
push a 16 GB machine into compressed memory and swap. A long elapsed time shared uniformly by
many small modules is usually resource contention; use `lean --profile` on an individual file
before attributing it to a tactic.

Before considering a core API stable:

1. build every affected downstream client;
2. check for accidentally strengthened hypotheses;
3. verify the module overview and human-readable theorem comments against the documentation policy;
4. verify that theorem names and docstrings describe relation direction;
5. inspect axioms of important exported declarations;
6. ensure the implementation file has minimal imports; and
7. add or update a regression client that demonstrates the API.

CSLib follows Mathlib-style documentation and review and recommends discussing major foundational
frameworks on Zulip or in an issue before implementation. Once this core is mature, propose its
scope and module placement first, then submit small reviewable PRs in dependency order. AI use must
be disclosed in each PR as required by CSLib's contribution policy.

## Contribution workflow

`CONTRIBUTING.md` is the contributor guide; these are the working rules with design consequences.

- discuss a new theorem family or a change to a shared foundation before starting
  (`CONTRIBUTING.md` §7), and keep one logical change per pull request;
- prefer adding a new leaf module over refactoring a shared foundation while other work is in
  flight;
- a refactor of a theorem that other modules consume keeps every public statement unchanged — proof
  body only — and shows the statement fingerprint (`#check` and `#print axioms` output) before and
  after;
- change `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, anything under `scripts/` or
  `.github/`, the `AxiomAudit*` or `Frontier` trees, umbrella imports, or the directory layout only
  deliberately, and say so in the pull request. These are the paths `.github/CODEOWNERS` reserves
  for owner review — inert until branch protection is enabled — because a change to a gate, a pin,
  or the axiom allowlist can make every other check vacuous;
- a change builds from a clean checkout: every `import` of every file it adds resolves to a tracked
  module or to one added in the same change, never to an untracked local file;
- build through `scripts/lake_serial.sh`, `scripts/lake_build_serial.sh`, or
  `scripts/lean_check_lowmem.sh`, which serialize on the worktree build lock;
- keep intermediate edits buildable; use ignored `tmp/` files for failing experiments;
- run targeted builds after each coherent edit, and the `scripts/` gates (see "Module hygiene") and
  a full build before opening a pull request;
- record new architectural decisions here rather than leaving them only in an issue thread.

When two tasks need the same declaration, agree on the smallest shared API first. One contributor
should own that declaration; the other should consume it after it builds. Verify a shared
convention — an alphabet, an index type, an encoding, a hypothesis shape — against the committed
declaration it must match, never against a summary of it.

Cleaning is part of the work rather than a phase after it: duplication, dead code, audit-coverage
gaps, documentation drift against the code, and hygiene-gate regressions are fixed when found, or
recorded as known debt.

## Roadmap and acceptance criteria

The reusable core is ready to propose to CSLib when it has:

- a coherent tensor/restriction/isomorphism API;
- a documented bilinear-algorithm/tensor-rank bridge and its connection to arithmetic complexity;
- direct sums, indexed products, and canonical powers with stable equivalences;
- constructive rank, border rank, and polynomial degeneration;
- matrix-multiplication tensors and their product/symmetry/restriction laws;
- asymptotic rank and a precise matrix-multiplication exponent;
- focused documentation and regression tests;
- no paper-specific constants or data; and
- a clean axiom audit.

A bound is a *record* only if it is unconditional in the sense of `Frontier.lean`: no `Prop`
hypothesis standing in for an unproved input, no paper-specific assumption, no variable carrying a
proof obligation. It must be reached by `Frontier.frontier` as an application of a committed
endpoint to a fingerprinted shape (`#assert_statement_fingerprint`), be covered by
`#assert_axioms`, and improve `Frontier.frontierConstant` (today `2374631/1000000`) by at least
`Frontier.recordDelta` (`1/100000`). `scripts/check_frontier_improvement.sh` checks that in CI on
exact rationals, so a record cannot tie, cannot regress, and cannot be claimed for shaving a final
digit off an existing search; a pull request claiming one carries the `record-claim` label, which
forces the generated-certificate rebuild the claim rests on. Conditional endpoints — an `omega`
bound that still carries a named proof obligation — are real results and belong in `README.md` and
in the ladder above, not on the leaderboard. `docs/STATEMENT_INTEGRITY.md` is the companion note.

The classical first-power CW development now satisfies the end-to-end criterion: its border-rank
degeneration, exact type extraction, hashing/induced-matching step, Schönhage asymptotic sum
inequality, entropy arithmetic, and exponent conclusion are all proved. The named abstract laser
propositions remain useful interfaces, but the literature-facing theorem does not assume them.

The current paper claim is end-to-end only after both the reusable mathematical bridge and the
exact reconstruction of its numerical certificate are verified in Lean. The certificate checker
and experimental optimizer remain downstream of the core regardless of completion.

`MatrixMultiplication/CurrentProofObligations.lean` is the current paper-layer adapter boundary.
It represents concrete recursive type counting, compatibility/hole repair, certificate-specific
parent-correction and two-letter instantiation, and level-4 reconstruction by named propositions,
while proving all composition, Schönhage application, source-rank, and final `2.369661` and
`2.36965963` arithmetic around them. Those two targets are superseded,
and re-targeting the module is planned. That work may not depend on the
constructions of the More-Asymmetry paper (arXiv:2404.16349), whose optimized constituent
constructions and parameter tables are unpublished; a framework statement from that paper may be
used only once it is proved here, from the paper's definitions, at this project's parameters.
The local parent-consistency inequality belongs to the reusable core and is proved in
`AlgebraicComplexity/Probability/ParentConsistency.lean`. The finite entropy-chain and stable
cross-entropy identities live in `Probability/EntropyChainRule.lean` and
`Probability/CrossEntropy.lean`; weighted retained-rate aggregation and arbitrary-active-branch
stagewise composition live in `Analysis/ParentConsistencyGain.lean`. Only identification of the
paper's concrete node laws, occurrence cells, and branch totals belongs at the adapter boundary.
The reusable fixed-interface coupling laws and correlated combination-loss comparison live in
`Probability/TwoLetter.lean`; only identification of concrete product partitions, rational
couplings, and active nodes belongs at the adapter boundary.
This boundary should shrink as the named propositions acquire concrete implementations; it must
not migrate into the reusable core.

## CSLib integration target

The library is meant to be upstreamed into [CSLib](https://github.com/leanprover/cslib) (pinned
here as a dependency; same toolchain and the same Mathlib commit — keep the pins in lockstep).
New work must follow CSLib's structure and conventions so that the eventual move is mechanical:

* **Destination by layer.** Layer 2 (pure mathematics: finite KL and Pinsker, binomial tails,
  multinomial entropy, the Fekete engine, the Behrend rate argument, log enclosures) is Mathlib
  material and should be written to Mathlib's standards with Mathlib upstreaming in mind. Layers
  1 and 3 (tensors, rank/border rank/degeneration, asymptotic invariants, laser and Galactic
  methods, the barrier framework) are CSLib material — a new area (working title
  `Cslib/Complexity/Algebraic/…`, exact location to be agreed with the CSLib maintainers through a
  working group, per their CONTRIBUTING). Layer 4 (paper clients) maps to CSLib examples.
* **Already enforced, not pending.** The Apache-2.0 copyright header with authors and the
  `/-! # Title … -/` module docstring citing published sources by `[BibKey]` are gates, not
  aspirations; see "Module hygiene" above for the checks and their standing debt.
* **File conventions to adopt now** (CSLib `CONTRIBUTING.md`/`ORGANISATION.md`): a
  `references.bib` for the bib keys; `Defs.lean` / `Basic.lean` splits for large topics with
  `Internal/` for implementation detail; namespaces that will become `Cslib.<Area>.<Topic>` (today
  `AlgebraicComplexity.<Topic>`, one rename away); Mathlib style guide; proofs readable rather than
  golfed; reuse of existing abstractions over new ones.
* **Tooling to converge on**: CSLib's linter set (`weak.linter.mathlibStandardSet`,
  `weak.linter.flexible`, header/style linters), `lake shake` minimal imports, `lake exe mk_all`
  for the umbrella, a test driver directory, and the Lean module system (`module` /
  `public import` / `Cslib.Init`). These are recorded as known debt, to be applied to our files
  in one conformance pass.
