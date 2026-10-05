# Formalization plan: the AVW asymptotic-independence-number barrier framework

Scope: a dependency-ordered plan for formalizing the framework of

> J. Alman and V. Vassilevska Williams, *Limits on All Known (and Some Unknown) Approaches to
> Matrix Multiplication*, arXiv:1810.08671v1,

up to its headline Theorem 7.1. All numbering below (`Definition 3.1`, `Lemma 4.3`, …) refers to
that paper. This document is a contract in the sense of `DESIGN.md`: it fixes the definitions,
the module graph, the true/false monotonicity statements, and an honest milestone list with the
external inputs and known gaps marked. It supersedes nothing in `DESIGN.md`; the AVW row of the
theorem ladder and the `LOWER_BOUNDS_ROADMAP.md` inventory remain authoritative for priorities.

**Status of tranche 1 (done):** `AlgebraicComplexity/Tensor/IndependenceNumber.lean` — the finite
independence number `I(T)`, its calculus, and the bridge to the proved slice-rank barrier. Fully
proved, no `sorry`/`axiom`, axiom audit `[propext, Classical.choice, Quot.sound]`.

---

## 1. Why this framework rather than slice rank directly

The obvious route to a matrix-multiplication barrier is: *bound the slice rank of `T^{⊗n}`*.
AVW explicitly reject it (Section 3.7), for two reasons that decide our architecture.

1. **Slice rank is not submultiplicative.** `sliceRank(CW_q) ≤ 3`, but the Coppersmith–Winograd
   analysis forces `sliceRank(CW_5^{⊗n}) ≥ 5.15^{n−o(n)}`. So a bound on `sliceRank(T)` says
   nothing about `sliceRank(T^{⊗n})`, and there is no known way to bound the latter for `CW_q`.
2. **Slice rank is not monotone under passing to sub-supports.** Deleting terms from the support
   of a tensor can *increase* its slice rank: the all-ones tensor on `ι³` is a single pure tensor
   (slice rank `1`) yet contains the diagonal `⟨|ι|⟩` (slice rank `|ι|`) as a sub-support. Every
   step of a laser-method analysis passes to sub-supports, so slice rank cannot be propagated
   along such an analysis.

What *is* available is Tao's diagonal lemma in its **restriction** form, which the repository has
already proved:

```
card_le_sliceRank_of_restricts_diagonalTensor :
  Restricts T (diagonalTensor K ι) → Fintype.card ι ≤ sliceRank T
```

(`Tensor/SliceRank.lean`). This applies to legwise linear maps only — it is not, and must not be
stated as, a statement about sub-supports. AVW therefore work with the combinatorial quantity
`I(T)` and its asymptotic version `Ī(T)`, which *are* monotone under the operations the laser
method actually uses, and only *compare* them with slice rank on honest restrictions.

A second structural fact drives the design: **`I` is basis-dependent**. Over `ℚ`, `I(⟨2⟩) = 2`,
while the legwise-isomorphic table obtained by the change of basis `[[1,1],[1,−1]]` on each leg
is supported on the four triples with an even number of index-`2` entries, no two of which differ
in all three coordinates, so its independence number is `1`. Hence `I` and `Ī` must be defined on
a *coefficient function*, never on an abstract `Tensor3`, and `I(T) ≤ sliceRank(T)` is
necessarily a one-way inequality. Tranche 1 implements exactly this.

---

## 2. Definitions to adopt

### 2.1 Relations between tensors (Section 3.1.2)

Five distinct relations appear, and the whole framework depends on not conflating them.

| relation | meaning | Lean home |
| --- | --- | --- |
| sub-tensor `t ⊆ t'` | `supp t ⊆ supp t'` with equal coefficients there; **not** a linear-algebra operation | support-level hypothesis (`IndependentSet.of_subSupport` uses it) |
| zeroing out (combinatorial restriction) | choose `X' ⊆ X, Y' ⊆ Y, Z' ⊆ Z`, set all other variables to `0` | `coordinateZeroOut` (tranche 1) |
| restriction `t ≤ t'` | one linear map per leg | `Tensor.Restricts` |
| monomial degeneration | diagonal `A(λ), B(λ), C(λ)` with monomial entries; equivalently: weights `a, b, c` into `ℤ` with `a+b+c ≥ 0` on `supp t'`, `= 0` exactly on `supp t` | `Tensor.MonomialDegenerates` (`Tensor/Monomial.lean`) |
| degeneration `t ⊴ t'` | polynomial matrices, `λ^q t = (A⊗B⊗C)t' + O(λ^{q+1})` | `Tensor.PolynomialDegenerates` |

Inclusions: zeroing out ⊂ restriction ⊂ degeneration, and zeroing out ⊂ monomial degeneration ⊂
degeneration. Restriction and monomial degeneration are incomparable.

The repository's `monomialDegenerates_fintype_sum_basis` is already exactly AVW's combinatorial
form, with `ℕ`-valued weights and a threshold `d` in place of `ℤ`-valued weights and threshold
`0` (shift each leg weight by a constant; `d` is the sum of the three shifts). No new
monomial-degeneration definition is needed. Its source shape,
`∑ i, a i • pure (fun c ↦ Pi.single (p i c) 1)`, is definitionally the `coordinateTensor` of
tranche 1 with `α = (∀ c, κ c)`, `a = T`, `p = id`.

### 2.2 Independent tensors and `I(T)` (Sections 3.1.1, 3.5)

AVW: a tensor is *independent of size `r`* if it equals `⟨r⟩` up to a permutation of the indices
on each leg; `I(T)` is the largest `r` such that some zeroing out of `T` is independent of size
`r`; `Ī(T) := limsup_n I(T^{⊗n})^{1/n}`.

Unfolded, this is the tranche-1 definition:

```lean
structure IndependentSet (T : (∀ i, κ i) → K) (S : Finset (∀ i, κ i)) : Prop where
  ne_zero  : ∀ p ∈ S, T p ≠ 0
  distinct : ∀ p ∈ S, ∀ q ∈ S, ∀ i, p i = q i → p = q
  closed   : ∀ p, T p ≠ 0 → (∀ i, ∃ q ∈ S, q i = p i) → p ∈ S

noncomputable def independenceNumber (T : (∀ i, κ i) → K) : ℕ := sSup (independenceCards T)
```

The third clause is the one that is easy to lose. Without it the invariant is a completely
different (and useless) quantity: the all-ones tensor would have "independence number" `|ι|`
instead of `1`. It is exactly the second clause of the definition of a tri-colored sum-free set
(Definition 3.3), which is why Lemma 6.1 is a triviality once the definition is right; tranche 1
isolates it as `IndependentSet.mix_eq`. `IndependentSet.zeroOut_support` and
`independentSet_of_zeroOut_support` prove the equivalence with AVW's zeroing-out phrasing, taking
`X', Y', Z'` to be the variables used by `S`.

Deliberate deviation from the letter of the paper: AVW's "independent tensor" has coefficients
equal to `1`. We require only nonzero coefficients on `S`, and recover their statement by the
diagonal rescaling built into `IndependentSet.restricts_diagonalTensor`, which needs only that
the coefficients are units. Over a field the two readings give the same number; over a general
commutative semiring ours is the usable one.

### 2.3 The monotonicity table — the part to get right

`I` (finite):

| operation | `I` monotone? | status |
| --- | --- | --- |
| zeroing out | **yes**, `I(T\|_{X',Y',Z'}) ≤ I(T)` | proved: `independenceNumber_coordinateZeroOut_le` |
| passing to a sub-support | **no** — it can strictly increase | proved by exhibiting both sides: `independenceNumber_const_one` (`= 1`) versus `independenceNumber_diagonalCoefficients` (`= |ι|`) |
| a fixed independent set restricted to a sub-support | **yes** (this is the true neighbour of the false statement above) | proved: `IndependentSet.of_subSupport` |
| legwise isomorphism | **no** — `I` is basis-dependent (§1) | not formalized; optional milestone in §6 |
| restriction | **no** (special case of the previous line) | — |
| monomial degeneration | **not claimed** — AVW never assert it, and their route (Lemma 4.3) is intrinsically asymptotic | — |
| Kronecker product | supermultiplicative: `I(S ⊗ T) ≥ I(S)·I(T)` | proved: `independenceNumber_coordinateProduct_ge` (needs `NoZeroDivisors`) |

`Ī` (asymptotic): monotone under zeroing outs, and monotone under **monomial degeneration**
(Corollary 4.2) — but only asymptotically, via Lemma 4.3. Neither `I` nor `Ī` is additive or
multiplicative: Example 5.1 gives `T₁ + T₂ + T₃ = CW_q` with `Ī(Tⱼ) = 1` each and
`Ī(CW_q) ≥ (q+2)^{2/3}`, and the same triple witnesses non-multiplicativity.

Slice rank, for contrast: monotone under restriction (proved, `sliceRank_restricts_le`), hence
under zeroing out; monotone under degeneration (**not** proved here — it needs Zariski-closedness
of the locus `sliceRank ≤ r`, not certificate manipulation; recorded as future work in
`Tensor/SliceRank.lean`); **not** monotone under sub-supports; not submultiplicative.

### 2.4 The bridge, stated exactly

Proved in tranche 1:

```
IndependentSet.restricts_diagonalTensor :
  IndependentSet T S → (∀ p ∈ S, IsUnit (T p)) →
    Restricts (coordinateTensor T) (diagonalTensor K {p // p ∈ S})     -- CommSemiring

IndependentSet.card_le_sliceRank : IndependentSet T S → S.card ≤ sliceRank (coordinateTensor T)
independenceNumber_le_sliceRank  : independenceNumber T ≤ sliceRank (coordinateTensor T)
independenceNumber_le_rank       : independenceNumber T ≤ rank (coordinateTensor T)   -- Field
```

The restriction is the zeroing out to the variables of `S` followed by a diagonal rescaling;
closure is what makes the image *exactly* diagonal, and injectivity of the three projections is
what makes the rescaling well-defined. What is **not** true and must never be written: a bound on
`sliceRank` of a sub-support of `T`, or monotonicity of `I` along `Restricts`.

`independenceNumber_le_rank` is the finite form of the elementary bound `Ī(T) ≤ R̃(T)` used
throughout Section 4; applied to powers it needs only the product bridge of Milestone A below.

---

## 3. Existence of `Ī`: supermultiplicativity and Fekete

AVW define `Ī` as a `limsup` and never prove that the limit exists, yet they use it through
inequalities of the shape `Ī(T) ≥ I(T^{⊗n})^{1/n}` for a *single* `n` (Corollary 4.1, Lemma 4.4,
Theorem 7.3). With a bare `limsup` each such use has to be re-derived along a subsequence (which
is what the appeal to Lemma 4.3 for every multiple `nm` is silently doing); proving the Fekete
upgrade once makes all of them immediate and matches the way the statements read.

Facts needed, in order:

1. `I(T^{⊗n})` is supermultiplicative in `n` — tranche 1 supplies the binary step
   `independenceNumber_coordinateProduct_ge`, over any `CommSemiring` with `NoZeroDivisors`.
2. `1 ≤ I(T^{⊗n})` for `T ≠ 0` (`one_le_independenceNumber`), and
   `I(T^{⊗n}) ≤ (min |κ i|)^n` (`independenceNumber_le_card`).
3. Fekete: `u n := −Real.log (I (T^{⊗n}))` is subadditive by (1), and `u n / n` is bounded below
   by `−log (min |κ i|)` by (2). Mathlib's `Subadditive.tendsto_lim` (`Mathlib/Analysis/
   Subadditive.lean`) gives convergence of `u n / n` to `sInf`, hence
   `limsup I(T^{⊗n})^{1/n} = lim I(T^{⊗n})^{1/n} = sup_n I(T^{⊗n})^{1/n}`.

Definition to adopt: `Ī(T) := Growth.exponentialRate (fun n ↦ independenceNumber (T^{⊗n}))`.
This is not a convenience choice — `Growth.exponentialRate a = sInf {ρ | ∃ C > 0, ∀ n, a n ≤ C ρ^n}`
equals `limsup a n^{1/n}`, i.e. literally AVW's definition (the identity is elementary in both
directions and should be recorded as a lemma in module (B), so that the match with the source is
on the record rather than folklore), and `AlgebraicComplexity/Asymptotics.lean`
already supplies `exponentialRate_le`, `le_exponentialRate_of_pow_le`, and
`le_exponentialRate_of_pow_succ_le_mul_polynomial` (a fixed polynomial loss does not move the
rate — exactly the shape of Lemma 4.3). The Fekete upgrade is then an added theorem, not a
different definition, and the `sup` form is what Corollary 4.1 consumes.

---

## 4. What the repository already provides

Reusable, proved, and directly relevant:

* `Tensor/SliceRank.lean` — slice-rank calculus, Tao's diagonal lemma
  (`sliceRank_diagonalTensor`), and the restriction barrier
  `card_le_sliceRank_of_restricts_diagonalTensor`. This is the finite substrate of the whole
  program and the target of the tranche-1 bridge.
* `Tensor/IndependenceNumber.lean` (tranche 1) — everything in §2 above.
* `Tensor/Monomial.lean` — `MonomialDegenerates`, and `monomialDegenerates_fintype_sum_basis`,
  the ready-made certificate former for AVW-style weight arguments (Lemma 4.2, Theorem 7.2).
* `Tensor/Coordinates.lean` — `standardCoordinateEquiv`, `coordinateTensorEquiv`; the bridge
  from coefficient tables to abstract tensors, needed to identify `coordinateProduct` with
  `Tensor.external`/`Tensor.power`.
* `Tensor/Product.lean`, `Tensor/Power.lean`, `Tensor/IndexedDirectSum.lean` — Kronecker product,
  canonical powers, direct sums, all with restriction/degeneration functoriality.
* `MatrixMultiplication/AsymptoticSum.lean` — **Schönhage's asymptotic sum inequality**
  (Theorem 3.1), proved with correct field hypotheses. This is the engine of Lemma 4.1.
* `MatrixMultiplication/Exponent.lean`, `RectangularExponent.lean` — `omega`, `MatrixExponentLE`,
  `omega_le_log_of_rankLE`, the symmetrized volume inequality. `ω_g(T)` must be defined so that
  `omega ≤ ω_g T` is provable from these.
* `Asymptotics.lean` — `ExponentialBound`, `exponentialRate`, and the polynomial-loss lemmas.
* `Analysis/Subexponential.lean` — the `n^{-2}`-loss removal of Lemma 4.3 is literally its
  motivating case.
* Type/entropy layer: `Combinatorics/WordType.lean` (multiplicity types, `Finset.piAntidiag`,
  polynomial bound on the number of types), `Combinatorics/BalancedMultinomial.lean`,
  `Analysis/ProportionalMultinomial.lean` (method-of-types entropy estimate with explicit
  polynomial loss), `Analysis/TernaryMultinomial.lean`, `Probability/KullbackLeibler*.lean`
  (finite KL with a quadratic lower bound), `Probability/Finite.lean` (finite probability
  vectors), `Analysis/Log.lean` (certified rational log enclosures).
* Existing CW clients: `Examples/CoppersmithWinogradEasyHashing.lean` (`ω < 2.41`) and
  `Examples/CoppersmithWinogradFirstPowerHashing.lean` (`ω < 2.3872`) — the positive analyses
  that Theorem 7.3 consumes as an *input*.

Not available and not to be assumed: asymptotic slice rank, semicontinuity of slice rank under
degeneration, Sawin's theorem (Theorem 3.2), and any Zariski-closure machinery.

---

## 5. Module graph

Layer 1 (`AlgebraicComplexity/Tensor/`), no combinatorics or matrix-multiplication imports:

```
Tensor/SliceRank.lean                     [exists]
        │
Tensor/IndependenceNumber.lean            [tranche 1, done]
        │
        ├── Tensor/IndependenceNumberPower.lean      (A)  coordinateProduct ↔ external/power;
        │                                                 the sequence n ↦ I(T^{⊗n})
        ├── Tensor/AsymptoticIndependenceNumber.lean (B)  Ī via Growth.exponentialRate + Fekete
        └── Tensor/MonomialIndependence.lean         (C)  Lemma 4.3, Cor 4.1, Cor 4.2
```

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`), may use Schönhage and `omega`:

```
MatrixMultiplication/GalacticMethod.lean        (D)  ω_g(T) (Def 4.1) + Lemma 4.1
MatrixMultiplication/IndependentDiagonal.lean   (E)  Lemma 4.2 (Strassen) + Lemma 4.4
MatrixMultiplication/IndependenceBarrier.lean   (F)  Theorem 4.1 + Corollary 4.3
```

Layer 2/3 partitioning tools (`Combinatorics/` for the counting, `MatrixMultiplication/` for the
tensor-facing statements):

```
Tensor/IndependenceMeasure.lean          (G)  Def 5.2, Claim 5.1, Theorem 5.3
Combinatorics/BinomialTail.lean          (H)  Lemma 5.1 (binomial tail, method-of-types form)
Tensor/IndependenceMassDistribution.lean (I)  Theorem 5.2 + Corollary 5.1
Tensor/IndependenceSplitting.lean        (J)  Theorem 5.1
```

Clients (`AlgebraicComplexityClients/` or `Examples/`):

```
Examples/GeneralizedCoppersmithWinogradBarrier.lean   (K)  Lemmas 7.1, 7.2, Theorem 7.1
Examples/GroupTensorBarrier.lean                      (L)  Lemma 6.1, Cor 6.1, Thm 6.1 (needs Sawin)
Examples/GroupTensorCWDegeneration.lean               (M)  Theorem 7.2, 7.3, 7.4
Examples/LowerTriangularBarrier.lean                  (N)  Theorems 7.5, 7.6
```

Note that `Tensor/GroupTensor.lean` and the generalized-CW modules are being written by another
contributor; (L), (M), (N) must consume whatever definitions land there rather than duplicate
them, and this document does not claim them.

---

## 6. Milestones, dependency ordered

Each entry states the AVW result, the prerequisite, and an honest difficulty note. "Tractable"
means the mathematics is finite or elementary and the repository already has the tools; "hard"
means new machinery; "research-scale" means an unformalized deep input is required.

**A. Powers of the independence number** — *PROVED 2026-08-25, as new sections of `Tensor/IndependenceNumber.lean` (relabelling invariance, `coordinatePower`, supermultiplicativity, the `Isomorphic.coordinateTensor_coordinatePower` bridge, and the basis-dependence witness `HadamardWitness.independenceNumber_not_isomorphism_invariant`).*
Identify `coordinateTensor (coordinateProduct T T')` with `Tensor.external` of the two coordinate
tensors through `coordinateTensorEquiv`, and define the iterated product for `T^{⊗n}` matching
`Tensor.power`. Deliverables: `I(T^{⊗(m+n)}) ≥ I(T^{⊗m})·I(T^{⊗n})`,
`I(T^{⊗n}) ≤ rank (power (coordinateTensor T) n)`. *Tractable*; the only friction is index-type
bookkeeping (`(∀ i, κ i × κ' i)` versus `Fin n → κ i`).

**B. The asymptotic independence number** (`Tensor/AsymptoticIndependenceNumber.lean`) — *PROVED 2026-08-25 as an instance of the layer-0 `Growth.supermultiplicativeLimit` engine; includes `Ī(T^{⊗k}) = Ī(T)^k` and the comparisons with `asymptoticSubrank` and `asymptoticRank`.*
`Ī(T) := Growth.exponentialRate (fun n ↦ I(T^{⊗n}))`; Fekete upgrade (§3); `I(T) ≤ Ī(T)`;
`Ī(T) ≤ min |κ i|`; `Ī(T) ≤ R̃(coordinateTensor T)`; monotonicity under zeroing outs.
*Tractable*, given A.

**C. Monomial degenerations feed `Ī`** (`Tensor/MonomialIndependence.lean`) — *PROVED 2026-08-25 (Lemma 4.3 with the explicit polynomial loss `(n·M_X+1)(n·M_Y+1)`, Corollaries 4.1 and 4.2), stated on the degenerated table `D` per the milestone-E correction.* Lemma 4.3
(= AW18 Lemma 5.1): if `A` monomially degenerates to `f` independent triples, then `A^{⊗n}`
zeroes out to `Ω(f^n/n²)` of them. Proof to formalize: with weights `a, b, c` and threshold, the
total weight of a surviving triple of `A^{⊗n}` is the sum of the per-coordinate weights, which
are all `≥ 0`; fixing the two partial weight sums `(α, β)` — `O(n²)` classes, since each partial
sum ranges over `O(n)` values — and zeroing out to the corresponding variable classes leaves
exactly the minimum-weight triples in that class, which form a subset of `D^n` and hence a valid
independent zeroing out. Pigeonhole on the `O(n²)` classes gives the count. Then Corollary 4.1
(`Ī(T) ≥ f^{1/n}`) via `Analysis/Subexponential.lean` or
`le_exponentialRate_of_pow_succ_le_mul_polynomial`, and Corollary 4.2. *Tractable*; this is the
single most reusable step in Section 4 and should be done early.
Note precisely what is *not* obtained: no finite statement `I(A) ≤ I(B)` for a monomial
degeneration. Do not add one.

**D. The Galactic method** (`MatrixMultiplication/GalacticMethod.lean`) — *PROVED 2026-08-26 under option (i): certificates reuse `Tensor.MonomialDegenerates` onto `matrixMultiplicationDirectSum` with equal dimensions (Lemma 4.1 made definitional; Schönhage §7.2 cited); `ω_g` is the `sInf` of `3(log R̲(T^{⊗n}) − log F)/log(abc)` over certificates (border rank of the power), with the AVW asymptotic-rank variant defined, proved sound, and compared (`galacticAsymptoticExponent ≤ galacticExponent`; equality would need `R̃(T^{⊗n}) = R̃(T)^n`, not in the tree); `ω ≤ ω_g` from `asymptoticSumInequality`; `ω_g ≥ 2`. Monotonicity under monomial degeneration of `T` awaits `MonomialDegenerates.trans` and powers of monomial degenerations (backlog).* Definition 4.1 and
Lemma 4.1. `ω_g(T)` is defined as a limit infimum over `(n, a, b, c)` of
`3(n log R̃(T) − log F_{T,n,a,b,c})/log(abc)`, where `F` counts disjoint copies of `⟨a,b,c⟩`
obtainable as a monomial degeneration of `T^{⊗n}`; the required soundness `ω ≤ ω_g(T)` comes from
Schönhage (`MatrixMultiplication/AsymptoticSum.lean`) applied to a direct sum of `F` equal
copies. *Hard, with a genuine gap:* Lemma 4.1 asserts "we can restrict attention without loss of
generality to degenerations into a disjoint sum of matrix multiplication tensors of the same
dimensions", citing Schönhage §7.2 / Bläser Theorem 7.5. That reduction is not in the repository
and is not part of the proved `AsymptoticSum` statement. Two options, and the choice must be
recorded here when made: (i) define `ω_g` directly by the equal-dimension formula, so Lemma 4.1
becomes a definition and the only obligation is `ω ≤ ω_g(T)` (recommended — it is the weaker,
honest reading and it is what Sections 4–7 actually use); (ii) formalize the reduction, which is
a substantial separate project.

**E. Matrix-multiplication tensors have large `Ī`** (`MatrixMultiplication/IndependentDiagonal.lean`).
*Status: finite half PROVED (2026-08-25), for all dimensions with the unweakened `3/4` constant, via a
level set `{i+j+k = s}` in raw `Fin` coordinates (the recentring is the choice of `s`, so no parity
hypothesis). Correction recorded there: the minimum-weight triples are NOT an `IndependentSet` of
`⟨a,b,c⟩`'s own table (closure fails — formal witness `not_independentSet_mmCoefficients_mmMinWeightSupport`);
Lemma 4.2 is a statement about the degenerated table `D`, and milestone C must be phrased on `D`.
Lemma 4.4 single-copy form PROVED (2026-08-26): `asymptoticIndependenceNumber_mmCoefficients : Ī(⟨m,n,p⟩) = mnp/max`,
exact for all dimensions; the `F`-copies form awaits a coordinate-level direct-sum table in the tensor layer.*
Lemma 4.2 (Strassen): the weights `α(x_{ij}) = i² + 2ij`, `β(y_{jk}) = j² + 2jk`,
`γ(z_{ki}) = k² + 2ki` on `⟨a,b,c⟩` indexed symmetrically about `0` give total weight `(i+j+k)²`,
so the minimum-weight sub-tensor is `{i + j + k = 0}`, which is independent, of size at least
`(3/4)·abc/max{a,b,c}`. Then Lemma 4.4: `Ī(F ⊙ ⟨a,b,c⟩) = F·abc/max{a,b,c}`. *Tractable but
fiddly*: (a) the repo's `MMIndex` is `Fin`-based, so the symmetric indexing needs a translation
and the weights need the `ℤ → ℕ` shift of §2.1; (b) AVW prove the odd case and write "the cases
where `a, b, c` are not all odd are similar" — the general case must be done, or the statement
restricted to odd dimensions and the general case obtained by monotonicity in `a, b, c` with an
explicitly weaker constant. Record which. (c) the counting "at least `(3/4)ab` pairs `(i,j)` with
`|i+j| ≤ p`" is a lattice-point count needing care at the boundary.

**F. The barrier inequality** (`MatrixMultiplication/IndependenceBarrier.lean`) — *PROVED 2026-08-26: Theorem 4.1 and Corollary 4.3 in the explicit `6/(s+2)` form, plus the coordinate direct-sum table, Lemma 4.4 for `F` copies, and `|κ i| ≤ R̃(T)` for coordinate-concise tables. CORRECTION recorded: because `Ī` is basis-dependent and `galacticExponent` is an infimum over all coordinate presentations, Theorem 4.1 bounds the `CoordinateGalacticCertificate` exponent `coordinateGalacticExponent`; the abstract `galacticExponent ≤ coordinateGalacticExponent` is proved and the reverse is not expected. AVW conflate the two. `GalacticCertificate` was relaxed from `Isomorphic` to `Restricts` on the target (monomial degenerations leave unused variables), which only enlarges the certificate set.* Theorem 4.1:
for concise `T`, `Ī(T) ≥ R̃(T)^{6/ω_g(T) − 2}`; Corollary 4.3. Conciseness enters exactly once, to
get `|X| ≤ R̃(T)` (`Tensor/Concise.lean`, `Tensor/BorderConcise.lean` give the leg-dimension
bounds). *Hard*: real-exponent arithmetic with an `ε`-and-limit argument; the repository's
`Growth` layer is the right home for the limiting step. Corollary 4.3 is the interface every
later section consumes and should be stated in the explicit form "for each `s < 1` the constant
`w = 6/(s+2) > 2` works", not with an unspecified constant.

**G. Measure and the partition bound** (`Tensor/IndependenceMeasure.lean`) — *PROVED 2026-08-26, in full and stronger than stated: Theorem 5.3 holds for covers (not just partitions), over a plain `CommSemiring`, with NO polynomial loss — the proof sums over colour words and injects each colour class into a leg projection (`IndependentSet.card_le_pow_of_cover`), so the greedy walk and `IndependentSet.of_subSupport` are not needed. Claim 5.1 needs no ring hypotheses; μ-multiplicativity equalities need `NoZeroDivisors` + `Nontrivial`.* Definition 5.2
(`μ(T) = |X'|·|Y'|·|Z'|` over the *minimal* variable sets), Claim 5.1 (`Ī(T) ≤ μ(T)^{1/3}`),
Theorem 5.3 (`Ī(T) ≤ Σ μ(Pᵢ)^{1/3}` for a partition of the support). *Hard but self-contained*:
the proof is a greedy walk over the `n` coordinates of `T^{⊗n}` replacing the `j`-th factor by a
part `Pᵢ` retaining a `pᵢ`-fraction of the independent triples. The step that must be proved
carefully is that re-applying the *same* zeroing out to the smaller tensor still yields an
independent tensor — that is `IndependentSet.of_subSupport` from tranche 1, and it is true only
because independence is a property of the *whole* surviving support. Also needs multiplicativity
of `μ` under Kronecker product.

**H. Binomial tail** (`Combinatorics/BinomialTail.lean`) — *PROVED 2026-08-26 by the method-of-types route (no measure theory): `|deviating words| ≤ (n+1)·qⁿ·exp(−n·tailExponent ε)` with `tailExponent ε = 2ε²` from the library\'s quadratic KL bound; AVW\'s `q^{(1−2δ)n}` shape recovered with `ε = √(2δ log q)` (their `√(δ log q)` needs sharp binary Pinsker, a recorded upgrade); the `(n+1)` factor is removed by `exponentialRate_deviatingWords_le`. Milestone I consumes `card_sub_bound_le_card_concentrated`.* Lemma 5.1: the number of words in
`[q]^n` in which a fixed letter occurs outside `(1/q ± ε)n` is at most `q^{(1−2δ)n}` for
`ε = sqrt(δ ln q)` (sharp since the 2026-08-26 binary-Pinsker upgrade; the earlier `2ε²/(1+ε)` exponent and `sqrt(2δ ln q)` radius are gone). AVW use Hoeffding. Mathlib's Hoeffding
(`ProbabilityTheory.measure_sum_ge_le_of_iIndepFun`) is measure-theoretic and would drag measure
theory into a combinatorics module; the repository's own method-of-types route
(`WordType`, `ProportionalMultinomial`, `KullbackLeiblerBounds`) gives the same bound
combinatorially and is the recommended path. *Tractable-to-hard*; decide and record the route.

**I. Near-uniform mass distributions** (`MatrixMultiplication/IndependenceMassDistribution.lean` — layer 3, because it needs both the tensor independence API and the layer-2 binomial tail; DESIGN forbids `Tensor/` importing `Combinatorics/`) — *PROVED 2026-08-26 in full: Theorem 5.2 with window `√((2δ+ρ) log q)` (the factor 2 is BinomialTail\'s Pinsker gap) and Corollary 5.1 with explicit `cornerExponent q = 1/(2q²(q+1)²log q)`, `cornerBound q < q`; AVW\'s second corner term turns out unnecessary. Lemma 7.1 consumes it on `gcwTable` with corners `(x₀, x_{q+1}, y₀, y_{q+1}, z₀)` at parameter `q+2`.* Theorem 5.2
and Corollary 5.1 (two corner terms force `Ī(T) < q`). Needs G/H and a finite probability
distribution on the terms of `T` (`Probability/Finite.lean`). *Hard*. Corollary 5.1 is the tool
that yields Lemma 7.1 and Theorem 7.5, so it is the highest-value item of Section 5.

**J. The splitting bound** (`Tensor/IndependenceSplitting.lean`) — *PROVED 2026-08-26 in full: Definition 5.1 as `coordinateFixVariable`/`coordinateEraseVariable`, the finite counting core with no loss at any `n` (colour-word sum with `min{x,y} ≤ x^θ y^{1−θ}` separating optimization from counting), Theorem 5.1 verbatim with `p` recovered as the optimal fraction, Remark 5.1, and BOTH AVW numerical certificates (`≤ 5.08`, `< 8`) by pure rational arithmetic — no `Log.lean` enclosures needed. Milestone H is NOT a prerequisite for J. `NoZeroDivisors` + `Nontrivial` are genuinely required (closure clause).* Theorem 5.1. Same greedy scheme
as G but with a two-part split and a binary-entropy optimization: the bound
`((q−1)/(1−p))^{1−p}·p^{−p}` is `(q−1)^{1−p}·2^{H₂(p)}`, and `k = pn` is the maximizer of the
minimum of the two counts. *Hard*: needs the exact real optimization plus `Analysis/Log.lean` for
the eventual numerics.

**K. The headline** (`Examples/GeneralizedCoppersmithWinogradBarrier.lean`) — *Lemma 7.2 PROVED 2026-08-26 via route 1 (Theorem 5.3): for every generalized CW tensor with `q ≥ 24` and every `σ`, `coordinateGalacticExponent ≥ 2000/999 > 2`, with exact `Log.lean` enclosures at `q = 24` and a `log x ≤ x − 1` induction step. SECOND ERRATUM: AVW\'s own displayed parts have `μ = q², (q+2)², (q+1)²`, not `q²`; moving the single term `x₀y₀z₀` balances them at `(q+1)²`, and the balanced parts are the leg-indexed classes "one coordinate equal to 0". Their printed `3q^{2/3} < q^{0.997}` is wrong on both sides (LHS from the wrong μ, RHS understates the base `q+2`). Route 2 (Theorem 5.1) PROVED 2026-08-26 for ALL `q ≥ 6`: `q = 6` with AVW\'s optimal `θ = 31/32` (`Ī ≤ 7.9976`), and a q-parametric two-step split with uniform rational exponents for every `q ≥ 7` (no per-`q` certificates), constant `60000/29999`; the gap to 2 is intrinsic. THEOREM 7.1 PROVED IN FULL (2026-08-26): Lemma 7.1 via Corollary 5.1 holds for EVERY `q` (no lower bound needed; AVW\'s `1 ≤ q ≤ 5` is where it is used), the certificate-nonemptiness side condition is discharged by an explicit `⟨1,1,2⟩` certificate uniform in `q`, and the universal constant is `avwTheoremSevenOneConstant = min (60000/29999) (6/(3 − cornerExponent 7)) = 2.0000546…`, certified `≥ 2 + 1/15000`; the binding regime is `q = 5` (`cornerExponent` antitone). Three overlapping regimes all proved: `q ≤ 5` (Cor 5.1), `6 ≤ q` (Thm 5.1), `24 ≤ q` (Thm 5.3). Scope: the coordinate galactic exponent of the literal Definition-3.1 table (milestone-F correction).* Theorem 7.1 from
Lemma 7.1 (small `q`, via Corollary 5.1 ⇒ I) and Lemma 7.2 (large `q`). Two independent routes to
Lemma 7.2:
* via Theorem 5.3 (needs G only): partition `CW_q^σ` into `T₁, T₂, T₃` each missing one variable
  type. **Erratum to carry:** AVW state `μ(T₁) = μ(T₂) = μ(T₃) = q²`, but with their own
  displayed parts the minimal variable sets have sizes `1, q+1, q+1` in each case (e.g.
  `T₁ = ∑_{i=0}^{q} x₀ yᵢ zᵢ` uses one `x`, `q+1` `y`s and `q+1` `z`s), so `μ = (q+1)²` and
  Theorem 5.3 gives `Ī(T) ≤ 3(q+1)^{2/3}`, not `3q^{2/3}`. The conclusion survives, but the
  displayed arithmetic must be redone: what Corollary 4.3 needs is `Ī(T) ≤ R̃(T)^s` with
  `R̃(T) = q+2`, i.e. `3(q+1)^{2/3} ≤ (q+2)^{0.997}`, which holds for every `q ≥ 24`
  (`3·25^{2/3} ≈ 25.65 ≤ 26^{0.997} ≈ 25.75`) and stays true for larger `q` because
  `0.997/(q+2) > (2/3)/(q+1)` for all `q ≥ 2`. Their printed inequality `3q^{2/3} < q^{0.997}`
  for `q ≥ 28` is itself correct but very tight (`27.663 < 27.721`) and compares against the
  wrong base; do not reuse it. Formalize with `q' = 28` (safe, and matching the paper) or
  `q' = 24`, and record the corrected chain.
* via Theorem 5.1 (needs J): the `q ≥ 6` route, with the numerical certificates
  `Ī(A) ≤ 5.07905`, `p = 0.133648`, `Ī(CW_6^σ) ≤ 7.9973 < 8`. These are exact-arithmetic
  obligations: `Analysis/Log.lean` enclosures plus `norm_num`, never floating point, per
  `DESIGN.md`.
*Research-scale as a whole*, tractable per route once G/I/J exist.

**L. Group tensors** (`Examples/GroupTensorBarrier.lean`) — *PROVED 2026-08-26 as specified: Lemma 6.1 as an equality `I(T_G) = triColoredSumFreeNumber G` (both directions), `T_G^{⊗n} = T_{Gⁿ}` definitionally, `SawinBound G` a plain `Prop` obligation (never an axiom or instance), Corollary 6.1 and the conditional Theorem 6.1 `SawinBound G → 2 < coordinateGalacticExponent (T_G)` with the certificate-nonemptiness side condition discharged by an explicit `⟨1,1,|G|⟩` certificate. Erratum recorded: `SawinBound` is false for the trivial group.* Lemma 6.1 is immediate from
`IndependentSet.mix_eq` once `T_G` and tri-colored sum-free sets are defined; Corollary 6.1 and
Theorem 6.1 (`ω_g(T_G) > 2` for every finite group) then follow from C, F and **Sawin's theorem**
(Theorem 3.2: tri-colored sum-free sets in `G^n` have size at most `(δ|G|)^n` for some `δ < 1`
depending on `G`). *Sawin's theorem is an external input with no Lean source and no realistic
prospect of one in this project.* It must therefore appear as a named proof obligation in the
sense of `DESIGN.md` — a `Prop` definition, exposed as an explicit hypothesis of every theorem
that uses it, never an `axiom`, never a typeclass instance, and never reported as proved. The
honest deliverable is `SawinBound G → ω_g (T_G) > 2`. Lemma 6.2/6.3 and Theorem 6.2 (`CW_q` is
not a sub-tensor of `T_G`) are independent of Sawin and are *tractable* now (see
`LOWER_BOUNDS_ROADMAP.md`); they belong to the `GroupTensor` work.

**M. Lower bounds on `Ī`** (`Examples/GroupTensorCWDegeneration.lean`). *Theorem 7.2 PROVED at the coefficient-table level 2026-08-26* (`minimumWeightPart_avwSymWeight`, `groupTensor_monomialDegenerates_isGeneralizedCW`) with the Ī bridge `asymptoticIndependenceNumber_gcwTable_le_groupCoefficients : Ī(CW_{|G|−2}^{σ_g}) ≤ Ī(T_G)` — the input Theorem 7.4 (M9) needs; note the target is the generalized member `σ_g(h) = h⁻¹g`, never the standard `CW_q`, and the abstract-tensor Theorem 7.2 already in `Examples/GeneralizedCoppersmithWinograd.lean` carries no Ī content because Corollary 4.2 is stated on `minimumWeightPart`. Theorem 7.2 (`T_G`
monomially degenerates to a generalized CW tensor of parameter `|G| − 2`) is fully explicit and
*tractable* — it is the recommended first positive result of the whole program. Theorem 7.3
(`Ī(T) ≥ (q+2)^{2/f(q)}` with `f(q) = log_q(4(q+2)³/27)`) and Theorem 7.4 need more care:
* **This is where the CW entropy optimization enters.** `f(q)` is the exponent bound of the
  classical first-power CW laser analysis (CW90 §6). AVW write "Coppersmith and Winograd show
  that `ω_g(CW_q) ≥ f(q)`"; this is a typo for `≤` — it is a positive result, an upper bound on
  `ω` achieved by the method.
* The repository proves the CW first-power analysis for the *numeric* instances `q = 6`
  (`ω < 2.3872`) and the easy variant (`ω < 2.41`), through Schönhage plus hashing, i.e. as a
  direct sum of many matrix-multiplication tensors. Theorem 7.3 needs something strictly
  stronger: a **symmetric, single-tensor** zeroing out of `CW_q^{⊗n}` into `⟨t,t,t⟩` with
  `t ≥ (q+2)^{(1−δ)n/f(q)}`, for *general* `q`, and for every generalized CW tensor. AVW
  acknowledge this in their footnote 9. Obtaining it means re-running the entropy optimization
  parametrically in `q` and in the symmetric form. *Research-scale*, and the largest single piece
  of work in Section 7.
* Theorem 7.4 additionally needs `|G| < 5` handled by citation to Kleinberg–Sawin–Speyer; those
  five groups should be done by explicit finite certificates instead.

**Correction 2026-08-26 (scoping pass).** The paragraph above overstates the difficulty. (i) The
parametric analysis already exists: `easyCW_omega_le_log` (`Examples/CoppersmithWinogradEasyHashing.lean`)
proves `ω ≤ log_q(4(q+2)³/27) = f(q)` for every `q > 1` from the uniform type — "[CW90 §6]" is the
three-constituent easy construction, so no entropy optimization has to be re-run. (ii) Footnote 9's
symmetric single-tensor zeroing out is unnecessary: Lemma 4.4's `F`-copies form
(`CoordinateGalacticCertificate.le_asymptoticIndependenceNumber_pow`, `IndependenceBarrier.lean`) only
needs *balanced* dimensions `a = b = c`, which the uniform-type extraction already has, and
`F·a² ≥ (F·a^f)^{2/f}` for `f ≥ 2` gives `Ī(CW_q^σ) ≥ ((27/4)q²)^{1/3} ≥ (q+2)^{2/f(q)}` — stronger
than AVW. (iii) The one real gap: every extraction in the tree is a `Tensor.Restricts` on abstract
tensors, and `Ī` is basis-dependent, so the extraction chain needs a **coordinate shadow**. Plan:

* **M1** balanced-certificate arithmetic bridge (`IndependenceBarrier.lean`): `F·a² ≤ Ī(T)^n` from a
  balanced certificate; `R ≤ F·M^f → R^{2/f} ≤ F·M²` for `f ≥ 2`. Trivial.
* **M2** zeroing out ⊂ coordinate Galactic certificate (`IndependenceBarrier.lean`): weights
  `w i v = if v ∈ A i then 0 else 1`, `d = 0`, so `minimumWeightPart w 0 = coordinateZeroOut`. Small.
* **M3** coordinate block words (`Tensor/CoordinateBlockWord.lean`, new): `coordinateBlockZeroOut`
  and its identification with `coordinateExtend ∘ coordinateDirectSum` under `HasUniqueLegFibers` /
  `IsLegwiseInjective` (reusing the predicates of `Tensor/PartitionedExtraction.lean`,
  `Tensor/PartitionedDirectSum.lean`); `coordinatePower` needs no `TensorProduct` reassociation. Medium.
* **M4** heterogeneous MM word products (`MatrixMultiplication/IndependentDiagonal.lean`):
  `mmWordIndexEquiv`/`coordinateRelabel_mmWordIndexEquiv` generalizing `mmPowerIndexEquiv` from
  `Fin k → Fin m` to `∀ t, Fin (m t)` (`finPiFinEquiv`). Medium.
* **M5** coordinate easy-CW extraction (`Examples/CoppersmithWinogradEasyCoordinate.lean`, new):
  `∃ copies, 27^k·roth(M/2) ≤ 6k²M²·copies ∧ CoordinateGalacticCertificate (gcwEasyTable) (3k) (q^k)³ copies`,
  consuming the easy-hashing combinatorics unchanged; the constituents are coordinate pullbacks
  (`cw011Map = funLeft (cw011Index)`); `σ` is a global legwise relabelling. Large, tractable.
* **M6** the limit (`easyCW_independence_base_inequality : (27/4)q² ≤ Ī(gcwTable)^3`) after the
  Behrend-rate extraction; via `le_of_pow_succ_le_subexponential_mul_pow_succ`
  and `asymptoticIndependenceNumber_coordinateZeroOut_le`. Small.
* **M7** Theorem 7.3 + Remark 7.2 (`Examples/GeneralizedCoppersmithWinogradIndependenceLower.lean`, new):
  `(q+2)^{2/f(q)} ≤ Ī(gcwTable)`; Remark 7.2 strengthened to `q ≥ 2` by `nlinarith`; sandwich with
  `asymptoticIndependenceNumber_gcwTable_le_cornerBound`. Small. Erratum: AVW say "every positive
  integer q" but `f(1)` is undefined.
* **M8** by-product `ω_g^coord(CW_q^σ) ≤ f(q)` from the M5 certificate ∈ `coordinateGalacticValues`.
* **M9** Theorem 7.4 (`Examples/GroupTensorBarrier.lean`): `Ī(T_G) ≥ Ī(gcwTable_{|G|−2})` through
  `groupTensorMul_monomialDegenerates_isGeneralizedCW` — check that `avwTarget_isomorphic_genCW` is a
  coordinate relabelling; `|G| < 5` by explicit certificates.
**STATUS 2026-08-26: M1–M7 PROVED.** `avw_theorem_seven_three`, `avw_remark_seven_two` (for `q ≥ 2`),
`avw_gcwTable_independence_sandwich`, and `easyCW_independence_base_inequality : (27/4)q² ≤ Ī(CW_q^σ)³`
(`Examples/GeneralizedCoppersmithWinogradIndependenceLower.lean`, `Examples/CoppersmithWinogradEasyCoordinate.lean`).
Errata: `f(1)` is undefined (AVW say "every positive integer q"); Remark 7.2 holds from `q ≥ 2`; footnote 9's
symmetric zeroing out is unnecessary.
**M8 PROVED 2026-08-26** (`Examples/GeneralizedCoppersmithWinogradGalacticUpper.lean`,
`Examples/GeneralizedCoppersmithWinogradBorderRank.lean`):
`coordinateGalacticExponent_gcwTable_le_avwF` (`ω_g^coord(CW_q^σ) ≤ f(q)` for `q ≥ 2` from the hypothesis
`R̲(genCW K μ σ) ≤ q+2`), `coordinateGalacticExponent_gcwTable_refl_le_avwF` (hypothesis discharged for `σ = id`
via `genCW_borderRankLE_refl`), the sandwich `avw_galactic_exponent_gcwTable_sandwich`
(`2 + 1/15000 ≤ ω_g^coord(CW_q) ≤ f(q)`) and the numeric instance
`avw_galactic_exponent_gcwTable_fin_six` (`2 + 1/15000 ≤ ω_g^coord(CW_6) ≤ 2.416`, from
`avwF 6 ∈ [2.4159, 2.416]` and the new `Analysis/LogConstants.log_three_ge`).  Generic pieces added:
`CoordinateGalacticCertificate.of_coordinateZeroOut` (`IndependenceBarrier.lean`, a certificate for a zeroing out
is one for the source table — the easy-to-full-table step),
`Growth.exists_forall_pow_le_copies` (`Analysis/BehrendRate.lean`, the copy-count reading of the Behrend rate
argument: `W < A/D` forces `W^k ≤ copies` eventually) and `Growth.Subexponential.eventually_le_pow`
(`Analysis/Subexponential.lean`).
**Erratum (new, ours not AVW's): `R̲(CW_q^σ) = q+2` is FALSE unless `σ² = id`.**  The `CW_q^σ` `Z`-slices are
`M_{z_0} = E_{0,q+1} + E_{q+1,0} + ∑_i E_{i,σi}` (a permutation matrix, so the tensor is 1-generic),
`M_{z_i} = E_{i,0} + E_{0,i}`, `M_{z_{q+1}} = E_{0,0}`; normalizing, `A_{z_i} = E_{σi,0} + E_{q+1,i}` and
`[A_{z_i}, A_{z_j}] = ([i = σj] − [j = σi])·E_{q+1,0}`, which vanishes for all `i,j` iff `σ = σ⁻¹`.  By Strassen's
commutation equations minimal border rank then fails for every non-involutive `σ` (already a 3-cycle at `q = 3`),
so `R̲(CW_q^σ) ≥ q+3`.  This vindicates AVW's conditional phrasing of Definition 3.1 and the non-goal recorded in
`Examples/GeneralizedCoppersmithWinograd.lean`; formalizing the `≥ q+3` half needs Strassen's equations, which the
repository does not have (open: `Tensor/StrassenEquations.lean`).  M8 is therefore stated with the border-rank
bound as an explicit hypothesis, discharged for the classical member `σ = id` — which is exactly the member
AVW's Definition 4.1 loop is about.
**M9 PROVED 2026-08-26** (`Examples/GroupTensorIndependenceLower.lean`): `avw_theorem_seven_four` (|G| ≥ 4, constant
`avwGroupExponent |G| = 2/f(|G|−2)`), `avw_theorem_seven_four_exists_of_four_le` (∃ c > 2/3 for |G| ≥ 4 — AVW need ≥ 5),
`Ī(T_G) = supermultiplicativeLimit (triColoredSumFreeNumber (Fin n → G))`, `avw_theorem_seven_four_triColoredSumFree`
(`|G|^{(c−ε)n} ≤ f(Gⁿ)` eventually), and `le_sawinConstant` (any Sawin constant satisfies `(27/4)(|G|−2)² ≤ (δ|G|)³`;
`δ ≥ 3/4` at order 4). Open: orders 2 and 3 (KSS, not formalized).

Research-scale: none. The numeric `q = 6` warm-up is not worth doing first (six constituents,
non-uniform type); instantiate the finished machinery on the first-power file afterwards
(`Ī(CW_6) ≥ 6.4194…`, AVW Remark 7.3). **Done 2026-08-27**: `avw_remark_seven_three : 6 + 419/1000 ≤ Ī(CW_6^σ)` via the shared `MatrixMultiplication/CoordinateBlockCertificate.lean` (both CW clients are instances); the exact value for the repository's rational type is `6.41933…`, so AVW's `6.4194` is a rounding of the exact optimizer, not attainable from the certified type.

**N. Lower triangular tensors** (`Examples/LowerTriangularBarrier.lean`). *Theorem 7.5 PROVED 2026-08-26* (`avw_theorem_seven_five`, explicit constant `6/(3 − cornerExponent q)` for every `q ≥ 2` via Corollary 5.1 — AVW leave `c_q` unnamed; the trivial half `Ī(T) ≤ q` of Theorem 7.6 and Definition 7.1 are also in; the hard half of 7.6 is open). **Theorem 7.6 PROVED 2026-08-27** (`Examples/LowerTriangularDiagonal.lean`: `avw_theorem_seven_six : Ī(T) = q ↔ HasIndependentDiagonal T` for `2 ≤ q`, quantitative form `Ī ≤ q^{1 − diagonalExponent q}` otherwise, no field needed; `CornerBarrier` generalized to an arbitrary gap). *Scoping note:* the hard half is not research-scale —
AVW's `O_q(κ)` bookkeeping has the closed form `c_j = q·2^j − q + 1`, so the strong induction is an ordinary induction on the
antidiagonal position with explicit constant `diagonalExponent q = 1/((q(1 + q2^q − q²))² log q)` (exponentially small in `q`, so
Theorem 7.5 stays the sharper statement for `T_q^lower`). Errata found: Definition 7.1's `z` index range `{1..q}` should be
`{0..q−1}`; `κ` is conflated with the window deficit `sqrt((δ+κ) ln q)`; a free index `i` in the inductive step; the
"assume such a term exists" case split is unnecessary (absent terms have mass 0 and the induction forces the diagonal to
exist); negative weights vs the ℕ-valued interface; "lower diagonal" for "lower triangular". Theorem 7.5 is a direct
application of Corollary 5.1 (needs I). Theorem 7.6 characterizes `Ī(T) = q` for lower-triangular
`T` and needs Theorem 5.2 plus a strong induction with `O_q(κ)` bookkeeping; the `O_q` notation
must be replaced by explicit constants. *Hard*.

**Optional, small, and worth doing early: the basis-dependence witness.** Formalize the `ℚ`
example of §1 — `⟨2⟩` has `I = 2`, its image under the legwise change of basis `[[1,1],[1,−1]]`
is `2·T_{C₂}`, whose four support triples pairwise share a coordinate, so `I = 1`. It is a
finite computation plus one explicit legwise isomorphism, and it puts on the record the reason
`independenceNumber` is a function of the coefficient table and not of the abstract tensor.
*Tractable.*

Recommended order: **A → B → C → E → D → F**, then **G → I → J**, then **K**; **M**'s Theorem 7.2
can be done at any time and is the best early win; **L** only after the named-obligation policy
for Sawin is settled.

---

**Sharpening 2026-08-26 (binary Pinsker → exact AVW constants).** `Combinatorics/BinomialTail.lean` now has
`tailExponent ε = 2ε²`; Theorem 5.2's window is AVW's `1/q − sqrt((δ+ρ) log q)` and
`cornerExponent q = 1/(q²(q+1)² log q)` is AVW's printed Corollary 5.1 constant (no factor 2 left).
Consequence for Theorem 7.1: `6/(3 − cornerExponent 7) ≈ 2.0001093 > 60000/29999 ≈ 2.0000667`, so
`avwTheoremSevenOneConstant = 60000/29999` — the binding regime is now the `q ≥ 6` splitting route, and
the certified bound is `2 + 1/15000 ≤ avwTheoremSevenOneConstant` (`1/14999` would be false). Theorem 7.5's
constant `6/(3 − cornerExponent q)` sharpened definitionally.

---

**Fit pass 2026-08-26 (applied).** One positionwise product `Tensor.coordinateWordProduct` (constant case
`coordinatePower`; M3 block-word tables and M4 `mmWordCoefficients` are `rfl`-instances); one pivot-leg
certificate lemma `coordinateGalacticCertificate_of_pivot_bijection` (the lower-triangular, group-tensor and GCW
certificates are instantiations); the corner→barrier chain lives once in `MatrixMultiplication/CornerBarrier.lean`;
`cornerExponent`/`cornerBound` are in `AlgebraicComplexity`, not `Tensor`; M5's generic helpers promoted
(`blockAddressWordEquiv`, `rothNumberNat_pos`, `mmIndexCongr`). Remaining: the two new sections of
`Tensor/MonomialIndependence.lean` into its namespace; the fourfold `log 2` enclosure (non-mechanical).

---

**Block-partition entropy bound (thesis Thm 5.3 for Ī) — landed 2026-08-27.** `Tensor/IndependenceBlockEntropy.lean`
(`asymptoticIndependenceNumber_le_of_blockEntropy`, loss-free method of types: one term of the multinomial expansion)
and `Examples/GeneralizedCoppersmithWinogradIndependenceUpper.lean`: `Ī(CW_q^σ) ≤ u^{1/3}(q + u + 1/u)` for every `u > 0`
(the Legendre dual of Alman's `sup_v` formula), certified `Ī(CW_6^σ) ≤ 6.45` (thesis 6.44493), `Ī(CW_1^σ) ≤ 2.7552`, and
the Galactic barrier `ω_g^coord(CW_6^σ) ≥ 29/14 = 2.0714…` (was 2.0000666…). Theorem 7.1's universal constant would
become ≈ 2.02708 (binding at q = 0, corner route) or ≈ 2.05305 with an entropy bound at q = 0 — not yet re-derived.

---

**Theorem 7.1 sharpened via the entropy bound — 2026-08-27.** `avwTheoremSevenOneSharpConstant =
6/(3 − cornerExponent 2) = 2.027078…`, certified `2 + 27/1000 ≤ …` (`avw_theorem_seven_one_sharp_unconditional`,
`Examples/GeneralizedCoppersmithWinogradSharpBarrier.lean`). Uniform entropy exponent `s₀ = 93/100` for all
`q ≥ 1` (`gcw_entropy_rpow_bound`, rational certificate `u_q = 2/(q+2)`; per-`q` sharp `s(1) = 0.92610`); the
binding route is now the `q = 0` corner case (`CW_0^σ` = the 2×2×2 table `x₀y₀z₁+x₀y₁z₀+x₁y₀z₀`,
handled only by `cornerExponent 2 = 1/(36 log 2)`) — to beat 2.0271, bound `Ī(CW_0)` directly.

**Strassen commutation equations — 2026-08-27.** `Tensor/StrassenEquations.lean`
(`normalizedSlices_commute_of_borderRankLE`, any `CommRing`, division-free) and
`Examples/GeneralizedCoppersmithWinogradStrassen.lean`: `R̲(CW_q^σ) ≥ q+3` for every non-involutive `σ`
(`borderRank_genCW_ge_of_not_involutive`) and the involutive slices commute — the M8 dichotomy is proved.
Open: the general inequality `2(R̲−n) ≥ rank[A_i,A_j]`, and a `Z`-basis-change wrapper (unlocks `R̲⟨2,2,2⟩ ≥ 5`).

---

**Thesis S̃ track — 2026-08-27.** Theorem 5.3 for slice rank (`Tensor/SliceRankBlockEntropy.lean`),
`S̃(CW_q^σ) ≤ u^{1/3}(q+u+1/u)` with `S̃(CW_6) ≤ 6.45`, Theorem 5.1 at S̃
(`MatrixMultiplication/UniversalSliceRankBarrier.lean`), and Theorem 5.7:
`13/6 ≤ ω_u(CW_q^σ)` for every field, q ≥ 1, σ — all conditional only on
`SliceRankDegenerationMonotone`. The thesis constant 2.16805 needs 8-digit log enclosures
(rational-certificate cap 2.16797 at exponent 12/13); recorded as future work.

---

**M9b PROVED 2026-08-27** (`avw_theorem_seven_four_exists_of_two_le`; small-group Ī bounds `1.84/2.629/3.31`; Sawin δ ≥ `92/100`/`876/1000`/`828/1000` at orders 2/3/4). *Original scoping:* Theorem 7.4 for ALL finite groups, no KSS.** The exact power law
`Ī(T_G)ⁿ = Ī(T_{Gⁿ})` (`coordinatePower_groupCoefficients` is an equality of functions;
`asymptoticIndependenceNumber_coordinatePower`) lifts the cube form from `Gⁿ` to `G` losslessly:
`27/4·(|G|ⁿ−2)² ≤ Ī(T_G)^{3n}`, and `avwCubeExponent(mⁿ)` IS the resulting exponent for `m` (no division).
Optimal `n`: 3 for C₂ (`Ī ≥ 3^{5/9} = 1.8411`, c = 0.880535), 2 for C₃ (`Ī ≥ (1323/4)^{1/6} = 2.6298`,
c = 0.880105), 2 for order 4 (`Ī ≥ 1323^{1/6} = 3.3133`, up from 3); n = 1 optimal for |G| ≥ 5. Ceiling of the
route: `avwCubeExponent 8 = 0.880535`. Consistency: all bounds sit below the true capacities
(`3/2^{2/3} = 1.8899` for C₂, `2.7551` for C₃ — NOT claimed; their proofs are char-p slice rank + KSS).
Upgrades `le_sawinConstant`: `δ(C₂) ≥ 0.9205`, `δ(C₃) ≥ 0.8766`. Optional M9c: the first-power bound gives
`c₂ → 0.894116` nearly free (`avw_remark_seven_three` at |G| = 8) and `c₃ → 0.890732` with one `q = 7` numeric.
Finite tri-colored certificates are a measured dead end (`f(C₂⁴) = 6` ⇒ c = 0.6462 < 2/3). Full KSS (M9e)
remains only for the sharp constants; research-scale; needs S₃-symmetric LP duality + a deletion argument.

---

## 7. Acceptance criteria and non-goals

Acceptance, per `DESIGN.md`:

* every module carries a module doc with layer placement and exact AVW numbering;
* every literature-facing theorem gets an `#assert_axioms` entry in `AxiomAudit.lean`;
* no `sorry`, `axiom`, `opaque`, `native_decide`, or `grind`; every unproved deep input (Sawin;
  the Schönhage equal-dimension reduction if route (ii) of D is not taken) appears as an explicit
  `Prop` hypothesis of the final statement;
* all numerics via exact rational arithmetic or proved enclosures (`Analysis/Log.lean`), with the
  rounding direction checked — the `7.9973 < 8` and `3(q+1)^{2/3} < q^{0.997}` certificates in
  particular;
* every erratum found in the source is recorded here and in the relevant module doc, with the
  corrected statement actually formalized (currently: the `μ = (q+1)²`/`q ≥ 30` correction in K,
  and the `ω_g(CW_q) ≥ f(q)` sign in M).

Explicit non-goals for this program: asymptotic slice rank; semicontinuity of slice rank under
degeneration; the Universal method exponent `ω_u`; the Cohn–Umans group-theoretic method as a
separate framework (declined in `LOWER_BOUNDS_ROADMAP.md`); Strassen support functionals and the
CVZ irreversibility reformulation (deferred there); and any claim that a bound on `sliceRank(T)`
alone constrains `ω_g(T)`.
