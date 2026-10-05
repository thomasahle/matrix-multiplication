/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.RationalTypedLeafCore
import AlgebraicComplexity.MatrixMultiplication.ZeroCoordinateMerge

/-!
# Merged rational typed leaves

A rational typed leaf gives each support letter three matrix dimensions and multiplies them along
a proportional word.  In a laser-method extraction whose nodes have a *zero coordinate* that table
is not the only sound one: a zero block's whole selected class shares the other two block words, so
the class enters **one** matrix dimension as `ZeroCoordinateMerge.mergedDimension q ones cls`,
rather than a single representative entering as its own `q ^ ones s`.

`MatrixMultiplication/CoarsenedRationalTypedLeaf.lean` deliberately declines to supply that reading
— *"Matrix dimensions are definitionally the original fine-leaf dimensions; coarsening costs no copy
and contributes no extra entropy term"* (`:500-501`) — and it is right to, because a *coarsening* of
the block alphabet really does not create one.  The merge is a different operation: it does not
coarsen the alphabet, it keeps the whole shared-leg class as one C-tensor.  This module supplies
the leaf datum for it.

## The residual convention — read this before instantiating anything

The structure stores a leaf called `residual`, **not** the committed fine leaf.  On the designated
leg `residual.dimension i mergeLeg` must record everything *except* the merged classes' own
contribution, because the merged dimension is put in by multiplication:

```
merged.dimension i mergeLeg = residual.dimension i mergeLeg * mergedFactor i
```

and `ofZeroClasses` sets `mergedFactor i = ∑ s ∈ cls i, q ^ ones i s`, which **already
contains** the class's local `q`-power.  Instantiating `residual` with a leaf whose designated
dimension still carries that `q ^ k` would double-count it: at a uniform class the product would
read `q ^ k · (card · q ^ k)` where the committed one-slice fusion supplies only `card · q ^ k`.
Codex C2 caught exactly this ambiguity in review; the convention above is its resolution, and
the honest bridge back to the fine reading is proved rather than asserted —

* `representativeLeaf residual mergeLeg q hq k` is the **fine (representative) leaf**: the residual
  leaf with the designated leg multiplied by each class's own `q ^ k i`.  This is the reading E2's
  FINE row measures.
* `dimensionProduct_mergeLeg_eq_classCardProduct_mul_representative` is the exact factorization at
  uniform local powers:

  ```
  merged.dimensionProduct mergeLeg = classCardProduct · representative.dimensionProduct mergeLeg
  ```

  So the exact multiplier of the merge over the fine reading is the product of the classes'
  **cardinalities** — `card`, not `card · q ^ k` — and `log₂` of it is precisely the `H(p)` term
  E1's volume decomposition places on each zero block's own coordinate, i.e. E2's missing
  `46.414` bits per `38`-word stride block (`better_bound/r4_scoping/E2_LATTICE.md` §1 and §4).
  This theorem, not `classCardProduct_mul_residual_le_dimensionProduct_mergeLeg`, is the statement
  a certificate client should cite against E2.

## What else is here

* `RationalTypedLeaf.scaleLeg` — multiply one leg's dimension table by a positive per-letter
  factor, with the two dimension-product laws (`scaleLeg_dimensionProduct_mergeLeg` and
  `scaleLeg_dimensionProduct_of_ne`).  Both the merged leaf and the representative leaf are
  instances, so the bookkeeping is proved once.
* `MergedRationalTypedLeaf.toRationalTypedLeaf` — **a merged leaf is a rational typed leaf**: every
  committed typed-leaf theorem applies to it verbatim.  What changes is only which per-letter
  degeneration a client must supply; see "The honest gap".
* `ofZeroClasses` and its four comparisons against the class: `pow_ones_le_mergedFactor`,
  `card_le_mergedFactor`, `card_mul_pow_le_mergedFactor`, and
  `mergedFactor_eq_card_mul_pow_of_uniform` — the last being the exact shape the *committed* uniform
  one-slice fusion produces,
  `UniformPowerFusion.restricts_matrixMultiplication_mergedDimension`.
* `restricts_matrixMultiplication_mergeX/Y/Z` — the leg-named `Restricts`-level absorptions of a
  merged one-slice factor `⟨N,1,1⟩`, `⟨1,N,1⟩`, `⟨1,1,N⟩` into a residual degeneration.  These are
  the `Restricts` siblings of `ZeroCoordinateMerge.mergeX/mergeY/mergeZ`, which do the same at the
  `WholeConstituentLaserVolumeStage` level; both rest on the committed isomorphism
  `Tensor.Isomorphic.matrixMultiplication_external`.

## Leg convention

Every statement is in Lean's `(X, Y, Z)` **matrix-shape leg** order, and `mergeLeg` is a `Leg`.
The certificate's volume coordinate `c` is the leg `(c + 2) % 3`
(`MatrixMultiplication.SimplifiedSequencePackaging.legOfCertificateCoordinate`,
`better_bound/r4_scoping/OBLIGATIONS.md` §9.1/§9.8); the rotation is **not** applied here, exactly
as in `ZeroCoordinateMerge` and `UniformPowerFusion`.  A certificate client applies it once, and
`MatrixMultiplication/MergedLeafBudget.lean` is where that happens for the total-weight track.
The committed one-slice fusion produces its merged dimension on `Y`
(`ZeroCoordinateMerge.mergeY`), so `mergeLeg = .Y` is the orientation available today; the other two
are reached by the committed orientation retyping and need no change here.

## The honest gap

Nothing in this module produces a merged degeneration.  A `MergedRationalTypedLeaf` is *data*, and
the per-letter hypothesis `∀ s, Restricts (P.constituent s) ⟨merged .X, merged .Y, merged .Z⟩` that
every typed-leaf consumer takes is exactly what a merged leaf cannot get from the fine chunk
dimension table (`Examples.cwChunk_constituent_restricts_of_leaf_dimension_eq`): it must come from
the zero-coordinate one-slice fusion, and that fusion still rests on the shared-`Z` map coherence
named in `OBLIGATIONS.md` §9.9.  In the residual convention the semantic obligation is precisely
`constituent ≽ external (residual leaf) ⟨1, N, 1⟩`, which is the shape
`restricts_matrixMultiplication_mergeY` consumes.  What this module removes is the *bookkeeping*
obstruction — that no committed leaf datum could even carry a merged dimension — not the semantic
one.
-/

open scoped BigOperators

namespace AlgebraicComplexity

open Tensor

universe u v w z

namespace RationalTypedLeaf

variable {I : Type u} {A : Leg → Type v}

/-! ## Scaling one leg of a leaf

Both readings this module compares — the merged leaf and the fine representative leaf — are the
same residual leaf with one leg multiplied by a positive per-letter factor.  Proving the dimension
product laws once, here, is what makes the comparison between them a one-line rewrite. -/

/-- Multiply one leg of a leaf's dimension table by a positive per-letter factor. -/
def scaleLeg (base : RationalTypedLeaf I A) (mergeLeg : Leg) (factor : I → ℕ)
    (hfactor : ∀ i, 0 < factor i) : RationalTypedLeaf I A where
  profile := base.profile
  coordinate := base.coordinate
  dimension := fun i c ↦
    if c = mergeLeg then base.dimension i c * factor i else base.dimension i c
  dimension_pos := by
    intro i c
    by_cases hc : c = mergeLeg
    · simpa [hc] using Nat.mul_pos (base.dimension_pos i c) (hfactor i)
    · simpa [hc] using base.dimension_pos i c

@[simp] theorem scaleLeg_profile (base : RationalTypedLeaf I A) (mergeLeg : Leg) (factor : I → ℕ)
    (hfactor : ∀ i, 0 < factor i) :
    (base.scaleLeg mergeLeg factor hfactor).profile = base.profile := rfl

@[simp] theorem scaleLeg_coordinate (base : RationalTypedLeaf I A) (mergeLeg : Leg)
    (factor : I → ℕ) (hfactor : ∀ i, 0 < factor i) :
    (base.scaleLeg mergeLeg factor hfactor).coordinate = base.coordinate := rfl

@[simp] theorem scaleLeg_dimension_self (base : RationalTypedLeaf I A) (mergeLeg : Leg)
    (factor : I → ℕ) (hfactor : ∀ i, 0 < factor i) (i : I) :
    (base.scaleLeg mergeLeg factor hfactor).dimension i mergeLeg =
      base.dimension i mergeLeg * factor i := by
  simp [scaleLeg]

theorem scaleLeg_dimension_of_ne (base : RationalTypedLeaf I A) (mergeLeg : Leg)
    (factor : I → ℕ) (hfactor : ∀ i, 0 < factor i) (i : I) {c : Leg} (hc : c ≠ mergeLeg) :
    (base.scaleLeg mergeLeg factor hfactor).dimension i c = base.dimension i c := by
  simp [scaleLeg, hc]

/-- Exact finite product of a per-letter factor along the primitive profile. -/
def legFactorProduct (base : RationalTypedLeaf I A) (factor : I → ℕ) : ℕ :=
  ∏ i ∈ base.profile.alphabet, factor i ^ base.profile.count i

theorem legFactorProduct_pos (base : RationalTypedLeaf I A) {factor : I → ℕ}
    (hfactor : ∀ i, 0 < factor i) : 0 < base.legFactorProduct factor :=
  Finset.prod_pos fun i _ ↦ pow_pos (hfactor i) _

/-- **The scaled leg's dimension product.**  Scaling one leg by a per-letter factor multiplies that
leg's dimension product by the factor's own product, and nothing else moves. -/
theorem scaleLeg_dimensionProduct_self (base : RationalTypedLeaf I A) (mergeLeg : Leg)
    (factor : I → ℕ) (hfactor : ∀ i, 0 < factor i) :
    (base.scaleLeg mergeLeg factor hfactor).dimensionProduct mergeLeg =
      base.dimensionProduct mergeLeg * base.legFactorProduct factor := by
  classical
  unfold dimensionProduct legFactorProduct
  calc ∏ i ∈ base.profile.alphabet,
        (base.scaleLeg mergeLeg factor hfactor).dimension i mergeLeg ^ base.profile.count i
      = ∏ i ∈ base.profile.alphabet,
          (base.dimension i mergeLeg ^ base.profile.count i *
            factor i ^ base.profile.count i) :=
        Finset.prod_congr rfl fun i _ ↦ by
          rw [scaleLeg_dimension_self, mul_pow]
    _ = _ := Finset.prod_mul_distrib

/-- The two undesignated legs are untouched by the scaling. -/
theorem scaleLeg_dimensionProduct_of_ne (base : RationalTypedLeaf I A) (mergeLeg : Leg)
    (factor : I → ℕ) (hfactor : ∀ i, 0 < factor i) {c : Leg} (hc : c ≠ mergeLeg) :
    (base.scaleLeg mergeLeg factor hfactor).dimensionProduct c = base.dimensionProduct c := by
  unfold dimensionProduct
  simp only [scaleLeg_profile]
  exact Finset.prod_congr rfl fun i _ ↦ by
    rw [scaleLeg_dimension_of_ne base mergeLeg factor hfactor i hc]

/-- Scaling never shrinks a leg. -/
theorem dimensionProduct_le_scaleLeg (base : RationalTypedLeaf I A) (mergeLeg : Leg)
    (factor : I → ℕ) (hfactor : ∀ i, 0 < factor i) (c : Leg) :
    base.dimensionProduct c ≤ (base.scaleLeg mergeLeg factor hfactor).dimensionProduct c := by
  by_cases hc : c = mergeLeg
  · subst hc
    rw [scaleLeg_dimensionProduct_self]
    exact Nat.le_mul_of_pos_right _ (base.legFactorProduct_pos hfactor)
  · rw [base.scaleLeg_dimensionProduct_of_ne mergeLeg factor hfactor hc]

end RationalTypedLeaf

/-- A rational typed leaf together with one designated leg and a positive per-letter factor to be
carried on that leg.

**`residual` is not the fine leaf.**  On the designated leg it must record the letter's contribution
*with the merged classes' own local power removed*, because `mergedFactor` — intended to be
`∑ s ∈ cls, q ^ ones s` — already contains that power.  The fine reading is recovered as
`MergedRationalTypedLeaf.representativeLeaf`, and the exact relation between the two is
`dimensionProduct_mergeLeg_eq_classCardProduct_mul_representative`. -/
structure MergedRationalTypedLeaf (I : Type u) (A : Leg → Type v) where
  /-- The leaf carrying everything on the designated leg *except* the merged classes' own local
  powers.  See the module doc: this is the residual reading, not E2's FINE row. -/
  residual : RationalTypedLeaf I A
  /-- The matrix-shape leg that carries the merged class dimension. -/
  mergeLeg : Leg
  /-- The merged class dimension of each support letter, `∑ s ∈ cls, q ^ ones s` for
  `ofZeroClasses`. -/
  mergedFactor : I → ℕ
  mergedFactor_pos : ∀ i, 0 < mergedFactor i

namespace MergedRationalTypedLeaf

variable {I : Type u} {A : Leg → Type v}

/-- **A merged leaf is a rational typed leaf.**  Its profile and coordinate labels are the residual
leaf's; only the dimension table moves, and only on the designated leg.  Consequently every
committed typed-leaf theorem — extraction, coarsening, hashing, segmented assembly — applies to a
merged leaf with no new interface. -/
def toRationalTypedLeaf (leaf : MergedRationalTypedLeaf I A) : RationalTypedLeaf I A :=
  leaf.residual.scaleLeg leaf.mergeLeg leaf.mergedFactor leaf.mergedFactor_pos

@[simp] theorem toRationalTypedLeaf_profile (leaf : MergedRationalTypedLeaf I A) :
    leaf.toRationalTypedLeaf.profile = leaf.residual.profile := rfl

@[simp] theorem toRationalTypedLeaf_coordinate (leaf : MergedRationalTypedLeaf I A) :
    leaf.toRationalTypedLeaf.coordinate = leaf.residual.coordinate := rfl

@[simp] theorem toRationalTypedLeaf_dimension_mergeLeg (leaf : MergedRationalTypedLeaf I A)
    (i : I) :
    leaf.toRationalTypedLeaf.dimension i leaf.mergeLeg =
      leaf.residual.dimension i leaf.mergeLeg * leaf.mergedFactor i :=
  leaf.residual.scaleLeg_dimension_self leaf.mergeLeg leaf.mergedFactor leaf.mergedFactor_pos i

theorem toRationalTypedLeaf_dimension_of_ne (leaf : MergedRationalTypedLeaf I A) (i : I)
    {c : Leg} (hc : c ≠ leaf.mergeLeg) :
    leaf.toRationalTypedLeaf.dimension i c = leaf.residual.dimension i c :=
  leaf.residual.scaleLeg_dimension_of_ne leaf.mergeLeg leaf.mergedFactor leaf.mergedFactor_pos i hc

/-! ## The dimension product -/

/-- Exact finite product of the merged factors along the primitive profile.  This is the whole of
what the merge adds to the residual reading on the designated leg. -/
def mergedFactorProduct (leaf : MergedRationalTypedLeaf I A) : ℕ :=
  leaf.residual.legFactorProduct leaf.mergedFactor

theorem mergedFactorProduct_pos (leaf : MergedRationalTypedLeaf I A) :
    0 < leaf.mergedFactorProduct :=
  leaf.residual.legFactorProduct_pos leaf.mergedFactor_pos

/-- **The exact bookkeeping.**  On the designated leg the merged dimension product is the residual
one times the merged factor product; the merge is multiplicative and enters in exactly one place. -/
theorem dimensionProduct_mergeLeg (leaf : MergedRationalTypedLeaf I A) :
    leaf.toRationalTypedLeaf.dimensionProduct leaf.mergeLeg =
      leaf.residual.dimensionProduct leaf.mergeLeg * leaf.mergedFactorProduct :=
  leaf.residual.scaleLeg_dimensionProduct_self leaf.mergeLeg leaf.mergedFactor
    leaf.mergedFactor_pos

/-- The two undesignated legs are untouched by the merge. -/
theorem dimensionProduct_of_ne (leaf : MergedRationalTypedLeaf I A) {c : Leg}
    (hc : c ≠ leaf.mergeLeg) :
    leaf.toRationalTypedLeaf.dimensionProduct c = leaf.residual.dimensionProduct c :=
  leaf.residual.scaleLeg_dimensionProduct_of_ne leaf.mergeLeg leaf.mergedFactor
    leaf.mergedFactor_pos hc

/-- The merge never shrinks a leg against the residual reading. -/
theorem residual_dimensionProduct_le (leaf : MergedRationalTypedLeaf I A) (c : Leg) :
    leaf.residual.dimensionProduct c ≤ leaf.toRationalTypedLeaf.dimensionProduct c :=
  leaf.residual.dimensionProduct_le_scaleLeg leaf.mergeLeg leaf.mergedFactor
    leaf.mergedFactor_pos c

/-! ## Merged factors that are zero-coordinate class dimensions -/

section ZeroClasses

variable {ι : Type w}

/-- **The merged leaf of a family of zero-coordinate classes.**  Letter `i`'s designated-leg
dimension is the residual one multiplied by `∑ s ∈ cls i, q ^ ones i s`, the merged dimension of
its class. -/
def ofZeroClasses (residual : RationalTypedLeaf I A) (mergeLeg : Leg)
    (q : ℕ) (hq : 0 < q) (ones : I → ι → ℕ) (cls : I → Finset ι)
    (hne : ∀ i, (cls i).Nonempty) : MergedRationalTypedLeaf I A where
  residual := residual
  mergeLeg := mergeLeg
  mergedFactor := fun i ↦ ZeroCoordinateMerge.mergedDimension q (ones i) (cls i)
  mergedFactor_pos := fun i ↦ ZeroCoordinateMerge.mergedDimension_pos q hq (ones i) (hne i)

@[simp] theorem ofZeroClasses_residual (residual : RationalTypedLeaf I A) (mergeLeg : Leg)
    (q : ℕ) (hq : 0 < q) (ones : I → ι → ℕ) (cls : I → Finset ι)
    (hne : ∀ i, (cls i).Nonempty) :
    (ofZeroClasses residual mergeLeg q hq ones cls hne).residual = residual := rfl

@[simp] theorem ofZeroClasses_mergeLeg (residual : RationalTypedLeaf I A) (mergeLeg : Leg)
    (q : ℕ) (hq : 0 < q) (ones : I → ι → ℕ) (cls : I → Finset ι)
    (hne : ∀ i, (cls i).Nonempty) :
    (ofZeroClasses residual mergeLeg q hq ones cls hne).mergeLeg = mergeLeg := rfl

@[simp] theorem ofZeroClasses_mergedFactor (residual : RationalTypedLeaf I A) (mergeLeg : Leg)
    (q : ℕ) (hq : 0 < q) (ones : I → ι → ℕ) (cls : I → Finset ι)
    (hne : ∀ i, (cls i).Nonempty) (i : I) :
    (ofZeroClasses residual mergeLeg q hq ones cls hne).mergedFactor i =
      ZeroCoordinateMerge.mergedDimension q (ones i) (cls i) := rfl

/-- Every fine address of a class is dominated by the class's merged factor. -/
theorem pow_ones_le_mergedFactor (residual : RationalTypedLeaf I A) (mergeLeg : Leg)
    (q : ℕ) (hq : 0 < q) (ones : I → ι → ℕ) (cls : I → Finset ι)
    (hne : ∀ i, (cls i).Nonempty) {i : I} {s : ι} (hs : s ∈ cls i) :
    q ^ ones i s ≤ (ofZeroClasses residual mergeLeg q hq ones cls hne).mergedFactor i :=
  ZeroCoordinateMerge.pow_ones_le_mergedDimension q (ones i) hs

/-- **The support-multiplicity content of one class.**  The merged factor dominates the class
cardinality, so the merge retains the whole exact type class rather than a representative. -/
theorem card_le_mergedFactor (residual : RationalTypedLeaf I A) (mergeLeg : Leg)
    {q : ℕ} (hq : 0 < q) (ones : I → ι → ℕ) (cls : I → Finset ι)
    (hne : ∀ i, (cls i).Nonempty) (i : I) :
    (cls i).card ≤ (ofZeroClasses residual mergeLeg q hq ones cls hne).mergedFactor i :=
  ZeroCoordinateMerge.card_le_mergedDimension hq (ones i) (cls i)

/-- **Cardinality times the class's own smallest local power.**  If `k` bounds `ones` from below on
the class, the merged factor is at least `card * q ^ k`.  Since the *fine* reading contributes
exactly the representative's `q ^ ones s` on this leg, this is the statement that the merge buys the
class cardinality on top of the fine power — made exact in
`dimensionProduct_mergeLeg_eq_classCardProduct_mul_representative`. -/
theorem card_mul_pow_le_mergedFactor (residual : RationalTypedLeaf I A) (mergeLeg : Leg)
    {q : ℕ} (hq : 0 < q) (ones : I → ι → ℕ) (cls : I → Finset ι)
    (hne : ∀ i, (cls i).Nonempty) {i : I} {k : ℕ} (hmin : ∀ s ∈ cls i, k ≤ ones i s) :
    (cls i).card * q ^ k ≤
      (ofZeroClasses residual mergeLeg q hq ones cls hne).mergedFactor i := by
  classical
  rw [ofZeroClasses_mergedFactor, ZeroCoordinateMerge.mergedDimension]
  calc (cls i).card * q ^ k = ∑ _s ∈ cls i, q ^ k := by
        simp [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ s ∈ cls i, q ^ ones i s :=
        Finset.sum_le_sum fun s hs ↦ Nat.pow_le_pow_right hq (hmin s hs)

/-- **The uniform case, exactly.**  On a class of constant `ones` the merged factor is
`card * q ^ k` — literally the dimension the committed one-slice fusion
`UniformPowerFusion.restricts_matrixMultiplication_mergedDimension` produces, so on such a class
the merged leaf costs nothing beyond that fusion. -/
theorem mergedFactor_eq_card_mul_pow_of_uniform (residual : RationalTypedLeaf I A) (mergeLeg : Leg)
    {q : ℕ} (hq : 0 < q) (ones : I → ι → ℕ) (cls : I → Finset ι)
    (hne : ∀ i, (cls i).Nonempty) {i : I} {k : ℕ} (huniform : ∀ s ∈ cls i, ones i s = k) :
    (ofZeroClasses residual mergeLeg q hq ones cls hne).mergedFactor i = (cls i).card * q ^ k :=
  ZeroCoordinateMerge.mergedDimension_of_uniform q (ones i) (cls i) huniform

/-! ### The fine reading, and the exact factorization between the two

`classCardProduct` is the exact integer whose base-two logarithm is E1's zero-coordinate entropy
term and E2's `46.414` bits per stride block. -/

/-- The product of the zero classes' cardinalities along the primitive profile. -/
def classCardProduct (profile : PositiveIntegralProfile I) (cls : I → Finset ι) : ℕ :=
  ∏ i ∈ profile.alphabet, (cls i).card ^ profile.count i

theorem classCardProduct_pos (profile : PositiveIntegralProfile I) (cls : I → Finset ι)
    (hne : ∀ i, (cls i).Nonempty) : 0 < classCardProduct profile cls :=
  Finset.prod_pos fun i _ ↦ pow_pos (Finset.card_pos.mpr (hne i)) _

/-- **The fine (representative) leaf.**  The residual leaf with the designated leg multiplied by
each class's own local power `q ^ k i` — that is, one representative address per zero class.  This
is the reading `Examples.cwChunkConstituentDimension` supplies, and the one E2's FINE row
measures. -/
def representativeLeaf (residual : RationalTypedLeaf I A) (mergeLeg : Leg)
    {q : ℕ} (hq : 0 < q) (k : I → ℕ) : RationalTypedLeaf I A :=
  residual.scaleLeg mergeLeg (fun i ↦ q ^ k i) fun i ↦ pow_pos hq (k i)

@[simp] theorem representativeLeaf_profile (residual : RationalTypedLeaf I A) (mergeLeg : Leg)
    {q : ℕ} (hq : 0 < q) (k : I → ℕ) :
    (representativeLeaf residual mergeLeg hq k).profile = residual.profile := rfl

theorem representativeLeaf_dimensionProduct_mergeLeg (residual : RationalTypedLeaf I A)
    (mergeLeg : Leg) {q : ℕ} (hq : 0 < q) (k : I → ℕ) :
    (representativeLeaf residual mergeLeg hq k).dimensionProduct mergeLeg =
      residual.dimensionProduct mergeLeg * residual.legFactorProduct fun i ↦ q ^ k i :=
  residual.scaleLeg_dimensionProduct_self mergeLeg _ _

/-- The merged factor product splits into the class-cardinality product and the fine reading's own
power product, whenever every class has constant `ones`. -/
theorem mergedFactorProduct_of_uniform (residual : RationalTypedLeaf I A) (mergeLeg : Leg)
    {q : ℕ} (hq : 0 < q) (ones : I → ι → ℕ) (cls : I → Finset ι)
    (hne : ∀ i, (cls i).Nonempty) (k : I → ℕ)
    (huniform : ∀ i, ∀ s ∈ cls i, ones i s = k i) :
    (ofZeroClasses residual mergeLeg q hq ones cls hne).mergedFactorProduct =
      classCardProduct residual.profile cls *
        residual.legFactorProduct fun i ↦ q ^ k i := by
  classical
  unfold mergedFactorProduct RationalTypedLeaf.legFactorProduct classCardProduct
  calc ∏ i ∈ residual.profile.alphabet,
        (ofZeroClasses residual mergeLeg q hq ones cls hne).mergedFactor i ^
          residual.profile.count i
      = ∏ i ∈ residual.profile.alphabet,
          ((cls i).card ^ residual.profile.count i *
            (q ^ k i) ^ residual.profile.count i) :=
        Finset.prod_congr rfl fun i _ ↦ by
          rw [mergedFactor_eq_card_mul_pow_of_uniform residual mergeLeg hq ones cls hne
            (huniform i), mul_pow]
    _ = _ := Finset.prod_mul_distrib

/-- **The exact multiplier of the merge over the fine reading.**

At uniform local powers the merged leaf's designated-leg dimension product is exactly the *fine*
one times the product of the classes' cardinalities.  The multiplier is `card`, **not**
`card · q ^ k`: the class's own local power is already inside the fine reading, and the merge adds
only the support multiplicity.

Taking `log₂`, the multiplier is `∑ i, count i · log₂ (card i)` — precisely the `H(p)` term E1's
volume decomposition places on each zero block's own coordinate, and precisely the `46.414` bits per
`38`-word stride block that E2 measured as missing from the committed fine reading
(`better_bound/r4_scoping/E2_LATTICE.md` §1, §4).  This is the theorem a certificate client cites
against E2; the residual comparison below is strictly weaker and must not be used for that. -/
theorem dimensionProduct_mergeLeg_eq_classCardProduct_mul_representative
    (residual : RationalTypedLeaf I A) (mergeLeg : Leg)
    {q : ℕ} (hq : 0 < q) (ones : I → ι → ℕ) (cls : I → Finset ι)
    (hne : ∀ i, (cls i).Nonempty) (k : I → ℕ)
    (huniform : ∀ i, ∀ s ∈ cls i, ones i s = k i) :
    (ofZeroClasses residual mergeLeg q hq ones cls
        hne).toRationalTypedLeaf.dimensionProduct mergeLeg =
      classCardProduct residual.profile cls *
        (representativeLeaf residual mergeLeg hq k).dimensionProduct mergeLeg := by
  have hmerged := (ofZeroClasses residual mergeLeg q hq ones cls hne).dimensionProduct_mergeLeg
  rw [ofZeroClasses_mergeLeg, ofZeroClasses_residual] at hmerged
  rw [hmerged, mergedFactorProduct_of_uniform residual mergeLeg hq ones cls hne k huniform,
    representativeLeaf_dimensionProduct_mergeLeg]
  ring

/-- **The merge never loses against the fine reading**, and it is the class cardinalities it
gains. -/
theorem representativeLeaf_dimensionProduct_le
    (residual : RationalTypedLeaf I A) (mergeLeg : Leg)
    {q : ℕ} (hq : 0 < q) (ones : I → ι → ℕ) (cls : I → Finset ι)
    (hne : ∀ i, (cls i).Nonempty) (k : I → ℕ)
    (huniform : ∀ i, ∀ s ∈ cls i, ones i s = k i) :
    (representativeLeaf residual mergeLeg hq k).dimensionProduct mergeLeg ≤
      (ofZeroClasses residual mergeLeg q hq ones cls
        hne).toRationalTypedLeaf.dimensionProduct mergeLeg := by
  rw [dimensionProduct_mergeLeg_eq_classCardProduct_mul_representative
    residual mergeLeg hq ones cls hne k huniform]
  exact Nat.le_mul_of_pos_left _ (classCardProduct_pos residual.profile cls hne)

/-- The class-cardinality product is a lower bound for the merged factor product with **no**
uniformity hypothesis.  Note carefully that the comparison is against the *residual* leaf, not the
fine one; for the fine comparison use
`dimensionProduct_mergeLeg_eq_classCardProduct_mul_representative`. -/
theorem classCardProduct_le_mergedFactorProduct (residual : RationalTypedLeaf I A) (mergeLeg : Leg)
    {q : ℕ} (hq : 0 < q) (ones : I → ι → ℕ) (cls : I → Finset ι)
    (hne : ∀ i, (cls i).Nonempty) :
    classCardProduct residual.profile cls ≤
      (ofZeroClasses residual mergeLeg q hq ones cls hne).mergedFactorProduct := by
  classical
  unfold classCardProduct mergedFactorProduct RationalTypedLeaf.legFactorProduct
  exact Finset.prod_le_prod' fun i _ ↦
    Nat.pow_le_pow_left (card_le_mergedFactor residual mergeLeg hq ones cls hne i) _

/-- The residual-side form of the same bound. -/
theorem classCardProduct_mul_residual_le_dimensionProduct_mergeLeg
    (residual : RationalTypedLeaf I A) (mergeLeg : Leg)
    {q : ℕ} (hq : 0 < q) (ones : I → ι → ℕ) (cls : I → Finset ι)
    (hne : ∀ i, (cls i).Nonempty) :
    classCardProduct residual.profile cls * residual.dimensionProduct mergeLeg ≤
      (ofZeroClasses residual mergeLeg q hq ones cls
        hne).toRationalTypedLeaf.dimensionProduct mergeLeg := by
  have hmerged := (ofZeroClasses residual mergeLeg q hq ones cls hne).dimensionProduct_mergeLeg
  rw [ofZeroClasses_mergeLeg, ofZeroClasses_residual] at hmerged
  rw [hmerged, mul_comm (residual.dimensionProduct mergeLeg)]
  exact Nat.mul_le_mul_right _
    (classCardProduct_le_mergedFactorProduct residual mergeLeg hq ones cls hne)

end ZeroClasses

/-! ## Absorbing a merged one-slice factor into a residual degeneration

`ZeroCoordinateMerge.mergeX/mergeY/mergeZ` absorb a merged `⟨N,1,1⟩` / `⟨1,N,1⟩` / `⟨1,1,N⟩` factor
into a `WholeConstituentLaserVolumeStage`.  The three theorems below do the same one level down, at
a bare `Restricts`, which is the shape the *letterwise* merged degeneration takes in the residual
convention: a letter's constituent degenerates to the external product of its residual part and its
zero classes' one-slice factor, and the two dimensions multiply on the designated leg only.

Both families rest on the same committed isomorphism
`Tensor.Isomorphic.matrixMultiplication_external`; neither is new tensor algebra. -/

section Absorption

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable {W : Leg → Type w} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]

/-- Absorb a merged `⟨N,1,1⟩` factor into a residual degeneration's `X` dimension. -/
theorem restricts_matrixMultiplication_mergeX
    {source : Tensor3 K V} {factor : Tensor3 K W} {xSize ySize zSize merged : ℕ}
    (hsource : Restricts source (matrixMultiplication (K := K) xSize ySize zSize))
    (hfactor : Restricts factor (matrixMultiplication (K := K) merged 1 1)) :
    Restricts (Tensor.external source factor)
      (matrixMultiplication (K := K) (xSize * merged) ySize zSize) := by
  refine ((hsource.external hfactor).trans
    (Tensor.Isomorphic.matrixMultiplication_external (K := K)
      xSize ySize zSize merged 1 1).restricts).trans ?_
  exact (Tensor.Isomorphic.matrixMultiplication_congr (K := K)
    rfl (mul_one _) (mul_one _)).restricts

/-- Absorb a merged `⟨1,N,1⟩` factor into a residual degeneration's `Y` dimension.  This is the
orientation the committed one-slice fusion produces. -/
theorem restricts_matrixMultiplication_mergeY
    {source : Tensor3 K V} {factor : Tensor3 K W} {xSize ySize zSize merged : ℕ}
    (hsource : Restricts source (matrixMultiplication (K := K) xSize ySize zSize))
    (hfactor : Restricts factor (matrixMultiplication (K := K) 1 merged 1)) :
    Restricts (Tensor.external source factor)
      (matrixMultiplication (K := K) xSize (ySize * merged) zSize) := by
  refine ((hsource.external hfactor).trans
    (Tensor.Isomorphic.matrixMultiplication_external (K := K)
      xSize ySize zSize 1 merged 1).restricts).trans ?_
  exact (Tensor.Isomorphic.matrixMultiplication_congr (K := K)
    (mul_one _) rfl (mul_one _)).restricts

/-- Absorb a merged `⟨1,1,N⟩` factor into a residual degeneration's `Z` dimension. -/
theorem restricts_matrixMultiplication_mergeZ
    {source : Tensor3 K V} {factor : Tensor3 K W} {xSize ySize zSize merged : ℕ}
    (hsource : Restricts source (matrixMultiplication (K := K) xSize ySize zSize))
    (hfactor : Restricts factor (matrixMultiplication (K := K) 1 1 merged)) :
    Restricts (Tensor.external source factor)
      (matrixMultiplication (K := K) xSize ySize (zSize * merged)) := by
  refine ((hsource.external hfactor).trans
    (Tensor.Isomorphic.matrixMultiplication_external (K := K)
      xSize ySize zSize 1 1 merged).restricts).trans ?_
  exact (Tensor.Isomorphic.matrixMultiplication_congr (K := K)
    (mul_one _) (mul_one _) rfl).restricts

end Absorption

end MergedRationalTypedLeaf

/-! ## Shrinking a stage's rectangular dimensions

A merged leaf produces a stage whose side lengths are its own dimension products; the packaging
interface asks for side lengths that are exact powers of the leaf base.  Passing from the former to
the latter is dimension monotonicity of `matrixMultiplication`, applied inside the direct sum.

This declaration is **generic laser-volume machinery** and belongs beside
`WholeConstituentLaserVolumeStage.precompose` and `.external` in
`MatrixMultiplication/WholeConstituentLaserVolumeAssembly.lean`; it is here only because that
module is not this lane's to edit.  Whoever owns it next: please lift it. -/
noncomputable def WholeConstituentLaserVolumeStage.shrinkDimensions
    {K : Type u} [CommSemiring K]
    {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
    {source : Tensor3 K V} {copies xSize ySize zSize xSmall ySmall zSmall : ℕ}
    (stage : WholeConstituentLaserVolumeStage.{u, v, z} K source copies xSize ySize zSize)
    (hx : xSmall ≤ xSize) (hy : ySmall ≤ ySize) (hz : zSmall ≤ zSize) :
    WholeConstituentLaserVolumeStage.{u, v, z} K source copies xSmall ySmall zSmall where
  I := stage.I
  fintypeI := stage.fintypeI
  card_I := stage.card_I
  source_restricts := by
    letI := stage.fintypeI
    refine stage.source_restricts.trans ?_
    have hshrink : Restricts
        (Tensor.indexedDirectSum
          (fun _i : stage.I ↦ matrixMultiplication (K := K) xSize ySize zSize))
        (Tensor.indexedDirectSum
          (fun _i : stage.I ↦ matrixMultiplication (K := K) xSmall ySmall zSmall)) :=
      Tensor.Restricts.indexedDirectSum
        fun _i ↦ matrixMultiplication_restricts (K := K) hx hy hz
    simpa only [matrixMultiplicationDirectSum] using hshrink

end AlgebraicComplexity
