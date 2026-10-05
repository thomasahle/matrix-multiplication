/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.MergedRationalTypedLeaf

/-!

## DORMANT AS A SEAM (2026-08-29 adjudication)

The `MergedLetterClassFactor` premise quantifies over raw chunk constituents; the board's
merged-seam fidelity verdict (codex-2.36x, accepted by the coordinator) shows that granularity
encodes a stronger, generally wrong construction — the class cardinality would be counted once
as copies and again as dimension, exactly the shape the E2 design memo excludes for C1b.
Every theorem here is kernel-true, but the premise is not honestly dischargeable for the e7987
certificate. The faithful seam is FAMILY-LEVEL: `encodedExactInterfacePowerRestriction/Product`
composed with `WholeConstituentLaserVolumeStage.external` (replacement module in flight,
codex-2.36x). Do not build count/repair work against this module's premise; consult the board's
"MERGED-SEAM VERDICT ADJUDICATED" entry.

# The letterwise premise of a merged typed leaf

Every typed-leaf consumer takes the per-letter degeneration

```
∀ i, Restricts (P.constituent i) ⟨leaf.dimension i .X, leaf.dimension i .Y, leaf.dimension i .Z⟩
```

and for a `MergedRationalTypedLeaf` that is the hypothesis `hmerged` of the merged cleanup
`cwTotalWeightFeatureYZCompatibilityCleanup_to_matrixMultiplicationDirectSum_of_mergedLeaf`.
This module reduces it to **one** named premise, in the shape the zero-coordinate fusion produces.

## Why an adapter is needed at all

The zero-coordinate fusion (`0e56cc6`, and its three-orientation form
`Examples.cwSelectedExactInterfaceTerm_zero_restricts_fusedOneSlice`) concludes *one family-level*
restriction, from a selected exact interface term's realization to `⟨1, |S| q^e, 1⟩`.  `hmerged`
instead quantifies over **each** support letter and targets the leaf's own three dimensions.  The
two statements are not the same shape, so the fusion cannot discharge `hmerged` literally; that was
checked independently by codex-2.36x and by Codex C2 on the board, and this module implements the
adapter half both verdicts describe.

## The one named premise

`MergedLetterClassFactor` says: each letter's constituent degenerates to the external product of
its **residual** matrix tensor and a one-slice factor of size `leaf.mergedFactor i`, placed on the
designated leg.  This is exactly the sentence `MergedRationalTypedLeaf`'s module doc names as the
semantic obligation of the residual convention —

> *"In the residual convention the semantic obligation is precisely
> `constituent ≽ external (residual leaf) ⟨1, N, 1⟩`, which is the shape
> `restricts_matrixMultiplication_mergeY` consumes."*

— and it is the only thing this module assumes.  What the fusion supplies is the *value* of that
one-slice factor: at a zero-coordinate class with uniform local power,
`MergedRationalTypedLeaf.mergedFactor_eq_card_mul_pow_of_uniform` rewrites `leaf.mergedFactor i` to
`(cls i).card * q ^ k`, which is the fused dimension `|S| q^e` of
`cwSelectedExactInterfaceTerm_zero_restricts_fusedOneSlice` once the class is identified with the
selected support and its cardinality is the type-class count of `0cf5dca`.

## Honest gap

This module proves the *bookkeeping* half — the absorption and the dimension rewrites — and nothing
else.  `MergedLetterClassFactor` is a hypothesis here, not a theorem: turning the family-level
fusion into a letterwise factorization is the remaining count/repair step, which the board assigns
to the B group together with the exact type-class cardinality.  No certificate inequality moves
here and `ω < 2.36999` is unchanged.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w z

namespace MergedRationalTypedLeaf

variable {K : Type u} [CommSemiring K]

/-! ## The merged one-slice factor -/

/-- The three dimensions of a merged one-slice factor of size `merged` on leg `mergeLeg`: `merged`
on the designated leg and `1` on the other two.  At `mergeLeg = .Y` this is `⟨1, merged, 1⟩`, the
shape the committed one-slice fusion produces. -/
def factorDimension (mergeLeg c : Leg) (merged : ℕ) : ℕ :=
  if c = mergeLeg then merged else 1

@[simp] theorem factorDimension_self (mergeLeg : Leg) (merged : ℕ) :
    factorDimension mergeLeg mergeLeg merged = merged := by
  simp [factorDimension]

theorem factorDimension_of_ne {mergeLeg c : Leg} (hc : c ≠ mergeLeg) (merged : ℕ) :
    factorDimension mergeLeg c merged = 1 := by
  simp [factorDimension, hc]

variable {I : Type z} {A : Leg → Type v}
variable {W : I → Leg → Type w}
variable [∀ i c, AddCommMonoid (W i c)] [∀ i c, Module K (W i c)]

/-- **The one named premise.**  Every support letter's constituent degenerates to the external
product of its residual matrix tensor and its own merged one-slice class factor.

This is the letterwise statement; the zero-coordinate fusion proves the corresponding *family*
statement, and closing the gap between the two is the count/repair step named in the module doc. -/
def MergedLetterClassFactor
    (leaf : MergedRationalTypedLeaf I A) (letter : ∀ i, Tensor3 K (W i)) : Prop :=
  ∀ i : I,
    Restricts (letter i)
      (Tensor.external
        (matrixMultiplication (K := K)
          (leaf.residual.dimension i .X)
          (leaf.residual.dimension i .Y)
          (leaf.residual.dimension i .Z))
        (matrixMultiplication (K := K)
          (factorDimension leaf.mergeLeg .X (leaf.mergedFactor i))
          (factorDimension leaf.mergeLeg .Y (leaf.mergedFactor i))
          (factorDimension leaf.mergeLeg .Z (leaf.mergedFactor i))))

/-! ## The adapter -/

/-- **The merged letterwise degeneration, from the residual factorization.**  This is exactly the
`hmerged` premise of the merged cleanup, obtained from `MergedLetterClassFactor` by the committed
absorptions `restricts_matrixMultiplication_mergeX / mergeY / mergeZ` and the two dimension rewrites
`toRationalTypedLeaf_dimension_mergeLeg` and `toRationalTypedLeaf_dimension_of_ne`.

No new tensor algebra: the absorption rests on `Tensor.Isomorphic.matrixMultiplication_external`,
and the leg case split is on the leaf's own designated leg. -/
theorem restricts_toRationalTypedLeaf_dimension_of_letterClassFactor
    (leaf : MergedRationalTypedLeaf I A) {letter : ∀ i, Tensor3 K (W i)}
    (hfactor : MergedLetterClassFactor leaf letter) (i : I) :
    Restricts (letter i)
      (matrixMultiplication (K := K)
        (leaf.toRationalTypedLeaf.dimension i .X)
        (leaf.toRationalTypedLeaf.dimension i .Y)
        (leaf.toRationalTypedLeaf.dimension i .Z)) := by
  have hresidual :
      Restricts
        (matrixMultiplication (K := K)
          (leaf.residual.dimension i .X)
          (leaf.residual.dimension i .Y)
          (leaf.residual.dimension i .Z))
        (matrixMultiplication (K := K)
          (leaf.residual.dimension i .X)
          (leaf.residual.dimension i .Y)
          (leaf.residual.dimension i .Z)) := Restricts.refl _
  cases hmerge : leaf.mergeLeg with
  | X =>
      have hdimX : leaf.toRationalTypedLeaf.dimension i .X =
          leaf.residual.dimension i .X * leaf.mergedFactor i := by
        rw [← hmerge]
        exact leaf.toRationalTypedLeaf_dimension_mergeLeg i
      have hdimY : leaf.toRationalTypedLeaf.dimension i .Y =
          leaf.residual.dimension i .Y :=
        leaf.toRationalTypedLeaf_dimension_of_ne i (by simp [hmerge])
      have hdimZ : leaf.toRationalTypedLeaf.dimension i .Z =
          leaf.residual.dimension i .Z :=
        leaf.toRationalTypedLeaf_dimension_of_ne i (by simp [hmerge])
      have hfactorLeg :
          Restricts
            (matrixMultiplication (K := K)
              (factorDimension leaf.mergeLeg .X (leaf.mergedFactor i))
              (factorDimension leaf.mergeLeg .Y (leaf.mergedFactor i))
              (factorDimension leaf.mergeLeg .Z (leaf.mergedFactor i)))
            (matrixMultiplication (K := K) (leaf.mergedFactor i) 1 1) := by
        rw [hmerge]
        exact Restricts.refl _
      rw [hdimX, hdimY, hdimZ]
      exact (hfactor i).trans (restricts_matrixMultiplication_mergeX hresidual hfactorLeg)
  | Y =>
      have hdimY : leaf.toRationalTypedLeaf.dimension i .Y =
          leaf.residual.dimension i .Y * leaf.mergedFactor i := by
        rw [← hmerge]
        exact leaf.toRationalTypedLeaf_dimension_mergeLeg i
      have hdimX : leaf.toRationalTypedLeaf.dimension i .X =
          leaf.residual.dimension i .X :=
        leaf.toRationalTypedLeaf_dimension_of_ne i (by simp [hmerge])
      have hdimZ : leaf.toRationalTypedLeaf.dimension i .Z =
          leaf.residual.dimension i .Z :=
        leaf.toRationalTypedLeaf_dimension_of_ne i (by simp [hmerge])
      have hfactorLeg :
          Restricts
            (matrixMultiplication (K := K)
              (factorDimension leaf.mergeLeg .X (leaf.mergedFactor i))
              (factorDimension leaf.mergeLeg .Y (leaf.mergedFactor i))
              (factorDimension leaf.mergeLeg .Z (leaf.mergedFactor i)))
            (matrixMultiplication (K := K) 1 (leaf.mergedFactor i) 1) := by
        rw [hmerge]
        exact Restricts.refl _
      rw [hdimX, hdimY, hdimZ]
      exact (hfactor i).trans (restricts_matrixMultiplication_mergeY hresidual hfactorLeg)
  | Z =>
      have hdimZ : leaf.toRationalTypedLeaf.dimension i .Z =
          leaf.residual.dimension i .Z * leaf.mergedFactor i := by
        rw [← hmerge]
        exact leaf.toRationalTypedLeaf_dimension_mergeLeg i
      have hdimX : leaf.toRationalTypedLeaf.dimension i .X =
          leaf.residual.dimension i .X :=
        leaf.toRationalTypedLeaf_dimension_of_ne i (by simp [hmerge])
      have hdimY : leaf.toRationalTypedLeaf.dimension i .Y =
          leaf.residual.dimension i .Y :=
        leaf.toRationalTypedLeaf_dimension_of_ne i (by simp [hmerge])
      have hfactorLeg :
          Restricts
            (matrixMultiplication (K := K)
              (factorDimension leaf.mergeLeg .X (leaf.mergedFactor i))
              (factorDimension leaf.mergeLeg .Y (leaf.mergedFactor i))
              (factorDimension leaf.mergeLeg .Z (leaf.mergedFactor i)))
            (matrixMultiplication (K := K) 1 1 (leaf.mergedFactor i)) := by
        rw [hmerge]
        exact Restricts.refl _
      rw [hdimX, hdimY, hdimZ]
      exact (hfactor i).trans (restricts_matrixMultiplication_mergeZ hresidual hfactorLeg)

end MergedRationalTypedLeaf

end AlgebraicComplexity
