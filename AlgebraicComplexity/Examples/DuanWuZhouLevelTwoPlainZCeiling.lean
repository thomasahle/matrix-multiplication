/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainMarginalSelect
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCompatibilityModel

/-!
# The `Z`-side isolation ceiling at the plain partition

Layer 4 (`AlgebraicComplexity/Examples/`).  The plain analogue of the two `Z`-side instance lemmas
of `Examples/DuanWuZhouLevelTwoCompatibilityModel.lean`, transcribed now that the §0 adjudication
has closed.

The generic content is unchanged and is not restated: `injOn_leg_of_compatibilityIsolated` and
`card_compatibilityIsolatedSupport_le_card_image` are fully generic in `A : Leg → Type w` and
survive the move to the plain partition verbatim.  Only the instance moves, and at the plain
partition the letterwise lift of a legwise model is `Tensor.positivePowerCompatible`, with no
orientations in sight --- `dwz63LabelCompat` and its soundness now serve directly as `hcompat`.

## What these say, and what they no longer obstruct

The ceiling is a property of the *signature*, not of the model: for every sound compatibility
relation the survivors of a `pivot` cleanup have pairwise distinct `pivot` labels, so the doubly
isolated support is capped by the number of distinct retained `Z`-block words.  Numerically that
cap binds --- `log dwz63TrueCopyRate = 1.0891743499950` against `H(α_Z) = 1.0796115207721`, an
excess of `0.0095628292229` nats per position, ratio `1.0096087` --- which is just branch two of
the count, `N_Z / p_comp > N_Z`, restated.

That is why `[DuanWuZhou2022]`'s retained triples share large `Z`-blocks
(`global_value.tex:28`), and why the block-address `Z` cleanup is **not** where the paper's
combination loss lives.  These lemmas are therefore kept as a *no-go record*, not as a step of the
endpoint: the hole route separates the copies at the fine level instead, where Additional
Zeroing-Out Step 2 makes each surviving small block useful for exactly one retained triple
(`usefulFor_of_notMem_dwz63HoleSet`), and the direct sum after repair is over the batch index `β`.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v

section ZCeiling

variable {R : Type v} [Field R]

/-- **The support left by the plain `Y` compatibility zero-out.** -/
noncomputable def dwz63PlainJointYIsolatedSupport (K : Type u) [CommRing K]
    (hinj : Function.Injective (cwSquareFieldValue (R := R))) (n t : ℕ)
    (markedWords : Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (compat : ∀ _leg : Leg, Fin 5 → CWSquareAddress → Prop) :=
  compatibilityIsolatedSupport (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed) .Y
    (positivePowerCompatible (A := fun _ : Leg ↦ Fin 5) (pivot := Leg.Y) (compat .Y) n)

/-- **The doubly compatibility-isolated retained support at the plain partition.** -/
noncomputable def dwz63PlainJointIsolatedSupport (K : Type u) [CommRing K]
    (hinj : Function.Injective (cwSquareFieldValue (R := R))) (n t : ℕ)
    (markedWords : Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (compat : ∀ _leg : Leg, Fin 5 → CWSquareAddress → Prop) :=
  compatibilityIsolatedSupport
    (dwz63PlainJointYIsolatedSupport K hinj n t markedWords B seed compat) .Z
    (positivePowerCompatible (A := fun _ : Leg ↦ Fin 5) (pivot := Leg.Z) (compat .Z) n)

/-- **The doubly isolated support is capped by the number of distinct retained `Z`-block words**,
uniformly in the legwise model `compat`.

`hsoundZ` is the `Z` soundness on the `Y`-isolated family, which
`Tensor.isCompatibilitySound_compatibilityIsolatedSupport` supplies from soundness on the retained
family for any legwise source model. -/
theorem card_dwz63PlainJointIsolatedSupport_le_card_zWords
    (K : Type u) [CommRing K] (hinj : Function.Injective (cwSquareFieldValue (R := R))) (n t : ℕ)
    (markedWords : Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (compat : ∀ _leg : Leg, Fin 5 → CWSquareAddress → Prop)
    (hsoundZ : IsCompatibilitySound
      (dwz63PlainJointYIsolatedSupport K hinj n t markedWords B seed compat) .Z
      (positivePowerCompatible (A := fun _ : Leg ↦ Fin 5) (pivot := Leg.Z) (compat .Z) n)) :
    (dwz63PlainJointIsolatedSupport K hinj n t markedWords B seed compat).card ≤
      ((dwz63PlainJointRetainedSupport K hinj n t markedWords B seed).image
        fun a ↦ a .Z).card := by
  classical
  have hcap := card_compatibilityIsolatedSupport_le_card_image
    (dwz63PlainJointYIsolatedSupport K hinj n t markedWords B seed compat) .Z
    (positivePowerCompatible (A := fun _ : Leg ↦ Fin 5) (pivot := Leg.Z) (compat .Z) n) hsoundZ
  refine hcap.trans (Finset.card_le_card (Finset.image_subset_image ?_))
  exact compatibilityIsolatedSupport_subset _ _ _

/-- **What any copy count forces on the `Z` side.**  Stated at a free exponent, so it applies both
to the per-position count and to its sixth power. -/
theorem dwz63_plainCopyCount_forces_card_zWords
    (K : Type u) [CommRing K] (hinj : Function.Injective (cwSquareFieldValue (R := R))) (n t : ℕ)
    (markedWords : Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (compat : ∀ _leg : Leg, Fin 5 → CWSquareAddress → Prop)
    (hsoundZ : IsCompatibilitySound
      (dwz63PlainJointYIsolatedSupport K hinj n t markedWords B seed compat) .Z
      (positivePowerCompatible (A := fun _ : Leg ↦ Fin 5) (pivot := Leg.Z) (compat .Z) n))
    {loss : ℝ} (hloss : 0 ≤ loss) {m : ℕ}
    (hcount : dwz63TrueCopyRate ^ m ≤
      loss * ((dwz63PlainJointIsolatedSupport K hinj n t markedWords B seed compat).card : ℝ)) :
    dwz63TrueCopyRate ^ m ≤
      loss * (((dwz63PlainJointRetainedSupport K hinj n t markedWords B seed).image
        fun a ↦ a .Z).card : ℝ) := by
  refine hcount.trans (mul_le_mul_of_nonneg_left ?_ hloss)
  exact_mod_cast card_dwz63PlainJointIsolatedSupport_le_card_zWords K hinj n t markedWords B seed
    compat hsoundZ

end ZCeiling

end AlgebraicComplexity.Examples
