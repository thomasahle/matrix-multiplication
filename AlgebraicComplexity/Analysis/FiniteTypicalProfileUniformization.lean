/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.ConditionalFeaturePenaltyRate
import AlgebraicComplexity.Combinatorics.TypeClassEntropyLowerCore

set_option autoImplicit false

/-!
# Uniform conditional-feature bounds over finite typical families

Claim 6.18 of [alman2025more] first bounds a compatibility numerator at each fixed empirical
fine profile, then takes the maximum over the finite family of profiles close to the prescribed
law.  This file formalizes that finite maximum and controls its loss as the common mass grows.  A
common mass and a uniform lower bound on empirical entropy turn the pointwise conditional-feature
estimate into one bound on the natural-valued supremum.

The varying repetition-one loss is bounded by a single envelope depending only on the alphabets
and common mass.  This matters because the existing subexponential theorem fixes the source
profile while varying its repetition, whereas Claim 6.18 varies the empirical source profile
itself.

This generic analysis leaf does not define the construction-specific typical alphabet, identify
the prescribed certificate law, divide the numerator by the symmetry denominator, or assert a
matrix-multiplication endpoint.

## Reference

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*, Claim 6.18;
  `papers/sources/2404.16349/constituent.tex:362-385,438-440`.
-/

namespace AlgebraicComplexity.WordType

universe u v w

/-- A source-profile-independent upper envelope for the conditional-feature loss at repetition
one and common source mass `N`.

The first factor enumerates possible joint types at the common mass, the second is the repetition
factor specialized to one, and the final factor is the uniform structural-zero multinomial loss. -/
noncomputable def conditionalFeatureEntropyLossOneEnvelope
    (S : Type u) [Fintype S] (T : Type v) [Fintype T] (N : ℕ) : ℝ :=
  ((((N + 1) ^ Fintype.card (S × T) : ℕ) : ℝ)) *
    ((((2 : ℕ) ^ Fintype.card (S × T) : ℕ) : ℝ)) *
      typeClassEntropyLoss S N

/-- Every repetition-one conditional-feature loss with mass `N` is bounded by the common
envelope.

Proof sketch: the two type-selection factors become the envelope's first two factors after the
mass equality is substituted.  Membership in the exact type class follows from that same mass
equality, so the structural-zero loss is bounded by `typeClassEntropyLoss`. -/
theorem conditionalFeatureEntropyLoss_one_le_envelope
    {S : Type u} {T : Type v} [Fintype S] [Fintype T]
    (sourceProfile : S → ℕ) (N : ℕ)
    (hmass : profileMass sourceProfile = N) :
    conditionalFeatureEntropyLoss T sourceProfile 1 ≤
      conditionalFeatureEntropyLossOneEnvelope S T N := by
  have htype : sourceProfile ∈ types S N := by
    rw [mem_types]
    exact hmass
  have hzero : structuralZeroMultinomialLoss sourceProfile 1 ≤
      typeClassEntropyLoss S N :=
    structuralZeroMultinomialLoss_one_le_typeClassEntropyLoss htype
  unfold conditionalFeatureEntropyLoss conditionalFeatureEntropyLossOneEnvelope
  rw [hmass]
  norm_num
  exact mul_le_mul_of_nonneg_left hzero (by positivity)

/-- For fixed finite alphabets, the common repetition-one envelope is subexponential in its
source mass.

Proof sketch: after unfolding `typeClassEntropyLoss`, the envelope is a nonnegative constant
times two powers of `N + 1`.  Successor polynomials are subexponential, and that class is closed
under products and multiplication by a nonnegative constant. -/
theorem conditionalFeatureEntropyLossOneEnvelope_subexponential
    (S : Type u) [Fintype S] (T : Type v) [Fintype T] :
    Growth.Subexponential (conditionalFeatureEntropyLossOneEnvelope S T) := by
  let d := Fintype.card (S × T)
  let e := Fintype.card S
  let constant : ℝ :=
    ((((2 : ℕ) ^ d : ℕ) : ℝ)) * Real.exp 1 ^ e
  have hfirst : Growth.Subexponential (fun N : ℕ ↦
      ((((N + 1) ^ d : ℕ) : ℝ))) := by
    simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
      Growth.Subexponential.natCast_succ_pow d
  have hlast : Growth.Subexponential (fun N : ℕ ↦
      ((((N + 1) ^ e : ℕ) : ℝ))) := by
    simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
      Growth.Subexponential.natCast_succ_pow e
  have hproduct := hfirst.mul hlast
  have hscaled := hproduct.const_mul (show 0 ≤ constant by
    unfold constant
    positivity)
  convert hscaled using 1
  funext N
  unfold conditionalFeatureEntropyLossOneEnvelope typeClassEntropyLoss constant d e
  push_cast
  ring

/-- A uniform real upper bound on a finite natural-valued family bounds the cast of its
supremum.  The nonnegativity premise covers the empty family. -/
private theorem cast_finset_sup_le
    {A : Type w} [DecidableEq A]
    (items : Finset A) (value : A → ℕ) (bound : ℝ)
    (hbound : 0 ≤ bound)
    (hvalue : ∀ item ∈ items, (value item : ℝ) ≤ bound) :
    ((items.sup value : ℕ) : ℝ) ≤ bound := by
  induction items using Finset.induction_on with
  | empty => simpa using hbound
  | @insert item items hnotmem ih =>
      rw [Finset.sup_insert]
      push_cast
      exact max_le
        (hvalue item (Finset.mem_insert_self item items))
        (ih (fun other hother ↦
          hvalue other (Finset.mem_insert_of_mem hother)))

/-- Pointwise conditional-feature bounds over a finite family of empirical profiles yield one
uniform typical-profile bound.

Every allowed profile has common mass `N`, entropy at least `referenceEntropy - defect`, and a
pointwise count bounded by the conditional-feature penalty with joint entropy `jointEntropy`.
Then the maximum count has exponent
`N * (jointEntropy - referenceEntropy + defect)`, with one common repetition-one loss envelope.

Proof sketch: rewrite each pointwise penalty base in base two.  The entropy lower bound increases
its exponent to the common reference-minus-defect exponent, while the preceding theorem replaces
the profile-dependent loss by the common envelope.  A finite induction then bounds the natural
supremum, including the empty-family case. -/
theorem cast_finset_sup_count_le_typicalProfileUniformBound
    {A : Type w} {S : Type u} {T : Type v}
    [DecidableEq A] [Fintype S] [Fintype T]
    (allowed : Finset A)
    (sourceProfile : A → S → ℕ)
    (count : A → ℕ)
    (N : ℕ) (referenceEntropy jointEntropy defect : ℝ)
    (hmass : ∀ a ∈ allowed, profileMass (sourceProfile a) = N)
    (hentropy : ∀ a ∈ allowed,
      referenceEntropy - defect ≤ profileEntropyBits (sourceProfile a))
    (hpointwise : ∀ a ∈ allowed,
      (count a : ℝ) ≤
        conditionalFeatureEntropyLoss T (sourceProfile a) 1 *
          conditionalFeatureEntropyPenaltyBase (sourceProfile a)
            ((N : ℝ) * Real.log 2 * jointEntropy)) :
    ((allowed.sup count : ℕ) : ℝ) ≤
      conditionalFeatureEntropyLossOneEnvelope S T N *
        (2 : ℝ) ^ ((N : ℝ) *
          (jointEntropy - referenceEntropy + defect)) := by
  let bound : ℝ :=
    conditionalFeatureEntropyLossOneEnvelope S T N *
      (2 : ℝ) ^ ((N : ℝ) *
        (jointEntropy - referenceEntropy + defect))
  have hbound : 0 ≤ bound := by
    dsimp only [bound]
    exact mul_nonneg (by
      unfold conditionalFeatureEntropyLossOneEnvelope typeClassEntropyLoss
      positivity) (Real.rpow_nonneg (by norm_num) _)
  apply cast_finset_sup_le allowed count bound hbound
  intro a ha
  have hmassA := hmass a ha
  have hpoint := hpointwise a ha
  rw [← hmassA,
    conditionalFeatureEntropyPenaltyBase_eq_two_rpow_entropyBits_sub] at hpoint
  have hloss : conditionalFeatureEntropyLoss T (sourceProfile a) 1 ≤
      conditionalFeatureEntropyLossOneEnvelope S T N :=
    conditionalFeatureEntropyLoss_one_le_envelope (sourceProfile a) N hmassA
  have hexponent :
      (profileMass (sourceProfile a) : ℝ) *
          (jointEntropy - profileEntropyBits (sourceProfile a)) ≤
        (N : ℝ) * (jointEntropy - referenceEntropy + defect) := by
    rw [hmassA]
    exact mul_le_mul_of_nonneg_left (by
      linarith [hentropy a ha]) (Nat.cast_nonneg N)
  have hpower :
      (2 : ℝ) ^ ((profileMass (sourceProfile a) : ℝ) *
          (jointEntropy - profileEntropyBits (sourceProfile a))) ≤
        (2 : ℝ) ^ ((N : ℝ) *
          (jointEntropy - referenceEntropy + defect)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
  refine hpoint.trans ?_
  change conditionalFeatureEntropyLoss T (sourceProfile a) 1 *
      (2 : ℝ) ^ ((profileMass (sourceProfile a) : ℝ) *
        (jointEntropy - profileEntropyBits (sourceProfile a))) ≤ bound
  dsimp only [bound]
  exact mul_le_mul hloss hpower (Real.rpow_nonneg (by norm_num) _)
    (by
      unfold conditionalFeatureEntropyLossOneEnvelope typeClassEntropyLoss
      positivity)

/-! A singleton exact profile instantiates every data-carrying premise of the uniform theorem. -/

private example :
    (((Finset.univ : Finset (Fin 1)).sup (fun _ ↦ 0) : ℕ) : ℝ) ≤
      conditionalFeatureEntropyLossOneEnvelope (Fin 1) (Fin 1) 1 *
        (2 : ℝ) ^ (((1 : ℕ) : ℝ) *
          (0 - profileEntropyBits (fun _ : Fin 1 ↦ 1) + 0)) := by
  refine cast_finset_sup_count_le_typicalProfileUniformBound
    (A := Fin 1) (S := Fin 1) (T := Fin 1)
    (allowed := (Finset.univ : Finset (Fin 1)))
    (sourceProfile := fun _ _ : Fin 1 ↦ 1)
    (count := fun _ ↦ 0)
    (N := 1)
    (referenceEntropy := profileEntropyBits (fun _ : Fin 1 ↦ 1))
    (jointEntropy := 0) (defect := 0) ?_ ?_ ?_
  · intro a ha
    simp [profileMass]
  · intro a ha
    simp
  · intro a ha
    norm_num only [Nat.cast_zero]
    exact mul_nonneg
      (conditionalFeatureEntropyLoss_pos
        (Fin 1) (fun _ : Fin 1 ↦ 1) 1).le
      (conditionalFeatureEntropyPenaltyBase_pos
        (fun _ : Fin 1 ↦ 1)
        ((1 : ℝ) * Real.log 2 * 0)).le

end AlgebraicComplexity.WordType
