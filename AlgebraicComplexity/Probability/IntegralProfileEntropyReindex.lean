/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.MappedType
import AlgebraicComplexity.Probability.IntegralProfileEntropyDefs

/-!
# Entropy of an integral profile under alphabet equivalence

This layer-2 module proves that pushing a finite integral profile through an equivalence of
alphabets preserves its normalized Shannon entropy, both in nats and in bits.  The proof works
also for the zero profile: no positivity or probability-normalization hypothesis is needed.

This is the reusable relabelling step behind the entropy terms in [alman2025more, Claim 6.18],
`papers/sources/2404.16349/constituent.tex:376-440`.  It proves only an exact finite identity; it
contains no compatibility count, independence premise, asymptotic estimate, or CW-specific data.
-/

set_option autoImplicit false

open scoped BigOperators

namespace AlgebraicComplexity.WordType

universe u v

private theorem mappedType_equiv_apply
    {A : Type u} {B : Type v} [Fintype A]
    (e : A ≃ B) (profile : A → ℕ) (b : B) :
    mappedType e profile b = profile (e.symm b) := by
  classical
  rw [mappedType_eq_sum_ite, Finset.sum_eq_single (e.symm b)]
  · simp
  · intro a _ ha
    have hne : e a ≠ b := by
      intro h
      exact ha (e.injective (by simpa using h))
    simp [hne]
  · simp

/-- Pushing an integral profile through an alphabet equivalence preserves its Shannon entropy in
nats.

Proof sketch: each target letter has the unique preimage given by the inverse equivalence, so the
pushed profile is the original profile with its coordinates permuted.  Pushforward preserves the
total mass, and finite summation is invariant under that permutation. -/
@[simp] theorem profileEntropyNats_mappedType_equiv
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (e : A ≃ B) (profile : A → ℕ) :
    profileEntropyNats (mappedType e profile) = profileEntropyNats profile := by
  classical
  unfold profileEntropyNats
  rw [profileMass_mappedType]
  simp only [mappedType_equiv_apply]
  exact e.symm.sum_comp
    (fun a ↦ Real.negMulLog ((profile a : ℝ) / (profileMass profile : ℝ)))

/-- Pushing an integral profile through an alphabet equivalence preserves its base-two Shannon
entropy. -/
@[simp] theorem profileEntropyBits_mappedType_equiv
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (e : A ≃ B) (profile : A → ℕ) :
    profileEntropyBits (mappedType e profile) = profileEntropyBits profile := by
  unfold profileEntropyBits
  rw [profileEntropyNats_mappedType_equiv]

private example :
    profileEntropyBits
        (mappedType (Equiv.swap (0 : Fin 2) 1)
          (fun i ↦ if i = 0 then 1 else 2)) =
      profileEntropyBits (fun i : Fin 2 ↦ if i = 0 then 1 else 2) := by
  exact profileEntropyBits_mappedType_equiv
    (Equiv.swap (0 : Fin 2) 1) (fun i ↦ if i = 0 then 1 else 2)

end AlgebraicComplexity.WordType
