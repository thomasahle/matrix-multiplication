/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Restriction
import Mathlib.LinearAlgebra.Prod

/-!
# Binary direct sums of three-legged tensors

For a finite binary sum the module direct sum is represented by a product. The two input tensors
are embedded into disjoint coordinates on every leg and then added. The file proves functoriality,
independent restriction of both summands, and the projection restrictions onto either summand.
-/

namespace AlgebraicComplexity.Tensor

universe u v w v' w'

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} {W : Leg → Type w}
variable {V' : Leg → Type v'} {W' : Leg → Type w'}
variable [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]
variable [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]
variable [∀ i, AddCommMonoid (V' i)] [∀ i, Module K (V' i)]
variable [∀ i, AddCommMonoid (W' i)] [∀ i, Module K (W' i)]

/-- Inclusion of the left summand on every leg. -/
abbrev includeLeft : ∀ i, V i →ₗ[K] V i × W i :=
  fun i ↦ LinearMap.inl K (V i) (W i)

/-- Inclusion of the right summand on every leg. -/
abbrev includeRight : ∀ i, W i →ₗ[K] V i × W i :=
  fun i ↦ LinearMap.inr K (V i) (W i)

/-- The direct sum of two tensors, embedded into pair spaces on all three legs. -/
def directSum (T : Tensor3 K V) (S : Tensor3 K W) :
    Tensor3 K (fun i ↦ V i × W i) :=
  map includeLeft T + map includeRight S

theorem map_directSum (f : ∀ i, V i →ₗ[K] V' i) (g : ∀ i, W i →ₗ[K] W' i)
    (T : Tensor3 K V) (S : Tensor3 K W) :
    map (fun i ↦ LinearMap.prodMap (f i) (g i)) (directSum T S) =
      directSum (map f T) (map g S) := by
  rw [directSum, LinearMap.map_add, directSum]
  congr 1
  · calc
      map (fun i ↦ LinearMap.prodMap (f i) (g i)) (map includeLeft T) =
          map (fun i ↦ LinearMap.prodMap (f i) (g i) ∘ₗ includeLeft i) T := by
            rw [map_comp]
            rfl
      _ = map (fun i ↦ includeLeft i ∘ₗ f i) T := by
            congr 2
            funext i
            ext x <;> simp
      _ = map includeLeft (map f T) := by
            rw [map_comp]
            rfl
  · calc
      map (fun i ↦ LinearMap.prodMap (f i) (g i)) (map includeRight S) =
          map (fun i ↦ LinearMap.prodMap (f i) (g i) ∘ₗ includeRight i) S := by
            rw [map_comp]
            rfl
      _ = map (fun i ↦ includeRight i ∘ₗ g i) S := by
            congr 2
            funext i
            ext x <;> simp
      _ = map includeRight (map g S) := by
            rw [map_comp]
            rfl

namespace Restricts

/-- **A direct sum restricts onto its left summand.**  Projecting every leg of `T ⊞ S` onto its
first coordinate returns `T`.

Proof sketch: the projection kills the right inclusion because the composite is the zero map on
every leg, and is the identity on the left inclusion. -/
theorem directSum_left (T : Tensor3 K V) (S : Tensor3 K W) :
    Restricts (Tensor.directSum T S) T := by
  refine ⟨fun i ↦ LinearMap.fst K (V i) (W i), ?_⟩
  have hleft : Tensor.map (fun i ↦ LinearMap.fst K (V i) (W i))
      (Tensor.map (Tensor.includeLeft (K := K) (V := V) (W := W)) T) = T := by
    rw [← LinearMap.comp_apply, ← Tensor.map_comp]
    have : (fun i ↦ (LinearMap.fst K (V i) (W i)) ∘ₗ Tensor.includeLeft (K := K) i) =
        fun i ↦ LinearMap.id (R := K) (M := V i) :=
      funext fun i ↦ LinearMap.ext fun x ↦ rfl
    rw [this, Tensor.map_id, LinearMap.id_apply]
  have hright : Tensor.map (fun i ↦ LinearMap.fst K (V i) (W i))
      (Tensor.map (Tensor.includeRight (K := K) (V := V) (W := W)) S) = 0 := by
    rw [← LinearMap.comp_apply, ← Tensor.map_comp]
    refine Tensor.map_eq_zero_of_coord _ S Leg.X ?_
    exact LinearMap.ext fun x ↦ rfl
  rw [Tensor.directSum, LinearMap.map_add, hleft, hright, add_zero]

/-- **A direct sum restricts onto its right summand.**  Projecting every leg of `T ⊞ S` onto its
second coordinate returns `S`. -/
theorem directSum_right (T : Tensor3 K V) (S : Tensor3 K W) :
    Restricts (Tensor.directSum T S) S := by
  refine ⟨fun i ↦ LinearMap.snd K (V i) (W i), ?_⟩
  have hleft : Tensor.map (fun i ↦ LinearMap.snd K (V i) (W i))
      (Tensor.map (Tensor.includeLeft (K := K) (V := V) (W := W)) T) = 0 := by
    rw [← LinearMap.comp_apply, ← Tensor.map_comp]
    refine Tensor.map_eq_zero_of_coord _ T Leg.X ?_
    exact LinearMap.ext fun x ↦ rfl
  have hright : Tensor.map (fun i ↦ LinearMap.snd K (V i) (W i))
      (Tensor.map (Tensor.includeRight (K := K) (V := V) (W := W)) S) = S := by
    rw [← LinearMap.comp_apply, ← Tensor.map_comp]
    have : (fun i ↦ (LinearMap.snd K (V i) (W i)) ∘ₗ Tensor.includeRight (K := K) i) =
        fun i ↦ LinearMap.id (R := K) (M := W i) :=
      funext fun i ↦ LinearMap.ext fun x ↦ rfl
    rw [this, Tensor.map_id, LinearMap.id_apply]
  rw [Tensor.directSum, LinearMap.map_add, hleft, hright, zero_add]

/-- Exact restrictions can be applied independently to the summands of a direct sum. -/
theorem directSum {T : Tensor3 K V} {T' : Tensor3 K V'}
    {S : Tensor3 K W} {S' : Tensor3 K W'}
    (hT : Restricts T T') (hS : Restricts S S') :
    Restricts (Tensor.directSum T S) (Tensor.directSum T' S') := by
  rcases hT with ⟨f, hf⟩
  rcases hS with ⟨g, hg⟩
  refine ⟨fun i ↦ LinearMap.prodMap (f i) (g i), ?_⟩
  rw [map_directSum, hf, hg]

end Restricts

end AlgebraicComplexity.Tensor
