/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Basic

/-!
# Tensor restriction

`Restricts T S` means that `S` is obtained from `T` by applying one linear map to each of its
three legs.  The direction of the arguments follows the operation: the first tensor is the source
and the second tensor is the result.
-/

namespace AlgebraicComplexity.Tensor

universe u v w x

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} {W : Leg → Type w} {U : Leg → Type x}
variable [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]
variable [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]
variable [∀ i, AddCommMonoid (U i)] [∀ i, Module K (U i)]

/-- Exact tensor restriction by independent linear maps on the three legs. -/
def Restricts (T : Tensor3 K V) (S : Tensor3 K W) : Prop :=
  ∃ f : ∀ i, V i →ₗ[K] W i, map f T = S

/-- Alternative order-theoretic notation: `S ⪯ T` means that `T` restricts to `S`. -/
scoped infix:50 " ⪯ " => fun S T ↦ Restricts T S

namespace Restricts

/-- Restriction is reflexive: the identity map on every leg carries `T` to itself. -/
theorem refl (T : Tensor3 K V) : Restricts T T := by
  refine ⟨fun i ↦ LinearMap.id (R := K) (M := V i), ?_⟩
  simp

/-- Restriction is transitive: if the source `T` restricts to `S` and `S` restricts to `R`, then
`T` restricts to `R` by composing the legwise maps. -/
theorem trans {T : Tensor3 K V} {S : Tensor3 K W} {R : Tensor3 K U}
    (hTS : Restricts T S) (hSR : Restricts S R) : Restricts T R := by
  rcases hTS with ⟨f, hf⟩
  rcases hSR with ⟨g, hg⟩
  refine ⟨fun i ↦ g i ∘ₗ f i, ?_⟩
  rw [map_comp]
  simp only [LinearMap.comp_apply, hf, hg]

/-- Equal tensors restrict to one another: given `h : T = S`, the identity map on every leg carries
the source `T` to the target `S`. -/
theorem of_eq {T S : Tensor3 K V} (h : T = S) : Restricts T S := by
  subst S
  exact refl T

/-- Every tensor restricts onto the zero tensor: take the zero map on each leg.  The source is `T`
and the target is `0`. -/
theorem zeroTarget (T : Tensor3 K V) : Restricts T (0 : Tensor3 K W) :=
  ⟨fun _ ↦ 0, map_eq_zero_of_coord _ _ Leg.X rfl⟩

/-- Leg permutations preserve restriction.  If the source `T` restricts to `S`, then
`Tensor.permute e T` restricts to `Tensor.permute e S`; the transported map on target leg `i` is
the original map on source leg `e.symm i`. -/
theorem permute {T : Tensor3 K V} {S : Tensor3 K W}
    (h : Restricts T S) (e : Orientation) :
    Restricts (Tensor.permute e T) (Tensor.permute e S) := by
  rcases h with ⟨f, hf⟩
  refine ⟨fun i ↦ f (e.symm i), ?_⟩
  rw [PiTensorProduct.map_reindex]
  exact congrArg (fun z ↦ Tensor.permute e z) hf

end Restricts

/-- Two tensors are isomorphic when invertible maps on their legs carry one to the other. -/
def Isomorphic (T : Tensor3 K V) (S : Tensor3 K W) : Prop :=
  ∃ f : ∀ i, V i ≃ₗ[K] W i, PiTensorProduct.congr f T = S

namespace Isomorphic

/-- Legwise isomorphism is reflexive: the identity equivalence on every leg carries `T` to
itself. -/
theorem refl (T : Tensor3 K V) : Isomorphic T T := by
  refine ⟨fun _ ↦ LinearEquiv.refl K _, ?_⟩
  simp [PiTensorProduct.congr]

/-- Equal tensors are legwise isomorphic.  Given `h : T = S`, the identity equivalence on every
leg carries the source `T` to the target `S`. -/
theorem of_eq {T S : Tensor3 K V} (h : T = S) : Isomorphic T S := by
  subst S
  exact refl T

/-- Applying invertible maps on every leg gives an isomorphic tensor. -/
theorem map (T : Tensor3 K V) (f : ∀ i, V i ≃ₗ[K] W i) :
    Isomorphic T (Tensor.map (fun i ↦ (f i).toLinearMap) T) := by
  exact ⟨f, rfl⟩

/-- Legwise isomorphism is a special case of exact restriction: forget invertibility and keep the
underlying linear map on each leg.  The source is `T` and the target is `S`. -/
theorem restricts {T : Tensor3 K V} {S : Tensor3 K W}
    (h : Isomorphic T S) : Restricts T S := by
  rcases h with ⟨f, hf⟩
  refine ⟨fun i ↦ (f i).toLinearMap, ?_⟩
  simpa [PiTensorProduct.congr] using hf

/-- Leg permutations preserve tensor isomorphism.  The transported equivalence on target leg
`i` is the original equivalence on source leg `e.symm i`. -/
theorem permute_legs {T : Tensor3 K V} {S : Tensor3 K W}
    (h : Isomorphic T S) (e : Orientation) :
    Isomorphic (Tensor.permute e T) (Tensor.permute e S) := by
  rcases h with ⟨f, hf⟩
  refine ⟨fun i ↦ f (e.symm i), ?_⟩
  change Tensor.map (fun i ↦ (f (e.symm i)).toLinearMap) (Tensor.permute e T) =
    Tensor.permute e S
  calc
    _ = Tensor.permute e (Tensor.map (fun i ↦ (f i).toLinearMap) T) :=
      PiTensorProduct.map_reindex (fun i ↦ (f i).toLinearMap) e T
    _ = Tensor.permute e S := congrArg (fun U ↦ Tensor.permute e U)
      (by simpa [PiTensorProduct.congr] using hf)

/-- Legwise isomorphism is symmetric: invert the equivalence on every leg.  Unlike restriction,
which is only a preorder, isomorphism is therefore an equivalence relation. -/
theorem symm {T : Tensor3 K V} {S : Tensor3 K W}
    (h : Isomorphic T S) : Isomorphic S T := by
  rcases h with ⟨f, hf⟩
  refine ⟨fun i ↦ (f i).symm, ?_⟩
  rw [← hf]
  exact LinearEquiv.symm_apply_apply (PiTensorProduct.congr f) T

/-- Tensor isomorphism is transitive. -/
theorem trans {T : Tensor3 K V} {S : Tensor3 K W} {R : Tensor3 K U}
    (hTS : Isomorphic T S) (hSR : Isomorphic S R) : Isomorphic T R := by
  rcases hTS with ⟨f, hf⟩
  rcases hSR with ⟨g, hg⟩
  refine ⟨fun i ↦ (f i).trans (g i), ?_⟩
  rw [← hg, ← hf]
  change
    PiTensorProduct.map (fun i ↦ ((g i).toLinearMap ∘ₗ (f i).toLinearMap)) T =
      PiTensorProduct.map (fun i ↦ (g i).toLinearMap)
        (PiTensorProduct.map (fun i ↦ (f i).toLinearMap) T)
  exact LinearMap.congr_fun (PiTensorProduct.map_comp
    (fun i ↦ (g i).toLinearMap) (fun i ↦ (f i).toLinearMap)) T

/-- Applying the forward three-cycle twice is legwise isomorphic to applying its inverse once.

The two ambient leg families are propositionally, but not definitionally, the same.  The explicit
leg equivalences below isolate that dependent reindexing detail for clients that assemble all
three cyclic orientations. -/
theorem permute_cycle_cycle (T : Tensor3 K V) :
    Isomorphic (Tensor.permute cycle (Tensor.permute cycle T))
      (Tensor.permute cycle.symm T) := by
  let f : ∀ c,
      V (cycle.symm (cycle.symm c)) ≃ₗ[K] V (cycle c) := by
    intro c
    cases c <;> exact LinearEquiv.refl K _
  refine ⟨f, ?_⟩
  change Tensor.map (fun c ↦ (f c).toLinearMap)
      (Tensor.permute cycle (Tensor.permute cycle T)) =
    Tensor.permute cycle.symm T
  refine PiTensorProduct.induction_on T ?_ ?_
  · intro a x
    simp only [map_smul, Tensor.permute_pure, Tensor.map_pure]
    congr 2
    funext c
    cases c <;> rfl
  · intro T₁ T₂ h₁ h₂
    simp only [map_add, h₁, h₂]

end Isomorphic

end AlgebraicComplexity.Tensor
