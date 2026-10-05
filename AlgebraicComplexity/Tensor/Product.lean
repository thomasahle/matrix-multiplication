/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.ProductCore
import AlgebraicComplexity.Tensor.Restriction
import Mathlib.LinearAlgebra.PiTensorProduct.DirectSum
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Products of three-legged tensors

The external product pairs corresponding tensor legs.  Thus a tensor over `V` and a tensor over
`W` produce a tensor whose leg `i` is `V i ⊗ W i`.

The lightweight `ProductCore` import supplies bilinearity and compatibility with leg maps.  This
file adds commutation and association through the canonical tensor-product equivalences, and
preservation of exact restriction and isomorphism.  Direct sums are a separate operation, and
their calculus lives in `Tensor/DirectSum.lean`.  The structural identities are proved first on
pure tensors and then extended by the universal property of `PiTensorProduct`.
-/

namespace AlgebraicComplexity.Tensor

universe u v w v' w' z

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} {W : Leg → Type w}
variable {V' : Leg → Type v'} {W' : Leg → Type w'}
variable [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]
variable [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]
variable [∀ i, AddCommMonoid (V' i)] [∀ i, Module K (V' i)]
variable [∀ i, AddCommMonoid (W' i)] [∀ i, Module K (W' i)]

/-- Applying maps after an external product is the same as applying them before it. -/
theorem map_external (f : ∀ i, V i →ₗ[K] V' i) (g : ∀ i, W i →ₗ[K] W' i)
    (T : Tensor3 K V) (S : Tensor3 K W) :
    map (fun i ↦ TensorProduct.map (f i) (g i)) (external T S) =
      external (map f T) (map g S) := by
  refine PiTensorProduct.induction_on T ?_ ?_
  · intro a x
    refine PiTensorProduct.induction_on S ?_ ?_
    · intro b y
      simp
    · intro S₁ S₂ h₁ h₂
      simp only [LinearMap.map_add, h₁, h₂]
  · intro T₁ T₂ h₁ h₂
    simp only [LinearMap.map_add, LinearMap.add_apply, h₁, h₂]

/-- Permuting the three legs commutes with the factorwise external product.

Proof sketch: verify the identity for a pair of pure tensors, then extend linearly in each tensor
argument using the universal property of `PiTensorProduct`. -/
theorem permute_external (e : Orientation) (T : Tensor3 K V) (S : Tensor3 K W) :
    Tensor.permute e (external T S) =
      external (Tensor.permute e T) (Tensor.permute e S) := by
  refine PiTensorProduct.induction_on T ?_ ?_
  · intro a x
    refine PiTensorProduct.induction_on S ?_ ?_
    · intro b y
      simp
    · intro S₁ S₂ h₁ h₂
      simp only [map_add, h₁, h₂]
  · intro T₁ T₂ h₁ h₂
    simp only [map_add, LinearMap.add_apply, h₁, h₂]

/-- Commuting the two tensor-product factors on every leg swaps the two external-product
arguments.  This is the tensor-level generator for permuting chunks in an iterated product. -/
theorem map_external_comm (T : Tensor3 K V) (S : Tensor3 K W) :
    map (fun c ↦ (TensorProduct.comm K (V c) (W c)).toLinearMap)
        (external T S) =
      external S T := by
  refine PiTensorProduct.induction_on T ?_ ?_
  · intro a x
    refine PiTensorProduct.induction_on S ?_ ?_
    · intro b y
      simp [smul_smul, mul_comm]
    · intro S₁ S₂ h₁ h₂
      simp only [LinearMap.map_add, LinearMap.add_apply, h₁, h₂]
  · intro T₁ T₂ h₁ h₂
    simp only [LinearMap.map_add, LinearMap.add_apply, h₁, h₂]

/-- Canonical legwise equivalence which swaps the final two factors of a left-associated triple
tensor product while leaving the prefix factor fixed. -/
def externalSwapRightEquiv {U : Leg → Type z}
    [∀ i, AddCommMonoid (U i)] [∀ i, Module K (U i)] (c : Leg) :
    TensorProduct K (TensorProduct K (U c) (V c)) (W c) ≃ₗ[K]
      TensorProduct K (TensorProduct K (U c) (W c)) (V c) :=
  TensorProduct.rightComm K (U c) (V c) (W c)

/-- The equivalence `externalSwapRightEquiv` swaps the final two tensor chunks. -/
theorem map_external_swap_right {U : Leg → Type z}
    [∀ i, AddCommMonoid (U i)] [∀ i, Module K (U i)]
    (R : Tensor3 K U) (T : Tensor3 K V) (S : Tensor3 K W) :
    map (fun c ↦ (externalSwapRightEquiv (K := K)
      (U := U) (V := V) (W := W) c).toLinearMap)
        (external (external R T) S) =
      external (external R S) T := by
  refine PiTensorProduct.induction_on R ?_ ?_
  · intro a x
    refine PiTensorProduct.induction_on T ?_ ?_
    · intro b y
      refine PiTensorProduct.induction_on S ?_ ?_
      · intro d z
        simp [externalSwapRightEquiv, smul_smul, mul_comm, mul_left_comm]
      · intro S₁ S₂ h₁ h₂
        simp only [LinearMap.map_add, LinearMap.add_apply, h₁, h₂]
    · intro T₁ T₂ h₁ h₂
      simp only [LinearMap.map_add, LinearMap.add_apply, h₁, h₂]
  · intro R₁ R₂ h₁ h₂
    simp only [LinearMap.map_add, LinearMap.add_apply, h₁, h₂]

/-- The tensor-product associator on every leg carries a left-associated external product to the
corresponding right-associated product. -/
theorem map_external_assoc {U : Leg → Type z}
    [∀ i, AddCommMonoid (U i)] [∀ i, Module K (U i)]
    (T : Tensor3 K V) (S : Tensor3 K W) (Q : Tensor3 K U) :
    map (fun c ↦ (TensorProduct.assoc K (V c) (W c) (U c)).toLinearMap)
        (external (external T S) Q) =
      external T (external S Q) := by
  refine PiTensorProduct.induction_on T ?_ ?_
  · intro a x
    refine PiTensorProduct.induction_on S ?_ ?_
    · intro b y
      refine PiTensorProduct.induction_on Q ?_ ?_
      · intro d q
        simp
      · intro Q₁ Q₂ h₁ h₂
        simp only [LinearMap.map_add, h₁, h₂]
    · intro S₁ S₂ h₁ h₂
      simp only [LinearMap.map_add, LinearMap.add_apply, h₁, h₂]
  · intro T₁ T₂ h₁ h₂
    simp only [LinearMap.map_add, LinearMap.add_apply, h₁, h₂]

/-- Inverse associator form of `map_external_assoc`. -/
theorem map_external_assoc_symm {U : Leg → Type z}
    [∀ i, AddCommMonoid (U i)] [∀ i, Module K (U i)]
    (T : Tensor3 K V) (S : Tensor3 K W) (Q : Tensor3 K U) :
    map (fun c ↦ (TensorProduct.assoc K (V c) (W c) (U c)).symm.toLinearMap)
        (external T (external S Q)) =
      external (external T S) Q := by
  have h := map_external_assoc T S Q
  rw [← h]
  change (PiTensorProduct.congr
      (fun c ↦ (TensorProduct.assoc K (V c) (W c) (U c)).symm))
      ((PiTensorProduct.congr
        (fun c ↦ TensorProduct.assoc K (V c) (W c) (U c)))
        (external (external T S) Q)) = _
  exact LinearEquiv.symm_apply_apply
    (PiTensorProduct.congr
      (fun c ↦ TensorProduct.assoc K (V c) (W c) (U c))) _

namespace Restricts

/-- Exact restrictions are compatible with factorwise external products. -/
theorem external {T : Tensor3 K V} {T' : Tensor3 K V'}
    {S : Tensor3 K W} {S' : Tensor3 K W'}
    (hT : Restricts T T') (hS : Restricts S S') :
    Restricts (Tensor.external T S) (Tensor.external T' S') := by
  rcases hT with ⟨f, hf⟩
  rcases hS with ⟨g, hg⟩
  refine ⟨fun i ↦ TensorProduct.map (f i) (g i), ?_⟩
  rw [map_external, hf, hg]

end Restricts

namespace Isomorphic

/-- Canonical reassociation of a three-factor external product.

On every tensor leg this is the standard tensor-product associator
`(U ⊗ V) ⊗ W ≃ U ⊗ (V ⊗ W)`. -/
theorem external_assoc {U : Leg → Type z}
    [∀ i, AddCommMonoid (U i)] [∀ i, Module K (U i)]
    (T : Tensor3 K V) (S : Tensor3 K W) (Q : Tensor3 K U) :
    Isomorphic (Tensor.external (Tensor.external T S) Q)
      (Tensor.external T (Tensor.external S Q)) := by
  refine ⟨fun c ↦ TensorProduct.assoc K (V c) (W c) (U c), ?_⟩
  simpa [PiTensorProduct.congr] using map_external_assoc T S Q

/-- Inverse canonical reassociation of a three-factor external product. -/
theorem external_assoc_symm {U : Leg → Type z}
    [∀ i, AddCommMonoid (U i)] [∀ i, Module K (U i)]
    (T : Tensor3 K V) (S : Tensor3 K W) (Q : Tensor3 K U) :
    Isomorphic (Tensor.external T (Tensor.external S Q))
      (Tensor.external (Tensor.external T S) Q) :=
  (external_assoc T S Q).symm

/-- Transposing the last two factors of a left-associated triple external product is a legwise
isomorphism.

On every tensor leg this is `externalSwapRightEquiv`, the right commutator
`(U ⊗ V) ⊗ W ≃ (U ⊗ W) ⊗ V`. -/
theorem external_swapRight {K : Type u} [CommSemiring K]
    {U : Leg → Type z} [∀ c, AddCommMonoid (U c)] [∀ c, Module K (U c)]
    {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
    {W : Leg → Type w} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]
    (R : Tensor3 K U) (T : Tensor3 K V) (S : Tensor3 K W) :
    Isomorphic (Tensor.external (Tensor.external R T) S)
      (Tensor.external (Tensor.external R S) T) := by
  refine ⟨fun c ↦ externalSwapRightEquiv (K := K) (U := U) (V := V) (W := W) c, ?_⟩
  simpa [PiTensorProduct.congr] using map_external_swap_right R T S

/-- Legwise tensor isomorphisms are compatible with factorwise external products. -/
theorem external {T : Tensor3 K V} {T' : Tensor3 K V'}
    {S : Tensor3 K W} {S' : Tensor3 K W'}
    (hT : Isomorphic T T') (hS : Isomorphic S S') :
    Isomorphic (Tensor.external T S) (Tensor.external T' S') := by
  rcases hT with ⟨f, hf⟩
  rcases hS with ⟨g, hg⟩
  refine ⟨fun i ↦ TensorProduct.congr (f i) (g i), ?_⟩
  change Tensor.map
      (fun i ↦ TensorProduct.map (f i).toLinearMap (g i).toLinearMap)
      (Tensor.external T S) = Tensor.external T' S'
  rw [map_external]
  change Tensor.external (PiTensorProduct.congr f T) (PiTensorProduct.congr g S) = _
  rw [hf, hg]

/-- **Middle-four interchange.**  `(X ⊠ Y) ⊠ (Z ⊠ Q) ≅ (X ⊠ Z) ⊠ (Y ⊠ Q)`.

Proof sketch: transpose `Y` past the pair `Z ⊠ Q`, reassociate that pair, transpose `Y` back into
third position, and reassociate. -/
theorem external_interchange {K : Type u} [CommSemiring K]
    {U : Leg → Type z} [∀ c, AddCommMonoid (U c)] [∀ c, Module K (U c)]
    {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
    {W : Leg → Type w} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]
    {U' : Leg → Type*} [∀ c, AddCommMonoid (U' c)] [∀ c, Module K (U' c)]
    (X : Tensor3 K V) (Y : Tensor3 K W) (Z : Tensor3 K U) (Q : Tensor3 K U') :
    Isomorphic (Tensor.external (Tensor.external X Y) (Tensor.external Z Q))
      (Tensor.external (Tensor.external X Z) (Tensor.external Y Q)) :=
  ((external_swapRight X Y (Tensor.external Z Q)).trans
    (((external_assoc_symm X Z Q).external (Isomorphic.refl Y)).trans
      ((external_swapRight (Tensor.external X Z) Q Y).trans
        (external_assoc (Tensor.external X Z) Y Q))))

end Isomorphic

end AlgebraicComplexity.Tensor
