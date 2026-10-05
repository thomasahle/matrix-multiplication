/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd112
import AlgebraicComplexity.Examples.CoppersmithWinogradSquareSymmetryDefs
import AlgebraicComplexity.Tensor.PartitionedPermutation

/-!
# Cyclic symmetry of the exceptional CW-square constituents

The degree-four support of the squared Coppersmith--Winograd tensor contains three exceptional
constituents, at addresses `112`, `211`, and `121`.  This file proves directly that cycling the
tensor legs carries each constituent to the next one.  The proof expands the four raw products in
each coarse constituent, checks the cyclic identity on pure tensors, and then verifies that the raw
identities commute with the degree-sum coarsening inclusions.

The main results are `cwSquareConstituent_211_cycle` and
`cwSquareConstituent_121_cycle`.  Together they provide the orientation bridge needed to assemble
the three exceptional chunks into the cyclic product used by the shared-`Z` extraction theorem.

The symmetry of the *base* constituents that this lifting rests on --
`cwBaseConstituentCycleEquiv`, `cwBaseConstituentSwapEquiv`, `cwConstituentOfBlocks_cycle` and
`cwConstituentOfBlocks_swap` -- lives in `CoppersmithWinogradSquareSymmetryDefs.lean`, which this
file imports and re-exports.  That module's closure is `CoppersmithWinogradPartitionDataCore`
alone, so a client needing only the base symmetry can import it instead of this file and skip the
whole `CoppersmithWinograd112` cone.  Every public name of this module is unchanged.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-! ## Lifting base cyclic symmetry through the square coarsening -/

/-- Rotate the labels of one base CW address in the order induced by `cycle`. -/
abbrev cwBlockCycleAddress (x y z : CWBlock) : CWBlockAddress :=
  ofLegs z x y

/-- Leg maps carrying the cyclic permutation of a raw product of two supported base
constituents to the raw product of their rotated constituents. -/
noncomputable def cwSquareRawCycleMap
    (K : Type u) [CommRing K] (q : ℕ)
    (x₁ y₁ z₁ x₂ y₂ z₂ : CWBlock) : ∀ c,
    CWSquareRawBlockSpace K q (cycle.symm c)
        (cwSquareRawAddress (ofLegs x₁ y₁ z₁) (ofLegs x₂ y₂ z₂)
          (cycle.symm c)) →ₗ[K]
      CWSquareRawBlockSpace K q c
        (cwSquareRawAddress (cwBlockCycleAddress x₁ y₁ z₁)
          (cwBlockCycleAddress x₂ y₂ z₂) c) :=
  fun c ↦ TensorProduct.map
    (cwBaseConstituentCycleEquiv K q x₁ y₁ z₁ c).toLinearMap
    (cwBaseConstituentCycleEquiv K q x₂ y₂ z₂ c).toLinearMap

/-- Cycling a raw square constituent is the raw constituent obtained by cycling both base
addresses.

Proof sketch: unfold the raw square constituent into an external product.  Permutation commutes
with that product, and the two factors are identified by `cwConstituentOfBlocks_cycle`. -/
theorem cwSquareRawConstituent_cycle
    (K : Type u) [CommRing K] (q : ℕ)
    (x₁ y₁ z₁ x₂ y₂ z₂ : CWBlock)
    (h₁ : ofLegs (V := fun _ : Leg ↦ CWBlock) x₁ y₁ z₁ ∈ cwBlockSupport)
    (h₂ : ofLegs (V := fun _ : Leg ↦ CWBlock) x₂ y₂ z₂ ∈ cwBlockSupport) :
    map (cwSquareRawCycleMap K q x₁ y₁ z₁ x₂ y₂ z₂)
        (Tensor.permute cycle
          (((cwPartitionedTensor K q).positivePower 1).constituent
            (cwSquareRawAddress (ofLegs x₁ y₁ z₁) (ofLegs x₂ y₂ z₂)))) =
      ((cwPartitionedTensor K q).positivePower 1).constituent
        (cwSquareRawAddress (cwBlockCycleAddress x₁ y₁ z₁)
          (cwBlockCycleAddress x₂ y₂ z₂)) := by
  change map (cwSquareRawCycleMap K q x₁ y₁ z₁ x₂ y₂ z₂)
      (Tensor.permute cycle
        (Tensor.external (cwConstituentOfBlocks K q x₁ y₁ z₁)
          (cwConstituentOfBlocks K q x₂ y₂ z₂))) =
    Tensor.external (cwConstituentOfBlocks K q z₁ x₁ y₁)
      (cwConstituentOfBlocks K q z₂ x₂ y₂)
  rw [Tensor.permute_external]
  change map (fun c ↦ TensorProduct.map
      (cwBaseConstituentCycleEquiv K q x₁ y₁ z₁ c).toLinearMap
      (cwBaseConstituentCycleEquiv K q x₂ y₂ z₂ c).toLinearMap)
      (Tensor.external
        (Tensor.permute cycle (cwConstituentOfBlocks K q x₁ y₁ z₁))
        (Tensor.permute cycle (cwConstituentOfBlocks K q x₂ y₂ z₂))) = _
  rw [Tensor.map_external,
    cwConstituentOfBlocks_cycle K q x₁ y₁ z₁ h₁,
    cwConstituentOfBlocks_cycle K q x₂ y₂ z₂ h₂]

/-- Cycling both fine addresses identifies the corresponding degree-sum fibers. -/
def cwSquareCycleFiberEquiv
    (x₁ y₁ z₁ x₂ y₂ z₂ : CWBlock) (c : Leg) :
    BlockFiber cwSquareDegreeMap (cycle.symm c)
        (coarsenBlockAddress cwSquareDegreeMap
          (cwSquareRawAddress (ofLegs x₁ y₁ z₁) (ofLegs x₂ y₂ z₂))
          (cycle.symm c)) ≃
      BlockFiber cwSquareDegreeMap c
        (coarsenBlockAddress cwSquareDegreeMap
          (cwSquareRawAddress (cwBlockCycleAddress x₁ y₁ z₁)
            (cwBlockCycleAddress x₂ y₂ z₂)) c) := by
  cases c <;> exact Equiv.refl _

/-- Reindex the coarsened direct-sum blocks along cyclic rotation of a raw address pair. -/
noncomputable def cwSquareCoarseCycleEquiv
    (K : Type u) [CommRing K] (q : ℕ)
    (x₁ y₁ z₁ x₂ y₂ z₂ : CWBlock) : ∀ c,
    CWSquareBlockSpace K q (cycle.symm c)
        (coarsenBlockAddress cwSquareDegreeMap
          (cwSquareRawAddress (ofLegs x₁ y₁ z₁) (ofLegs x₂ y₂ z₂))
          (cycle.symm c)) ≃ₗ[K]
      CWSquareBlockSpace K q c
        (coarsenBlockAddress cwSquareDegreeMap
          (cwSquareRawAddress (cwBlockCycleAddress x₁ y₁ z₁)
            (cwBlockCycleAddress x₂ y₂ z₂)) c) := by
  intro c
  cases c <;>
    exact DirectSum.lequivCongrLeft K
      (cwSquareCycleFiberEquiv x₁ y₁ z₁ x₂ y₂ z₂ _)

/-- Cyclic symmetry of a raw square constituent descends through degree-sum coarsening.

This is the reusable termwise bridge for both ordinary square constituents and the exceptional
`112` orbit.  Its conclusion uses each term's actual coarse address, so clients can assemble
one-, two-, or three-term ordinary fibers without repeating dependent direct-sum bookkeeping.

Proof sketch: apply `map_permute_coarsenedTerm`.  The fine constituent compatibility is
`cwSquareRawConstituent_cycle`; compatibility with coarse inclusions is the defining
`DirectSum.lof` reindexing identity. -/
theorem cwSquareCoarsenedTerm_cycle
    (K : Type u) [CommRing K] (q : ℕ)
    (x₁ y₁ z₁ x₂ y₂ z₂ : CWBlock)
    (h₁ : ofLegs (V := fun _ : Leg ↦ CWBlock) x₁ y₁ z₁ ∈ cwBlockSupport)
    (h₂ : ofLegs (V := fun _ : Leg ↦ CWBlock) x₂ y₂ z₂ ∈ cwBlockSupport) :
    map (fun c ↦
        (cwSquareCoarseCycleEquiv K q x₁ y₁ z₁ x₂ y₂ z₂ c).toLinearMap)
      (Tensor.permute cycle
        (coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap
          (coarsenBlockAddress cwSquareDegreeMap
            (cwSquareRawAddress (ofLegs x₁ y₁ z₁) (ofLegs x₂ y₂ z₂)))
          (cwSquareRawAddress (ofLegs x₁ y₁ z₁) (ofLegs x₂ y₂ z₂)))) =
      coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
        cwSquareDegreeMap
        (coarsenBlockAddress cwSquareDegreeMap
          (cwSquareRawAddress (cwBlockCycleAddress x₁ y₁ z₁)
            (cwBlockCycleAddress x₂ y₂ z₂)))
        (cwSquareRawAddress (cwBlockCycleAddress x₁ y₁ z₁)
          (cwBlockCycleAddress x₂ y₂ z₂)) := by
  apply map_permute_coarsenedTerm
    ((cwPartitionedTensor K q).positivePower 1) cwSquareDegreeMap
    (cwSquareRawAddress (ofLegs x₁ y₁ z₁) (ofLegs x₂ y₂ z₂))
    (cwSquareRawAddress (cwBlockCycleAddress x₁ y₁ z₁)
      (cwBlockCycleAddress x₂ y₂ z₂))
    _ _ rfl rfl cycle
    (cwSquareRawCycleMap K q x₁ y₁ z₁ x₂ y₂ z₂)
    (cwSquareCoarseCycleEquiv K q x₁ y₁ z₁ x₂ y₂ z₂)
  · exact cwSquareRawConstituent_cycle K q x₁ y₁ z₁ x₂ y₂ z₂ h₁ h₂
  · intro c x
    cases c <;>
      simp only [cwSquareCoarseCycleEquiv, coarsenedBlockIncludeAt,
        cwSquareRawCycleMap, cwBlockCycleAddress, cwSquareDegreeMap,
        cwSquareBlockDegree]
    all_goals
      apply DirectSum.lequivCongrLeft_lof K
      · exact eq_of_heq ((cast_heq _ x).trans (by
          simp only [cwBaseConstituentCycleEquiv]
          change HEq x ((TensorProduct.map LinearMap.id LinearMap.id) x)
          rw [TensorProduct.map_id]
          rfl))
      · apply Subtype.ext
        rfl

/-! ## Lifting the `Y`/`Z` symmetry through the square coarsening -/

/-- Swap the last two labels of one base CW address. -/
abbrev cwBlockSwapAddress (x y z : CWBlock) : CWBlockAddress :=
  ofLegs x z y

/-- Leg maps carrying the `Y`/`Z` permutation of a raw square constituent to the product of the
two correspondingly swapped base constituents. -/
noncomputable def cwSquareRawSwapMap
    (K : Type u) [CommRing K] (q : ℕ)
    (x₁ y₁ z₁ x₂ y₂ z₂ : CWBlock) : ∀ c,
    CWSquareRawBlockSpace K q (xzy.symm c)
        (cwSquareRawAddress (ofLegs x₁ y₁ z₁) (ofLegs x₂ y₂ z₂)
          (xzy.symm c)) →ₗ[K]
      CWSquareRawBlockSpace K q c
        (cwSquareRawAddress (cwBlockSwapAddress x₁ y₁ z₁)
          (cwBlockSwapAddress x₂ y₂ z₂) c) :=
  fun c ↦ TensorProduct.map
    (cwBaseConstituentSwapEquiv K q x₁ y₁ z₁ c).toLinearMap
    (cwBaseConstituentSwapEquiv K q x₂ y₂ z₂ c).toLinearMap

/-- Swapping the last two legs of a raw square constituent swaps those labels in both base
addresses.

Proof sketch: expose the raw external product, commute the leg permutation and the product, and
apply `cwConstituentOfBlocks_swap` independently to the two factors. -/
theorem cwSquareRawConstituent_swap
    (K : Type u) [CommRing K] (q : ℕ)
    (x₁ y₁ z₁ x₂ y₂ z₂ : CWBlock)
    (h₁ : ofLegs (V := fun _ : Leg ↦ CWBlock) x₁ y₁ z₁ ∈ cwBlockSupport)
    (h₂ : ofLegs (V := fun _ : Leg ↦ CWBlock) x₂ y₂ z₂ ∈ cwBlockSupport) :
    map (cwSquareRawSwapMap K q x₁ y₁ z₁ x₂ y₂ z₂)
        (Tensor.permute xzy
          (((cwPartitionedTensor K q).positivePower 1).constituent
            (cwSquareRawAddress (ofLegs x₁ y₁ z₁) (ofLegs x₂ y₂ z₂)))) =
      ((cwPartitionedTensor K q).positivePower 1).constituent
        (cwSquareRawAddress (cwBlockSwapAddress x₁ y₁ z₁)
          (cwBlockSwapAddress x₂ y₂ z₂)) := by
  change map (cwSquareRawSwapMap K q x₁ y₁ z₁ x₂ y₂ z₂)
      (Tensor.permute xzy
        (Tensor.external (cwConstituentOfBlocks K q x₁ y₁ z₁)
          (cwConstituentOfBlocks K q x₂ y₂ z₂))) =
    Tensor.external (cwConstituentOfBlocks K q x₁ z₁ y₁)
      (cwConstituentOfBlocks K q x₂ z₂ y₂)
  rw [Tensor.permute_external]
  change map (fun c ↦ TensorProduct.map
      (cwBaseConstituentSwapEquiv K q x₁ y₁ z₁ c).toLinearMap
      (cwBaseConstituentSwapEquiv K q x₂ y₂ z₂ c).toLinearMap)
      (Tensor.external
        (Tensor.permute xzy (cwConstituentOfBlocks K q x₁ y₁ z₁))
        (Tensor.permute xzy (cwConstituentOfBlocks K q x₂ y₂ z₂))) = _
  rw [Tensor.map_external,
    cwConstituentOfBlocks_swap K q x₁ y₁ z₁ h₁,
    cwConstituentOfBlocks_swap K q x₂ y₂ z₂ h₂]

/-- Swapping both fine addresses identifies the corresponding degree-sum fibers. -/
def cwSquareSwapFiberEquiv
    (x₁ y₁ z₁ x₂ y₂ z₂ : CWBlock) (c : Leg) :
    BlockFiber cwSquareDegreeMap (xzy.symm c)
        (coarsenBlockAddress cwSquareDegreeMap
          (cwSquareRawAddress (ofLegs x₁ y₁ z₁) (ofLegs x₂ y₂ z₂))
          (xzy.symm c)) ≃
      BlockFiber cwSquareDegreeMap c
        (coarsenBlockAddress cwSquareDegreeMap
          (cwSquareRawAddress (cwBlockSwapAddress x₁ y₁ z₁)
            (cwBlockSwapAddress x₂ y₂ z₂)) c) := by
  cases c <;> exact Equiv.refl _

/-- Reindex the coarsened direct-sum blocks along the `Y`/`Z` swap of a raw address pair. -/
noncomputable def cwSquareCoarseSwapEquiv
    (K : Type u) [CommRing K] (q : ℕ)
    (x₁ y₁ z₁ x₂ y₂ z₂ : CWBlock) : ∀ c,
    CWSquareBlockSpace K q (xzy.symm c)
        (coarsenBlockAddress cwSquareDegreeMap
          (cwSquareRawAddress (ofLegs x₁ y₁ z₁) (ofLegs x₂ y₂ z₂))
          (xzy.symm c)) ≃ₗ[K]
      CWSquareBlockSpace K q c
        (coarsenBlockAddress cwSquareDegreeMap
          (cwSquareRawAddress (cwBlockSwapAddress x₁ y₁ z₁)
            (cwBlockSwapAddress x₂ y₂ z₂)) c) := by
  intro c
  cases c <;>
    exact DirectSum.lequivCongrLeft K
      (cwSquareSwapFiberEquiv x₁ y₁ z₁ x₂ y₂ z₂ _)

/-- The `Y`/`Z` symmetry of a raw square constituent descends through degree-sum coarsening.

Proof sketch: invoke the generic coarsening-naturality theorem with
`cwSquareRawConstituent_swap`; the remaining local calculation is the canonical direct-sum
fiber reindexing on a single included block. -/
theorem cwSquareCoarsenedTerm_swap
    (K : Type u) [CommRing K] (q : ℕ)
    (x₁ y₁ z₁ x₂ y₂ z₂ : CWBlock)
    (h₁ : ofLegs (V := fun _ : Leg ↦ CWBlock) x₁ y₁ z₁ ∈ cwBlockSupport)
    (h₂ : ofLegs (V := fun _ : Leg ↦ CWBlock) x₂ y₂ z₂ ∈ cwBlockSupport) :
    map (fun c ↦
        (cwSquareCoarseSwapEquiv K q x₁ y₁ z₁ x₂ y₂ z₂ c).toLinearMap)
      (Tensor.permute xzy
        (coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap
          (coarsenBlockAddress cwSquareDegreeMap
            (cwSquareRawAddress (ofLegs x₁ y₁ z₁) (ofLegs x₂ y₂ z₂)))
          (cwSquareRawAddress (ofLegs x₁ y₁ z₁) (ofLegs x₂ y₂ z₂)))) =
      coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
        cwSquareDegreeMap
        (coarsenBlockAddress cwSquareDegreeMap
          (cwSquareRawAddress (cwBlockSwapAddress x₁ y₁ z₁)
            (cwBlockSwapAddress x₂ y₂ z₂)))
        (cwSquareRawAddress (cwBlockSwapAddress x₁ y₁ z₁)
          (cwBlockSwapAddress x₂ y₂ z₂)) := by
  apply map_permute_coarsenedTerm
    ((cwPartitionedTensor K q).positivePower 1) cwSquareDegreeMap
    (cwSquareRawAddress (ofLegs x₁ y₁ z₁) (ofLegs x₂ y₂ z₂))
    (cwSquareRawAddress (cwBlockSwapAddress x₁ y₁ z₁)
      (cwBlockSwapAddress x₂ y₂ z₂))
    _ _ rfl rfl xzy
    (cwSquareRawSwapMap K q x₁ y₁ z₁ x₂ y₂ z₂)
    (cwSquareCoarseSwapEquiv K q x₁ y₁ z₁ x₂ y₂ z₂)
  · exact cwSquareRawConstituent_swap K q x₁ y₁ z₁ x₂ y₂ z₂ h₁ h₂
  · intro c x
    cases c <;>
      simp only [cwSquareCoarseSwapEquiv, coarsenedBlockIncludeAt,
        cwSquareRawSwapMap, cwBlockSwapAddress, cwSquareDegreeMap,
        cwSquareBlockDegree]
    all_goals
      apply DirectSum.lequivCongrLeft_lof K
      · exact eq_of_heq ((cast_heq _ x).trans (by
          simp only [cwBaseConstituentSwapEquiv]
          change HEq x ((TensorProduct.map LinearMap.id LinearMap.id) x)
          rw [TensorProduct.map_id]
          rfl))
      · apply Subtype.ext
        rfl

/-! ## Coarse-address symmetry independent of individual raw summands -/

/-- Rotate a coarse square address by the forward three-cycle. -/
abbrev cwSquareCycleAddress (source : CWSquareAddress) : CWSquareAddress :=
  fun c ↦ source (cycle.symm c)

/-- The degree fiber of a rotated coarse address is the same fiber with its leg name changed. -/
def cwSquareAddressCycleFiberEquiv (source : CWSquareAddress) (c : Leg) :
    BlockFiber cwSquareDegreeMap (cycle.symm c) (source (cycle.symm c)) ≃
      BlockFiber cwSquareDegreeMap c (cwSquareCycleAddress source c) := by
  cases c <;> exact Equiv.refl _

/-- One fixed coordinate equivalence rotates an entire coarse constituent, independently of
which raw summand in its source fiber is being considered. -/
noncomputable def cwSquareAddressCycleEquiv
    (K : Type u) [CommRing K] (q : ℕ) (source : CWSquareAddress) : ∀ c,
    CWSquareBlockSpace K q (cycle.symm c) (source (cycle.symm c)) ≃ₗ[K]
      CWSquareBlockSpace K q c (cwSquareCycleAddress source c) := by
  intro c
  cases c <;> exact DirectSum.lequivCongrLeft K
    (cwSquareAddressCycleFiberEquiv source _)

/-- A raw term over a named coarse address rotates using the address-level coordinate
equivalence, provided the raw address actually lies over that coarse address.

Unlike `cwSquareCoarsenedTerm_cycle`, the leg map here depends only on `source`.  It can therefore
be distributed over the full sum defining a two- or three-term ordinary constituent.

Proof sketch: the rotated raw address lies over `cwSquareCycleAddress source` by applying
`hsource` on the inverse leg.  The rest is the same coarsening-naturality calculation as for the
raw-address-indexed form. -/
theorem cwSquareCoarsenedTerm_cycleAt
    (K : Type u) [CommRing K] (q : ℕ)
    (source : CWSquareAddress)
    (x₁ y₁ z₁ x₂ y₂ z₂ : CWBlock)
    (h₁ : ofLegs (V := fun _ : Leg ↦ CWBlock) x₁ y₁ z₁ ∈ cwBlockSupport)
    (h₂ : ofLegs (V := fun _ : Leg ↦ CWBlock) x₂ y₂ z₂ ∈ cwBlockSupport)
    (hsource : coarsenBlockAddress cwSquareDegreeMap
      (cwSquareRawAddress (ofLegs x₁ y₁ z₁) (ofLegs x₂ y₂ z₂)) = source) :
    map (fun c ↦ (cwSquareAddressCycleEquiv K q source c).toLinearMap)
      (Tensor.permute cycle
        (coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap source
          (cwSquareRawAddress (ofLegs x₁ y₁ z₁) (ofLegs x₂ y₂ z₂)))) =
      coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
        cwSquareDegreeMap (cwSquareCycleAddress source)
        (cwSquareRawAddress (cwBlockCycleAddress x₁ y₁ z₁)
          (cwBlockCycleAddress x₂ y₂ z₂)) := by
  have htarget : coarsenBlockAddress cwSquareDegreeMap
      (cwSquareRawAddress (cwBlockCycleAddress x₁ y₁ z₁)
        (cwBlockCycleAddress x₂ y₂ z₂)) =
      cwSquareCycleAddress source := by
    funext c
    cases c with
    | X => exact congrFun hsource .Z
    | Y => exact congrFun hsource .X
    | Z => exact congrFun hsource .Y
  apply map_permute_coarsenedTerm
    ((cwPartitionedTensor K q).positivePower 1) cwSquareDegreeMap
    (cwSquareRawAddress (ofLegs x₁ y₁ z₁) (ofLegs x₂ y₂ z₂))
    (cwSquareRawAddress (cwBlockCycleAddress x₁ y₁ z₁)
      (cwBlockCycleAddress x₂ y₂ z₂))
    source (cwSquareCycleAddress source) hsource htarget cycle
    (cwSquareRawCycleMap K q x₁ y₁ z₁ x₂ y₂ z₂)
    (cwSquareAddressCycleEquiv K q source)
  · exact cwSquareRawConstituent_cycle K q
      x₁ y₁ z₁ x₂ y₂ z₂ h₁ h₂
  · intro c x
    cases c <;>
      simp only [cwSquareAddressCycleEquiv, coarsenedBlockIncludeAt,
        cwSquareRawCycleMap, cwBlockCycleAddress, cwSquareDegreeMap,
        cwSquareBlockDegree]
    all_goals
      apply DirectSum.lequivCongrLeft_lof K
      · exact eq_of_heq ((cast_heq _ x).trans (by
          simp only [cwBaseConstituentCycleEquiv]
          change HEq x ((TensorProduct.map LinearMap.id LinearMap.id) x)
          rw [TensorProduct.map_id]
          rfl))
      · apply Subtype.ext
        rfl

/-- Swap the `Y` and `Z` entries of a coarse square address. -/
abbrev cwSquareSwapAddress (source : CWSquareAddress) : CWSquareAddress :=
  fun c ↦ source (xzy.symm c)

/-- The degree fibers at a coarse address and its `Y`/`Z` swap are canonically identical. -/
def cwSquareAddressSwapFiberEquiv (source : CWSquareAddress) (c : Leg) :
    BlockFiber cwSquareDegreeMap (xzy.symm c) (source (xzy.symm c)) ≃
      BlockFiber cwSquareDegreeMap c (cwSquareSwapAddress source c) := by
  cases c <;> exact Equiv.refl _

/-- One fixed coordinate equivalence swaps an entire coarse constituent. -/
noncomputable def cwSquareAddressSwapEquiv
    (K : Type u) [CommRing K] (q : ℕ) (source : CWSquareAddress) : ∀ c,
    CWSquareBlockSpace K q (xzy.symm c) (source (xzy.symm c)) ≃ₗ[K]
      CWSquareBlockSpace K q c (cwSquareSwapAddress source c) := by
  intro c
  cases c <;> exact DirectSum.lequivCongrLeft K
    (cwSquareAddressSwapFiberEquiv source _)

/-- A raw term over a named coarse address respects the fixed address-level `Y`/`Z`
equivalence.

Proof sketch: swapping the fine labels commutes with degree coarsening because the degree map is
the same on every leg.  Apply `map_permute_coarsenedTerm`, using the base square swap theorem for
the fine constituent and direct-sum reindexing for the inclusions. -/
theorem cwSquareCoarsenedTerm_swapAt
    (K : Type u) [CommRing K] (q : ℕ)
    (source : CWSquareAddress)
    (x₁ y₁ z₁ x₂ y₂ z₂ : CWBlock)
    (h₁ : ofLegs (V := fun _ : Leg ↦ CWBlock) x₁ y₁ z₁ ∈ cwBlockSupport)
    (h₂ : ofLegs (V := fun _ : Leg ↦ CWBlock) x₂ y₂ z₂ ∈ cwBlockSupport)
    (hsource : coarsenBlockAddress cwSquareDegreeMap
      (cwSquareRawAddress (ofLegs x₁ y₁ z₁) (ofLegs x₂ y₂ z₂)) = source) :
    map (fun c ↦ (cwSquareAddressSwapEquiv K q source c).toLinearMap)
      (Tensor.permute xzy
        (coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap source
          (cwSquareRawAddress (ofLegs x₁ y₁ z₁) (ofLegs x₂ y₂ z₂)))) =
      coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
        cwSquareDegreeMap (cwSquareSwapAddress source)
        (cwSquareRawAddress (cwBlockSwapAddress x₁ y₁ z₁)
          (cwBlockSwapAddress x₂ y₂ z₂)) := by
  have htarget : coarsenBlockAddress cwSquareDegreeMap
      (cwSquareRawAddress (cwBlockSwapAddress x₁ y₁ z₁)
        (cwBlockSwapAddress x₂ y₂ z₂)) =
      cwSquareSwapAddress source := by
    funext c
    cases c with
    | X => exact congrFun hsource .X
    | Y => exact congrFun hsource .Z
    | Z => exact congrFun hsource .Y
  apply map_permute_coarsenedTerm
    ((cwPartitionedTensor K q).positivePower 1) cwSquareDegreeMap
    (cwSquareRawAddress (ofLegs x₁ y₁ z₁) (ofLegs x₂ y₂ z₂))
    (cwSquareRawAddress (cwBlockSwapAddress x₁ y₁ z₁)
      (cwBlockSwapAddress x₂ y₂ z₂))
    source (cwSquareSwapAddress source) hsource htarget xzy
    (cwSquareRawSwapMap K q x₁ y₁ z₁ x₂ y₂ z₂)
    (cwSquareAddressSwapEquiv K q source)
  · exact cwSquareRawConstituent_swap K q
      x₁ y₁ z₁ x₂ y₂ z₂ h₁ h₂
  · intro c x
    cases c <;>
      simp only [cwSquareAddressSwapEquiv, coarsenedBlockIncludeAt,
        cwSquareRawSwapMap, cwBlockSwapAddress, cwSquareDegreeMap,
        cwSquareBlockDegree]
    all_goals
      apply DirectSum.lequivCongrLeft_lof K
      · exact eq_of_heq ((cast_heq _ x).trans (by
          simp only [cwBaseConstituentSwapEquiv]
          change HEq x ((TensorProduct.map LinearMap.id LinearMap.id) x)
          rw [TensorProduct.map_id]
          rfl))
      · apply Subtype.ext
        rfl

/-- The exceptional square address with degree profile `(2,1,1)`. -/
abbrev cwSquare211 : CWSquareAddress := cwSquareAddress 2 1 1

/-- The exceptional square address with degree profile `(1,2,1)`. -/
abbrev cwSquare121 : CWSquareAddress := cwSquareAddress 1 2 1

/-- The degree fiber on each `211` leg is the corresponding rotated `112` degree fiber. -/
def cwSquare211CycleFiberEquiv (c : Leg) :
    BlockFiber cwSquareDegreeMap c (cwSquare211 c) ≃
      BlockFiber cwSquareDegreeMap (cycle.symm c) (cwSquare112 (cycle.symm c)) := by
  cases c <;> exact Equiv.refl _

/-- At the three exceptional addresses, cycling the legs reindexes the same coarse coordinate
fibers. -/
noncomputable def cwSquare211CycleEquiv
    (K : Type u) [CommRing K] (q : ℕ) : ∀ c,
    CWSquareBlockSpace K q c (cwSquare211 c) ≃ₗ[K]
      CWSquareBlockSpace K q (cycle.symm c) (cwSquare112 (cycle.symm c)) := by
  intro c
  cases c with
  | X => exact DirectSum.lequivCongrLeft K (cwSquare211CycleFiberEquiv .X)
  | Y => exact DirectSum.lequivCongrLeft K (cwSquare211CycleFiberEquiv .Y)
  | Z => exact DirectSum.lequivCongrLeft K (cwSquare211CycleFiberEquiv .Z)

/-- The degree fiber on each `121` leg is the corresponding rotation of a `211` fiber. -/
def cwSquare121CycleFiberEquiv (c : Leg) :
    BlockFiber cwSquareDegreeMap c (cwSquare121 c) ≃
      BlockFiber cwSquareDegreeMap (cycle.symm c) (cwSquare211 (cycle.symm c)) := by
  cases c <;> exact Equiv.refl _

/-- Cycling the legs reindexes the coarse coordinate fibers from `211` to `121`. -/
noncomputable def cwSquare121CycleEquiv
    (K : Type u) [CommRing K] (q : ℕ) : ∀ c,
    CWSquareBlockSpace K q c (cwSquare121 c) ≃ₗ[K]
      CWSquareBlockSpace K q (cycle.symm c) (cwSquare211 (cycle.symm c)) := by
  intro c
  cases c with
  | X => exact DirectSum.lequivCongrLeft K (cwSquare121CycleFiberEquiv .X)
  | Y => exact DirectSum.lequivCongrLeft K (cwSquare121CycleFiberEquiv .Y)
  | Z => exact DirectSum.lequivCongrLeft K (cwSquare121CycleFiberEquiv .Z)

/-- The four ordered raw products that coarsen to the exceptional address `211`. -/
theorem cwSquareSourceFiber_211 :
    cwSquareSourceFiber cwSquare211 =
      {cwSquareRawAddress cw200 cw011,
        cwSquareRawAddress cw011 cw200,
        cwSquareRawAddress cw101 cw110,
        cwSquareRawAddress cw110 cw101} := by
  decide

/-- The four ordered raw products that coarsen to the exceptional address `121`. -/
theorem cwSquareSourceFiber_121 :
    cwSquareSourceFiber cwSquare121 =
      {cwSquareRawAddress cw020 cw101,
        cwSquareRawAddress cw101 cw020,
        cwSquareRawAddress cw110 cw011,
        cwSquareRawAddress cw011 cw110} := by
  decide

private noncomputable def cwSquareRaw200011CycleEquiv
    (K : Type u) [CommRing K] (q : ℕ) : ∀ c,
    CWSquareRawBlockSpace K q c (cwSquareRawAddress cw200 cw011 c) ≃ₗ[K]
      CWSquareRawBlockSpace K q (cycle.symm c)
        (cwSquareRawAddress cw002 cw110 (cycle.symm c)) := by
  intro c
  cases c <;> exact LinearEquiv.refl K _

private theorem cwSquareRaw_200_011_cycle
    (K : Type u) [CommRing K] (q : ℕ) :
    map (fun c ↦ (cwSquareRaw200011CycleEquiv K q c).toLinearMap)
        (((cwPartitionedTensor K q).positivePower 1).constituent
          (cwSquareRawAddress cw200 cw011)) =
      Tensor.permute cycle
        (((cwPartitionedTensor K q).positivePower 1).constituent
          (cwSquareRawAddress cw002 cw110)) := by
  let rawCycle := fun c ↦ (cwSquareRaw200011CycleEquiv K q c).toLinearMap
  let left : Fin q → Tensor3 K (fun c ↦
      CWSquareRawBlockSpace K q c (cwSquareRawAddress cw200 cw011 c)) := fun i ↦
    external
      (pure (K := K) (ofLegs
        (cwBlockBasis K q .last ())
        (cwBlockBasis K q .zero ())
        (cwBlockBasis K q .zero ())))
      (pure (K := K) (ofLegs
        (cwBlockBasis K q .zero ())
        (cwBlockBasis K q .middle i)
        (cwBlockBasis K q .middle i)))
  let right : Fin q → Tensor3 K (fun c ↦
      CWSquareRawBlockSpace K q c (cwSquareRawAddress cw002 cw110 c)) := fun i ↦
    external
      (pure (K := K) (ofLegs
        (cwBlockBasis K q .zero ())
        (cwBlockBasis K q .zero ())
        (cwBlockBasis K q .last ())))
      (pure (K := K) (ofLegs
        (cwBlockBasis K q .middle i)
        (cwBlockBasis K q .middle i)
        (cwBlockBasis K q .zero ())))
  rw [cwSquareRawConstituent, cwSquareRawConstituent]
  simp only [cwPartitionedTensor, cwPartitionConstituent_ofLegs,
    cwConstituentOfBlocks]
  rw [external_fintypeSum_right, external_fintypeSum_right]
  change map rawCycle (∑ i, left i) = Tensor.permute cycle (∑ i, right i)
  calc
    map rawCycle (∑ i, left i) = ∑ i, map rawCycle (left i) :=
      map_sum (map rawCycle) left Finset.univ
    _ = ∑ i, Tensor.permute cycle (right i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [left, right, Tensor.external_pure, Tensor.map_pure,
        Tensor.permute_pure]
      congr 1
      funext leg
      cases leg <;> rfl
    _ = Tensor.permute cycle (∑ i, right i) :=
      (map_sum (Tensor.permute (K := K) cycle) right Finset.univ).symm

private noncomputable def cwSquareRaw011200CycleEquiv
    (K : Type u) [CommRing K] (q : ℕ) : ∀ c,
    CWSquareRawBlockSpace K q c (cwSquareRawAddress cw011 cw200 c) ≃ₗ[K]
      CWSquareRawBlockSpace K q (cycle.symm c)
        (cwSquareRawAddress cw110 cw002 (cycle.symm c)) := by
  intro c
  cases c <;> exact LinearEquiv.refl K _

private theorem cwSquareRaw_011_200_cycle
    (K : Type u) [CommRing K] (q : ℕ) :
    map (fun c ↦ (cwSquareRaw011200CycleEquiv K q c).toLinearMap)
        (((cwPartitionedTensor K q).positivePower 1).constituent
          (cwSquareRawAddress cw011 cw200)) =
      Tensor.permute cycle
        (((cwPartitionedTensor K q).positivePower 1).constituent
          (cwSquareRawAddress cw110 cw002)) := by
  let rawCycle := fun c ↦ (cwSquareRaw011200CycleEquiv K q c).toLinearMap
  let left : Fin q → Tensor3 K (fun c ↦
      CWSquareRawBlockSpace K q c (cwSquareRawAddress cw011 cw200 c)) := fun i ↦
    external
      (pure (K := K) (ofLegs
        (cwBlockBasis K q .zero ())
        (cwBlockBasis K q .middle i)
        (cwBlockBasis K q .middle i)))
      (pure (K := K) (ofLegs
        (cwBlockBasis K q .last ())
        (cwBlockBasis K q .zero ())
        (cwBlockBasis K q .zero ())))
  let right : Fin q → Tensor3 K (fun c ↦
      CWSquareRawBlockSpace K q c (cwSquareRawAddress cw110 cw002 c)) := fun i ↦
    external
      (pure (K := K) (ofLegs
        (cwBlockBasis K q .middle i)
        (cwBlockBasis K q .middle i)
        (cwBlockBasis K q .zero ())))
      (pure (K := K) (ofLegs
        (cwBlockBasis K q .zero ())
        (cwBlockBasis K q .zero ())
        (cwBlockBasis K q .last ())))
  rw [cwSquareRawConstituent, cwSquareRawConstituent]
  simp only [cwPartitionedTensor, cwPartitionConstituent_ofLegs,
    cwConstituentOfBlocks]
  rw [external_fintypeSum_left, external_fintypeSum_left]
  change map rawCycle (∑ i, left i) = Tensor.permute cycle (∑ i, right i)
  calc
    map rawCycle (∑ i, left i) = ∑ i, map rawCycle (left i) :=
      map_sum (map rawCycle) left Finset.univ
    _ = ∑ i, Tensor.permute cycle (right i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [left, right, Tensor.external_pure, Tensor.map_pure,
        Tensor.permute_pure]
      congr 1
      funext leg
      cases leg <;> rfl
    _ = Tensor.permute cycle (∑ i, right i) :=
      (map_sum (Tensor.permute (K := K) cycle) right Finset.univ).symm

private noncomputable def cwSquareRaw101110CycleEquiv
    (K : Type u) [CommRing K] (q : ℕ) : ∀ c,
    CWSquareRawBlockSpace K q c (cwSquareRawAddress cw101 cw110 c) ≃ₗ[K]
      CWSquareRawBlockSpace K q (cycle.symm c)
        (cwSquareRawAddress cw011 cw101 (cycle.symm c)) := by
  intro c
  cases c <;> exact LinearEquiv.refl K _

private theorem cwSquareRaw_101_110_cycle
    (K : Type u) [CommRing K] (q : ℕ) :
    map (fun c ↦ (cwSquareRaw101110CycleEquiv K q c).toLinearMap)
        (((cwPartitionedTensor K q).positivePower 1).constituent
          (cwSquareRawAddress cw101 cw110)) =
      Tensor.permute cycle
        (((cwPartitionedTensor K q).positivePower 1).constituent
          (cwSquareRawAddress cw011 cw101)) := by
  let rawCycle := fun c ↦ (cwSquareRaw101110CycleEquiv K q c).toLinearMap
  let left : Fin q → Fin q → Tensor3 K (fun c ↦
      CWSquareRawBlockSpace K q c (cwSquareRawAddress cw101 cw110 c)) := fun i j ↦
    external
      (pure (K := K) (ofLegs
        (cwBlockBasis K q .middle i)
        (cwBlockBasis K q .zero ())
        (cwBlockBasis K q .middle i)))
      (pure (K := K) (ofLegs
        (cwBlockBasis K q .middle j)
        (cwBlockBasis K q .middle j)
        (cwBlockBasis K q .zero ())))
  let right : Fin q → Fin q → Tensor3 K (fun c ↦
      CWSquareRawBlockSpace K q c (cwSquareRawAddress cw011 cw101 c)) := fun i j ↦
    external
      (pure (K := K) (ofLegs
        (cwBlockBasis K q .zero ())
        (cwBlockBasis K q .middle i)
        (cwBlockBasis K q .middle i)))
      (pure (K := K) (ofLegs
        (cwBlockBasis K q .middle j)
        (cwBlockBasis K q .zero ())
        (cwBlockBasis K q .middle j)))
  rw [cwSquareRawConstituent, cwSquareRawConstituent]
  simp only [cwPartitionedTensor, cwPartitionConstituent_ofLegs,
    cwConstituentOfBlocks]
  rw [external_sum_sum, external_sum_sum]
  change map rawCycle (∑ i, ∑ j, left i j) =
    Tensor.permute cycle (∑ i, ∑ j, right i j)
  calc
    map rawCycle (∑ i, ∑ j, left i j) =
        ∑ i, ∑ j, map rawCycle (left i j) := by simp
    _ = ∑ i, ∑ j, Tensor.permute cycle (right i j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [left, right, Tensor.external_pure, Tensor.map_pure,
        Tensor.permute_pure]
      congr 1
      funext leg
      cases leg <;> rfl
    _ = Tensor.permute cycle (∑ i, ∑ j, right i j) := by simp

private noncomputable def cwSquareRaw110101CycleEquiv
    (K : Type u) [CommRing K] (q : ℕ) : ∀ c,
    CWSquareRawBlockSpace K q c (cwSquareRawAddress cw110 cw101 c) ≃ₗ[K]
      CWSquareRawBlockSpace K q (cycle.symm c)
        (cwSquareRawAddress cw101 cw011 (cycle.symm c)) := by
  intro c
  cases c <;> exact LinearEquiv.refl K _

private theorem cwSquareRaw_110_101_cycle
    (K : Type u) [CommRing K] (q : ℕ) :
    map (fun c ↦ (cwSquareRaw110101CycleEquiv K q c).toLinearMap)
        (((cwPartitionedTensor K q).positivePower 1).constituent
          (cwSquareRawAddress cw110 cw101)) =
      Tensor.permute cycle
        (((cwPartitionedTensor K q).positivePower 1).constituent
          (cwSquareRawAddress cw101 cw011)) := by
  let rawCycle := fun c ↦ (cwSquareRaw110101CycleEquiv K q c).toLinearMap
  let left : Fin q → Fin q → Tensor3 K (fun c ↦
      CWSquareRawBlockSpace K q c (cwSquareRawAddress cw110 cw101 c)) := fun i j ↦
    external
      (pure (K := K) (ofLegs
        (cwBlockBasis K q .middle i)
        (cwBlockBasis K q .middle i)
        (cwBlockBasis K q .zero ())))
      (pure (K := K) (ofLegs
        (cwBlockBasis K q .middle j)
        (cwBlockBasis K q .zero ())
        (cwBlockBasis K q .middle j)))
  let right : Fin q → Fin q → Tensor3 K (fun c ↦
      CWSquareRawBlockSpace K q c (cwSquareRawAddress cw101 cw011 c)) := fun i j ↦
    external
      (pure (K := K) (ofLegs
        (cwBlockBasis K q .middle i)
        (cwBlockBasis K q .zero ())
        (cwBlockBasis K q .middle i)))
      (pure (K := K) (ofLegs
        (cwBlockBasis K q .zero ())
        (cwBlockBasis K q .middle j)
        (cwBlockBasis K q .middle j)))
  rw [cwSquareRawConstituent, cwSquareRawConstituent]
  simp only [cwPartitionedTensor, cwPartitionConstituent_ofLegs,
    cwConstituentOfBlocks]
  rw [external_sum_sum, external_sum_sum]
  change map rawCycle (∑ i, ∑ j, left i j) =
    Tensor.permute cycle (∑ i, ∑ j, right i j)
  calc
    map rawCycle (∑ i, ∑ j, left i j) =
        ∑ i, ∑ j, map rawCycle (left i j) := by simp
    _ = ∑ i, ∑ j, Tensor.permute cycle (right i j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [left, right, Tensor.external_pure, Tensor.map_pure,
        Tensor.permute_pure]
      congr 1
      funext leg
      cases leg <;> rfl
    _ = Tensor.permute cycle (∑ i, ∑ j, right i j) := by simp

private noncomputable def cwSquareRaw020101CycleEquiv
    (K : Type u) [CommRing K] (q : ℕ) : ∀ c,
    CWSquareRawBlockSpace K q c (cwSquareRawAddress cw020 cw101 c) ≃ₗ[K]
      CWSquareRawBlockSpace K q (cycle.symm c)
        (cwSquareRawAddress cw200 cw011 (cycle.symm c)) := by
  intro c
  cases c <;> exact LinearEquiv.refl K _

private theorem cwSquareRaw_020_101_cycle
    (K : Type u) [CommRing K] (q : ℕ) :
    map (fun c ↦ (cwSquareRaw020101CycleEquiv K q c).toLinearMap)
        (((cwPartitionedTensor K q).positivePower 1).constituent
          (cwSquareRawAddress cw020 cw101)) =
      Tensor.permute cycle
        (((cwPartitionedTensor K q).positivePower 1).constituent
          (cwSquareRawAddress cw200 cw011)) := by
  let rawCycle := fun c ↦ (cwSquareRaw020101CycleEquiv K q c).toLinearMap
  let left : Fin q → Tensor3 K (fun c ↦
      CWSquareRawBlockSpace K q c (cwSquareRawAddress cw020 cw101 c)) := fun i ↦
    external
      (pure (K := K) (ofLegs
        (cwBlockBasis K q .zero ())
        (cwBlockBasis K q .last ())
        (cwBlockBasis K q .zero ())))
      (pure (K := K) (ofLegs
        (cwBlockBasis K q .middle i)
        (cwBlockBasis K q .zero ())
        (cwBlockBasis K q .middle i)))
  let right : Fin q → Tensor3 K (fun c ↦
      CWSquareRawBlockSpace K q c (cwSquareRawAddress cw200 cw011 c)) := fun i ↦
    external
      (pure (K := K) (ofLegs
        (cwBlockBasis K q .last ())
        (cwBlockBasis K q .zero ())
        (cwBlockBasis K q .zero ())))
      (pure (K := K) (ofLegs
        (cwBlockBasis K q .zero ())
        (cwBlockBasis K q .middle i)
        (cwBlockBasis K q .middle i)))
  rw [cwSquareRawConstituent, cwSquareRawConstituent]
  simp only [cwPartitionedTensor, cwPartitionConstituent_ofLegs,
    cwConstituentOfBlocks]
  rw [external_fintypeSum_right, external_fintypeSum_right]
  change map rawCycle (∑ i, left i) = Tensor.permute cycle (∑ i, right i)
  calc
    map rawCycle (∑ i, left i) = ∑ i, map rawCycle (left i) := by simp
    _ = ∑ i, Tensor.permute cycle (right i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [left, right, Tensor.external_pure, Tensor.map_pure,
        Tensor.permute_pure]
      congr 1
      funext leg
      cases leg <;> rfl
    _ = Tensor.permute cycle (∑ i, right i) := by simp

private noncomputable def cwSquareRaw101020CycleEquiv
    (K : Type u) [CommRing K] (q : ℕ) : ∀ c,
    CWSquareRawBlockSpace K q c (cwSquareRawAddress cw101 cw020 c) ≃ₗ[K]
      CWSquareRawBlockSpace K q (cycle.symm c)
        (cwSquareRawAddress cw011 cw200 (cycle.symm c)) := by
  intro c
  cases c <;> exact LinearEquiv.refl K _

private theorem cwSquareRaw_101_020_cycle
    (K : Type u) [CommRing K] (q : ℕ) :
    map (fun c ↦ (cwSquareRaw101020CycleEquiv K q c).toLinearMap)
        (((cwPartitionedTensor K q).positivePower 1).constituent
          (cwSquareRawAddress cw101 cw020)) =
      Tensor.permute cycle
        (((cwPartitionedTensor K q).positivePower 1).constituent
          (cwSquareRawAddress cw011 cw200)) := by
  let rawCycle := fun c ↦ (cwSquareRaw101020CycleEquiv K q c).toLinearMap
  let left : Fin q → Tensor3 K (fun c ↦
      CWSquareRawBlockSpace K q c (cwSquareRawAddress cw101 cw020 c)) := fun i ↦
    external
      (pure (K := K) (ofLegs
        (cwBlockBasis K q .middle i)
        (cwBlockBasis K q .zero ())
        (cwBlockBasis K q .middle i)))
      (pure (K := K) (ofLegs
        (cwBlockBasis K q .zero ())
        (cwBlockBasis K q .last ())
        (cwBlockBasis K q .zero ())))
  let right : Fin q → Tensor3 K (fun c ↦
      CWSquareRawBlockSpace K q c (cwSquareRawAddress cw011 cw200 c)) := fun i ↦
    external
      (pure (K := K) (ofLegs
        (cwBlockBasis K q .zero ())
        (cwBlockBasis K q .middle i)
        (cwBlockBasis K q .middle i)))
      (pure (K := K) (ofLegs
        (cwBlockBasis K q .last ())
        (cwBlockBasis K q .zero ())
        (cwBlockBasis K q .zero ())))
  rw [cwSquareRawConstituent, cwSquareRawConstituent]
  simp only [cwPartitionedTensor, cwPartitionConstituent_ofLegs,
    cwConstituentOfBlocks]
  rw [external_fintypeSum_left, external_fintypeSum_left]
  change map rawCycle (∑ i, left i) = Tensor.permute cycle (∑ i, right i)
  calc
    map rawCycle (∑ i, left i) = ∑ i, map rawCycle (left i) := by simp
    _ = ∑ i, Tensor.permute cycle (right i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [left, right, Tensor.external_pure, Tensor.map_pure,
        Tensor.permute_pure]
      congr 1
      funext leg
      cases leg <;> rfl
    _ = Tensor.permute cycle (∑ i, right i) := by simp

private noncomputable def cwSquareRaw110011CycleEquiv
    (K : Type u) [CommRing K] (q : ℕ) : ∀ c,
    CWSquareRawBlockSpace K q c (cwSquareRawAddress cw110 cw011 c) ≃ₗ[K]
      CWSquareRawBlockSpace K q (cycle.symm c)
        (cwSquareRawAddress cw101 cw110 (cycle.symm c)) := by
  intro c
  cases c <;> exact LinearEquiv.refl K _

private theorem cwSquareRaw_110_011_cycle
    (K : Type u) [CommRing K] (q : ℕ) :
    map (fun c ↦ (cwSquareRaw110011CycleEquiv K q c).toLinearMap)
        (((cwPartitionedTensor K q).positivePower 1).constituent
          (cwSquareRawAddress cw110 cw011)) =
      Tensor.permute cycle
        (((cwPartitionedTensor K q).positivePower 1).constituent
          (cwSquareRawAddress cw101 cw110)) := by
  let rawCycle := fun c ↦ (cwSquareRaw110011CycleEquiv K q c).toLinearMap
  let left : Fin q → Fin q → Tensor3 K (fun c ↦
      CWSquareRawBlockSpace K q c (cwSquareRawAddress cw110 cw011 c)) := fun i j ↦
    external
      (pure (K := K) (ofLegs
        (cwBlockBasis K q .middle i)
        (cwBlockBasis K q .middle i)
        (cwBlockBasis K q .zero ())))
      (pure (K := K) (ofLegs
        (cwBlockBasis K q .zero ())
        (cwBlockBasis K q .middle j)
        (cwBlockBasis K q .middle j)))
  let right : Fin q → Fin q → Tensor3 K (fun c ↦
      CWSquareRawBlockSpace K q c (cwSquareRawAddress cw101 cw110 c)) := fun i j ↦
    external
      (pure (K := K) (ofLegs
        (cwBlockBasis K q .middle i)
        (cwBlockBasis K q .zero ())
        (cwBlockBasis K q .middle i)))
      (pure (K := K) (ofLegs
        (cwBlockBasis K q .middle j)
        (cwBlockBasis K q .middle j)
        (cwBlockBasis K q .zero ())))
  rw [cwSquareRawConstituent, cwSquareRawConstituent]
  simp only [cwPartitionedTensor, cwPartitionConstituent_ofLegs,
    cwConstituentOfBlocks]
  rw [external_sum_sum, external_sum_sum]
  change map rawCycle (∑ i, ∑ j, left i j) =
    Tensor.permute cycle (∑ i, ∑ j, right i j)
  calc
    map rawCycle (∑ i, ∑ j, left i j) =
        ∑ i, ∑ j, map rawCycle (left i j) := by simp
    _ = ∑ i, ∑ j, Tensor.permute cycle (right i j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [left, right, Tensor.external_pure, Tensor.map_pure,
        Tensor.permute_pure]
      congr 1
      funext leg
      cases leg <;> rfl
    _ = Tensor.permute cycle (∑ i, ∑ j, right i j) := by simp

private noncomputable def cwSquareRaw011110CycleEquiv
    (K : Type u) [CommRing K] (q : ℕ) : ∀ c,
    CWSquareRawBlockSpace K q c (cwSquareRawAddress cw011 cw110 c) ≃ₗ[K]
      CWSquareRawBlockSpace K q (cycle.symm c)
        (cwSquareRawAddress cw110 cw101 (cycle.symm c)) := by
  intro c
  cases c <;> exact LinearEquiv.refl K _

private theorem cwSquareRaw_011_110_cycle
    (K : Type u) [CommRing K] (q : ℕ) :
    map (fun c ↦ (cwSquareRaw011110CycleEquiv K q c).toLinearMap)
        (((cwPartitionedTensor K q).positivePower 1).constituent
          (cwSquareRawAddress cw011 cw110)) =
      Tensor.permute cycle
        (((cwPartitionedTensor K q).positivePower 1).constituent
          (cwSquareRawAddress cw110 cw101)) := by
  let rawCycle := fun c ↦ (cwSquareRaw011110CycleEquiv K q c).toLinearMap
  let left : Fin q → Fin q → Tensor3 K (fun c ↦
      CWSquareRawBlockSpace K q c (cwSquareRawAddress cw011 cw110 c)) := fun i j ↦
    external
      (pure (K := K) (ofLegs
        (cwBlockBasis K q .zero ())
        (cwBlockBasis K q .middle i)
        (cwBlockBasis K q .middle i)))
      (pure (K := K) (ofLegs
        (cwBlockBasis K q .middle j)
        (cwBlockBasis K q .middle j)
        (cwBlockBasis K q .zero ())))
  let right : Fin q → Fin q → Tensor3 K (fun c ↦
      CWSquareRawBlockSpace K q c (cwSquareRawAddress cw110 cw101 c)) := fun i j ↦
    external
      (pure (K := K) (ofLegs
        (cwBlockBasis K q .middle i)
        (cwBlockBasis K q .middle i)
        (cwBlockBasis K q .zero ())))
      (pure (K := K) (ofLegs
        (cwBlockBasis K q .middle j)
        (cwBlockBasis K q .zero ())
        (cwBlockBasis K q .middle j)))
  rw [cwSquareRawConstituent, cwSquareRawConstituent]
  simp only [cwPartitionedTensor, cwPartitionConstituent_ofLegs,
    cwConstituentOfBlocks]
  rw [external_sum_sum, external_sum_sum]
  change map rawCycle (∑ i, ∑ j, left i j) =
    Tensor.permute cycle (∑ i, ∑ j, right i j)
  calc
    map rawCycle (∑ i, ∑ j, left i j) =
        ∑ i, ∑ j, map rawCycle (left i j) := by simp
    _ = ∑ i, ∑ j, Tensor.permute cycle (right i j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [left, right, Tensor.external_pure, Tensor.map_pure,
        Tensor.permute_pure]
      congr 1
      funext leg
      cases leg <;> rfl
    _ = Tensor.permute cycle (∑ i, ∑ j, right i j) := by simp

/-- A raw cyclic symmetry compatible with the coarsening inclusions descends to the corresponding
coarse square terms. -/
private theorem coarsenedTerm_cycle
    (K : Type u) [CommRing K] (q : ℕ)
    (source211 source112 : BlockAddress (fun _ : Leg ↦ PositiveWord CWBlock 1))
    (h211 : coarsenBlockAddress cwSquareDegreeMap source211 = cwSquare211)
    (h112 : coarsenBlockAddress cwSquareDegreeMap source112 = cwSquare112)
    (hsource : ∀ c, source211 c = source112 (cycle.symm c))
    (rawCycle : ∀ c,
      CWSquareRawBlockSpace K q c (source211 c) ≃ₗ[K]
        CWSquareRawBlockSpace K q (cycle.symm c) (source112 (cycle.symm c)))
    (hraw : map (fun c ↦ (rawCycle c).toLinearMap)
        (((cwPartitionedTensor K q).positivePower 1).constituent source211) =
      Tensor.permute cycle
        (((cwPartitionedTensor K q).positivePower 1).constituent source112))
    (hidentity : ∀ (c) (x : CWSquareRawBlockSpace K q c (source211 c)),
      HEq (rawCycle c x) x) :
    map (fun c ↦ (cwSquare211CycleEquiv K q c).toLinearMap)
        (coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare211 source211) =
      Tensor.permute cycle
        (coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare112 source112) := by
  rw [coarsenedTerm_eq_map_of_eq _ _ _ _ h211,
    coarsenedTerm_eq_map_of_eq _ _ _ _ h112]
  rw [← PiTensorProduct.map_reindex
    (coarsenedBlockIncludeAt
      (K := K) (V := CWSquareRawBlockSpace K q)
      cwSquareDegreeMap source112 cwSquare112 h112)
    cycle]
  let include211 := coarsenedBlockIncludeAt
    (K := K) (V := CWSquareRawBlockSpace K q)
    cwSquareDegreeMap source211 cwSquare211 h211
  let include112 := coarsenedBlockIncludeAt
    (K := K) (V := CWSquareRawBlockSpace K q)
    cwSquareDegreeMap source112 cwSquare112 h112
  let coarseCycle := fun c ↦ (cwSquare211CycleEquiv K q c).toLinearMap
  change map coarseCycle (map include211
      (((cwPartitionedTensor K q).positivePower 1).constituent source211)) =
    map (fun c ↦ include112 (cycle.symm c))
      (Tensor.permute cycle
        (((cwPartitionedTensor K q).positivePower 1).constituent source112))
  rw [← hraw]
  change (map coarseCycle ∘ₗ map include211)
      (((cwPartitionedTensor K q).positivePower 1).constituent source211) =
    (map (fun c ↦ include112 (cycle.symm c)) ∘ₗ
      map (fun c ↦ (rawCycle c).toLinearMap))
      (((cwPartitionedTensor K q).positivePower 1).constituent source211)
  rw [← map_comp, ← map_comp]
  have hmaps :
      (fun leg ↦ coarseCycle leg ∘ₗ include211 leg) =
        (fun leg ↦ include112 (cycle.symm leg) ∘ₗ (rawCycle leg).toLinearMap) := by
    funext leg
    apply LinearMap.ext
    intro x
    change cwSquare211CycleEquiv K q leg
        (coarsenedBlockIncludeAt
          (K := K) (V := CWSquareRawBlockSpace K q)
          cwSquareDegreeMap source211 cwSquare211 h211 leg x) =
      coarsenedBlockIncludeAt
          (K := K) (V := CWSquareRawBlockSpace K q)
          cwSquareDegreeMap source112 cwSquare112 h112 (cycle.symm leg)
        (rawCycle leg x)
    cases leg <;>
      simp only [cwSquare211CycleEquiv, cwSquare211CycleFiberEquiv,
        coarsenedBlockIncludeAt, cwSquareDegreeMap, cwSquareBlockDegree]
    all_goals
      apply DirectSum.lequivCongrLeft_lof K
      · exact eq_of_heq ((cast_heq _ x).trans (hidentity _ x).symm)
      · apply Subtype.ext
        exact hsource _
  rw [hmaps]

/-- The same descent argument for the second cyclic step, from coarse class `211` to `121`. -/
private theorem coarsenedTerm_cycle_121_211
    (K : Type u) [CommRing K] (q : ℕ)
    (source121 source211 : BlockAddress (fun _ : Leg ↦ PositiveWord CWBlock 1))
    (h121 : coarsenBlockAddress cwSquareDegreeMap source121 = cwSquare121)
    (h211 : coarsenBlockAddress cwSquareDegreeMap source211 = cwSquare211)
    (hsource : ∀ c, source121 c = source211 (cycle.symm c))
    (rawCycle : ∀ c,
      CWSquareRawBlockSpace K q c (source121 c) ≃ₗ[K]
        CWSquareRawBlockSpace K q (cycle.symm c) (source211 (cycle.symm c)))
    (hraw : map (fun c ↦ (rawCycle c).toLinearMap)
        (((cwPartitionedTensor K q).positivePower 1).constituent source121) =
      Tensor.permute cycle
        (((cwPartitionedTensor K q).positivePower 1).constituent source211))
    (hidentity : ∀ (c) (x : CWSquareRawBlockSpace K q c (source121 c)),
      HEq (rawCycle c x) x) :
    map (fun c ↦ (cwSquare121CycleEquiv K q c).toLinearMap)
        (coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare121 source121) =
      Tensor.permute cycle
        (coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare211 source211) := by
  rw [coarsenedTerm_eq_map_of_eq _ _ _ _ h121,
    coarsenedTerm_eq_map_of_eq _ _ _ _ h211]
  rw [← PiTensorProduct.map_reindex
    (coarsenedBlockIncludeAt
      (K := K) (V := CWSquareRawBlockSpace K q)
      cwSquareDegreeMap source211 cwSquare211 h211)
    cycle]
  let include121 := coarsenedBlockIncludeAt
    (K := K) (V := CWSquareRawBlockSpace K q)
    cwSquareDegreeMap source121 cwSquare121 h121
  let include211 := coarsenedBlockIncludeAt
    (K := K) (V := CWSquareRawBlockSpace K q)
    cwSquareDegreeMap source211 cwSquare211 h211
  let coarseCycle := fun c ↦ (cwSquare121CycleEquiv K q c).toLinearMap
  change map coarseCycle (map include121
      (((cwPartitionedTensor K q).positivePower 1).constituent source121)) =
    map (fun c ↦ include211 (cycle.symm c))
      (Tensor.permute cycle
        (((cwPartitionedTensor K q).positivePower 1).constituent source211))
  rw [← hraw]
  change (map coarseCycle ∘ₗ map include121)
      (((cwPartitionedTensor K q).positivePower 1).constituent source121) =
    (map (fun c ↦ include211 (cycle.symm c)) ∘ₗ
      map (fun c ↦ (rawCycle c).toLinearMap))
      (((cwPartitionedTensor K q).positivePower 1).constituent source121)
  rw [← map_comp, ← map_comp]
  have hmaps :
      (fun leg ↦ coarseCycle leg ∘ₗ include121 leg) =
        (fun leg ↦ include211 (cycle.symm leg) ∘ₗ (rawCycle leg).toLinearMap) := by
    funext leg
    apply LinearMap.ext
    intro x
    change cwSquare121CycleEquiv K q leg
        (coarsenedBlockIncludeAt
          (K := K) (V := CWSquareRawBlockSpace K q)
          cwSquareDegreeMap source121 cwSquare121 h121 leg x) =
      coarsenedBlockIncludeAt
          (K := K) (V := CWSquareRawBlockSpace K q)
          cwSquareDegreeMap source211 cwSquare211 h211 (cycle.symm leg)
        (rawCycle leg x)
    cases leg <;>
      simp only [cwSquare121CycleEquiv, cwSquare121CycleFiberEquiv,
        coarsenedBlockIncludeAt, cwSquareDegreeMap, cwSquareBlockDegree]
    all_goals
      apply DirectSum.lequivCongrLeft_lof K
      · exact eq_of_heq ((cast_heq _ x).trans (hidentity _ x).symm)
      · apply Subtype.ext
        exact hsource _
  rw [hmaps]

private theorem cwSquareTerm_011_200_cycle
    (K : Type u) [CommRing K] (q : ℕ) :
    map (fun c ↦ (cwSquare211CycleEquiv K q c).toLinearMap)
        (coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare211 (cwSquareRawAddress cw011 cw200)) =
      Tensor.permute cycle
        (coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare112 (cwSquareRawAddress cw110 cw002)) := by
  apply coarsenedTerm_cycle K q _ _ (by decide) (by decide)
    (by intro c; cases c <;> rfl)
    (cwSquareRaw011200CycleEquiv K q)
    (cwSquareRaw_011_200_cycle K q)
  intro c x
  cases c <;> rfl

private theorem cwSquareTerm_101_110_cycle
    (K : Type u) [CommRing K] (q : ℕ) :
    map (fun c ↦ (cwSquare211CycleEquiv K q c).toLinearMap)
        (coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare211 (cwSquareRawAddress cw101 cw110)) =
      Tensor.permute cycle
        (coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare112 (cwSquareRawAddress cw011 cw101)) := by
  apply coarsenedTerm_cycle K q _ _ (by decide) (by decide)
    (by intro c; cases c <;> rfl)
    (cwSquareRaw101110CycleEquiv K q)
    (cwSquareRaw_101_110_cycle K q)
  intro c x
  cases c <;> rfl

private theorem cwSquareTerm_110_101_cycle
    (K : Type u) [CommRing K] (q : ℕ) :
    map (fun c ↦ (cwSquare211CycleEquiv K q c).toLinearMap)
        (coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare211 (cwSquareRawAddress cw110 cw101)) =
      Tensor.permute cycle
        (coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare112 (cwSquareRawAddress cw101 cw011)) := by
  apply coarsenedTerm_cycle K q _ _ (by decide) (by decide)
    (by intro c; cases c <;> rfl)
    (cwSquareRaw110101CycleEquiv K q)
    (cwSquareRaw_110_101_cycle K q)
  intro c x
  cases c <;> rfl

private theorem cwSquareTerm_200_011_cycle
    (K : Type u) [CommRing K] (q : ℕ) :
    map (fun c ↦ (cwSquare211CycleEquiv K q c).toLinearMap)
        (coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare211 (cwSquareRawAddress cw200 cw011)) =
      Tensor.permute cycle
        (coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare112 (cwSquareRawAddress cw002 cw110)) := by
  rw [coarsenedTerm_eq_map_of_eq _ _ _ _ (by decide),
    coarsenedTerm_eq_map_of_eq _ _ _ _ (by decide)]
  rw [← PiTensorProduct.map_reindex
    (coarsenedBlockIncludeAt
      (K := K) (V := CWSquareRawBlockSpace K q)
      cwSquareDegreeMap (cwSquareRawAddress cw002 cw110) cwSquare112 (by decide))
    cycle]
  let source211 := cwSquareRawAddress cw200 cw011
  let source112 := cwSquareRawAddress cw002 cw110
  let include211 := coarsenedBlockIncludeAt
    (K := K) (V := CWSquareRawBlockSpace K q)
    cwSquareDegreeMap source211 cwSquare211 (by decide)
  let include112 := coarsenedBlockIncludeAt
    (K := K) (V := CWSquareRawBlockSpace K q)
    cwSquareDegreeMap source112 cwSquare112 (by decide)
  let rawCycle := fun c ↦ (cwSquareRaw200011CycleEquiv K q c).toLinearMap
  let coarseCycle := fun c ↦ (cwSquare211CycleEquiv K q c).toLinearMap
  change map coarseCycle (map include211
      (((cwPartitionedTensor K q).positivePower 1).constituent source211)) =
    map (fun c ↦ include112 (cycle.symm c))
      (Tensor.permute cycle
        (((cwPartitionedTensor K q).positivePower 1).constituent source112))
  rw [← cwSquareRaw_200_011_cycle K q]
  change (map coarseCycle ∘ₗ map include211)
      (((cwPartitionedTensor K q).positivePower 1).constituent source211) =
    (map (fun c ↦ include112 (cycle.symm c)) ∘ₗ map rawCycle)
      (((cwPartitionedTensor K q).positivePower 1).constituent source211)
  rw [← map_comp, ← map_comp]
  have hmaps :
      (fun leg ↦ coarseCycle leg ∘ₗ include211 leg) =
        (fun leg ↦ include112 (cycle.symm leg) ∘ₗ rawCycle leg) := by
    funext leg
    apply LinearMap.ext
    intro x
    change cwSquare211CycleEquiv K q leg
        (coarsenedBlockIncludeAt
          (K := K) (V := CWSquareRawBlockSpace K q)
          cwSquareDegreeMap source211 cwSquare211 (by decide) leg x) =
      coarsenedBlockIncludeAt
          (K := K) (V := CWSquareRawBlockSpace K q)
          cwSquareDegreeMap source112 cwSquare112 (by decide) (cycle.symm leg)
        (cwSquareRaw200011CycleEquiv K q leg x)
    cases leg <;>
      simp only [source211, source112,
        cwSquare211CycleEquiv, cwSquareRaw200011CycleEquiv,
        cwSquare211CycleFiberEquiv,
        coarsenedBlockIncludeAt, cwSquareRawAddress, blockAddressProductEquiv,
        cwSquareDegreeMap, cwSquareBlockDegree]
    all_goals
      apply DirectSum.lequivCongrLeft_lof K
      · exact eq_of_heq (cast_heq _ x)
      · apply Subtype.ext
        rfl
  rw [hmaps]

/-- The coarse square constituent at `211` is the cyclic leg permutation of the constituent at
`112`.

Proof sketch: expand both coarse constituents into their four raw source terms.  Each raw product
is the cyclic permutation of its matching `112` product, and the direct-sum fiber equivalence
commutes with every coarsening inclusion.  Linearity then identifies the two four-term sums. -/
theorem cwSquareConstituent_211_cycle
    (K : Type u) [CommRing K] (q : ℕ) :
    map (fun c ↦ (cwSquare211CycleEquiv K q c).toLinearMap)
        ((cwSquarePartitionedTensor K q).constituent cwSquare211) =
      Tensor.permute cycle
        ((cwSquarePartitionedTensor K q).constituent cwSquare112) := by
  rw [cwSquareConstituent_eq_sum_sourceFiber,
    cwSquareConstituent_eq_sum_sourceFiber]
  rw [cwSquareSourceFiber_211, cwSquareSourceFiber_112]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [map_add]
  rw [cwSquareTerm_200_011_cycle,
    cwSquareTerm_011_200_cycle,
    cwSquareTerm_101_110_cycle,
    cwSquareTerm_110_101_cycle]

/-- Relation-level form of `cwSquareConstituent_211_cycle`: the `211` constituent is isomorphic
to the forward cyclic orientation of `112`. -/
theorem cwSquareConstituent_211_isomorphic_cycle
    (K : Type u) [CommRing K] (q : ℕ) :
    Isomorphic
      ((cwSquarePartitionedTensor K q).constituent cwSquare211)
      (Tensor.permute cycle
        ((cwSquarePartitionedTensor K q).constituent cwSquare112)) := by
  refine ⟨cwSquare211CycleEquiv K q, ?_⟩
  simpa [PiTensorProduct.congr] using cwSquareConstituent_211_cycle K q

private theorem cwSquareTerm_020_101_cycle
    (K : Type u) [CommRing K] (q : ℕ) :
    map (fun c ↦ (cwSquare121CycleEquiv K q c).toLinearMap)
        (coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare121 (cwSquareRawAddress cw020 cw101)) =
      Tensor.permute cycle
        (coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare211 (cwSquareRawAddress cw200 cw011)) := by
  apply coarsenedTerm_cycle_121_211 K q _ _ (by decide) (by decide)
    (by intro c; cases c <;> rfl)
    (cwSquareRaw020101CycleEquiv K q)
    (cwSquareRaw_020_101_cycle K q)
  intro c x
  cases c <;> rfl

private theorem cwSquareTerm_101_020_cycle
    (K : Type u) [CommRing K] (q : ℕ) :
    map (fun c ↦ (cwSquare121CycleEquiv K q c).toLinearMap)
        (coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare121 (cwSquareRawAddress cw101 cw020)) =
      Tensor.permute cycle
        (coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare211 (cwSquareRawAddress cw011 cw200)) := by
  apply coarsenedTerm_cycle_121_211 K q _ _ (by decide) (by decide)
    (by intro c; cases c <;> rfl)
    (cwSquareRaw101020CycleEquiv K q)
    (cwSquareRaw_101_020_cycle K q)
  intro c x
  cases c <;> rfl

private theorem cwSquareTerm_110_011_cycle
    (K : Type u) [CommRing K] (q : ℕ) :
    map (fun c ↦ (cwSquare121CycleEquiv K q c).toLinearMap)
        (coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare121 (cwSquareRawAddress cw110 cw011)) =
      Tensor.permute cycle
        (coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare211 (cwSquareRawAddress cw101 cw110)) := by
  apply coarsenedTerm_cycle_121_211 K q _ _ (by decide) (by decide)
    (by intro c; cases c <;> rfl)
    (cwSquareRaw110011CycleEquiv K q)
    (cwSquareRaw_110_011_cycle K q)
  intro c x
  cases c <;> rfl

private theorem cwSquareTerm_011_110_cycle
    (K : Type u) [CommRing K] (q : ℕ) :
    map (fun c ↦ (cwSquare121CycleEquiv K q c).toLinearMap)
        (coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare121 (cwSquareRawAddress cw011 cw110)) =
      Tensor.permute cycle
        (coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare211 (cwSquareRawAddress cw110 cw101)) := by
  apply coarsenedTerm_cycle_121_211 K q _ _ (by decide) (by decide)
    (by intro c; cases c <;> rfl)
    (cwSquareRaw011110CycleEquiv K q)
    (cwSquareRaw_011_110_cycle K q)
  intro c x
  cases c <;> rfl

/-- The coarse square constituent at `121` is the cyclic leg permutation of the constituent at
`211`.

Proof sketch: use the exact four-element source fibers for `121` and `211`, descend each raw cyclic
identity through the degree-sum coarsening map, and sum the four resulting equalities. -/
theorem cwSquareConstituent_121_cycle
    (K : Type u) [CommRing K] (q : ℕ) :
    map (fun c ↦ (cwSquare121CycleEquiv K q c).toLinearMap)
        ((cwSquarePartitionedTensor K q).constituent cwSquare121) =
      Tensor.permute cycle
        ((cwSquarePartitionedTensor K q).constituent cwSquare211) := by
  rw [cwSquareConstituent_eq_sum_sourceFiber,
    cwSquareConstituent_eq_sum_sourceFiber]
  rw [cwSquareSourceFiber_121, cwSquareSourceFiber_211]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [map_add]
  rw [cwSquareTerm_020_101_cycle,
    cwSquareTerm_101_020_cycle,
    cwSquareTerm_110_011_cycle,
    cwSquareTerm_011_110_cycle]

/-- Relation-level form of `cwSquareConstituent_121_cycle`: the `121` constituent is isomorphic
to the forward cyclic orientation of `211`. -/
theorem cwSquareConstituent_121_isomorphic_cycle_211
    (K : Type u) [CommRing K] (q : ℕ) :
    Isomorphic
      ((cwSquarePartitionedTensor K q).constituent cwSquare121)
      (Tensor.permute cycle
        ((cwSquarePartitionedTensor K q).constituent cwSquare211)) := by
  refine ⟨cwSquare121CycleEquiv K q, ?_⟩
  simpa [PiTensorProduct.congr] using cwSquareConstituent_121_cycle K q

/-- The `121` square constituent is isomorphic to the inverse cyclic orientation of `112`.

Proof sketch: first rotate `121` to a cyclic copy of `211`, rotate the `211 ≅ cycle(112)`
isomorphism once more, and use the canonical identification between two forward cycles and one
inverse cycle. -/
theorem cwSquareConstituent_121_isomorphic_cycleSymm
    (K : Type u) [CommRing K] (q : ℕ) :
    Isomorphic
      ((cwSquarePartitionedTensor K q).constituent cwSquare121)
      (Tensor.permute cycle.symm
        ((cwSquarePartitionedTensor K q).constituent cwSquare112)) :=
  (cwSquareConstituent_121_isomorphic_cycle_211 K q).trans
    ((cwSquareConstituent_211_isomorphic_cycle K q).permute_legs cycle |>.trans
      (Tensor.Isomorphic.permute_cycle_cycle
        ((cwSquarePartitionedTensor K q).constituent cwSquare112)))

end AlgebraicComplexity.Examples
