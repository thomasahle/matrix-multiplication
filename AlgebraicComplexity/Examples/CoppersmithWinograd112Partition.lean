/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd112
import AlgebraicComplexity.Tensor.Partitioned
import Mathlib.LinearAlgebra.Pi

/-!
# Partitioned C-tensor form of the exceptional CW constituent

This file equips `cw112Tensor` with the block structure used by Coppersmith and Winograd's
C-tensor argument.  X and Y each have two side blocks.  Z has two one-dimensional corner blocks
and one `q × q` grid block.  The four supported addresses are

* `(first, first, firstCorner)`;
* `(second, second, secondCorner)`;
* `(first, second, grid)`; and
* `(second, first, grid)`.

The two diagonal constituents are copies of `⟨1,q,1⟩`; the two cross constituents are copies
of `⟨q,1,q⟩`.  Crucially, the cross constituents share the same Z block.  Ordinary
independent-constituent laser extraction would discard that coupling, while the special `112`
argument retains it as a C-tensor.

This module first defines the typed partition and its tight support.  It then supplies exact
coordinate and matrix-multiplication certificates, so the later word-type and hashing proof can
refer only to this checked partitioned tensor.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped DirectSum

universe u

/-- The three blocks on the Z leg of the `112` C-tensor partition. -/
inductive CW112ZBlock
  | firstCorner
  | secondCorner
  | grid
  deriving DecidableEq

/-- The Z-block type has exactly its three named blocks. -/
instance : Fintype CW112ZBlock where
  elems := {.firstCorner, .secondCorner, .grid}
  complete block := by cases block <;> simp

/-- Block labels on the three legs of the `112` C-tensor partition. -/
abbrev CW112Block : Leg → Type
  | .X => CW112Side
  | .Y => CW112Side
  | .Z => CW112ZBlock

/-- Equality of `112` block labels is decidable on every leg. -/
instance (c : Leg) : DecidableEq (CW112Block c) := by
  cases c <;> simp only [CW112Block] <;> infer_instance

/-- Every `112` block-label set is finite. -/
instance (c : Leg) : Fintype (CW112Block c) := by
  cases c <;> simp only [CW112Block] <;> infer_instance

/-- Coordinate indices inside one block of the C-tensor partition. -/
abbrev CW112PartitionIndex (q : ℕ) : ∀ c, CW112Block c → Type
  | .X, _ => Fin q
  | .Y, _ => Fin q
  | .Z, .firstCorner => Unit
  | .Z, .secondCorner => Unit
  | .Z, .grid => Fin q × Fin q

/-- Equality of coordinates inside a `112` block is decidable. -/
instance (q : ℕ) (c : Leg) (b : CW112Block c) :
    DecidableEq (CW112PartitionIndex q c b) := by
  cases c with
  | X => exact inferInstance
  | Y => exact inferInstance
  | Z => cases b <;> exact inferInstance

/-- Each block of the `112` partition has a finite coordinate set. -/
instance (q : ℕ) (c : Leg) (b : CW112Block c) :
    Fintype (CW112PartitionIndex q c b) := by
  cases c with
  | X => exact inferInstance
  | Y => exact inferInstance
  | Z => cases b <;> exact inferInstance

/-- Coordinate vector space carried by one block of the partition. -/
abbrev CW112PartitionBlockSpace (K : Type u) (q : ℕ)
    (c : Leg) (b : CW112Block c) :=
  CW112PartitionIndex q c b → K

/-- Standard basis vector inside one block of the partition. -/
noncomputable def cw112PartitionBasis {K : Type u} [Zero K] [One K]
    (q : ℕ) (c : Leg) (b : CW112Block c)
    (i : CW112PartitionIndex q c b) : CW112PartitionBlockSpace K q c b :=
  Pi.single i 1

/-- Construct a block address from explicit X, Y, and Z labels. -/
abbrev cw112BlockAddress (x y : CW112Side) (z : CW112ZBlock) :
    BlockAddress CW112Block :=
  ofLegs x y z

abbrev cw112DiagonalFirstAddress : BlockAddress CW112Block :=
  cw112BlockAddress .first .first .firstCorner

abbrev cw112DiagonalSecondAddress : BlockAddress CW112Block :=
  cw112BlockAddress .second .second .secondCorner

abbrev cw112CrossFirstAddress : BlockAddress CW112Block :=
  cw112BlockAddress .first .second .grid

abbrev cw112CrossSecondAddress : BlockAddress CW112Block :=
  cw112BlockAddress .second .first .grid

/-- The four addresses appearing in the C-tensor partition. -/
def cw112BlockSupport : Finset (BlockAddress CW112Block) :=
  {cw112DiagonalFirstAddress, cw112DiagonalSecondAddress,
    cw112CrossFirstAddress, cw112CrossSecondAddress}

/-- There are exactly four supported block addresses. -/
@[simp] theorem card_cw112BlockSupport : cw112BlockSupport.card = 4 := by
  decide

/-- The four-address support is tight: X and Y sides receive weights `0,1`, while the three Z
blocks receive weights `2,0,1`, so every supported address has total weight two. -/
theorem cw112BlockSupport_isTight : IsTightSupport cw112BlockSupport := by
  let weight : ∀ c, CW112Block c → ℤ
    | .X, .first => 0
    | .X, .second => 1
    | .Y, .first => 0
    | .Y, .second => 1
    | .Z, .firstCorner => 2
    | .Z, .secondCorner => 0
    | .Z, .grid => 1
  refine ⟨weight, ?_, 2, ?_⟩
  · intro c
    cases c <;> intro a b h <;> cases a <;> cases b <;> simp_all [weight]
  · intro address haddress
    simp only [cw112BlockSupport, Finset.mem_insert, Finset.mem_singleton] at haddress
    rcases haddress with rfl | rfl | rfl | rfl <;>
      decide

/-- The sigma of block-local coordinate sets is the readable ambient `CW112Index` on each leg. -/
def cw112PartitionIndexEquiv (q : ℕ) : ∀ c,
    (Σ b : CW112Block c, CW112PartitionIndex q c b) ≃ CW112Index q c
  | .X =>
      { toFun := fun x ↦ (x.1, x.2)
        invFun := fun x ↦ ⟨x.1, x.2⟩
        left_inv := by rintro ⟨side, i⟩; rfl
        right_inv := by rintro ⟨side, i⟩; rfl }
  | .Y =>
      { toFun := fun x ↦ (x.1, x.2)
        invFun := fun x ↦ ⟨x.1, x.2⟩
        left_inv := by rintro ⟨side, i⟩; rfl
        right_inv := by rintro ⟨side, i⟩; rfl }
  | .Z =>
      { toFun := fun x ↦
          match x with
          | ⟨.firstCorner, _⟩ => .inl .first
          | ⟨.secondCorner, _⟩ => .inl .second
          | ⟨.grid, ij⟩ => .inr ij
        invFun := fun x ↦
          match x with
          | .inl .first => ⟨.firstCorner, ()⟩
          | .inl .second => ⟨.secondCorner, ()⟩
          | .inr ij => ⟨.grid, ij⟩
        left_inv := by
          rintro ⟨block, i⟩
          cases block <;> try { cases i } <;> rfl
        right_inv := by
          intro x
          rcases x with side | ij
          · cases side <;> rfl
          · rfl }

/-- Currying a block-local standard basis vector gives the corresponding standard basis vector
on the sigma of block and local coordinate. -/
theorem sigma_uncurry_single_cw112PartitionBasis
    (K : Type u) [AddMonoidWithOne K]
    (q : ℕ) (c : Leg) (b : CW112Block c)
    (i : CW112PartitionIndex q c b) :
    Sigma.uncurry
        (Pi.single b (cw112PartitionBasis q c b i) :
          ∀ b : CW112Block c, CW112PartitionIndex q c b → K) =
      (Pi.single ⟨b, i⟩ (1 : K) :
        (Σ b : CW112Block c, CW112PartitionIndex q c b) → K) := by
  funext x
  rcases x with ⟨d, j⟩
  by_cases h : d = b
  · subst d
    simp [Sigma.uncurry, Pi.single_apply, cw112PartitionBasis]
  · have hs :
        (⟨d, j⟩ : Σ d : CW112Block c, CW112PartitionIndex q c d) ≠ ⟨b, i⟩ := by
      intro hs
      exact h (congrArg Sigma.fst hs)
    simp [Sigma.uncurry, h, hs]

section Partition

variable (K : Type u) [CommRing K]
variable (q : ℕ)

/-- Canonical equivalence from the direct sum of C-tensor blocks on one leg to the readable
ambient coordinate space. -/
noncomputable def cw112PartitionSpaceEquiv (c : Leg) :
    PartitionedSpace K (CW112PartitionBlockSpace K q) c ≃ₗ[K]
      CW112Space K q c :=
  DirectSum.linearEquivFunOnFintype K (CW112Block c)
      (fun b ↦ CW112PartitionIndex q c b → K) ≪≫ₗ
    (LinearEquiv.piCurry K
      (fun b : CW112Block c ↦ fun _ : CW112PartitionIndex q c b ↦ K)).symm ≪≫ₗ
    LinearEquiv.piCongrLeft K (fun _ : CW112Index q c ↦ K)
      (cw112PartitionIndexEquiv q c)

/-- Legwise linear-map form of `cw112PartitionSpaceEquiv`. -/
noncomputable def cw112PartitionMap : ∀ c,
    PartitionedSpace K (CW112PartitionBlockSpace K q) c →ₗ[K]
      CW112Space K q c :=
  fun c ↦ (cw112PartitionSpaceEquiv K q c).toLinearMap

/-- A block-local basis vector maps to the ambient basis vector named by its block and local
coordinate. -/
@[simp] theorem cw112PartitionSpaceEquiv_lof_basis
    (c : Leg) (b : CW112Block c) (i : CW112PartitionIndex q c b) :
    cw112PartitionSpaceEquiv K q c
        (DirectSum.lof K (CW112Block c)
          (fun b ↦ CW112PartitionIndex q c b → K) b
          (cw112PartitionBasis q c b i)) =
      cw112Basis q c (cw112PartitionIndexEquiv q c ⟨b, i⟩) := by
  simp only [cw112PartitionSpaceEquiv, LinearEquiv.trans_apply,
    DirectSum.linearEquivFunOnFintype_lof, LinearEquiv.piCurry_symm_apply,
    cw112Basis]
  rw [sigma_uncurry_single_cw112PartitionBasis]
  ext j
  change
    (Equiv.piCongrLeft (fun _ : CW112Index q c ↦ K)
      (cw112PartitionIndexEquiv q c))
        (Pi.single ⟨b, i⟩ (1 : K) :
          (Σ b : CW112Block c, CW112PartitionIndex q c b) → K) j =
      (Pi.single (cw112PartitionIndexEquiv q c ⟨b, i⟩) (1 : K) :
        CW112Index q c → K) j
  rw [Equiv.piCongrLeft_apply]
  simp only [eq_rec_constant]
  by_cases h : j = cw112PartitionIndexEquiv q c ⟨b, i⟩
  · subst j
    simp
  · have h' : (cw112PartitionIndexEquiv q c).symm j ≠ ⟨b, i⟩ := by
      intro h'
      apply h
      rw [← h', Equiv.apply_symm_apply]
    simp [h, h']

/-- Mapping a block-local basis vector through its block inclusion and the canonical ambient
equivalence yields the corresponding readable basis vector. -/
@[simp] theorem cw112PartitionMap_blockInclude_basis
    (s : BlockAddress CW112Block) (c : Leg)
    (i : CW112PartitionIndex q c (s c)) :
    (cw112PartitionMap K q c ∘ₗ
        blockInclude (K := K) (V := CW112PartitionBlockSpace K q) s c)
        (cw112PartitionBasis q c (s c) i) =
      cw112Basis q c (cw112PartitionIndexEquiv q c ⟨s c, i⟩) := by
  exact cw112PartitionSpaceEquiv_lof_basis K q c (s c) i

/-- Three-coordinate form of the embedded-basis computation rule. -/
theorem map_embedded_cw112PartitionBasis_pure_ofLegs
    (x y : CW112Side) (z : CW112ZBlock)
    (ix : CW112PartitionIndex q .X x)
    (iy : CW112PartitionIndex q .Y y)
    (iz : CW112PartitionIndex q .Z z) :
    map (fun c ↦ cw112PartitionMap K q c ∘ₗ
        blockInclude (K := K) (V := CW112PartitionBlockSpace K q)
          (cw112BlockAddress x y z) c)
        (pure (K := K) (ofLegs
          (cw112PartitionBasis q .X x ix)
          (cw112PartitionBasis q .Y y iy)
          (cw112PartitionBasis q .Z z iz))) =
      pure (K := K) (ofLegs
        (cw112Basis q .X (cw112PartitionIndexEquiv q .X ⟨x, ix⟩))
        (cw112Basis q .Y (cw112PartitionIndexEquiv q .Y ⟨y, iy⟩))
        (cw112Basis q .Z (cw112PartitionIndexEquiv q .Z ⟨z, iz⟩))) := by
  rw [Tensor.map_pure]
  congr 1
  funext c
  cases c
  · exact cw112PartitionMap_blockInclude_basis K q
      (cw112BlockAddress x y z) .X ix
  · exact cw112PartitionMap_blockInclude_basis K q
      (cw112BlockAddress x y z) .Y iy
  · exact cw112PartitionMap_blockInclude_basis K q
      (cw112BlockAddress x y z) .Z iz

/-- Constituent associated to three explicit block labels, with zero away from the four-address
support. -/
noncomputable def cw112ConstituentOfBlocks
    (x y : CW112Side) (z : CW112ZBlock) :
    Tensor3 K (fun c ↦ CW112PartitionBlockSpace K q c
      (cw112BlockAddress x y z c)) :=
  match x, y, z with
  | .first, .first, .firstCorner =>
      ∑ i : Fin q, pure (K := K) (ofLegs
        (cw112PartitionBasis q .X .first i)
        (cw112PartitionBasis q .Y .first i)
        (cw112PartitionBasis q .Z .firstCorner ()))
  | .second, .second, .secondCorner =>
      ∑ i : Fin q, pure (K := K) (ofLegs
        (cw112PartitionBasis q .X .second i)
        (cw112PartitionBasis q .Y .second i)
        (cw112PartitionBasis q .Z .secondCorner ()))
  | .first, .second, .grid =>
      ∑ i : Fin q, ∑ k : Fin q, pure (K := K) (ofLegs
        (cw112PartitionBasis q .X .first i)
        (cw112PartitionBasis q .Y .second k)
        (cw112PartitionBasis q .Z .grid (i, k)))
  | .second, .first, .grid =>
      ∑ i : Fin q, ∑ k : Fin q, pure (K := K) (ofLegs
        (cw112PartitionBasis q .X .second k)
        (cw112PartitionBasis q .Y .first i)
        (cw112PartitionBasis q .Z .grid (i, k)))
  | _, _, _ => 0

/-- Transport a constituent along equality of its three block labels. -/
noncomputable def cw112TransportConstituent
    {s t : BlockAddress CW112Block} (h : s = t)
    (T : Tensor3 K (fun c ↦ CW112PartitionBlockSpace K q c (s c))) :
    Tensor3 K (fun c ↦ CW112PartitionBlockSpace K q c (t c)) := by
  subst t
  exact T

/-- Transport along reflexive address equality leaves a constituent unchanged. -/
@[simp] theorem cw112TransportConstituent_self
    {s : BlockAddress CW112Block} (h : s = s)
    (T : Tensor3 K (fun c ↦ CW112PartitionBlockSpace K q c (s c))) :
    cw112TransportConstituent K q h T = T := by
  have hh : h = rfl := Subsingleton.elim _ _
  rw [hh]
  rfl

/-- Constituent function on every address, obtained from the explicit X/Y/Z labels. -/
noncomputable def cw112PartitionConstituent (s : BlockAddress CW112Block) :
    Tensor3 K (fun c ↦ CW112PartitionBlockSpace K q c (s c)) :=
  cw112TransportConstituent K q (ofLegs_eta s)
    (cw112ConstituentOfBlocks K q (s .X) (s .Y) (s .Z))

/-- On an address constructed with `ofLegs`, the constituent function reduces to the displayed
three-block definition. -/
@[simp] theorem cw112PartitionConstituent_ofLegs
    (x y : CW112Side) (z : CW112ZBlock) :
    cw112PartitionConstituent K q (cw112BlockAddress x y z) =
      cw112ConstituentOfBlocks K q x y z := by
  unfold cw112PartitionConstituent
  change cw112TransportConstituent K q
    (_ : cw112BlockAddress x y z = cw112BlockAddress x y z) _ = _
  apply cw112TransportConstituent_self

/-- The typed four-constituent C-tensor partition. -/
noncomputable def cw112PartitionedTensor :
    PartitionedTensor (K := K) (A := CW112Block)
      (CW112PartitionBlockSpace K q) where
  support := cw112BlockSupport
  constituent := cw112PartitionConstituent K q

/-- The partitioned tensor has exactly the four named C-tensor addresses. -/
@[simp] theorem cw112PartitionedTensor_support :
    (cw112PartitionedTensor K q).support = cw112BlockSupport :=
  rfl

/-- The four constituents written directly in the readable ambient coordinate spaces. -/
noncomputable def cw112AmbientBlockConstituent
    (s : BlockAddress CW112Block) : Tensor3 K (CW112Space K q) :=
  match s .X, s .Y, s .Z with
  | .first, .first, .firstCorner => cw112DiagonalFirst K q
  | .second, .second, .secondCorner => cw112DiagonalSecond K q
  | .first, .second, .grid => cw112CrossFirst K q
  | .second, .first, .grid => cw112CrossSecond K q
  | _, _, _ => 0

/-- The embedded first diagonal constituent maps to `cw112DiagonalFirst`. -/
theorem map_cw112DiagonalFirstConstituent :
    map (fun c ↦ cw112PartitionMap K q c ∘ₗ
        blockInclude (K := K) (V := CW112PartitionBlockSpace K q)
          cw112DiagonalFirstAddress c)
        (cw112ConstituentOfBlocks K q .first .first .firstCorner) =
      cw112DiagonalFirst K q := by
  simp only [cw112ConstituentOfBlocks, cw112DiagonalFirst, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simpa [cw112Pure, cw112PartitionIndexEquiv] using
    map_embedded_cw112PartitionBasis_pure_ofLegs K q
      .first .first .firstCorner i i ()

/-- The embedded second diagonal constituent maps to `cw112DiagonalSecond`. -/
theorem map_cw112DiagonalSecondConstituent :
    map (fun c ↦ cw112PartitionMap K q c ∘ₗ
        blockInclude (K := K) (V := CW112PartitionBlockSpace K q)
          cw112DiagonalSecondAddress c)
        (cw112ConstituentOfBlocks K q .second .second .secondCorner) =
      cw112DiagonalSecond K q := by
  simp only [cw112ConstituentOfBlocks, cw112DiagonalSecond, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simpa [cw112Pure, cw112PartitionIndexEquiv] using
    map_embedded_cw112PartitionBasis_pure_ofLegs K q
      .second .second .secondCorner i i ()

/-- The embedded first cross constituent maps to `cw112CrossFirst`. -/
theorem map_cw112CrossFirstConstituent :
    map (fun c ↦ cw112PartitionMap K q c ∘ₗ
        blockInclude (K := K) (V := CW112PartitionBlockSpace K q)
          cw112CrossFirstAddress c)
        (cw112ConstituentOfBlocks K q .first .second .grid) =
      cw112CrossFirst K q := by
  simp only [cw112ConstituentOfBlocks, cw112CrossFirst, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  simpa [cw112Pure, cw112PartitionIndexEquiv] using
    map_embedded_cw112PartitionBasis_pure_ofLegs K q
      .first .second .grid i k (i, k)

/-- The embedded second cross constituent maps to `cw112CrossSecond`. -/
theorem map_cw112CrossSecondConstituent :
    map (fun c ↦ cw112PartitionMap K q c ∘ₗ
        blockInclude (K := K) (V := CW112PartitionBlockSpace K q)
          cw112CrossSecondAddress c)
        (cw112ConstituentOfBlocks K q .second .first .grid) =
      cw112CrossSecond K q := by
  simp only [cw112ConstituentOfBlocks, cw112CrossSecond, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  simpa [cw112Pure, cw112PartitionIndexEquiv] using
    map_embedded_cw112PartitionBasis_pure_ofLegs K q
      .second .first .grid k i (i, k)

/-- Every supported typed constituent maps to its corresponding ambient four-family branch. -/
theorem map_cw112SupportedConstituent
    (s : BlockAddress CW112Block) (hs : s ∈ cw112BlockSupport) :
    map (fun c ↦ cw112PartitionMap K q c ∘ₗ
        blockInclude (K := K) (V := CW112PartitionBlockSpace K q) s c)
        (cw112PartitionConstituent K q s) =
      cw112AmbientBlockConstituent K q s := by
  simp only [cw112BlockSupport, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · simpa [cw112AmbientBlockConstituent] using
      map_cw112DiagonalFirstConstituent K q
  · simpa [cw112AmbientBlockConstituent] using
      map_cw112DiagonalSecondConstituent K q
  · simpa [cw112AmbientBlockConstituent] using
      map_cw112CrossFirstConstituent K q
  · simpa [cw112AmbientBlockConstituent] using
      map_cw112CrossSecondConstituent K q

/-- The four ambient branches sum to the normal-form tensor. -/
theorem sum_cw112AmbientBlockConstituent :
    ∑ s ∈ cw112BlockSupport, cw112AmbientBlockConstituent K q s =
      cw112Tensor K q := by
  rw [show cw112BlockSupport =
      {cw112DiagonalFirstAddress, cw112DiagonalSecondAddress,
        cw112CrossFirstAddress, cw112CrossSecondAddress} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [cw112AmbientBlockConstituent, cw112DiagonalFirstAddress,
    cw112DiagonalSecondAddress, cw112CrossFirstAddress, cw112CrossSecondAddress,
    cw112BlockAddress, ofLegs]
  unfold cw112Tensor
  abel

/-- Applying the canonical block-space equivalences to the partitioned realization recovers the
explicit four-family normal form. -/
theorem map_cw112PartitionMap_realize :
    map (cw112PartitionMap K q) (cw112PartitionedTensor K q).realize =
      cw112Tensor K q := by
  classical
  unfold PartitionedTensor.realize realizePartition
  rw [map_sum]
  calc
    (∑ s ∈ cw112BlockSupport,
        map (cw112PartitionMap K q)
          (map (blockInclude (K := K) (V := CW112PartitionBlockSpace K q) s)
            ((cw112PartitionedTensor K q).constituent s))) =
        ∑ s ∈ cw112BlockSupport, cw112AmbientBlockConstituent K q s := by
          apply Finset.sum_congr rfl
          intro s hs
          calc
            map (cw112PartitionMap K q)
                (map (blockInclude (K := K) (V := CW112PartitionBlockSpace K q) s)
                  ((cw112PartitionedTensor K q).constituent s)) =
                map (fun c ↦ cw112PartitionMap K q c ∘ₗ
                    blockInclude (K := K) (V := CW112PartitionBlockSpace K q) s c)
                  ((cw112PartitionedTensor K q).constituent s) := by
                    rw [map_comp]
                    rfl
            _ = cw112AmbientBlockConstituent K q s := by
              change map (fun c ↦ cw112PartitionMap K q c ∘ₗ
                  blockInclude (K := K) (V := CW112PartitionBlockSpace K q) s c)
                (cw112PartitionConstituent K q s) = _
              exact map_cw112SupportedConstituent K q s hs
    _ = cw112Tensor K q := sum_cw112AmbientBlockConstituent K q

/-- The typed C-tensor partition realizes the explicit `cw112Tensor` up to canonical coordinate
equivalences. -/
theorem cw112PartitionedTensor_isomorphic :
    Isomorphic (cw112PartitionedTensor K q).realize (cw112Tensor K q) := by
  refine ⟨fun c ↦ cw112PartitionSpaceEquiv K q c, ?_⟩
  change map (cw112PartitionMap K q) (cw112PartitionedTensor K q).realize =
    cw112Tensor K q
  exact map_cw112PartitionMap_realize K q

/-- The original coarse `112` constituent restricts to the typed C-tensor partition used in the
asymptotic value proof. -/
theorem cwSquareConstituent_112_restricts_partitioned :
    Restricts
      ((cwSquarePartitionedTensor K q).constituent cwSquare112)
      (cw112PartitionedTensor K q).realize :=
  (cwSquareConstituent_112_restricts K q).trans
    (cw112PartitionedTensor_isomorphic K q).symm.restricts

/-! ## Matrix-multiplication certificates for the four constituents -/

/-- Coordinate selector identifying the first diagonal constituent with `⟨1,q,1⟩`. -/
def cw112DiagonalFirstMMIndex : ∀ c,
    MMIndex 1 q 1 c →
      CW112PartitionIndex q c (cw112DiagonalFirstAddress c)
  | .X, a => a.2
  | .Y, a => a.1
  | .Z, _ => ()

/-- Leg maps for the first diagonal constituent's matrix-multiplication certificate. -/
def cw112DiagonalFirstMMMap : ∀ c,
    CW112PartitionBlockSpace K q c (cw112DiagonalFirstAddress c) →ₗ[K]
      MMSpace K 1 q 1 c :=
  fun c ↦ LinearMap.funLeft K K (cw112DiagonalFirstMMIndex q c)

/-- Coordinate selector identifying the second diagonal constituent with `⟨1,q,1⟩`. -/
def cw112DiagonalSecondMMIndex : ∀ c,
    MMIndex 1 q 1 c →
      CW112PartitionIndex q c (cw112DiagonalSecondAddress c)
  | .X, a => a.2
  | .Y, a => a.1
  | .Z, _ => ()

/-- Leg maps for the second diagonal constituent's matrix-multiplication certificate. -/
def cw112DiagonalSecondMMMap : ∀ c,
    CW112PartitionBlockSpace K q c (cw112DiagonalSecondAddress c) →ₗ[K]
      MMSpace K 1 q 1 c :=
  fun c ↦ LinearMap.funLeft K K (cw112DiagonalSecondMMIndex q c)

/-- A pure term in the first diagonal block maps to the corresponding term of `⟨1,q,1⟩`. -/
theorem map_cw112DiagonalFirstMMMap_pure (i : Fin q) :
    map (cw112DiagonalFirstMMMap K q)
        (pure (K := K) (ofLegs
          (cw112PartitionBasis q .X .first i)
          (cw112PartitionBasis q .Y .first i)
          (cw112PartitionBasis q .Z .firstCorner ()))) =
      pure (K := K) (mmTerm (K := K) 1 q 1 0 i 0) := by
  rw [Tensor.map_pure]
  congr 1
  funext c
  cases c <;> ext a
  · rcases a with ⟨h, j⟩
    fin_cases h
    simp [cw112DiagonalFirstMMMap, cw112DiagonalFirstMMIndex,
      cw112PartitionBasis, mmTerm, ofLegs, Pi.single_apply]
  · rcases a with ⟨j, h⟩
    fin_cases h
    simp [cw112DiagonalFirstMMMap, cw112DiagonalFirstMMIndex,
      cw112PartitionBasis, mmTerm, ofLegs, Pi.single_apply]
  · rcases a with ⟨h₁, h₂⟩
    fin_cases h₁
    fin_cases h₂
    change (Pi.single () (1 : K) : Unit → K) () = 1
    simp

/-- A pure term in the second diagonal block maps to the corresponding term of `⟨1,q,1⟩`. -/
theorem map_cw112DiagonalSecondMMMap_pure (i : Fin q) :
    map (cw112DiagonalSecondMMMap K q)
        (pure (K := K) (ofLegs
          (cw112PartitionBasis q .X .second i)
          (cw112PartitionBasis q .Y .second i)
          (cw112PartitionBasis q .Z .secondCorner ()))) =
      pure (K := K) (mmTerm (K := K) 1 q 1 0 i 0) := by
  rw [Tensor.map_pure]
  congr 1
  funext c
  cases c <;> ext a
  · rcases a with ⟨h, j⟩
    fin_cases h
    simp [cw112DiagonalSecondMMMap, cw112DiagonalSecondMMIndex,
      cw112PartitionBasis, mmTerm, ofLegs, Pi.single_apply]
  · rcases a with ⟨j, h⟩
    fin_cases h
    simp [cw112DiagonalSecondMMMap, cw112DiagonalSecondMMIndex,
      cw112PartitionBasis, mmTerm, ofLegs, Pi.single_apply]
  · rcases a with ⟨h₁, h₂⟩
    fin_cases h₁
    fin_cases h₂
    change (Pi.single () (1 : K) : Unit → K) () = 1
    simp

/-- Either diagonal constituent is the coordinate tensor `⟨1,q,1⟩`; this theorem records the
first copy. -/
theorem cw112DiagonalFirstConstituent_restricts :
    Restricts
      (cw112ConstituentOfBlocks K q .first .first .firstCorner)
      (matrixMultiplication (K := K) 1 q 1) := by
  refine ⟨cw112DiagonalFirstMMMap K q, ?_⟩
  rw [show cw112ConstituentOfBlocks K q .first .first .firstCorner =
      ∑ i : Fin q, pure (K := K) (ofLegs
        (cw112PartitionBasis q .X .first i)
        (cw112PartitionBasis q .Y .first i)
        (cw112PartitionBasis q .Z .firstCorner ())) from rfl]
  rw [map_sum]
  simp_rw [map_cw112DiagonalFirstMMMap_pure]
  exact (matrixMultiplication_outer_one q).symm

/-- The second diagonal constituent is another coordinate copy of `⟨1,q,1⟩`. -/
theorem cw112DiagonalSecondConstituent_restricts :
    Restricts
      (cw112ConstituentOfBlocks K q .second .second .secondCorner)
      (matrixMultiplication (K := K) 1 q 1) := by
  refine ⟨cw112DiagonalSecondMMMap K q, ?_⟩
  rw [show cw112ConstituentOfBlocks K q .second .second .secondCorner =
      ∑ i : Fin q, pure (K := K) (ofLegs
        (cw112PartitionBasis q .X .second i)
        (cw112PartitionBasis q .Y .second i)
        (cw112PartitionBasis q .Z .secondCorner ())) from rfl]
  rw [map_sum]
  simp_rw [map_cw112DiagonalSecondMMMap_pure]
  exact (matrixMultiplication_outer_one q).symm

/-- Coordinate selector identifying the first cross constituent with `⟨q,1,q⟩`.  The Z-grid
coordinate is transposed because matrix-multiplication Z coordinates are ordered `(k,i)`. -/
def cw112CrossFirstMMIndex : ∀ c,
    MMIndex q 1 q c →
      CW112PartitionIndex q c (cw112CrossFirstAddress c)
  | .X, a => a.1
  | .Y, a => a.2
  | .Z, a => (a.2, a.1)

/-- Leg maps for the first cross constituent's matrix-multiplication certificate. -/
def cw112CrossFirstMMMap : ∀ c,
    CW112PartitionBlockSpace K q c (cw112CrossFirstAddress c) →ₗ[K]
      MMSpace K q 1 q c :=
  fun c ↦ LinearMap.funLeft K K (cw112CrossFirstMMIndex q c)

/-- Coordinate selector identifying the second cross constituent with `⟨q,1,q⟩`.  In this
orientation the native Z-grid order already agrees with the matrix-multiplication convention. -/
def cw112CrossSecondMMIndex : ∀ c,
    MMIndex q 1 q c →
      CW112PartitionIndex q c (cw112CrossSecondAddress c)
  | .X, a => a.1
  | .Y, a => a.2
  | .Z, a => a

/-- Leg maps for the second cross constituent's matrix-multiplication certificate. -/
def cw112CrossSecondMMMap : ∀ c,
    CW112PartitionBlockSpace K q c (cw112CrossSecondAddress c) →ₗ[K]
      MMSpace K q 1 q c :=
  fun c ↦ LinearMap.funLeft K K (cw112CrossSecondMMIndex q c)

/-- One pure term of the first cross constituent maps to the corresponding summand of
`⟨q,1,q⟩`. -/
theorem map_cw112CrossFirstMMMap_pure (i k : Fin q) :
    map (cw112CrossFirstMMMap K q)
        (pure (K := K) (ofLegs
          (cw112PartitionBasis q .X .first i)
          (cw112PartitionBasis q .Y .second k)
          (cw112PartitionBasis q .Z .grid (i, k)))) =
      pure (K := K) (mmTerm (K := K) q 1 q i 0 k) := by
  rw [Tensor.map_pure]
  congr 1
  funext c
  cases c with
  | X =>
      ext a
      rcases a with ⟨j, h⟩
      fin_cases h
      simp [cw112CrossFirstMMMap, cw112CrossFirstMMIndex,
        cw112PartitionBasis, mmTerm, ofLegs, Pi.single_apply]
  | Y =>
      ext a
      rcases a with ⟨h, l⟩
      fin_cases h
      simp [cw112CrossFirstMMMap, cw112CrossFirstMMIndex,
        cw112PartitionBasis, mmTerm, ofLegs, Pi.single_apply]
  | Z =>
      ext a
      rcases a with ⟨l, j⟩
      change LinearMap.funLeft K K (cw112CrossFirstMMIndex q .Z)
          (Pi.single (i, k) (1 : K) :
            CW112PartitionIndex q .Z (cw112CrossFirstAddress .Z) → K) (l, j) =
        (Pi.single (k, i) (1 : K) : (Fin q × Fin q) → K) (l, j)
      rw [LinearMap.funLeft_apply]
      rw [show cw112CrossFirstMMIndex q .Z (l, j) = (j, l) from rfl]
      by_cases hj : j = i
      · subst j
        by_cases hl : l = k
        · subst l
          calc
            (Pi.single (i, k) (1 : K) :
                CW112PartitionIndex q .Z (cw112CrossFirstAddress .Z) → K) (i, k) = 1 :=
              Pi.single_eq_same
                (M := fun _ : CW112PartitionIndex q .Z
                  (cw112CrossFirstAddress .Z) ↦ K) (i, k) (1 : K)
            _ = (Pi.single (k, i) (1 : K) : (Fin q × Fin q) → K) (k, i) :=
              (Pi.single_eq_same (M := fun _ : Fin q × Fin q ↦ K)
                (k, i) (1 : K)).symm
        · have hpair : (i, l) ≠ (i, k) := by
            intro h
            exact hl (congrArg (fun a : Fin q × Fin q ↦ a.2) h)
          have hpair' : (l, i) ≠ (k, i) := by
            intro h
            exact hl (congrArg (fun a : Fin q × Fin q ↦ a.1) h)
          calc
            (Pi.single (i, k) (1 : K) :
                CW112PartitionIndex q .Z (cw112CrossFirstAddress .Z) → K) (i, l) = 0 :=
              Pi.single_eq_of_ne
                (M := fun _ : CW112PartitionIndex q .Z
                  (cw112CrossFirstAddress .Z) ↦ K) hpair (1 : K)
            _ = (Pi.single (k, i) (1 : K) : (Fin q × Fin q) → K) (l, i) :=
              (Pi.single_eq_of_ne (M := fun _ : Fin q × Fin q ↦ K)
                hpair' (1 : K)).symm
      · have hpair : (j, l) ≠ (i, k) := by
          intro h
          exact hj (congrArg (fun a : Fin q × Fin q ↦ a.1) h)
        have hpair' : (l, j) ≠ (k, i) := by
          intro h
          exact hj (congrArg (fun a : Fin q × Fin q ↦ a.2) h)
        calc
          (Pi.single (i, k) (1 : K) :
              CW112PartitionIndex q .Z (cw112CrossFirstAddress .Z) → K) (j, l) = 0 :=
            Pi.single_eq_of_ne
              (M := fun _ : CW112PartitionIndex q .Z
                (cw112CrossFirstAddress .Z) ↦ K) hpair (1 : K)
          _ = (Pi.single (k, i) (1 : K) : (Fin q × Fin q) → K) (l, j) :=
            (Pi.single_eq_of_ne (M := fun _ : Fin q × Fin q ↦ K)
              hpair' (1 : K)).symm

/-- One pure term of the second cross constituent maps to the corresponding summand of
`⟨q,1,q⟩`, with the two outer summation indices exchanged. -/
theorem map_cw112CrossSecondMMMap_pure (i k : Fin q) :
    map (cw112CrossSecondMMMap K q)
        (pure (K := K) (ofLegs
          (cw112PartitionBasis q .X .second k)
          (cw112PartitionBasis q .Y .first i)
          (cw112PartitionBasis q .Z .grid (i, k)))) =
      pure (K := K) (mmTerm (K := K) q 1 q k 0 i) := by
  rw [Tensor.map_pure]
  congr 1
  funext c
  cases c with
  | X =>
      ext a
      rcases a with ⟨j, h⟩
      fin_cases h
      simp [cw112CrossSecondMMMap, cw112CrossSecondMMIndex,
        cw112PartitionBasis, mmTerm, ofLegs, Pi.single_apply]
  | Y =>
      ext a
      rcases a with ⟨h, l⟩
      fin_cases h
      simp [cw112CrossSecondMMMap, cw112CrossSecondMMIndex,
        cw112PartitionBasis, mmTerm, ofLegs, Pi.single_apply]
  | Z =>
      ext a
      rcases a with ⟨l, j⟩
      change LinearMap.funLeft K K (cw112CrossSecondMMIndex q .Z)
          (Pi.single (i, k) (1 : K) :
            CW112PartitionIndex q .Z (cw112CrossSecondAddress .Z) → K) (l, j) =
        (Pi.single (i, k) (1 : K) : (Fin q × Fin q) → K) (l, j)
      rw [LinearMap.funLeft_apply]
      rfl

/-- The first cross constituent exactly restricts to `⟨q,1,q⟩`. -/
theorem cw112CrossFirstConstituent_restricts :
    Restricts
      (cw112ConstituentOfBlocks K q .first .second .grid)
      (matrixMultiplication (K := K) q 1 q) := by
  refine ⟨cw112CrossFirstMMMap K q, ?_⟩
  rw [show cw112ConstituentOfBlocks K q .first .second .grid =
      ∑ i : Fin q, ∑ k : Fin q, pure (K := K) (ofLegs
        (cw112PartitionBasis q .X .first i)
        (cw112PartitionBasis q .Y .second k)
        (cw112PartitionBasis q .Z .grid (i, k))) from rfl]
  rw [map_sum]
  simp_rw [map_sum, map_cw112CrossFirstMMMap_pure]
  exact matrixMultiplication_middle_one q q |>.symm

/-- The second cross constituent exactly restricts to `⟨q,1,q⟩`. -/
theorem cw112CrossSecondConstituent_restricts :
    Restricts
      (cw112ConstituentOfBlocks K q .second .first .grid)
      (matrixMultiplication (K := K) q 1 q) := by
  refine ⟨cw112CrossSecondMMMap K q, ?_⟩
  rw [show cw112ConstituentOfBlocks K q .second .first .grid =
      ∑ i : Fin q, ∑ k : Fin q, pure (K := K) (ofLegs
        (cw112PartitionBasis q .X .second k)
        (cw112PartitionBasis q .Y .first i)
        (cw112PartitionBasis q .Z .grid (i, k))) from rfl]
  rw [map_sum]
  simp_rw [map_sum, map_cw112CrossSecondMMMap_pure]
  calc
    (∑ i : Fin q, ∑ k : Fin q,
        pure (K := K) (mmTerm (K := K) q 1 q k 0 i)) =
        ∑ k : Fin q, ∑ i : Fin q,
          pure (K := K) (mmTerm (K := K) q 1 q k 0 i) :=
      Finset.sum_comm
    _ = matrixMultiplication (K := K) q 1 q :=
      (matrixMultiplication_middle_one q q).symm

end Partition

end AlgebraicComplexity.Examples
