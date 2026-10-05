/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd112Partition
import AlgebraicComplexity.Tensor.CoordinateTensorSingle
import AlgebraicComplexity.Tensor.PartitionedBlockMap

set_option autoImplicit false

/-!
# The raw `(1,1,2)` cell of the CW square, addressed as the `112` C-tensor partition

Layer 4 (`AlgebraicComplexity/Examples/`).  `[duan2023faster]` section 6.3 cuts the level-two leaf
by a per-segment split profile on the `Z` leg, so its `(1,1,2)` region is a **word-type restricted**
sub-object of a power of the raw CW square.  The committed value chain for `T₁₁₂`, by
contrast,
is attached to `cw112PartitionedTensor` — a four-address coordinate presentation with its own
block alphabet `CW112Block`.  Comparing the two therefore needs more than the committed
`cwSquareConstituent_112_restricts_partitioned`
(`Examples/CoppersmithWinograd112Partition.lean`), which identifies the two tensors but says
nothing about *which* raw block goes to *which* `112` block — and it is exactly that
address-level dictionary that a word-type condition has to travel along.

`Examples/DuanWuZhouLevelTwoLeafTauWeight.lean` records this identification as the first of its
open items ("true by construction … but neither is stated as a theorem yet").  This module states
it, at the letter level, as blockwise data rather than as a bare restriction:

* `cw112RawDict` — the dictionary, `(middle, zero) ↦ first`, `(zero, middle) ↦ second` on the
  two
  degree-one legs and `(zero, last) ↦ firstCorner`, `(last, zero) ↦ secondCorner`,
  `(middle, middle) ↦ grid` on the degree-two leg;
* `cw112RawBlockMap` — one linear map per raw block, the coordinate identification
  `(α → K) ⊗ (β → K) ≃ (α × β → K)` followed by the reindexing that reads a `112`
  block
  coordinate as a pair of CW block coordinates, and `0` on the raw blocks outside the cell;
* `map_cw112RawBlockMap_constituent` — each of the four raw constituents is carried exactly onto
  the corresponding `112` constituent;
* `cw112RawCell_restricts_partitioned` — the resulting exact restriction.

The dictionary is what a later module transports a `Z`-word type along; the restriction is the
letter-level composition test for it.

## Why a blockwise map and not a reindexing

`PartitionedTensor.reindex` needs a legwise equivalence of block alphabets.  There is none: the raw
alphabet `PositiveWord CWBlock 1` has nine labels per leg and `CW112Block` has two, two and three.
`Tensor.Restricts.partitionedBlockMap` (`Tensor/PartitionedBlockMap.lean`) is the instrument that
does not ask for one; the five raw labels off the cell are simply sent to zero.

Primary sources: Don Coppersmith and Shmuel Winograd, *Matrix multiplication via arithmetic
progressions*, J. Symbolic Computation 9 (1990), pp. 270--272; Ran Duan, Hongxun Wu and Renfei
Zhou, *Faster Matrix Multiplication via Asymmetric Hashing*, arXiv:2210.10173, `note:T112`.

Exact source lines: `papers/sources/2210.10173/global_value.tex:332-378` (§6.3),
`papers/sources/2210.10173/second_power.tex:234-237` (`note:T112`).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-! ## The block dictionary -/

/-- **The block dictionary of the raw `(1,1,2)` cell.**

On the two degree-one legs the two supported raw pairs are `(middle, zero)` and `(zero, middle)`,
which name the two `112` sides; on the degree-two leg the three supported raw pairs are
`(zero, last)`, `(last, zero)` and `(middle, middle)`, which name the two corners and the grid.
Raw pairs outside the cell are given an arbitrary value; `cw112RawBlockMap` sends them to zero. -/
def cw112RawDict : ∀ c : Leg, PositiveWord CWBlock 1 → CW112Block c
  | .X, (.middle, .zero) => CW112Side.first
  | .X, (.zero, .middle) => CW112Side.second
  | .X, _ => CW112Side.first
  | .Y, (.middle, .zero) => CW112Side.first
  | .Y, (.zero, .middle) => CW112Side.second
  | .Y, _ => CW112Side.first
  | .Z, (.zero, .last) => CW112ZBlock.firstCorner
  | .Z, (.last, .zero) => CW112ZBlock.secondCorner
  | .Z, _ => CW112ZBlock.grid

/-- The `110 ⊗ 002` raw address is the first diagonal `112` address. -/
theorem cw112RawDict_110_002 :
    (fun c ↦ cw112RawDict c (cwSquareRawAddress cw110 cw002 c)) =
      cw112DiagonalFirstAddress := by
  funext c
  cases c <;> rfl

/-- The `002 ⊗ 110` raw address is the second diagonal `112` address. -/
theorem cw112RawDict_002_110 :
    (fun c ↦ cw112RawDict c (cwSquareRawAddress cw002 cw110 c)) =
      cw112DiagonalSecondAddress := by
  funext c
  cases c <;> rfl

/-- The `011 ⊗ 101` raw address is the second cross `112` address. -/
theorem cw112RawDict_011_101 :
    (fun c ↦ cw112RawDict c (cwSquareRawAddress cw011 cw101 c)) =
      cw112CrossSecondAddress := by
  funext c
  cases c <;> rfl

/-- The `101 ⊗ 011` raw address is the first cross `112` address. -/
theorem cw112RawDict_101_011 :
    (fun c ↦ cw112RawDict c (cwSquareRawAddress cw101 cw011 c)) =
      cw112CrossFirstAddress := by
  funext c
  cases c <;> rfl

/-! ## The cell of the raw square -/

/-- The legwise predicate cutting the raw square down to its `(1,1,2)` cell: on every leg the raw
pair has the degree the coarse `(1,1,2)` address prescribes. -/
def cw112RawCellKeep : ∀ _ : Leg, PositiveWord CWBlock 1 → Prop :=
  fun c a ↦ cwSquareDegreeMap c a = cwSquare112 c

instance cw112RawCellKeepDecidable (c : Leg) (a : PositiveWord CWBlock 1) :
    Decidable (cw112RawCellKeep c a) :=
  inferInstanceAs (Decidable (cwSquareDegreeMap c a = cwSquare112 c))

/-- The four raw square addresses lying over the coarse `(1,1,2)` cell. -/
def cw112RawCellSupport : Finset (BlockAddress (fun _ : Leg ↦ PositiveWord CWBlock 1)) :=
  {cwSquareRawAddress cw110 cw002, cwSquareRawAddress cw002 cw110,
    cwSquareRawAddress cw011 cw101, cwSquareRawAddress cw101 cw011}

/-- Membership in the raw square support is membership of both projections in the CW support. -/
theorem mem_cwSquareRawPower_support_iff
    (K : Type u) [CommRing K] (q : ℕ)
    (s : BlockAddress (fun _ : Leg ↦ PositiveWord CWBlock 1)) :
    s ∈ ((cwPartitionedTensor K q).positivePower 1).support ↔
      (fun c ↦ (s c).1) ∈ cwBlockSupport ∧ (fun c ↦ (s c).2) ∈ cwBlockSupport := by
  exact PartitionedTensor.mem_external_support
    ((cwPartitionedTensor K q).positivePower 0) (cwPartitionedTensor K q) s

/-- A pair of supported CW addresses is a supported raw square address. -/
theorem mem_cwSquareRawPower_support_of
    (K : Type u) [CommRing K] (q : ℕ) (left right : CWBlockAddress)
    (hleft : left ∈ cwBlockSupport) (hright : right ∈ cwBlockSupport) :
    cwSquareRawAddress left right ∈ ((cwPartitionedTensor K q).positivePower 1).support :=
  (mem_cwSquareRawPower_support_iff K q _).mpr ⟨hleft, hright⟩

/-- **The cell has exactly the four displayed raw addresses.**

Proof sketch: a supported raw address is a pair of supported CW addresses, thirty-six in all; the
three degree conditions leave four.  The check is finite and runs on the pair of CW addresses, not
on the 729 raw addresses. -/
theorem cw112RawCell_support (K : Type u) [CommRing K] (q : ℕ) :
    (((cwPartitionedTensor K q).positivePower 1).select cw112RawCellKeep).support =
      cw112RawCellSupport := by
  apply Finset.Subset.antisymm
  · intro s hs
    rw [PartitionedTensor.mem_select_support, mem_cwSquareRawPower_support_iff] at hs
    obtain ⟨⟨hleft, hright⟩, hdeg⟩ := hs
    have key : ∀ left right : CWBlockAddress, left ∈ cwBlockSupport → right ∈ cwBlockSupport
      →
        (∀ c, cwSquareDegreeMap c (left c, right c) = cwSquare112 c) →
        cwSquareRawAddress left right ∈ cw112RawCellSupport := by
      intro left right hl hr hd
      fin_cases hl <;> fin_cases hr <;>
        first
          | decide
          | exact absurd (hd .X) (by decide)
          | exact absurd (hd .Y) (by decide)
    exact key (fun c ↦ (s c).1) (fun c ↦ (s c).2) hleft hright hdeg
  · intro s hs
    rw [PartitionedTensor.mem_select_support]
    fin_cases hs <;>
      exact ⟨mem_cwSquareRawPower_support_of K q _ _ (by decide) (by decide),
        fun c ↦ by cases c <;> rfl⟩

/-! ## The blockwise coordinate maps -/

/-- **One linear map per raw block of the cell.**

Each is the coordinate identification of a tensor product of two CW block spaces with the
coordinate space on pairs, followed by the reindexing that reads a `112` block coordinate as such a
pair.  Raw blocks outside the cell are sent to zero. -/
noncomputable def cw112RawBlockMap (K : Type u) [CommRing K] (q : ℕ) :
    ∀ (c : Leg) (a : PositiveWord CWBlock 1),
      CWSquareRawBlockSpace K q c a →ₗ[K] CW112PartitionBlockSpace K q c (cw112RawDict c a)
  | .X, (.middle, .zero) =>
      LinearMap.funLeft K K (fun i : Fin q ↦ ((i : CWBlockIndex q .middle), ((), ()).1)) ∘ₗ
        (coordinateTensorEquiv (K := K)).toLinearMap
  | .X, (.zero, .middle) =>
      LinearMap.funLeft K K (fun i : Fin q ↦ ((((), ()).1 : CWBlockIndex q .zero), i)) ∘ₗ
        (coordinateTensorEquiv (K := K)).toLinearMap
  | .X, _ => 0
  | .Y, (.middle, .zero) =>
      LinearMap.funLeft K K (fun i : Fin q ↦ ((i : CWBlockIndex q .middle), ((), ()).1)) ∘ₗ
        (coordinateTensorEquiv (K := K)).toLinearMap
  | .Y, (.zero, .middle) =>
      LinearMap.funLeft K K (fun i : Fin q ↦ ((((), ()).1 : CWBlockIndex q .zero), i)) ∘ₗ
        (coordinateTensorEquiv (K := K)).toLinearMap
  | .Y, _ => 0
  | .Z, (.zero, .last) =>
      LinearMap.funLeft K K (fun _ : Unit ↦ (((), ()) : Unit × Unit)) ∘ₗ
        (coordinateTensorEquiv (K := K)).toLinearMap
  | .Z, (.last, .zero) =>
      LinearMap.funLeft K K (fun _ : Unit ↦ (((), ()) : Unit × Unit)) ∘ₗ
        (coordinateTensorEquiv (K := K)).toLinearMap
  | .Z, (.middle, .middle) =>
      LinearMap.funLeft K K (fun p : Fin q × Fin q ↦ p) ∘ₗ
        (coordinateTensorEquiv (K := K)).toLinearMap
  | .Z, _ => 0

section BasisValues

variable (K : Type u) [CommRing K] (q : ℕ)

/-- The `(middle, zero)` block map on the `X` leg sends the pure basis tensor to the first side's
basis vector. -/
theorem cw112RawBlockMap_X_middle_zero (i : Fin q) :
    cw112RawBlockMap K q .X (CWBlock.middle, CWBlock.zero)
        (cwBlockBasis K q .middle i ⊗ₜ[K] cwBlockBasis K q .zero ()) =
      cw112PartitionBasis q .X CW112Side.first i :=
  Tensor.funLeft_coordinateTensorEquiv_single_tmul_single (K := K)
    (fun i : Fin q ↦ (i, ((), ()).1)) (fun _ _ hc ↦ congrArg Prod.fst hc) i _ _ rfl

/-- The `(zero, middle)` block map on the `X` leg sends the pure basis tensor to the second side's
basis vector. -/
theorem cw112RawBlockMap_X_zero_middle (i : Fin q) :
    cw112RawBlockMap K q .X (CWBlock.zero, CWBlock.middle)
        (cwBlockBasis K q .zero () ⊗ₜ[K] cwBlockBasis K q .middle i) =
      cw112PartitionBasis q .X CW112Side.second i :=
  Tensor.funLeft_coordinateTensorEquiv_single_tmul_single (K := K)
    (fun i : Fin q ↦ (((), ()).1, i)) (fun _ _ hc ↦ congrArg Prod.snd hc) i _ _ rfl

/-- The `(middle, zero)` block map on the `Y` leg. -/
theorem cw112RawBlockMap_Y_middle_zero (i : Fin q) :
    cw112RawBlockMap K q .Y (CWBlock.middle, CWBlock.zero)
        (cwBlockBasis K q .middle i ⊗ₜ[K] cwBlockBasis K q .zero ()) =
      cw112PartitionBasis q .Y CW112Side.first i :=
  Tensor.funLeft_coordinateTensorEquiv_single_tmul_single (K := K)
    (fun i : Fin q ↦ (i, ((), ()).1)) (fun _ _ hc ↦ congrArg Prod.fst hc) i _ _ rfl

/-- The `(zero, middle)` block map on the `Y` leg. -/
theorem cw112RawBlockMap_Y_zero_middle (i : Fin q) :
    cw112RawBlockMap K q .Y (CWBlock.zero, CWBlock.middle)
        (cwBlockBasis K q .zero () ⊗ₜ[K] cwBlockBasis K q .middle i) =
      cw112PartitionBasis q .Y CW112Side.second i :=
  Tensor.funLeft_coordinateTensorEquiv_single_tmul_single (K := K)
    (fun i : Fin q ↦ (((), ()).1, i)) (fun _ _ hc ↦ congrArg Prod.snd hc) i _ _ rfl

/-- The `(zero, last)` block map on the `Z` leg lands in the first corner. -/
theorem cw112RawBlockMap_Z_zero_last :
    cw112RawBlockMap K q .Z (CWBlock.zero, CWBlock.last)
        (cwBlockBasis K q .zero () ⊗ₜ[K] cwBlockBasis K q .last ()) =
      cw112PartitionBasis q .Z CW112ZBlock.firstCorner () := by
  refine Tensor.funLeft_coordinateTensorEquiv_single_tmul_single (K := K)
    (fun _ ↦ ((), ())) ?_ () _ _ rfl
  intro a b _
  exact Subsingleton.elim a b

/-- The `(last, zero)` block map on the `Z` leg lands in the second corner. -/
theorem cw112RawBlockMap_Z_last_zero :
    cw112RawBlockMap K q .Z (CWBlock.last, CWBlock.zero)
        (cwBlockBasis K q .last () ⊗ₜ[K] cwBlockBasis K q .zero ()) =
      cw112PartitionBasis q .Z CW112ZBlock.secondCorner () := by
  refine Tensor.funLeft_coordinateTensorEquiv_single_tmul_single (K := K)
    (fun _ ↦ ((), ())) ?_ () _ _ rfl
  intro a b _
  exact Subsingleton.elim a b

/-- The `(middle, middle)` block map on the `Z` leg lands in the grid at the pair of indices. -/
theorem cw112RawBlockMap_Z_middle_middle (i k : Fin q) :
    cw112RawBlockMap K q .Z (CWBlock.middle, CWBlock.middle)
        (cwBlockBasis K q .middle i ⊗ₜ[K] cwBlockBasis K q .middle k) =
      cw112PartitionBasis q .Z CW112ZBlock.grid (i, k) :=
  Tensor.funLeft_coordinateTensorEquiv_single_tmul_single (K := K)
    (fun p : Fin q × Fin q ↦ p) (fun _ _ hc ↦ hc) (i, k) _ _ rfl

end BasisValues

/-! ## The four constituents -/

section Constituents

variable (K : Type u) [CommRing K] (q : ℕ)

/-- The `110 ⊗ 002` raw term maps to the corresponding first-diagonal term. -/
theorem map_cw112RawBlockMap_raw110002 (i : Fin q) :
    map (fun c ↦ cw112RawBlockMap K q c (cwSquareRawAddress cw110 cw002 c))
        (cw112Raw110002Term K q i) =
      pure (K := K) (ofLegs
        (cw112PartitionBasis q .X CW112Side.first i)
        (cw112PartitionBasis q .Y CW112Side.first i)
        (cw112PartitionBasis q .Z CW112ZBlock.firstCorner ())) := by
  rw [cw112Raw110002Term, external_pure, Tensor.map_pure]
  refine congrArg (pure (K := K)) (funext fun c ↦ ?_)
  cases c
  · exact cw112RawBlockMap_X_middle_zero K q i
  · exact cw112RawBlockMap_Y_middle_zero K q i
  · exact cw112RawBlockMap_Z_zero_last K q

/-- The `002 ⊗ 110` raw term maps to the corresponding second-diagonal term. -/
theorem map_cw112RawBlockMap_raw002110 (i : Fin q) :
    map (fun c ↦ cw112RawBlockMap K q c (cwSquareRawAddress cw002 cw110 c))
        (cw112Raw002110Term K q i) =
      pure (K := K) (ofLegs
        (cw112PartitionBasis q .X CW112Side.second i)
        (cw112PartitionBasis q .Y CW112Side.second i)
        (cw112PartitionBasis q .Z CW112ZBlock.secondCorner ())) := by
  rw [cw112Raw002110Term, external_pure, Tensor.map_pure]
  refine congrArg (pure (K := K)) (funext fun c ↦ ?_)
  cases c
  · exact cw112RawBlockMap_X_zero_middle K q i
  · exact cw112RawBlockMap_Y_zero_middle K q i
  · exact cw112RawBlockMap_Z_last_zero K q

/-- The `011 ⊗ 101` raw term maps to the corresponding second-cross term. -/
theorem map_cw112RawBlockMap_raw011101 (i k : Fin q) :
    map (fun c ↦ cw112RawBlockMap K q c (cwSquareRawAddress cw011 cw101 c))
        (cw112Raw011101Term K q i k) =
      pure (K := K) (ofLegs
        (cw112PartitionBasis q .X CW112Side.second k)
        (cw112PartitionBasis q .Y CW112Side.first i)
        (cw112PartitionBasis q .Z CW112ZBlock.grid (i, k))) := by
  rw [cw112Raw011101Term, external_pure, Tensor.map_pure]
  refine congrArg (pure (K := K)) (funext fun c ↦ ?_)
  cases c
  · exact cw112RawBlockMap_X_zero_middle K q k
  · exact cw112RawBlockMap_Y_middle_zero K q i
  · exact cw112RawBlockMap_Z_middle_middle K q i k

/-- The `101 ⊗ 011` raw term maps to the corresponding first-cross term. -/
theorem map_cw112RawBlockMap_raw101011 (i k : Fin q) :
    map (fun c ↦ cw112RawBlockMap K q c (cwSquareRawAddress cw101 cw011 c))
        (cw112Raw101011Term K q i k) =
      pure (K := K) (ofLegs
        (cw112PartitionBasis q .X CW112Side.first i)
        (cw112PartitionBasis q .Y CW112Side.second k)
        (cw112PartitionBasis q .Z CW112ZBlock.grid (i, k))) := by
  rw [cw112Raw101011Term, external_pure, Tensor.map_pure]
  refine congrArg (pure (K := K)) (funext fun c ↦ ?_)
  cases c
  · exact cw112RawBlockMap_X_middle_zero K q i
  · exact cw112RawBlockMap_Y_zero_middle K q k
  · exact cw112RawBlockMap_Z_middle_middle K q i k

/-- Two block inclusions at addresses that agree leg by leg embed a pure tensor identically.

The two addresses of interest — the dictionary composite and the named `112` address — are equal
only up to `funext`, but they agree *definitionally at each concrete leg*, which is all an
embedded pure tensor sees. -/
theorem map_blockInclude_pure_congr
    (t t' : BlockAddress CW112Block)
    (v : ∀ c, CW112PartitionBlockSpace K q c (t c))
    (v' : ∀ c, CW112PartitionBlockSpace K q c (t' c))
    (h : ∀ c, HEq (blockInclude (K := K) (V := CW112PartitionBlockSpace K q) t c (v c))
      (blockInclude (K := K) (V := CW112PartitionBlockSpace K q) t' c (v' c))) :
    map (blockInclude (K := K) (V := CW112PartitionBlockSpace K q) t) (pure (K := K) v) =
      map (blockInclude (K := K) (V := CW112PartitionBlockSpace K q) t') (pure (K := K) v') := by
  rw [Tensor.map_pure, Tensor.map_pure]
  exact congrArg (pure (K := K)) (funext fun c ↦ eq_of_heq (h c))

/-- **Every raw constituent of the cell is carried exactly onto its `112` constituent.**

Proof sketch: substitute the named `112` address for the dictionary composite, expand the raw
constituent into its explicit pure terms (committed as `cwSquareRawConstituent_110_002` and its
three companions), map each term by the four term lemmas above, and embed; the two block
inclusions agree at every concrete leg. -/
theorem map_cw112RawBlockMap_constituent
    (s : BlockAddress (fun _ : Leg ↦ PositiveWord CWBlock 1))
    (hs : s ∈ cw112RawCellSupport) (t : BlockAddress CW112Block)
    (ht : (fun c ↦ cw112RawDict c (s c)) = t) :
    map (Tensor.partitionedBlockMap (K := K)
        (V := CWSquareRawBlockSpace K q) (W := CW112PartitionBlockSpace K q)
        cw112RawDict (cw112RawBlockMap K q))
        (map (blockInclude (K := K) (V := CWSquareRawBlockSpace K q) s)
          (((cwPartitionedTensor K q).positivePower 1).constituent s)) =
      map (blockInclude (K := K) (V := CW112PartitionBlockSpace K q) t)
        ((cw112PartitionedTensor K q).constituent t) := by
  rw [map_partitionedBlockMap_block]
  fin_cases hs
  · have hT : t = cw112DiagonalFirstAddress := ht.symm.trans cw112RawDict_110_002
    subst hT
    rw [cwSquareRawConstituent_110_002, map_sum,
      show (cw112PartitionedTensor K q).constituent cw112DiagonalFirstAddress =
        cw112ConstituentOfBlocks K q CW112Side.first CW112Side.first CW112ZBlock.firstCorner from
        cw112PartitionConstituent_ofLegs K q CW112Side.first CW112Side.first
          CW112ZBlock.firstCorner,
      cw112ConstituentOfBlocks, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_cw112RawBlockMap_raw110002]
    exact map_blockInclude_pure_congr K q _ _ _ _ (fun c ↦ by cases c <;> rfl)
  · have hT : t = cw112DiagonalSecondAddress := ht.symm.trans cw112RawDict_002_110
    subst hT
    rw [cwSquareRawConstituent_002_110, map_sum,
      show (cw112PartitionedTensor K q).constituent cw112DiagonalSecondAddress =
        cw112ConstituentOfBlocks K q CW112Side.second CW112Side.second
          CW112ZBlock.secondCorner from cw112PartitionConstituent_ofLegs K q CW112Side.second
          CW112Side.second CW112ZBlock.secondCorner,
      cw112ConstituentOfBlocks, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_cw112RawBlockMap_raw002110]
    exact map_blockInclude_pure_congr K q _ _ _ _ (fun c ↦ by cases c <;> rfl)
  · have hT : t = cw112CrossSecondAddress := ht.symm.trans cw112RawDict_011_101
    subst hT
    rw [cwSquareRawConstituent_011_101, map_sum,
      show (cw112PartitionedTensor K q).constituent cw112CrossSecondAddress =
        cw112ConstituentOfBlocks K q CW112Side.second CW112Side.first CW112ZBlock.grid from
        cw112PartitionConstituent_ofLegs K q CW112Side.second CW112Side.first CW112ZBlock.grid,
      cw112ConstituentOfBlocks, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_cw112RawBlockMap_raw011101]
    exact map_blockInclude_pure_congr K q _ _ _ _ (fun c ↦ by cases c <;> rfl)
  · have hT : t = cw112CrossFirstAddress := ht.symm.trans cw112RawDict_101_011
    subst hT
    rw [cwSquareRawConstituent_101_011, map_sum,
      show (cw112PartitionedTensor K q).constituent cw112CrossFirstAddress =
        cw112ConstituentOfBlocks K q CW112Side.first CW112Side.second CW112ZBlock.grid from
        cw112PartitionConstituent_ofLegs K q CW112Side.first CW112Side.second CW112ZBlock.grid,
      cw112ConstituentOfBlocks, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_cw112RawBlockMap_raw101011]
    exact map_blockInclude_pure_congr K q _ _ _ _ (fun c ↦ by cases c <;> rfl)

end Constituents

/-! ## The letter-level restriction -/

/-- The four `112` addresses are exactly the dictionary images of the four raw cell addresses. -/
theorem cw112BlockSupport_eq_image :
    cw112BlockSupport =
      cw112RawCellSupport.image (fun s ↦ (fun c ↦ cw112RawDict c (s c))) := by
  decide

section Restriction

variable (K : Type u) [CommRing K] (q : ℕ)

/-- The dictionary is injective on the four addresses of the cell. -/
theorem cw112RawDict_injOn :
    ∀ s ∈ cw112RawCellSupport, ∀ t ∈ cw112RawCellSupport,
      (fun c ↦ cw112RawDict c (s c)) = (fun c ↦ cw112RawDict c (t c)) → s = t := by
  intro s hs t ht hst
  fin_cases hs <;> fin_cases ht <;>
    first
      | rfl
      | exact absurd (congrFun hst .X) (by decide)
      | exact absurd (congrFun hst .Y) (by decide)

/-- **The raw `(1,1,2)` cell of the CW square restricts to the `112` C-tensor partition, block by
block.**

This is the letter-level half of the identification recorded as open in
`Examples/DuanWuZhouLevelTwoLeafTauWeight.lean`.  Unlike
`cwSquareConstituent_112_restricts_partitioned`, whose witness is a single coordinate selector on
the coarse cell, the witness here is assembled from the block dictionary, so the same data will
transport a per-letter type condition through a power. -/
theorem cw112RawCell_restricts_partitioned :
    Restricts
      ((((cwPartitionedTensor K q).positivePower 1).select cw112RawCellKeep).realize)
      ((cw112PartitionedTensor K q).realize) := by
  refine Tensor.Restricts.partitionedBlockMap _ _ (cw112RawDict) (cw112RawBlockMap K q)
    ?_ ?_ ?_
  · rw [cw112RawCell_support]
    exact cw112RawDict_injOn
  · rw [cw112RawCell_support, cw112PartitionedTensor_support]
    exact cw112BlockSupport_eq_image
  · rw [cw112RawCell_support]
    intro s hs t ht
    exact map_cw112RawBlockMap_constituent K q s hs t ht

end Restriction

end AlgebraicComplexity.Examples
