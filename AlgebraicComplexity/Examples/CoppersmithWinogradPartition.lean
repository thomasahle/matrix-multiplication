/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd
import AlgebraicComplexity.Examples.CoppersmithWinogradPartitionCore
import AlgebraicComplexity.Examples.CoppersmithWinogradSupport
import AlgebraicComplexity.MatrixMultiplication.PartitionedValue
import Mathlib.LinearAlgebra.Pi

/-!
# A typed partitioned realization of the Coppersmith--Winograd tensor

The zero and final CW coordinate blocks are one-dimensional, while the middle block has dimension
`q`.  This file realizes those three spaces as an actual direct-sum partition and proves that its
canonical direct sum is linearly equivalent to the original coordinate space of `CW_q`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped DirectSum

universe u

section

variable (K : Type u) [CommRing K]
variable (q : ℕ)

/-- The same six constituents written in the original unpartitioned CW coordinate space. -/
noncomputable def cwAmbientBlockConstituent (s : CWBlockAddress) :
    Tensor3 K (CWSpace K q) :=
  match s .X, s .Y, s .Z with
  | .last, .zero, .zero =>
      pure (K := K) (ofLegs (cwLastVector K q) (cwZeroVector K q) (cwZeroVector K q))
  | .zero, .last, .zero =>
      pure (K := K) (ofLegs (cwZeroVector K q) (cwLastVector K q) (cwZeroVector K q))
  | .zero, .zero, .last =>
      pure (K := K) (ofLegs (cwZeroVector K q) (cwZeroVector K q) (cwLastVector K q))
  | .zero, .middle, .middle =>
      ∑ i : Fin q, pure (K := K) (ofLegs
        (cwZeroVector K q) (cwMiddleVector K q i) (cwMiddleVector K q i))
  | .middle, .zero, .middle =>
      ∑ i : Fin q, pure (K := K) (ofLegs
        (cwMiddleVector K q i) (cwZeroVector K q) (cwMiddleVector K q i))
  | .middle, .middle, .zero =>
      ∑ i : Fin q, pure (K := K) (ofLegs
        (cwMiddleVector K q i) (cwMiddleVector K q i) (cwZeroVector K q))
  | _, _, _ => 0

@[simp] theorem cwPartitionMap_blockInclude_basis
    (s : CWBlockAddress) (c : Leg) (i : CWBlockIndex q (s c)) :
    (cwPartitionMap K q c ∘ₗ
        blockInclude (K := K) (V := CWPartitionBlockSpace K q) s c)
        (cwBlockBasis K q (s c) i) =
      cwBasis K q (cwBlockIndexEquiv q ⟨s c, i⟩) := by
  exact cwPartitionSpaceEquiv_lof_basis K q c (s c) i

/-- Map a pure tensor of block-coordinate vectors through the embedded partition. -/
theorem map_embedded_cwBlockBasis_pure
    (s : CWBlockAddress) (i : ∀ c, CWBlockIndex q (s c)) :
    map (fun c ↦ cwPartitionMap K q c ∘ₗ
        blockInclude (K := K) (V := CWPartitionBlockSpace K q) s c)
        (pure (K := K) (fun c ↦ cwBlockBasis K q (s c) (i c))) =
      pure (K := K) (fun c ↦ cwBasis K q
        (cwBlockIndexEquiv q ⟨s c, i c⟩)) := by
  rw [Tensor.map_pure]
  congr 1
  funext c
  exact cwPartitionMap_blockInclude_basis K q s c (i c)

/-- Three-coordinate spelling of `map_embedded_cwBlockBasis_pure`. -/
theorem map_embedded_cwBlockBasis_pure_ofLegs
    (x y z : CWBlock)
    (ix : CWBlockIndex q x) (iy : CWBlockIndex q y) (iz : CWBlockIndex q z) :
    map (fun c ↦ cwPartitionMap K q c ∘ₗ
        blockInclude (K := K) (V := CWPartitionBlockSpace K q)
          (ofLegs x y z) c)
        (pure (K := K) (ofLegs
          (cwBlockBasis K q x ix) (cwBlockBasis K q y iy)
          (cwBlockBasis K q z iz))) =
      pure (K := K) (ofLegs
        (cwBasis K q (cwBlockIndexEquiv q ⟨x, ix⟩))
        (cwBasis K q (cwBlockIndexEquiv q ⟨y, iy⟩))
        (cwBasis K q (cwBlockIndexEquiv q ⟨z, iz⟩))) := by
  rw [Tensor.map_pure]
  congr 1
  funext c
  cases c
  · exact cwPartitionMap_blockInclude_basis K q (ofLegs x y z) .X ix
  · exact cwPartitionMap_blockInclude_basis K q (ofLegs x y z) .Y iy
  · exact cwPartitionMap_blockInclude_basis K q (ofLegs x y z) .Z iz

theorem map_cw200Constituent :
    map (fun c ↦ cwPartitionMap K q c ∘ₗ
        blockInclude (K := K) (V := CWPartitionBlockSpace K q) cw200 c)
        (cwConstituentOfBlocks K q .last .zero .zero) =
      cwAmbientBlockConstituent K q cw200 := by
  simpa [cwConstituentOfBlocks, cwAmbientBlockConstituent, cw200, cwBlockAddress,
    cwBlockIndexEquiv] using
    map_embedded_cwBlockBasis_pure_ofLegs K q .last .zero .zero () () ()

theorem map_cw020Constituent :
    map (fun c ↦ cwPartitionMap K q c ∘ₗ
        blockInclude (K := K) (V := CWPartitionBlockSpace K q) cw020 c)
        (cwConstituentOfBlocks K q .zero .last .zero) =
      cwAmbientBlockConstituent K q cw020 := by
  simpa [cwConstituentOfBlocks, cwAmbientBlockConstituent, cw020, cwBlockAddress,
    cwBlockIndexEquiv] using
    map_embedded_cwBlockBasis_pure_ofLegs K q .zero .last .zero () () ()

theorem map_cw002Constituent :
    map (fun c ↦ cwPartitionMap K q c ∘ₗ
        blockInclude (K := K) (V := CWPartitionBlockSpace K q) cw002 c)
        (cwConstituentOfBlocks K q .zero .zero .last) =
      cwAmbientBlockConstituent K q cw002 := by
  simpa [cwConstituentOfBlocks, cwAmbientBlockConstituent, cw002, cwBlockAddress,
    cwBlockIndexEquiv] using
    map_embedded_cwBlockBasis_pure_ofLegs K q .zero .zero .last () () ()

theorem map_cw011Constituent :
    map (fun c ↦ cwPartitionMap K q c ∘ₗ
        blockInclude (K := K) (V := CWPartitionBlockSpace K q) cw011 c)
        (cwConstituentOfBlocks K q .zero .middle .middle) =
      cwAmbientBlockConstituent K q cw011 := by
  simp only [cwConstituentOfBlocks, cwAmbientBlockConstituent, cw011, cwBlockAddress]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simpa [cwBlockIndexEquiv] using
    map_embedded_cwBlockBasis_pure_ofLegs K q .zero .middle .middle () i i

theorem map_cw101Constituent :
    map (fun c ↦ cwPartitionMap K q c ∘ₗ
        blockInclude (K := K) (V := CWPartitionBlockSpace K q) cw101 c)
        (cwConstituentOfBlocks K q .middle .zero .middle) =
      cwAmbientBlockConstituent K q cw101 := by
  simp only [cwConstituentOfBlocks, cwAmbientBlockConstituent, cw101, cwBlockAddress]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simpa [cwBlockIndexEquiv] using
    map_embedded_cwBlockBasis_pure_ofLegs K q .middle .zero .middle i () i

theorem map_cw110Constituent :
    map (fun c ↦ cwPartitionMap K q c ∘ₗ
        blockInclude (K := K) (V := CWPartitionBlockSpace K q) cw110 c)
        (cwConstituentOfBlocks K q .middle .middle .zero) =
      cwAmbientBlockConstituent K q cw110 := by
  simp only [cwConstituentOfBlocks, cwAmbientBlockConstituent, cw110, cwBlockAddress]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simpa [cwBlockIndexEquiv] using
    map_embedded_cwBlockBasis_pure_ofLegs K q .middle .middle .zero i i ()

/-- Mapping one embedded typed constituent through the canonical block equivalence gives its
coordinate-space constituent. -/
theorem map_cwSupportedConstituent (s : cwBlockSupport) :
    map (fun c ↦ cwPartitionMap K q c ∘ₗ
        blockInclude (K := K) (V := CWPartitionBlockSpace K q) s.1 c)
        (cwSupportedConstituent K q s) =
      cwAmbientBlockConstituent K q s.1 := by
  rcases s with ⟨s, hs⟩
  simp only [cwBlockSupport, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [cwSupportedConstituent, cwPartitionConstituent_ofLegs] using
      map_cw200Constituent K q
  · simpa only [cwSupportedConstituent, cwPartitionConstituent_ofLegs] using
      map_cw020Constituent K q
  · simpa only [cwSupportedConstituent, cwPartitionConstituent_ofLegs] using
      map_cw002Constituent K q
  · simpa only [cwSupportedConstituent, cwPartitionConstituent_ofLegs] using
      map_cw011Constituent K q
  · simpa only [cwSupportedConstituent, cwPartitionConstituent_ofLegs] using
      map_cw101Constituent K q
  · simpa only [cwSupportedConstituent, cwPartitionConstituent_ofLegs] using
      map_cw110Constituent K q

/-- The six coordinate-space constituents sum to the full CW tensor. -/
theorem sum_cwAmbientBlockConstituent :
    ∑ s ∈ cwBlockSupport, cwAmbientBlockConstituent K q s =
      coppersmithWinograd K q := by
  rw [sum_cwBlockSupport]
  simp only [cwAmbientBlockConstituent, cw200, cw020, cw002, cw011, cw101, cw110,
    cwBlockAddress, ofLegs, coppersmithWinograd, cwMiddle, cwCorners]
  simp_rw [Finset.sum_add_distrib]
  abel

/-- Applying the canonical block-space equivalences to the realization recovers `CW_q`. -/
theorem map_cwPartitionMap_realize :
    map (cwPartitionMap K q) (cwPartitionedTensor K q).realize =
      coppersmithWinograd K q := by
  classical
  unfold PartitionedTensor.realize realizePartition
  rw [map_sum]
  calc
    (∑ s ∈ cwBlockSupport,
        map (cwPartitionMap K q)
          (map (blockInclude (K := K) (V := CWPartitionBlockSpace K q) s)
            ((cwPartitionedTensor K q).constituent s))) =
        ∑ s ∈ cwBlockSupport, cwAmbientBlockConstituent K q s := by
          apply Finset.sum_congr rfl
          intro s hs
          calc
            map (cwPartitionMap K q)
                (map (blockInclude (K := K) (V := CWPartitionBlockSpace K q) s)
                  ((cwPartitionedTensor K q).constituent s)) =
                map (fun c ↦ cwPartitionMap K q c ∘ₗ
                    blockInclude (K := K) (V := CWPartitionBlockSpace K q) s c)
                  ((cwPartitionedTensor K q).constituent s) := by
                    rw [map_comp]
                    rfl
            _ = cwAmbientBlockConstituent K q s := by
              change map (fun c ↦ cwPartitionMap K q c ∘ₗ
                  blockInclude (K := K) (V := CWPartitionBlockSpace K q) s c)
                (cwPartitionConstituent K q s) = cwAmbientBlockConstituent K q s
              simpa only [cwSupportedConstituent] using
                map_cwSupportedConstituent K q ⟨s, hs⟩
    _ = coppersmithWinograd K q := sum_cwAmbientBlockConstituent K q

/-- The typed partitioned realization is the original CW tensor up to canonical changes of
basis on its three legs. -/
theorem cwPartitionedTensor_isomorphic :
    Isomorphic (cwPartitionedTensor K q).realize (coppersmithWinograd K q) := by
  refine ⟨fun c ↦ cwPartitionSpaceEquiv K q c, ?_⟩
  change map (cwPartitionMap K q) (cwPartitionedTensor K q).realize =
    coppersmithWinograd K q
  exact map_cwPartitionMap_realize K q

/-- The typed partition does not change the constructive border rank of `CW_q`. -/
theorem cwPartitionedTensor_borderRank :
    borderRank (cwPartitionedTensor K q).realize =
      borderRank (coppersmithWinograd K q) :=
  borderRank_isomorphic (cwPartitionedTensor_isomorphic K q)

/-! ## Matrix-multiplication certificates for the six constituents -/

/-- Choose the distinguished ambient CW coordinate represented by a corner block. -/
def cwCornerCoordinate (q : ℕ) : CWBlock → CWIndex q
  | .zero => .zero
  | .middle => .zero
  | .last => .last

/-- Project the three selected ambient corner coordinates to the three singleton spaces of
`⟨1,1,1⟩`. -/
def cwCornerIndex (s : CWBlockAddress) : ∀ c, MMIndex 1 1 1 c → CWIndex q :=
  fun c _ ↦ cwCornerCoordinate q (s c)

def cwCornerMap (s : CWBlockAddress) : ∀ c,
    CWSpace K q c →ₗ[K] MMSpace K 1 1 1 c :=
  fun c ↦ LinearMap.funLeft K K (cwCornerIndex q s c)

/-- Each of the three corner constituents `cw200`, `cw020`, `cw002` is carried by its corner
map onto the one-dimensional matrix-multiplication tensor `⟨1,1,1⟩`.

Source and target: the source is the ambient constituent `cwAmbientBlockConstituent K q s` of
`CW_q`, and the result of applying `cwCornerMap K q s` to it is exactly `⟨1,1,1⟩`.

Proof sketch: all three corners have singleton blocks on every leg, so after `fin_cases` on the
six matrix indices — each ranging over `Fin 1` — both sides are a single standard coordinate,
and the same `simp` set evaluates the corner projection and the `CW` basis on it.  The three
addresses therefore share one script, and the named corollaries below select a case. -/
theorem map_cwCornerMap_corner (s : CWBlockAddress)
    (hs : s ∈ ({cw200, cw020, cw002} : Finset CWBlockAddress)) :
    map (cwCornerMap K q s) (cwAmbientBlockConstituent K q s) =
      matrixMultiplication (K := K) 1 1 1 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl <;>
    (apply standardCoordinate_ext
     intro a
     unfold cwCornerMap
     rw [standardCoordinateEquiv_map_funLeft]
     rcases hX : a .X with ⟨i, j⟩
     rcases hY : a .Y with ⟨j', k⟩
     rcases hZ : a .Z with ⟨k', i'⟩
     fin_cases i
     fin_cases j
     fin_cases j'
     fin_cases k
     fin_cases k'
     fin_cases i'
     simp [cwAmbientBlockConstituent, cwCornerIndex, cwCornerCoordinate,
       cwBasis, hX, hY, hZ, standardCoordinateEquiv_pure,
       prod_leg, matrixMultiplication, mmTermOfTriple, mmTerm, Fintype.sum_prod_type])

/-- The `cw200` corner constituent maps onto `⟨1,1,1⟩`. -/
theorem map_cwCornerMap_cw200 :
    map (cwCornerMap K q cw200) (cwAmbientBlockConstituent K q cw200) =
      matrixMultiplication (K := K) 1 1 1 :=
  map_cwCornerMap_corner K q cw200 (by decide)

/-- The `cw020` corner constituent maps onto `⟨1,1,1⟩`. -/
theorem map_cwCornerMap_cw020 :
    map (cwCornerMap K q cw020) (cwAmbientBlockConstituent K q cw020) =
      matrixMultiplication (K := K) 1 1 1 :=
  map_cwCornerMap_corner K q cw020 (by decide)

/-- The `cw002` corner constituent maps onto `⟨1,1,1⟩`. -/
theorem map_cwCornerMap_cw002 :
    map (cwCornerMap K q cw002) (cwAmbientBlockConstituent K q cw002) =
      matrixMultiplication (K := K) 1 1 1 :=
  map_cwCornerMap_corner K q cw002 (by decide)

theorem map_cw011Map_cwAmbientBlock :
    map (cw011Map K q) (cwAmbientBlockConstituent K q cw011) =
      matrixMultiplication (K := K) 1 1 q := by
  apply standardCoordinate_ext
  intro a
  unfold cw011Map
  rw [standardCoordinateEquiv_map_funLeft]
  rcases hX : a .X with ⟨i, j⟩
  rcases hY : a .Y with ⟨j', k⟩
  rcases hZ : a .Z with ⟨k', i'⟩
  fin_cases i
  fin_cases j
  fin_cases j'
  fin_cases i'
  simp [cwAmbientBlockConstituent, cw011Index, cwBasis, Pi.single_apply,
    hX, hY, hZ, standardCoordinateEquiv_pure, prod_leg,
    matrixMultiplication, mmTermOfTriple, mmTerm, Fintype.sum_prod_type]

theorem map_cw101Map_cwAmbientBlock :
    map (cw101Map K q) (cwAmbientBlockConstituent K q cw101) =
      matrixMultiplication (K := K) q 1 1 := by
  apply standardCoordinate_ext
  intro a
  unfold cw101Map
  rw [standardCoordinateEquiv_map_funLeft]
  rcases hX : a .X with ⟨i, j⟩
  rcases hY : a .Y with ⟨j', k⟩
  rcases hZ : a .Z with ⟨k', i'⟩
  fin_cases j
  fin_cases j'
  fin_cases k
  fin_cases k'
  simp [cwAmbientBlockConstituent, cw101Index, cwBasis, Pi.single_apply,
    hX, hY, hZ, standardCoordinateEquiv_pure, prod_leg,
    matrixMultiplication, mmTermOfTriple, mmTerm, Fintype.sum_prod_type]

theorem map_cw110Map_cwAmbientBlock :
    map (cw110Map K q) (cwAmbientBlockConstituent K q cw110) =
      matrixMultiplication (K := K) 1 q 1 := by
  apply standardCoordinate_ext
  intro a
  unfold cw110Map
  rw [standardCoordinateEquiv_map_funLeft]
  rcases hX : a .X with ⟨i, j⟩
  rcases hY : a .Y with ⟨j', k⟩
  rcases hZ : a .Z with ⟨k', i'⟩
  fin_cases i
  fin_cases k
  fin_cases k'
  fin_cases i'
  simp [cwAmbientBlockConstituent, cw110Index, cwBasis, Pi.single_apply,
    hX, hY, hZ, standardCoordinateEquiv_pure, prod_leg,
    matrixMultiplication, mmTermOfTriple, mmTerm, Fintype.sum_prod_type]

theorem cw200Constituent_restricts :
    Restricts (cwConstituentOfBlocks K q .last .zero .zero)
      (matrixMultiplication (K := K) 1 1 1) := by
  refine Restricts.trans (W := CWSpace K q)
    (S := cwAmbientBlockConstituent K q cw200) ?_ ?_
  · exact ⟨fun c ↦ cwPartitionMap K q c ∘ₗ
        blockInclude (K := K) (V := CWPartitionBlockSpace K q) cw200 c,
      map_cw200Constituent K q⟩
  · exact ⟨cwCornerMap K q cw200, map_cwCornerMap_cw200 K q⟩

theorem cw020Constituent_restricts :
    Restricts (cwConstituentOfBlocks K q .zero .last .zero)
      (matrixMultiplication (K := K) 1 1 1) := by
  refine Restricts.trans (W := CWSpace K q)
    (S := cwAmbientBlockConstituent K q cw020) ?_ ?_
  · exact ⟨fun c ↦ cwPartitionMap K q c ∘ₗ
        blockInclude (K := K) (V := CWPartitionBlockSpace K q) cw020 c,
      map_cw020Constituent K q⟩
  · exact ⟨cwCornerMap K q cw020, map_cwCornerMap_cw020 K q⟩

theorem cw002Constituent_restricts :
    Restricts (cwConstituentOfBlocks K q .zero .zero .last)
      (matrixMultiplication (K := K) 1 1 1) := by
  refine Restricts.trans (W := CWSpace K q)
    (S := cwAmbientBlockConstituent K q cw002) ?_ ?_
  · exact ⟨fun c ↦ cwPartitionMap K q c ∘ₗ
        blockInclude (K := K) (V := CWPartitionBlockSpace K q) cw002 c,
      map_cw002Constituent K q⟩
  · exact ⟨cwCornerMap K q cw002, map_cwCornerMap_cw002 K q⟩

theorem cw011Constituent_restricts :
    Restricts (cwConstituentOfBlocks K q .zero .middle .middle)
      (matrixMultiplication (K := K) 1 1 q) := by
  refine Restricts.trans (W := CWSpace K q)
    (S := cwAmbientBlockConstituent K q cw011) ?_ ?_
  · exact ⟨fun c ↦ cwPartitionMap K q c ∘ₗ
        blockInclude (K := K) (V := CWPartitionBlockSpace K q) cw011 c,
      map_cw011Constituent K q⟩
  · exact ⟨cw011Map K q, map_cw011Map_cwAmbientBlock K q⟩

theorem cw101Constituent_restricts :
    Restricts (cwConstituentOfBlocks K q .middle .zero .middle)
      (matrixMultiplication (K := K) q 1 1) := by
  refine Restricts.trans (W := CWSpace K q)
    (S := cwAmbientBlockConstituent K q cw101) ?_ ?_
  · exact ⟨fun c ↦ cwPartitionMap K q c ∘ₗ
        blockInclude (K := K) (V := CWPartitionBlockSpace K q) cw101 c,
      map_cw101Constituent K q⟩
  · exact ⟨cw101Map K q, map_cw101Map_cwAmbientBlock K q⟩

theorem cw110Constituent_restricts :
    Restricts (cwConstituentOfBlocks K q .middle .middle .zero)
      (matrixMultiplication (K := K) 1 q 1) := by
  refine Restricts.trans (W := CWSpace K q)
    (S := cwAmbientBlockConstituent K q cw110) ?_ ?_
  · exact ⟨fun c ↦ cwPartitionMap K q c ∘ₗ
        blockInclude (K := K) (V := CWPartitionBlockSpace K q) cw110 c,
      map_cw110Constituent K q⟩
  · exact ⟨cw110Map K q, map_cw110Map_cwAmbientBlock K q⟩

/-- Matrix dimensions attached to each standard CW block address.  The fallback value is harmless:
the certificate below only evaluates this function on the six supported addresses. -/
abbrev cwConstituentDimensions (s : CWBlockAddress) : ℕ × ℕ × ℕ :=
  match s .X, s .Y, s .Z with
  | .zero, .middle, .middle => (1, 1, q)
  | .middle, .zero, .middle => (q, 1, 1)
  | .middle, .middle, .zero => (1, q, 1)
  | _, _, _ => (1, 1, 1)

@[simp] theorem cwConstituentDimensions_cw200 :
    cwConstituentDimensions q cw200 = (1, 1, 1) := by
  simp [cwConstituentDimensions, cw200, cwBlockAddress]

@[simp] theorem cwConstituentDimensions_cw020 :
    cwConstituentDimensions q cw020 = (1, 1, 1) := by
  simp [cwConstituentDimensions, cw020, cwBlockAddress]

@[simp] theorem cwConstituentDimensions_cw002 :
    cwConstituentDimensions q cw002 = (1, 1, 1) := by
  simp [cwConstituentDimensions, cw002, cwBlockAddress]

@[simp] theorem cwConstituentDimensions_cw011 :
    cwConstituentDimensions q cw011 = (1, 1, q) := by
  simp [cwConstituentDimensions, cw011, cwBlockAddress]

@[simp] theorem cwConstituentDimensions_cw101 :
    cwConstituentDimensions q cw101 = (q, 1, 1) := by
  simp [cwConstituentDimensions, cw101, cwBlockAddress]

@[simp] theorem cwConstituentDimensions_cw110 :
    cwConstituentDimensions q cw110 = (1, q, 1) := by
  simp [cwConstituentDimensions, cw110, cwBlockAddress]

theorem cwConstituentDimensions_pos (hq : 0 < q) (s : cwBlockSupport) :
    0 < (cwConstituentDimensions q s.1).1 ∧
      0 < (cwConstituentDimensions q s.1).2.1 ∧
      0 < (cwConstituentDimensions q s.1).2.2 := by
  rcases s with ⟨s, hs⟩
  simp only [cwBlockSupport, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [cwConstituentDimensions, hq]

/-- Every supported ambient constituent exactly restricts to the matrix-multiplication tensor
recorded by `cwConstituentDimensions`. -/
theorem cwAmbientBlockConstituent_restricts (s : CWBlockAddress)
    (hs : s ∈ cwBlockSupport) :
    Restricts (cwAmbientBlockConstituent K q s)
      (matrixMultiplication (K := K)
        (cwConstituentDimensions q s).1
        (cwConstituentDimensions q s).2.1
        (cwConstituentDimensions q s).2.2) := by
  simp only [cwBlockSupport, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [cwConstituentDimensions_cw200]
    exact (show Restricts (cwAmbientBlockConstituent K q cw200)
          (matrixMultiplication (K := K) 1 1 1) from
        ⟨cwCornerMap K q cw200, map_cwCornerMap_cw200 K q⟩)
  · rw [cwConstituentDimensions_cw020]
    exact (show Restricts (cwAmbientBlockConstituent K q cw020)
          (matrixMultiplication (K := K) 1 1 1) from
        ⟨cwCornerMap K q cw020, map_cwCornerMap_cw020 K q⟩)
  · rw [cwConstituentDimensions_cw002]
    exact (show Restricts (cwAmbientBlockConstituent K q cw002)
          (matrixMultiplication (K := K) 1 1 1) from
        ⟨cwCornerMap K q cw002, map_cwCornerMap_cw002 K q⟩)
  · rw [cwConstituentDimensions_cw011]
    exact (show Restricts (cwAmbientBlockConstituent K q cw011)
          (matrixMultiplication (K := K) 1 1 q) from
        ⟨cw011Map K q, map_cw011Map_cwAmbientBlock K q⟩)
  · rw [cwConstituentDimensions_cw101]
    exact (show Restricts (cwAmbientBlockConstituent K q cw101)
          (matrixMultiplication (K := K) q 1 1) from
        ⟨cw101Map K q, map_cw101Map_cwAmbientBlock K q⟩)
  · rw [cwConstituentDimensions_cw110]
    exact (show Restricts (cwAmbientBlockConstituent K q cw110)
          (matrixMultiplication (K := K) 1 q 1) from
        ⟨cw110Map K q, map_cw110Map_cwAmbientBlock K q⟩)

/-- Every typed supported constituent has the expected exact matrix-multiplication restriction. -/
theorem cwSupportedConstituent_restricts (s : cwBlockSupport) :
    Restricts (cwSupportedConstituent K q s)
      (matrixMultiplication (K := K)
        (cwConstituentDimensions q s.1).1
        (cwConstituentDimensions q s.1).2.1
        (cwConstituentDimensions q s.1).2.2) := by
  refine Restricts.trans (W := CWSpace K q)
    (S := cwAmbientBlockConstituent K q s.1) ?_ ?_
  · exact ⟨fun c ↦ cwPartitionMap K q c ∘ₗ
        blockInclude (K := K) (V := CWPartitionBlockSpace K q) s.1 c,
      map_cwSupportedConstituent K q s⟩
  · exact cwAmbientBlockConstituent_restricts K q s.1 s.2

/-- End-to-end matrix-multiplication certificate for the typed six-block partition of `CW_q`. -/
noncomputable def cwPartitionedMMCertificate (hq : 0 < q) :
    PartitionedMMCertificate K (cwPartitionedTensor K q) where
  m s := (cwConstituentDimensions q s.1).1
  n s := (cwConstituentDimensions q s.1).2.1
  p s := (cwConstituentDimensions q s.1).2.2
  m_pos s := (cwConstituentDimensions_pos q hq s).1
  n_pos s := (cwConstituentDimensions_pos q hq s).2.1
  p_pos s := (cwConstituentDimensions_pos q hq s).2.2
  degenerates s := by
    apply PolynomialDegenerates.of_restricts
    change Restricts (cwSupportedConstituent K q s)
      (matrixMultiplication (K := K)
        (cwConstituentDimensions q s.1).1
        (cwConstituentDimensions q s.1).2.1
        (cwConstituentDimensions q s.1).2.2)
    exact cwSupportedConstituent_restricts K q s

/-- The certificate's generic volume function is the support-level CW volume used by the entropy
calculation. -/
theorem cwPartitionedMMCertificate_volume (hq : 0 < q) (s : cwBlockSupport) :
    (cwPartitionedMMCertificate K q hq).volume s = cwConstituentVolume q s := by
  rcases s with ⟨s, hs⟩
  simp only [cwBlockSupport, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [PartitionedMMCertificate.volume, cwPartitionedMMCertificate,
      cwConstituentDimensions, cwConstituentVolume]

/-- The certificate-backed laser value is definitionally the support-level value used in the
classical CW entropy calculation. -/
theorem cwPartitionedLaserLogValue_eq_supportLaserLogValue (hq : 0 < q)
    (mu : SupportDistribution cwBlockSupport) :
    partitionedLaserLogValue K (cwPartitionedMMCertificate K q hq) mu =
      supportLaserLogValue K mu (cwConstituentVolume q) := by
  unfold partitionedLaserLogValue
  congr 1
  funext s
  exact cwPartitionedMMCertificate_volume K q hq s

/-- The typed realization inherits the classical `q + 2` border-rank certificate. -/
theorem cwPartitionedTensor_borderRankLE :
    BorderRankLE (q + 2) (cwPartitionedTensor K q).realize :=
  (BorderRankLE.isomorphic (cwPartitionedTensor_isomorphic K q)).mpr
    (coppersmithWinograd_borderRankLE K q)

/-- The typed realization inherits the classical `q + 2` border-rank bound. -/
theorem cwPartitionedTensor_borderRank_le :
    borderRank (cwPartitionedTensor K q).realize ≤ q + 2 := by
  exact borderRank_le_iff.mpr (cwPartitionedTensor_borderRankLE K q)

theorem log_cwPartitionedTensor_borderRank_le :
    Real.log (borderRank (cwPartitionedTensor K q).realize) ≤ Real.log (q + 2) := by
  by_cases hzero : borderRank (cwPartitionedTensor K q).realize = 0
  · rw [hzero]
    simp only [Nat.cast_zero, Real.log_zero]
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ q + 2 by omega)
  · apply Real.log_le_log
    · exact_mod_cast Nat.pos_of_ne_zero hzero
    · exact_mod_cast cwPartitionedTensor_borderRank_le K q

end

end AlgebraicComplexity.Examples
