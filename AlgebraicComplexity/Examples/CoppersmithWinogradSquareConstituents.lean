/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradSquare

/-!
# Concrete constituents of the Coppersmith--Winograd tensor square

This file gives coordinate models for the five coarse block spaces and uses them to identify the
ordinary `004`, `013`, and `022` constituent classes.  The exceptional `112` value argument is
kept in its own later module.

For each coarse block, the direct sum over source-block fibers is flattened to a sigma-indexed
coordinate space.  The `013` coordinates split into two copies of `Fin q`, corresponding to the
two orders of a corner and a middle term.  The `022` coordinates split into a `q × q` middle
block and two exceptional corner coordinates.

The proofs are constructive restriction certificates.  They compute the coordinate map on each
pure defining term, sum those identities by linearity, and reindex the resulting finite sums to
the standard matrix-multiplication tensor.  Thus the final theorems are exact `Restricts`
statements, not assumed constituent-value interfaces.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped DirectSum

universe u

/-- Coordinate indices carried by one coarsened block of the CW tensor square. -/
abbrev CWSquareBlockCoordinate (q : ℕ) (c : Leg) (degree : Fin 5) :=
  Σ word : BlockFiber cwSquareDegreeMap c degree,
    CWBlockIndex q word.1.1 × CWBlockIndex q word.1.2

/-- Standard coordinate vector without exposing a global decidable-equality instance for the
dependent sigma index. -/
noncomputable def cwSquareCoordinateBasis {K : Type u} [Zero K] [One K]
    (q : ℕ) (c : Leg) (degree : Fin 5)
    (a : CWSquareBlockCoordinate q c degree) :
    CWSquareBlockCoordinate q c degree → K := by
  classical
  exact Pi.single a 1

@[instance_reducible] private def cwBlockIndexFintype' (q : ℕ) (a : CWBlock) :
    Fintype (CWBlockIndex q a) := by
  cases a <;> simp [CWBlockIndex] <;> infer_instance

section Coordinates

variable (K : Type u) [CommRing K]
variable (q : ℕ)

/-- Canonical coordinate equivalence for one coarse block: first coordinatize each tensor-product
source block, then uncurry the finite family into a sigma-indexed function. -/
noncomputable def cwSquareBlockCoordinateEquiv (c : Leg) (degree : Fin 5) :
    CWSquareBlockSpace K q c degree ≃ₗ[K]
      (CWSquareBlockCoordinate q c degree → K) := by
  classical
  letI : ∀ word : BlockFiber cwSquareDegreeMap c degree,
      Finite (CWBlockIndex q word.1.1) := fun word ↦
        @Finite.of_fintype _ (cwBlockIndexFintype' q word.1.1)
  letI : ∀ word : BlockFiber cwSquareDegreeMap c degree,
      Finite (CWBlockIndex q word.1.2) := fun word ↦
        @Finite.of_fintype _ (cwBlockIndexFintype' q word.1.2)
  exact (DirectSum.linearEquivFunOnFintype K
      (BlockFiber cwSquareDegreeMap c degree)
      (fun word ↦ CWSquareRawBlockSpace K q c word.1)).trans
    ((LinearEquiv.piCongrRight fun _word ↦ coordinateTensorEquiv (K := K)).trans
      (LinearEquiv.piCurry K
        (fun word : BlockFiber cwSquareDegreeMap c degree ↦
          fun _ : CWBlockIndex q word.1.1 × CWBlockIndex q word.1.2 ↦ K)).symm)

end Coordinates

/-! ## The ordinary `013` constituent -/

/-- Coordinate of the `013` coarse block selected by a matrix-multiplication index.  The two
copies of `Fin q` distinguish the two orders `002 × 011` and `011 × 002`. -/
def cw013CoordinateIndex (q : ℕ) : ∀ c,
    MMIndex 1 1 (q + q) c → CWSquareBlockCoordinate q c (cwSquare013 c)
  | .X, _ => ⟨⟨(.zero, .zero), by decide⟩, ((), ())⟩
  | .Y, (_, k) =>
      match finSumFinEquiv.symm k with
      | .inl i => ⟨⟨(.zero, .middle), by decide⟩, ((), i)⟩
      | .inr i => ⟨⟨(.middle, .zero), by decide⟩, (i, ())⟩
  | .Z, (k, _) =>
      match finSumFinEquiv.symm k with
      | .inl i => ⟨⟨(.last, .middle), by decide⟩, ((), i)⟩
      | .inr i => ⟨⟨(.middle, .last), by decide⟩, (i, ())⟩

/-- Leg maps extracting `⟨1,1,q+q⟩` from the coarsened `013` block. -/
noncomputable def cw013Map (K : Type u) [CommRing K] (q : ℕ) : ∀ c,
    CWSquareBlockSpace K q c (cwSquare013 c) →ₗ[K] MMSpace K 1 1 (q + q) c :=
  fun c ↦ LinearMap.funLeft K K (cw013CoordinateIndex q c) ∘ₗ
    (cwSquareBlockCoordinateEquiv K q c (cwSquare013 c)).toLinearMap

/-- The terms of `⟨1,1,q+q⟩` belonging to the first copy of `Fin q`. -/
noncomputable def cw013LeftMMTerms (K : Type u) [CommRing K] (q : ℕ) :
    Tensor3 K (MMSpace K 1 1 (q + q)) :=
  ∑ k : Fin q, pure (K := K)
    (mmTerm (K := K) 1 1 (q + q) 0 0 (Fin.castAdd q k))

/-- The terms of `⟨1,1,q+q⟩` belonging to the second copy of `Fin q`. -/
noncomputable def cw013RightMMTerms (K : Type u) [CommRing K] (q : ℕ) :
    Tensor3 K (MMSpace K 1 1 (q + q)) :=
  ∑ k : Fin q, pure (K := K)
    (mmTerm (K := K) 1 1 (q + q) 0 0 (Fin.natAdd q k))

/-- One raw `002 × 011` defining term, typed in its exact uncoarsened square block. -/
noncomputable def cw013LeftRawTerm (K : Type u) [CommRing K] (q : ℕ) (i : Fin q) :
    Tensor3 K (fun c ↦ CWSquareRawBlockSpace K q c
      (cwSquareRawAddress cw002 cw011 c)) :=
  external
    (pure (K := K) (ofLegs
      (cwBlockBasis K q .zero ())
      (cwBlockBasis K q .zero ())
      (cwBlockBasis K q .last ())))
    (pure (K := K) (ofLegs
      (cwBlockBasis K q .zero ())
      (cwBlockBasis K q .middle i)
      (cwBlockBasis K q .middle i)))

/-- The raw `002 × 011` branch before coarsening. -/
noncomputable def cw013LeftRawTensor (K : Type u) [CommRing K] (q : ℕ) :
    Tensor3 K (fun c ↦ CWSquareRawBlockSpace K q c
      (cwSquareRawAddress cw002 cw011 c)) :=
  ∑ i : Fin q, cw013LeftRawTerm K q i

/-- One raw `011 × 002` defining term, typed in its exact uncoarsened square block. -/
noncomputable def cw013RightRawTerm (K : Type u) [CommRing K] (q : ℕ) (i : Fin q) :
    Tensor3 K (fun c ↦ CWSquareRawBlockSpace K q c
      (cwSquareRawAddress cw011 cw002 c)) :=
  external
    (pure (K := K) (ofLegs
      (cwBlockBasis K q .zero ())
      (cwBlockBasis K q .middle i)
      (cwBlockBasis K q .middle i)))
    (pure (K := K) (ofLegs
      (cwBlockBasis K q .zero ())
      (cwBlockBasis K q .zero ())
      (cwBlockBasis K q .last ())))

/-- The raw `011 × 002` branch before coarsening. -/
noncomputable def cw013RightRawTensor (K : Type u) [CommRing K] (q : ℕ) :
    Tensor3 K (fun c ↦ CWSquareRawBlockSpace K q c
      (cwSquareRawAddress cw011 cw002 c)) :=
  ∑ i : Fin q, cw013RightRawTerm K q i

section Constituent013

variable (K : Type u) [CommRing K]
variable (q : ℕ)

/-- A defining pure term from the `002 × 011` branch maps to the corresponding first-half
matrix-multiplication term. -/
theorem map_cw013Map_left_pure (i : Fin q) :
    map (cw013Map K q)
        (map
          (coarsenedBlockIncludeAt
            (K := K) (V := CWSquareRawBlockSpace K q)
            cwSquareDegreeMap (cwSquareRawAddress cw002 cw011) cwSquare013 (by decide))
          (external
            (pure (K := K) (ofLegs
              (cwBlockBasis K q .zero ())
              (cwBlockBasis K q .zero ())
              (cwBlockBasis K q .last ())))
            (pure (K := K) (ofLegs
              (cwBlockBasis K q .zero ())
              (cwBlockBasis K q .middle i)
              (cwBlockBasis K q .middle i))))) =
      pure (K := K)
        (mmTerm (K := K) 1 1 (q + q) 0 0 (Fin.castAdd q i)) := by
  simp only [external_pure, Tensor.map_pure]
  congr 1
  funext c
  cases c with
  | X =>
      ext a
      rcases a with ⟨a, b⟩
      fin_cases a
      fin_cases b
      simp only [cw013Map, LinearMap.comp_apply, LinearMap.funLeft_apply]
      change coordinateTensorEquiv (K := K)
        ((Pi.single () (1 : K) : Unit → K) ⊗ₜ[K]
          (Pi.single () (1 : K) : Unit → K)) ((), ()) = 1
      rw [coordinateTensorEquiv_single_tmul_single]
      simp
  | Y =>
      ext a
      rcases a with ⟨a, k⟩
      fin_cases a
      obtain ⟨k | k, rfl⟩ := finSumFinEquiv.surjective k
      · simp only [finSumFinEquiv_apply_left, cw013Map, LinearMap.comp_apply,
          LinearMap.funLeft_apply, cw013CoordinateIndex,
          finSumFinEquiv_symm_apply_castAdd]
        change coordinateTensorEquiv (K := K)
          ((Pi.single () (1 : K) : Unit → K) ⊗ₜ[K]
            (Pi.single i (1 : K) : Fin q → K)) ((), k) =
          (Pi.single (0, Fin.castAdd q i) (1 : K) :
            (Fin 1 × Fin (q + q) → K)) (0, Fin.castAdd q k)
        rw [coordinateTensorEquiv_single_tmul_single]
        simp [Pi.single_apply]
      · simp only [finSumFinEquiv_apply_right, cw013Map, LinearMap.comp_apply,
          LinearMap.funLeft_apply, cw013CoordinateIndex,
          finSumFinEquiv_symm_apply_natAdd]
        change (0 : K) =
          (Pi.single (0, Fin.castAdd q i) (1 : K) :
            (Fin 1 × Fin (q + q) → K)) (0, Fin.natAdd q k)
        rw [Pi.single_apply]
        split_ifs with h
        · have hval := congrArg (fun x : Fin 1 × Fin (q + q) ↦ x.2.val) h
          simp at hval
          omega
        · rfl

  | Z =>
      ext a
      rcases a with ⟨k, a⟩
      fin_cases a
      obtain ⟨k | k, rfl⟩ := finSumFinEquiv.surjective k
      · simp only [finSumFinEquiv_apply_left, cw013Map, LinearMap.comp_apply,
          LinearMap.funLeft_apply, cw013CoordinateIndex,
          finSumFinEquiv_symm_apply_castAdd]
        change coordinateTensorEquiv (K := K)
          ((Pi.single () (1 : K) : Unit → K) ⊗ₜ[K]
            (Pi.single i (1 : K) : Fin q → K)) ((), k) =
          (Pi.single (Fin.castAdd q i, 0) (1 : K) :
            (Fin (q + q) × Fin 1 → K)) (Fin.castAdd q k, 0)
        rw [coordinateTensorEquiv_single_tmul_single]
        simp [Pi.single_apply]
      · simp only [finSumFinEquiv_apply_right, cw013Map, LinearMap.comp_apply,
          LinearMap.funLeft_apply, cw013CoordinateIndex,
          finSumFinEquiv_symm_apply_natAdd]
        change (0 : K) =
          (Pi.single (Fin.castAdd q i, 0) (1 : K) :
            (Fin (q + q) × Fin 1 → K)) (Fin.natAdd q k, 0)
        rw [Pi.single_apply]
        split_ifs with h
        · have hval := congrArg (fun x : Fin (q + q) × Fin 1 ↦ x.1.val) h
          simp at hval
          omega
        · rfl

/-- The raw square constituent at `002 × 011` has the expected `q`-term expansion. -/
theorem cwSquareRawConstituent_002_011 :
    ((cwPartitionedTensor K q).positivePower 1).constituent
        (cwSquareRawAddress cw002 cw011) =
      cw013LeftRawTensor K q := by
  rw [cwSquareRawConstituent]
  change external
      (cwConstituentOfBlocks K q .zero .zero .last)
      (cwConstituentOfBlocks K q .zero .middle .middle) =
    cw013LeftRawTensor K q
  simp only [cwConstituentOfBlocks, cw013LeftRawTensor, cw013LeftRawTerm]
  exact external_fintypeSum_right _ _

/-- A defining pure term from the `011 × 002` branch maps to the corresponding second-half
matrix-multiplication term. -/
theorem map_cw013Map_right_pure (i : Fin q) :
    map (cw013Map K q)
        (map
          (coarsenedBlockIncludeAt
            (K := K) (V := CWSquareRawBlockSpace K q)
            cwSquareDegreeMap (cwSquareRawAddress cw011 cw002) cwSquare013 (by decide))
          (external
            (pure (K := K) (ofLegs
              (cwBlockBasis K q .zero ())
              (cwBlockBasis K q .middle i)
              (cwBlockBasis K q .middle i)))
            (pure (K := K) (ofLegs
              (cwBlockBasis K q .zero ())
              (cwBlockBasis K q .zero ())
              (cwBlockBasis K q .last ()))))) =
      pure (K := K)
        (mmTerm (K := K) 1 1 (q + q) 0 0 (Fin.natAdd q i)) := by
  simp only [external_pure, Tensor.map_pure]
  congr 1
  funext c
  cases c with
  | X =>
      ext a
      rcases a with ⟨a, b⟩
      fin_cases a
      fin_cases b
      simp only [cw013Map, LinearMap.comp_apply, LinearMap.funLeft_apply]
      change coordinateTensorEquiv (K := K)
        ((Pi.single () (1 : K) : Unit → K) ⊗ₜ[K]
          (Pi.single () (1 : K) : Unit → K)) ((), ()) = 1
      rw [coordinateTensorEquiv_single_tmul_single]
      simp
  | Y =>
      ext a
      rcases a with ⟨a, k⟩
      fin_cases a
      obtain ⟨k | k, rfl⟩ := finSumFinEquiv.surjective k
      · simp only [finSumFinEquiv_apply_left, cw013Map, LinearMap.comp_apply,
          LinearMap.funLeft_apply, cw013CoordinateIndex,
          finSumFinEquiv_symm_apply_castAdd]
        change (0 : K) =
          (Pi.single (0, Fin.natAdd q i) (1 : K) :
            (Fin 1 × Fin (q + q) → K)) (0, Fin.castAdd q k)
        rw [Pi.single_apply]
        split_ifs with h
        · have hval := congrArg (fun x : Fin 1 × Fin (q + q) ↦ x.2.val) h
          simp at hval
          omega
        · rfl
      · simp only [finSumFinEquiv_apply_right, cw013Map, LinearMap.comp_apply,
          LinearMap.funLeft_apply, cw013CoordinateIndex,
          finSumFinEquiv_symm_apply_natAdd]
        change coordinateTensorEquiv (K := K)
          ((Pi.single i (1 : K) : Fin q → K) ⊗ₜ[K]
            (Pi.single () (1 : K) : Unit → K)) (k, ()) =
          (Pi.single (0, Fin.natAdd q i) (1 : K) :
            (Fin 1 × Fin (q + q) → K)) (0, Fin.natAdd q k)
        rw [coordinateTensorEquiv_single_tmul_single]
        simp [Pi.single_apply]

  | Z =>
      ext a
      rcases a with ⟨k, a⟩
      fin_cases a
      obtain ⟨k | k, rfl⟩ := finSumFinEquiv.surjective k
      · simp only [finSumFinEquiv_apply_left, cw013Map, LinearMap.comp_apply,
          LinearMap.funLeft_apply, cw013CoordinateIndex,
          finSumFinEquiv_symm_apply_castAdd]
        change (0 : K) =
          (Pi.single (Fin.natAdd q i, 0) (1 : K) :
            (Fin (q + q) × Fin 1 → K)) (Fin.castAdd q k, 0)
        rw [Pi.single_apply]
        split_ifs with h
        · have hval := congrArg (fun x : Fin (q + q) × Fin 1 ↦ x.1.val) h
          simp at hval
          omega
        · rfl
      · simp only [finSumFinEquiv_apply_right, cw013Map, LinearMap.comp_apply,
          LinearMap.funLeft_apply, cw013CoordinateIndex,
          finSumFinEquiv_symm_apply_natAdd]
        change coordinateTensorEquiv (K := K)
          ((Pi.single i (1 : K) : Fin q → K) ⊗ₜ[K]
            (Pi.single () (1 : K) : Unit → K)) (k, ()) =
          (Pi.single (Fin.natAdd q i, 0) (1 : K) :
            (Fin (q + q) × Fin 1 → K)) (Fin.natAdd q k, 0)
        rw [coordinateTensorEquiv_single_tmul_single]
        simp [Pi.single_apply]

/-- The raw square constituent at `011 × 002` has the expected `q`-term expansion. -/
theorem cwSquareRawConstituent_011_002 :
    ((cwPartitionedTensor K q).positivePower 1).constituent
        (cwSquareRawAddress cw011 cw002) =
      cw013RightRawTensor K q := by
  rw [cwSquareRawConstituent]
  change external
      (cwConstituentOfBlocks K q .zero .middle .middle)
      (cwConstituentOfBlocks K q .zero .zero .last) =
    cw013RightRawTensor K q
  simp only [cwConstituentOfBlocks, cw013RightRawTensor, cw013RightRawTerm]
  exact external_fintypeSum_left _ _

/-- The full `002 × 011` transported branch maps to the first `q` terms. -/
theorem map_cw013Map_leftTerm :
    map (cw013Map K q)
        (coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare013 (cwSquareRawAddress cw002 cw011)) =
      cw013LeftMMTerms K q := by
  rw [coarsenedTerm_eq_map_of_eq
    ((cwPartitionedTensor K q).positivePower 1) cwSquareDegreeMap cwSquare013
    (cwSquareRawAddress cw002 cw011) (by decide)]
  rw [cwSquareRawConstituent_002_011]
  simp only [cw013LeftRawTensor, cw013LeftMMTerms]
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact map_cw013Map_left_pure K q i

/-- The full `011 × 002` transported branch maps to the second `q` terms. -/
theorem map_cw013Map_rightTerm :
    map (cw013Map K q)
        (coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare013 (cwSquareRawAddress cw011 cw002)) =
      cw013RightMMTerms K q := by
  rw [coarsenedTerm_eq_map_of_eq
    ((cwPartitionedTensor K q).positivePower 1) cwSquareDegreeMap cwSquare013
    (cwSquareRawAddress cw011 cw002) (by decide)]
  rw [cwSquareRawConstituent_011_002]
  simp only [cw013RightRawTensor, cw013RightMMTerms]
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact map_cw013Map_right_pure K q i

/-- The two `q`-term halves are exactly `⟨1,1,q+q⟩`.

Proof sketch: split the standard sum over `Fin (q + q)` through `finSumFinEquiv`.  Its left and
right summands are definitionally the two coordinate ranges constructed above. -/
theorem cw013MMTerms_eq_matrixMultiplication :
    cw013LeftMMTerms K q + cw013RightMMTerms K q =
      matrixMultiplication (K := K) 1 1 (q + q) := by
  rw [cw013LeftMMTerms, cw013RightMMTerms, matrixMultiplication_one_one]
  let term : Fin (q + q) → Tensor3 K (MMSpace K 1 1 (q + q)) :=
    fun k ↦ pure (K := K) (mmTerm (K := K) 1 1 (q + q) 0 0 k)
  calc
    (∑ k : Fin q, term (Fin.castAdd q k)) +
          ∑ k : Fin q, term (Fin.natAdd q k) =
        ∑ k : Fin q ⊕ Fin q, term (finSumFinEquiv k) := by
          rw [Fintype.sum_sum_type]
          simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
    _ = ∑ k : Fin (q + q), term k :=
      Equiv.sum_comp finSumFinEquiv term

/-- The explicit coordinate maps identify the full `013` coarse constituent with
`⟨1,1,q+q⟩`.

Proof sketch: expand the coarsened constituent into its two source branches, map each branch to
its corresponding `q`-term half, and use `cw013MMTerms_eq_matrixMultiplication` to recombine the
halves. -/
theorem map_cw013Map_constituent :
    map (cw013Map K q)
        ((cwSquarePartitionedTensor K q).constituent cwSquare013) =
      matrixMultiplication (K := K) 1 1 (q + q) := by
  rw [cwSquareConstituent_013, map_add, map_cw013Map_leftTerm,
    map_cw013Map_rightTerm, cw013MMTerms_eq_matrixMultiplication]

/-- Paper form of the ordinary `013` certificate: the constituent restricts to
`⟨1,1,2q⟩`.

The restriction witness is the explicit leg map `cw013Map`; only the elementary equality
`2 * q = q + q` is needed to put the coordinate theorem in the paper's notation. -/
theorem cwSquareConstituent_013_restricts :
    Restricts
      ((cwSquarePartitionedTensor K q).constituent cwSquare013)
      (matrixMultiplication (K := K) 1 1 (2 * q)) := by
  have hdim : 2 * q = q + q := by omega
  rw [hdim]
  exact ⟨cw013Map K q, map_cw013Map_constituent K q⟩

end Constituent013

/-! ## The ordinary `022` constituent -/

/-- Index equivalence exhibiting the `q² + 2` coordinates as a `q × q` block and two corner
coordinates. -/
def cw022IndexEquiv (q : ℕ) : (Fin q × Fin q) ⊕ Fin 2 ≃ Fin (q * q + 2) :=
  (Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin 2))).trans finSumFinEquiv

/-- The `q × q` part of the `022` index equivalence occupies the first `q²` coordinates. -/
@[simp] theorem cw022IndexEquiv_inl (q : ℕ) (i j : Fin q) :
    cw022IndexEquiv q (Sum.inl (i, j)) =
      Fin.castAdd 2 (finProdFinEquiv (i, j)) := by
  rfl

/-- The two exceptional `022` indices occupy the final two coordinates. -/
@[simp] theorem cw022IndexEquiv_inr (q : ℕ) (r : Fin 2) :
    cw022IndexEquiv q (Sum.inr r) = Fin.natAdd (q * q) r := by
  rfl

/-- A middle `q × q` coordinate never equals an exceptional corner coordinate. -/
@[simp] theorem cw022IndexEquiv_inl_ne_inr (q : ℕ) (ij : Fin q × Fin q) (r : Fin 2) :
    cw022IndexEquiv q (Sum.inl ij) ≠ cw022IndexEquiv q (Sum.inr r) := by
  intro h
  have hs : (Sum.inl ij : (Fin q × Fin q) ⊕ Fin 2) = Sum.inr r :=
    (cw022IndexEquiv q).injective h
  cases hs

/-- An exceptional corner coordinate never equals a middle `q × q` coordinate. -/
@[simp] theorem cw022IndexEquiv_inr_ne_inl (q : ℕ) (r : Fin 2) (ij : Fin q × Fin q) :
    cw022IndexEquiv q (Sum.inr r) ≠ cw022IndexEquiv q (Sum.inl ij) := by
  exact Ne.symm (cw022IndexEquiv_inl_ne_inr q ij r)

/-- Coordinate of the `022` coarse block selected by a matrix-multiplication index. -/
def cw022CoordinateIndex (q : ℕ) : ∀ c,
    MMIndex 1 1 (q * q + 2) c → CWSquareBlockCoordinate q c (cwSquare022 c)
  | .X, _ => ⟨⟨(.zero, .zero), by decide⟩, ((), ())⟩
  | .Y, (_, k) =>
      match (cw022IndexEquiv q).symm k with
      | .inl ij => ⟨⟨(.middle, .middle), by decide⟩, ij⟩
      | .inr r => Fin.cases
          ⟨⟨(.zero, .last), by decide⟩, ((), ())⟩
          (fun _ => ⟨⟨(.last, .zero), by decide⟩, ((), ())⟩) r
  | .Z, (k, _) =>
      match (cw022IndexEquiv q).symm k with
      | .inl ij => ⟨⟨(.middle, .middle), by decide⟩, ij⟩
      | .inr r => Fin.cases
          ⟨⟨(.last, .zero), by decide⟩, ((), ())⟩
          (fun _ => ⟨⟨(.zero, .last), by decide⟩, ((), ())⟩) r

/-- Leg maps extracting `⟨1,1,q²+2⟩` from the coarsened `022` block. -/
noncomputable def cw022Map (K : Type u) [CommRing K] (q : ℕ) : ∀ c,
    CWSquareBlockSpace K q c (cwSquare022 c) →ₗ[K]
      MMSpace K 1 1 (q * q + 2) c :=
  fun c ↦ LinearMap.funLeft K K (cw022CoordinateIndex q c) ∘ₗ
    (cwSquareBlockCoordinateEquiv K q c (cwSquare022 c)).toLinearMap

/-- Matrix terms belonging to the `q × q` middle block of `022`. -/
noncomputable def cw022MiddleMMTerms (K : Type u) [CommRing K] (q : ℕ) :
    Tensor3 K (MMSpace K 1 1 (q * q + 2)) :=
  ∑ ij : Fin q × Fin q, pure (K := K)
    (mmTerm (K := K) 1 1 (q * q + 2) 0 0
      (cw022IndexEquiv q (Sum.inl ij)))

/-- The two corner matrix terms of `022`. -/
noncomputable def cw022CornerMMTerms (K : Type u) [CommRing K] (q : ℕ) :
    Tensor3 K (MMSpace K 1 1 (q * q + 2)) :=
  ∑ r : Fin 2, pure (K := K)
    (mmTerm (K := K) 1 1 (q * q + 2) 0 0
      (cw022IndexEquiv q (Sum.inr r)))

/-- One defining term from the raw `011 × 011` middle block. -/
noncomputable def cw022MiddleRawTerm (K : Type u) [CommRing K]
    (q : ℕ) (ij : Fin q × Fin q) :
    Tensor3 K (fun c ↦ CWSquareRawBlockSpace K q c
      (cwSquareRawAddress cw011 cw011 c)) :=
  external
    (pure (K := K) (ofLegs
      (cwBlockBasis K q .zero ())
      (cwBlockBasis K q .middle ij.1)
      (cwBlockBasis K q .middle ij.1)))
    (pure (K := K) (ofLegs
      (cwBlockBasis K q .zero ())
      (cwBlockBasis K q .middle ij.2)
      (cwBlockBasis K q .middle ij.2)))

/-- The `q²`-term raw `011 × 011` constituent. -/
noncomputable def cw022MiddleRawTensor (K : Type u) [CommRing K] (q : ℕ) :
    Tensor3 K (fun c ↦ CWSquareRawBlockSpace K q c
      (cwSquareRawAddress cw011 cw011 c)) :=
  ∑ ij : Fin q × Fin q, cw022MiddleRawTerm K q ij

/-- Raw corner term `002 × 020`. -/
noncomputable def cw022Corner0RawTerm (K : Type u) [CommRing K] (q : ℕ) :
    Tensor3 K (fun c ↦ CWSquareRawBlockSpace K q c
      (cwSquareRawAddress cw002 cw020 c)) :=
  external
    (pure (K := K) (ofLegs
      (cwBlockBasis K q .zero ())
      (cwBlockBasis K q .zero ())
      (cwBlockBasis K q .last ())))
    (pure (K := K) (ofLegs
      (cwBlockBasis K q .zero ())
      (cwBlockBasis K q .last ())
      (cwBlockBasis K q .zero ())))

/-- Raw corner term `020 × 002`. -/
noncomputable def cw022Corner1RawTerm (K : Type u) [CommRing K] (q : ℕ) :
    Tensor3 K (fun c ↦ CWSquareRawBlockSpace K q c
      (cwSquareRawAddress cw020 cw002 c)) :=
  external
    (pure (K := K) (ofLegs
      (cwBlockBasis K q .zero ())
      (cwBlockBasis K q .last ())
      (cwBlockBasis K q .zero ())))
    (pure (K := K) (ofLegs
      (cwBlockBasis K q .zero ())
      (cwBlockBasis K q .zero ())
      (cwBlockBasis K q .last ())))

section Constituent022

variable (K : Type u) [CommRing K]
variable (q : ℕ)

/-- A defining `011 × 011` term maps to its coordinate in the `q²` middle block. -/
theorem map_cw022Map_middle_pure (i j : Fin q) :
    map (cw022Map K q)
        (map
          (coarsenedBlockIncludeAt
            (K := K) (V := CWSquareRawBlockSpace K q)
            cwSquareDegreeMap (cwSquareRawAddress cw011 cw011) cwSquare022 (by decide))
          (cw022MiddleRawTerm K q (i, j))) =
      pure (K := K)
        (mmTerm (K := K) 1 1 (q * q + 2) 0 0
          (cw022IndexEquiv q (Sum.inl (i, j)))) := by
  simp only [cw022MiddleRawTerm, external_pure, Tensor.map_pure]
  congr 1
  funext c
  cases c with
  | X =>
      ext a
      rcases a with ⟨a, b⟩
      fin_cases a
      fin_cases b
      simp only [cw022Map, LinearMap.comp_apply, LinearMap.funLeft_apply]
      change coordinateTensorEquiv (K := K)
        ((Pi.single () (1 : K) : Unit → K) ⊗ₜ[K]
          (Pi.single () (1 : K) : Unit → K)) ((), ()) = 1
      rw [coordinateTensorEquiv_single_tmul_single]
      simp
  | Y =>
      ext a
      rcases a with ⟨a, k⟩
      fin_cases a
      obtain ⟨ij | r, rfl⟩ := (cw022IndexEquiv q).surjective k
      · rcases ij with ⟨i', j'⟩
        simp only [cw022Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
          cw022CoordinateIndex, Equiv.symm_apply_apply]
        change coordinateTensorEquiv (K := K)
            ((Pi.single i (1 : K) : Fin q → K) ⊗ₜ[K]
              (Pi.single j (1 : K) : Fin q → K)) (i', j') =
          (Pi.single (0, cw022IndexEquiv q (Sum.inl (i, j))) (1 : K) :
            (Fin 1 × Fin (q * q + 2) → K))
              (0, cw022IndexEquiv q (Sum.inl (i', j')))
        rw [coordinateTensorEquiv_single_tmul_single]
        simp [Pi.single_apply]
      · fin_cases r
        · simp only [cw022Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
            cw022CoordinateIndex, Equiv.symm_apply_apply]
          change (0 : K) =
            (Pi.single (0, cw022IndexEquiv q (Sum.inl (i, j))) (1 : K) :
              (Fin 1 × Fin (q * q + 2) → K))
                (0, cw022IndexEquiv q (Sum.inr 0))
          rw [Pi.single_apply]
          split_ifs with h
          · have hs := (cw022IndexEquiv q).injective (congrArg Prod.snd h)
            contradiction
          · rfl
        · simp only [cw022Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
            cw022CoordinateIndex, Equiv.symm_apply_apply]
          change (0 : K) =
            (Pi.single (0, cw022IndexEquiv q (Sum.inl (i, j))) (1 : K) :
              (Fin 1 × Fin (q * q + 2) → K))
                (0, cw022IndexEquiv q (Sum.inr 1))
          rw [Pi.single_apply]
          split_ifs with h
          · have hs := (cw022IndexEquiv q).injective (congrArg Prod.snd h)
            contradiction
          · rfl
  | Z =>
      ext a
      rcases a with ⟨k, a⟩
      fin_cases a
      obtain ⟨ij | r, rfl⟩ := (cw022IndexEquiv q).surjective k
      · rcases ij with ⟨i', j'⟩
        simp only [cw022Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
          cw022CoordinateIndex, Equiv.symm_apply_apply]
        change coordinateTensorEquiv (K := K)
            ((Pi.single i (1 : K) : Fin q → K) ⊗ₜ[K]
              (Pi.single j (1 : K) : Fin q → K)) (i', j') =
          (Pi.single (cw022IndexEquiv q (Sum.inl (i, j)), 0) (1 : K) :
            (Fin (q * q + 2) × Fin 1 → K))
              (cw022IndexEquiv q (Sum.inl (i', j')), 0)
        rw [coordinateTensorEquiv_single_tmul_single]
        simp [Pi.single_apply]
      · fin_cases r
        · simp only [cw022Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
            cw022CoordinateIndex, Equiv.symm_apply_apply]
          change (0 : K) =
            (Pi.single (cw022IndexEquiv q (Sum.inl (i, j)), 0) (1 : K) :
              (Fin (q * q + 2) × Fin 1 → K))
                (cw022IndexEquiv q (Sum.inr 0), 0)
          rw [Pi.single_apply]
          split_ifs with h
          · have hs := (cw022IndexEquiv q).injective (congrArg Prod.fst h)
            contradiction
          · rfl
        · simp only [cw022Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
            cw022CoordinateIndex, Equiv.symm_apply_apply]
          change (0 : K) =
            (Pi.single (cw022IndexEquiv q (Sum.inl (i, j)), 0) (1 : K) :
              (Fin (q * q + 2) × Fin 1 → K))
                (cw022IndexEquiv q (Sum.inr 1), 0)
          rw [Pi.single_apply]
          split_ifs with h
          · have hs := (cw022IndexEquiv q).injective (congrArg Prod.fst h)
            contradiction
          · rfl

/-- The raw `011 × 011` square constituent has its explicit `q²`-term expansion. -/
theorem cwSquareRawConstituent_011_011 :
    ((cwPartitionedTensor K q).positivePower 1).constituent
        (cwSquareRawAddress cw011 cw011) =
      cw022MiddleRawTensor K q := by
  rw [cwSquareRawConstituent]
  change external
      (cwConstituentOfBlocks K q .zero .middle .middle)
      (cwConstituentOfBlocks K q .zero .middle .middle) =
    cw022MiddleRawTensor K q
  simp only [cwConstituentOfBlocks, cw022MiddleRawTensor, cw022MiddleRawTerm]
  rw [external_sum_sum, ← Fintype.sum_prod_type']
  rfl

/-- The transported `011 × 011` branch maps to the `q²` middle matrix terms. -/
theorem map_cw022Map_middleTerm :
    map (cw022Map K q)
        (coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare022 (cwSquareRawAddress cw011 cw011)) =
      cw022MiddleMMTerms K q := by
  rw [coarsenedTerm_eq_map_of_eq
    ((cwPartitionedTensor K q).positivePower 1) cwSquareDegreeMap cwSquare022
    (cwSquareRawAddress cw011 cw011) (by decide)]
  rw [cwSquareRawConstituent_011_011]
  simp only [cw022MiddleRawTensor, cw022MiddleMMTerms]
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  rintro ⟨i, j⟩ _
  exact map_cw022Map_middle_pure K q i j

/-- The raw `002 × 020` corner maps to the first exceptional coordinate. -/
theorem map_cw022Map_corner0_pure :
    map (cw022Map K q)
        (map
          (coarsenedBlockIncludeAt
            (K := K) (V := CWSquareRawBlockSpace K q)
            cwSquareDegreeMap (cwSquareRawAddress cw002 cw020) cwSquare022 (by decide))
          (cw022Corner0RawTerm K q)) =
      pure (K := K)
        (mmTerm (K := K) 1 1 (q * q + 2) 0 0
          (cw022IndexEquiv q (Sum.inr 0))) := by
  simp only [cw022Corner0RawTerm, external_pure, Tensor.map_pure]
  congr 1
  funext c
  cases c with
  | X =>
      ext a
      rcases a with ⟨a, b⟩
      fin_cases a
      fin_cases b
      simp only [cw022Map, LinearMap.comp_apply, LinearMap.funLeft_apply]
      change coordinateTensorEquiv (K := K)
        ((Pi.single () (1 : K) : Unit → K) ⊗ₜ[K]
          (Pi.single () (1 : K) : Unit → K)) ((), ()) = 1
      rw [coordinateTensorEquiv_single_tmul_single]
      simp
  | Y =>
      ext a
      rcases a with ⟨a, k⟩
      fin_cases a
      obtain ⟨ij | r, rfl⟩ := (cw022IndexEquiv q).surjective k
      · rcases ij with ⟨i, j⟩
        simp only [cw022Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
          cw022CoordinateIndex, Equiv.symm_apply_apply]
        change (0 : K) =
          (Pi.single (0, cw022IndexEquiv q (Sum.inr 0)) (1 : K) :
            (Fin 1 × Fin (q * q + 2) → K))
              (0, cw022IndexEquiv q (Sum.inl (i, j)))
        rw [Pi.single_apply]
        split_ifs with h
        · exact (cw022IndexEquiv_inl_ne_inr q (i, j) 0
            (congrArg Prod.snd h)).elim
        · rfl
      · fin_cases r
        · simp only [cw022Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
            cw022CoordinateIndex, Equiv.symm_apply_apply]
          change coordinateTensorEquiv (K := K)
              ((Pi.single () (1 : K) : Unit → K) ⊗ₜ[K]
                (Pi.single () (1 : K) : Unit → K)) ((), ()) =
            (Pi.single (0, cw022IndexEquiv q (Sum.inr 0)) (1 : K) :
              (Fin 1 × Fin (q * q + 2) → K))
                (0, cw022IndexEquiv q (Sum.inr 0))
          rw [coordinateTensorEquiv_single_tmul_single]
          simp
        · simp only [cw022Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
            cw022CoordinateIndex, Equiv.symm_apply_apply]
          change (0 : K) =
            (Pi.single (0, cw022IndexEquiv q (Sum.inr 0)) (1 : K) :
              (Fin 1 × Fin (q * q + 2) → K))
                (0, cw022IndexEquiv q (Sum.inr 1))
          simp
  | Z =>
      ext a
      rcases a with ⟨k, a⟩
      fin_cases a
      obtain ⟨ij | r, rfl⟩ := (cw022IndexEquiv q).surjective k
      · rcases ij with ⟨i, j⟩
        simp only [cw022Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
          cw022CoordinateIndex, Equiv.symm_apply_apply]
        change (0 : K) =
          (Pi.single (cw022IndexEquiv q (Sum.inr 0), 0) (1 : K) :
            (Fin (q * q + 2) × Fin 1 → K))
              (cw022IndexEquiv q (Sum.inl (i, j)), 0)
        rw [Pi.single_apply]
        split_ifs with h
        · exact (cw022IndexEquiv_inl_ne_inr q (i, j) 0
            (congrArg Prod.fst h)).elim
        · rfl
      · fin_cases r
        · simp only [cw022Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
            cw022CoordinateIndex, Equiv.symm_apply_apply]
          change coordinateTensorEquiv (K := K)
              ((Pi.single () (1 : K) : Unit → K) ⊗ₜ[K]
                (Pi.single () (1 : K) : Unit → K)) ((), ()) =
            (Pi.single (cw022IndexEquiv q (Sum.inr 0), 0) (1 : K) :
              (Fin (q * q + 2) × Fin 1 → K))
                (cw022IndexEquiv q (Sum.inr 0), 0)
          rw [coordinateTensorEquiv_single_tmul_single]
          simp
        · simp only [cw022Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
            cw022CoordinateIndex, Equiv.symm_apply_apply]
          change (0 : K) =
            (Pi.single (cw022IndexEquiv q (Sum.inr 0), 0) (1 : K) :
              (Fin (q * q + 2) × Fin 1 → K))
                (cw022IndexEquiv q (Sum.inr 1), 0)
          simp

/-- The raw `020 × 002` corner maps to the second exceptional coordinate. -/
theorem map_cw022Map_corner1_pure :
    map (cw022Map K q)
        (map
          (coarsenedBlockIncludeAt
            (K := K) (V := CWSquareRawBlockSpace K q)
            cwSquareDegreeMap (cwSquareRawAddress cw020 cw002) cwSquare022 (by decide))
          (cw022Corner1RawTerm K q)) =
      pure (K := K)
        (mmTerm (K := K) 1 1 (q * q + 2) 0 0
          (cw022IndexEquiv q (Sum.inr 1))) := by
  simp only [cw022Corner1RawTerm, external_pure, Tensor.map_pure]
  congr 1
  funext c
  cases c with
  | X =>
      ext a
      rcases a with ⟨a, b⟩
      fin_cases a
      fin_cases b
      simp only [cw022Map, LinearMap.comp_apply, LinearMap.funLeft_apply]
      change coordinateTensorEquiv (K := K)
        ((Pi.single () (1 : K) : Unit → K) ⊗ₜ[K]
          (Pi.single () (1 : K) : Unit → K)) ((), ()) = 1
      rw [coordinateTensorEquiv_single_tmul_single]
      simp
  | Y =>
      ext a
      rcases a with ⟨a, k⟩
      fin_cases a
      obtain ⟨ij | r, rfl⟩ := (cw022IndexEquiv q).surjective k
      · rcases ij with ⟨i, j⟩
        simp only [cw022Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
          cw022CoordinateIndex, Equiv.symm_apply_apply]
        change (0 : K) =
          (Pi.single (0, cw022IndexEquiv q (Sum.inr 1)) (1 : K) :
            (Fin 1 × Fin (q * q + 2) → K))
              (0, cw022IndexEquiv q (Sum.inl (i, j)))
        rw [Pi.single_apply]
        split_ifs with h
        · exact (cw022IndexEquiv_inl_ne_inr q (i, j) 1
            (congrArg Prod.snd h)).elim
        · rfl
      · fin_cases r
        · simp only [cw022Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
            cw022CoordinateIndex, Equiv.symm_apply_apply]
          change (0 : K) =
            (Pi.single (0, cw022IndexEquiv q (Sum.inr 1)) (1 : K) :
              (Fin 1 × Fin (q * q + 2) → K))
                (0, cw022IndexEquiv q (Sum.inr 0))
          simp
        · simp only [cw022Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
            cw022CoordinateIndex, Equiv.symm_apply_apply]
          change coordinateTensorEquiv (K := K)
              ((Pi.single () (1 : K) : Unit → K) ⊗ₜ[K]
                (Pi.single () (1 : K) : Unit → K)) ((), ()) =
            (Pi.single (0, cw022IndexEquiv q (Sum.inr 1)) (1 : K) :
              (Fin 1 × Fin (q * q + 2) → K))
                (0, cw022IndexEquiv q (Sum.inr 1))
          rw [coordinateTensorEquiv_single_tmul_single]
          simp
  | Z =>
      ext a
      rcases a with ⟨k, a⟩
      fin_cases a
      obtain ⟨ij | r, rfl⟩ := (cw022IndexEquiv q).surjective k
      · rcases ij with ⟨i, j⟩
        simp only [cw022Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
          cw022CoordinateIndex, Equiv.symm_apply_apply]
        change (0 : K) =
          (Pi.single (cw022IndexEquiv q (Sum.inr 1), 0) (1 : K) :
            (Fin (q * q + 2) × Fin 1 → K))
              (cw022IndexEquiv q (Sum.inl (i, j)), 0)
        rw [Pi.single_apply]
        split_ifs with h
        · exact (cw022IndexEquiv_inl_ne_inr q (i, j) 1
            (congrArg Prod.fst h)).elim
        · rfl
      · fin_cases r
        · simp only [cw022Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
            cw022CoordinateIndex, Equiv.symm_apply_apply]
          change (0 : K) =
            (Pi.single (cw022IndexEquiv q (Sum.inr 1), 0) (1 : K) :
              (Fin (q * q + 2) × Fin 1 → K))
                (cw022IndexEquiv q (Sum.inr 0), 0)
          simp
        · simp only [cw022Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
            cw022CoordinateIndex, Equiv.symm_apply_apply]
          change coordinateTensorEquiv (K := K)
              ((Pi.single () (1 : K) : Unit → K) ⊗ₜ[K]
                (Pi.single () (1 : K) : Unit → K)) ((), ()) =
            (Pi.single (cw022IndexEquiv q (Sum.inr 1), 0) (1 : K) :
              (Fin (q * q + 2) × Fin 1 → K))
                (cw022IndexEquiv q (Sum.inr 1), 0)
          rw [coordinateTensorEquiv_single_tmul_single]
          simp

/-- The first raw corner constituent is exactly its single defining term. -/
theorem cwSquareRawConstituent_002_020 :
    ((cwPartitionedTensor K q).positivePower 1).constituent
        (cwSquareRawAddress cw002 cw020) =
      cw022Corner0RawTerm K q := by
  rw [cwSquareRawConstituent]
  change external
      (cwConstituentOfBlocks K q .zero .zero .last)
      (cwConstituentOfBlocks K q .zero .last .zero) =
    cw022Corner0RawTerm K q
  rfl

/-- The second raw corner constituent is exactly its single defining term. -/
theorem cwSquareRawConstituent_020_002 :
    ((cwPartitionedTensor K q).positivePower 1).constituent
        (cwSquareRawAddress cw020 cw002) =
      cw022Corner1RawTerm K q := by
  rw [cwSquareRawConstituent]
  change external
      (cwConstituentOfBlocks K q .zero .last .zero)
      (cwConstituentOfBlocks K q .zero .zero .last) =
    cw022Corner1RawTerm K q
  rfl

/-- The transported first corner branch maps to exceptional coordinate zero. -/
theorem map_cw022Map_corner0Term :
    map (cw022Map K q)
        (coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare022 (cwSquareRawAddress cw002 cw020)) =
      pure (K := K)
        (mmTerm (K := K) 1 1 (q * q + 2) 0 0
          (cw022IndexEquiv q (Sum.inr 0))) := by
  rw [coarsenedTerm_eq_map_of_eq
    ((cwPartitionedTensor K q).positivePower 1) cwSquareDegreeMap cwSquare022
    (cwSquareRawAddress cw002 cw020) (by decide)]
  rw [cwSquareRawConstituent_002_020]
  exact map_cw022Map_corner0_pure K q

/-- The transported second corner branch maps to exceptional coordinate one. -/
theorem map_cw022Map_corner1Term :
    map (cw022Map K q)
        (coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare022 (cwSquareRawAddress cw020 cw002)) =
      pure (K := K)
        (mmTerm (K := K) 1 1 (q * q + 2) 0 0
          (cw022IndexEquiv q (Sum.inr 1))) := by
  rw [coarsenedTerm_eq_map_of_eq
    ((cwPartitionedTensor K q).positivePower 1) cwSquareDegreeMap cwSquare022
    (cwSquareRawAddress cw020 cw002) (by decide)]
  rw [cwSquareRawConstituent_020_002]
  exact map_cw022Map_corner1_pure K q

/-- The two explicitly mapped corner terms form the two-coordinate corner sum. -/
theorem cw022CornerMMTerms_eq :
    pure (K := K)
        (mmTerm (K := K) 1 1 (q * q + 2) 0 0
          (cw022IndexEquiv q (Sum.inr 0))) +
      pure (K := K)
        (mmTerm (K := K) 1 1 (q * q + 2) 0 0
          (cw022IndexEquiv q (Sum.inr 1))) =
      cw022CornerMMTerms K q := by
  rw [cw022CornerMMTerms, Fin.sum_univ_two]

/-- The `q²` middle terms and two corner terms are exactly `⟨1,1,q²+2⟩`.

Proof sketch: use `cw022IndexEquiv` to reindex the disjoint sum of `Fin q × Fin q` and
`Fin 2` as `Fin (q² + 2)`.  This turns the two partial sums into the defining sum for the
matrix-multiplication tensor. -/
theorem cw022MMTerms_eq_matrixMultiplication :
    cw022MiddleMMTerms K q + cw022CornerMMTerms K q =
      matrixMultiplication (K := K) 1 1 (q * q + 2) := by
  rw [cw022MiddleMMTerms, cw022CornerMMTerms, matrixMultiplication_one_one]
  let term : Fin (q * q + 2) → Tensor3 K (MMSpace K 1 1 (q * q + 2)) :=
    fun k ↦ pure (K := K) (mmTerm (K := K) 1 1 (q * q + 2) 0 0 k)
  calc
    (∑ ij : Fin q × Fin q, term (cw022IndexEquiv q (Sum.inl ij))) +
          ∑ r : Fin 2, term (cw022IndexEquiv q (Sum.inr r)) =
        ∑ s : (Fin q × Fin q) ⊕ Fin 2, term (cw022IndexEquiv q s) := by
          rw [Fintype.sum_sum_type]
    _ = ∑ k : Fin (q * q + 2), term k :=
      Equiv.sum_comp (cw022IndexEquiv q) term

/-- The explicit coordinate maps identify the full `022` coarse constituent with
`⟨1,1,q²+2⟩`.

Proof sketch: expand `022` into its two one-term corners and its `q²` middle branch.  The
coordinate lemmas map these to the exceptional and middle index ranges; commutativity of addition
then places them in the order used by `cw022MMTerms_eq_matrixMultiplication`. -/
theorem map_cw022Map_constituent :
    map (cw022Map K q)
        ((cwSquarePartitionedTensor K q).constituent cwSquare022) =
      matrixMultiplication (K := K) 1 1 (q * q + 2) := by
  rw [cwSquareConstituent_022, map_add, map_add,
    map_cw022Map_corner0Term, map_cw022Map_corner1Term,
    map_cw022Map_middleTerm, cw022CornerMMTerms_eq]
  calc
    cw022CornerMMTerms K q + cw022MiddleMMTerms K q =
        cw022MiddleMMTerms K q + cw022CornerMMTerms K q := add_comm _ _
    _ = matrixMultiplication (K := K) 1 1 (q * q + 2) :=
      cw022MMTerms_eq_matrixMultiplication K q

/-- Paper form of the ordinary `022` certificate: the constituent restricts to
`⟨1,1,q²+2⟩`.

The restriction witness is `cw022Map`.  The final normalization merely changes Lean's `q ^ 2`
notation to the product `q * q` used by the coordinate indexing equivalence. -/
theorem cwSquareConstituent_022_restricts :
    Restricts
      ((cwSquarePartitionedTensor K q).constituent cwSquare022)
      (matrixMultiplication (K := K) 1 1 (q ^ 2 + 2)) := by
  have hdim : q ^ 2 + 2 = q * q + 2 := by simp [pow_two]
  rw [hdim]
  exact ⟨cw022Map K q, map_cw022Map_constituent K q⟩

end Constituent022

end AlgebraicComplexity.Examples
