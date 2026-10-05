/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Degeneration

/-!
# Numerical constructive border rank

`BorderRankLE` is the certificate-facing predicate.  This file defines its least numerical bound
and derives the standard monotonicity and submultiplicativity laws from the constructive API.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} {W : Leg → Type w}
variable [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]
variable [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]

namespace BorderRankLE

/-- Cyclically reindexing the three tensor legs preserves every constructive border-rank
certificate: a size-`r` certificate for the source `T` gives a size-`r` certificate for the
rotated target `Tensor.permute cycle T`, with the same leading degree.

Proof sketch: this mirrors `RankLE.permute`.  Apply the linear equivalence `Tensor.permute cycle`
coefficientwise to the certificate path.  That preserves the leading degree and carries the
leading coefficient `T` to `Tensor.permute cycle T`, and `polynomialPure_permute_cycle` identifies
the transported path with the polynomial pure path of the termwise rotated list
`terms.map fun x c ↦ x (cycle.symm c)`, which has the same length. -/
theorem permute_cycle {r : ℕ} {T : Tensor3 K V} (h : BorderRankLE r T) :
    BorderRankLE r (Tensor.permute cycle T) := by
  rcases h with ⟨d, terms, hlen, hlead⟩
  refine ⟨d, terms.map fun x c ↦ x (cycle.symm c), by simpa using hlen, ?_⟩
  have hmapped := hlead.mapLinear (Tensor.permute (K := K) (V := V) cycle).toLinearMap
  have hpath :
      PolynomialVector.mapLinear (Tensor.permute (K := K) (V := V) cycle).toLinearMap
          (terms.map (polynomialPure (K := K))).sum =
        ((terms.map fun x c ↦ x (cycle.symm c)).map (polynomialPure (K := K))).sum := by
    rw [map_list_sum]
    simp [Function.comp_def, polynomialPure_permute_cycle]
  rw [← hpath]
  exact hmapped

end BorderRankLE

/-- Every tensor has a constructive border-rank upper bound. -/
theorem exists_borderRankLE (T : Tensor3 K V) : ∃ r, BorderRankLE r T :=
  ⟨rank T, (rank_spec T).toBorderRankLE⟩

/-- Constructive border rank, defined as the least size of an exact polynomial certificate. -/
noncomputable def borderRank (T : Tensor3 K V) : ℕ := by
  classical
  exact Nat.find (exists_borderRankLE T)

/-- The defining property of `borderRank`: every tensor admits an exact polynomial degeneration
certificate of size at most `borderRank T`. -/
theorem borderRank_spec (T : Tensor3 K V) : BorderRankLE (borderRank T) T := by
  classical
  exact Nat.find_spec (exists_borderRankLE T)

/-- The numerical border rank and its constructive upper-bound predicate are equivalent. -/
theorem borderRank_le_iff {T : Tensor3 K V} {r : ℕ} :
    borderRank T ≤ r ↔ BorderRankLE r T := by
  classical
  constructor
  · intro h
    exact (borderRank_spec T).mono h
  · intro h
    exact Nat.find_min' (exists_borderRankLE T) h

/-- The zero tensor has border rank exactly `0`. -/
@[simp] theorem borderRank_zero : borderRank (0 : Tensor3 K V) = 0 := by
  have h := borderRank_le_iff.mpr (BorderRankLE.zero (K := K) (V := V))
  omega

/-- A tensor has border rank `0` if and only if it is the zero tensor. -/
@[simp] theorem borderRank_eq_zero {T : Tensor3 K V} : borderRank T = 0 ↔ T = 0 := by
  constructor
  · intro h
    have hborder := borderRank_spec T
    rw [h] at hborder
    exact hborder.eq_zero
  · intro h
    subst T
    exact borderRank_zero

/-- Border rank never exceeds ordinary rank: an exact decomposition is in particular a
polynomial certificate. -/
theorem borderRank_le_rank (T : Tensor3 K V) : borderRank T ≤ rank T :=
  borderRank_le_iff.mpr (rank_spec T).toBorderRankLE

/-- Border rank is subadditive: the border rank of `T + S` is at most
`borderRank T + borderRank S`. -/
theorem borderRank_add_le (T S : Tensor3 K V) :
    borderRank (T + S) ≤ borderRank T + borderRank S :=
  borderRank_le_iff.mpr ((borderRank_spec T).add (borderRank_spec S))

/-- Applying legwise linear maps cannot increase border rank: the image `map f T` has border
rank at most that of the source `T`. -/
theorem borderRank_map_le (f : ∀ c, V c →ₗ[K] W c) (T : Tensor3 K V) :
    borderRank (map f T) ≤ borderRank T :=
  borderRank_le_iff.mpr ((borderRank_spec T).map f)

/-- Cyclically permuting tensor legs cannot increase constructive border rank:
`borderRank (permute cycle T) ≤ borderRank T`. -/
theorem borderRank_permute_cycle_le (T : Tensor3 K V) :
    borderRank (permute cycle T) ≤ borderRank T :=
  borderRank_le_iff.mpr (borderRank_spec T).permute_cycle

/-- Restriction cannot increase border rank: if legwise maps carry the source `T` to the target
`S`, then `borderRank S ≤ borderRank T`. -/
theorem borderRank_restricts_le {T : Tensor3 K V} {S : Tensor3 K W}
    (h : Restricts T S) : borderRank S ≤ borderRank T :=
  borderRank_le_iff.mpr ((borderRank_spec T).of_restricts h)

/-- Polynomial degeneration cannot increase border rank: if the source `T` polynomially
degenerates to the target `S`, then `borderRank S ≤ borderRank T`. -/
theorem borderRank_polynomialDegenerates_le {T : Tensor3 K V} {S : Tensor3 K W}
    (h : PolynomialDegenerates T S) : borderRank S ≤ borderRank T :=
  borderRank_le_iff.mpr ((borderRank_spec T).of_polynomialDegenerates h)

/-- Legwise-isomorphic tensors have equal border rank. -/
theorem borderRank_isomorphic {T : Tensor3 K V} {S : Tensor3 K W}
    (h : Isomorphic T S) : borderRank T = borderRank S := by
  apply Nat.le_antisymm
  · exact borderRank_restricts_le h.symm.restricts
  · exact borderRank_restricts_le h.restricts

/-- Border rank is submultiplicative under the external product:
`borderRank (external T S) ≤ borderRank T * borderRank S`. -/
theorem borderRank_external_le (T : Tensor3 K V) (S : Tensor3 K W) :
    borderRank (external T S) ≤ borderRank T * borderRank S :=
  borderRank_le_iff.mpr ((borderRank_spec T).external (borderRank_spec S))

/-- Border rank is subadditive under direct sums:
`borderRank (directSum T S) ≤ borderRank T + borderRank S`. -/
theorem borderRank_directSum_le (T : Tensor3 K V) (S : Tensor3 K W) :
    borderRank (directSum T S) ≤ borderRank T + borderRank S :=
  borderRank_le_iff.mpr ((borderRank_spec T).directSum (borderRank_spec S))

end AlgebraicComplexity.Tensor
