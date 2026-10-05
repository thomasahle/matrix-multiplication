/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.RankDefs
import AlgebraicComplexity.Tensor.Restriction

/-!
# Map and restriction calculus for tensor rank

The minimal witness and ordinary-rank definitions live in `Tensor/RankDefs.lean`.  This module
adds the laws for legwise maps, permutations, restrictions, and isomorphisms.  External-product
and direct-sum laws remain in `Tensor/Rank.lean`.

The three layers are statement-driven: an exponent definition needs only `RankDefs`; a generic
functorial rank argument needs `RankCore`; and product/direct-sum calculations import `Rank`.
The old `Tensor/Rank.lean` path re-exports every public declaration.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} {W : Leg → Type w}
variable [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]
variable [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]

namespace RankLE

/-- Applying legwise linear maps preserves rank upper bounds: mapping each term of a
decomposition of the source `T` yields an equally long decomposition of the image
`Tensor.map f T`. -/
theorem map {r : ℕ} {T : Tensor3 K V} (hT : RankLE r T)
    (f : ∀ i, V i →ₗ[K] W i) : RankLE r (Tensor.map f T) := by
  rcases hT with ⟨terms, hlen, rfl⟩
  let mapped : (∀ i, V i) → (∀ i, W i) := fun x i ↦ f i (x i)
  have hlen' : (terms.map mapped).length ≤ r := by simpa using hlen
  refine ⟨terms.map mapped, hlen', ?_⟩
  rw [map_list_sum]
  simp [Function.comp_def, mapped]

/-- Reindexing the three tensor legs preserves every constructive rank upper bound. -/
theorem permute {r : ℕ} {T : Tensor3 K V} (hT : RankLE r T)
    (e : Orientation) : RankLE r (Tensor.permute e T) := by
  rcases hT with ⟨terms, hlen, rfl⟩
  let reindexTerm : (∀ i, V i) → (∀ i, V (e.symm i)) :=
    fun x i ↦ x (e.symm i)
  refine ⟨terms.map reindexTerm, by simpa, ?_⟩
  rw [map_list_sum]
  simp [Function.comp_def, reindexTerm]

/-- Rank upper bounds transfer along restriction: if legwise maps carry the source `T` to the
target `S`, then any rank bound for `T` is also a rank bound for `S`. -/
theorem of_restricts {r : ℕ} {T : Tensor3 K V} {S : Tensor3 K W}
    (hT : RankLE r T) (hTS : Restricts T S) : RankLE r S := by
  rcases hTS with ⟨f, rfl⟩
  exact hT.map f

/-- Rank upper bounds are invariant under legwise linear isomorphism. -/
theorem isomorphic {r : ℕ} {T : Tensor3 K V} {S : Tensor3 K W}
    (hTS : Isomorphic T S) : RankLE r T ↔ RankLE r S := by
  constructor
  · intro hT
    exact hT.of_restricts hTS.restricts
  · intro hS
    exact hS.of_restricts hTS.symm.restricts

end RankLE

/-- Applying legwise linear maps cannot increase rank: the image `map f T` has rank at most
that of the source `T`. -/
theorem rank_map_le (f : ∀ c, V c →ₗ[K] W c) (T : Tensor3 K V) :
    rank (map f T) ≤ rank T :=
  rank_le_iff.mpr ((rank_spec T).map f)

/-- Permuting tensor legs cannot increase ordinary tensor rank. -/
theorem rank_permute_le (e : Orientation) (T : Tensor3 K V) :
    rank (permute e T) ≤ rank T :=
  rank_le_iff.mpr ((rank_spec T).permute e)

/-- Restriction cannot increase rank: if legwise maps carry the source `T` to the target `S`,
then `rank S ≤ rank T`. -/
theorem rank_restricts_le {T : Tensor3 K V} {S : Tensor3 K W}
    (h : Restricts T S) : rank S ≤ rank T :=
  rank_le_iff.mpr ((rank_spec T).of_restricts h)

/-- Legwise-isomorphic tensors have equal rank. -/
theorem rank_isomorphic {T : Tensor3 K V} {S : Tensor3 K W}
    (h : Isomorphic T S) : rank T = rank S := by
  apply Nat.le_antisymm
  · exact rank_restricts_le h.symm.restricts
  · exact rank_restricts_le h.restricts

end AlgebraicComplexity.Tensor
