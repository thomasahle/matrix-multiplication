/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.WordType
import AlgebraicComplexity.Tensor.IndexedPower

/-!
# Grouping indexed tensor-power words by multiplicity type

This bridge combines the paper-independent word expansion of a power of an indexed tensor sum
with the finite word-type partition from `Combinatorics.WordType`. It is deliberately outside the
tensor foundation so importing `AlgebraicComplexity.Tensor` does not pull in type-counting APIs.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {ι : Type w} [Fintype ι]
variable {V : ι → Leg → Type v}
variable [∀ i c, AddCommMonoid (V i c)] [∀ i c, Module K (V i c)]

/-- **The word expansion can be grouped exactly by multiplicity type.**

This is the finite algebraic counterpart of type selection in Schönhage's multiple-compression
proof.

Proof sketch: start from `power_indexedDirectSum_eq_sum_wordPower`, then partition the finite sum
over words using `WordType.sum_by_type`. -/
theorem power_indexedDirectSum_eq_sum_type_wordPower
    (T : ∀ i, Tensor3 K (V i)) (n : ℕ) :
    power (indexedDirectSum T) n =
      ∑ a ∈ WordType.types ι n,
        ∑ word ∈ WordType.typeClass n a, indexedWordPower T n word := by
  rw [power_indexedDirectSum_eq_sum_wordPower]
  exact WordType.sum_by_type (fun word ↦ indexedWordPower T n word)

end AlgebraicComplexity.Tensor
