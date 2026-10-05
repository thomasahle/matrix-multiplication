/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.InterfaceTensorExactCore
import AlgebraicComplexity.Tensor.PositiveWord

/-!
# Exact-profile predicates for positive words

This module defines the purely combinatorial predicates used to select an exact complete-split
profile from a positive word.  It contains no partitioned tensor products or realization maps.
-/

namespace AlgebraicComplexity

open Tensor

universe w

namespace CompleteSplitProfile

variable {depth total n : ℕ}

/-- A positive word realizes an exact complete-split profile when its function-word form belongs
to the corresponding type class. -/
noncomputable def MatchesPositiveWord
    (β : CompleteSplitProfile depth total (n + 1))
    (word : PositiveWord (SplitWord depth) n) : Prop :=
  positiveWordEquiv (SplitWord depth) n word ∈ β.typeClass

@[simp] theorem matchesPositiveWord_iff_isConsistent
    (β : CompleteSplitProfile depth total (n + 1))
    (word : PositiveWord (SplitWord depth) n) :
    β.MatchesPositiveWord word ↔
      β.IsConsistent (positiveWordEquiv (SplitWord depth) n word) := by
  rw [β.isConsistent_iff_mem_typeClass]
  rfl

/-- Encoded exact-profile matching for an arbitrary native block alphabet. -/
noncomputable def MatchesEncodedPositiveWord {A : Type w}
    (β : CompleteSplitProfile depth total (n + 1)) (encode : A → SplitWord depth)
    (word : PositiveWord A n) : Prop :=
  β.IsConsistent (encode ∘ positiveWordEquiv A n word)

@[simp] theorem matchesEncodedPositiveWord_iff
    {A : Type w} (β : CompleteSplitProfile depth total (n + 1))
    (encode : A → SplitWord depth) (word : PositiveWord A n) :
    β.MatchesEncodedPositiveWord encode word ↔
      β.IsConsistent (encode ∘ positiveWordEquiv A n word) := by
  rfl

/-- At sample size one, an injective encoding makes a singleton profile select exactly one native
block label. -/
@[simp] theorem singleton_matchesEncodedPositiveWord_zero_iff
    {A : Type w} (encode : A → SplitWord depth) (hencode : Function.Injective encode)
    (target other : A) (hweight : splitWordWeight (encode target) = total) :
    (CompleteSplitProfile.singleton (encode target) hweight).MatchesEncodedPositiveWord
        encode (n := 0) other ↔ other = target := by
  change (CompleteSplitProfile.singleton (encode target) hweight).IsConsistent
    (fun _ : Fin 1 ↦ encode other) ↔ other = target
  rw [CompleteSplitProfile.singleton_isConsistent_const_iff]
  exact hencode.eq_iff

end CompleteSplitProfile

namespace ExactInterfaceTermParameters

/-- Retype a stored term profile at the length of a positive partitioned power. -/
def positivePowerProfile {depth n : ℕ} (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (c : Leg) :
    CompleteSplitProfile depth (term.index.count c) (n + 1) :=
  hmultiplicity ▸ term.split c

end ExactInterfaceTermParameters

end AlgebraicComplexity
