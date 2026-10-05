/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.WordTypeStatistics
import AlgebraicComplexity.MatrixMultiplication.InterfaceTensor

/-!
# Additive statistics fixed by complete-split profiles

An exact complete-split profile stores the multiplicity of every chunk word.  Consequently it
fixes not only the total digit weight but every statistic that is additive over chunks.  The
result below is denominator-free and applies to arbitrary finite alphabets of chunk statistics.

For zero-coordinate Coppersmith--Winograd constituents, the relevant statistic counts the
middle digits in a chunk.  Its profile-weighted total is the exponent of the uniform local
`q`-power.
-/

namespace AlgebraicComplexity

open scoped BigOperators

/-- Number of middle (`1`) digits in a complete-split word. -/
def splitWordMiddleCount {depth : ℕ} (word : SplitWord depth) : ℕ :=
  ∑ position, if word position = (1 : SplitDigit) then 1 else 0

namespace CompleteSplitProfile

variable {depth total samples : ℕ}

/-- Every sequence realizing an exact complete-split profile has the stored value of any
additive chunk statistic. -/
theorem sum_statistic_of_isConsistent
    (profile : CompleteSplitProfile depth total samples)
    (sequence : Fin samples → SplitWord depth)
    (hconsistent : profile.IsConsistent sequence)
    (statistic : SplitWord depth → ℕ) :
    ∑ sample, statistic (sequence sample) =
      ∑ word, profile.counts word * statistic word := by
  rw [WordType.sum_word_eq_sum_multiplicity_mul, hconsistent]

/-- Two sequences realizing one exact complete-split profile agree on every additive chunk
statistic. -/
theorem sum_statistic_eq_of_isConsistent
    (profile : CompleteSplitProfile depth total samples)
    {left right : Fin samples → SplitWord depth}
    (hleft : profile.IsConsistent left) (hright : profile.IsConsistent right)
    (statistic : SplitWord depth → ℕ) :
    ∑ sample, statistic (left sample) =
      ∑ sample, statistic (right sample) := by
  rw [profile.sum_statistic_of_isConsistent left hleft statistic,
    profile.sum_statistic_of_isConsistent right hright statistic]

/-- Specialization of `sum_statistic_of_isConsistent` to the middle-digit statistic that
controls zero-coordinate CW dimensions. -/
theorem sum_middleCount_of_isConsistent
    (profile : CompleteSplitProfile depth total samples)
    (sequence : Fin samples → SplitWord depth)
    (hconsistent : profile.IsConsistent sequence) :
    ∑ sample, splitWordMiddleCount (sequence sample) =
      ∑ word, profile.counts word * splitWordMiddleCount word :=
  profile.sum_statistic_of_isConsistent sequence hconsistent splitWordMiddleCount

end CompleteSplitProfile

end AlgebraicComplexity
