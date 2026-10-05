/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.OneSliceRestriction
import AlgebraicComplexity.MatrixMultiplication.PositiveWordProduct
import AlgebraicComplexity.Tensor.PartitionedPowerConstituent

/-!
# One-slice restrictions in partitioned positive powers

This module iterates exposed one-slice restriction maps along a supported word of a partitioned
tensor.  It is separated from `OneSliceRestriction` so clients needing only the binary semantic
law do not import multinomial type extraction.

The result is stronger than the existing proposition-level constituent theorem: it returns the
actual composite maps.  Consequently a shared-leg client can subsequently prove that the `Z`
map is constant over an entire type class.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

namespace OneSliceRestriction

/-- Letterwise one-slice certificates aligned with one particular supported source word.

Unlike a hypothesis quantified over the whole support, this dependent record permits a client to
certify only the letters that actually occur in the word.  That distinction is essential for a
zero-coordinate fiber: the zero-coordinate CW letters are one-slice tensors, while the other
three CW constituents need not be. -/
def PositiveSupportWordData
    (P : PartitionedTensor (K := K) (A := A) V)
    (dimension : P.support → ℕ) :
    (r : ℕ) → (word : PositiveWord P.support r) → Type (max u v)
  | 0, word => OneSliceRestriction (P.constituent word.1) (dimension word)
  | r + 1, word =>
      PositiveSupportWordData P dimension r word.1 ×
        OneSliceRestriction (P.constituent word.2.1) (dimension word.2)

/-- Assemble word-aligned explicit certificates into one explicit restriction of the external
product constituent. -/
noncomputable def ofPositiveSupportWordData
    (P : PartitionedTensor (K := K) (A := A) V)
    (dimension : P.support → ℕ) :
    (r : ℕ) → (word : PositiveWord P.support r) →
      PositiveSupportWordData P dimension r word →
      OneSliceRestriction (P.positiveSupportWordTensor r word)
        (positiveWordProduct dimension r word)
  | 0, _word, data => data
  | r + 1, word, data =>
      (ofPositiveSupportWordData P dimension r word.1 data.1).external data.2

/-- Constituent form of `ofPositiveSupportWordData`, with the source written as the block of the
canonical partitioned positive power. -/
noncomputable def ofPositivePowerConstituentData
    (P : PartitionedTensor (K := K) (A := A) V)
    (dimension : P.support → ℕ)
    (r : ℕ) (word : PositiveWord P.support r)
    (data : PositiveSupportWordData P dimension r word) :
    OneSliceRestriction
      ((P.positivePower r).constituent
        (positiveSupportWordBlockAddress P.support r word))
      (positiveWordProduct dimension r word) := by
  rw [P.positivePower_constituent_positiveSupportWordBlockAddress r word]
  exact ofPositiveSupportWordData P dimension r word data

/-- Iterate explicit constituent maps along a supported word of a partitioned tensor. -/
noncomputable def positiveSupportWord
    (P : PartitionedTensor (K := K) (A := A) V)
    (dimension : P.support → ℕ)
    (base : ∀ support : P.support,
      OneSliceRestriction (P.constituent support.1) (dimension support)) :
    (r : ℕ) → (word : PositiveWord P.support r) →
      OneSliceRestriction (P.positiveSupportWordTensor r word)
        (positiveWordProduct dimension r word)
  | 0, word => base word
  | r + 1, word =>
      (positiveSupportWord P dimension base r word.1).external (base word.2)

@[simp] theorem positiveSupportWord_zero
    (P : PartitionedTensor (K := K) (A := A) V)
    (dimension : P.support → ℕ)
    (base : ∀ support : P.support,
      OneSliceRestriction (P.constituent support.1) (dimension support))
    (word : PositiveWord P.support 0) :
    positiveSupportWord P dimension base 0 word = base word :=
  rfl

@[simp] theorem positiveSupportWord_succ
    (P : PartitionedTensor (K := K) (A := A) V)
    (dimension : P.support → ℕ)
    (base : ∀ support : P.support,
      OneSliceRestriction (P.constituent support.1) (dimension support))
    (r : ℕ) (word : PositiveWord P.support (r + 1)) :
    positiveSupportWord P dimension base (r + 1) word =
      (positiveSupportWord P dimension base r word.1).external (base word.2) :=
  rfl

/-- Constituent form of `positiveSupportWord`, with the source written as the corresponding
block of the canonical partitioned positive power. -/
noncomputable def positivePowerConstituent
    (P : PartitionedTensor (K := K) (A := A) V)
    (dimension : P.support → ℕ)
    (base : ∀ support : P.support,
      OneSliceRestriction (P.constituent support.1) (dimension support))
    (r : ℕ) (word : PositiveWord P.support r) :
    OneSliceRestriction
      ((P.positivePower r).constituent
        (positiveSupportWordBlockAddress P.support r word))
      (positiveWordProduct dimension r word) := by
  rw [P.positivePower_constituent_positiveSupportWordBlockAddress r word]
  exact positiveSupportWord P dimension base r word

end OneSliceRestriction

end AlgebraicComplexity
