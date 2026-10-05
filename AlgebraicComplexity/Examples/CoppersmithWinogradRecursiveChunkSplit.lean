/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradChunkSplitWordEquivCore
import AlgebraicComplexity.MatrixMultiplication.InterfaceTensorWordSplitCore
import AlgebraicComplexity.Tensor.IteratedProduct
import Mathlib.Tactic.Order

set_option autoImplicit false

/-!
# Recursive half-chunk splitting for Coppersmith--Winograd constituents

A level-`d+2` recursive CW chunk contains `2^(d+1)` base blocks.  The constituent theorem splits
it into two *labelled consecutive* level-`d+1` chunks of length `2^d`; the ordered split `u` is
the three-leg weight of the first child, and the second child has the complementary weight.

This module records that semantic boundary independently of any optimizer or certificate.  The
native recursively parenthesized CW word is identified with its complete-split word, and the
standard consecutive-halves equivalence `splitWordSuccEquiv` is transported back to native CW
chunks.  The partitioned-tensor reassociation corollary is kept in the downstream module
`CoppersmithWinogradRecursiveChunkSplitPartition`, so clients needing only the labelled split do
not import the substantially heavier regional-division layer.  No total-weight quotient, hashing
predicate, or asymptotic estimate is used here.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-- Canonically split one parent native chunk into its two labelled consecutive child chunks.

The definition deliberately transports the already-audited positional split on `SplitWord`; it
does not forget the left/right label and does not quotient a child by its total weight. -/
noncomputable def cwRecursiveChunkSplit (depth : ℕ) :
    PositiveWord CWBlock (2 ^ (depth + 1) - 1) ≃
      PositiveWord CWBlock (2 ^ depth - 1) ×
        PositiveWord CWBlock (2 ^ depth - 1) :=
  (cwChunkSplitWordEquiv (depth + 1)).trans
    ((splitWordSuccEquiv depth).trans
      (Equiv.prodCongr (cwChunkSplitWordEquiv depth).symm
        (cwChunkSplitWordEquiv depth).symm))

/-- Splitting a native parent chunk and then encoding its children is exactly
`splitWordSuccEquiv`; in particular, the first component is the paper's ordered split and the
second component is its labelled complement. -/
@[simp] theorem cwRecursiveChunkSplit_encoded (depth : ℕ)
    (parent : PositiveWord CWBlock (2 ^ (depth + 1) - 1)) :
    (cwChunkSplitWord depth (cwRecursiveChunkSplit depth parent).1,
        cwChunkSplitWord depth (cwRecursiveChunkSplit depth parent).2) =
      splitWordSuccEquiv depth (cwChunkSplitWord (depth + 1) parent) := by
  change
    (cwChunkSplitWordEquiv depth (cwRecursiveChunkSplit depth parent).1,
        cwChunkSplitWordEquiv depth (cwRecursiveChunkSplit depth parent).2) = _
  simp [cwRecursiveChunkSplit]

/-- Join two labelled child chunks into their canonical parent chunk. -/
noncomputable def cwRecursiveChunkJoin (depth : ℕ) :
    PositiveWord CWBlock (2 ^ depth - 1) ×
        PositiveWord CWBlock (2 ^ depth - 1) ≃
      PositiveWord CWBlock (2 ^ (depth + 1) - 1) :=
  (cwRecursiveChunkSplit depth).symm

/-- Complete-split encoding sends native child joining to literal word concatenation. -/
@[simp] theorem cwRecursiveChunkJoin_encoded (depth : ℕ)
    (children : PositiveWord CWBlock (2 ^ depth - 1) ×
      PositiveWord CWBlock (2 ^ depth - 1)) :
    cwChunkSplitWord (depth + 1) (cwRecursiveChunkJoin depth children) =
      concatSplitWords (cwChunkSplitWord depth children.1)
        (cwChunkSplitWord depth children.2) := by
  apply (splitWordSuccEquiv depth).injective
  rw [splitWordSuccEquiv_concatSplitWords]
  simpa [cwRecursiveChunkJoin] using
    (cwRecursiveChunkSplit_encoded depth
      (cwRecursiveChunkJoin depth children)).symm

/-- The parent total weight is the sum of the two labelled child weights. -/
theorem cwRecursiveChunkSplit_weight_add (depth : ℕ)
    (parent : PositiveWord CWBlock (2 ^ (depth + 1) - 1)) :
    splitWordWeight (cwChunkSplitWord depth (cwRecursiveChunkSplit depth parent).1) +
        splitWordWeight (cwChunkSplitWord depth (cwRecursiveChunkSplit depth parent).2) =
      splitWordWeight (cwChunkSplitWord (depth + 1) parent) := by
  rw [splitWordWeight_succ]
  have h := cwRecursiveChunkSplit_encoded depth parent
  rw [← h]

/-- The positive-word parameter for a parent chunk is the sum of the two child parameters plus
one, matching the append convention for two nonempty words. -/
theorem cwChunkParameter_succ (depth : ℕ) :
    2 ^ (depth + 1) - 1 =
      (2 ^ depth - 1) + (2 ^ depth - 1) + 1 := by
  rw [pow_succ]
  have h : 1 ≤ 2 ^ depth := Nat.one_le_two_pow
  omega

/-- Function-word evaluation commutes with transport of the positive-word length parameter. -/
theorem positiveWordEquiv_positiveWordCast_apply {I : Type*} {n m : ℕ}
    (h : n = m) (word : PositiveWord I n) (position : Fin (m + 1)) :
    positiveWordEquiv I m (positiveWordCast h word) position =
      positiveWordEquiv I n word
        (Fin.cast (congrArg (fun k : ℕ ↦ k + 1) h).symm position) := by
  subst m
  rfl

/-- The concrete consecutive-word joining equivalence used by partitioned positive powers. -/
noncomputable def cwStandardChunkJoin (depth : ℕ) :
    PositiveWord CWBlock (2 ^ depth - 1) ×
        PositiveWord CWBlock (2 ^ depth - 1) ≃
      PositiveWord CWBlock (2 ^ (depth + 1) - 1) :=
  (positiveWordAppendEquiv CWBlock (2 ^ depth - 1) (2 ^ depth - 1)).trans
    (Equiv.cast (congrArg (PositiveWord CWBlock) (cwChunkParameter_succ depth).symm))

@[simp] theorem cwStandardChunkJoin_apply (depth : ℕ)
    (children : PositiveWord CWBlock (2 ^ depth - 1) ×
      PositiveWord CWBlock (2 ^ depth - 1)) :
    cwStandardChunkJoin depth children =
      positiveWordCast (cwChunkParameter_succ depth).symm
        (positiveWordAppend children.1 (2 ^ depth - 1) children.2) := by
  rcases children with ⟨left, right⟩
  simp [cwStandardChunkJoin, positiveWordCast]

/-- The standard append operation used by the partitioned tensor has the same complete-split
semantics as literal concatenation of the two child words. -/
theorem cwStandardChunkJoin_encoded (depth : ℕ)
    (children : PositiveWord CWBlock (2 ^ depth - 1) ×
      PositiveWord CWBlock (2 ^ depth - 1)) :
    cwChunkSplitWord (depth + 1) (cwStandardChunkJoin depth children) =
      concatSplitWords (cwChunkSplitWord depth children.1)
        (cwChunkSplitWord depth children.2) := by
  apply (splitWordSuccEquiv depth).injective
  rw [splitWordSuccEquiv_concatSplitWords]
  apply Prod.ext
  · funext position
    change cwBlockDigit
        (positiveWordEquiv CWBlock (2 ^ (depth + 1) - 1)
          (cwStandardChunkJoin depth children)
          ((cwChunkPositionEquiv (depth + 1)).symm
            ((splitIndexSuccEquiv depth).symm (Sum.inl position)))) =
      cwBlockDigit
        (positiveWordEquiv CWBlock (2 ^ depth - 1) children.1
          ((cwChunkPositionEquiv depth).symm position))
    rw [cwStandardChunkJoin_apply,
      positiveWordEquiv_positiveWordCast_apply,
      positiveWordEquiv_append]
    simp only [Function.comp_apply]
    have hposition :
        Fin.cast (by omega)
          (Fin.cast
              (congrArg (fun k : ℕ ↦ k + 1)
                (cwChunkParameter_succ depth).symm).symm
              ((cwChunkPositionEquiv (depth + 1)).symm
                ((splitIndexSuccEquiv depth).symm (Sum.inl position)))) =
        Fin.castAdd (2 ^ depth - 1 + 1)
          ((cwChunkPositionEquiv depth).symm position) := by
      apply Fin.ext
      simp [cwChunkPositionEquiv, splitIndexSuccEquiv]
    rw [hposition, Fin.append_left]
  · funext position
    change cwBlockDigit
        (positiveWordEquiv CWBlock (2 ^ (depth + 1) - 1)
          (cwStandardChunkJoin depth children)
          ((cwChunkPositionEquiv (depth + 1)).symm
            ((splitIndexSuccEquiv depth).symm (Sum.inr position)))) =
      cwBlockDigit
        (positiveWordEquiv CWBlock (2 ^ depth - 1) children.2
          ((cwChunkPositionEquiv depth).symm position))
    rw [cwStandardChunkJoin_apply,
      positiveWordEquiv_positiveWordCast_apply,
      positiveWordEquiv_append]
    simp only [Function.comp_apply]
    have hposition :
        Fin.cast (by omega)
          (Fin.cast
              (congrArg (fun k : ℕ ↦ k + 1)
                (cwChunkParameter_succ depth).symm).symm
              ((cwChunkPositionEquiv (depth + 1)).symm
                ((splitIndexSuccEquiv depth).symm (Sum.inr position)))) =
        Fin.natAdd (2 ^ depth - 1 + 1)
          ((cwChunkPositionEquiv depth).symm position) := by
      apply Fin.ext
      simp [cwChunkPositionEquiv, splitIndexSuccEquiv, two_pow_sub_one_add_one]
    rw [hposition, Fin.append_right]

/-- The split transported through complete-split words is the inverse of the standard native
consecutive-word join.  This closes the semantic gap between the evaluator's ordered split and
the block reindexing used by the tensor partition. -/
theorem cwRecursiveChunkJoin_eq_standard (depth : ℕ) :
    cwRecursiveChunkJoin depth = cwStandardChunkJoin depth := by
  apply Equiv.ext
  intro children
  apply cwChunkSplitWord_injective (depth + 1)
  rw [cwRecursiveChunkJoin_encoded, cwStandardChunkJoin_encoded]

end AlgebraicComplexity.Examples
