/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Batteries.Data.Fin.Basic

set_option autoImplicit false

/-!
# A leg-local obstruction for the paired Total-Weight mixed reader

The paired Total-Weight certificate reads a depth-two physical `Y` word in two incompatible ways:
an interior child keeps only its ordered pair of depth-one total weights, while a boundary child
keeps the literal word.  This module records the smallest exact obstruction to representing both
kernels by one pre-isolation leg-local label.

The obstruction is deliberately about the label's kernel, not mere factorization.  Taking the
label to be the identity always permits candidate-dependent postprocessing, but retains the raw
entropy and therefore does not realize the certificate's feature-only rate.  Here the boundary
decoder forces the label to distinguish all total-four words, whereas the interior feature rule
forces it to identify a concrete pair of distinct total-four words.

This is a regression for Definition Y-Compatibility and Claim 6.18 of [alman2025more],
`papers/sources/2404.16349/constituent.tex:235-276,388-436`.  It pinpoints why the fixed leg-map
description at `better_bound/paper.tex:1263-1265,1325-1331,1641-1654,2122-2130` cannot model the
frozen certificate's mixed positive/boundary reader.  It proves no counting, entropy, tensor
restriction, or exponent statement.

## Reference

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
-/

namespace MatrixMultiplication.PairedTotalWeightA5MixedKernelNoGo

universe u

/-- No fixed leg-local label can both preserve the interior ordered-half-total kernel and allow
literal recovery on every boundary word of total weight four.

The first condition is exactly what is needed to obtain the feature-only interior alphabet: words
with the same ordered pair of half totals must receive the same label.  The second condition is
what the boundary identity reader needs: the raw word must be recoverable from that same label.

Proof sketch: use the distinct words `(0,1,2,1)` and `(0,1,1,2)`.  Both have total weight four and
both have ordered half totals `(1,3)`, so the interior rule identifies their labels.  Applying the
boundary decoder then identifies the words themselves, contradicting their first differing digit.
-/
theorem no_legLocalLabel_preserves_pairedTotalWeightA5_mixedKernels
    {Q : Type u} (q : (Fin 4 → Fin 3) → Q)
    (decodeBoundary : Q → Fin 4 → Fin 3)
    (hBoundary :
      ∀ word,
        (word 0 : Nat) + word 1 + word 2 + word 3 = 4 →
        decodeBoundary (q word) = word)
    (hPositive :
      ∀ left right,
        (left 0 : Nat) + left 1 + left 2 + left 3 = 4 →
        (right 0 : Nat) + right 1 + right 2 + right 3 = 4 →
        (left 0 : Nat) + left 1 = (right 0 : Nat) + right 1 →
        (left 2 : Nat) + left 3 = (right 2 : Nat) + right 3 →
        q left = q right) :
    False := by
  let left : Fin 4 → Fin 3 := fun i ↦
    if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 2 else 1
  let right : Fin 4 → Fin 3 := fun i ↦
    if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 1 else 2
  have hleftWeight :
      (left 0 : Nat) + left 1 + left 2 + left 3 = 4 := by
    simp [left]
  have hrightWeight :
      (right 0 : Nat) + right 1 + right 2 + right 3 = 4 := by
    simp [right]
  have hleftHalf :
      (left 0 : Nat) + left 1 = (right 0 : Nat) + right 1 := by
    simp [left, right]
  have hrightHalf :
      (left 2 : Nat) + left 3 = (right 2 : Nat) + right 3 := by
    simp [left, right]
  have hlabels : q left = q right :=
    hPositive left right hleftWeight hrightWeight hleftHalf hrightHalf
  have hwords : left = right := by
    calc
      left = decodeBoundary (q left) := (hBoundary left hleftWeight).symm
      _ = decodeBoundary (q right) := congrArg decodeBoundary hlabels
      _ = right := hBoundary right hrightWeight
  have hdigit := congrFun hwords (2 : Fin 4)
  simp [left, right] at hdigit

end MatrixMultiplication.PairedTotalWeightA5MixedKernelNoGo
