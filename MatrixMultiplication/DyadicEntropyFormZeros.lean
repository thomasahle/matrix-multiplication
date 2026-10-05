/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.DyadicEntropyFormDefs
import MatrixMultiplication.DyadicNumeratorList

/-!
# Removing zero padding from dyadic entropy forms

These structural lemmas justify compacting padded certificate rows before constructing exact
signed-log forms.  They use no real entropy semantics.
The statements and proofs are preserved from the former `DyadicEntropyForm` monolith; this
definition-preserving refactor introduces no new paper theorem or certificate assertion.

This module carries no claim of its own.  The homogeneous Shannon entropies it represents exactly
are the ones evaluated by the recursive Coppersmith--Winograd constituent analysis of
[alman2025more], `papers/sources/2404.16349/constituent.tex:113-147`, and by the dual certificate
of the Total-Weight manuscript, `better_bound/paper.tex`, `sec:dual` (lines 2274-2307).

## References

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
- *Total-Weight Hashing and Rectangular Volume in the Coppersmith--Winograd Method*.
-/

set_option autoImplicit false

namespace MatrixMultiplication.DyadicEntropyForm

open MatrixMultiplication.SignedDyadicLogForm

/-- Removing zero numerators does not change their sum.

Proof sketch: induct over the list.  A zero head is removed and contributes zero to the sum; a
nonzero head is retained, after which the induction hypothesis identifies the tails. -/
theorem sum_dropZeros (numerators : List ℕ) :
    (dropZeros numerators).sum = numerators.sum := by
  induction numerators with
  | nil => rfl
  | cons numerator numerators ih =>
      cases numerator with
      | zero => simp [dropZeros, ih]
      | succ numerator => simp [dropZeros, ih]

/-- Removing zero numerators leaves the exact Shannon-summand form unchanged.

Proof sketch: induct over the list.  At a zero head, `entropyTermForm` is the zero form and the
zero remover discards it; at a nonzero head both sides retain the same term.  The tail equality is
the induction hypothesis in either case. -/
theorem entropyForm_dropZeros (bits : ℕ) (numerators : List ℕ) :
    entropyForm bits (dropZeros numerators) =
      entropyForm bits numerators := by
  induction numerators with
  | nil => rfl
  | cons numerator numerators ih =>
      cases numerator with
      | zero =>
          change entropyForm bits (dropZeros numerators) =
            entropyForm bits (0 :: numerators)
          rw [ih]
          unfold entropyForm
          simp [entropyTermForm, Form.sum, Form.add, Form.zero]
      | succ numerator =>
          change entropyForm bits ((numerator + 1) :: dropZeros numerators) =
            entropyForm bits ((numerator + 1) :: numerators)
          unfold entropyForm at ih ⊢
          simp only [List.map_cons, Form.sum]
          rw [ih]

/-- Removing zero numerators leaves the exact homogeneous-entropy form unchanged.

Proof sketch: the Shannon-summand part is unchanged by `entropyForm_dropZeros`, while
`sum_dropZeros` shows that the total-mass correction has the same numerator. -/
theorem weightedEntropyForm_dropZeros (bits : ℕ) (numerators : List ℕ) :
    weightedEntropyForm bits (dropZeros numerators) =
      weightedEntropyForm bits numerators := by
  unfold weightedEntropyForm
  rw [entropyForm_dropZeros, sum_dropZeros]

/-- Removing zeros independently from every row leaves the rowwise entropy-form list unchanged.

Proof sketch: map `weightedEntropyForm_dropZeros` over the outer list and use the induction
hypothesis for its tail. -/
theorem map_weightedEntropyForm_dropZeros (bits : ℕ) (rows : List (List ℕ)) :
    rows.map (fun row ↦ weightedEntropyForm bits (dropZeros row)) =
      rows.map (weightedEntropyForm bits) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [List.map_cons]
      rw [weightedEntropyForm_dropZeros, ih]

/-- Removing zeros rowwise before summing homogeneous-entropy forms preserves the exact sum.

Proof sketch: rewrite the nested map by functoriality, then apply
`map_weightedEntropyForm_dropZeros` under `Form.sum`. -/
theorem sum_map_weightedEntropyForm_dropZeros (bits : ℕ) (rows : List (List ℕ)) :
    Form.sum ((rows.map dropZeros).map (weightedEntropyForm bits)) =
      Form.sum (rows.map (weightedEntropyForm bits)) := by
  rw [List.map_map]
  exact congrArg Form.sum (map_weightedEntropyForm_dropZeros bits rows)

end MatrixMultiplication.DyadicEntropyForm
