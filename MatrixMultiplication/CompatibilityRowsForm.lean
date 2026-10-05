/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.CompatibilityRows
import MatrixMultiplication.DyadicEntropyFormEval

/-!
# Exact signed-log forms for compatibility rows

This numerical adapter is separated from `CompatibilityRows.lean` so semantic rate theorems do
not import the signed-log certificate machinery.  Both files use the same namespace, preserving
the established `CompatibilityRows.form` API for evaluator clients.

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

namespace MatrixMultiplication.SimplifiedExponentRootRecurrence

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicEntropyForm
open MatrixMultiplication.SignedDyadicLogForm

noncomputable section

namespace CompatibilityRows

/-- Exact signed-log form of one compatibility branch. -/
def form (bits : ℕ) (rows : CompatibilityRows) : Form :=
  Form.sub
    (Form.sub (weightedEntropyForm bits rows.pooled)
      (Form.sum (rows.first.map (weightedEntropyForm bits))))
    (Form.sum (rows.groups.map (weightedEntropyForm bits)))

/-- Evaluation of the exact signed-log form agrees with the real entropy expression. -/
theorem form_eval (bits : ℕ) (rows : CompatibilityRows) :
    Form.eval bits (rows.form bits) = rows.rate bits := by
  rw [form, Form.eval_sub, Form.eval_sub, weightedEntropyForm_eval,
    Form.eval_sum, Form.eval_sum]
  have heval (rowFamily : List (List ℕ)) :
      (List.map (Form.eval bits)
          (rowFamily.map (weightedEntropyForm bits))).sum =
        (rowFamily.map (weightedEntropyList bits)).sum := by
    induction rowFamily with
    | nil => rfl
    | cons row rows ih =>
        simp only [List.map_cons, List.sum_cons, weightedEntropyForm_eval, ih]
  unfold rate
  rw [heval rows.first, heval rows.groups]

end CompatibilityRows

end

end MatrixMultiplication.SimplifiedExponentRootRecurrence
