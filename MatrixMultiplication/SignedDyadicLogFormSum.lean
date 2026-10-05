/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SignedDyadicLogFormDefs

set_option autoImplicit false

/-!
# Splitting a signed-log form sum along a list append

`Form.sum` folds `Form.add` over a list, and `Form.add` concatenates term lists while adding
constants.  Both operations are therefore associative on the nose, and a `Form.sum` over an
appended list splits into the sum of the two halves.

This is a library fact about the exact-form algebra, independent of any certificate.  It exists
because generated payloads need to check a large `Form.sum` in bounded pieces: a producer emits one
literal per chunk of the summand list, proves each chunk against its own literal by `rfl`, and then
reassembles with `sum_append` instead of reducing the whole sum at once.  Without it the only route
is a single reduction whose memory cost grows with the entire list — measured at over 3 GB for a
153-state integer dual, against a 1 GB budget.

Nothing here evaluates a form; `Form.eval` is not even imported.  These are structural identities
about constants and term lists.
-/

namespace MatrixMultiplication.SignedDyadicLogForm.Form

/-- Adding exact forms is associative: constants add associatively and term lists concatenate
associatively. -/
theorem add_assoc (left middle right : Form) :
    add (add left middle) right = add left (add middle right) := by
  simp [add, Int.add_assoc, List.append_assoc]

/-- The empty form is a left unit for addition. -/
@[simp] theorem zero_add (form : Form) : add zero form = form := by
  simp [add, zero]

/-- The empty form is a right unit for addition. -/
@[simp] theorem add_zero (form : Form) : add form zero = form := by
  simp [add, zero]

/-- **A form sum splits along an append.**

The reassembly law for bounded generated payloads: a producer checks `Form.sum` on each chunk of
the summand list separately and combines the results here, so no proof ever reduces the whole
list.

Proof sketch: induct on the left list.  The empty case is left unitality; the cons case rewrites by
the induction hypothesis and reassociates one addition. -/
theorem sum_append (left right : List Form) :
    sum (left ++ right) = add (sum left) (sum right) := by
  induction left with
  | nil => simp [sum]
  | cons form forms ih =>
      simp only [List.cons_append, sum, ih, add_assoc]

/-- Iterating `sum_append` over an explicit chunking: the sum of a flattened list of chunks is the
sum of the chunks' sums.

This is the shape a generated payload actually uses — one literal per chunk, then one application
here — so the reassembly costs a single fold over the chunk list rather than over the whole
summand list. -/
theorem sum_flatten (chunks : List (List Form)) :
    sum chunks.flatten = sum (chunks.map sum) := by
  induction chunks with
  | nil => rfl
  | cons chunk chunks ih =>
      simp only [List.flatten_cons, List.map_cons, sum, sum_append, ih]

end MatrixMultiplication.SignedDyadicLogForm.Form
