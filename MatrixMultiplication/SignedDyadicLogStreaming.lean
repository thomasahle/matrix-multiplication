/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SignedDyadicLogCanonical
import MatrixMultiplication.SignedDyadicLogStreamingDefs

/-!
# Soundness laws for streaming signed dyadic logarithm forms

This module proves that bounded streaming is only a change in certificate presentation.  Folding
an appended shard list resumes from the first fold's checkpoint, and real evaluation of the final
accumulator equals evaluation of the ordinary sum of all shards.

Generated equality clients need import only `SignedDyadicLogStreamingDefs`; semantic consumers use
this module to transport a checked accumulator equality to the represented entropy or exponent.
-/

namespace MatrixMultiplication.SignedDyadicLogForm.Form

open MatrixMultiplication.SignedDyadicLogForm

noncomputable section

/-! ## Syntactic checkpoint calculus -/

/-- Folding no shards leaves the initial accumulator unchanged. -/
@[simp] theorem streamFoldFrom_nil (initial : Form) :
    streamFoldFrom initial [] = initial := rfl

/-- Folding a leading shard first steps the accumulator, then processes the tail. -/
theorem streamFoldFrom_cons (initial shard : Form) (shards : List Form) :
    streamFoldFrom initial (shard :: shards) =
      streamFoldFrom (streamStep initial shard) shards := rfl

/-- Folding an append is the same as resuming from the left fold's final accumulator.

Proof sketch: this is the standard `foldl` append law specialized to `streamStep`. -/
theorem streamFoldFrom_append (initial : Form) (left right : List Form) :
    streamFoldFrom initial (left ++ right) =
      streamFoldFrom (streamFoldFrom initial left) right := by
  exact List.foldl_append

/-- A checked intermediate accumulator may replace the corresponding prefix fold.

Proof sketch: split the fold at the prefix with `streamFoldFrom_append`, then rewrite by the
certificate's checkpoint equality. -/
theorem streamFoldFrom_append_of_checkpoint (initial checkpoint : Form)
    (left right : List Form) (hcheckpoint : streamFoldFrom initial left = checkpoint) :
    streamFoldFrom initial (left ++ right) = streamFoldFrom checkpoint right := by
  rw [streamFoldFrom_append, hcheckpoint]

/-- A zero-started fold over an append resumes from the left zero-started fold. -/
theorem streamFold_append (left right : List Form) :
    streamFold (left ++ right) = streamFoldFrom (streamFold left) right := by
  exact streamFoldFrom_append zero left right

/-! ## Real-evaluation soundness -/

/-- One streaming merge represents the sum of its accumulator and shard.

Proof sketch: structural canonicalization preserves evaluation, and `Form.add` evaluates as real
addition. -/
theorem eval_streamStep (bits : ℕ) (accumulator shard : Form) :
    eval bits (streamStep accumulator shard) =
      eval bits accumulator + eval bits shard := by
  rw [streamStep, eval_structuralFastCanonical, eval_add]

/-- Streaming from an arbitrary accumulator represents that accumulator plus every shard.

Proof sketch: induct over the shard list.  The successor case uses `eval_streamStep` and the
induction hypothesis, then reassociates addition to match `Form.sum`. -/
theorem eval_streamFoldFrom (bits : ℕ) (initial : Form) (shards : List Form) :
    eval bits (streamFoldFrom initial shards) =
      eval bits initial + eval bits (sum shards) := by
  induction shards generalizing initial with
  | nil => simp [streamFoldFrom, sum]
  | cons shard shards ih =>
      rw [streamFoldFrom_cons, ih, eval_streamStep]
      simp only [sum, eval_add]
      ring

/-- A zero-started streaming fold represents the ordinary exact sum of its shards.

Proof sketch: specialize `eval_streamFoldFrom` to the zero accumulator and use `eval_zero`. -/
theorem eval_streamFold (bits : ℕ) (shards : List Form) :
    eval bits (streamFold shards) = eval bits (sum shards) := by
  rw [streamFold, eval_streamFoldFrom, eval_zero, zero_add]

end

end MatrixMultiplication.SignedDyadicLogForm.Form
