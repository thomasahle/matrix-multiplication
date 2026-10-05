/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SignedDyadicLogCanonicalDefs

/-!
# Executable streaming folds for signed dyadic logarithm forms

Large generated certificate branches should not elaborate one enormous equality.  They can instead
split their terms into bounded shards and fold those shards through a canonical accumulator.  This
definition-only module provides that executable fold without importing real logarithms or any
soundness proof.

Each step concatenates one shard with the accumulator and applies the explicit-fuel structural
canonicalizer, whose internal term sort is balanced.  The outer operation is still a left fold:
bounded input shards alone neither bound the growing accumulator nor imply balanced total work.
A certificate client should establish that its canonical forms use a bounded key universe before
relying on small checkpoint equalities; clients with broadly growing keys should use a tree-shaped
accumulator instead.  `SignedDyadicLogStreaming.lean` proves only the append and real-evaluation
laws, independent of either performance condition.
-/

namespace MatrixMultiplication.SignedDyadicLogForm.Form

open MatrixMultiplication.SignedDyadicLogForm

/-- Merge one bounded shard into an already accumulated form and canonicalize the result. -/
@[reducible] def streamStep (accumulator shard : Form) : Form :=
  structuralFastCanonical (add accumulator shard)

/-- Fold a list of bounded shards starting from an explicit accumulator. -/
@[reducible] def streamFoldFrom (initial : Form) (shards : List Form) : Form :=
  shards.foldl streamStep initial

/-- Fold a list of bounded shards starting from the exact zero form. -/
@[reducible] def streamFold (shards : List Form) : Form :=
  streamFoldFrom zero shards

end MatrixMultiplication.SignedDyadicLogForm.Form
