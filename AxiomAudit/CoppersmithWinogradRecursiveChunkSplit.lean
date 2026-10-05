/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveChunkSplit
import AxiomAudit.Command

set_option autoImplicit false

/-!
# Axiom audit for recursive half-chunk splitting of CW constituents

These checks cover every public declaration of the labelled consecutive split of a native
Coppersmith--Winograd chunk into its two child chunks, together with its inverse join and the
identification of that join with the standard consecutive-halves map.

The split transcribes the sentence of [alman2025more] that a level-`l` index sequence splits into
two level-`(l-1)` sequences, `papers/sources/2404.16349/constituent.tex:41-47`, over the complete
split distributions of `papers/sources/2404.16349/prelim.tex:249-269`.

The audited module carries the equivalences only.  No total-weight quotient, hashing predicate,
compatibility count, tensor restriction, asymptotic rate, certificate or exponent endpoint is
asserted here.

## References

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
-/

open AlgebraicComplexity.Examples

#assert_axioms cwRecursiveChunkSplit
#assert_axioms cwRecursiveChunkSplit_encoded
#assert_axioms cwRecursiveChunkJoin
#assert_axioms cwRecursiveChunkJoin_encoded
#assert_axioms cwRecursiveChunkSplit_weight_add
#assert_axioms cwChunkParameter_succ
#assert_axioms positiveWordEquiv_positiveWordCast_apply
#assert_axioms cwStandardChunkJoin
#assert_axioms cwStandardChunkJoin_apply
#assert_axioms cwStandardChunkJoin_encoded
#assert_axioms cwRecursiveChunkJoin_eq_standard
