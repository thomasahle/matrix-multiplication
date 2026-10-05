/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd112SymmetricHashEncoding
import AlgebraicComplexity.Examples.CoppersmithWinograd112SymmetricTypedLeaf
import AlgebraicComplexity.MatrixMultiplication.RationalTypedLeafMarginalHashing

/-!
# Generic fixed-marginal hashing instantiated for the symmetric CW `112` leaf

This module is the finite semantic handoff between the symmetric 64-address profile and affine
hashing.  The profile, entropy, dimensions, constituent restrictions, and field encoding are all
proved in separate modules; here they are assembled through the paper-independent
`RationalTypedLeaf` marginal-family API.

The resulting theorem is intentionally finite.  It supplies the marked and ambient families and
the exact competitor bound needed by the generic good-seed theorem.  No asymptotic estimate or
value axiom is introduced here.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

variable (K : Type u) [CommRing K]

/-- The support-indexed symmetric CW leaf uses the actual block coordinate of every partition leg.

Proof sketch: unfold the source reindexing.  The support equivalence decodes the three source
addresses, and `cw112SymmetricAddress` reassembles exactly the compound block read at leg `c`. -/
theorem cw112SymmetricPartitionRationalTypedLeaf_isSupportCoordinate
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    RationalTypedLeaf.IsSupportCoordinate
      (cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG) := by
  intro c s
  let source := (cw112SymmetricPartitionSupportEquiv K q).symm s
  have hs : cw112SymmetricPartitionSupportEquiv K q source = s :=
    (cw112SymmetricPartitionSupportEquiv K q).apply_symm_apply s
  change (cw112SymmetricRationalTypedLeaf q L G hq hL hG).coordinate c source = s.1 c
  rw [← hs]
  rfl

/-- The symmetric CW marked family is contained in its complete three-marginal ambient family. -/
theorem cw112SymmetricMarkedWords_subset_ambientWords
    (q L G k : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    (cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).markedWords k ⊆
      (cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).ambientWords k := by
  exact RationalTypedLeaf.markedWords_subset_ambientWords _
    (cw112SymmetricPartitionRationalTypedLeaf_isSupportCoordinate K q L G hq hL hG) k

end AlgebraicComplexity.Examples
