/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightCore
import AlgebraicComplexity.MatrixMultiplication.CompatibilityTargetCore
import AlgebraicComplexity.Tensor.PartitionedCore

set_option autoImplicit false

/-!
# Finite tagged and oriented CW compatibility cells

This dependency-light client names the finite cell alphabet obtained by adjoining a region tag to
the three bounded coarse digits of a Coppersmith--Winograd constituent.  It also gives the forgetful
map to the natural-valued coarse index used by compatibility targets.  Position sequences,
normalizing permutations, and tensor cleanup remain in downstream modules.

The cell is the finite encoding of the exact and pooled complete-split cells in [alman2025more],
Claim 6.18 (`papers/sources/2404.16349/constituent.tex:404-429`), and of the tagged empirical cell
type used in the Total-Weight whole-fiber transport
(`better_bound/paper.tex:1692-1744,1771-1802`).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe v

/-- Finite version of a tagged/oriented coarse cell.  The compatibility model stores the three
digits as naturals, but normalization must use this bounded alphabet to invoke finite word-type
permutations. -/
abbrev CWOrientedCoarseCell (Part : Type v) (depth : ℕ) :=
  Part × BlockAddress (fun _c ↦ CWCoarseDigit depth)

/-- Forget the finite bounds on the three coarse digits. -/
def cwOrientedCoarseCellToIndex {Part : Type v} {depth : ℕ} :
    CWOrientedCoarseCell Part depth → CoarseIndex Part
  | ⟨part, digits⟩ =>
      { part := part
        x := digits .X
        y := digits .Y
        z := digits .Z }

end AlgebraicComplexity.Examples
