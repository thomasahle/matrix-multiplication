/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradPartitionCore
import AlgebraicComplexity.MatrixMultiplication.OneSliceRestriction

/-!
# Coordinate maps for base zero-coordinate CW constituents

This definition-only module exposes the three coordinate projections used by the zero-`Z`
Coppersmith--Winograd constituents.  Their tensor identities live in separate small modules so
each finite coordinate proof elaborates with bounded memory.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity

universe u

variable (K : Type u) [CommRing K]
variable (q : ℕ)

/-- Direct target-to-source coordinate map for the typed `(2,0,0)` constituent. -/
def cw200OneSliceIndex : ∀ c,
    MMIndex 1 1 1 c → CWBlockIndex q (cw200 c)
  | .X => fun _ ↦ ()
  | .Y => fun _ ↦ ()
  | .Z => fun _ ↦ ()

/-- Direct local-block restriction maps for the typed `(2,0,0)` constituent. -/
def cw200OneSliceMap : ∀ c,
    CWPartitionBlockSpace K q c (cw200 c) →ₗ[K] MMSpace K 1 1 1 c :=
  fun c ↦ LinearMap.funLeft K K (cw200OneSliceIndex q c)

/-- Direct target-to-source coordinate map for the typed `(0,2,0)` constituent. -/
def cw020OneSliceIndex : ∀ c,
    MMIndex 1 1 1 c → CWBlockIndex q (cw020 c)
  | .X => fun _ ↦ ()
  | .Y => fun _ ↦ ()
  | .Z => fun _ ↦ ()

/-- Direct local-block restriction maps for the typed `(0,2,0)` constituent. -/
def cw020OneSliceMap : ∀ c,
    CWPartitionBlockSpace K q c (cw020 c) →ₗ[K] MMSpace K 1 1 1 c :=
  fun c ↦ LinearMap.funLeft K K (cw020OneSliceIndex q c)

/-- Direct target-to-source coordinate map for the typed `(1,1,0)` constituent. -/
def cw110OneSliceIndex : ∀ c,
    MMIndex 1 q 1 c → CWBlockIndex q (cw110 c)
  | .X => fun a ↦ a.2
  | .Y => fun a ↦ a.1
  | .Z => fun _ ↦ ()

/-- Direct local-block restriction maps for the typed `(1,1,0)` constituent. -/
def cw110OneSliceMap : ∀ c,
    CWPartitionBlockSpace K q c (cw110 c) →ₗ[K] MMSpace K 1 q 1 c :=
  fun c ↦ LinearMap.funLeft K K (cw110OneSliceIndex q c)

/-- All three zero-`Z` base certificates use definitionally the same map on their shared block. -/
theorem cwZeroBaseOneSliceMap_Z_coherent :
    cw200OneSliceMap K q .Z = cw020OneSliceMap K q .Z ∧
      cw020OneSliceMap K q .Z = cw110OneSliceMap K q .Z := by
  exact ⟨rfl, rfl⟩

end AlgebraicComplexity.Examples
