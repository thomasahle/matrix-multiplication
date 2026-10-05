/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.CompatibleSplitCountDefs
import AlgebraicComplexity.MatrixMultiplication.SegmentMultiplicityReflect
import AlgebraicComplexity.MatrixMultiplication.SegmentMultiplicityJointWord

/-!
# Compatibility from reflected boundary profiles

This is the count argument in [duan2023faster], section 6.1,
`papers/sources/2210.10173/global_value.tex:63-71`, claim
`lemma:triple_implies_compatible`, concluding `def:global-compatible` at lines 44-50.
The retained Z word is typical. On each boundary segment, a retained other-leg word has
the prescribed reflected profile and is pointwise the reflection of the Z word.
The paper's displayed chain at line 70 cancels that involution to recover the Z profile.

The alphabet, involution and counts are parameters. A boundary witness is supplied only on
the segment where it is used: no agreement outside that segment is required. The native
support and legwise keep rules yielding these witnesses belong to the downstream client.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.CompatibleSplit.SplitRequirements

universe u v

variable {L : Type u} {Z : Type v} [Fintype L] [DecidableEq L]
variable {n m : Nat}

/-- Typicalness and the paper's reflected other-leg counts imply compatibility.
Proof sketch: on each boundary segment, evaluate the involutive count identity at `f l`,
use the retained profile, and cancel `f (f l)` on both sides. -/
theorem isCompatible_of_reflectedBoundary (S : SplitRequirements (Fin m) L Z)
    (comp : Fin n → Fin m) (zw : Fin n → L) (f : L → L)
    (hf : Function.Involutive f) (htyp : S.IsTypical (S.zIndex ∘ comp) zw)
    (hboundary : ∀ t, S.boundary t → ∃ bw : Fin n → L,
      segmentMultiplicity comp bw t = (fun l => S.splitCount t (f l)) ∧
      ∀ i, comp i = t → bw i = f (zw i)) :
    S.IsCompatible comp zw := by
  classical
  refine ⟨?_, htyp⟩
  intro t ht l
  obtain ⟨bw, hkeep, hreflect⟩ := hboundary t ht
  rw [multiplicity_jointWord_eq_segmentMultiplicity]
  have hr := segmentMultiplicity_comp_involutive comp bw zw t f hf hreflect
  have hcount := (congrFun hr (f l)).symm.trans (congrFun hkeep (f l))
  simpa only [hf l] using hcount

end AlgebraicComplexity.CompatibleSplit.SplitRequirements
