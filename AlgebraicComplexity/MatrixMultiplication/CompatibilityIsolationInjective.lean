/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.CompatibilityIsolationCounting

/-!
# Lossless compatibility isolation on an injective support

Compatibility isolation is unnecessary when two elementary facts hold: compatibility with a
label forces the candidate's pivot coordinate to equal that label, and the pivot coordinate is
injective on the ambient support.  This file records that reusable finite principle.  In this
situation every ambient address is uniquely compatible, the isolated support is the entire
ambient support, and the directed competitor incidence is exactly zero.

The hypotheses are deliberately local.  They mention neither a tensor degeneration nor an
assembled product, so client constructions cannot hide their extraction theorem inside this
counting interface.
-/

namespace AlgebraicComplexity.Tensor

universe u

variable {A : Leg → Type u}

/-- If compatibility determines the pivot coordinate and that coordinate is injective on the
ambient family, every ambient address survives compatibility isolation. -/
theorem compatibilityIsolatedSupport_eq_ambient_of_injOn_of_rigid
    (ambient : Finset (BlockAddress A)) (pivot : Leg)
    (compatible : A pivot → BlockAddress A → Prop)
    (hinjective : Set.InjOn (fun address : BlockAddress A ↦ address pivot) ambient)
    (hrigid : ∀ label address, compatible label address → label = address pivot) :
    compatibilityIsolatedSupport ambient pivot compatible = ambient := by
  classical
  apply Finset.Subset.antisymm
  · exact compatibilityIsolatedSupport_subset ambient pivot compatible
  · intro address haddress
    rw [mem_compatibilityIsolatedSupport]
    refine ⟨haddress, ?_⟩
    intro other hother hcompatible
    exact hinjective hother haddress (hrigid (address pivot) other hcompatible).symm

variable [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

/-- Under the same rigidity and injectivity hypotheses, there are no directed compatibility
competitors. -/
theorem compatibilityCompetitorIncidence_eq_zero_of_injOn_of_rigid
    (ambient : Finset (BlockAddress A)) (pivot : Leg)
    (compatible : A pivot → BlockAddress A → Prop)
    (hinjective : Set.InjOn (fun address : BlockAddress A ↦ address pivot) ambient)
    (hrigid : ∀ label address, compatible label address → label = address pivot) :
    compatibilityCompetitorIncidence ambient pivot compatible = 0 := by
  classical
  have hcompetitors (address : BlockAddress A) (haddress : address ∈ ambient) :
      compatibilityCompetitors ambient pivot compatible address = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro other hother
    have hmem :=
      (mem_compatibilityCompetitors ambient pivot compatible address other).mp hother
    have heq : other = address :=
      hinjective hmem.1 haddress (hrigid (address pivot) other hmem.2.2).symm
    exact hmem.2.1 heq
  unfold compatibilityCompetitorIncidence
  apply Finset.sum_eq_zero
  intro address haddress
  rw [hcompetitors address haddress]
  rfl

end AlgebraicComplexity.Tensor
