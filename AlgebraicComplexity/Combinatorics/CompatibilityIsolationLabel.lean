/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.CompatibilityHashingIsolation

set_option autoImplicit false

/-!
# Compatibility isolation for an arbitrary target label

Claim 6.18 of Alman--Duan--Vassilevska Williams--Xu--Xu--Zhou, *More Asymmetry
Yields Faster Matrix Multiplication*, isolates targets using compatibility and then reads the
result through a finer quotient label; see
`papers/sources/2404.16349/constituent.tex:376-440`.  This file records the elementary adapter
between those two steps.

The label need not be a tensor leg.  The sole semantic premise says that two marked targets with
the same label are compatible.  Hence a compatibility-isolated marked subfamily is injective
under the label.  This prevents a client from identifying a richer quotient label with a coarser
tensor-leg index merely to use a leg-specific isolation theorem.
-/

namespace AlgebraicComplexity.ProgressionHash.Seed

universe u v

variable {τ : Type u} {Label : Type v}

/-- A selected marked family that is compatibility-isolated inside `filtered` is injective under
any label whose equality implies compatibility on marked targets. -/
theorem compatibilityIsolatedTargets_injectiveOn_label
    (marked filtered selected : Finset τ)
    (compatible : τ → τ → Prop) (label : τ → Label)
    (hselectedMarked : selected ⊆ marked)
    (hselectedIsolated : selected ⊆ compatibilityIsolatedTargets filtered compatible)
    (hcomplete : ∀ left ∈ marked, ∀ right ∈ marked,
      label left = label right → compatible left right) :
    Set.InjOn label selected := by
  intro left hleft right hright hlabel
  have hleftIsolated :=
    (mem_compatibilityIsolatedTargets filtered compatible left).mp
      (hselectedIsolated hleft)
  have hrightFiltered :=
    (mem_compatibilityIsolatedTargets filtered compatible right).mp
      (hselectedIsolated hright) |>.1
  exact (hleftIsolated.2 right hrightFiltered
    (hcomplete left (hselectedMarked hleft) right (hselectedMarked hright) hlabel)).symm

private example :
    Set.InjOn (fun i : Fin 2 ↦ i)
      (Finset.univ : Finset (Fin 2)) := by
  apply compatibilityIsolatedTargets_injectiveOn_label
    (marked := Finset.univ) (filtered := Finset.univ) (selected := Finset.univ)
    (compatible := (· = ·))
  · exact Finset.Subset.rfl
  · intro i _
    simp [compatibilityIsolatedTargets]
  · intro left _ right _ h
    exact h

end AlgebraicComplexity.ProgressionHash.Seed
