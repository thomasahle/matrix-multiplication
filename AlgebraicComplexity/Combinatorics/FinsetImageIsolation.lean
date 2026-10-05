/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Data.Finset.Image

/-!
# Isolation transported through finite images

These elementary lemmas separate finite-image bookkeeping from the mathematical isolation
argument.  They are useful whenever a combinatorial target is represented by native block labels.
-/

namespace Finset

universe u v w x

variable {α : Type u} {β : Type v} {κ : Type w} {κ' : Type x}

/-- Injectivity of a source key passes to an image key whenever equality of image keys reflects
to equality of source keys. -/
theorem injOn_key_image_of_reflects
    [DecidableEq β] (s : Finset α) (f : α → β)
    (sourceKey : α → κ) (imageKey : β → κ')
    (hsource : Set.InjOn sourceKey s)
    (hreflect : ∀ x ∈ s, ∀ y ∈ s,
      imageKey (f x) = imageKey (f y) → sourceKey x = sourceKey y) :
    Set.InjOn imageKey (s.image f) := by
  intro left hleft right hright hkey
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hleft
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hright
  exact congrArg f (hsource hx hy (hreflect x hx y hy hkey))

/-- A source-family unique-fiber statement passes through a finite image whenever equality of
image keys reflects to equality of source keys. -/
theorem image_hasUniqueFibers_of_reflects
    [DecidableEq β] (selected surviving : Finset α) (f : α → β)
    (sourceKey : α → κ) (imageKey : β → κ')
    (hsubset : selected ⊆ surviving)
    (hsource : ∀ x ∈ selected, ∀ y ∈ surviving,
      sourceKey y = sourceKey x → y = x)
    (hreflect : ∀ x ∈ selected, ∀ y ∈ surviving,
      imageKey (f y) = imageKey (f x) → sourceKey y = sourceKey x) :
    selected.image f ⊆ surviving.image f ∧
      ∀ x ∈ selected.image f, ∀ y ∈ surviving.image f,
        imageKey y = imageKey x → y = x := by
  refine ⟨Finset.image_mono f hsubset, ?_⟩
  intro selectedAddress hselected survivingAddress hsurviving hkey
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hselected
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hsurviving
  exact congrArg f (hsource x hx y hy (hreflect x hx y hy hkey))

end Finset
