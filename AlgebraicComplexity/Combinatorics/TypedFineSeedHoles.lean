/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.HashingSeedHoleMass

set_option autoImplicit false

/-!
# Hole normalization on the prescribed fine-block alphabet

Claims 6.18 and 6.21 of [alman2025more] count holes among the useful fine blocks of each
retained interface.  Counting over the full raw word alphabet instead would not establish the
required relative bound.  Identify a fixed finite reference alphabet with an owner-dependent
subset of raw labels, and test compatibility after that embedding.  The resulting seed holes
map exactly onto the raw seed holes in the embedded subset.  Their cardinality and relative
normalization therefore agree without a loss depending on the size of the raw alphabet.

The embedding is allowed to depend on the owner, as it does when a position permutation moves
the reference constituent to a retained constituent of the same exact type.  No independence
of the two compatibility cleanups is assumed.  Applying a two-leg seed theorem to the reference
alphabets still chooses one seed for both legs.  A tensor client must supply the actual reference
embeddings and prove that literal cleanup deletions are charged to these holes.

## Reference

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*, Claims 6.18 and 6.21;
  `papers/sources/2404.16349/constituent.tex:350-374,462-479`.
-/

namespace AlgebraicComplexity.ProgressionHash.LegalTriple

universe u v w x

variable {R : Type u} [Field R] {ι : Type v} {target : R}
variable {A : Type w} {B : Type x}

/-- Reading a reference label through an owner-dependent map leaves its competitor family
exactly equal to that of the corresponding raw label. -/
theorem fineCompetitors_pullbackFine
    (ambient : Finset (LegalTriple R ι target))
    (compat : LegalTriple R ι target → B → LegalTriple R ι target → Prop)
    (label : LegalTriple R ι target → A → B)
    (owner : LegalTriple R ι target) (fine : A) :
    fineCompetitors ambient (fun t a c ↦ compat t (label t a) c) owner fine =
      fineCompetitors ambient compat owner (label owner fine) := rfl

variable [Fintype ι] [Fintype A] [Fintype B] [DecidableEq B]

/-- The seed holes in the reference alphabet embed onto precisely the raw holes belonging to
that owner's prescribed interface.  The raw alphabet may contain arbitrarily many other labels.

Proof sketch: a reference block and its image have identical competitors.  Filtering commutes
with the injective map, so the two finite sets agree exactly. -/
theorem map_seedSharedHoles_pullbackFine
    (ambient : Finset (LegalTriple R ι target))
    (compat : LegalTriple R ι target → B → LegalTriple R ι target → Prop)
    (label : LegalTriple R ι target → A ↪ B)
    (seed : Seed R ι) (owner : LegalTriple R ι target) (bucket : R) :
    (seedSharedHoles ambient (fun t a c ↦ compat t (label t a) c)
      seed owner bucket).map (label owner) =
        (Finset.univ.map (label owner)).filter
          (fun b ↦ b ∈ seedSharedHoles ambient compat seed owner bucket) := by
  classical
  unfold seedSharedHoles
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Finset.filter_map]
  rfl

/-- Counting reference holes is exactly counting raw holes inside the prescribed image. -/
theorem card_seedSharedHoles_pullbackFine
    (ambient : Finset (LegalTriple R ι target))
    (compat : LegalTriple R ι target → B → LegalTriple R ι target → Prop)
    (label : LegalTriple R ι target → A ↪ B)
    (seed : Seed R ι) (owner : LegalTriple R ι target) (bucket : R) :
    (seedSharedHoles ambient (fun t a c ↦ compat t (label t a) c)
      seed owner bucket).card =
        ((Finset.univ.map (label owner)).filter
          (fun b ↦ b ∈ seedSharedHoles ambient compat seed owner bucket)).card := by
  rw [← map_seedSharedHoles_pullbackFine, Finset.card_map]

/-- A division-free relative-hole bound on the reference alphabet is equivalent to the same
bound on the owner's actual interface.  Its denominator is the interface size, not the raw
alphabet size. -/
theorem relative_seedSharedHoles_pullbackFine_iff
    (ambient : Finset (LegalTriple R ι target))
    (compat : LegalTriple R ι target → B → LegalTriple R ι target → Prop)
    (label : LegalTriple R ι target → A ↪ B)
    (seed : Seed R ι) (owner : LegalTriple R ι target) (bucket : R) (D : ℕ) :
    D * ((Finset.univ.map (label owner)).filter
        (fun b ↦ b ∈ seedSharedHoles ambient compat seed owner bucket)).card ≤
        (Finset.univ.map (label owner)).card ↔
      D * (seedSharedHoles ambient (fun t a c ↦ compat t (label t a) c)
        seed owner bucket).card ≤ Fintype.card A := by
  rw [← card_seedSharedHoles_pullbackFine, Finset.card_map, Finset.card_univ]

end AlgebraicComplexity.ProgressionHash.LegalTriple
