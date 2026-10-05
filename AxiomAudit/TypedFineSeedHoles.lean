/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Combinatorics.TypedFineSeedHoles
import Mathlib.Data.Fin.Embedding

set_option autoImplicit false

/-!
# Audit of prescribed-interface hole normalization

The finite reference-alphabet transport used in Claims 6.18/6.21 of [alman2025more].
-/

open AlgebraicComplexity.ProgressionHash.LegalTriple

#assert_axioms fineCompetitors_pullbackFine
#assert_axioms map_seedSharedHoles_pullbackFine
#assert_axioms card_seedSharedHoles_pullbackFine
#assert_axioms relative_seedSharedHoles_pullbackFine_iff

/-! A semantic client: a two-block reference interface inside a three-block raw alphabet.
The conclusion has denominator two for every ambient family, compatibility predicate and seed.
No upper bound on holes or existence of a good seed is assumed by this transport identity. -/

example {R : Type*} [Field R] {ι : Type*} [Fintype ι] {target : R}
    (ambient : Finset (AlgebraicComplexity.ProgressionHash.LegalTriple R ι target))
    (compat : AlgebraicComplexity.ProgressionHash.LegalTriple R ι target → Fin 3 →
      AlgebraicComplexity.ProgressionHash.LegalTriple R ι target → Prop)
    (seed : AlgebraicComplexity.ProgressionHash.Seed R ι)
    (owner : AlgebraicComplexity.ProgressionHash.LegalTriple R ι target)
    (bucket : R) (D : ℕ) :
    let embed : Fin 2 ↪ Fin 3 := Fin.castLEEmb (by omega)
    D * ((Finset.univ.map embed).filter
        (fun b ↦ b ∈ seedSharedHoles ambient compat seed owner bucket)).card ≤ 2 ↔
      D * (seedSharedHoles ambient (fun t a c ↦ compat t (embed a) c)
        seed owner bucket).card ≤ 2 := by
  dsimp only
  simpa only [Finset.card_map, Finset.card_univ, Fintype.card_fin] using
    (relative_seedSharedHoles_pullbackFine_iff ambient compat
      (fun _ ↦ Fin.castLEEmb (by omega : 2 ≤ 3)) seed owner bucket D)
