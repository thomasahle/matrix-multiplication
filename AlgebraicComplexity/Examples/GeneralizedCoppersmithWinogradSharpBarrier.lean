/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.GeneralizedCoppersmithWinogradIndependenceUpper

/-! # The sharpened universal Galactic barrier, unconditionally

The sharpened AVW Theorem 7.1 (`avw_theorem_seven_one_sharp` in
`Examples/GeneralizedCoppersmithWinogradBarrier.lean`, constant
`avwTheoremSevenOneSharpConstant = 6/(3 − cornerExponent 2) = 2.027078…`, certified
`≥ 2 + 27/1000`) takes the block-partition entropy bound as a hypothesis, because the entropy
bound (`asymptoticIndependenceNumber_gcwTable_le_rpow_mul`,
`Examples/GeneralizedCoppersmithWinogradIndependenceUpper.lean` — Alman's Theorem 5.3
[Alman2019]) lives downstream of the barrier module in the import graph.  This file sits below
both and discharges the hypothesis, giving the unconditional statement: **no Galactic-method
analysis of any generalized Coppersmith–Winograd tensor, over any field, can prove
`ω < 2 + 27/1000`** [AlmanVassilevskaWilliams2018, Theorem 7.1].
-/

namespace AlgebraicComplexity.Examples

open Tensor

universe u

/-- The sharpened universal Galactic barrier, unconditionally: for every `q` and every
permutation `σ`, `avwTheoremSevenOneSharpConstant ≤ ω_g^coord(CW_q^σ)`.  The entropy hypothesis
of `avw_theorem_seven_one_sharp` is discharged by
`asymptoticIndependenceNumber_gcwTable_le_rpow_mul`. -/
theorem avw_theorem_seven_one_sharp_unconditional (K : Type u) [Field K] (q : ℕ)
    (σ : Equiv.Perm (Fin q)) :
    avwTheoremSevenOneSharpConstant ≤ coordinateGalacticExponent K (gcwTable K (Fin q) σ) :=
  avw_theorem_seven_one_sharp K q σ (fun hq u hu => by
    simpa using asymptoticIndependenceNumber_gcwTable_le_rpow_mul (K := K) σ (by simpa using hq) hu)

/-- Existential form: a single constant `c ≥ 2 + 27/1000` barring the Galactic method on every
generalized CW tensor. -/
theorem avw_theorem_seven_one_exists_sharp_unconditional (K : Type u) [Field K] :
    ∃ c : ℝ, 2 + 27/1000 ≤ c ∧ ∀ (q : ℕ) (σ : Equiv.Perm (Fin q)),
      c ≤ coordinateGalacticExponent K (gcwTable K (Fin q) σ) :=
  ⟨avwTheoremSevenOneSharpConstant, two_add_le_avwTheoremSevenOneSharpConstant,
    fun q σ => avw_theorem_seven_one_sharp_unconditional K q σ⟩

end AlgebraicComplexity.Examples
