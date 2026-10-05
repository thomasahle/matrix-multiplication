/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoOrbitRowSixAmbientWeight
import AlgebraicComplexity.MatrixMultiplication.CyclicValueNormalization

set_option autoImplicit false

/-!
# Row 6 of the fine leaf's orbit premise, hypothesis-free

Layer 4 (`AlgebraicComplexity/Examples/`).  Image 150 made the symmetric ambient power a
`HasTauWeight` at any value bounded by the volume power sum of its surviving triples; this module
instantiates that at the canonical hash modulus, Behrend buckets and a surviving seed, and thereby
discharges the binder image 148 left open.  Row `6` of image 135's `R3` premise is then
hypothesis-free at `eps = dwz63LeafMargin`.

## The paper

`[duan2023faster]` arXiv:2210.10173, `second_power_appendix.tex:26-45` (proof of
`lem:non-rot-values` (d)): the symmetric hashing method applied to `sym₃(\T)` yields
`binom(m,m/2)² binom(m,2a'm,b'm,b'm) · 2^{-o(m)}` disjoint triples, each isomorphic to
`⟨q^{(4a'+2b')m}, q^{(4a'+2b')m}, q^{(4a'+2b')m}⟩`, giving
`V^{(3)}_τ(T_{1,1,2}, α̃_Z) ≥ (…)^{1/(3m)} · q^{(4a'+2b')τ}`; the optimisation `b' =
1/(2+q^{3τ})` is Coppersmith and Winograd, *Matrix multiplication via arithmetic progressions*, J.
Symbolic Computation 9 (1990), pp. 270--272.  The level-two free-`b` instance carried here is
`global_value.tex:341-348`, at the table's `b = 0.00021015`.

## Deviation, flagged (unchanged from image 150)

The paper's `V^{(3)}_τ` is the limit of the `1/(3m)`-th root; the repository keeps the finite
volume power sum in `HasTauWeight` and puts the asymptotics in the growth module.  The two meet
here: the committed `CyclicExtractionCertificate.rpow_three_mul_power_le_volumePowerSum`
(`MatrixMultiplication/CyclicValueNormalization.lean:59`) undoes the certificate's root exactly, so
the finite volume power sum dominates `exp (dwz112LogValue - 10^(-22)) ^ (3 · dwz112Mass · k)` ---
the published value backed off by the round reserve of `dwz112_exp_le_leafTerm`.  Only the
exponent has to be converted from a real to a natural power, by `Real.rpow_natCast`.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `second_power_appendix.tex:26-45`, `global_value.tex:341-348`; Don
Coppersmith and Shmuel Winograd, *Matrix multiplication via arithmetic progressions*, J. Symbolic
Computation 9 (1990), pp. 270--272.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v

variable (K : Type u) [Field K]

/-- **Eventually, the symmetric ambient power carries the published `(1,1,2)` value.**

The canonical modulus, buckets and a surviving seed come from the growth module; the value is the
volume power sum of the survivors, and it dominates `exp (dwz112LogValue - 10^(-22))` raised to
the leaf's total index length `3 · dwz112Mass · k`.

`hq` is bound as a named hypothesis rather than inlined, because an inline tactic proof in this
dependent argument position makes the statement itself time out at `isDefEq`. -/
theorem exists_eventually_cw112SymmetricAmbientHasTauWeight (hq : 0 < 6) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      ∃ (_hkpos : 0 < k)
        (seed : CW112SymmetricCanonicalSeed K 6 dwz112L dwz112G k hq dwz112L_pos dwz112G_pos)
        (_hne : Nonempty (CW112SymmetricCanonicalSurvivor K 6 dwz112L dwz112G k hq
          dwz112L_pos dwz112G_pos seed))
        (value : ℝ),
        HasTauWeight K
          (cw112SymmetricAmbientPartitionedPower K 6 dwz112L dwz112G k
            (cw112SymmetricHashModulus K 6 dwz112L dwz112G k hq dwz112L_pos dwz112G_pos)
            hq dwz112L_pos dwz112G_pos
            (cw112SymmetricHashModulus_ge_twentySeven K 6 dwz112L dwz112G k hq
              dwz112L_pos dwz112G_pos)).realize dwz63Tau value ∧
        Real.exp (dwz112LogValue - 1 / 10 ^ 22) ^ (3 * (dwz112Mass * k)) ≤ value := by
  obtain ⟨N, hN⟩ := exists_eventually_cw112SymmetricLimitLowerTerm_le_certificate
    K dwz63Tau 6 dwz112L dwz112G hq dwz112L_pos dwz112G_pos
    (dwz112InnerCopyBase_pos K) (dwz112InnerCopyBase_lt K)
  refine ⟨N, fun k hk ↦ ?_⟩
  obtain ⟨hkpos, seed, hnonempty, hterm⟩ := hN k hk
  refine ⟨hkpos, seed, hnonempty, _,
    cw112SymmetricAmbientHasTauWeight K 6 dwz112L dwz112G k _ hq dwz112L_pos dwz112G_pos hkpos
      (cw112SymmetricHashModulus_ge_twentySeven K 6 dwz112L dwz112G k hq
        dwz112L_pos dwz112G_pos)
      (cw112SymmetricBuckets K 6 dwz112L dwz112G k hq dwz112L_pos dwz112G_pos)
      (cw112SymmetricBuckets_threeAPFree K 6 dwz112L dwz112G k hq dwz112L_pos dwz112G_pos)
      seed dwz63Tau le_rfl, ?_⟩
  have hpower : (cw112SymmetricCanonicalDegenerationValueCertificate
      K dwz63Tau 6 dwz112L dwz112G k hq dwz112L_pos dwz112G_pos hkpos seed hnonempty).power =
      dwz112Mass * k := by
    have h := RationalTypedLeaf.proportionalDepth_add_one
      (cw112SymmetricLeaf K 6 dwz112L dwz112G hq dwz112L_pos dwz112G_pos) hkpos
    rw [cw112SymmetricLeaf_profile_mass] at h
    show (cw112SymmetricLeaf K 6 dwz112L dwz112G hq dwz112L_pos dwz112G_pos).proportionalDepth k
      + 1 = _
    rw [h]
  have hbound := (cw112SymmetricCanonicalDegenerationValueCertificate
      K dwz63Tau 6 dwz112L dwz112G k hq dwz112L_pos dwz112G_pos hkpos
      seed hnonempty).rpow_three_mul_power_le_volumePowerSum K (Real.exp_nonneg _)
    (le_trans (dwz112_exp_le_leafTerm K) hterm)
  rw [Real.rpow_natCast, hpower] at hbound
  exact hbound

/-! ## Row 6 of the assembly's orbit premise, with no hypothesis -/

/-- **Row `6` of image 135's `R3` premise, hypothesis-free.**

For every sufficiently large repetition on the assembly's own `112` lattice `4·10^13 ∣ s`, the
`(1,1,2)` orbit region of the fine leaf carries the published value backed off by
`dwz63LeafMargin`, in exactly the binder shape
`DuanWuZhouLevelTwoAssemblyMarkedSeededLoss.lean:67-72` asks for at `o = 0`.

Proof: the canonical ambient weight above, fed through image 148's
`dwz63_orbitRowSix_R3_of_ambient` (which chains images 146, 144 and 127 and drops the deficit from
`10^(-22)` to `dwz63LeafMargin`), with the index length identified by
`dwz63_orbitRowSix_depth`. -/
theorem dwz63_orbitRowSix_R3 (hq : 0 < 6) (hqQ : 0 < dwz63Q) :
    ∃ N : ℕ, ∀ s : ℕ, 40000000000000 ∣ s →
      N ≤ 20088623 * (s / 40000000000000) →
      0 < 20088623 * (s / 40000000000000) →
      ∀ m : ℕ, m + 1 = 200000000 * (dwz63Alpha (dwz63OrbitRow 0) * s) →
        HasTauWeight K (symThree K (dwz63OrbitRegion K dwz63Q 0 (dwz63OrbitRow 0) m
          (dwz63Alpha (dwz63OrbitRow 0) * s)).realize) dwz63Tau
          (Real.exp ((200000000 : ℝ) * ((dwz63Alpha (dwz63OrbitRow 0) * s : ℕ) : ℝ)
            * (dwz63OrbitLogVal 0 - dwz63LeafMargin)) ^ 3) := by
  obtain ⟨N, hN⟩ := exists_eventually_cw112SymmetricAmbientHasTauWeight K hq
  refine ⟨N, fun s hs hk hkpos m hm ↦ ?_⟩
  obtain ⟨_hkpos, seed, _hne, value, hvalue, hlower⟩ := hN _ hk
  exact dwz63_orbitRowSix_R3_of_ambient K hqQ
    (cw112SymmetricHashModulus K 6 dwz112L dwz112G (20088623 * (s / 40000000000000)) hq
      dwz112L_pos dwz112G_pos)
    (cw112SymmetricHashModulus_ge_twentySeven K 6 dwz112L dwz112G
      (20088623 * (s / 40000000000000)) hq dwz112L_pos dwz112G_pos)
    s hs hvalue hlower m
    (dwz63_orbitRowSix_depth K hqQ s hs hkpos m hm)

end AlgebraicComplexity.Examples
