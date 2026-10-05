/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoLeafTauWeight

/-!
# The free-`beta` `tau`-weight of the `(1,2,1)` / `(2,1,1)` orbit letters

`Examples/DuanWuZhouLevelTwoLeafTauWeight.lean` produces the `[DuanWuZhou2022]` section 6.3
`tau`-weight for the `(1,1,2)` split `b = 21015 / 10 ^ 8`.  This module produces the *second*
lower bound for the very same orbit tensor, at the split `[DuanWuZhou2022]` assigns to the two
remaining letters of the orbit.

## Why there are two splits for one tensor

`global_value.tex` section 6.3 breaks the symmetry of the orbit `{(1,1,2), (1,2,1), (2,1,1)}`:
the `(1,1,2)` letter is given the free parameter `b`, while `(1,2,1)` and `(2,1,1)` "do not change
from section 4" and keep the classical optimum

`beta = 1 / (2 + q^{3 tau})`, rationalized as `beta = 69022217 / 5000000000`,

which is `PREP.md` section 1.5's choice, losing a relative `3.1 * 10 ^ (-20)` against the true
supremum.  A letter of the six-orientation partition carries the full `S_3`-orbit of its coarse
address, so both bounds are statements about *the same* tensor `sym_3(T_{1,1,2}^{tensor m})`; which
one a letter uses is decided by the letter's coarse address, not by its tensor.  Concretely the two
modules differ only in `(L, G)`:

| letter(s) | split | `(L, G)` | stride `2(L+G)` | value |
|---|---|---|---|---|
| `(1,1,2)` | `b = 21015/10^8` | `(4203, 9995797)` | `2 * 10^7` | `27.0947543121752429` |
| `(1,2,1)`, `(2,1,1)` | `beta = 69022217/5000000000` | `(69022217, 2430977783)` | `5 * 10^9` | `27.3288311864040788` |

`beta = L / (2 (L + G))` exactly, and the two entropy atoms it produces,
`2(L+G)/L = 5000000000/69022217 = 1/beta` and `(L+G)/G = 2500000000/2430977783 = 1/(1-2beta)`, are
literally two of the nine logarithm atoms of `dwz63LogVal`.
`dwz63LogVal_beta_atom_coefficients` checks that their committed coefficients are exactly
`alpha(1,2,1) + alpha(2,1,1) = 41468916 / 10 ^ 8` times the coefficients produced here --- the same
identification that pins `(4203, 9995797)` to the `(1,1,2)` letter.

**This is not `(L,G) = (7,247)`.**  `7/508 = 0.013779...` is the *same* classical optimum rounded
much more coarsely, as the committed `Examples/CoppersmithWinograd2375477.lean` client does.  It is
a legitimate lower bound here too --- the loss is second order, about `6.4 * 10 ^ (-9)` nats against
section 6.3's tightest slack of `1.7446 * 10 ^ (-7)` --- but `PREP.md`'s finer rationalization is
free, so it is the one taken.

## What is produced

The exact analogues of the `(1,1,2)` module's endpoints, at
`D = [2(L+G)]^3 = 1.25 * 10 ^ 29`:

* `exists_eventually_dwz121LeafHasTauWeight` and its `sym_6`-letter form
  `exists_eventually_dwz121ConstituentHasTauWeight`;
* `exists_eventually_dwz121LeafHasTauWeight_exp`, in the `hvalue` shape;
* `log_dwz121LeafTerm_eq`, the exact identity `log term = dwz121LogValue - log 2 / (3 D)`.

The strict-base reserve is `log 2 / (3 D) < 1.9 * 10 ^ (-30)` nats, recorded as the round
`10 ^ (-29)`.

Nothing here is conditional; there are no hypotheses.  The four symbolic bridge lemmas are reused
from `Examples/DuanWuZhouLevelTwoLeafTauWeight.lean` (see its docstring for why they are inlined
there rather than imported from `Examples/CoppersmithWinogradSquare112TauValueGrowth.lean`).

## Position in the library

Layer 4 (a client), a sibling of `Examples/DuanWuZhouLevelTwoLeafTauWeight.lean`.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `second_power.tex` `lem:non-rot-values` (d) and `global_value.tex`
section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-! ## The free-`beta` split parameters -/

/-- Light letter count of the free split `beta = 69022217 / 5000000000 = L / (2 (L + G))`. -/
def dwz121L : ℕ := 69022217

/-- Heavy letter count of the free split. -/
def dwz121G : ℕ := 2430977783

theorem dwz121L_pos : 0 < dwz121L := by norm_num [dwz121L]

theorem dwz121G_pos : 0 < dwz121G := by norm_num [dwz121G]

/-- The stride `2 (L + G)` is `5 * 10 ^ 9`, so `L / (2 (L+G)) = 69022217 / 5000000000 = beta`. -/
theorem dwz121Stride_eq : 2 * (dwz121L + dwz121G) = 5000000000 := by
  norm_num [dwz121L, dwz121G]

/-- Profile mass of the symmetric `(112)` typed leaf at the free split: `D = [2(L+G)]^3`. -/
abbrev dwz121Mass : ℕ := (2 * (dwz121L + dwz121G)) ^ 3

theorem dwz121Mass_eq : dwz121Mass = 125000000000000000000000000000 := by
  norm_num [dwz121Mass, dwz121L, dwz121G]

/-- **The parameter check.**  The two `beta`-dependent logarithm atoms of `dwz63LogVal` carry
exactly `alpha(1,2,1) + alpha(2,1,1) = 41468916 / 10 ^ 8` times the coefficients `dwz121LogValue`
gives them.  This is what identifies `(L, G) = (69022217, 2430977783)` as the free split of the
two remaining orbit letters. -/
theorem dwz63LogVal_beta_atom_coefficients :
    (41468916 / 100000000 : ℝ) * (2430977783 / 7500000000) =
        8400834456757769 / 62500000000000000 ∧
      (41468916 / 100000000 : ℝ) * (69022217 / 7500000000) =
        238523043242231 / 62500000000000000 := by
  constructor <;> norm_num

noncomputable section

variable (K : Type u) [Field K]

/-! ## The strict inner copy base -/

/-- Strict inner visible-copy base at the free `beta` split, with the factor-two reserve the
committed growth theorem requires.  The reserve costs `log 2 / (3 D)` nats, under
`1.9 * 10 ^ (-30)`. -/
noncomputable def dwz121InnerCopyBase : ℝ :=
  cw112SymmetricMarginalEntropyBase K 6 dwz121L dwz121G
    (by norm_num) dwz121L_pos dwz121G_pos / 2

theorem dwz121InnerCopyBase_pos : 0 < dwz121InnerCopyBase K := by
  unfold dwz121InnerCopyBase
  exact div_pos
    (cw112SymmetricMarginalEntropyBase_pos K 6 dwz121L dwz121G
      (by norm_num) dwz121L_pos dwz121G_pos)
    (by norm_num)

theorem dwz121InnerCopyBase_lt :
    dwz121InnerCopyBase K <
      cw112SymmetricMarginalEntropyBase K 6 dwz121L dwz121G
        (by norm_num) dwz121L_pos dwz121G_pos := by
  unfold dwz121InnerCopyBase
  exact div_lt_self
    (cw112SymmetricMarginalEntropyBase_pos K 6 dwz121L dwz121G
      (by norm_num) dwz121L_pos dwz121G_pos)
    (by norm_num)

/-! ## Exact logarithmic identities at the free split -/

/-- Exact logarithm of the symmetric inner entropy base at `(L,G) = (69022217, 2430977783)`. -/
theorem log_dwz121InnerEntropyBase :
    Real.log
        (cw112SymmetricMarginalEntropyBase K 6 dwz121L dwz121G
          (by norm_num) dwz121L_pos dwz121G_pos) =
      2 * 125000000000000000000000000000 * Real.log 2 +
        3451110850000000000000000000 * Real.log (5000000000 / 69022217 : ℝ) +
        121548889150000000000000000000 * Real.log (2500000000 / 2430977783 : ℝ) := by
  rw [dwz_log_cw112SymmetricMarginalEntropyBase K 6 dwz121L dwz121G
    (by norm_num) dwz121L_pos dwz121G_pos]
  norm_num [dwz121L, dwz121G]

/-- Exact logarithm of the strict inner visible-copy base: the entropy base less `log 2`. -/
theorem log_dwz121InnerCopyBase :
    Real.log (dwz121InnerCopyBase K) =
      2 * 125000000000000000000000000000 * Real.log 2 +
        3451110850000000000000000000 * Real.log (5000000000 / 69022217 : ℝ) +
        121548889150000000000000000000 * Real.log (2500000000 / 2430977783 : ℝ) -
        Real.log 2 := by
  rw [dwz121InnerCopyBase,
    Real.log_div
      (cw112SymmetricMarginalEntropyBase_pos K 6 dwz121L dwz121G
        (by norm_num) dwz121L_pos dwz121G_pos).ne'
      (by norm_num : (2 : ℝ) ≠ 0),
    log_dwz121InnerEntropyBase]

/-- The symmetric `(112)` leaf at the free split has matrix-volume logarithm
`3 [2(L+G)]^2 (4G + 2L) log 6 = 739646667450000000000000000000 * log 6`. -/
theorem log_dwz121InnerDimensionVolume :
    Real.log
        (((cw112SymmetricLeaf K 6 dwz121L dwz121G
              (by norm_num) dwz121L_pos dwz121G_pos).dimensionProduct .X *
          (cw112SymmetricLeaf K 6 dwz121L dwz121G
              (by norm_num) dwz121L_pos dwz121G_pos).dimensionProduct .Y *
          (cw112SymmetricLeaf K 6 dwz121L dwz121G
              (by norm_num) dwz121L_pos dwz121G_pos).dimensionProduct .Z : ℕ) : ℝ) =
      739646667450000000000000000000 * Real.log 6 := by
  rw [dwz_log_cw112SymmetricDimensionVolume K 6 dwz121L dwz121G
    (by norm_num) dwz121L_pos dwz121G_pos]
  norm_num [dwz121L, dwz121G]

/-! ## The achieved orbit value at the free split -/

/-- The normalized orbit leaf term achieved at the free `beta` split and at the declared exponent
`dwz63Tau`.  This is `[DuanWuZhou2022]` `lem:non-rot-values` (d) at the classical optimum. -/
noncomputable def dwz121LeafTerm : ℝ :=
  cw112SymmetricLimitLowerTerm K (dwz121InnerCopyBase K) dwz63Tau 6 dwz121L dwz121G
    (by norm_num) dwz121L_pos dwz121G_pos

theorem dwz121LeafTerm_pos : 0 < dwz121LeafTerm K := by
  unfold dwz121LeafTerm
  exact dwzCw112SymmetricLimitLowerTerm_pos K (dwz121InnerCopyBase_pos K) dwz63Tau 6
    dwz121L dwz121G (by norm_num) dwz121L_pos dwz121G_pos

/-- Clearing the `3 D` normalization exposes one visible-copy logarithm and one matrix-volume
logarithm.

Proof sketch: specialize `dwz_log_cw112SymmetricLimitLowerTerm`, substitute the exact entropy and
dimension identities, and clear the nonzero profile-mass denominator `3 * 1.25 * 10 ^ 29`. -/
theorem scaled_log_dwz121LeafTerm :
    (375000000000000000000000000000 : ℝ) * Real.log (dwz121LeafTerm K) =
      (2 * 125000000000000000000000000000 * Real.log 2 +
        3451110850000000000000000000 * Real.log (5000000000 / 69022217 : ℝ) +
        121548889150000000000000000000 * Real.log (2500000000 / 2430977783 : ℝ) -
        Real.log 2) +
      (2374631 / 3000000 : ℝ) * (739646667450000000000000000000 * Real.log 6) := by
  have h := dwz_log_cw112SymmetricLimitLowerTerm K
    (dwz121InnerCopyBase_pos K) dwz63Tau 6 dwz121L dwz121G
      (by norm_num) dwz121L_pos dwz121G_pos
  rw [cw112SymmetricLeaf_profile_mass, log_dwz121InnerCopyBase,
    log_dwz121InnerDimensionVolume] at h
  change Real.log (dwz121LeafTerm K) = _ at h
  norm_num [dwz121L, dwz121G, dwz63Tau] at h ⊢
  linarith

/-- The logarithm of `PREP.md` section 1.6's `(1,2,1)` / `(2,1,1)` component value
`(4 / ((1-2beta)^{1-2beta} beta^{2beta}))^{1/3} * q^{(2-2beta) tau}`, with
`beta = 69022217/5000000000`, `q = 6` and `tau = dwz63Tau`.  Numerically `exp` of this is
`27.3288311864040788`. -/
noncomputable def dwz121LogValue : ℝ :=
  2 / 3 * Real.log 2 +
    69022217 / 7500000000 * Real.log (5000000000 / 69022217 : ℝ) +
    2430977783 / 7500000000 * Real.log (2500000000 / 2430977783 : ℝ) +
    4930977783 / 2500000000 * (dwz63Tau * Real.log 6)

/-- **The join point with the values lane.**  `dwz121LogValue` written in the exact shape
`Examples/DuanWuZhouLevelTwoConstituentValues.lean` uses for `dwz63LogVal121`, so that the two
constants are identified by a single `rw` on that side, with no import dependency in either
direction.  The only difference is `log 6 = log 2 + log 3` and the collection of the three
rational coefficients. -/
theorem dwz121LogValue_eq_paperForm :
    dwz121LogValue =
      (2 * Real.log 2 + (1 - 2 * dwz63Beta) * Real.log (2500000000 / 2430977783 : ℝ)
          + 2 * dwz63Beta * Real.log (5000000000 / 69022217 : ℝ)) / 3
        + (2 - 2 * dwz63Beta) * dwz63Tau * (Real.log 2 + Real.log 3) := by
  have h6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [dwz121LogValue, dwz63Beta, h6]
  ring

/-- **The achieved term is the published orbit value less the strict-base reserve.**

`log dwz121LeafTerm = dwz121LogValue - log 2 / (3 D)` exactly, with
`3 D = 3.75 * 10 ^ 29`. -/
theorem log_dwz121LeafTerm_eq :
    Real.log (dwz121LeafTerm K) =
      dwz121LogValue - Real.log 2 / 375000000000000000000000000000 := by
  have h := scaled_log_dwz121LeafTerm K
  rw [dwz121LogValue, dwz63Tau]
  linarith

/-- The strict-base reserve is below `10 ^ (-29)` nats. -/
theorem dwz121LogValue_sub_le_log_dwz121LeafTerm :
    dwz121LogValue - 1 / 10 ^ 29 ≤ Real.log (dwz121LeafTerm K) := by
  rw [log_dwz121LeafTerm_eq]
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  linarith

/-- Exponential form: the published orbit value, backed off by `10 ^ (-29)` nats, is genuinely
achieved by the extracted leaf term. -/
theorem dwz121_exp_le_leafTerm :
    Real.exp (dwz121LogValue - 1 / 10 ^ 29) ≤ dwz121LeafTerm K := by
  calc Real.exp (dwz121LogValue - 1 / 10 ^ 29)
      ≤ Real.exp (Real.log (dwz121LeafTerm K)) :=
        Real.exp_le_exp.mpr (dwz121LogValue_sub_le_log_dwz121LeafTerm K)
    _ = dwz121LeafTerm K := Real.exp_log (dwz121LeafTerm_pos K)

/-! ## The `tau`-weight -/

/-- **The orbit tensor carries its free-`beta` `tau`-weight.**

Identical in shape to `exists_eventually_dwz112LeafHasTauWeight`, at the free split.  The proof is
the same three steps: the committed growth theorem supplies a canonical cyclic degeneration
certificate past a cutoff, `CyclicDegenerationCertificate.toTauValueCertificateSymThree` reads it
as a value certificate of `sym_3` at the same length, and raising the term domination to the
`3 * power` cancels the certificate's own cube-and-length root exactly. -/
theorem exists_eventually_dwz121LeafHasTauWeight :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      HasTauWeight K
        (Tensor.power (symThree K (cw112PartitionedTensor K 6).realize) (dwz121Mass * k))
        dwz63Tau (dwz121LeafTerm K ^ (3 * (dwz121Mass * k))) := by
  obtain ⟨N, hN⟩ :=
    exists_eventually_cw112SymmetricLimitLowerTerm_le_certificate K dwz63Tau 6
      dwz121L dwz121G (by norm_num) dwz121L_pos dwz121G_pos
      (dwz121InnerCopyBase_pos K) (dwz121InnerCopyBase_lt K)
  refine ⟨N, fun k hk ↦ ?_⟩
  obtain ⟨hkpos, seed, hnonempty, hterm⟩ := hN k hk
  set certificate := cw112SymmetricCanonicalDegenerationValueCertificate K dwz63Tau 6
    dwz121L dwz121G k (by norm_num) dwz121L_pos dwz121G_pos hkpos seed hnonempty with hcert
  have hpower : certificate.power = dwz121Mass * k := by
    rw [hcert, cw112SymmetricCanonicalDegenerationValueCertificate_power,
      RationalTypedLeaf.proportionalDepth_add_one _ hkpos,
      cw112SymmetricLeaf_profile_mass]
  have hsumPos : 0 < matrixMultiplicationVolumePowerSum
      certificate.xSize certificate.ySize certificate.zSize dwz63Tau :=
    matrixMultiplicationVolumePowerSum_pos certificate.copies_pos certificate.xSize_pos
      certificate.ySize_pos certificate.zSize_pos dwz63Tau
  have hroot : certificate.term ^ (3 * certificate.power) =
      matrixMultiplicationVolumePowerSum
        certificate.xSize certificate.ySize certificate.zSize dwz63Tau := by
    have hne : ((3 * certificate.power : ℕ) : ℝ) ≠ 0 := by
      have hp := certificate.power_pos
      have : 0 < 3 * certificate.power := by omega
      exact_mod_cast this.ne'
    show (matrixMultiplicationVolumePowerSum
        certificate.xSize certificate.ySize certificate.zSize dwz63Tau ^
        (((3 * certificate.power : ℕ) : ℝ))⁻¹) ^ (3 * certificate.power) = _
    rw [← Real.rpow_natCast (matrixMultiplicationVolumePowerSum
        certificate.xSize certificate.ySize certificate.zSize dwz63Tau ^
        (((3 * certificate.power : ℕ) : ℝ))⁻¹) (3 * certificate.power),
      ← Real.rpow_mul hsumPos.le, inv_mul_cancel₀ hne, Real.rpow_one]
  have hweight := (certificate.toTauValueCertificateSymThree).hasTauWeight dwz63Tau
  have hpowerEq : (certificate.toTauValueCertificateSymThree).power = certificate.power := rfl
  rw [hpowerEq, hpower] at hweight
  refine hweight.mono ?_
  have hle : dwz121LeafTerm K ≤ certificate.term := hterm
  have hmono : dwz121LeafTerm K ^ (3 * certificate.power) ≤
      certificate.term ^ (3 * certificate.power) :=
    pow_le_pow_left₀ (dwz121LeafTerm_pos K).le hle _
  rw [hpower] at hmono
  calc dwz121LeafTerm K ^ (3 * (dwz121Mass * k)) ≤ certificate.term ^ (3 * (dwz121Mass * k)) :=
        hmono
    _ = matrixMultiplicationVolumePowerSum
          certificate.xSize certificate.ySize certificate.zSize dwz63Tau := by
        rw [← hpower]; exact hroot

/-- **The free-`beta` weight, read on the coarse orbit constituent of the level-two source.**

Same transport as `exists_eventually_dwz112ConstituentHasTauWeight`, and the same remark applies:
a `sym_6` letter carries the full `S_3`-orbit of its coarse address, so this is simultaneously a
weight on the external product of the `(1,1,2)`, `(1,2,1)` and `(2,1,1)` constituents.  A letter
whose coarse address is `(1,2,1)` or `(2,1,1)` spends *this* bound; a `(1,1,2)` letter spends
`exists_eventually_dwz112ConstituentHasTauWeight`. -/
theorem exists_eventually_dwz121ConstituentHasTauWeight :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      HasTauWeight K
        (Tensor.power
          (symThree K ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare112))
          (dwz121Mass * k))
        dwz63Tau (dwz121LeafTerm K ^ (3 * (dwz121Mass * k))) := by
  obtain ⟨N, hN⟩ := exists_eventually_dwz121LeafHasTauWeight K
  refine ⟨N, fun k hk ↦ (hN k hk).of_restricts ?_⟩
  exact Tensor.Restricts.power
    (restricts_symThree_of_restricts K
      (cwSquareConstituent_112_restricts_partitioned K dwz63Q)) _

/-! ### Note: the explicit `S_3`-orbit product

`sym_3` of the `(1,1,2)` constituent is, by the two committed orbit isomorphisms
`cwSquareConstituent_211_isomorphic_cycle` and `cwSquareConstituent_121_isomorphic_cycleSymm`,
exactly the external product `T_{1,1,2} tensor T_{2,1,1} tensor T_{1,2,1}`, so
`exists_eventually_dwz121ConstituentHasTauWeight` above *is* a weight for all three letters of the
orbit at once.

Stating that product as its own `HasTauWeight` here does not elaborate: naming the three *distinct*
coarse addresses forces three different `cwSquareSourceFiber` block-space families into one
external product, and the declaration exceeds `whnf`'s budget even at
`maxHeartbeats 2000000` / `maxRecDepth 16000`.  A client that wants the named-constituent form
should apply the two isomorphisms on its own side, inside a context where those block spaces are
already elaborated:

```text
((Tensor.Restricts.refl _).external
    (cwSquareConstituent_211_isomorphic_cycle K dwz63Q).restricts).external
  (cwSquareConstituent_121_isomorphic_cycleSymm K dwz63Q).restricts
  : Restricts (T_{1,1,2} ⊗ T_{2,1,1} ⊗ T_{1,2,1}) (symThree K T_{1,1,2})
```

followed by `Tensor.Restricts.power` and `HasTauWeight.of_restricts`.  The repository has no
`sym_3`-versus-cyclic-permutation invariance lemma either (only
`Isomorphic.permute_swapXY_symThree`), so `symThree K (constituent cwSquare121)` is likewise not
available as a separate statement without adding one. -/

/-- The same weight in the exponential shape the `hvalue` premise of
`exists_value_of_repairedStage_true` consumes. -/
theorem exists_eventually_dwz121LeafHasTauWeight_exp :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → ∃ value : ℝ, 0 < value ∧
      HasTauWeight K
        (Tensor.power (symThree K (cw112PartitionedTensor K 6).realize) (dwz121Mass * k))
        dwz63Tau value ∧
      Real.exp (dwz121LogValue - 1 / 10 ^ 29) ^ (3 * (dwz121Mass * k)) ≤ value := by
  obtain ⟨N, hN⟩ := exists_eventually_dwz121LeafHasTauWeight K
  refine ⟨N, fun k hk ↦ ⟨dwz121LeafTerm K ^ (3 * (dwz121Mass * k)),
    pow_pos (dwz121LeafTerm_pos K) _, hN k hk, ?_⟩⟩
  exact pow_le_pow_left₀ (Real.exp_nonneg _) (dwz121_exp_le_leafTerm K) _

end

end AlgebraicComplexity.Examples
