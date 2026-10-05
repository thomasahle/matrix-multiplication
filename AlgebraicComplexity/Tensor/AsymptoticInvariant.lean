/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.AsymptoticRank
import AlgebraicComplexity.Tensor.PowerCoherence
import AlgebraicComplexity.Tensor.SliceRank
import AlgebraicComplexity.Tensor.Subrank

/-!
# A generic asymptotic-invariant engine

Asymptotic rank, asymptotic border rank, asymptotic subrank, and asymptotic slice rank all have
the same shape: a numerical invariant `μ` is evaluated on the canonical tensor powers `T^{⊗n}` and
the exponential growth rate `lim_n μ(T^{⊗n})^{1/n}` is extracted.  The only inputs are that `μ` is
invariant under legwise isomorphism and that it is sub- or supermultiplicative under external
products.  This module isolates that shared core so that each new invariant needs only its two
structural lemmas.

The file has three parts.  The **sequence engine** it runs on --- the multiplicative form of
Fekete's lemma, `Growth.Submultiplicative`, `Growth.Supermultiplicative` and their
`tendsto_nthRootSeq` limits --- mentions no tensors and lives in `AlgebraicComplexity/Asymptotics.lean`
alongside the constant-tolerant `Growth.exponentialRate` it is compared with.

* A **tensor wrapper**.  `NatInvariant K` is the type of numerical invariants of three-legged
  tensors whose leg spaces live in one fixed universe; `IsoInvariant`, `ExternalSubmultiplicative`,
  `ExternalSupermultiplicative`, and `RestrictionMonotone` are the four structural hypotheses.
  `asymptoticInvariant μ T` and `asymptoticSuperInvariant μ T` apply the engine to
  `n ↦ μ (power T n)`.  Every theorem here is a schema: it takes the structural properties of `μ`
  as hypotheses and is therefore usable by any invariant that satisfies them.
* A **bridge**.  `asymptoticRank_eq_asymptoticInvariant` specializes
  `Growth.exponentialRate_eq_submultiplicativeLimit` --- the layer-0 identification of the
  constant-tolerant infimum `Growth.exponentialRate` with the Fekete limit --- to the existing
  `asymptoticRank` of `Tensor/AsymptoticRank.lean`, which is left untouched.
* A **supermultiplicative client**: the diagonal-restriction subrank.  The finite theory of
  `subrank` --- the largest `m` for which `T` restricts onto `diagonalTensor K (Fin m)`, its
  supermultiplicativity under external products, and the slice-rank bound that makes the defining
  supremum attained over a field --- lives in `Tensor/Subrank.lean`, which mentions no analysis.
  Here `subrankInvariant` packages it as a `NatInvariant`, and feeding it into the schema defines
  `asymptoticSubrank` and gives its existence theorem together with the transported slice-rank and
  rank upper bounds.

The key tensor input is `isomorphic_external_power` of `Tensor/PowerCoherence.lean`, the isomorphism
`T^{⊗m} ⊠ T^{⊗n} ≅ T^{⊗(m+n)}` that turns external multiplicativity of `μ` into multiplicativity
along the power sequence.  `Tensor/IteratedProduct.lean`'s left-associated products are a proof
device for type extraction and are deliberately not used here.

## Non-goals

The module packages only two concrete invariants: ordinary tensor rank (for the bridge) and the
diagonal-restriction subrank (as the supermultiplicative client).  Asymptotic slice rank and
asymptotic border rank should be added as further clients of the same schema; so should the
comparison `asymptoticSubrank T ≤ asymptoticSliceRank T ≤ asymptoticRank T` once asymptotic slice
rank exists.  The module also does not develop Strassen's
asymptotic spectrum (Strassen, *The asymptotic spectrum of tensors*, J. reine angew. Math. 384
(1988), 102--152; *Degeneration and complexity of bilinear maps*, ibid. 375/376 (1987), 406--443),
for which these limits are the basic objects.

## References

* M. Fekete, *Über die Verteilung der Wurzeln bei gewissen algebraischen Gleichungen mit
  ganzzahligen Koeffizienten*, Math. Z. 17 (1923), 228--249.
* V. Strassen, *Relative bilinear complexity and matrix multiplication*, J. reine angew. Math. 375/376
  (1987), 406--443, and *The asymptotic spectrum of tensors*, ibid. 384 (1988), 102--152.
-/

namespace AlgebraicComplexity.Tensor

open Filter Topology

universe u v w

/-! ## Numerical tensor invariants

An invariant must be applicable to the tensor powers of `T` as well as to `T` itself.  Since
`PowerSpace K V n` again takes values in `Type (max u v)` when `V` does, fixing the leg universe to
`max u v` makes the powers of a tensor stay in the domain of the invariant. -/

/-- The type of numerical invariants of three-legged tensors over `K` whose leg spaces live in the
universe `max u v`.  Ordinary rank, border rank, slice rank, and subrank are all of this shape.

Fixing one leg universe is unavoidable: Lean cannot quantify over universe-polymorphic functions.
The choice `max u v` is the one for which canonical tensor powers stay in the domain. -/
abbrev NatInvariant (K : Type u) [CommSemiring K] :=
  ∀ {V : Leg → Type (max u v)} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)],
    Tensor3 K V → ℕ

section Invariant

variable {K : Type u} [CommSemiring K]

/-- `μ` takes the same value on legwise isomorphic tensors. -/
def IsoInvariant (μ : NatInvariant.{u, v} K) : Prop :=
  ∀ {V W : Leg → Type (max u v)} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
    [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)] (T : Tensor3 K V) (S : Tensor3 K W),
    Isomorphic T S → μ T = μ S

/-- `μ` is submultiplicative under external products: `μ (T ⊠ S) ≤ μ T * μ S`.  Ordinary rank and
border rank satisfy this. -/
def ExternalSubmultiplicative (μ : NatInvariant.{u, v} K) : Prop :=
  ∀ {V W : Leg → Type (max u v)} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
    [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)] (T : Tensor3 K V) (S : Tensor3 K W),
    μ (external T S) ≤ μ T * μ S

/-- `μ` is supermultiplicative under external products: `μ T * μ S ≤ μ (T ⊠ S)`.  Subrank-style
invariants satisfy this. -/
def ExternalSupermultiplicative (μ : NatInvariant.{u, v} K) : Prop :=
  ∀ {V W : Leg → Type (max u v)} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
    [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)] (T : Tensor3 K V) (S : Tensor3 K W),
    μ T * μ S ≤ μ (external T S)

/-- `μ` decreases along exact restriction: if `T` restricts to `S`, then `μ S ≤ μ T`.  The source of
the restriction is `T` and the target is `S`, so the *smaller* tensor has the *smaller* invariant. -/
def RestrictionMonotone (μ : NatInvariant.{u, v} K) : Prop :=
  ∀ {V W : Leg → Type (max u v)} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
    [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)] (T : Tensor3 K V) (S : Tensor3 K W),
    Restricts T S → μ S ≤ μ T

variable {μ : NatInvariant.{u, v} K}
variable {V : Leg → Type (max u v)} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable {W : Leg → Type (max u v)} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]

/-- An isomorphism-invariant `μ` sees no difference between `T` and its first canonical power. -/
theorem IsoInvariant.power_one (hiso : IsoInvariant μ) (T : Tensor3 K V) :
    μ (power T 1) = μ T := by
  refine hiso _ _ ?_
  rw [power_one_eq_powerOne]
  exact (Isomorphic.powerOneTransport T).symm

/-- A submultiplicative isomorphism-invariant is submultiplicative along the power sequence:
`μ (T^{⊗(m+n)}) ≤ μ (T^{⊗m}) * μ (T^{⊗n})`.

Proof sketch: transport `μ` across `isomorphic_external_power` and apply external
submultiplicativity to the two powers. -/
theorem IsoInvariant.power_add_le (hiso : IsoInvariant μ)
    (hsub : ExternalSubmultiplicative μ) (T : Tensor3 K V) (m n : ℕ) :
    μ (power T (m + n)) ≤ μ (power T m) * μ (power T n) :=
  calc μ (power T (m + n)) = μ (external (power T m) (power T n)) :=
        (hiso _ _ (isomorphic_external_power T m n)).symm
    _ ≤ μ (power T m) * μ (power T n) := hsub _ _

/-- A supermultiplicative isomorphism-invariant is supermultiplicative along the power sequence:
`μ (T^{⊗m}) * μ (T^{⊗n}) ≤ μ (T^{⊗(m+n)})`. -/
theorem IsoInvariant.le_power_add (hiso : IsoInvariant μ)
    (hsup : ExternalSupermultiplicative μ) (T : Tensor3 K V) (m n : ℕ) :
    μ (power T m) * μ (power T n) ≤ μ (power T (m + n)) :=
  calc μ (power T m) * μ (power T n) ≤ μ (external (power T m) (power T n)) := hsup _ _
    _ = μ (power T (m + n)) := hiso _ _ (isomorphic_external_power T m n)

/-! ### The asymptotic invariant -/

/-- The real-valued sequence `n ↦ μ (T^{⊗n})` of invariant values on canonical tensor powers. -/
noncomputable def invariantPowerSequence (μ : NatInvariant.{u, v} K) (T : Tensor3 K V) (n : ℕ) :
    ℝ := (μ (power T n) : ℝ)

/-- The asymptotic invariant of `T` for a submultiplicative `μ`: the infimum, equivalently the
limit, of `μ (T^{⊗n}) ^ (1/n)`. -/
noncomputable def asymptoticInvariant (μ : NatInvariant.{u, v} K) (T : Tensor3 K V) : ℝ :=
  Growth.submultiplicativeLimit (invariantPowerSequence μ T)

/-- The asymptotic invariant of `T` for a supermultiplicative `μ`: the supremum, equivalently the
limit, of `μ (T^{⊗n}) ^ (1/n)`. -/
noncomputable def asymptoticSuperInvariant (μ : NatInvariant.{u, v} K) (T : Tensor3 K V) : ℝ :=
  Growth.supermultiplicativeLimit (invariantPowerSequence μ T)

/-- Values of a natural-valued invariant are nonnegative reals. -/
theorem invariantPowerSequence_nonneg (μ : NatInvariant.{u, v} K) (T : Tensor3 K V) (n : ℕ) :
    0 ≤ invariantPowerSequence μ T n := by
  unfold invariantPowerSequence
  positivity

/-- A pointwise lower bound of one on the invariant of tensor powers transfers to the real
power sequence. -/
theorem one_le_invariantPowerSequence (μ : NatInvariant.{u, v} K) (T : Tensor3 K V)
    (h : ∀ n, 1 ≤ μ (power T n)) (n : ℕ) : 1 ≤ invariantPowerSequence μ T n := by
  unfold invariantPowerSequence
  exact_mod_cast h n

/-- A geometric upper bound on the invariant of tensor powers transfers to the real power
sequence. -/
theorem invariantPowerSequence_le_pow (μ : NatInvariant.{u, v} K) (T : Tensor3 K V) {r : ℕ}
    (h : ∀ n, μ (power T n) ≤ r ^ n) (n : ℕ) : invariantPowerSequence μ T n ≤ (r : ℝ) ^ n := by
  unfold invariantPowerSequence
  exact_mod_cast h n

/-- The power sequence of a submultiplicative isomorphism-invariant is a submultiplicative real
sequence. -/
theorem IsoInvariant.submultiplicative_invariantPowerSequence (hiso : IsoInvariant μ)
    (hsub : ExternalSubmultiplicative μ) (T : Tensor3 K V) :
    Growth.Submultiplicative (invariantPowerSequence μ T) := by
  intro m n
  unfold invariantPowerSequence
  exact_mod_cast hiso.power_add_le hsub T m n

/-- The power sequence of a supermultiplicative isomorphism-invariant is a supermultiplicative real
sequence. -/
theorem IsoInvariant.supermultiplicative_invariantPowerSequence (hiso : IsoInvariant μ)
    (hsup : ExternalSupermultiplicative μ) (T : Tensor3 K V) :
    Growth.Supermultiplicative (invariantPowerSequence μ T) := by
  intro m n
  unfold invariantPowerSequence
  exact_mod_cast hiso.le_power_add hsup T m n

/-- **Existence of the asymptotic invariant, submultiplicative case.**  If `μ` is an
isomorphism-invariant, externally submultiplicative, and at least `1` on every power of `T`, then
`μ (T^{⊗n}) ^ (1/n)` converges to `asymptoticInvariant μ T`.

Proof sketch: `IsoInvariant.submultiplicative_invariantPowerSequence` turns the two structural
hypotheses into submultiplicativity of the real sequence `n ↦ μ (T^{⊗n})`, which is then bounded
below by the geometric sequence `1 ^ n`; the multiplicative Fekete lemma
`Growth.Submultiplicative.tendsto_nthRootSeq` supplies the limit. -/
theorem tendsto_asymptoticInvariant (hiso : IsoInvariant μ) (hsub : ExternalSubmultiplicative μ)
    (T : Tensor3 K V) (hone : ∀ n, 1 ≤ μ (power T n)) :
    Tendsto (Growth.nthRootSeq (invariantPowerSequence μ T)) atTop
      (𝓝 (asymptoticInvariant μ T)) := by
  unfold asymptoticInvariant
  refine (hiso.submultiplicative_invariantPowerSequence hsub T).tendsto_nthRootSeq
    (fun n ↦ ?_) zero_lt_one fun n ↦ ?_
  · exact lt_of_lt_of_le zero_lt_one (one_le_invariantPowerSequence μ T hone n)
  · simpa using one_le_invariantPowerSequence μ T hone n

/-- **Existence of the asymptotic invariant, supermultiplicative case.**  If `μ` is an
isomorphism-invariant, externally supermultiplicative, positive on every power of `T`, and bounded
by a geometric sequence along powers of `T`, then `μ (T^{⊗n}) ^ (1/n)` converges to
`asymptoticSuperInvariant μ T`. -/
theorem tendsto_asymptoticSuperInvariant (hiso : IsoInvariant μ)
    (hsup : ExternalSupermultiplicative μ) (T : Tensor3 K V) (hone : ∀ n, 1 ≤ μ (power T n))
    {r : ℕ} (hub : ∀ n, μ (power T n) ≤ r ^ n) :
    Tendsto (Growth.nthRootSeq (invariantPowerSequence μ T)) atTop
      (𝓝 (asymptoticSuperInvariant μ T)) := by
  unfold asymptoticSuperInvariant
  refine (hiso.supermultiplicative_invariantPowerSequence hsup T).tendsto_nthRootSeq
    (fun n ↦ ?_) (C := (r : ℝ)) fun n ↦ ?_
  · exact lt_of_lt_of_le zero_lt_one (one_le_invariantPowerSequence μ T hone n)
  · exact invariantPowerSequence_le_pow μ T hub n

/-! ### The sup/inf characterization and comparison lemmas -/

/-- The asymptotic invariant is bounded by the normalized value at every single positive power:
`asymptoticInvariant μ T ≤ μ (T^{⊗n}) ^ (1/n)`.  No structural hypothesis is needed, because the
asymptotic invariant is defined as an infimum. -/
theorem asymptoticInvariant_le_root (μ : NatInvariant.{u, v} K) (T : Tensor3 K V) {n : ℕ}
    (hn : 1 ≤ n) : asymptoticInvariant μ T ≤ (μ (power T n) : ℝ) ^ ((n : ℝ)⁻¹) :=
  Growth.submultiplicativeLimit_le_nthRootSeq (invariantPowerSequence_nonneg μ T) hn

/-- A uniform lower bound on the normalized values bounds the asymptotic invariant below. -/
theorem le_asymptoticInvariant {b : ℝ} (μ : NatInvariant.{u, v} K) (T : Tensor3 K V)
    (h : ∀ n : ℕ, 1 ≤ n → b ≤ (μ (power T n) : ℝ) ^ ((n : ℝ)⁻¹)) :
    b ≤ asymptoticInvariant μ T :=
  Growth.le_submultiplicativeLimit h

/-- For an isomorphism-invariant `μ`, the asymptotic invariant of `T` never exceeds `μ T` itself. -/
theorem asymptoticInvariant_le_self (hiso : IsoInvariant μ) (T : Tensor3 K V) :
    asymptoticInvariant μ T ≤ (μ T : ℝ) := by
  have h := asymptoticInvariant_le_root μ T (n := 1) le_rfl
  rwa [Nat.cast_one, inv_one, Real.rpow_one, hiso.power_one] at h

/-- **Monotone transport.**  If the invariant of the powers of `S` is dominated by that of the
powers of `T`, then the asymptotic invariants are ordered the same way.  This is the abstract form
of monotonicity under any relation `R` for which `μ` is monotone and `R` is stable under canonical
powers: both properties combine into the single hypothesis `hpow`. -/
theorem asymptoticInvariant_mono {T : Tensor3 K V} {S : Tensor3 K W}
    (hpow : ∀ n, μ (power S n) ≤ μ (power T n)) :
    asymptoticInvariant μ S ≤ asymptoticInvariant μ T := by
  refine Growth.submultiplicativeLimit_mono (invariantPowerSequence_nonneg μ S) fun n ↦ ?_
  unfold invariantPowerSequence
  exact_mod_cast hpow n

/-- Asymptotic invariants of a restriction-monotone `μ` decrease along exact restriction: the
source `T` has the larger asymptotic invariant.

Proof sketch: exact restriction is stable under canonical powers (`Restricts.power`), so
`asymptoticInvariant_mono` applies with the pointwise comparison supplied by `hμ`. -/
theorem asymptoticInvariant_restricts_le (hμ : RestrictionMonotone μ)
    {T : Tensor3 K V} {S : Tensor3 K W} (h : Restricts T S) :
    asymptoticInvariant μ S ≤ asymptoticInvariant μ T :=
  asymptoticInvariant_mono fun n ↦ hμ _ _ (h.power n)

/-- Legwise isomorphic tensors have equal asymptotic invariants, for a restriction-monotone `μ`. -/
theorem asymptoticInvariant_isomorphic (hμ : RestrictionMonotone μ)
    {T : Tensor3 K V} {S : Tensor3 K W} (h : Isomorphic T S) :
    asymptoticInvariant μ T = asymptoticInvariant μ S :=
  le_antisymm (asymptoticInvariant_restricts_le hμ h.symm.restricts)
    (asymptoticInvariant_restricts_le hμ h.restricts)

/-- **Exactly geometric invariant sequences.**  If `μ (T^{⊗n}) = b ^ n` for every `n`, then the
asymptotic invariant is exactly `b`. -/
theorem asymptoticInvariant_eq_of_pow {b : ℕ} (μ : NatInvariant.{u, v} K) (T : Tensor3 K V)
    (h : ∀ n, μ (power T n) = b ^ n) : asymptoticInvariant μ T = (b : ℝ) := by
  have hseq : invariantPowerSequence μ T = fun n ↦ (b : ℝ) ^ n := by
    funext n
    show ((μ (power T n) : ℕ) : ℝ) = (b : ℝ) ^ n
    rw [h n, Nat.cast_pow]
  rw [asymptoticInvariant, hseq, Growth.submultiplicativeLimit_pow (by positivity)]

/-- A uniform upper bound on the normalized values bounds the supermultiplicative asymptotic
invariant above. -/
theorem asymptoticSuperInvariant_le {b : ℝ} (μ : NatInvariant.{u, v} K) (T : Tensor3 K V)
    (h : ∀ n : ℕ, 1 ≤ n → (μ (power T n) : ℝ) ^ ((n : ℝ)⁻¹) ≤ b) :
    asymptoticSuperInvariant μ T ≤ b :=
  Growth.supermultiplicativeLimit_le h

/-- Every single normalized power value bounds the supermultiplicative asymptotic invariant from
below, given a geometric upper bound along powers. -/
theorem root_le_asymptoticSuperInvariant (μ : NatInvariant.{u, v} K) (T : Tensor3 K V)
    {r : ℕ} (hub : ∀ n, μ (power T n) ≤ r ^ n) {n : ℕ} (hn : 1 ≤ n) :
    (μ (power T n) : ℝ) ^ ((n : ℝ)⁻¹) ≤ asymptoticSuperInvariant μ T := by
  refine Growth.nthRootSeq_le_supermultiplicativeLimit
    (Growth.bddAbove_nthRootSeq_image (C := (r : ℝ)) (invariantPowerSequence_nonneg μ T)
      fun k ↦ ?_) hn
  unfold invariantPowerSequence
  exact_mod_cast hub k

/-- For an isomorphism-invariant `μ` with a geometric upper bound along powers, `μ T` itself is a
lower bound for the supermultiplicative asymptotic invariant. -/
theorem self_le_asymptoticSuperInvariant (hiso : IsoInvariant μ) (T : Tensor3 K V)
    {r : ℕ} (hub : ∀ n, μ (power T n) ≤ r ^ n) :
    (μ T : ℝ) ≤ asymptoticSuperInvariant μ T := by
  have h := root_le_asymptoticSuperInvariant μ T hub (n := 1) le_rfl
  rwa [Nat.cast_one, inv_one, Real.rpow_one, hiso.power_one] at h

/-- **Monotone transport, supermultiplicative case.**  Pointwise domination of the power sequences
transports to the supermultiplicative asymptotic invariants, given a geometric upper bound for the
dominating tensor. -/
theorem asymptoticSuperInvariant_mono {T : Tensor3 K V} {S : Tensor3 K W}
    (hpow : ∀ n, μ (power S n) ≤ μ (power T n)) {r : ℕ} (hub : ∀ n, μ (power T n) ≤ r ^ n) :
    asymptoticSuperInvariant μ S ≤ asymptoticSuperInvariant μ T := by
  refine Growth.supermultiplicativeLimit_mono (C := (r : ℝ))
    (invariantPowerSequence_nonneg μ S) (fun n ↦ ?_) (invariantPowerSequence_nonneg μ T) fun n ↦ ?_
  · unfold invariantPowerSequence
    exact_mod_cast hpow n
  · unfold invariantPowerSequence
    exact_mod_cast hub n

/-- Asymptotic invariants of a restriction-monotone supermultiplicative `μ` decrease along exact
restriction. -/
theorem asymptoticSuperInvariant_restricts_le (hμ : RestrictionMonotone μ)
    {T : Tensor3 K V} {S : Tensor3 K W} (h : Restricts T S)
    {r : ℕ} (hub : ∀ n, μ (power T n) ≤ r ^ n) :
    asymptoticSuperInvariant μ S ≤ asymptoticSuperInvariant μ T :=
  asymptoticSuperInvariant_mono (fun n ↦ hμ _ _ (h.power n)) hub

/-- **Exactly geometric invariant sequences, supermultiplicative case.** -/
theorem asymptoticSuperInvariant_eq_of_pow {b : ℕ} (μ : NatInvariant.{u, v} K) (T : Tensor3 K V)
    (h : ∀ n, μ (power T n) = b ^ n) : asymptoticSuperInvariant μ T = (b : ℝ) := by
  have hseq : invariantPowerSequence μ T = fun n ↦ (b : ℝ) ^ n := by
    funext n
    show ((μ (power T n) : ℕ) : ℝ) = (b : ℝ) ^ n
    rw [h n, Nat.cast_pow]
  rw [asymptoticSuperInvariant, hseq, Growth.supermultiplicativeLimit_pow (by positivity)]

end Invariant

/-! ## Bridge: ordinary tensor rank

Ordinary rank is the motivating submultiplicative invariant.  Packaging it as a `NatInvariant`
identifies the engine's output with the existing `asymptoticRank` of `Tensor/AsymptoticRank.lean`,
which is not modified. -/

section RankBridge

variable {K : Type u} [CommSemiring K]

/-- Ordinary tensor rank, packaged as a numerical invariant on the leg universe `max u v`. -/
noncomputable def rankInvariant (K : Type u) [CommSemiring K] : NatInvariant.{u, v} K :=
  fun {_V} _ _ T ↦ rank T

/-- Tensor rank is invariant under legwise isomorphism. -/
theorem rankInvariant_isoInvariant : IsoInvariant (rankInvariant.{u, v} K) := by
  intro V W _ _ _ _ T S h
  exact rank_isomorphic h

/-- Tensor rank is submultiplicative under external products. -/
theorem rankInvariant_externalSubmultiplicative :
    ExternalSubmultiplicative (rankInvariant.{u, v} K) := by
  intro V W _ _ _ _ T S
  exact rank_external_le T S

/-- Tensor rank decreases along exact restriction. -/
theorem rankInvariant_restrictionMonotone : RestrictionMonotone (rankInvariant.{u, v} K) := by
  intro V W _ _ _ _ T S h
  exact rank_restricts_le h

variable {V : Leg → Type (max u v)} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- The engine's power sequence for `rankInvariant` is the repository's `rankPowerSequence`. -/
theorem invariantPowerSequence_rankInvariant (T : Tensor3 K V) (n : ℕ) :
    invariantPowerSequence (rankInvariant.{u, v} K) T n = (rankPowerSequence T n : ℝ) := rfl

/-- **The bridge.**  For a tensor all of whose canonical powers have positive rank, the asymptotic
invariant produced by this engine for `μ = rank` is exactly the `asymptoticRank` defined in
`Tensor/AsymptoticRank.lean`.

Proof sketch: `asymptoticRank` is the infimum of exponential bases tolerating a fixed positive
multiplicative constant, while the engine's value is the infimum of the `n`th roots.
`Growth.exponentialRate_eq_submultiplicativeLimit` identifies the two for any submultiplicative
natural sequence bounded below by `1`, and the rank sequence of tensor powers is submultiplicative
by `IsoInvariant.power_add_le` for rank. -/
theorem asymptoticRank_eq_asymptoticInvariant (T : Tensor3 K V)
    (hone : ∀ n, 1 ≤ rank (power T n)) :
    asymptoticRank T = asymptoticInvariant (rankInvariant.{u, v} K) T := by
  have hsub : ∀ m n, rankPowerSequence T (m + n) ≤ rankPowerSequence T m * rankPowerSequence T n :=
    fun m n ↦ rankInvariant_isoInvariant.power_add_le
      rankInvariant_externalSubmultiplicative T m n
  exact Growth.exponentialRate_eq_submultiplicativeLimit (a := rankPowerSequence T) hone hsub

end RankBridge

/-! ## Supermultiplicative client: asymptotic subrank

`subrank` itself --- the largest diagonal tensor that `T` restricts onto --- and its finite theory
live in `Tensor/Subrank.lean`.  Here it is packaged as a `NatInvariant`, its three structural
properties are recorded, and the schema is instantiated. -/

section AsymptoticSubrank

variable {K : Type u} [Field K]

/-- Subrank packaged as a numerical invariant on the leg universe `max u v`. -/
noncomputable def subrankInvariant (K : Type u) [CommSemiring K] : NatInvariant.{u, v} K :=
  fun {_V} _ _ T ↦ subrank T

/-- Subrank is invariant under legwise isomorphism. -/
theorem subrankInvariant_isoInvariant : IsoInvariant (subrankInvariant.{u, v} K) := by
  intro V W _ _ _ _ T S h
  exact subrank_isomorphic h

/-- Subrank is supermultiplicative under external products. -/
theorem subrankInvariant_externalSupermultiplicative :
    ExternalSupermultiplicative (subrankInvariant.{u, v} K) := by
  intro V W _ _ _ _ T S
  exact subrank_mul_le_subrank_external T S

/-- Subrank decreases along exact restriction. -/
theorem subrankInvariant_restrictionMonotone :
    RestrictionMonotone (subrankInvariant.{u, v} K) := by
  intro V W _ _ _ _ T S h
  exact subrank_restricts_le h

variable {V : Leg → Type (max u v)} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- **Asymptotic subrank**: the engine applied to the supermultiplicative invariant `subrank`,
that is the limit, equivalently the supremum, of `subrank (T^{⊗n}) ^ (1/n)`. -/
noncomputable def asymptoticSubrank (T : Tensor3 K V) : ℝ :=
  asymptoticSuperInvariant (subrankInvariant.{u, v} K) T

/-- Subrank of a tensor power is bounded by the corresponding power of ordinary rank; this is the
geometric upper bound the supermultiplicative engine requires. -/
theorem subrank_power_le_rank_pow (T : Tensor3 K V) (n : ℕ) :
    subrank (power T n) ≤ rank T ^ n :=
  (subrank_le_rank _).trans (rank_power_le T n)

/-- If `T` restricts onto the diagonal tensor of size one, then so does every tensor power, so the
subrank of every power is at least one. -/
theorem one_le_subrank_power {T : Tensor3 K V} (h : Restricts T (diagonalTensor K (Fin 1)))
    (n : ℕ) : 1 ≤ subrank (power T n) := by
  have hpow := h.power_diagonalTensor n
  rw [one_pow] at hpow
  exact le_subrank_of_restricts hpow

/-- **Existence of asymptotic subrank.**  For a tensor restricting onto the diagonal tensor of size
one, the normalized subranks `subrank (T^{⊗n}) ^ (1/n)` converge to `asymptoticSubrank T`.

Proof sketch: instantiate `tendsto_asymptoticSuperInvariant` at `μ = subrank`.  Its two structural
hypotheses are `subrankInvariant_isoInvariant` and `subrankInvariant_externalSupermultiplicative`;
positivity along powers comes from `one_le_subrank_power`, and the geometric upper bound needed by
Fekete's lemma is `subrank (T^{⊗n}) ≤ rank T ^ n`. -/
theorem tendsto_asymptoticSubrank {T : Tensor3 K V}
    (h : Restricts T (diagonalTensor K (Fin 1))) :
    Tendsto (Growth.nthRootSeq (invariantPowerSequence (subrankInvariant.{u, v} K) T)) atTop
      (𝓝 (asymptoticSubrank T)) :=
  tendsto_asymptoticSuperInvariant subrankInvariant_isoInvariant
    subrankInvariant_externalSupermultiplicative T (one_le_subrank_power h)
    (r := rank T) (subrank_power_le_rank_pow T)

/-- Asymptotic subrank dominates the ordinary subrank. -/
theorem subrank_le_asymptoticSubrank (T : Tensor3 K V) :
    (subrank T : ℝ) ≤ asymptoticSubrank T :=
  self_le_asymptoticSuperInvariant subrankInvariant_isoInvariant T
    (r := rank T) (subrank_power_le_rank_pow T)

/-- A geometric upper bound on the subranks of tensor powers bounds asymptotic subrank.

Proof sketch: taking `n`th roots turns `subrank (T^{⊗n}) ≤ r ^ n` into
`subrank (T^{⊗n}) ^ (1/n) ≤ r`, and asymptotic subrank is the supremum of those roots. -/
theorem asymptoticSubrank_le_of_pow {T : Tensor3 K V} {r : ℕ}
    (h : ∀ n, subrank (power T n) ≤ r ^ n) : asymptoticSubrank T ≤ (r : ℝ) := by
  refine asymptoticSuperInvariant_le _ T fun n hn ↦ ?_
  calc ((subrank (power T n) : ℕ) : ℝ) ^ ((n : ℝ)⁻¹)
      ≤ ((r : ℝ) ^ n) ^ ((n : ℝ)⁻¹) := by
        refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
        exact_mod_cast h n
    _ = (r : ℝ) := Real.pow_rpow_inv_natCast (by positivity) (by omega)

/-- A geometric upper bound on the *slice ranks* of tensor powers transports to asymptotic
subrank, because subrank is bounded by slice rank at every power.  This is the form in which
slice-rank barrier estimates bound asymptotic subrank. -/
theorem asymptoticSubrank_le_of_sliceRank_pow {T : Tensor3 K V} {r : ℕ}
    (h : ∀ n, sliceRank (power T n) ≤ r ^ n) : asymptoticSubrank T ≤ (r : ℝ) :=
  asymptoticSubrank_le_of_pow fun n ↦ (subrank_le_sliceRank _).trans (h n)

/-- Asymptotic subrank never exceeds ordinary tensor rank. -/
theorem asymptoticSubrank_le_rank (T : Tensor3 K V) : asymptoticSubrank T ≤ (rank T : ℝ) :=
  asymptoticSubrank_le_of_pow (subrank_power_le_rank_pow T)

end AsymptoticSubrank

end AlgebraicComplexity.Tensor
