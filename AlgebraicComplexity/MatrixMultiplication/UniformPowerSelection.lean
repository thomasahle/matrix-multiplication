/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.Subexponential
import AlgebraicComplexity.Tensor.PartitionedExtraction
import AlgebraicComplexity.MatrixMultiplication.ZeroCoordinateMerge
import AlgebraicComplexity.MatrixMultiplication.CompleteSplitStatistics
import AlgebraicComplexity.MatrixMultiplication.InterfaceTensorRealization

/-!
# Refining a selected family to a uniform local `q`-power

`ZeroCoordinateMerge` replaces a zero-coordinate class's fine dimensions `q ^ ones s` by the
merged dimension `∑ s, q ^ ones s`, and records that a class of *uniform* `ones` merges to
exactly `card * q ^ k` — the shape the committed one-slice C-tensor fusion produces.  This module
supplies the missing selection step: how a family whose members carry *varying* local `q`-powers
is refined to a sub-family carrying one common power, and what that refinement costs.

## Two routes, and the cost of each

* **The pigeonhole route, for a family selected by chunk *weight* only.**  The statistic to fix is
  the *total* value of an additive chunk statistic across the `n + 1` samples of one outer power,
  not a per-chunk value.  A statistic bounded by `chunkBound` on each chunk therefore takes at
  most `chunkBound * (n + 1) + 1` values, so `exists_uniform_fibre_mergedDimension_le` costs the
  named loss `uniformPowerLoss chunkBound n`, which is **polynomial in the outer power** and hence
  `Growth.Subexponential` — the vocabulary `Combinatorics/TypeClassCounting.lean` phrases its own
  losses in.  It is *not* a constant factor compounding once per chunk.
* **The exact route, for a family selected by an exact complete-split profile — no loss at all.**
  `PartitionedTensor.selectEncodedCompleteSplitProfiles` retains exactly those addresses whose
  encoded chunk sequence is `CompleteSplitProfile.IsConsistent` with the stored profile, and exact
  consistency is equality of empirical multiplicities.  Hence *every* additive chunk statistic —
  in particular `splitWordMiddleCount`, the exponent of the local `q`-power — is already constant
  on the selected support, with value `∑ word, counts word * statistic word` read off the profile
  (`outerChunkStatistic_eq_of_mem_selectEncodedExactInterfaceTerm_support`).  The refinement is
  free: the loss is `1` and the filter is the whole family.

The second route is the one an *exact* interface term takes.  The first is stated in full because
a family selected only by a per-sample weight — the leg-permuted and approximate variants — does
not have its profile pinned, and then the pigeonhole is exactly what is spent.

## The sub-family is a genuine degeneration

Dropping constituents from a partitioned tensor is a restriction only when the dropped addresses
can be zeroed independently on some leg.  On a shared-leg fibre the `X` label is injective, so an
arbitrary sub-family is projection closed on `{X}` and
`Tensor.Restricts.partitionedProjectionClosed` applies: `restricts_withSupport_of_injOn_x`.

No Coppersmith--Winograd constant, no certificate datum and no tensor-algebraic identity occurs
here; the fusion itself is `MatrixMultiplication/UniformPowerFusion.lean`.
-/

namespace AlgebraicComplexity

open Tensor
open scoped BigOperators

universe u v w

private theorem positivePowerProfile_counts_aux {depth : ℕ}
    (index : LevelConstituentIndex depth) (multiplicity n : ℕ)
    (split : ∀ c, CompleteSplitProfile depth (index.count c) multiplicity)
    (hmultiplicity : multiplicity = n + 1) (c : Leg) :
    ((ExactInterfaceTermParameters.mk multiplicity index split).positivePowerProfile
      hmultiplicity c).counts = (split c).counts := by
  subst hmultiplicity
  rfl

/-- The stored counts of an exact interface term's leg profile survive the outer-power transport
along `term.multiplicity = n + 1`.  Only the sample count is transported, and the counts do not
depend on it. -/
@[simp] theorem ExactInterfaceTermParameters.positivePowerProfile_counts
    {depth n : ℕ} (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (c : Leg) :
    (term.positivePowerProfile hmultiplicity c).counts = (term.split c).counts :=
  positivePowerProfile_counts_aux term.index term.multiplicity n term.split hmultiplicity c

namespace UniformPowerSelection

/-! ## The named loss -/

/-- **The uniform-local-power loss.**  An additive chunk statistic bounded by `chunkBound` on each
of the `n + 1` samples of one outer power takes at most `chunkBound * (n + 1) + 1` values, so the
pigeonhole that fixes it costs exactly that factor.  It is polynomial in the outer power `n`;
nothing asymptotic is hidden inside it. -/
noncomputable def uniformPowerLoss (chunkBound n : ℕ) : ℝ :=
  ((chunkBound * (n + 1) + 1 : ℕ) : ℝ)

theorem uniformPowerLoss_pos (chunkBound n : ℕ) : 0 < uniformPowerLoss chunkBound n := by
  unfold uniformPowerLoss
  exact_mod_cast Nat.succ_pos (chunkBound * (n + 1))

/-- The uniform-local-power loss is linear in the outer power, hence subexponential.  This is the
estimate that lets the committed *uniform* one-slice fusion be used in place of a non-uniform
one. -/
theorem uniformPowerLoss_subexponential (chunkBound : ℕ) :
    Growth.Subexponential (uniformPowerLoss chunkBound) := by
  refine Growth.Subexponential.mono
    ((Growth.Subexponential.natCast_succ_pow 1).const_mul
      (show (0 : ℝ) ≤ ((chunkBound + 1 : ℕ) : ℝ) from Nat.cast_nonneg _))
    (fun n ↦ (uniformPowerLoss_pos chunkBound n).le) (fun n ↦ ?_)
  have hone : (1 : ℕ) ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
  have hnat : chunkBound * (n + 1) + 1 ≤ (chunkBound + 1) * (n + 1) := by
    calc chunkBound * (n + 1) + 1 ≤ chunkBound * (n + 1) + (n + 1) :=
          Nat.add_le_add_left hone _
      _ = (chunkBound + 1) * (n + 1) := by ring
  unfold uniformPowerLoss
  calc ((chunkBound * (n + 1) + 1 : ℕ) : ℝ) ≤ (((chunkBound + 1) * (n + 1) : ℕ) : ℝ) := by
        exact_mod_cast hnat
    _ = ((chunkBound + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ)) ^ 1 := by
        push_cast
        ring

/-! ## The pigeonhole at the outer power -/

section Pigeonhole

variable {ι : Type*}

/-- **The uniform local `q`-power refinement, division free.**  If the local power exponent is
bounded by `chunkBound` on each of the `n + 1` samples, then some single exponent `k` carries a
`1 / (chunkBound * (n + 1) + 1)` share of the merged dimension, and its fibre merges to exactly
`card * q ^ k` — the shape the committed uniform one-slice fusion consumes. -/
theorem exists_uniform_power_fibre [DecidableEq ι]
    (q : ℕ) (ones : ι → ℕ) (cls : Finset ι) (chunkBound n : ℕ)
    (hbound : ∀ s ∈ cls, ones s ≤ chunkBound * (n + 1)) :
    ∃ k ≤ chunkBound * (n + 1),
      (∀ s ∈ cls.filter fun s ↦ ones s = k, ones s = k) ∧
        ZeroCoordinateMerge.mergedDimension q ones cls ≤
          (chunkBound * (n + 1) + 1) *
            ((cls.filter fun s ↦ ones s = k).card * q ^ k) := by
  classical
  obtain ⟨k, hk, hfibre⟩ :=
    ZeroCoordinateMerge.exists_uniform_fibre_mergedDimension_le q ones cls
      (chunkBound * (n + 1))
      (fun s hs ↦ Finset.mem_range.mpr (Nat.lt_succ_of_le (hbound s hs)))
  have huniform : ∀ s ∈ cls.filter fun s ↦ ones s = k, ones s = k :=
    fun s hs ↦ (Finset.mem_filter.mp hs).2
  refine ⟨k, Nat.lt_succ_iff.mp (Finset.mem_range.mp hk), huniform, ?_⟩
  rwa [ZeroCoordinateMerge.mergedDimension_of_uniform q ones _ huniform] at hfibre

/-- Real-valued restatement of the outer-power pigeonhole against the named subexponential
loss. -/
theorem exists_uniform_power_fibre_le_uniformPowerLoss_mul [DecidableEq ι]
    (q : ℕ) (ones : ι → ℕ) (cls : Finset ι) (chunkBound n : ℕ)
    (hbound : ∀ s ∈ cls, ones s ≤ chunkBound * (n + 1)) :
    ∃ k ≤ chunkBound * (n + 1),
      ((ZeroCoordinateMerge.mergedDimension q ones cls : ℕ) : ℝ) ≤
        uniformPowerLoss chunkBound n *
          (((cls.filter fun s ↦ ones s = k).card * q ^ k : ℕ) : ℝ) := by
  classical
  obtain ⟨k, hk, _huniform, hfibre⟩ :=
    exists_uniform_power_fibre q ones cls chunkBound n hbound
  refine ⟨k, hk, ?_⟩
  unfold uniformPowerLoss
  exact_mod_cast hfibre

/-- **A family that is already uniform pays nothing.**  Its uniform fibre is the whole family, so
the pigeonhole degenerates and the loss is `1` rather than `uniformPowerLoss`. -/
theorem filter_eq_self_of_uniform [DecidableEq ι] {ones : ι → ℕ} {cls : Finset ι} {k : ℕ}
    (huniform : ∀ s ∈ cls, ones s = k) :
    (cls.filter fun s ↦ ones s = k) = cls :=
  Finset.filter_true_of_mem huniform

end Pigeonhole

/-! ## The sub-family is a degeneration -/

section SubFamily

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type v}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- On a support whose `X` labels are pairwise distinct, *every* sub-family is cut out by zeroing
the complementary `X` block variables.  This is what makes a pigeonhole fibre a legitimate
degeneration rather than an unjustified deletion of constituents. -/
theorem isProjectionClosed_of_injOn_x
    {ambient fibre : Finset (BlockAddress A)} (hsubset : fibre ⊆ ambient)
    (hx : Set.InjOn (fun address ↦ address .X) (ambient : Set (BlockAddress A))) :
    IsProjectionClosed ambient fibre {Leg.X} := by
  refine ⟨hsubset, ?_⟩
  intro u hu hlabels
  obtain ⟨s, hs, hus⟩ := hlabels .X (Finset.mem_singleton_self _)
  have hueq : u = s :=
    hx (Finset.mem_coe.mpr hu) (Finset.mem_coe.mpr (hsubset hs)) hus
  rw [hueq]
  exact hs

/-- Tensor form of `isProjectionClosed_of_injOn_x`: a shared-leg family restricts to any of its
sub-families. -/
theorem restricts_withSupport_of_injOn_x
    (P : PartitionedTensor (K := K) (A := A) V)
    {fibre : Finset (BlockAddress A)} (hsubset : fibre ⊆ P.support)
    (hx : Set.InjOn (fun address ↦ address .X) (P.support : Set (BlockAddress A))) :
    Restricts P.realize (P.withSupport fibre).realize :=
  Restricts.partitionedProjectionClosed P fibre {Leg.X}
    (isProjectionClosed_of_injOn_x hsubset hx)

end SubFamily

/-! ## The exact route: complete-split consistency already fixes the local power -/

section ExactInterface

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {depth n : ℕ}

/-- The number of middle digits of a complete-split word is at most the number of digits. -/
theorem splitWordMiddleCount_le_two_pow {depth : ℕ} (word : SplitWord depth) :
    splitWordMiddleCount word ≤ 2 ^ depth := by
  classical
  unfold splitWordMiddleCount
  calc (∑ position, if word position = (1 : SplitDigit) then 1 else 0)
      ≤ ∑ _position : Fin (2 ^ depth), 1 :=
        Finset.sum_le_sum fun _ _ ↦ by split <;> simp
    _ = 2 ^ depth := by simp

/-- **The local power exponent of one outer address.**  The total value of an additive chunk
statistic along the encoded `c`-word of an address of the outer power.  For the middle-digit
statistic this is the exponent of the local `q`-power the constituent carries. -/
def outerChunkStatistic (encode : ∀ c, A c → SplitWord depth)
    (statistic : SplitWord depth → ℕ) (c : Leg)
    (address : BlockAddress fun c ↦ PositiveWord (A c) n) : ℕ :=
  ∑ sample, statistic (encode c (positiveWordEquiv (A c) n (address c) sample))

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- The outer exponent is bounded by the per-chunk bound times the number of samples.  This is the
bound the outer-power pigeonhole is applied at: it is polynomial in `n`, not exponential. -/
theorem outerChunkStatistic_le
    (encode : ∀ c, A c → SplitWord depth) (statistic : SplitWord depth → ℕ)
    (chunkBound : ℕ) (hstatistic : ∀ word, statistic word ≤ chunkBound)
    (c : Leg) (address : BlockAddress fun c ↦ PositiveWord (A c) n) :
    outerChunkStatistic (n := n) encode statistic c address ≤ chunkBound * (n + 1) := by
  classical
  unfold outerChunkStatistic
  calc (∑ sample, statistic (encode c (positiveWordEquiv (A c) n (address c) sample)))
      ≤ ∑ _sample : Fin (n + 1), chunkBound :=
        Finset.sum_le_sum fun _ _ ↦ hstatistic _
    _ = chunkBound * (n + 1) := by
        simp [Finset.sum_const, Finset.card_univ, mul_comm]

/-- **Exact complete-split consistency already fixes every additive chunk statistic.**  An address
survives `selectEncodedCompleteSplitProfiles` exactly when its encoded chunk sequence has the
stored empirical multiplicities, and an additive statistic of a sequence is determined by those
multiplicities.  So the local power exponent is read off the profile, with no pigeonhole. -/
theorem outerChunkStatistic_eq_of_mem_selectEncodedCompleteSplitProfiles_support
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    (index : LevelConstituentIndex depth)
    (profile : ∀ c, CompleteSplitProfile depth (index.count c) (n + 1))
    (statistic : SplitWord depth → ℕ) (c : Leg)
    (address : BlockAddress fun c ↦ PositiveWord (A c) n)
    (haddress : address ∈
      (P.selectEncodedCompleteSplitProfiles encode index profile).support) :
    outerChunkStatistic (n := n) encode statistic c address =
      ∑ word, (profile c).counts word * statistic word := by
  classical
  have hconsistent :=
    ((P.mem_selectEncodedCompleteSplitProfiles_support encode index profile address).mp
      haddress).2 c
  simpa only [outerChunkStatistic, Function.comp_apply] using
    (profile c).sum_statistic_of_isConsistent
      (encode c ∘ positiveWordEquiv (A c) n (address c)) hconsistent statistic

/-- **The uniform local power is free at an exact interface term.**  Every retained address of an
encoded exact interface term carries the same value of every additive chunk statistic — in
particular the same middle-digit count, hence the same local `q`-power.  No pigeonhole is spent
and no subexponential loss is paid. -/
theorem outerChunkStatistic_eq_of_mem_selectEncodedExactInterfaceTerm_support
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (statistic : SplitWord depth → ℕ) (c : Leg)
    (address : BlockAddress fun c ↦ PositiveWord (A c) n)
    (haddress : address ∈
      (P.selectEncodedExactInterfaceTerm encode term hmultiplicity).support) :
    outerChunkStatistic (n := n) encode statistic c address =
      ∑ word, (term.split c).counts word * statistic word := by
  have hprofile := outerChunkStatistic_eq_of_mem_selectEncodedCompleteSplitProfiles_support
    P encode term.index (fun c ↦ term.positivePowerProfile hmultiplicity c)
    statistic c address haddress
  rwa [ExactInterfaceTermParameters.positivePowerProfile_counts] at hprofile

/-- **The exact interface's merged dimension.**  On the selected support of an encoded exact
interface term the merged dimension is exactly `card * q ^ e`, with the exponent `e` read off the
stored complete-split profile.  This is `mergedDimension_of_uniform` at the uniformity the
previous theorem supplies: the merged dimension is the type-class reading `h * q ^ e`, not a
maximum over addresses. -/
theorem mergedDimension_selectEncodedExactInterfaceTerm
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (statistic : SplitWord depth → ℕ) (c : Leg) (q : ℕ) :
    ZeroCoordinateMerge.mergedDimension q
        (outerChunkStatistic (n := n) encode statistic c)
        (P.selectEncodedExactInterfaceTerm encode term hmultiplicity).support =
      (P.selectEncodedExactInterfaceTerm encode term hmultiplicity).support.card *
        q ^ (∑ word, (term.split c).counts word * statistic word) :=
  ZeroCoordinateMerge.mergedDimension_of_uniform q _ _
    (fun address haddress ↦
      outerChunkStatistic_eq_of_mem_selectEncodedExactInterfaceTerm_support
        P encode term hmultiplicity statistic c address haddress)

end ExactInterface

end UniformPowerSelection

end AlgebraicComplexity
