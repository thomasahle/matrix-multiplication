/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.SubstitutionMethod

/-!
# Multi-step substitution: kill chains at scale

`Tensor/SubstitutionMethod.lean` provides the *single* substitution step: from a rank certificate
of length `r` for `T` and a covector `φ` detecting `T`, it produces a substitution direction `v`
and a certificate of length `r - 1` for `substituteX φ v T`.  Lower bounds beyond the first few
constants need *many* such steps, with the substitution directions chosen adversarially at every
stage.  This file provides the reusable bookkeeping for those chains, in two flavours.

## Objects and principal results

### Budget-indexed adaptive chains

* `RankLE.exists_killChainX` (and the `Y`, `Z` mirrors): let `Inv : ℕ → Tensor3 K V → Prop` be an
  invariant whose numeric index is the number of substitutions still to be performed.  If from
  every tensor `S` with `Inv (k+1) S` one can exhibit a detecting covector `φ` such that *every*
  legal substitution direction lands in `Inv k`, then a length-`r` certificate for a tensor with
  `Inv k` yields a tensor `S` with `Inv 0 S` and a certificate of length `r - k`, together with
  `k ≤ r`.
* `rank_lower_of_killChainX` (and mirrors): the packaged lower bound `k + s ≤ rank T`, where `s`
  is any uniform rank lower bound valid on the terminal states `Inv 0`.

This is the general interface: the invariant may record any amount of adaptive information, so a
proof may pick the next covector depending on all previously chosen directions.

### Coordinate chains with a uniform detection certificate

Many classical arguments substitute along a fixed *biorthogonal family* of covectors, and their
detection certificates can be checked once and for all on the source tensor.  For that fragment
this file provides an interface with no invariant at all:

* `substProjChain φ L`: the composite linear map of the substitution chain described by a list `L`
  of (index, direction) pairs, applied in list order.  Like `substProj` of
  `Tensor/SubstitutionMethod.lean` it is a statement about a single module, so the three leg names
  `substProjXChain`, `substProjYChain`, `substProjZChain` are abbreviations for it and the
  protection lemma below is proved once;
* `substituteXChain φ L T`: the tensor obtained by performing those substitutions in list order;
* `contractX_substituteXChain`, `contractY_substituteXChain`, `contractZ_substituteXChain`:
  contractions of a chained tensor, either as the composite projection of a contraction of the
  source (the retained leg) or as a contraction against a precomposed covector (the other legs);
* `substProjChain_apply_of_forall_ker` (leg aliases `substProjXChain_apply_of_forall_ker` and
  mirrors): the *protection* lemma.  The composite projection fixes every vector annihilated by
  all covectors of the chain; this is what makes an untouched coordinate row survive an
  arbitrarily long chain, uniformly in the adversarial directions;
* `RankLE.exists_substituteXChain`: the multi-step kill.  If `qs : List ι` is a duplicate-free
  list of indices and each `q ∈ qs` is detected in `T` by a product contraction whose value is
  *normalized against the whole family* (`φ q' (contractX fy fz T) = if q' = q then 1 else 0`),
  then there is a chain `L` over exactly the indices `qs`, with `φ q v = 1` at every step, such
  that `substituteXChain φ L T` has a certificate of length `r - qs.length`, and
  `qs.length ≤ r`;
* `rank_lower_of_substituteXChain`: the packaged bound `qs.length + s ≤ rank T`, where `s` is a
  rank lower bound valid for every chain over `qs` — in practice supplied by a conciseness
  argument on a leg that the chain provably does not disturb.

Each of these has its `Y` and `Z` mirror (`substituteYChain`, `substituteZChain`, and so on), so a
client may kill variables on any leg without first permuting the tensor.  As of this writing the
mirrors are *unused*: the only client, `Examples/BlaeserLowerBound.lean`, kills on `X` and obtains
its `Y` and `Z` forms by `RankLE.matrixMultiplication_cycle`.  They are kept deliberately — after
the module-level `substProjChain` factorization they cost a handful of one-line aliases each — but
a client, not a mirror, is what should justify any *further* per-leg machinery here.

## Layer placement and strategy

This is a layer-1 tensor-algebra module.  It imports only `Tensor/SubstitutionMethod` and mentions
no matrix-multiplication construction and no numerical bound.

Proof sketch for the chain kill: induction on the list of indices.  The head index `q` is detected
in `T` by hypothesis, so one substitution step removes one term of the certificate and produces a
direction `v` with `φ q v = 1`.  For the tail one has to re-establish the detection hypothesis for
the substituted tensor: contracting the substituted tensor equals `substProjX (φ q) v` applied to
the contraction of the source (`contractX_substituteX`), and the normalization hypothesis says
that the detection vector of any *other* index of the family is annihilated by `φ q`, so the
projection leaves it unchanged.  Duplicate-freeness is exactly what makes "other index" apply to
every remaining step.  The final bookkeeping `qs.length ≤ r` comes from the fact that a detected
tensor is nonzero, so each step consumes a genuinely present term.

## Non-goals

The chain interface transports only *rank certificates*; border rank and degeneration versions of
the substitution method are deliberately left to future work.  As in `Tensor/SubstitutionMethod`,
detection is stated against a rank-one (product) covector on the two untouched legs, which is what
explicit coordinate certificates provide.  Chains on two different legs are not combined into a
single interface: a client that needs them composes the packaged bounds, applying one leg's chain
lemma to the tensor produced by the other's.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

section KillChain

variable {K : Type u} [Field K]
variable {V : Leg → Type v}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

/-- **Budget-indexed kill chain on the `X` leg.**  Let `Inv k S` be an invariant whose index `k`
counts the substitutions still to be performed.  Assume that from every state with a positive
budget one can produce a covector `φ` detecting the current tensor through a product contraction,
such that *every* substitution direction `v` normalized by `φ v = 1` decreases the budget.  Then a
rank certificate of length `r` for a tensor `T` in state `k` produces a terminal tensor `S` in
state `0` with a certificate of length `r - k`, and `k ≤ r`.

Proof sketch: induction on the budget `k`.  The step hypothesis supplies a detecting covector, so
`RankLE.exists_substituteX` returns a direction `v` with `φ v = 1` and a certificate of length
`r - 1` for the substituted tensor, which lies in state `k` by hypothesis; the induction
hypothesis finishes.  Detection forces `T ≠ 0`, hence `1 ≤ r`, which is what keeps the natural
number subtraction honest and yields `k + 1 ≤ r`. -/
theorem RankLE.exists_killChainX {Inv : ℕ → Tensor3 K V → Prop}
    (hstep : ∀ (k : ℕ) (S : Tensor3 K V), Inv (k + 1) S →
      ∃ (φ : V .X →ₗ[K] K) (fy : V .Y →ₗ[K] K) (fz : V .Z →ₗ[K] K),
        φ (contractX fy fz S) ≠ 0 ∧
          ∀ v : V .X, φ v = 1 → Inv k (substituteX φ v S)) :
    ∀ {k r : ℕ} {T : Tensor3 K V}, RankLE r T → Inv k T →
      ∃ S : Tensor3 K V, Inv 0 S ∧ RankLE (r - k) S ∧ k ≤ r := by
  intro k
  induction k with
  | zero =>
      intro r T hT hInv
      exact ⟨T, hInv, by simpa using hT, Nat.zero_le r⟩
  | succ k ih =>
      intro r T hT hInv
      obtain ⟨φ, fy, fz, hdet, hnext⟩ := hstep k T hInv
      obtain ⟨v, hv, hsub⟩ := hT.exists_substituteX φ hdet
      have hTne : T ≠ 0 := by
        rintro rfl
        simp at hdet
      have hr : 1 ≤ r := by
        rcases Nat.eq_zero_or_pos r with rfl | h
        · exact absurd hT.eq_zero hTne
        · exact h
      obtain ⟨S, hS0, hSrank, hkr⟩ := ih hsub (hnext v hv)
      refine ⟨S, hS0, ?_, by omega⟩
      have hsubs : r - 1 - k = r - (k + 1) := by omega
      rwa [hsubs] at hSrank

/-- **Budget-indexed kill chain on the `Y` leg**; see `RankLE.exists_killChainX`. -/
theorem RankLE.exists_killChainY {Inv : ℕ → Tensor3 K V → Prop}
    (hstep : ∀ (k : ℕ) (S : Tensor3 K V), Inv (k + 1) S →
      ∃ (φ : V .Y →ₗ[K] K) (fx : V .X →ₗ[K] K) (fz : V .Z →ₗ[K] K),
        φ (contractY fx fz S) ≠ 0 ∧
          ∀ v : V .Y, φ v = 1 → Inv k (substituteY φ v S)) :
    ∀ {k r : ℕ} {T : Tensor3 K V}, RankLE r T → Inv k T →
      ∃ S : Tensor3 K V, Inv 0 S ∧ RankLE (r - k) S ∧ k ≤ r := by
  intro k
  induction k with
  | zero =>
      intro r T hT hInv
      exact ⟨T, hInv, by simpa using hT, Nat.zero_le r⟩
  | succ k ih =>
      intro r T hT hInv
      obtain ⟨φ, fx, fz, hdet, hnext⟩ := hstep k T hInv
      obtain ⟨v, hv, hsub⟩ := hT.exists_substituteY φ hdet
      have hTne : T ≠ 0 := by
        rintro rfl
        simp at hdet
      have hr : 1 ≤ r := by
        rcases Nat.eq_zero_or_pos r with rfl | h
        · exact absurd hT.eq_zero hTne
        · exact h
      obtain ⟨S, hS0, hSrank, hkr⟩ := ih hsub (hnext v hv)
      refine ⟨S, hS0, ?_, by omega⟩
      have hsubs : r - 1 - k = r - (k + 1) := by omega
      rwa [hsubs] at hSrank

/-- **Budget-indexed kill chain on the `Z` leg**; see `RankLE.exists_killChainX`. -/
theorem RankLE.exists_killChainZ {Inv : ℕ → Tensor3 K V → Prop}
    (hstep : ∀ (k : ℕ) (S : Tensor3 K V), Inv (k + 1) S →
      ∃ (φ : V .Z →ₗ[K] K) (fx : V .X →ₗ[K] K) (fy : V .Y →ₗ[K] K),
        φ (contractZ fx fy S) ≠ 0 ∧
          ∀ v : V .Z, φ v = 1 → Inv k (substituteZ φ v S)) :
    ∀ {k r : ℕ} {T : Tensor3 K V}, RankLE r T → Inv k T →
      ∃ S : Tensor3 K V, Inv 0 S ∧ RankLE (r - k) S ∧ k ≤ r := by
  intro k
  induction k with
  | zero =>
      intro r T hT hInv
      exact ⟨T, hInv, by simpa using hT, Nat.zero_le r⟩
  | succ k ih =>
      intro r T hT hInv
      obtain ⟨φ, fx, fy, hdet, hnext⟩ := hstep k T hInv
      obtain ⟨v, hv, hsub⟩ := hT.exists_substituteZ φ hdet
      have hTne : T ≠ 0 := by
        rintro rfl
        simp at hdet
      have hr : 1 ≤ r := by
        rcases Nat.eq_zero_or_pos r with rfl | h
        · exact absurd hT.eq_zero hTne
        · exact h
      obtain ⟨S, hS0, hSrank, hkr⟩ := ih hsub (hnext v hv)
      refine ⟨S, hS0, ?_, by omega⟩
      have hsubs : r - 1 - k = r - (k + 1) := by omega
      rwa [hsubs] at hSrank

/-- Packaged budget-indexed lower bound on the `X` leg: if `T` is in state `k` and every terminal
state has rank at least `s`, then `rank T ≥ k + s`.  Each of the `k` substitutions removes one
term of a minimal decomposition, and the terminal tensor still needs `s` of them. -/
theorem rank_lower_of_killChainX {Inv : ℕ → Tensor3 K V → Prop}
    (hstep : ∀ (k : ℕ) (S : Tensor3 K V), Inv (k + 1) S →
      ∃ (φ : V .X →ₗ[K] K) (fy : V .Y →ₗ[K] K) (fz : V .Z →ₗ[K] K),
        φ (contractX fy fz S) ≠ 0 ∧
          ∀ v : V .X, φ v = 1 → Inv k (substituteX φ v S))
    {k s : ℕ} {T : Tensor3 K V} (hInv : Inv k T)
    (hfinal : ∀ S : Tensor3 K V, Inv 0 S → s ≤ rank S) :
    k + s ≤ rank T := by
  obtain ⟨S, hS0, hSrank, hkr⟩ := RankLE.exists_killChainX hstep (rank_spec T) hInv
  have h1 : s ≤ rank T - k := (hfinal S hS0).trans (rank_le_iff.mpr hSrank)
  omega

/-- Packaged budget-indexed lower bound on the `Y` leg; see `rank_lower_of_killChainX`. -/
theorem rank_lower_of_killChainY {Inv : ℕ → Tensor3 K V → Prop}
    (hstep : ∀ (k : ℕ) (S : Tensor3 K V), Inv (k + 1) S →
      ∃ (φ : V .Y →ₗ[K] K) (fx : V .X →ₗ[K] K) (fz : V .Z →ₗ[K] K),
        φ (contractY fx fz S) ≠ 0 ∧
          ∀ v : V .Y, φ v = 1 → Inv k (substituteY φ v S))
    {k s : ℕ} {T : Tensor3 K V} (hInv : Inv k T)
    (hfinal : ∀ S : Tensor3 K V, Inv 0 S → s ≤ rank S) :
    k + s ≤ rank T := by
  obtain ⟨S, hS0, hSrank, hkr⟩ := RankLE.exists_killChainY hstep (rank_spec T) hInv
  have h1 : s ≤ rank T - k := (hfinal S hS0).trans (rank_le_iff.mpr hSrank)
  omega

/-- Packaged budget-indexed lower bound on the `Z` leg; see `rank_lower_of_killChainX`. -/
theorem rank_lower_of_killChainZ {Inv : ℕ → Tensor3 K V → Prop}
    (hstep : ∀ (k : ℕ) (S : Tensor3 K V), Inv (k + 1) S →
      ∃ (φ : V .Z →ₗ[K] K) (fx : V .X →ₗ[K] K) (fy : V .Y →ₗ[K] K),
        φ (contractZ fx fy S) ≠ 0 ∧
          ∀ v : V .Z, φ v = 1 → Inv k (substituteZ φ v S))
    {k s : ℕ} {T : Tensor3 K V} (hInv : Inv k T)
    (hfinal : ∀ S : Tensor3 K V, Inv 0 S → s ≤ rank S) :
    k + s ≤ rank T := by
  obtain ⟨S, hS0, hSrank, hkr⟩ := RankLE.exists_killChainZ hstep (rank_spec T) hInv
  have h1 : s ≤ rank T - k := (hfinal S hS0).trans (rank_le_iff.mpr hSrank)
  omega

end KillChain

section ChainModule

variable {K : Type u} [Field K] {M : Type v} [AddCommGroup M] [Module K M] {ι : Type w}

/-- The composite linear map of a substitution chain in a single module: the list `L` of
(index, direction) pairs is applied in list order, so the head of the list acts first.  The three
leg-specific names `substProjXChain`, `substProjYChain`, `substProjZChain` are reducible
abbreviations for it. -/
def substProjChain (φ : ι → (M →ₗ[K] K)) : List (ι × M) → (M →ₗ[K] M)
  | [] => LinearMap.id
  | (q, v) :: L => substProjChain φ L ∘ₗ substProj (φ q) v

@[simp] theorem substProjChain_nil (φ : ι → (M →ₗ[K] K)) :
    substProjChain φ ([] : List (ι × M)) = LinearMap.id := rfl

@[simp] theorem substProjChain_cons (φ : ι → (M →ₗ[K] K)) (q : ι) (v : M) (L : List (ι × M)) :
    substProjChain φ ((q, v) :: L) = substProjChain φ L ∘ₗ substProj (φ q) v := rfl

/-- **Protection lemma.**  The composite projection of a substitution chain fixes every vector
annihilated by all covectors used in the chain, uniformly in the substitution directions.

Proof sketch: induction on the chain.  Each individual substitution projection
`w ↦ w - φ q w • v` acts as the identity on `ker (φ q)`, and the hypothesis puts `w` in every one
of those kernels, so no step can move it. -/
theorem substProjChain_apply_of_forall_ker (φ : ι → (M →ₗ[K] K))
    {L : List (ι × M)} {w : M} (h : ∀ qv ∈ L, φ qv.1 w = 0) :
    substProjChain φ L w = w := by
  induction L with
  | nil => simp
  | cons qv L ih =>
      obtain ⟨q, v⟩ := qv
      rw [substProjChain_cons, LinearMap.comp_apply,
        substProj_apply_of_ker v (h (q, v) (List.mem_cons_self))]
      exact ih fun x hx ↦ h x (List.mem_cons_of_mem _ hx)

/-- A covector precomposed with a substitution chain agrees with the covector itself on every
vector annihilated by all covectors of the chain. -/
theorem comp_substProjChain_apply (φ : ι → (M →ₗ[K] K)) (f : M →ₗ[K] K)
    {L : List (ι × M)} {w : M} (h : ∀ qv ∈ L, φ qv.1 w = 0) :
    (f ∘ₗ substProjChain φ L) w = f w := by
  rw [LinearMap.comp_apply, substProjChain_apply_of_forall_ker φ h]

end ChainModule

section CoordinateChain

variable {K : Type u} [Field K]
variable {V : Leg → Type v}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
variable {ι : Type w}

/-- The composite `X`-leg linear map of the substitution chain described by the list `L` of
(index, direction) pairs, with the covector family `φ`.  The substitutions are applied in list
order, so the head of the list acts first. -/
abbrev substProjXChain (φ : ι → (V .X →ₗ[K] K)) (L : List (ι × V .X)) :
    V .X →ₗ[K] V .X := substProjChain φ L

@[simp] theorem substProjXChain_nil (φ : ι → (V .X →ₗ[K] K)) :
    substProjXChain φ ([] : List (ι × V .X)) = LinearMap.id := rfl

@[simp] theorem substProjXChain_cons (φ : ι → (V .X →ₗ[K] K)) (q : ι) (v : V .X)
    (L : List (ι × V .X)) :
    substProjXChain φ ((q, v) :: L) = substProjXChain φ L ∘ₗ substProjX (φ q) v := rfl

/-- The tensor obtained by performing the substitutions of the chain `L` on the `X` leg, in list
order. -/
def substituteXChain (φ : ι → (V .X →ₗ[K] K)) :
    List (ι × V .X) → Tensor3 K V → Tensor3 K V
  | [], T => T
  | (q, v) :: L, T => substituteXChain φ L (substituteX (φ q) v T)

@[simp] theorem substituteXChain_nil (φ : ι → (V .X →ₗ[K] K)) (T : Tensor3 K V) :
    substituteXChain φ [] T = T := rfl

@[simp] theorem substituteXChain_cons (φ : ι → (V .X →ₗ[K] K)) (q : ι) (v : V .X)
    (L : List (ι × V .X)) (T : Tensor3 K V) :
    substituteXChain φ ((q, v) :: L) T = substituteXChain φ L (substituteX (φ q) v T) := rfl

/-- An `X`-retaining contraction of a chained tensor is the composite chain projection applied to
the corresponding contraction of the source. -/
theorem contractX_substituteXChain (φ : ι → (V .X →ₗ[K] K)) (L : List (ι × V .X))
    (fy : V .Y →ₗ[K] K) (fz : V .Z →ₗ[K] K) (T : Tensor3 K V) :
    contractX fy fz (substituteXChain φ L T) =
      substProjXChain φ L (contractX fy fz T) := by
  induction L generalizing T with
  | nil => simp
  | cons qv L ih =>
      obtain ⟨q, v⟩ := qv
      rw [substituteXChain_cons, ih, contractX_substituteX, substProjXChain_cons,
        LinearMap.comp_apply]

/-- A `Y`-retaining contraction of a chained tensor is the contraction of the source against the
`X`-covector precomposed with the composite chain projection. -/
theorem contractY_substituteXChain (φ : ι → (V .X →ₗ[K] K)) (L : List (ι × V .X))
    (fx : V .X →ₗ[K] K) (fz : V .Z →ₗ[K] K) (T : Tensor3 K V) :
    contractY fx fz (substituteXChain φ L T) =
      contractY (fx ∘ₗ substProjXChain φ L) fz T := by
  induction L generalizing T with
  | nil => simp
  | cons qv L ih =>
      obtain ⟨q, v⟩ := qv
      rw [substituteXChain_cons, ih, contractY_substituteX, substProjXChain_cons,
        LinearMap.comp_assoc]

/-- A `Z`-retaining contraction of a chained tensor is the contraction of the source against the
`X`-covector precomposed with the composite chain projection. -/
theorem contractZ_substituteXChain (φ : ι → (V .X →ₗ[K] K)) (L : List (ι × V .X))
    (fx : V .X →ₗ[K] K) (fy : V .Y →ₗ[K] K) (T : Tensor3 K V) :
    contractZ fx fy (substituteXChain φ L T) =
      contractZ (fx ∘ₗ substProjXChain φ L) fy T := by
  induction L generalizing T with
  | nil => simp
  | cons qv L ih =>
      obtain ⟨q, v⟩ := qv
      rw [substituteXChain_cons, ih, contractZ_substituteX, substProjXChain_cons,
        LinearMap.comp_assoc]

/-- **Protection lemma.**  The composite projection of a substitution chain fixes every vector
annihilated by all covectors used in the chain, uniformly in the substitution directions.

Proof sketch: induction on the chain.  Each individual substitution projection
`w ↦ w - φ q w • v` acts as the identity on `ker (φ q)`, and the hypothesis puts `w` in every one
of those kernels, so no step can move it. -/
theorem substProjXChain_apply_of_forall_ker (φ : ι → (V .X →ₗ[K] K))
    {L : List (ι × V .X)} {w : V .X} (h : ∀ qv ∈ L, φ qv.1 w = 0) :
    substProjXChain φ L w = w := substProjChain_apply_of_forall_ker φ h

/-- A covector precomposed with a substitution chain agrees with the covector itself on every
vector annihilated by all covectors of the chain. -/
theorem comp_substProjXChain_apply (φ : ι → (V .X →ₗ[K] K)) (fx : V .X →ₗ[K] K)
    {L : List (ι × V .X)} {w : V .X} (h : ∀ qv ∈ L, φ qv.1 w = 0) :
    (fx ∘ₗ substProjXChain φ L) w = fx w := comp_substProjChain_apply φ fx h

/-- **Multi-step substitution on the `X` leg with a uniform detection certificate.**

Let `φ : ι → (V .X)*` be a family of covectors and `qs` a duplicate-free list of indices.  Assume
that every `q ∈ qs` is detected in `T` by a product contraction whose value is normalized against
the whole family: some `fy, fz` satisfy `φ q' (contractX fy fz T) = if q' = q then 1 else 0` for
all `q' ∈ qs`.  Then there is a substitution chain `L` over exactly the indices `qs`, with
`φ q v = 1` at every step, such that the chained tensor has a rank certificate of length
`r - qs.length`; moreover `qs.length ≤ r`.

Proof sketch: induction on `qs`.  The head index is detected, so one application of
`RankLE.exists_substituteX` removes a term and returns a normalized direction.  The detection
certificates of the remaining indices survive that step: contracting the substituted tensor
applies `substProjX (φ q) v` to the old contraction (`contractX_substituteX`), and the
normalization hypothesis says `φ q` annihilates the detection vector of every other index, so the
projection fixes it.  Duplicate-freeness of `qs` guarantees that all remaining indices are indeed
other indices.  Finally, a detected tensor is nonzero, so each step really consumes a term of the
certificate, giving `qs.length ≤ r`. -/
theorem RankLE.exists_substituteXChain [DecidableEq ι] (φ : ι → (V .X →ₗ[K] K)) :
    ∀ {qs : List ι} {r : ℕ} {T : Tensor3 K V}, RankLE r T → qs.Nodup →
      (∀ q ∈ qs, ∃ (fy : V .Y →ₗ[K] K) (fz : V .Z →ₗ[K] K),
          ∀ q' ∈ qs, φ q' (contractX fy fz T) = if q' = q then 1 else 0) →
      ∃ L : List (ι × V .X), L.map Prod.fst = qs ∧ (∀ qv ∈ L, φ qv.1 qv.2 = 1) ∧
        RankLE (r - qs.length) (substituteXChain φ L T) ∧ qs.length ≤ r := by
  intro qs
  induction qs with
  | nil =>
      intro r T hT _ _
      exact ⟨[], rfl, by simp, by simpa using hT, Nat.zero_le r⟩
  | cons q qs ih =>
      intro r T hT hnd hdet
      obtain ⟨fy, fz, hval⟩ := hdet q (List.mem_cons_self)
      have hq1 : φ q (contractX fy fz T) = 1 := by
        simpa using hval q (List.mem_cons_self)
      have hslice : φ q (contractX fy fz T) ≠ 0 := by
        rw [hq1]
        exact one_ne_zero
      obtain ⟨v, hv, hsub⟩ := hT.exists_substituteX (φ q) hslice
      have hTne : T ≠ 0 := by
        rintro rfl
        simp at hslice
      have hr : 1 ≤ r := by
        rcases Nat.eq_zero_or_pos r with rfl | h
        · exact absurd hT.eq_zero hTne
        · exact h
      have hqnot : q ∉ qs := (List.nodup_cons.mp hnd).1
      -- the detection certificates of the remaining indices survive the first substitution
      have hdet' : ∀ q'' ∈ qs, ∃ (fy' : V .Y →ₗ[K] K) (fz' : V .Z →ₗ[K] K),
          ∀ q' ∈ qs, φ q' (contractX fy' fz' (substituteX (φ q) v T)) =
            if q' = q'' then 1 else 0 := by
        intro q'' hq''
        obtain ⟨fy', fz', hval'⟩ := hdet q'' (List.mem_cons_of_mem _ hq'')
        have hqzero : φ q (contractX fy' fz' T) = 0 := by
          have hne : q ≠ q'' := fun h ↦ hqnot (h ▸ hq'')
          simpa [hne] using hval' q (List.mem_cons_self)
        refine ⟨fy', fz', fun q' hq' ↦ ?_⟩
        rw [contractX_substituteX, substProjX_apply, hqzero, zero_smul, sub_zero]
        exact hval' q' (List.mem_cons_of_mem _ hq')
      obtain ⟨L, hmap, hnorm, hrank, hlen⟩ :=
        ih hsub (List.nodup_cons.mp hnd).2 hdet'
      refine ⟨(q, v) :: L, by simp [hmap], ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hv
        · exact hnorm x hx
      · rw [substituteXChain_cons]
        have hsubs : r - 1 - qs.length = r - (q :: qs).length := by
          simp only [List.length_cons]
          omega
        rwa [hsubs] at hrank
      · simp only [List.length_cons]
        omega

/-- **Packaged multi-step substitution lower bound on the `X` leg.**  With the hypotheses of
`RankLE.exists_substituteXChain`, if every substitution chain over the index list `qs` leaves a
tensor of rank at least `s`, then `rank T ≥ qs.length + s`.

In applications `s` comes from a conciseness argument on a leg that the chain provably does not
disturb: `substProjXChain_apply_of_forall_ker` shows that contractions pinned to coordinates
outside the killed family are unchanged, uniformly in the adversarial substitution directions. -/
theorem rank_lower_of_substituteXChain [DecidableEq ι] (φ : ι → (V .X →ₗ[K] K)) {qs : List ι}
    {T : Tensor3 K V} {s : ℕ} (hnd : qs.Nodup)
    (hdet : ∀ q ∈ qs, ∃ (fy : V .Y →ₗ[K] K) (fz : V .Z →ₗ[K] K),
        ∀ q' ∈ qs, φ q' (contractX fy fz T) = if q' = q then 1 else 0)
    (hfinal : ∀ L : List (ι × V .X), L.map Prod.fst = qs → (∀ qv ∈ L, φ qv.1 qv.2 = 1) →
        s ≤ rank (substituteXChain φ L T)) :
    qs.length + s ≤ rank T := by
  obtain ⟨L, hmap, hnorm, hrank, hlen⟩ :=
    RankLE.exists_substituteXChain φ (rank_spec T) hnd hdet
  have h1 : s ≤ rank T - qs.length := (hfinal L hmap hnorm).trans (rank_le_iff.mpr hrank)
  omega

/-! ### The `Y`-leg mirror -/

/-- The composite `Y`-leg linear map of a substitution chain; see `substProjXChain`. -/
abbrev substProjYChain (φ : ι → (V .Y →ₗ[K] K)) (L : List (ι × V .Y)) :
    V .Y →ₗ[K] V .Y := substProjChain φ L

@[simp] theorem substProjYChain_nil (φ : ι → (V .Y →ₗ[K] K)) :
    substProjYChain φ ([] : List (ι × V .Y)) = LinearMap.id := rfl

@[simp] theorem substProjYChain_cons (φ : ι → (V .Y →ₗ[K] K)) (q : ι) (v : V .Y)
    (L : List (ι × V .Y)) :
    substProjYChain φ ((q, v) :: L) = substProjYChain φ L ∘ₗ substProjY (φ q) v := rfl

/-- The tensor obtained by performing the substitutions of the chain `L` on the `Y` leg, in list
order. -/
def substituteYChain (φ : ι → (V .Y →ₗ[K] K)) :
    List (ι × V .Y) → Tensor3 K V → Tensor3 K V
  | [], T => T
  | (q, v) :: L, T => substituteYChain φ L (substituteY (φ q) v T)

@[simp] theorem substituteYChain_nil (φ : ι → (V .Y →ₗ[K] K)) (T : Tensor3 K V) :
    substituteYChain φ [] T = T := rfl

@[simp] theorem substituteYChain_cons (φ : ι → (V .Y →ₗ[K] K)) (q : ι) (v : V .Y)
    (L : List (ι × V .Y)) (T : Tensor3 K V) :
    substituteYChain φ ((q, v) :: L) T = substituteYChain φ L (substituteY (φ q) v T) := rfl

/-- A `Y`-retaining contraction of a `Y`-chained tensor is the composite chain projection applied
to the corresponding contraction of the source. -/
theorem contractY_substituteYChain (φ : ι → (V .Y →ₗ[K] K)) (L : List (ι × V .Y))
    (fx : V .X →ₗ[K] K) (fz : V .Z →ₗ[K] K) (T : Tensor3 K V) :
    contractY fx fz (substituteYChain φ L T) =
      substProjYChain φ L (contractY fx fz T) := by
  induction L generalizing T with
  | nil => simp
  | cons qv L ih =>
      obtain ⟨q, v⟩ := qv
      rw [substituteYChain_cons, ih, contractY_substituteY, substProjYChain_cons,
        LinearMap.comp_apply]

/-- An `X`-retaining contraction of a `Y`-chained tensor is the contraction of the source against
the `Y`-covector precomposed with the composite chain projection. -/
theorem contractX_substituteYChain (φ : ι → (V .Y →ₗ[K] K)) (L : List (ι × V .Y))
    (fy : V .Y →ₗ[K] K) (fz : V .Z →ₗ[K] K) (T : Tensor3 K V) :
    contractX fy fz (substituteYChain φ L T) =
      contractX (fy ∘ₗ substProjYChain φ L) fz T := by
  induction L generalizing T with
  | nil => simp
  | cons qv L ih =>
      obtain ⟨q, v⟩ := qv
      rw [substituteYChain_cons, ih, contractX_substituteY, substProjYChain_cons,
        LinearMap.comp_assoc]

/-- A `Z`-retaining contraction of a `Y`-chained tensor is the contraction of the source against
the `Y`-covector precomposed with the composite chain projection. -/
theorem contractZ_substituteYChain (φ : ι → (V .Y →ₗ[K] K)) (L : List (ι × V .Y))
    (fx : V .X →ₗ[K] K) (fy : V .Y →ₗ[K] K) (T : Tensor3 K V) :
    contractZ fx fy (substituteYChain φ L T) =
      contractZ fx (fy ∘ₗ substProjYChain φ L) T := by
  induction L generalizing T with
  | nil => simp
  | cons qv L ih =>
      obtain ⟨q, v⟩ := qv
      rw [substituteYChain_cons, ih, contractZ_substituteY, substProjYChain_cons,
        LinearMap.comp_assoc]

/-- Protection lemma on the `Y` leg: the composite projection of a substitution chain fixes every
vector annihilated by all covectors of the chain. -/
theorem substProjYChain_apply_of_forall_ker (φ : ι → (V .Y →ₗ[K] K))
    {L : List (ι × V .Y)} {w : V .Y} (h : ∀ qv ∈ L, φ qv.1 w = 0) :
    substProjYChain φ L w = w := substProjChain_apply_of_forall_ker φ h

/-- A covector precomposed with a substitution chain agrees with the covector itself on every
vector annihilated by all covectors of the chain. -/
theorem comp_substProjYChain_apply (φ : ι → (V .Y →ₗ[K] K)) (fy : V .Y →ₗ[K] K)
    {L : List (ι × V .Y)} {w : V .Y} (h : ∀ qv ∈ L, φ qv.1 w = 0) :
    (fy ∘ₗ substProjYChain φ L) w = fy w := comp_substProjChain_apply φ fy h

/-- Multi-step substitution on the `Y` leg with a uniform detection certificate; see
`RankLE.exists_substituteXChain` for the statement pattern and proof sketch. -/
theorem RankLE.exists_substituteYChain [DecidableEq ι] (φ : ι → (V .Y →ₗ[K] K)) :
    ∀ {qs : List ι} {r : ℕ} {T : Tensor3 K V}, RankLE r T → qs.Nodup →
      (∀ q ∈ qs, ∃ (fx : V .X →ₗ[K] K) (fz : V .Z →ₗ[K] K),
          ∀ q' ∈ qs, φ q' (contractY fx fz T) = if q' = q then 1 else 0) →
      ∃ L : List (ι × V .Y), L.map Prod.fst = qs ∧ (∀ qv ∈ L, φ qv.1 qv.2 = 1) ∧
        RankLE (r - qs.length) (substituteYChain φ L T) ∧ qs.length ≤ r := by
  intro qs
  induction qs with
  | nil =>
      intro r T hT _ _
      exact ⟨[], rfl, by simp, by simpa using hT, Nat.zero_le r⟩
  | cons q qs ih =>
      intro r T hT hnd hdet
      obtain ⟨fx, fz, hval⟩ := hdet q (List.mem_cons_self)
      have hq1 : φ q (contractY fx fz T) = 1 := by
        simpa using hval q (List.mem_cons_self)
      have hslice : φ q (contractY fx fz T) ≠ 0 := by
        rw [hq1]
        exact one_ne_zero
      obtain ⟨v, hv, hsub⟩ := hT.exists_substituteY (φ q) hslice
      have hTne : T ≠ 0 := by
        rintro rfl
        simp at hslice
      have hr : 1 ≤ r := by
        rcases Nat.eq_zero_or_pos r with rfl | h
        · exact absurd hT.eq_zero hTne
        · exact h
      have hqnot : q ∉ qs := (List.nodup_cons.mp hnd).1
      have hdet' : ∀ q'' ∈ qs, ∃ (fx' : V .X →ₗ[K] K) (fz' : V .Z →ₗ[K] K),
          ∀ q' ∈ qs, φ q' (contractY fx' fz' (substituteY (φ q) v T)) =
            if q' = q'' then 1 else 0 := by
        intro q'' hq''
        obtain ⟨fx', fz', hval'⟩ := hdet q'' (List.mem_cons_of_mem _ hq'')
        have hqzero : φ q (contractY fx' fz' T) = 0 := by
          have hne : q ≠ q'' := fun h ↦ hqnot (h ▸ hq'')
          simpa [hne] using hval' q (List.mem_cons_self)
        refine ⟨fx', fz', fun q' hq' ↦ ?_⟩
        rw [contractY_substituteY, substProjY_apply, hqzero, zero_smul, sub_zero]
        exact hval' q' (List.mem_cons_of_mem _ hq')
      obtain ⟨L, hmap, hnorm, hrank, hlen⟩ :=
        ih hsub (List.nodup_cons.mp hnd).2 hdet'
      refine ⟨(q, v) :: L, by simp [hmap], ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hv
        · exact hnorm x hx
      · rw [substituteYChain_cons]
        have hsubs : r - 1 - qs.length = r - (q :: qs).length := by
          simp only [List.length_cons]
          omega
        rwa [hsubs] at hrank
      · simp only [List.length_cons]
        omega

/-- Packaged multi-step substitution lower bound on the `Y` leg; see
`rank_lower_of_substituteXChain`. -/
theorem rank_lower_of_substituteYChain [DecidableEq ι] (φ : ι → (V .Y →ₗ[K] K)) {qs : List ι}
    {T : Tensor3 K V} {s : ℕ} (hnd : qs.Nodup)
    (hdet : ∀ q ∈ qs, ∃ (fx : V .X →ₗ[K] K) (fz : V .Z →ₗ[K] K),
        ∀ q' ∈ qs, φ q' (contractY fx fz T) = if q' = q then 1 else 0)
    (hfinal : ∀ L : List (ι × V .Y), L.map Prod.fst = qs → (∀ qv ∈ L, φ qv.1 qv.2 = 1) →
        s ≤ rank (substituteYChain φ L T)) :
    qs.length + s ≤ rank T := by
  obtain ⟨L, hmap, hnorm, hrank, hlen⟩ :=
    RankLE.exists_substituteYChain φ (rank_spec T) hnd hdet
  have h1 : s ≤ rank T - qs.length := (hfinal L hmap hnorm).trans (rank_le_iff.mpr hrank)
  omega

/-! ### The `Z`-leg mirror -/

/-- The composite `Z`-leg linear map of a substitution chain; see `substProjXChain`. -/
abbrev substProjZChain (φ : ι → (V .Z →ₗ[K] K)) (L : List (ι × V .Z)) :
    V .Z →ₗ[K] V .Z := substProjChain φ L

@[simp] theorem substProjZChain_nil (φ : ι → (V .Z →ₗ[K] K)) :
    substProjZChain φ ([] : List (ι × V .Z)) = LinearMap.id := rfl

@[simp] theorem substProjZChain_cons (φ : ι → (V .Z →ₗ[K] K)) (q : ι) (v : V .Z)
    (L : List (ι × V .Z)) :
    substProjZChain φ ((q, v) :: L) = substProjZChain φ L ∘ₗ substProjZ (φ q) v := rfl

/-- The tensor obtained by performing the substitutions of the chain `L` on the `Z` leg, in list
order. -/
def substituteZChain (φ : ι → (V .Z →ₗ[K] K)) :
    List (ι × V .Z) → Tensor3 K V → Tensor3 K V
  | [], T => T
  | (q, v) :: L, T => substituteZChain φ L (substituteZ (φ q) v T)

@[simp] theorem substituteZChain_nil (φ : ι → (V .Z →ₗ[K] K)) (T : Tensor3 K V) :
    substituteZChain φ [] T = T := rfl

@[simp] theorem substituteZChain_cons (φ : ι → (V .Z →ₗ[K] K)) (q : ι) (v : V .Z)
    (L : List (ι × V .Z)) (T : Tensor3 K V) :
    substituteZChain φ ((q, v) :: L) T = substituteZChain φ L (substituteZ (φ q) v T) := rfl

/-- A `Z`-retaining contraction of a `Z`-chained tensor is the composite chain projection applied
to the corresponding contraction of the source. -/
theorem contractZ_substituteZChain (φ : ι → (V .Z →ₗ[K] K)) (L : List (ι × V .Z))
    (fx : V .X →ₗ[K] K) (fy : V .Y →ₗ[K] K) (T : Tensor3 K V) :
    contractZ fx fy (substituteZChain φ L T) =
      substProjZChain φ L (contractZ fx fy T) := by
  induction L generalizing T with
  | nil => simp
  | cons qv L ih =>
      obtain ⟨q, v⟩ := qv
      rw [substituteZChain_cons, ih, contractZ_substituteZ, substProjZChain_cons,
        LinearMap.comp_apply]

/-- An `X`-retaining contraction of a `Z`-chained tensor is the contraction of the source against
the `Z`-covector precomposed with the composite chain projection. -/
theorem contractX_substituteZChain (φ : ι → (V .Z →ₗ[K] K)) (L : List (ι × V .Z))
    (fy : V .Y →ₗ[K] K) (fz : V .Z →ₗ[K] K) (T : Tensor3 K V) :
    contractX fy fz (substituteZChain φ L T) =
      contractX fy (fz ∘ₗ substProjZChain φ L) T := by
  induction L generalizing T with
  | nil => simp
  | cons qv L ih =>
      obtain ⟨q, v⟩ := qv
      rw [substituteZChain_cons, ih, contractX_substituteZ, substProjZChain_cons,
        LinearMap.comp_assoc]

/-- A `Y`-retaining contraction of a `Z`-chained tensor is the contraction of the source against
the `Z`-covector precomposed with the composite chain projection. -/
theorem contractY_substituteZChain (φ : ι → (V .Z →ₗ[K] K)) (L : List (ι × V .Z))
    (fx : V .X →ₗ[K] K) (fz : V .Z →ₗ[K] K) (T : Tensor3 K V) :
    contractY fx fz (substituteZChain φ L T) =
      contractY fx (fz ∘ₗ substProjZChain φ L) T := by
  induction L generalizing T with
  | nil => simp
  | cons qv L ih =>
      obtain ⟨q, v⟩ := qv
      rw [substituteZChain_cons, ih, contractY_substituteZ, substProjZChain_cons,
        LinearMap.comp_assoc]

/-- Protection lemma on the `Z` leg: the composite projection of a substitution chain fixes every
vector annihilated by all covectors of the chain. -/
theorem substProjZChain_apply_of_forall_ker (φ : ι → (V .Z →ₗ[K] K))
    {L : List (ι × V .Z)} {w : V .Z} (h : ∀ qv ∈ L, φ qv.1 w = 0) :
    substProjZChain φ L w = w := substProjChain_apply_of_forall_ker φ h

/-- A covector precomposed with a substitution chain agrees with the covector itself on every
vector annihilated by all covectors of the chain. -/
theorem comp_substProjZChain_apply (φ : ι → (V .Z →ₗ[K] K)) (fz : V .Z →ₗ[K] K)
    {L : List (ι × V .Z)} {w : V .Z} (h : ∀ qv ∈ L, φ qv.1 w = 0) :
    (fz ∘ₗ substProjZChain φ L) w = fz w := comp_substProjChain_apply φ fz h

/-- Multi-step substitution on the `Z` leg with a uniform detection certificate; see
`RankLE.exists_substituteXChain` for the statement pattern and proof sketch. -/
theorem RankLE.exists_substituteZChain [DecidableEq ι] (φ : ι → (V .Z →ₗ[K] K)) :
    ∀ {qs : List ι} {r : ℕ} {T : Tensor3 K V}, RankLE r T → qs.Nodup →
      (∀ q ∈ qs, ∃ (fx : V .X →ₗ[K] K) (fy : V .Y →ₗ[K] K),
          ∀ q' ∈ qs, φ q' (contractZ fx fy T) = if q' = q then 1 else 0) →
      ∃ L : List (ι × V .Z), L.map Prod.fst = qs ∧ (∀ qv ∈ L, φ qv.1 qv.2 = 1) ∧
        RankLE (r - qs.length) (substituteZChain φ L T) ∧ qs.length ≤ r := by
  intro qs
  induction qs with
  | nil =>
      intro r T hT _ _
      exact ⟨[], rfl, by simp, by simpa using hT, Nat.zero_le r⟩
  | cons q qs ih =>
      intro r T hT hnd hdet
      obtain ⟨fx, fy, hval⟩ := hdet q (List.mem_cons_self)
      have hq1 : φ q (contractZ fx fy T) = 1 := by
        simpa using hval q (List.mem_cons_self)
      have hslice : φ q (contractZ fx fy T) ≠ 0 := by
        rw [hq1]
        exact one_ne_zero
      obtain ⟨v, hv, hsub⟩ := hT.exists_substituteZ (φ q) hslice
      have hTne : T ≠ 0 := by
        rintro rfl
        simp at hslice
      have hr : 1 ≤ r := by
        rcases Nat.eq_zero_or_pos r with rfl | h
        · exact absurd hT.eq_zero hTne
        · exact h
      have hqnot : q ∉ qs := (List.nodup_cons.mp hnd).1
      have hdet' : ∀ q'' ∈ qs, ∃ (fx' : V .X →ₗ[K] K) (fy' : V .Y →ₗ[K] K),
          ∀ q' ∈ qs, φ q' (contractZ fx' fy' (substituteZ (φ q) v T)) =
            if q' = q'' then 1 else 0 := by
        intro q'' hq''
        obtain ⟨fx', fy', hval'⟩ := hdet q'' (List.mem_cons_of_mem _ hq'')
        have hqzero : φ q (contractZ fx' fy' T) = 0 := by
          have hne : q ≠ q'' := fun h ↦ hqnot (h ▸ hq'')
          simpa [hne] using hval' q (List.mem_cons_self)
        refine ⟨fx', fy', fun q' hq' ↦ ?_⟩
        rw [contractZ_substituteZ, substProjZ_apply, hqzero, zero_smul, sub_zero]
        exact hval' q' (List.mem_cons_of_mem _ hq')
      obtain ⟨L, hmap, hnorm, hrank, hlen⟩ :=
        ih hsub (List.nodup_cons.mp hnd).2 hdet'
      refine ⟨(q, v) :: L, by simp [hmap], ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hv
        · exact hnorm x hx
      · rw [substituteZChain_cons]
        have hsubs : r - 1 - qs.length = r - (q :: qs).length := by
          simp only [List.length_cons]
          omega
        rwa [hsubs] at hrank
      · simp only [List.length_cons]
        omega

/-- Packaged multi-step substitution lower bound on the `Z` leg; see
`rank_lower_of_substituteXChain`. -/
theorem rank_lower_of_substituteZChain [DecidableEq ι] (φ : ι → (V .Z →ₗ[K] K)) {qs : List ι}
    {T : Tensor3 K V} {s : ℕ} (hnd : qs.Nodup)
    (hdet : ∀ q ∈ qs, ∃ (fx : V .X →ₗ[K] K) (fy : V .Y →ₗ[K] K),
        ∀ q' ∈ qs, φ q' (contractZ fx fy T) = if q' = q then 1 else 0)
    (hfinal : ∀ L : List (ι × V .Z), L.map Prod.fst = qs → (∀ qv ∈ L, φ qv.1 qv.2 = 1) →
        s ≤ rank (substituteZChain φ L T)) :
    qs.length + s ≤ rank T := by
  obtain ⟨L, hmap, hnorm, hrank, hlen⟩ :=
    RankLE.exists_substituteZChain φ (rank_spec T) hnd hdet
  have h1 : s ≤ rank T - qs.length := (hfinal L hmap hnorm).trans (rank_le_iff.mpr hrank)
  omega

end CoordinateChain

end AlgebraicComplexity.Tensor
