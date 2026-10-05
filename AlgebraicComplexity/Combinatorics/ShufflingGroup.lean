/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.HoleRepair
import AlgebraicComplexity.Combinatorics.WordType
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm

/-!
# The shuffling group and its single union bound

Layer 2 (`AlgebraicComplexity/Combinatorics/`).  This module supplies the finite combinatorics of
the Hole Lemma of

> R. Duan, H. Wu and R. Zhou, *Faster Matrix Multiplication via Asymmetric Hashing*,
> arXiv:2210.10173v5, **§5 (`hole_lemma.tex`)** (`[DuanWuZhou2022]`).

`[DuanWuZhou2022]` define the *shuffling group* of a standard form tensor
`𝒯^* = ⊗_{t ∈ [m]} T_{i_t,j_t,k_t}^{⊗ n_t}[α̃_t]` as `G = Sym[n₁] × ⋯ × Sym[n_m]`, permuting the
positions inside each tensor factor.  Their three claims about it are:

1. availability of a small Z-block is `G`-invariant (`hole_lemma.tex` Claim 1);
2. the induced variable renaming is an automorphism of `𝒯^*` (Claim 2 — **asserted with no proof
   in the source**);
3. a uniformly random `φ ∈ G` sends a fixed available Z-block to a uniformly random available
   Z-block (Claim 3), whose proof is the constant orbit count `∏_t ∏_{k'} (α̃_t(k') · n_t)!`.

Claims 1 and 2 are tensor statements and are proved in
`MatrixMultiplication/RestrictedSplittingShuffle.lean`.  Claim 3 and the probabilistic method
built on it are pure finite combinatorics and are proved here.

## Design

The right abstraction for Claim 3 already exists: `HoleRepair.UniformOnParts G A`, the
division-free statement that a uniformly chosen family member sends a fixed part uniformly over
all parts.  This module adds

* `UniformOnParts.uniform_point` — the pointwise fiber identity, recovered from the subset form by
  taking a singleton target (so the structure needs only one field);
* `UniformOnParts.ofTargetIndependentFiber` — the constructor `[DuanWuZhou2022]` actually use: it
  suffices that, for each fixed source, the number of group elements hitting a given target does
  not depend on that target.  The paper's factorial formula is one way to see this; it is not
  needed, and computing it would be strictly more work than the argument requires;
* `UniformOnParts.prod` — the product family, which is how `∏_t Sym[n_t]` is assembled from the
  individual factors (a standard form tensor is an iterated external product, so the binary
  product iterates);
* `WordShuffle.uniformOnTypedWords` — the instance for `Sym[n]` acting on the words of one fixed
  multiplicity type, i.e. exactly the available small Z-blocks of one restricted-splitting power.
  Transitivity comes from `WordType.positionPermOfSameMultiplicity`.

The main theorem is `exists_shuffles_avoiding`, `[DuanWuZhou2022]`'s probabilistic method in exact
finite form: with hole sets `H_t` in the available alphabet `A`,

`|A| · ∏_t |H_t| < |A|^s  ⟹  ∃ φ : ι → G, ∀ a ∈ A, ∃ t, φ_t · a ∉ H_t`.

This is one union bound over one leg's alphabet — not the seven-branch three-leg recursion of
`Combinatorics/HoleRepair.exists_simultaneously_small_overlap`.  The paper's displayed hypothesis
`∑_t η_t ≥ Nℓ + 1` implies the displayed one through `∏_t (1 − η_t) ≤ e^{−∑ η_t}` together with
`|A| ≤ 2^{Nℓ}`; that estimate is real-analytic packaging of this finite statement and is left to
the client, which is where the actual `|A|` bound is known.
-/

namespace AlgebraicComplexity

open scoped BigOperators

universe u v w

namespace HoleRepair.UniformOnParts

variable {G : Type u} {A : Type v}
variable [Fintype G] [Fintype A] [DecidableEq G] [DecidableEq A]

/-- **Pointwise form of uniformity.**  The number of relabellings taking a fixed source part `a`
to a fixed target part `b`, multiplied by the number of parts, is the family size.  This is
`[DuanWuZhou2022]`'s Claim 3 in division-free form; it is recovered from the stored subset
statement by taking a singleton target. -/
theorem uniform_point (family : UniformOnParts G A) (a b : A) :
    Fintype.card A * (Finset.univ.filter fun g ↦ family.relabel g a = b).card =
      Fintype.card G := by
  classical
  have h := family.uniform_subset a {b}
  have hfilter : (Finset.univ.filter fun g ↦ family.relabel g a ∈ ({b} : Finset A)) =
      Finset.univ.filter fun g ↦ family.relabel g a = b := by
    apply Finset.filter_congr
    intro g _
    simp
  rw [hfilter, Finset.card_singleton, mul_one] at h
  exact h

/-- **The constructor used by the shuffling group.**  A family is uniform as soon as, for each
fixed source part, the number of relabellings reaching a target part is the same for every target
part.

Proof sketch: summing that fiber count over all targets counts every relabelling exactly once, so
the common value `k` satisfies `|A| · k = |G|`, which is the pointwise uniformity hypothesis of
`UniformOnParts.ofPointwise`.  No formula for `k` is needed — in `[DuanWuZhou2022]` it is
`∏_t ∏_{k'} (α̃_t(k') · n_t)!`. -/
noncomputable def ofTargetIndependentFiber
    (relabel : G → Equiv.Perm A)
    (hconstant : ∀ a b b' : A,
      (Finset.univ.filter fun g ↦ relabel g a = b).card =
        (Finset.univ.filter fun g ↦ relabel g a = b').card) :
    UniformOnParts G A := by
  classical
  refine UniformOnParts.ofPointwise relabel ?_
  intro a b
  have hsum : (Finset.univ : Finset G).card =
      ∑ b' : A, (Finset.univ.filter fun g ↦ relabel g a = b').card :=
    Finset.card_eq_sum_card_fiberwise fun g _ ↦ Finset.mem_univ (relabel g a)
  have hconst' : (∑ b' : A, (Finset.univ.filter fun g ↦ relabel g a = b').card) =
      ∑ _b' : A, (Finset.univ.filter fun g ↦ relabel g a = b).card :=
    Finset.sum_congr rfl fun b' _ ↦ hconstant a b' b
  rw [hconst', Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  rw [Finset.card_univ] at hsum
  exact hsum.symm

variable {H : Type u} {B : Type v}
variable [Fintype H] [Fintype B] [DecidableEq H] [DecidableEq B]

/-- **The product of two shuffling families is a shuffling family.**

`[DuanWuZhou2022]`'s shuffling group is `Sym[n₁] × ⋯ × Sym[n_m]` acting factorwise on the
positions of a standard form tensor.  A standard form tensor is an iterated external product, so
the `m`-fold group is obtained by iterating this binary construction. -/
noncomputable def prod (family : UniformOnParts G A) (other : UniformOnParts H B) :
    UniformOnParts (G × H) (A × B) := by
  classical
  refine ofTargetIndependentFiber
    (fun gh ↦ Equiv.prodCongr (family.relabel gh.1) (other.relabel gh.2)) ?_
  have hsplit : ∀ (a : A) (b : B) (a' : A) (b' : B),
      (Finset.univ.filter fun gh : G × H ↦
          Equiv.prodCongr (family.relabel gh.1) (other.relabel gh.2) (a, b) = (a', b')).card =
        (Finset.univ.filter fun g ↦ family.relabel g a = a').card *
          (Finset.univ.filter fun h ↦ other.relabel h b = b').card := by
    intro a b a' b'
    have hset :
        (Finset.univ.filter fun gh : G × H ↦
            Equiv.prodCongr (family.relabel gh.1) (other.relabel gh.2) (a, b) = (a', b')) =
          (Finset.univ.filter fun g ↦ family.relabel g a = a') ×ˢ
            (Finset.univ.filter fun h ↦ other.relabel h b = b') := by
      ext gh
      simp [Finset.mem_filter, Finset.mem_product, Prod.ext_iff]
    rw [hset, Finset.card_product]
  intro ab a'b' a''b''
  obtain ⟨a, b⟩ := ab
  obtain ⟨a', b'⟩ := a'b'
  obtain ⟨a'', b''⟩ := a''b''
  have hA := uniform_point family a
  have hB := uniform_point other b
  have hApos : 0 < Fintype.card A := Fintype.card_pos_iff.2 ⟨a⟩
  have hBpos : 0 < Fintype.card B := Fintype.card_pos_iff.2 ⟨b⟩
  have hfirst : (Finset.univ.filter fun g ↦ family.relabel g a = a').card =
      (Finset.univ.filter fun g ↦ family.relabel g a = a'').card := by
    have h1 := hA a'
    have h2 := hA a''
    exact Nat.eq_of_mul_eq_mul_left hApos (h1.trans h2.symm)
  have hsecond : (Finset.univ.filter fun h ↦ other.relabel h b = b').card =
      (Finset.univ.filter fun h ↦ other.relabel h b = b'').card := by
    have h1 := hB b'
    have h2 := hB b''
    exact Nat.eq_of_mul_eq_mul_left hBpos (h1.trans h2.symm)
  rw [hsplit a b a' b', hsplit a b a'' b'', hfirst, hsecond]

end HoleRepair.UniformOnParts

/-! ## The probabilistic method: one union bound -/

open HoleRepair

/-- **`[DuanWuZhou2022]`'s Hole Lemma union bound, in exact finite form.**

`A` is the set of available blocks, `holes t` the holes of the `t`-th broken copy, and `family` a
shuffling family acting uniformly on `A`.  If

`|A| · ∏_t |holes t| < |A| ^ (number of copies)`

then some choice of one group element per copy makes every available block survive in at least
one shuffled copy.

Proof sketch (the paper's probabilistic method, with expectations replaced by exact counts): the
set of bad tuples is contained in the union over `a ∈ A` of the product sets
`∏_t {g : g · a ∈ holes t}`, whose cardinality is `∏_t |{g : g · a ∈ holes t}|`.  Uniformity turns
each factor into `|G| · |holes t| / |A|`, so multiplying by `|A|^{|ι|}` clears every division and
the displayed hypothesis says exactly that the number of bad tuples is smaller than `|G|^{|ι|}`,
the number of tuples.  Hence a good tuple exists.  Note that the bound does **not** depend on how
the holes of different copies are related; only their sizes enter. -/
theorem exists_shuffles_avoiding
    {G : Type u} {A : Type v} {ι : Type w}
    [Fintype G] [DecidableEq G] [Nonempty G]
    [Fintype A] [DecidableEq A]
    [Fintype ι] [DecidableEq ι]
    (family : UniformOnParts G A) (holes : ι → Finset A)
    (hsmall : Fintype.card A * ∏ t, (holes t).card <
      Fintype.card A ^ Fintype.card ι) :
    ∃ shuffle : ι → G, ∀ a : A, ∃ t : ι, family.relabel (shuffle t) a ∉ holes t := by
  classical
  rcases Nat.eq_zero_or_pos (Fintype.card A) with hAzero | hApos
  · refine ⟨fun _ ↦ Classical.arbitrary G, fun a ↦ ?_⟩
    have : 0 < Fintype.card A := Fintype.card_pos_iff.2 ⟨a⟩
    omega
  set fiber : ι → A → Finset G :=
    fun t a ↦ Finset.univ.filter fun g ↦ family.relabel g a ∈ holes t with hfiberDef
  have hfiber : ∀ (t : ι) (a : A),
      Fintype.card A * (fiber t a).card = Fintype.card G * (holes t).card :=
    fun t a ↦ family.uniform_subset a (holes t)
  set bad : Finset (ι → G) :=
    Finset.univ.filter fun φ ↦ ∃ a : A, ∀ t, family.relabel (φ t) a ∈ holes t with hbadDef
  have hsub : bad ⊆ Finset.univ.biUnion fun a : A ↦ Fintype.piFinset fun t ↦ fiber t a := by
    intro φ hφ
    rw [hbadDef, Finset.mem_filter] at hφ
    obtain ⟨a, ha⟩ := hφ.2
    refine Finset.mem_biUnion.2 ⟨a, Finset.mem_univ a, ?_⟩
    refine Fintype.mem_piFinset.2 fun t ↦ ?_
    rw [hfiberDef]
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ha t⟩
  have hcard : bad.card ≤ ∑ a : A, ∏ t, (fiber t a).card := by
    refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
    exact Finset.sum_le_sum fun a _ ↦ le_of_eq (Fintype.card_piFinset _)
  have hprod : ∀ a : A,
      Fintype.card A ^ Fintype.card ι * ∏ t, (fiber t a).card =
        Fintype.card G ^ Fintype.card ι * ∏ t, (holes t).card := by
    intro a
    calc Fintype.card A ^ Fintype.card ι * ∏ t, (fiber t a).card
        = ∏ t : ι, Fintype.card A * (fiber t a).card := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      _ = ∏ t : ι, Fintype.card G * (holes t).card :=
          Finset.prod_congr rfl fun t _ ↦ hfiber t a
      _ = Fintype.card G ^ Fintype.card ι * ∏ t, (holes t).card := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have hsum : Fintype.card A ^ Fintype.card ι * ∑ a : A, ∏ t, (fiber t a).card =
      Fintype.card A * (Fintype.card G ^ Fintype.card ι * ∏ t, (holes t).card) := by
    rw [Finset.mul_sum, Finset.sum_congr rfl fun a _ ↦ hprod a, Finset.sum_const,
      Finset.card_univ, smul_eq_mul]
  have hGpow : 0 < Fintype.card G ^ Fintype.card ι := pow_pos Fintype.card_pos _
  have hstrict : Fintype.card A ^ Fintype.card ι * ∑ a : A, ∏ t, (fiber t a).card <
      Fintype.card A ^ Fintype.card ι * Fintype.card (ι → G) := by
    rw [hsum, Fintype.card_fun]
    calc Fintype.card A * (Fintype.card G ^ Fintype.card ι * ∏ t, (holes t).card)
        = (Fintype.card A * ∏ t, (holes t).card) * Fintype.card G ^ Fintype.card ι := by
          rw [mul_comm (Fintype.card G ^ Fintype.card ι) (∏ t, (holes t).card), ← mul_assoc]
      _ < Fintype.card A ^ Fintype.card ι * Fintype.card G ^ Fintype.card ι :=
          mul_lt_mul_of_pos_right hsmall hGpow
  have hlt : bad.card < Fintype.card (ι → G) :=
    lt_of_le_of_lt hcard (lt_of_mul_lt_mul_left hstrict (Nat.zero_le _))
  have hexists : ∃ φ : ι → G, φ ∉ bad := by
    by_contra hcon
    push Not at hcon
    have hsubset : (Finset.univ : Finset (ι → G)) ⊆ bad := fun φ _ ↦ hcon φ
    have hle := Finset.card_le_card hsubset
    rw [Finset.card_univ] at hle
    omega
  obtain ⟨φ, hφ⟩ := hexists
  refine ⟨φ, fun a ↦ ?_⟩
  by_contra hcon
  push Not at hcon
  exact hφ (by rw [hbadDef]; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨a, hcon⟩⟩)

/-! ## Position shuffling of words of a fixed type -/

namespace WordShuffle

open AlgebraicComplexity.WordType

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {m : ℕ}

/-- The permutations of positions carrying the word `v` to the word `w`. -/
def transporter (v w : Fin m → ι) : Finset (Equiv.Perm (Fin m)) :=
  Finset.univ.filter fun π ↦ v ∘ π = w

omit [Fintype ι] in
@[simp] theorem mem_transporter {v w : Fin m → ι} {π : Equiv.Perm (Fin m)} :
    π ∈ transporter v w ↔ v ∘ π = w := by
  simp [transporter]

omit [Fintype ι] in
/-- **The transporter of a fixed source word has a size independent of its target.**

Proof sketch: right translation by a chosen transporting permutation `ρ` is a bijection from the
stabilizer `transporter v v` onto `transporter v w`.  This is the only group-theoretic input the
Hole Lemma needs; the paper instead computes the common size as a product of factorials. -/
theorem card_transporter_eq_card_stabilizer (v w : Fin m → ι)
    (ρ : Equiv.Perm (Fin m)) (hρ : v ∘ ρ = w) :
    (transporter v w).card = (transporter v v).card := by
  refine Finset.card_nbij' (fun μ ↦ ρ.symm.trans μ) (fun π ↦ ρ.trans π) ?_ ?_ ?_ ?_
  · intro μ hμ
    rw [Finset.mem_coe, mem_transporter] at hμ
    rw [Finset.mem_coe, mem_transporter]
    funext i
    have h1 : v (μ (ρ.symm i)) = w (ρ.symm i) := congrFun hμ (ρ.symm i)
    have h2 : v (ρ (ρ.symm i)) = w (ρ.symm i) := congrFun hρ (ρ.symm i)
    rw [Equiv.apply_symm_apply] at h2
    simpa [Equiv.trans_apply] using h1.trans h2.symm
  · intro π hπ
    rw [Finset.mem_coe, mem_transporter] at hπ
    rw [Finset.mem_coe, mem_transporter]
    funext i
    have h1 : v (π (ρ i)) = v (ρ i) := congrFun hπ (ρ i)
    have h2 : v (ρ i) = w i := congrFun hρ i
    simpa [Equiv.trans_apply] using h1.trans h2
  · intro μ _
    apply Equiv.ext
    intro i
    simp [Equiv.trans_apply]
  · intro π _
    apply Equiv.ext
    intro i
    simp [Equiv.trans_apply]

/-- **The available blocks of one factor**: the words of length `m` over `ι` whose empirical type
is `τ`.  In `[DuanWuZhou2022]` these are the available small Z-blocks of a single restricted
splitting power `T^{⊗ m}[τ]`. -/
abbrev TypedWord (ι : Type u) [Fintype ι] (m : ℕ) (τ : ι → ℕ) :=
  {w : Fin m → ι // WordType.multiplicity w = τ}

/-- **The shuffling action on available blocks.**  A permutation of positions maps words of type
`τ` to words of type `τ`, because the empirical type of a word is invariant under reindexing
(`WordType.multiplicity_reindex`).  This is `[DuanWuZhou2022]`'s Claim 1 at the level of block
labels. -/
noncomputable def typedWordShuffle (τ : ι → ℕ) (σ : Equiv.Perm (Fin m)) :
    Equiv.Perm (TypedWord ι m τ) where
  toFun w := ⟨w.1 ∘ σ.symm, by rw [WordType.multiplicity_reindex]; exact w.2⟩
  invFun w := ⟨w.1 ∘ σ, by
    have h := WordType.multiplicity_reindex σ.symm w.1
    rw [Equiv.symm_symm] at h
    rw [h]
    exact w.2⟩
  left_inv := by
    intro w
    apply Subtype.ext
    funext i
    simp
  right_inv := by
    intro w
    apply Subtype.ext
    funext i
    simp

omit [DecidableEq ι] in
@[simp] theorem typedWordShuffle_val (τ : ι → ℕ) (σ : Equiv.Perm (Fin m))
    (w : TypedWord ι m τ) : (typedWordShuffle τ σ w).1 = w.1 ∘ σ.symm := rfl

/-- The number of shuffles carrying a fixed available block to a prescribed available block does
not depend on the prescribed block. -/
theorem card_typedWordShuffle_fiber (τ : ι → ℕ) (a b : TypedWord ι m τ) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin m) ↦ typedWordShuffle τ σ a = b).card =
      (transporter a.1 a.1).card := by
  classical
  have hstep : (Finset.univ.filter fun σ : Equiv.Perm (Fin m) ↦ typedWordShuffle τ σ a = b).card =
      (transporter a.1 b.1).card := by
    refine Finset.card_nbij' (fun σ ↦ σ.symm) (fun π ↦ π.symm) ?_ ?_ ?_ ?_
    · intro σ hσ
      rw [Finset.mem_coe, Finset.mem_filter] at hσ
      rw [Finset.mem_coe, mem_transporter]
      exact congrArg Subtype.val hσ.2
    · intro π hπ
      rw [Finset.mem_coe, mem_transporter] at hπ
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, Subtype.ext ?_⟩
      rw [typedWordShuffle_val, Equiv.symm_symm]
      exact hπ
    · intro σ _
      simp
    · intro π _
      simp
  rw [hstep]
  refine card_transporter_eq_card_stabilizer a.1 b.1
    (WordType.positionPermOfSameMultiplicity b.1 a.1 (by rw [a.2, b.2])) ?_
  exact WordType.positionPermOfSameMultiplicity_map b.1 a.1 (by rw [a.2, b.2])

/-- **`[DuanWuZhou2022]`'s Claim 3 for a single factor.**  The symmetric group of positions acts
uniformly on the available blocks of a restricted splitting power: a uniformly random position
permutation carries a fixed available block to a uniformly random available block. -/
noncomputable def uniformOnTypedWords (τ : ι → ℕ) (m : ℕ) :
    UniformOnParts (Equiv.Perm (Fin m)) (TypedWord ι m τ) := by
  classical
  refine HoleRepair.UniformOnParts.ofTargetIndependentFiber (typedWordShuffle τ) ?_
  intro a b b'
  rw [card_typedWordShuffle_fiber τ a b, card_typedWordShuffle_fiber τ a b']

@[simp] theorem uniformOnTypedWords_relabel (τ : ι → ℕ) (m : ℕ) (σ : Equiv.Perm (Fin m)) :
    (uniformOnTypedWords τ m).relabel σ = typedWordShuffle τ σ := rfl

end WordShuffle

end AlgebraicComplexity
