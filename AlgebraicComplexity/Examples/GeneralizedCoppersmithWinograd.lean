/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.GroupTensor
import AlgebraicComplexity.Tensor.IndependenceNumber
import AlgebraicComplexity.Examples.CoppersmithWinograd
import AlgebraicComplexity.Examples.CoppersmithWinogradSupport
import Mathlib.Algebra.Group.TypeTags.Finite

/-!
# Generalized Coppersmith--Winograd tensors and the group-tensor degeneration

This file formalizes two results of Alman and Vassilevska Williams, *Limits on all known (and some
unknown) approaches to matrix multiplication* (arXiv:1810.08671):

* **Definition 3.1**, the family `CW_q^σ` of *generalized Coppersmith--Winograd tensors*, obtained
  from the classical `CW_q` by replacing the constituent `T_{110} = ∑_i x_i y_i z_0` with
  `∑_i x_i y_{σ(i)} z_0` for an arbitrary permutation `σ`; and
* **Theorem 7.2**: for every finite group `G` there is a *monomial degeneration* of the group
  tensor `T_G` into a generalized Coppersmith--Winograd tensor of parameter `|G| - 2`.

Theorem 7.2 is the positive half of the AVW barrier program: it says that any implementation of the
Solar/Galactic/Universal method applied to a group tensor can do no better than the best known
analysis of `CW_{|G|-2}`.  It is also the cheapest genuine test of the constructive
monomial-degeneration API of `Tensor/Monomial.lean` on a published theorem, which is why it is
formalized here first.

## The generalized family

AVW display `CW_q^σ` on the index set `{0, 1, …, q, q+1}`:

`CW_q^σ = (x_0 y_0 z_{q+1} + x_0 y_{q+1} z_0 + x_{q+1} y_0 z_0)
            + ∑_{i=1}^q (x_i y_{σ(i)} z_0 + x_i y_0 z_i + x_0 y_i z_i).`

Here the middle block is indexed by an arbitrary type `μ` rather than by `Fin q`
(`GenCWIndex μ`, `genCW K μ σ`).  The extra generality is free and is exactly what makes the group
application painless: the group tensor's middle block is naturally indexed by `G \ {1, g}`, and
forcing it into `Fin (|G| - 2)` before the algebra is done would obscure the argument.  The
literal Definition 3.1 is the special case `μ = Fin q`, and `IsGeneralizedCW K q T` is stated with
that literal instance.

`genCW_isomorphic_coppersmithWinograd` checks the compatibility claim: the identity permutation
recovers the repository's classical `Examples.coppersmithWinograd`, legwise isomorphically.  The
two definitions align on the nose (same three corner terms, same three middle terms), so the bridge
is a relabelling of the index inductive with no reindexing of coefficients; the relabelling
equation itself is exposed as `congr_relabel_genCW_eq_coppersmithWinograd`, which is what transports
`standardCoordinateEquiv_genCW` to `CW_q`.  The legwise relabelling machinery it uses
(`Tensor.relabelLegEquiv`, `congr_relabelLegEquiv_pure`,
`standardCoordinateEquiv_congr_relabel`) is layer-1 and lives in `Tensor/Coordinates.lean`.

## Tiny regression clients

Two deliberately small instances close the file: `coppersmithWinograd_isGeneralizedCW` states the
compatibility bridge in the predicate form actually used by the main theorem, and
`twoElementGroup_monomialDegenerates_isGeneralizedCW` instantiates AVW Theorem 7.2 on the
two-element group, where the parameter is `|G| - 2 = 0` and the target is the bare three-term
corner tensor.  The only purpose of the extra `Mathlib.Algebra.Group.TypeTags.Finite` import is to
give that concrete group its `Fintype` instance.

## AVW's weights

The proof of Theorem 7.2 fixes any `g ≠ 1` in `G` and uses the integer weights

`α(x_1) = β(y_1) = γ(z_1) = 0`, `α(x_g) = β(y_g) = -γ(z_g) = 2`,
`α(x_h) = β(y_h) = -γ(z_h) = 1` for `h ∉ {1, g}`.

Since the repository's monomial certificates carry natural-number weights, the `Z` weight is
shifted by `+2` (`avwWeight`); the whole weight function is then `α` on `X` and `Y` and `2 - α` on
`Z`, and the minimum total weight is `2` instead of `0`.  Shifting one leg by a constant changes
nothing: it multiplies the whole polynomial curve by `ε^2`.

Rather than reproducing AVW's eleven displayed case checks, the argument here isolates the single
arithmetic fact behind them (`avwAlpha_add_eq_iff`): for the multiplicative support triple
`(a, b, ab)` the total weight `α(a) + α(b) + (2 - α(ab))` is always at least `2`, with equality
exactly when `α(a) + α(b) = α(ab)`, which happens exactly when `a = 1`, or `b = 1`, or
`a ∉ {1, g}` and `ab = g`.  Those three families are precisely AVW's surviving terms, so the
displayed leading tensor is

`T = x_1 y_1 z_1 + x_1 y_g z_g + x_g y_1 z_g
       + ∑_{h ∉ {1,g}} (x_1 y_h z_h + x_h y_1 z_h + x_h y_{σ(h)} z_g)`, `σ(h) = h⁻¹ g`,

which is `avwTarget`.  Relabelling `1 ↦ 0`, `g ↦ q+1` on the `X` and `Y` legs and `1 ↦ q+1`,
`g ↦ 0` on the `Z` leg turns it into a generalized CW tensor of parameter `|G| - 2`
(`avwTarget_isomorphic_genCW`).

## Convention and scope

The source tensor is `Tensor.groupTensorMul`, the *multiplicative* presentation
`T_G = ∑_{g,h} x_g y_h z_{gh}` of `Tensor/GroupTensor.lean`, because that is literally AVW's
Definition 3.2 and the one their weights are written against.  Monomial degeneration is a
basis-dependent notion, so the statement is genuinely about that coordinate presentation.  For the
repository's primary *symmetric* presentation `groupTensor` the corresponding statement is recorded
only in the weaker basis-free form
`groupTensor_polynomialDegeneratesAt_generalizedCW` (`PolynomialDegeneratesAt 2`), obtained by
composing with the exact relabelling `groupTensor_isomorphic_groupTensorMul`.  Promoting that to a
*monomial* degeneration would need a reusable "monomial certificates transport along coordinate
relabellings" lemma in `Tensor/Monomial.lean`; that lemma belongs to the tensor core and is
deliberately not added from this client file.

## Layer placement

This is a layer-4 regression/paper client under `AlgebraicComplexity/Examples/`.  It imports the
layer-1 group tensor (`Tensor/GroupTensor.lean`, which brings in `Tensor/Coordinates.lean`) and the
existing classical CW client (`Examples/CoppersmithWinograd.lean`, which brings in
`Tensor/Monomial.lean`) purely to state the compatibility bridge.  It also imports
`Examples/CoppersmithWinogradSupport.lean` for the three-letter block alphabet `CWBlock`, in which
the shared coarse labelling `gcwBlockLabel` below takes its values.  Nothing here is imported by a
lower layer.

## Non-goals

The border rank of `CW_q^σ` is *not* claimed.  AVW's Definition 3.1 is a family of candidate
tensors and their discussion is explicitly conditional ("if its border rank is `q + 2`, the
Coppersmith--Winograd approach would give exactly the same bound on `ω`"); the classical `q + 2`
certificate proved in `Examples/CoppersmithWinograd.lean` is for `σ = 1` only and its cancellation
curve does not obviously survive a general `σ`.  Likewise the asymptotic independence-number
statements of AVW Section 7 (Theorems 7.1, 7.3) need the `Ī`/`ω_g` framework, which the repository
does not yet have.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v w

/-! ## The generalized Coppersmith--Winograd family (AVW Definition 3.1) -/

/-- The coordinate index set of a generalized Coppersmith--Winograd tensor whose middle block is
indexed by `μ`.  In AVW's display `zero` is the coordinate `0`, `last` is the coordinate `q + 1`,
and `middle i` is the coordinate `i ∈ {1, …, q}`. -/
inductive GenCWIndex (μ : Type v)
  | zero
  | middle (i : μ)
  | last
  deriving DecidableEq

namespace GenCWIndex

/-- Presentation of `GenCWIndex μ` as a three-block sum type, used only to transport finiteness
and cardinality. -/
def equivSum (μ : Type v) : GenCWIndex μ ≃ Unit ⊕ μ ⊕ Unit where
  toFun
    | .zero => .inl ()
    | .middle i => .inr (.inl i)
    | .last => .inr (.inr ())
  invFun
    | .inl _ => .zero
    | .inr (.inl i) => .middle i
    | .inr (.inr _) => .last
  left_inv := by rintro (_ | i | _) <;> rfl
  right_inv := by rintro (⟨⟩ | (i | ⟨⟩)) <;> rfl

instance (μ : Type v) [Fintype μ] : Fintype (GenCWIndex μ) :=
  Fintype.ofEquiv (Unit ⊕ μ ⊕ Unit) (equivSum μ).symm

/-- A generalized CW tensor of parameter `q` has `q + 2` coordinates on each leg. -/
theorem card (μ : Type v) [Fintype μ] :
    Fintype.card (GenCWIndex μ) = Fintype.card μ + 2 := by
  rw [Fintype.card_congr (equivSum μ)]
  simp [Fintype.card_sum]
  omega

/-- Relabel the middle block along an equivalence, fixing the two distinguished coordinates. -/
def congr {μ : Type v} {ν : Type w} (ε : μ ≃ ν) : GenCWIndex μ ≃ GenCWIndex ν where
  toFun
    | .zero => .zero
    | .middle i => .middle (ε i)
    | .last => .last
  invFun
    | .zero => .zero
    | .middle j => .middle (ε.symm j)
    | .last => .last
  left_inv := by rintro (_ | i | _) <;> simp
  right_inv := by rintro (_ | j | _) <;> simp

@[simp] theorem congr_zero {μ : Type v} {ν : Type w} (ε : μ ≃ ν) :
    GenCWIndex.congr ε .zero = .zero := rfl

@[simp] theorem congr_last {μ : Type v} {ν : Type w} (ε : μ ≃ ν) :
    GenCWIndex.congr ε .last = .last := rfl

@[simp] theorem congr_middle {μ : Type v} {ν : Type w} (ε : μ ≃ ν) (i : μ) :
    GenCWIndex.congr ε (.middle i) = .middle (ε i) := rfl

/-- The transposition of the two distinguished coordinates fixes the middle block. -/
@[simp] theorem swap_middle {μ : Type v} [DecidableEq μ] (i : μ) :
    Equiv.swap (GenCWIndex.zero : GenCWIndex μ) .last (.middle i) = .middle i :=
  Equiv.swap_apply_of_ne_of_ne (by simp) (by simp)

end GenCWIndex

/-- All three legs of a generalized CW tensor carry the same coordinate index type. -/
abbrev GenCWIndexFamily (μ : Type v) : Leg → Type v := fun _ ↦ GenCWIndex μ

/-- The three coordinate spaces of a generalized CW tensor. -/
abbrev GenCWSpace (K : Type u) (μ : Type v) : Leg → Type (max u v) :=
  CoordinateSpace K (GenCWIndexFamily μ)

section Family

variable {K : Type u} [CommSemiring K] {μ : Type v} [DecidableEq μ]

/-- Standard coordinate vector of a generalized CW ambient space. -/
def gcwBasis (K : Type u) [CommSemiring K] {μ : Type v} [DecidableEq μ]
    (a : GenCWIndex μ) : GenCWIndex μ → K :=
  Pi.single a 1

/-- The three corner terms `x_0 y_0 z_{q+1} + x_0 y_{q+1} z_0 + x_{q+1} y_0 z_0` of AVW's
Definition 3.1.  They do not depend on the permutation. -/
noncomputable def genCWCorners (K : Type u) [CommSemiring K] (μ : Type v) [DecidableEq μ] :
    Tensor3 K (GenCWSpace K μ) :=
  pure (K := K) (ofLegs (gcwBasis K (.zero : GenCWIndex μ)) (gcwBasis K .zero)
    (gcwBasis K .last)) +
  pure (K := K) (ofLegs (gcwBasis K (.zero : GenCWIndex μ)) (gcwBasis K .last)
    (gcwBasis K .zero)) +
  pure (K := K) (ofLegs (gcwBasis K (.last : GenCWIndex μ)) (gcwBasis K .zero)
    (gcwBasis K .zero))

/-- The three middle terms `x_i y_{σ(i)} z_0 + x_i y_0 z_i + x_0 y_i z_i` of AVW's
Definition 3.1 at the middle index `i`. -/
noncomputable def genCWMiddle (K : Type u) [CommSemiring K] {μ : Type v} [DecidableEq μ]
    (σ : Equiv.Perm μ) (i : μ) : Tensor3 K (GenCWSpace K μ) :=
  pure (K := K) (ofLegs (gcwBasis K (.middle i)) (gcwBasis K (.middle (σ i)))
    (gcwBasis K (.zero : GenCWIndex μ))) +
  pure (K := K) (ofLegs (gcwBasis K (.middle i)) (gcwBasis K (.zero : GenCWIndex μ))
    (gcwBasis K (.middle i))) +
  pure (K := K) (ofLegs (gcwBasis K (.zero : GenCWIndex μ)) (gcwBasis K (.middle i))
    (gcwBasis K (.middle i)))

/-- The generalized Coppersmith--Winograd tensor `CW_q^σ` of AVW Definition 3.1, with middle block
indexed by `μ` (so parameter `q = |μ|`) and middle permutation `σ`. -/
noncomputable def genCW (K : Type u) [CommSemiring K] (μ : Type v) [Fintype μ] [DecidableEq μ]
    (σ : Equiv.Perm μ) : Tensor3 K (GenCWSpace K μ) :=
  genCWCorners K μ + ∑ i : μ, genCWMiddle K σ i

/-- The support of `CW_q^σ`: the `3|μ| + 3` coordinate triples carrying the coefficient `1`. -/
def GenCWSupport {μ : Type v} (σ : Equiv.Perm μ) (s : ∀ c, GenCWIndexFamily μ c) : Prop :=
  (s .X = .zero ∧ s .Y = .zero ∧ s .Z = .last) ∨
  (s .X = .zero ∧ s .Y = .last ∧ s .Z = .zero) ∨
  (s .X = .last ∧ s .Y = .zero ∧ s .Z = .zero) ∨
  (∃ i, s .X = .middle i ∧ s .Y = .middle (σ i) ∧ s .Z = .zero) ∨
  (∃ i, s .X = .middle i ∧ s .Y = .zero ∧ s .Z = .middle i) ∨
  (∃ i, s .X = .zero ∧ s .Y = .middle i ∧ s .Z = .middle i)

instance decidableGenCWSupport [Fintype μ] (σ : Equiv.Perm μ)
    (s : ∀ c, GenCWIndexFamily μ c) : Decidable (GenCWSupport σ s) := by
  unfold GenCWSupport
  infer_instance

/-- Coordinate support formula for a generalized CW tensor: the coefficient of a triple is `1` on
the `3|μ| + 3` displayed triples of AVW Definition 3.1 and `0` elsewhere.

Proof sketch: expand the defining sum through the coefficient equivalence.  Each summand
contributes a product of three Kronecker deltas.  Splitting on the three shapes of each of the
three coordinates leaves, in every case, either an empty family of matching deltas or a single
`Finset` sum of the form `∑ i, [j = i][k = i]`, which collapses.  The only case needing a manual
collapse is `(middle, middle, zero)`, where the surviving summand is pinned by the `X` coordinate
rather than by the `Y` coordinate. -/
theorem standardCoordinateEquiv_genCW [Fintype μ] (σ : Equiv.Perm μ)
    (s : ∀ c, GenCWIndexFamily μ c) :
    standardCoordinateEquiv (K := K) (κ := GenCWIndexFamily μ) (genCW K μ σ) s =
      if GenCWSupport σ s then 1 else 0 := by
  classical
  unfold genCW genCWCorners
  simp only [map_add, map_sum, Pi.add_apply, Finset.sum_apply,
    standardCoordinateEquiv_pure, prod_leg, ofLegs_X, ofLegs_Y, ofLegs_Z,
    gcwBasis, Pi.single_apply, genCWMiddle]
  rcases hx : s .X with _ | i₀ | _ <;> rcases hy : s .Y with _ | j₀ | _ <;>
    rcases hz : s .Z with _ | k₀ | _ <;>
    simp [GenCWSupport, hx, hy, hz, Finset.sum_ite_eq, eq_comm, mul_ite]
  rw [Finset.sum_eq_single i₀]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/-- `T` is a generalized Coppersmith--Winograd tensor of parameter `q` (AVW Definition 3.1): some
legwise change of coordinates identifies `T` with `CW_q^σ` on the literal index set of the
definition, for some permutation `σ` of the `q` middle coordinates. -/
def IsGeneralizedCW (K : Type u) [CommSemiring K] (q : ℕ) {V : Leg → Type w}
    [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)] (T : Tensor3 K V) : Prop :=
  ∃ σ : Equiv.Perm (Fin q), Isomorphic T (genCW K (Fin q) σ)

end Family

/-! ## The coefficient table of `CW_q^σ` -/

section Table

variable {K : Type u} [CommSemiring K] {μ : Type v} [Fintype μ] [DecidableEq μ]

/-- The generalized CW index set is nonempty; it always carries the distinguished coordinate `0`.
Needed for the concise form of AVW Corollary 4.3, whose statement assumes every leg has a
variable. -/
instance nonempty_genCWIndex : Nonempty (GenCWIndex μ) := ⟨GenCWIndex.zero⟩

/-- **The coefficient table of `CW_q^σ`** in the standard coordinates of AVW Definition 3.1: the
function assigning to each index triple its coefficient in `genCW K μ σ`.

The whole barrier argument is about this table rather than about the abstract tensor, because the
independence number `I` --- and hence `Ī` and `coordinateGalacticExponent` --- is
basis-dependent. -/
noncomputable def gcwTable (K : Type u) [CommSemiring K] (μ : Type v) [Fintype μ] [DecidableEq μ]
    (σ : Equiv.Perm μ) : (∀ c, GenCWIndexFamily μ c) → K :=
  standardCoordinateEquiv (K := K) (κ := GenCWIndexFamily μ) (genCW K μ σ)

/-- The coefficients of `CW_q^σ` are `1` on the `3q + 3` displayed triples of AVW Definition 3.1
and `0` elsewhere. -/
theorem gcwTable_apply (σ : Equiv.Perm μ) (s : ∀ c, GenCWIndexFamily μ c) :
    gcwTable K μ σ s = if GenCWSupport σ s then 1 else 0 :=
  standardCoordinateEquiv_genCW (K := K) σ s

/-- The table `gcwTable` really presents `genCW`: its coordinate tensor is `CW_q^σ` itself. -/
theorem coordinateTensor_gcwTable (σ : Equiv.Perm μ) :
    coordinateTensor (gcwTable K μ σ) = genCW K μ σ := by
  unfold coordinateTensor gcwTable
  exact (standardCoordinateEquiv (K := K) (κ := GenCWIndexFamily μ)).symm_apply_apply _

/-- The support of the table is AVW's displayed support. -/
theorem gcwTable_ne_zero_iff [Nontrivial K] (σ : Equiv.Perm μ)
    (s : ∀ c, GenCWIndexFamily μ c) : gcwTable K μ σ s ≠ 0 ↔ GenCWSupport σ s := by
  rw [gcwTable_apply]
  by_cases h : GenCWSupport σ s <;> simp [h]

end Table

/-! ### The coarse block labelling -/

section BlockLabel

variable {μ : Type v}

/-- The coarse **block label** of a generalized Coppersmith--Winograd coordinate: the three
coordinate blocks `0`, `{1, …, q}` and `q + 1` of [AlmanVassilevskaWilliams2018, Definition 3.1],
named as in the classical partition of [CoppersmithWinograd1990].  This is the block labelling of
the classical CW partition in the sense of `Tensor/CoordinateBlockWord.lean`, shared by every
client that needs it. -/
def gcwBlockLabel (μ : Type v) : GenCWIndex μ → CWBlock
  | .zero => .zero
  | .middle _ => .middle
  | .last => .last

@[simp] theorem gcwBlockLabel_zero : gcwBlockLabel μ .zero = CWBlock.zero := rfl

@[simp] theorem gcwBlockLabel_middle (i : μ) :
    gcwBlockLabel μ (.middle i) = CWBlock.middle := rfl

@[simp] theorem gcwBlockLabel_last : gcwBlockLabel μ .last = CWBlock.last := rfl

end BlockLabel

/-! ### Relabelling the middle block -/

section Relabelling

variable {K : Type u} [CommSemiring K]
variable {μ : Type v} [Fintype μ] [DecidableEq μ]
variable {ν : Type w} [Fintype ν] [DecidableEq ν]

/-- Relabelling the middle block of a generalized CW tensor along `ε : μ ≃ ν` gives the
generalized CW tensor with the conjugated permutation.  In particular the parameter, `|μ| = |ν|`,
is the only invariant of the middle index type.

Proof sketch: the legwise relabelling `GenCWIndex.congr ε` fixes the two distinguished coordinates,
so it matches the three corner terms on the nose; on middle terms it sends the term at `i` to the
term at `ε i`, using `(ε.permCongr σ) (ε i) = ε (σ i)`, and reindexing the middle sum along the
bijection `ε` matches the two families. -/
theorem genCW_isomorphic_congr (ε : μ ≃ ν) (σ : Equiv.Perm μ) :
    Isomorphic (genCW K μ σ) (genCW K ν (Equiv.permCongr ε σ)) := by
  classical
  refine ⟨relabelLegEquiv K (fun _ : Leg ↦ GenCWIndex.congr ε), ?_⟩
  have hmid : ∀ i : μ,
      PiTensorProduct.congr (relabelLegEquiv K (fun _ : Leg ↦ GenCWIndex.congr ε))
          (genCWMiddle K σ i) =
        genCWMiddle K (Equiv.permCongr ε σ) (ε i) := by
    intro i
    rw [genCWMiddle, map_add, map_add]
    simp only [gcwBasis, congr_relabelLegEquiv_pure, GenCWIndex.congr_zero,
      GenCWIndex.congr_middle, genCWMiddle, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rw [genCW, map_add, map_sum]
  rw [Finset.sum_congr rfl (fun i _ ↦ hmid i),
    Equiv.sum_comp ε (fun j : ν ↦ genCWMiddle K (Equiv.permCongr ε σ) j)]
  rw [genCW, genCWCorners, genCWCorners, map_add, map_add]
  simp only [gcwBasis, congr_relabelLegEquiv_pure, GenCWIndex.congr_zero, GenCWIndex.congr_last]

end Relabelling

/-! ### The classical Coppersmith--Winograd tensor is an instance -/

section Classical

variable {K : Type u} [CommSemiring K]

/-- Identification of the abstract generalized CW index set on `Fin q` with the repository's
`Examples.CWIndex q`. -/
def genCWIndexEquivCWIndex (q : ℕ) : GenCWIndex (Fin q) ≃ CWIndex q where
  toFun
    | .zero => .zero
    | .middle i => .middle i
    | .last => .last
  invFun
    | .zero => .zero
    | .middle i => .middle i
    | .last => .last
  left_inv := by rintro (_ | i | _) <;> rfl
  right_inv := by rintro (_ | i | _) <;> rfl

@[simp] theorem genCWIndexEquivCWIndex_zero (q : ℕ) :
    genCWIndexEquivCWIndex q .zero = .zero := rfl

@[simp] theorem genCWIndexEquivCWIndex_last (q : ℕ) :
    genCWIndexEquivCWIndex q .last = .last := rfl

@[simp] theorem genCWIndexEquivCWIndex_middle (q : ℕ) (i : Fin q) :
    genCWIndexEquivCWIndex q (.middle i) = .middle i := rfl

/-- **The witness equation** behind `genCW_isomorphic_coppersmithWinograd`: relabelling the index
inductive along `genCWIndexEquivCWIndex q` carries `CW_q^{id}` to the repository's classical
`coppersmithWinograd K q` on the nose.

Stated separately from the isomorphism because clients need the equation itself: it transports the
coefficient formula `standardCoordinateEquiv_genCW` to `CW_q` through
`standardCoordinateEquiv_congr_relabel`.

Proof sketch: the two definitions display the same six families of pure basis terms, so the
relabelling of the index inductive matches them one by one; only the order of the summands inside
each block differs, which `abel` absorbs. -/
theorem congr_relabel_genCW_eq_coppersmithWinograd (K : Type u) [CommSemiring K] (q : ℕ) :
    PiTensorProduct.congr (relabelLegEquiv K (fun _ : Leg ↦ genCWIndexEquivCWIndex q))
        (genCW K (Fin q) (Equiv.refl (Fin q))) = coppersmithWinograd K q := by
  classical
  have hmid : ∀ i : Fin q,
      PiTensorProduct.congr (relabelLegEquiv K (fun _ : Leg ↦ genCWIndexEquivCWIndex q))
          (genCWMiddle K (Equiv.refl (Fin q)) i) = cwMiddle K q i := by
    intro i
    rw [genCWMiddle, map_add, map_add, cwMiddle_eq_pure]
    simp only [gcwBasis, congr_relabelLegEquiv_pure, cwBasis, Equiv.refl_apply,
      genCWIndexEquivCWIndex_zero, genCWIndexEquivCWIndex_middle]
    abel
  have hcorner : PiTensorProduct.congr
      (relabelLegEquiv K (fun _ : Leg ↦ genCWIndexEquivCWIndex q))
      (genCWCorners K (Fin q)) = cwCorners K q := by
    rw [genCWCorners, map_add, map_add, cwCorners_eq_pure]
    simp only [gcwBasis, congr_relabelLegEquiv_pure, cwBasis,
      genCWIndexEquivCWIndex_zero, genCWIndexEquivCWIndex_last]
    abel
  rw [genCW, map_add, map_sum, hcorner, Finset.sum_congr rfl (fun i _ ↦ hmid i),
    coppersmithWinograd]
  abel

/-- The classical Coppersmith--Winograd tensor is the member of the generalized family with the
identity permutation: `CW_q = CW_q^{id}`, legwise isomorphically. -/
theorem genCW_isomorphic_coppersmithWinograd (K : Type u) [CommSemiring K] (q : ℕ) :
    Isomorphic (genCW K (Fin q) (Equiv.refl (Fin q))) (coppersmithWinograd K q) :=
  ⟨_, congr_relabel_genCW_eq_coppersmithWinograd K q⟩

end Classical

/-! ## AVW's monomial weights on a finite group -/

section Weights

variable {G : Type v} [Group G] [DecidableEq G]

/-- AVW's weight `α` on the `X` and `Y` legs: `0` at the identity, `2` at the distinguished element
`g`, and `1` elsewhere.  The `Z` weight of AVW is `-α`; see `avwWeight` for the shift to `ℕ`. -/
def avwAlpha (g : G) (h : G) : ℕ := if h = 1 then 0 else if h = g then 2 else 1

@[simp] theorem avwAlpha_one (g : G) : avwAlpha g 1 = 0 := by simp [avwAlpha]

/-- The distinguished element has weight `2`. -/
theorem avwAlpha_self {g : G} (hg : g ≠ 1) : avwAlpha g g = 2 := by simp [avwAlpha, hg]

/-- Every other element has weight `1`. -/
theorem avwAlpha_of_ne {g h : G} (h1 : h ≠ 1) (hg : h ≠ g) : avwAlpha g h = 1 := by
  simp [avwAlpha, h1, hg]

theorem avwAlpha_le_two (g h : G) : avwAlpha g h ≤ 2 := by
  unfold avwAlpha
  split <;> [omega; split] <;> omega

theorem one_le_avwAlpha {g h : G} (h1 : h ≠ 1) : 1 ≤ avwAlpha g h := by
  unfold avwAlpha
  simp only [h1, if_false]
  split <;> omega

theorem avwAlpha_eq_two_iff {g : G} (hg : g ≠ 1) (h : G) : avwAlpha g h = 2 ↔ h = g := by
  constructor
  · intro hh
    by_contra hne
    by_cases h1 : h = 1
    · rw [h1] at hh; simp at hh
    · rw [avwAlpha_of_ne h1 hne] at hh; omega
  · rintro rfl
    exact avwAlpha_self hg

theorem avwAlpha_eq_one_iff {g : G} (hg : g ≠ 1) (h : G) :
    avwAlpha g h = 1 ↔ (h ≠ 1 ∧ h ≠ g) := by
  constructor
  · intro hh
    refine ⟨?_, ?_⟩
    · rintro rfl; simp at hh
    · rintro rfl; rw [avwAlpha_self hg] at hh; omega
  · rintro ⟨h1, hg'⟩
    exact avwAlpha_of_ne h1 hg'

/-- Subadditivity of the weight: `α(ab) ≤ α(a) + α(b)`.  This is the inequality behind the
"no term has total weight below the minimum" half of AVW's case analysis. -/
theorem avwAlpha_mul_le (g a b : G) : avwAlpha g (a * b) ≤ avwAlpha g a + avwAlpha g b := by
  by_cases ha : a = 1
  · subst ha; simp
  by_cases hb : b = 1
  · subst hb; simp
  have h1 := one_le_avwAlpha (g := g) ha
  have h2 := one_le_avwAlpha (g := g) hb
  have h3 := avwAlpha_le_two g (a * b)
  omega

/-- The equality case of subadditivity, which is exactly AVW's list of surviving terms: the weight
of a support triple `(a, b, ab)` of `T_G` is minimal precisely when `a = 1`, or `b = 1`, or
`a ∉ {1, g}` and `ab = g`.

Proof sketch: if neither `a` nor `b` is the identity then both weights are at least `1` while
`α(ab) ≤ 2`, so equality forces `α(a) = α(b) = 1` and `α(ab) = 2`; the first gives `a ∉ {1, g}` and
the last gives `ab = g`.  Conversely the three listed families are checked directly, using that
`b = a⁻¹g` lies outside `{1, g}` when `a` does. -/
theorem avwAlpha_add_eq_iff {g : G} (hg : g ≠ 1) (a b : G) :
    avwAlpha g a + avwAlpha g b = avwAlpha g (a * b) ↔
      (a = 1 ∨ b = 1 ∨ (a ≠ 1 ∧ a ≠ g ∧ a * b = g)) := by
  constructor
  · intro h
    by_cases ha : a = 1
    · exact Or.inl ha
    by_cases hb : b = 1
    · exact Or.inr (Or.inl hb)
    refine Or.inr (Or.inr ⟨ha, ?_, ?_⟩)
    · have h1 := one_le_avwAlpha (g := g) ha
      have h2 := one_le_avwAlpha (g := g) hb
      have h3 := avwAlpha_le_two g (a * b)
      have haa : avwAlpha g a = 1 := by omega
      exact ((avwAlpha_eq_one_iff hg a).mp haa).2
    · have h1 := one_le_avwAlpha (g := g) ha
      have h2 := one_le_avwAlpha (g := g) hb
      have h3 := avwAlpha_le_two g (a * b)
      have : avwAlpha g (a * b) = 2 := by omega
      exact (avwAlpha_eq_two_iff hg (a * b)).mp this
  · rintro (rfl | rfl | ⟨ha, hag, hab⟩)
    · simp
    · simp
    · have hb1 : b ≠ 1 := by
        rintro rfl
        exact hag (by simpa using hab)
      have hbg : b ≠ g := by
        rintro rfl
        exact ha (by simpa using hab)
      rw [hab, avwAlpha_self hg, avwAlpha_of_ne ha hag, avwAlpha_of_ne hb1 hbg]

end Weights

/-! ## The monomial degeneration of the group tensor (AVW Theorem 7.2) -/

section Degeneration

variable {K : Type u} [CommSemiring K] {G : Type v} [Group G] [Fintype G] [DecidableEq G]

/-- AVW's monomial weight family, shifted so that all three weights are natural numbers: `α` on the
`X` and `Y` legs and `2 - α` on the `Z` leg. -/
def avwWeight (g : G) : ∀ c, GroupIndex G c → ℕ
  | .X => avwAlpha g
  | .Y => avwAlpha g
  | .Z => fun h ↦ 2 - avwAlpha g h

/-- The coordinate triple of the defining term `x_a y_b z_{ab}` of `T_G`. -/
def avwTriple (q : G × G) : ∀ c, GroupIndex G c :=
  ofLegs (V := GroupIndex G) q.1 q.2 (q.1 * q.2)

omit [Fintype G] in
theorem monomialTotalWeight_avwTriple (g : G) (a b : G) :
    monomialTotalWeight (avwWeight g) (avwTriple (a, b)) =
      avwAlpha g a + avwAlpha g b + (2 - avwAlpha g (a * b)) := rfl

omit [Fintype G] in
/-- Every defining term of `T_G` has total weight at least `2`, so `2` is a legitimate leading
degree for the monomial certificate. -/
theorem two_le_monomialTotalWeight_avwTriple (g : G) (q : G × G) :
    2 ≤ monomialTotalWeight (avwWeight g) (avwTriple q) := by
  obtain ⟨a, b⟩ := q
  rw [monomialTotalWeight_avwTriple]
  have h1 := avwAlpha_mul_le g a b
  have h2 := avwAlpha_le_two g (a * b)
  omega

omit [Fintype G] in
/-- The terms of `T_G` of minimal total weight are exactly AVW's surviving terms. -/
theorem monomialTotalWeight_avwTriple_eq_two_iff {g : G} (hg : g ≠ 1) (a b : G) :
    monomialTotalWeight (avwWeight g) (avwTriple (a, b)) = 2 ↔
      (a = 1 ∨ b = 1 ∨ (a ≠ 1 ∧ a ≠ g ∧ a * b = g)) := by
  rw [monomialTotalWeight_avwTriple, ← avwAlpha_add_eq_iff hg]
  have h1 := avwAlpha_mul_le g a b
  have h2 := avwAlpha_le_two g (a * b)
  omega

omit [Fintype G] in
theorem pure_avwTriple (a b : G) :
    pure (K := K) (fun c ↦ Pi.single (avwTriple (a, b) c) 1) =
      pure (K := K) (groupTermMul K a b) := by
  congr 1
  funext c
  cases c <;> rfl

omit [Fintype G] in
/-- The defining term of `T_G` written in the `ofLegs` basis form used by the relabelling API. -/
theorem pure_groupTermMul_ofLegs (a b : G) :
    pure (K := K) (groupTermMul K a b) =
      pure (K := K) (ofLegs (V := CoordinateSpace K (GroupIndex G))
        (Pi.single a 1) (Pi.single b 1) (Pi.single (a * b) 1)) := by
  congr 1

/-- The group tensor written in the explicit coordinate form consumed by the monomial API. -/
theorem groupTensorMul_eq_basis_sum :
    groupTensorMul K G =
      ∑ q : G × G, (1 : K) • pure (K := K) (fun c ↦ Pi.single (avwTriple q c) 1) := by
  unfold groupTensorMul
  refine Finset.sum_congr rfl ?_
  rintro ⟨a, b⟩ _
  rw [one_smul, pure_avwTriple]

end Degeneration

/-- The middle index set `G \ {1, g}` of the resulting generalized CW tensor. -/
abbrev AVWMid {G : Type v} [Group G] (g : G) : Type v := {h : G // h ≠ 1 ∧ h ≠ g}

/-- AVW's permutation `σ(h) = h⁻¹ g` of `G \ {1, g}`, with inverse `k ↦ g k⁻¹`.  It is a bijection
because `h ↦ h⁻¹g` is a bijection of `G` sending `g ↦ 1` and `1 ↦ g`. -/
def avwPerm {G : Type v} [Group G] (g : G) : Equiv.Perm (AVWMid g) where
  toFun h := ⟨h.1⁻¹ * g, by
    refine ⟨fun hc ↦ h.2.2 ?_, fun hc ↦ h.2.1 ?_⟩
    · exact inv_mul_eq_one.mp hc
    · have : h.1⁻¹ = 1 := by
        have := mul_right_cancel (b := g) (by simpa using hc)
        simpa using this
      simpa using this⟩
  invFun k := ⟨g * k.1⁻¹, by
    refine ⟨fun hc ↦ k.2.2 ?_, fun hc ↦ k.2.1 ?_⟩
    · have := mul_inv_eq_one.mp hc
      exact this.symm
    · have : k.1⁻¹ = 1 := by
        have := mul_left_cancel (a := g) (by simpa using hc)
        simpa using this
      simpa using this⟩
  left_inv h := by
    apply Subtype.ext
    simp [mul_inv_rev, ← mul_assoc]
  right_inv k := by
    apply Subtype.ext
    simp [mul_inv_rev, mul_assoc]

@[simp] theorem avwPerm_coe {G : Type v} [Group G] (g : G) (h : AVWMid g) :
    (avwPerm g h : G) = h.1⁻¹ * g := rfl

section Target

variable {K : Type u} [CommSemiring K] {G : Type v} [Group G] [Fintype G] [DecidableEq G]

/-- Split a sum over `G` into the identity, the distinguished element `g`, and the rest. -/
theorem sum_split_avwMid {M : Type*} [AddCommMonoid M] {g : G} (hg : g ≠ 1) (f : G → M) :
    ∑ a : G, f a = f 1 + f g + ∑ h : AVWMid g, f h.1 := by
  have hmem : ∀ x : G, x ∈ ({1, g} : Finset G)ᶜ ↔ (x ≠ 1 ∧ x ≠ g) := by
    intro x
    simp
  rw [← Finset.sum_add_sum_compl ({1, g} : Finset G) f, Finset.sum_pair (Ne.symm hg),
    Finset.sum_subtype _ hmem f]

/-- The leading term of AVW's monomial degeneration of `T_G`, displayed exactly as in their proof:

`x_1 y_1 z_1 + x_1 y_g z_g + x_g y_1 z_g + ∑_{h ∉ {1,g}} (x_1 y_h z_h + x_h y_1 z_h + x_h y_{h⁻¹g} z_g)`.
-/
noncomputable def avwTarget (K : Type u) [CommSemiring K] {G : Type v} [Group G] [Fintype G]
    [DecidableEq G] (g : G) : Tensor3 K (GroupSpace K G) :=
  (pure (K := K) (groupTermMul K (1 : G) 1) +
      pure (K := K) (groupTermMul K (1 : G) g) +
      pure (K := K) (groupTermMul K g (1 : G))) +
    ∑ h : AVWMid g,
      (pure (K := K) (groupTermMul K (1 : G) h.1) +
        pure (K := K) (groupTermMul K h.1 (1 : G)) +
        pure (K := K) (groupTermMul K h.1 (h.1⁻¹ * g)))

/-- Identification of the minimum-weight part of `T_G` with AVW's displayed tensor.

Proof sketch: the minimum-weight condition on the pair `(a, b)` is `avwAlpha_add_eq_iff`.  Summing
over `a` first and splitting `G` into `1`, `g`, and the rest: for `a = 1` every `b` survives, for
`a = g` only `b = 1` survives, and for `a ∉ {1, g}` exactly `b ∈ {1, a⁻¹g}` survive.  Collecting
the three families and splitting `G` once more in the `a = 1` row gives the display. -/
theorem avwTarget_eq_conditional_sum {g : G} (hg : g ≠ 1) :
    (∑ q : G × G, if monomialTotalWeight (avwWeight g) (avwTriple q) = 2 then
      (fun _ : G × G ↦ (1 : K)) q • pure (K := K) (fun c ↦ Pi.single (avwTriple q c) 1)
      else 0) = avwTarget K g := by
  classical
  have hstep : (∑ q : G × G, if monomialTotalWeight (avwWeight g) (avwTriple q) = 2 then
      (fun _ : G × G ↦ (1 : K)) q • pure (K := K) (fun c ↦ Pi.single (avwTriple q c) 1)
      else 0) =
      ∑ a : G, ∑ b : G, (if monomialTotalWeight (avwWeight g) (avwTriple (a, b)) = 2 then
        pure (K := K) (groupTermMul K a b) else 0) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
    by_cases hw : monomialTotalWeight (avwWeight g) (avwTriple (a, b)) = 2
    · rw [if_pos hw, if_pos hw]
      simp [pure_avwTriple]
    · rw [if_neg hw, if_neg hw]
  rw [hstep, sum_split_avwMid hg]
  have hF1 : (∑ b : G, if monomialTotalWeight (avwWeight g) (avwTriple ((1 : G), b)) = 2 then
      pure (K := K) (groupTermMul K (1 : G) b) else 0) =
      pure (K := K) (groupTermMul K (1 : G) 1) + pure (K := K) (groupTermMul K (1 : G) g) +
        ∑ h : AVWMid g, pure (K := K) (groupTermMul K (1 : G) h.1) := by
    have hall : ∀ b : G, monomialTotalWeight (avwWeight g) (avwTriple ((1 : G), b)) = 2 :=
      fun b ↦ (monomialTotalWeight_avwTriple_eq_two_iff hg 1 b).mpr (Or.inl rfl)
    rw [Finset.sum_congr rfl (fun b _ ↦ if_pos (hall b))]
    exact sum_split_avwMid hg (fun b ↦ pure (K := K) (groupTermMul K (1 : G) b))
  have hFg : (∑ b : G, if monomialTotalWeight (avwWeight g) (avwTriple (g, b)) = 2 then
      pure (K := K) (groupTermMul K g b) else 0) =
      pure (K := K) (groupTermMul K g (1 : G)) := by
    have hiff : ∀ b : G,
        (monomialTotalWeight (avwWeight g) (avwTriple (g, b)) = 2) ↔ b = 1 := by
      intro b
      rw [monomialTotalWeight_avwTriple_eq_two_iff hg]
      constructor
      · rintro (h | h | ⟨-, h, -⟩)
        · exact absurd h hg
        · exact h
        · exact absurd rfl h
      · rintro rfl
        exact Or.inr (Or.inl rfl)
    rw [Finset.sum_congr rfl (fun b _ ↦ if_congr (hiff b) rfl rfl)]
    simp
  have hFh : ∀ h : AVWMid g,
      (∑ b : G, if monomialTotalWeight (avwWeight g) (avwTriple (h.1, b)) = 2 then
        pure (K := K) (groupTermMul K h.1 b) else 0) =
      pure (K := K) (groupTermMul K h.1 (1 : G)) +
        pure (K := K) (groupTermMul K h.1 (h.1⁻¹ * g)) := by
    rintro ⟨x, hx1, hxg⟩
    have hiff : ∀ b : G, (monomialTotalWeight (avwWeight g) (avwTriple (x, b)) = 2) ↔
        b ∈ ({1, x⁻¹ * g} : Finset G) := by
      intro b
      rw [monomialTotalWeight_avwTriple_eq_two_iff hg]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (h | h | ⟨-, -, h⟩)
        · exact absurd h hx1
        · exact Or.inl h
        · right
          rw [← h]
          simp
      · rintro (rfl | rfl)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr ⟨hx1, hxg, by simp⟩)
    have hne : (1 : G) ≠ x⁻¹ * g := fun hc ↦ hxg (inv_mul_eq_one.mp hc.symm)
    rw [Finset.sum_congr rfl (fun b _ ↦ if_congr (hiff b) rfl rfl), Finset.sum_ite_mem,
      Finset.univ_inter, Finset.sum_pair hne]
  rw [hF1, hFg, Finset.sum_congr rfl (fun h _ ↦ hFh h)]
  simp only [avwTarget, Finset.sum_add_distrib]
  abel

/-- The monomial certificate of AVW Theorem 7.2 in its raw form: applying AVW's diagonal weights to
`T_G` gives a polynomial curve whose lowest-order coefficient is exactly `avwTarget`. -/
theorem avw_hasLeadingTerm {g : G} (hg : g ≠ 1) :
    HasLeadingTerm (monomialTransform (K := K) (avwWeight g) (groupTensorMul K G)) 2
      (avwTarget K g) := by
  classical
  rw [groupTensorMul_eq_basis_sum, ← avwTarget_eq_conditional_sum (K := K) hg]
  exact monomialTransform_fintype_sum_basis_leading (K := K) (κ := GroupIndex G)
    (avwWeight g) (fun _ : G × G ↦ (1 : K)) avwTriple 2
    (fun q ↦ two_le_monomialTotalWeight_avwTriple g q)

/-- **AVW Theorem 7.2, degeneration half.**  For every finite group `G` and every `g ≠ 1`, the
group tensor `T_G` monomially degenerates to `avwTarget K g`. -/
theorem groupTensorMul_monomialDegenerates_avwTarget {g : G} (hg : g ≠ 1) :
    MonomialDegenerates (groupTensorMul K G) (avwTarget K g) :=
  ⟨avwWeight g, 2, avw_hasLeadingTerm hg⟩

/-- The same certificate read as a degree-aware polynomial degeneration of leading degree `2`. -/
theorem groupTensorMul_polynomialDegeneratesAt_avwTarget {g : G} (hg : g ≠ 1) :
    PolynomialDegeneratesAt 2 (groupTensorMul K G) (avwTarget K g) :=
  ⟨fun c ↦ Monomial.weightFamily (K := K) (avwWeight g c), avw_hasLeadingTerm hg⟩

end Target

/-! ### The leading term is a generalized CW tensor -/

section Identification

variable {K : Type u} [CommSemiring K] {G : Type v} [Group G] [Fintype G] [DecidableEq G]

/-- AVW's relabelling of the group elements as generalized CW coordinates: the identity becomes the
distinguished coordinate `0`, the chosen element `g` becomes `q + 1`, and everything else becomes a
middle coordinate. -/
def avwIndexEquiv {g : G} (hg : g ≠ 1) : G ≃ GenCWIndex (AVWMid g) where
  toFun h := if h1 : h = 1 then .zero else if h2 : h = g then .last else .middle ⟨h, h1, h2⟩
  invFun
    | .zero => 1
    | .middle i => i.1
    | .last => g
  left_inv h := by
    by_cases h1 : h = 1
    · simp [h1]
    · by_cases h2 : h = g
      · simp [h2, hg]
      · simp [h1, h2]
  right_inv s := by
    rcases s with _ | i | _
    · simp
    · have h1 : (i.1 : G) ≠ 1 := i.2.1
      have h2 : (i.1 : G) ≠ g := i.2.2
      simp [h1, h2]
    · simp [hg]

omit [Fintype G] in
@[simp] theorem avwIndexEquiv_one {g : G} (hg : g ≠ 1) :
    avwIndexEquiv hg (1 : G) = .zero := by simp [avwIndexEquiv]

omit [Fintype G] in
@[simp] theorem avwIndexEquiv_self {g : G} (hg : g ≠ 1) :
    avwIndexEquiv hg g = .last := by simp [avwIndexEquiv, hg]

omit [Fintype G] in
@[simp] theorem avwIndexEquiv_mid {g : G} (hg : g ≠ 1) (h : AVWMid g) :
    avwIndexEquiv hg h.1 = .middle h := by
  have h1 : (h.1 : G) ≠ 1 := h.2.1
  have h2 : (h.1 : G) ≠ g := h.2.2
  simp [avwIndexEquiv, h1, h2]

/-- The legwise relabelling of AVW Theorem 7.2: the `X` and `Y` legs send `1 ↦ 0` and `g ↦ q + 1`,
while the `Z` leg additionally swaps the two distinguished coordinates, because in the surviving
terms the `Z` index `1` plays the role of `q + 1` and the `Z` index `g` plays the role of `0`. -/
def avwLegEquiv {g : G} (hg : g ≠ 1) :
    ∀ c, GroupIndex G c ≃ GenCWIndexFamily (AVWMid g) c
  | .X => avwIndexEquiv hg
  | .Y => avwIndexEquiv hg
  | .Z => (avwIndexEquiv hg).trans (Equiv.swap .zero .last)

/-- AVW's displayed leading tensor is a generalized Coppersmith--Winograd tensor with middle block
`G \ {1, g}` and middle permutation `σ(h) = h⁻¹ g`.

Proof sketch: apply the legwise relabelling `avwLegEquiv` to each of the six displayed families of
terms.  On `X` and `Y` the identity becomes the coordinate `0` and `g` becomes `q + 1`; on `Z` the
two are exchanged.  This turns `x_1 y_1 z_1`, `x_1 y_g z_g`, `x_g y_1 z_g` into the three corner
terms and, for each `h ∉ {1, g}`, turns `x_1 y_h z_h`, `x_h y_1 z_h`, `x_h y_{h⁻¹g} z_g` into the
three middle terms at `h`, using `h · (h⁻¹g) = g` for the last `Z` index.  No reindexing of the
middle sum is needed because the middle block is `G \ {1, g}` itself. -/
theorem avwTarget_isomorphic_genCW {g : G} (hg : g ≠ 1) :
    Isomorphic (avwTarget K g) (genCW K (AVWMid g) (avwPerm g)) := by
  classical
  refine ⟨relabelLegEquiv K (avwLegEquiv hg), ?_⟩
  have hterm : ∀ a b : G,
      PiTensorProduct.congr (relabelLegEquiv K (avwLegEquiv hg))
          (pure (K := K) (groupTermMul K a b)) =
        pure (K := K) (ofLegs (V := GenCWSpace K (AVWMid g))
          (Pi.single (avwLegEquiv hg .X a) 1) (Pi.single (avwLegEquiv hg .Y b) 1)
          (Pi.single (avwLegEquiv hg .Z (a * b)) 1)) := by
    intro a b
    rw [pure_groupTermMul_ofLegs, congr_relabelLegEquiv_pure]
  have hmid : ∀ h : AVWMid g,
      PiTensorProduct.congr (relabelLegEquiv K (avwLegEquiv hg))
          (pure (K := K) (groupTermMul K (1 : G) h.1) +
            pure (K := K) (groupTermMul K h.1 (1 : G)) +
            pure (K := K) (groupTermMul K h.1 (h.1⁻¹ * g))) =
        genCWMiddle K (avwPerm g) h := by
    intro h
    have hzg : h.1 * (h.1⁻¹ * g) = g := by
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    rw [map_add, map_add, hterm, hterm, hterm, hzg]
    have hy : avwIndexEquiv hg (h.1⁻¹ * g) =
        (GenCWIndex.middle (avwPerm g h) : GenCWIndex (AVWMid g)) := by
      rw [show h.1⁻¹ * g = (avwPerm g h).1 from rfl, avwIndexEquiv_mid]
    simp only [avwLegEquiv, Equiv.trans_apply, avwIndexEquiv_one, avwIndexEquiv_self,
      avwIndexEquiv_mid, one_mul, mul_one, Equiv.swap_apply_right,
      GenCWIndex.swap_middle, hy, genCWMiddle, gcwBasis]
    abel
  have hcorner :
      PiTensorProduct.congr (relabelLegEquiv K (avwLegEquiv hg))
          (pure (K := K) (groupTermMul K (1 : G) 1) +
            pure (K := K) (groupTermMul K (1 : G) g) +
            pure (K := K) (groupTermMul K g (1 : G))) =
        genCWCorners K (AVWMid g) := by
    rw [map_add, map_add, hterm, hterm, hterm]
    simp only [avwLegEquiv, Equiv.trans_apply, avwIndexEquiv_one, avwIndexEquiv_self,
      one_mul, mul_one, Equiv.swap_apply_left, Equiv.swap_apply_right, genCWCorners, gcwBasis]
  rw [avwTarget, map_add, map_sum, hcorner, Finset.sum_congr rfl (fun h _ ↦ hmid h), genCW]

/-- The middle block has `|G| - 2` elements. -/
theorem card_AVWMid {g : G} (hg : g ≠ 1) : Fintype.card (AVWMid g) = Fintype.card G - 2 := by
  rw [Fintype.card_subtype]
  have hfilter : (Finset.univ.filter (fun h : G ↦ h ≠ 1 ∧ h ≠ g)) =
      Finset.univ \ ({1, g} : Finset G) := by
    ext x
    simp
  rw [hfilter, Finset.card_sdiff, Finset.inter_univ, Finset.card_pair (Ne.symm hg),
    Finset.card_univ]

/-- **AVW Theorem 7.2 (explicit form).**  For a finite group `G` and any `g ≠ 1`, the group tensor
`T_G = ∑_{a,b} x_a y_b z_{ab}` monomially degenerates to a tensor which is a generalized
Coppersmith--Winograd tensor of parameter `|G| - 2`.

Proof sketch: `groupTensorMul_monomialDegenerates_avwTarget` supplies the monomial certificate with
AVW's weights and leading degree `2`; `avwTarget_isomorphic_genCW` identifies its leading term with
`CW^σ` on the middle block `G \ {1, g}`; `genCW_isomorphic_congr` transports that along any
bijection `G \ {1, g} ≃ Fin (|G| - 2)`, which exists by `card_AVWMid`. -/
theorem groupTensorMul_monomialDegenerates_isGeneralizedCW {g : G} (hg : g ≠ 1) :
    MonomialDegenerates (groupTensorMul K G) (avwTarget K g) ∧
      IsGeneralizedCW K (Fintype.card G - 2) (avwTarget K g) := by
  classical
  refine ⟨groupTensorMul_monomialDegenerates_avwTarget hg, ?_⟩
  let ε : AVWMid g ≃ Fin (Fintype.card G - 2) := Fintype.equivFinOfCardEq (card_AVWMid hg)
  exact ⟨Equiv.permCongr ε (avwPerm g),
    (avwTarget_isomorphic_genCW hg).trans (genCW_isomorphic_congr ε (avwPerm g))⟩

/-- **AVW Theorem 7.2.**  For every finite group `G` with at least two elements there is a
monomial degeneration of the group tensor `T_G` into a generalized Coppersmith--Winograd tensor of
parameter `|G| - 2`. -/
theorem exists_monomialDegenerates_isGeneralizedCW [Nontrivial G] :
    ∃ T : Tensor3 K (GroupSpace K G),
      MonomialDegenerates (groupTensorMul K G) T ∧
        IsGeneralizedCW K (Fintype.card G - 2) T := by
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  exact ⟨avwTarget K g, groupTensorMul_monomialDegenerates_isGeneralizedCW hg⟩

/-- The same conclusion for the repository's primary *symmetric* presentation
`T_G = ∑_{a,b} x_a y_b z_{(ab)⁻¹}`, in the weaker basis-free form of a degree-`2` polynomial
degeneration.  Monomial degeneration is basis dependent, so the certificate itself is stated for
the multiplicative presentation; the two differ by the exact relabelling
`groupTensor_isomorphic_groupTensorMul`, which is a degree-zero polynomial degeneration, and
degrees compose as `(2 + 1) * 0 + 2 = 2`. -/
theorem groupTensor_polynomialDegeneratesAt_generalizedCW [Nontrivial G] :
    ∃ (q : ℕ) (σ : Equiv.Perm (Fin q)), q = Fintype.card G - 2 ∧
      PolynomialDegeneratesAt 2 (groupTensor K G) (genCW K (Fin q) σ) := by
  classical
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  obtain ⟨σ, hσ⟩ := (groupTensorMul_monomialDegenerates_isGeneralizedCW (K := K) hg).2
  refine ⟨Fintype.card G - 2, σ, rfl, ?_⟩
  have h0 : PolynomialDegeneratesAt 0 (groupTensor K G) (groupTensorMul K G) :=
    PolynomialDegeneratesAt.of_restricts (groupTensor_isomorphic_groupTensorMul).restricts
  have h2 : PolynomialDegeneratesAt 2 (groupTensorMul K G) (avwTarget K g) :=
    groupTensorMul_polynomialDegeneratesAt_avwTarget hg
  have h3 : PolynomialDegeneratesAt 0 (avwTarget K g) (genCW K (Fin (Fintype.card G - 2)) σ) :=
    PolynomialDegeneratesAt.of_restricts hσ.restricts
  have hcomp := (h0.trans h2).trans h3
  simpa using hcomp

end Identification

/-! ## Tiny regression clients -/

/-- The classical Coppersmith--Winograd tensor is a generalized Coppersmith--Winograd tensor of
parameter `q`: the member of the family carrying the identity permutation. -/
theorem coppersmithWinograd_isGeneralizedCW (K : Type u) [CommSemiring K] (q : ℕ) :
    IsGeneralizedCW K q (coppersmithWinograd K q) :=
  ⟨Equiv.refl _, (genCW_isomorphic_coppersmithWinograd K q).symm⟩

/-- Smallest nontrivial instance of AVW Theorem 7.2: the group tensor of the two-element group
monomially degenerates to a generalized Coppersmith--Winograd tensor of parameter `|G| - 2 = 0`,
that is, to the bare corner tensor `x_0 y_0 z_1 + x_0 y_1 z_0 + x_1 y_0 z_0`.  This client exists to
check that the parameter arithmetic and the leg relabelling really instantiate on a concrete
group. -/
theorem twoElementGroup_monomialDegenerates_isGeneralizedCW :
    ∃ T : Tensor3 ℚ (GroupSpace ℚ (Multiplicative (Fin 2))),
      MonomialDegenerates (groupTensorMul ℚ (Multiplicative (Fin 2))) T ∧
        IsGeneralizedCW ℚ 0 T := by
  have hcard : Fintype.card (Multiplicative (Fin 2)) - 2 = 0 := by simp
  have hg : (Multiplicative.ofAdd (1 : Fin 2)) ≠ 1 := by decide
  have h := groupTensorMul_monomialDegenerates_isGeneralizedCW (K := ℚ) hg
  rw [hcard] at h
  exact ⟨_, h⟩

end AlgebraicComplexity.Examples
