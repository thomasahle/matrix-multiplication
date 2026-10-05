/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Concise
import AlgebraicComplexity.Tensor.Coordinates
import Mathlib.Algebra.Group.Equiv.Basic

/-!
# The structural tensor of a finite group algebra

For a finite group `G` (written multiplicatively, and **not** assumed abelian) and a commutative
semiring `K` of scalars, this file defines the *group tensor* `groupTensor K G`: the structural
tensor of the group algebra `K[G]`, presented in the standard coordinate basis `{e_g | g ∈ G}` on
each of the three legs.

## Support convention

The structural tensor of an algebra `A` with basis `(e_i)` is the trilinear form
`(a, b, c) ↦ ⟨a * b, c⟩`.  For a group algebra there are two customary coordinate presentations of
it, differing only by how the third leg is labelled:

* the *multiplicative* convention `∑_{g,h} x_g ⊗ y_h ⊗ z_{g*h}`, with support
  `{(a, b, c) | a * b = c}`.  This is the form printed in
  Alman–Vassilevska Williams, *Limits on all known (and some unknown) approaches to matrix
  multiplication* (arXiv:1810.08671), Definition 3.2, and it is the form in which their Lemma 6.1
  reads off a tri-coloured sum-free set;
* the *symmetric* convention `∑_{g,h} x_g ⊗ y_h ⊗ z_{(g*h)⁻¹}`, with support
  `{(a, b, c) | a * b * c = 1}`.  Equivalently, the coefficient of the triple `(a, b, c)` is the
  coefficient of the identity in the product `a * b * c` inside `K[G]`.

This file takes the **symmetric** convention as primary, because its support condition
`a * b * c = 1` is genuinely invariant under cyclic rotation of the three legs even for a
nonabelian group (`abc = 1 → bca = 1` by conjugation), which is the symmetry barrier arguments use;
the multiplicative convention only has that symmetry after relabelling.  Nothing is lost: the two
tensors are related by relabelling the `Z` leg along the inversion bijection of `G`, so they are
legwise isomorphic.  Both are defined here (`groupTensor` and `groupTensorMul`) and the explicit
isomorphism is `groupTensor_isomorphic_groupTensorMul`, so a downstream client may quote either
presentation of AVW and transport restriction, degeneration, and rank statements between them.

## Main results

* `groupTensor`, `groupTerm`: the tensor and its `|G|²` defining pure terms;
* `standardCoordinateEquiv_groupTensor`: the coordinate/support characterisation
  `T_G[a, b, c] = 1` if `a * b * c = 1` and `0` otherwise, stated through the canonical coefficient
  equivalence `standardCoordinateEquiv` of `Tensor/Coordinates.lean`;
* `groupTensor_rankLE`: the trivial certificate `R(T_G) ≤ |G|²` read off the defining sum;
* `contractX_groupTensor`, `contractY_groupTensor`, `contractZ_groupTensor` and
  `groupTensor_isConcise`: every single-leg flattening of `T_G` has full rank `|G|`, so `T_G` is
  concise on all three legs; over a field this gives the flattening lower bound
  `groupTensor_card_le_of_rankLE : R(T_G) ≥ |G|`;
* `groupTensor_isomorphic_of_mulEquiv`: isomorphic groups have legwise isomorphic group tensors;
* `groupCycleEquiv_groupTensor` and `groupSwapInvEquiv_groupTensor`: the exact leg symmetries of
  the symmetric convention — cyclic rotation on the nose, and the transposition of two legs
  combined with the inversion anti-automorphism on all three.

## Layer placement

This is a layer-1 (tensor algebra) leaf module.  It imports only the tensor core
(`Tensor/Coordinates.lean` for coefficients and `Tensor/Concise.lean` for the dual-contraction
conciseness machinery) together with Mathlib group theory.  It deliberately mentions no
matrix-multiplication tensor and no named construction from any paper; the connections to
generalized Coppersmith–Winograd tensors (AVW Theorem 7.2), to sub-tensor obstructions (AVW
Lemma 6.3), and to tri-coloured sum-free sets (AVW Lemma 6.1) belong to downstream clients.

## Non-goals and deliberate omissions

The rank bound proved here is the honest generic one, `R(T_G) ≤ |G|²`, obtained by counting the
defining pure terms.  The familiar bound `R(T_G) ≤ |G|` is **not** available at this generality and
is not claimed:

* for abelian `G` it needs a discrete Fourier transform, hence a scalar ring containing a
  primitive `|G|`-th root of unity and in which `|G|` is invertible — under those hypotheses the
  characters diagonalize `K[G]` and `T_G` becomes a direct sum of `|G|` copies of `⟨1,1,1⟩`;
* for nonabelian `G` it is false: over `ℂ` Wedderburn's decomposition makes `T_G` isomorphic to
  `⨁_u ⟨d_u, d_u, d_u⟩` with `∑_u d_u² = |G|`, and the Alder–Strassen bound
  `R(A) ≥ 2 · dim A − #{maximal two-sided ideals of A}` gives `R(T_G) ≥ 2|G| − ℓ > |G|`, where
  `ℓ`, the number of irreducible characters, is strictly smaller than `|G|`.

Both refinements are left as documented future work for a module that may assume a field, roots of
unity, or representation theory.  The conciseness lower bound `R(T_G) ≥ |G|` proved here is the
matching bound that holds over every field.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

/-- The coordinate index type on each leg of a group tensor: one copy of the group `G` on all
three legs. -/
abbrev GroupIndex (G : Type v) : Leg → Type v := fun _ ↦ G

/-- The three coordinate vector spaces of a group tensor, each the free `K`-module `G → K` on the
group elements. -/
abbrev GroupSpace (K : Type u) (G : Type v) : Leg → Type (max u v) :=
  CoordinateSpace K (GroupIndex G)

section Definition

variable {K : Type u} [CommSemiring K] {G : Type v} [Group G] [Fintype G] [DecidableEq G]

/-- The pure summand `x_g ⊗ y_h ⊗ z_{(g*h)⁻¹}` of the group tensor indexed by the pair `(g, h)`.

Its `Z` component is the standard basis vector at `(g * h)⁻¹`, so the three indices of the term
multiply to `1`. -/
def groupTerm (K : Type u) [CommSemiring K] {G : Type v} [Group G] [DecidableEq G] (g h : G) :
    ∀ c, GroupSpace K G c
  | .X => Pi.single g 1
  | .Y => Pi.single h 1
  | .Z => Pi.single (g * h)⁻¹ 1

omit [Fintype G] in
/-- The `X` component of the defining term at `(g, h)` is the standard basis vector at `g`. -/
@[simp] theorem groupTerm_X (g h : G) :
    groupTerm K g h .X = Pi.single g (1 : K) := rfl

omit [Fintype G] in
/-- The `Y` component of the defining term at `(g, h)` is the standard basis vector at `h`. -/
@[simp] theorem groupTerm_Y (g h : G) :
    groupTerm K g h .Y = Pi.single h (1 : K) := rfl

omit [Fintype G] in
/-- The `Z` component of the defining term at `(g, h)` is the standard basis vector at
`(g * h)⁻¹`. -/
@[simp] theorem groupTerm_Z (g h : G) :
    groupTerm K g h .Z = Pi.single (g * h)⁻¹ (1 : K) := rfl

/-- The structural tensor of the group algebra `K[G]` in the standard basis, in the symmetric
convention `T_G = ∑_{g,h ∈ G} x_g ⊗ y_h ⊗ z_{(g*h)⁻¹}`.

See the module documentation for the comparison with the multiplicative convention
`∑ x_g ⊗ y_h ⊗ z_{g*h}` of Alman–Vassilevska Williams (arXiv:1810.08671, Definition 3.2), which is
`groupTensorMul` below. -/
noncomputable def groupTensor (K : Type u) [CommSemiring K] (G : Type v) [Group G] [Fintype G]
    [DecidableEq G] : Tensor3 K (GroupSpace K G) :=
  ∑ p : G × G, pure (K := K) (groupTerm K p.1 p.2)

/-- The support condition of the symmetric convention: the three leg indices multiply to the
identity, in the order `X`, `Y`, `Z`. -/
abbrev GroupCompatible {G : Type v} [Group G] (a : ∀ c, GroupIndex G c) : Prop :=
  a .X * a .Y * a .Z = 1

/-- The support condition is decidable, so it may appear in coordinate `if` expressions. -/
instance decidableGroupCompatible {G : Type v} [Group G] [DecidableEq G]
    (a : ∀ c, GroupIndex G c) : Decidable (GroupCompatible a) :=
  inferInstance

/-- Coordinate support formula for the group tensor: in the standard basis on each leg, the
coefficient of the triple `a` is `1` when `a .X * a .Y * a .Z = 1` and `0` otherwise.

Proof sketch: expand the defining sum through the coefficient equivalence.  The term indexed by
`(g, h)` contributes the product of three Kronecker deltas, which vanishes unless `g = a .X` and
`h = a .Y`; the single surviving term contributes the delta of `a .Z = (a .X * a .Y)⁻¹`, and in a
group that equation is equivalent to `a .X * a .Y * a .Z = 1`. -/
@[simp] theorem standardCoordinateEquiv_groupTensor (a : ∀ c, GroupIndex G c) :
    standardCoordinateEquiv (K := K) (κ := GroupIndex G) (groupTensor K G) a =
      if GroupCompatible a then 1 else 0 := by
  classical
  unfold groupTensor
  rw [map_sum, Finset.sum_apply, Finset.sum_eq_single (a .X, a .Y)]
  · have hiff : (a .Z = (a .X * a .Y)⁻¹) ↔ GroupCompatible a := by
      show (a .Z = (a .X * a .Y)⁻¹) ↔ a .X * a .Y * a .Z = 1
      constructor
      · rintro h
        simp [h]
      · intro h
        exact eq_inv_of_mul_eq_one_right h
    simp only [standardCoordinateEquiv_pure, prod_leg, groupTerm_X, groupTerm_Y, groupTerm_Z,
      Pi.single_eq_same, one_mul]
    simp only [Pi.single_apply]
    exact if_congr hiff rfl rfl
  · rintro ⟨g, h⟩ _ hne
    have hnot : ¬(a .X = g ∧ a .Y = h) := by
      rintro ⟨rfl, rfl⟩
      exact hne rfl
    simp only [standardCoordinateEquiv_pure, prod_leg, groupTerm, Pi.single_apply]
    rcases not_and_or.mp hnot with hx | hy
    · simp [hx]
    · simp [hy]
  · simp

/-- The defining expansion of the group tensor into its `|G|²` pure terms is a rank certificate:
`R(T_G) ≤ |G|²`.

This is the honest generic bound; see the module documentation for why `|G|` is not available
without further hypotheses on `K` or on `G`. -/
theorem groupTensor_rankLE : RankLE (Fintype.card G ^ 2) (groupTensor K G) := by
  classical
  have h := RankLE.fintype_sum_pure (K := K) (V := GroupSpace K G)
    (fun p : G × G ↦ groupTerm K p.1 p.2)
  simpa [groupTensor, Fintype.card_prod, pow_two] using h

end Definition

section Conciseness

variable {K : Type u} [CommSemiring K] {G : Type v} [Group G] [Fintype G] [DecidableEq G]

/-- Contracting the `Y` leg at `h` and the `Z` leg at `(g * h)⁻¹` isolates the standard `X`-basis
vector at `g`.

Proof sketch: this is the Latin-square property of the group.  Fixing two of the three indices of
a compatible triple determines the third, so exactly one defining term of `T_G` survives the pair
of coordinate functionals, namely the one indexed by `(g, h)`. -/
theorem contractX_groupTensor (g h : G) :
    contractX (LinearMap.proj (R := K) h) (LinearMap.proj (R := K) (g * h)⁻¹)
        (groupTensor K G) = Pi.single g 1 := by
  classical
  unfold groupTensor
  rw [map_sum]
  ext a
  rw [Finset.sum_eq_single (g, h)]
  · simp [groupTerm, Pi.single_apply]
  · rintro ⟨g', h'⟩ _ hne
    simp only [contractX_pure, groupTerm, LinearMap.proj_apply, Pi.single_apply]
    by_cases hh : h = h'
    · subst hh
      have hg : g ≠ g' := fun hcontra ↦ hne (by simp [hcontra])
      simp [hg]
    · simp [hh]
  · simp

/-- Contracting the `X` leg at `g` and the `Z` leg at `(g * h)⁻¹` isolates the standard `Y`-basis
vector at `h`.  Same Latin-square argument as `contractX_groupTensor`. -/
theorem contractY_groupTensor (g h : G) :
    contractY (LinearMap.proj (R := K) g) (LinearMap.proj (R := K) (g * h)⁻¹)
        (groupTensor K G) = Pi.single h 1 := by
  classical
  unfold groupTensor
  rw [map_sum]
  ext a
  rw [Finset.sum_eq_single (g, h)]
  · simp [groupTerm, Pi.single_apply]
  · rintro ⟨g', h'⟩ _ hne
    simp only [contractY_pure, groupTerm, LinearMap.proj_apply, Pi.single_apply]
    by_cases hg : g = g'
    · subst hg
      have hh : h ≠ h' := fun hcontra ↦ hne (by simp [hcontra])
      simp [hh]
    · simp [hg]
  · simp

/-- Contracting the `X` leg at `g` and the `Y` leg at `h` isolates the standard `Z`-basis vector at
`(g * h)⁻¹`.  Same Latin-square argument as `contractX_groupTensor`. -/
theorem contractZ_groupTensor (g h : G) :
    contractZ (LinearMap.proj (R := K) g) (LinearMap.proj (R := K) h)
        (groupTensor K G) = Pi.single (g * h)⁻¹ 1 := by
  classical
  unfold groupTensor
  rw [map_sum]
  ext a
  rw [Finset.sum_eq_single (g, h)]
  · simp [groupTerm, Pi.single_apply]
  · rintro ⟨g', h'⟩ _ hne
    simp only [contractZ_pure, groupTerm, LinearMap.proj_apply, Pi.single_apply]
    by_cases hg : g = g'
    · subst hg
      have hh : h ≠ h' := fun hcontra ↦ hne (by simp [hcontra])
      simp [hh]
    · simp [hg]
  · simp

/-- The group tensor is concise on its `X` leg: the `Y,Z` contractions span all of `G → K`. -/
theorem groupTensor_isConciseX : IsConciseX (groupTensor K G) := by
  classical
  apply le_antisymm le_top
  rw [← (Pi.basisFun K G).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨g, rfl⟩
  rw [Pi.basisFun_apply]
  refine ⟨(LinearMap.proj (R := K) (1 : G), LinearMap.proj (R := K) g⁻¹), ?_⟩
  simpa using contractX_groupTensor (K := K) g 1

/-- The group tensor is concise on its `Y` leg: the `X,Z` contractions span all of `G → K`. -/
theorem groupTensor_isConciseY : IsConciseY (groupTensor K G) := by
  classical
  apply le_antisymm le_top
  rw [← (Pi.basisFun K G).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨h, rfl⟩
  rw [Pi.basisFun_apply]
  refine ⟨(LinearMap.proj (R := K) (1 : G), LinearMap.proj (R := K) h⁻¹), ?_⟩
  simpa using contractY_groupTensor (K := K) 1 h

/-- The group tensor is concise on its `Z` leg: the `X,Y` contractions span all of `G → K`. -/
theorem groupTensor_isConciseZ : IsConciseZ (groupTensor K G) := by
  classical
  apply le_antisymm le_top
  rw [← (Pi.basisFun K G).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨k, rfl⟩
  rw [Pi.basisFun_apply]
  refine ⟨(LinearMap.proj (R := K) (1 : G), LinearMap.proj (R := K) k⁻¹), ?_⟩
  have h := contractZ_groupTensor (K := K) (1 : G) k⁻¹
  simpa using h

/-- The group tensor of any finite group is concise on all three legs.

Proof sketch: for each leg, the group's Latin-square property turns the slice obtained by fixing
one index into a permutation matrix, so the coordinate contractions realize every standard basis
vector of that leg (`contractX_groupTensor` and its two companions). -/
theorem groupTensor_isConcise : IsConcise (groupTensor K G) :=
  ⟨groupTensor_isConciseX, groupTensor_isConciseY, groupTensor_isConciseZ⟩

end Conciseness

section Flattening

variable {K : Type u} [Field K] {G : Type v} [Group G] [Fintype G] [DecidableEq G]

/-- Flattening lower bound over a field: every rank certificate for the group tensor has length at
least `|G|`.

Proof sketch: `T_G` is concise on the `X` leg, so the general flattening bound of
`Tensor/Concise.lean` bounds the dimension `|G|` of that leg by the certificate length. -/
theorem groupTensor_card_le_of_rankLE {r : ℕ} (h : RankLE r (groupTensor K G)) :
    Fintype.card G ≤ r := by
  have hdim := h.finrank_X_le (groupTensor_isConciseX (K := K) (G := G))
  simpa [GroupSpace, GroupIndex, CoordinateSpace, Module.finrank_fintype_fun_eq_card] using hdim

end Flattening

section Functoriality

variable {K : Type u} [CommSemiring K]
variable {G : Type v} [Group G] [Fintype G] [DecidableEq G]
variable {H : Type w} [Group H] [Fintype H] [DecidableEq H]

/-- The legwise coordinate equivalence induced by a group isomorphism: relabel the standard basis
of `G → K` along `e`.  This is `Tensor.relabelLegEquiv` for the constant leg family `GroupIndex`
and the underlying bijection of `e`. -/
noncomputable def groupMulEquivLegEquiv (K : Type u) [CommSemiring K] (e : G ≃* H) (c : Leg) :
    GroupSpace K G c ≃ₗ[K] GroupSpace K H c :=
  relabelLegEquiv K (fun _ : Leg ↦ e.toEquiv) c

omit [Fintype G] [Fintype H] in
/-- The relabelling equivalence sends the standard basis vector at `g` to the standard basis
vector at `e g`. -/
@[simp] theorem groupMulEquivLegEquiv_single (e : G ≃* H) (c : Leg) (g : G) :
    groupMulEquivLegEquiv K e c (Pi.single g (1 : K)) = Pi.single (e g) 1 :=
  funCongrLeft_symm_single (K := K) e.toEquiv g 1

/-- Isomorphic finite groups have legwise isomorphic group tensors.

Proof sketch: relabelling each leg along `e` carries the defining term at `(g, h)` to the defining
term at `(e g, e h)`, because `e` is multiplicative and commutes with inversion; summing over the
bijection `(g, h) ↦ (e g, e h)` of index pairs matches the two defining sums. -/
theorem groupTensor_isomorphic_of_mulEquiv (e : G ≃* H) :
    Isomorphic (groupTensor K G) (groupTensor K H) := by
  classical
  refine ⟨groupMulEquivLegEquiv K e, ?_⟩
  unfold groupTensor
  rw [map_sum]
  have hterm : ∀ p : G × G,
      PiTensorProduct.congr (groupMulEquivLegEquiv K e) (pure (K := K) (groupTerm K p.1 p.2)) =
        pure (K := K) (groupTerm K (e p.1) (e p.2)) := by
    rintro ⟨g, h⟩
    rw [PiTensorProduct.congr_tprod]
    congr 1
    funext c
    cases c <;>
      simp [groupTerm, groupMulEquivLegEquiv_single, map_mul, map_inv]
  simp_rw [hterm]
  exact Equiv.sum_comp (Equiv.prodCongr e.toEquiv e.toEquiv)
    (fun q : H × H ↦ pure (K := K) (groupTerm K q.1 q.2))

end Functoriality

section Symmetry

variable {K : Type u} [CommSemiring K] {G : Type v} [Group G] [Fintype G] [DecidableEq G]

/-- Retype each cyclically permuted leg of a group tensor; all three legs carry the same
coordinate space `G → K`.  This is `Tensor.relabelLegEquiv` at the identity bijection. -/
noncomputable def groupCycleLegEquiv (K : Type u) [CommSemiring K] (G : Type v) (c : Leg) :
    GroupSpace K G (cycle.symm c) ≃ₗ[K] GroupSpace K G c :=
  relabelLegEquiv (ι := fun c ↦ GroupIndex G (cycle.symm c)) (ι' := GroupIndex G) K
    (fun _ ↦ Equiv.refl G) c

/-- The canonical cyclic leg rotation `X ↦ Y ↦ Z ↦ X` on the ambient space of a group tensor. -/
noncomputable def groupCycleEquiv (K : Type u) [CommSemiring K] (G : Type v) [Group G] :
    Tensor3 K (GroupSpace K G) ≃ₗ[K] Tensor3 K (GroupSpace K G) :=
  (permute cycle).trans (PiTensorProduct.congr (groupCycleLegEquiv K G))

/-- Rotating the summation index of the group tensor: `(g, h) ↦ ((g * h)⁻¹, g)`. -/
def groupPairCycleEquiv (G : Type v) [Group G] : G × G ≃ G × G where
  toFun p := ((p.1 * p.2)⁻¹, p.1)
  invFun q := (q.2, (q.1 * q.2)⁻¹)
  left_inv := by
    rintro ⟨g, h⟩
    simp [mul_assoc]
  right_inv := by
    rintro ⟨a, b⟩
    simp

omit [Fintype G] [DecidableEq G] in
/-- Evaluating the index rotation: the pair `(g, h)` is sent to `((g * h)⁻¹, g)`. -/
@[simp] theorem groupPairCycleEquiv_apply (g h : G) :
    groupPairCycleEquiv G (g, h) = ((g * h)⁻¹, g) := rfl

omit [Fintype G] in
/-- The cyclic leg rotation carries the defining term at `(g, h)` to the defining term at
`((g * h)⁻¹, g)`. -/
@[simp] theorem groupCycleEquiv_pure (g h : G) :
    groupCycleEquiv K G (pure (K := K) (groupTerm K g h)) =
      pure (K := K) (groupTerm K (g * h)⁻¹ g) := by
  simp only [groupCycleEquiv, LinearEquiv.trans_apply, permute_pure,
    PiTensorProduct.congr_tprod]
  congr 1
  funext c
  cases c <;> simp [groupCycleLegEquiv, relabelLegEquiv, groupTerm, mul_assoc]

/-- The symmetric convention is exactly cyclically symmetric: rotating the three legs of `T_G`
gives `T_G` back, for every finite group, abelian or not.

Proof sketch: the support condition `a * b * c = 1` is invariant under cyclic rotation, since
`abc = 1` implies `bca = a⁻¹(abc)a = 1`.  Concretely, rotating the legs sends the defining term at
`(g, h)` to the defining term at `((g * h)⁻¹, g)`, and that index map is the bijection
`groupPairCycleEquiv` of `G × G`, so the two defining sums agree term by term after
reindexing. -/
theorem groupCycleEquiv_groupTensor :
    groupCycleEquiv K G (groupTensor K G) = groupTensor K G := by
  unfold groupTensor
  rw [map_sum]
  simp_rw [groupCycleEquiv_pure]
  exact Equiv.sum_comp (groupPairCycleEquiv G)
    (fun q : G × G ↦ pure (K := K) (groupTerm K q.1 q.2))

/-- Retype the `Y`/`Z` leg transposition of a group tensor and simultaneously relabel every leg
along the inversion bijection of `G`.  This is `Tensor.relabelLegEquiv` at `Equiv.inv G`. -/
noncomputable def groupSwapInvLegEquiv (K : Type u) [CommSemiring K] (G : Type v) [Group G]
    (c : Leg) : GroupSpace K G (xzy.symm c) ≃ₗ[K] GroupSpace K G c :=
  relabelLegEquiv (ι := fun c ↦ GroupIndex G (xzy.symm c)) (ι' := GroupIndex G) K
    (fun _ ↦ Equiv.inv G) c

omit [Fintype G] in
/-- The inverting relabelling sends the standard basis vector at `g` to the one at `g⁻¹`. -/
@[simp] theorem groupSwapInvLegEquiv_single (c : Leg) (g : G) :
    groupSwapInvLegEquiv K G c (Pi.single g (1 : K)) = Pi.single g⁻¹ 1 :=
  funCongrLeft_symm_single (K := K) (Equiv.inv G) g 1

/-- Transposing the `Y` and `Z` legs of a group tensor while relabelling all three legs by
inversion. -/
noncomputable def groupSwapInvEquiv (K : Type u) [CommSemiring K] (G : Type v) [Group G] :
    Tensor3 K (GroupSpace K G) ≃ₗ[K] Tensor3 K (GroupSpace K G) :=
  (permute xzy).trans (PiTensorProduct.congr (groupSwapInvLegEquiv K G))

/-- Reflecting the summation index of the group tensor: `(g, h) ↦ (g⁻¹, g * h)`. -/
def groupPairSwapInvEquiv (G : Type v) [Group G] : G × G ≃ G × G where
  toFun p := (p.1⁻¹, p.1 * p.2)
  invFun q := (q.1⁻¹, q.1 * q.2)
  left_inv := by
    rintro ⟨g, h⟩
    simp
  right_inv := by
    rintro ⟨a, b⟩
    simp

omit [Fintype G] [DecidableEq G] in
/-- Evaluating the index reflection: the pair `(g, h)` is sent to `(g⁻¹, g * h)`. -/
@[simp] theorem groupPairSwapInvEquiv_apply (g h : G) :
    groupPairSwapInvEquiv G (g, h) = (g⁻¹, g * h) := rfl

omit [Fintype G] in
/-- The inverting `Y`/`Z` transposition carries the defining term at `(g, h)` to the defining term
at `(g⁻¹, g * h)`. -/
@[simp] theorem groupSwapInvEquiv_pure (g h : G) :
    groupSwapInvEquiv K G (pure (K := K) (groupTerm K g h)) =
      pure (K := K) (groupTerm K g⁻¹ (g * h)) := by
  simp only [groupSwapInvEquiv, LinearEquiv.trans_apply, permute_pure,
    PiTensorProduct.congr_tprod]
  congr 1
  funext c
  -- `xzy.symm` evaluates on each constructor, so `show` replaces the permuted leg by a literal
  -- one; a propositional rewrite of the leg index would be blocked by the dependent type.
  cases c with
  | X =>
      show groupSwapInvLegEquiv K G .X (groupTerm K g h .X) = groupTerm K g⁻¹ (g * h) .X
      simp
  | Y =>
      show groupSwapInvLegEquiv K G .Y (groupTerm K g h .Z) = groupTerm K g⁻¹ (g * h) .Y
      simp
  | Z =>
      show groupSwapInvLegEquiv K G .Z (groupTerm K g h .Y) = groupTerm K g⁻¹ (g * h) .Z
      simp

/-- The remaining symmetry of the symmetric convention: transposing two legs is a symmetry of
`T_G` only when combined with the inversion anti-automorphism of `G` on all three legs.

Proof sketch: `a * b * c = 1` is not preserved by transposing `a` and `b` in a nonabelian group,
but it is preserved by `(a, b, c) ↦ (a⁻¹, c⁻¹, b⁻¹)`, since `abc = 1` gives
`a⁻¹ c⁻¹ b⁻¹ = a⁻¹ (bc)⁻¹ = a⁻¹ a = 1`.  On defining terms this is the index bijection
`groupPairSwapInvEquiv`, and reindexing the defining sum along it proves the identity. -/
theorem groupSwapInvEquiv_groupTensor :
    groupSwapInvEquiv K G (groupTensor K G) = groupTensor K G := by
  unfold groupTensor
  rw [map_sum]
  simp_rw [groupSwapInvEquiv_pure]
  exact Equiv.sum_comp (groupPairSwapInvEquiv G)
    (fun q : G × G ↦ pure (K := K) (groupTerm K q.1 q.2))

end Symmetry

section MultiplicativeConvention

variable {K : Type u} [CommSemiring K] {G : Type v} [Group G] [Fintype G] [DecidableEq G]

/-- The pure summand `x_g ⊗ y_h ⊗ z_{g*h}` of the multiplicative convention. -/
def groupTermMul (K : Type u) [CommSemiring K] {G : Type v} [Group G] [DecidableEq G] (g h : G) :
    ∀ c, GroupSpace K G c
  | .X => Pi.single g 1
  | .Y => Pi.single h 1
  | .Z => Pi.single (g * h) 1

/-- The group tensor in the multiplicative convention `∑_{g,h} x_g ⊗ y_h ⊗ z_{g*h}` of
Alman–Vassilevska Williams (arXiv:1810.08671, Definition 3.2). -/
noncomputable def groupTensorMul (K : Type u) [CommSemiring K] (G : Type v) [Group G] [Fintype G]
    [DecidableEq G] : Tensor3 K (GroupSpace K G) :=
  ∑ p : G × G, pure (K := K) (groupTermMul K p.1 p.2)

/-- Coordinate support formula in the multiplicative convention: the coefficient of the triple `a`
is `1` when `a .X * a .Y = a .Z` and `0` otherwise. -/
@[simp] theorem standardCoordinateEquiv_groupTensorMul (a : ∀ c, GroupIndex G c) :
    standardCoordinateEquiv (K := K) (κ := GroupIndex G) (groupTensorMul K G) a =
      if a .X * a .Y = a .Z then 1 else 0 := by
  classical
  unfold groupTensorMul
  rw [map_sum, Finset.sum_apply, Finset.sum_eq_single (a .X, a .Y)]
  · simp only [standardCoordinateEquiv_pure, prod_leg, groupTermMul, Pi.single_eq_same, one_mul]
    simp only [Pi.single_apply]
    exact if_congr eq_comm rfl rfl
  · rintro ⟨g, h⟩ _ hne
    have hnot : ¬(a .X = g ∧ a .Y = h) := by
      rintro ⟨rfl, rfl⟩
      exact hne rfl
    simp only [standardCoordinateEquiv_pure, prod_leg, groupTermMul, Pi.single_apply]
    rcases not_and_or.mp hnot with hx | hy
    · simp [hx]
    · simp [hy]
  · simp

/-- Relabel only the `Z` leg by inversion, leaving the `X` and `Y` legs alone. -/
noncomputable def groupInvZLegEquiv (K : Type u) [CommSemiring K] (G : Type v) [Group G] :
    ∀ c, GroupSpace K G c ≃ₗ[K] GroupSpace K G c
  | .X => LinearEquiv.refl K _
  | .Y => LinearEquiv.refl K _
  | .Z => LinearEquiv.funCongrLeft K K (Equiv.inv G)

/-- The two coordinate conventions for the structural tensor of `K[G]` are legwise isomorphic: they
differ only by relabelling the `Z` leg along the inversion bijection of `G`.

Proof sketch: inversion sends the basis vector at `(g * h)⁻¹` to the basis vector at `g * h`, so
the identity on the `X` and `Y` legs together with inversion on the `Z` leg matches the defining
terms of the two tensors index by index, with no reindexing of the summation. -/
theorem groupTensor_isomorphic_groupTensorMul :
    Isomorphic (groupTensor K G) (groupTensorMul K G) := by
  classical
  refine ⟨groupInvZLegEquiv K G, ?_⟩
  unfold groupTensor groupTensorMul
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  rintro ⟨g, h⟩ _
  rw [PiTensorProduct.congr_tprod]
  congr 1
  funext c
  cases c with
  | X => rfl
  | Y => rfl
  | Z =>
      show LinearEquiv.funCongrLeft K K (Equiv.inv G) (Pi.single (g * h)⁻¹ (1 : K)) =
        Pi.single (g * h) 1
      simpa using funCongrLeft_symm_single (K := K) (Equiv.inv G) (g * h)⁻¹ 1

end MultiplicativeConvention

end AlgebraicComplexity.Tensor
