import AlgebraicComplexity.MatrixMultiplication
import AlgebraicComplexity.MatrixMultiplication.PositiveWordProduct
import AlgebraicComplexity.Tensor.TypeExtraction

/-!
# Multinomial type extraction for matrix-multiplication tensors

This module specializes the tensor-level word decomposition to finite direct sums of rectangular
matrix-multiplication tensors.  Every word in one multiplicity class is identified with the same
rectangular tensor, whose three dimensions are the products of the constituent dimensions with
the prescribed multiplicities.  Consequently a positive power restricts to exactly the
corresponding multinomial number of independent identical copies.

This is the finite algebraic content of the type-selection step in Schönhage's multiple
compression argument.  It does not use asymptotics or the asymptotic sum inequality.
-/

namespace AlgebraicComplexity

open Tensor
open scoped BigOperators

universe u w

variable {K : Type u} [CommSemiring K]
variable {I : Type w} [Fintype I]

/-- Package the three leg spaces of an indexed family of matrix-multiplication tensors. -/
@[reducible] def matrixMultiplicationFamily (m n p : I → ℕ) (i : I) :
    Tensor.LegModuleFamily.{u, 0} K :=
  Tensor.LegModuleFamily.of (MMSpace K (m i) (n i) (p i))

/-- The indexed tensor family, with its module instances fixed by `matrixMultiplicationFamily`. -/
@[reducible] noncomputable def matrixMultiplicationTensorFamily (m n p : I → ℕ) (i : I) :
    Tensor3 K (matrixMultiplicationFamily (K := K) m n p i).Space :=
  matrixMultiplication (K := K) (m i) (n i) (p i)

/-- A word product depends only on the word's multiplicity type. -/
theorem positiveWordProduct_eq_prod_pow (x : I → ℕ) {r : ℕ} {a : I → ℕ}
    {q : Tensor.PositiveWord I r} (hq : q ∈ Tensor.positiveTypeClass I r a) :
    positiveWordProduct x r q = ∏ i, x i ^ a i := by
  rw [positiveWordProduct_eq_fin_prod, WordType.prod_word_eq_prod_pow,
    Tensor.mem_positiveTypeClass.mp hq]

/-- The volume of the rectangular tensor selected by a multiplicity type is the product of the
constituent volumes with those multiplicities. -/
theorem productDimensions_eq_product_volume
    (m n p : I → ℕ) (a : I → ℕ) :
    (∏ i, m i ^ a i) * (∏ i, n i ^ a i) * (∏ i, p i ^ a i) =
      ∏ i, (m i * n i * p i) ^ a i := by
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]

namespace Tensor.Isomorphic

/-- Retyping a cyclically permuted matrix-multiplication tensor gives the corresponding cyclic
rotation of its three dimensions. -/
theorem matrixMultiplication_cycle (m n p : ℕ) :
    Isomorphic
      (Tensor.permute cycle (matrixMultiplication (K := K) m n p))
      (matrixMultiplication (K := K) p m n) := by
  refine ⟨mmCycleLegEquiv (K := K) m n p, ?_⟩
  simpa [mmCycleEquiv] using
    mmCycleEquiv_matrixMultiplication (K := K) m n p

/-- Retyping an inverse-cyclic leg permutation rotates matrix-multiplication dimensions in the
opposite direction: `⟨m,n,p⟩` becomes `⟨n,p,m⟩`.

Proof sketch: retype the three permuted matrix-coordinate spaces by identity equivalences and
reindex the defining sum by `(i,j,k) ↦ (j,k,i)`. -/
theorem matrixMultiplication_cycle_symm (m n p : ℕ) :
    Isomorphic
      (Tensor.permute cycle.symm (matrixMultiplication (K := K) m n p))
      (matrixMultiplication (K := K) n p m) := by
  let tripleEquiv : MMTriple m n p ≃ MMTriple n p m :=
    { toFun := fun a ↦ (a.2.1, a.2.2, a.1)
      invFun := fun a ↦ (a.2.2, a.1, a.2.1)
      left_inv := by rintro ⟨i, j, k⟩; rfl
      right_inv := by rintro ⟨j, k, i⟩; rfl }
  let legEquiv : ∀ c,
      MMSpace K m n p (cycle.symm.symm c) ≃ₗ[K] MMSpace K n p m c := by
    intro c
    cases c <;> exact LinearEquiv.refl K _
  refine ⟨legEquiv, ?_⟩
  have hterm (a : MMTriple m n p) :
      PiTensorProduct.congr legEquiv
          (Tensor.permute cycle.symm
            (pure (K := K) (mmTermOfTriple (K := K) m n p a))) =
        pure (K := K)
          (mmTermOfTriple (K := K) n p m (tripleEquiv a)) := by
    rcases a with ⟨i, j, k⟩
    simp only [Tensor.permute_pure, PiTensorProduct.congr_tprod, mmTermOfTriple]
    congr 1
    funext c
    cases c <;> rfl
  unfold matrixMultiplication
  rw [map_sum, map_sum]
  simp_rw [hterm]
  exact Equiv.sum_comp tripleEquiv
    (fun a : MMTriple n p m ↦ pure (K := K) (mmTermOfTriple (K := K) n p m a))

/-- Interchanging the `Y` and `Z` tensor legs transposes the first two matrix dimensions:
`permute xzy ⟨m,n,p⟩ ≅ ⟨n,m,p⟩`.

Proof sketch: the ambient equivalence `mmSwapYZEquiv` reverses the two coordinates in every
matrix-variable space after swapping the last two tensor roles.  Its verified action on the
defining sum is `mmSwapYZEquiv_matrixMultiplication`. -/
theorem matrixMultiplication_swapYZ (m n p : ℕ) :
    Isomorphic
      (Tensor.permute xzy (matrixMultiplication (K := K) m n p))
      (matrixMultiplication (K := K) n m p) := by
  refine ⟨mmSwapYZLegEquiv (K := K) m n p, ?_⟩
  simpa [mmSwapYZEquiv] using
    mmSwapYZEquiv_matrixMultiplication (K := K) m n p

/-- Componentwise equal dimension triples define isomorphic matrix-multiplication tensors.
This lemma is useful when arithmetic normalization changes the dependent coordinate-space
types. -/
theorem matrixMultiplication_congr
    {m n p m' n' p' : ℕ} (hm : m = m') (hn : n = n') (hp : p = p') :
    Isomorphic
      (matrixMultiplication (K := K) m n p)
      (matrixMultiplication (K := K) m' n' p') := by
  subst m'
  subst n'
  subst p'
  exact Isomorphic.refl _

/-- The binary external product law, packaged as a legwise tensor isomorphism. -/
theorem matrixMultiplication_external (m n p m' n' p' : ℕ) :
    Isomorphic
      (Tensor.external
        (matrixMultiplication (K := K) m n p)
        (matrixMultiplication (K := K) m' n' p'))
      (matrixMultiplication (K := K) (m * m') (n * n') (p * p')) := by
  refine ⟨mmProductLegEquiv (K := K) m n p m' n' p', ?_⟩
  simpa [mmExternalEquiv, PiTensorProduct.congr] using
    mmExternalEquiv_matrixMultiplication (K := K) m n p m' n' p'

omit [Fintype I] in
/-- The tensor selected by a word of matrix-multiplication constituents is the rectangular tensor
whose dimensions are the three products along that word. -/
theorem positiveWordTensor_matrixMultiplication
    (m n p : I → ℕ) (r : ℕ) (q : Tensor.PositiveWord I r) :
    Isomorphic
      (Tensor.positiveWordTensor
        (matrixMultiplicationFamily (K := K) m n p)
        (matrixMultiplicationTensorFamily (K := K) m n p) r q)
      (matrixMultiplication (K := K)
        (positiveWordProduct m r q)
        (positiveWordProduct n r q)
        (positiveWordProduct p r q)) := by
  induction r with
  | zero =>
      dsimp [Tensor.positiveWordTensor, Tensor.positiveWordFamily,
        matrixMultiplicationTensorFamily, matrixMultiplicationFamily,
        Tensor.LegModuleFamily.of, positiveWordProduct]
      exact Isomorphic.refl (K := K)
        (matrixMultiplication (K := K) (m q) (n q) (p q))
  | succ r ih =>
      change Isomorphic
        (Tensor.external
          (Tensor.positiveWordTensor
            (matrixMultiplicationFamily (K := K) m n p)
            (matrixMultiplicationTensorFamily (K := K) m n p) r q.1)
          (matrixMultiplication (K := K) (m q.2) (n q.2) (p q.2)))
        _
      rw [positiveWordProduct_succ m r q, positiveWordProduct_succ n r q,
        positiveWordProduct_succ p r q]
      exact
        (Isomorphic.external (ih q.1)
          (Isomorphic.refl (K := K)
            (matrixMultiplication (K := K) (m q.2) (n q.2) (p q.2)))).trans
          (matrixMultiplication_external
            (positiveWordProduct m r q.1)
            (positiveWordProduct n r q.1)
            (positiveWordProduct p r q.1)
            (m q.2) (n q.2) (p q.2))

/-- All word tensors of one multiplicity type are simultaneously isomorphic to copies of one
rectangular matrix-multiplication tensor. -/
theorem indexedDirectSum_positiveType_matrixMultiplication
    (m n p : I → ℕ) (r : ℕ) (a : I → ℕ) :
    Isomorphic
      (Tensor.indexedDirectSum
        (V := Tensor.PositiveTypeFamily (K := K)
          (matrixMultiplicationFamily (K := K) m n p) r a)
        (fun q : Tensor.positiveTypeClass I r a ↦
          Tensor.positiveWordTensor
            (matrixMultiplicationFamily (K := K) m n p)
            (matrixMultiplicationTensorFamily (K := K) m n p) r q.1))
      (Tensor.indexedDirectSum
        (fun _q : Tensor.positiveTypeClass I r a ↦
          matrixMultiplication (K := K)
            (∏ i, m i ^ a i) (∏ i, n i ^ a i) (∏ i, p i ^ a i))) := by
  apply Isomorphic.indexedDirectSum
  intro q
  have h := positiveWordTensor_matrixMultiplication (K := K) m n p r q.1
  rw [positiveWordProduct_eq_prod_pow (a := a) m q.2,
    positiveWordProduct_eq_prod_pow (a := a) n q.2,
    positiveWordProduct_eq_prod_pow (a := a) p q.2] at h
  exact h

end Tensor.Isomorphic

namespace Tensor.Restricts

/-- A positive power of a finite direct sum of matrix-multiplication tensors restricts to the
independent copies belonging to any prescribed multiplicity type.  Every retained copy has the
same three product dimensions. -/
theorem iteratedExternal_matrixMultiplicationDirectSum_type
    (m n p : I → ℕ) (r : ℕ) (a : I → ℕ) :
    Restricts
      (Tensor.iteratedExternal
        (Tensor.indexedDirectSumFamily (matrixMultiplicationFamily (K := K) m n p))
        (Tensor.indexedDirectSum
          (matrixMultiplicationTensorFamily (K := K) m n p)) r)
      (Tensor.indexedDirectSum
        (fun _q : Tensor.positiveTypeClass I r a ↦
          matrixMultiplication (K := K)
            (∏ i, m i ^ a i) (∏ i, n i ^ a i) (∏ i, p i ^ a i))) := by
  exact
    (Restricts.iteratedExternal_indexedDirectSum_type
      (matrixMultiplicationFamily (K := K) m n p)
      (matrixMultiplicationTensorFamily (K := K) m n p) r a).trans
      (Isomorphic.indexedDirectSum_positiveType_matrixMultiplication
        (K := K) m n p r a).restricts

end Tensor.Restricts

namespace Tensor.RankLE

/-- An optimized rank certificate for a canonical positive power restricts to all independent
matrix-multiplication copies in any prescribed multiplicity type. -/
theorem matrixMultiplicationDirectSum_type_of_power
    {r : ℕ} (m n p : I → ℕ) (s : ℕ) (a : I → ℕ)
    (h : RankLE r
      (Tensor.power
        (Tensor.indexedDirectSum
          (matrixMultiplicationTensorFamily (K := K) m n p)) (s + 1))) :
    RankLE r
      (Tensor.indexedDirectSum
        (fun _q : Tensor.positiveTypeClass I s a ↦
          matrixMultiplication (K := K)
            (∏ i, m i ^ a i) (∏ i, n i ^ a i) (∏ i, p i ^ a i))) := by
  have hiter : RankLE r
      (Tensor.iteratedExternal
        (Tensor.indexedDirectSumFamily
          (matrixMultiplicationFamily (K := K) m n p))
        (Tensor.indexedDirectSum
          (matrixMultiplicationTensorFamily (K := K) m n p)) s) :=
    Tensor.RankLE.iteratedExternal_of_power
      (A := Tensor.indexedDirectSumFamily
        (matrixMultiplicationFamily (K := K) m n p))
      (T := Tensor.indexedDirectSum
        (matrixMultiplicationTensorFamily (K := K) m n p)) h
  exact hiter.of_restricts
    (Tensor.Restricts.iteratedExternal_matrixMultiplicationDirectSum_type
      (K := K) m n p s a)

/-- Simultaneously cycle every matrix-multiplication constituent of an indexed direct sum
without changing an optimized rank bound for the whole sum. -/
theorem matrixMultiplication_indexedDirectSum_cycle
    {r : ℕ} {m n p : I → ℕ}
    (h : RankLE r
      (Tensor.indexedDirectSum
        (fun i => matrixMultiplication (K := K) (m i) (n i) (p i)))) :
    RankLE r
      (Tensor.indexedDirectSum
        (fun i => matrixMultiplication (K := K) (p i) (m i) (n i))) := by
  have hperm := h.permute_indexedDirectSum cycle
  exact (RankLE.isomorphic
    (Tensor.Isomorphic.indexedDirectSum fun i =>
      Tensor.Isomorphic.matrixMultiplication_cycle
        (K := K) (m i) (n i) (p i))).mp hperm

end Tensor.RankLE

/-- The index type of the retained identical copies has exactly the expected multinomial size. -/
theorem fintypeCard_positiveTypeClass_eq_multinomial (r : ℕ) (a : I → ℕ)
    (ha : a ∈ WordType.types I (r + 1)) :
    Fintype.card (Tensor.positiveTypeClass I r a) =
      Nat.multinomial Finset.univ a := by
  rw [Fintype.card_coe]
  exact Tensor.card_positiveTypeClass_eq_multinomial (I := I) r a ha

end AlgebraicComplexity
