import AlgebraicComplexity.MatrixMultiplication.Core
import AlgebraicComplexity.MatrixMultiplication.ExternalProduct
import AlgebraicComplexity.Tensor.Rank

/-!
# Matrix-multiplication tensors

The tensor `matrixMultiplication K m n p` is the coordinate tensor
`∑ i j k, xᵢⱼ ⊗ yⱼₖ ⊗ zₖᵢ`.  Its three spaces are kept distinct in the type.
-/

namespace AlgebraicComplexity

open Tensor

universe u

section

variable {K : Type u} [CommSemiring K]

/-- The defining expansion gives the elementary rank bound `m*n*p`. -/
theorem matrixMultiplication_rankLE (m n p : ℕ) :
    RankLE (m * n * p) (matrixMultiplication (K := K) m n p) := by
  simpa [matrixMultiplication, Nat.mul_assoc] using
    RankLE.finset_sum_pure (K := K) (V := MMSpace K m n p)
      (Finset.univ : Finset (MMTriple m n p))
      (mmTermOfTriple (K := K) m n p)

/-- Compatibility equations characterizing the support of a matrix-multiplication tensor. -/
abbrev MMCompatible {m n p : ℕ} (a : ∀ c, MMIndex m n p c) : Prop :=
  (a .X).2 = (a .Y).1 ∧ (a .Y).2 = (a .Z).1 ∧ (a .Z).2 = (a .X).1

instance {m n p : ℕ} (a : ∀ c, MMIndex m n p c) :
    Decidable (MMCompatible a) :=
  inferInstance

/-- Coordinate support formula for the matrix-multiplication tensor. -/
@[simp] theorem standardCoordinateEquiv_matrixMultiplication (m n p : ℕ)
    (a : ∀ c, MMIndex m n p c) :
    standardCoordinateEquiv (K := K) (κ := MMIndex m n p)
        (matrixMultiplication (K := K) m n p) a =
      if MMCompatible a then 1 else 0 := by
  rcases hX : a .X with ⟨i, j⟩
  rcases hY : a .Y with ⟨j', k⟩
  rcases hZ : a .Z with ⟨k', i'⟩
  simp [matrixMultiplication, mmTermOfTriple, mmTerm, MMCompatible,
    hX, hY, hZ, Fintype.sum_prod_type, prod_leg, Pi.single_apply,
    ite_and, eq_comm]
  by_cases hj : j = j' <;> by_cases hk : k = k' <;> by_cases hi : i = i' <;>
    simp [hj, hk, hi]

end

section Cyclic

variable {K : Type u} [CommSemiring K]

/-- Rotate a matrix-multiplication summation triple `(i,j,k)` to `(k,i,j)`. -/
def mmTripleCycleEquiv (m n p : ℕ) : MMTriple m n p ≃ MMTriple p m n where
  toFun a := (a.2.2, a.1, a.2.1)
  invFun a := (a.2.1, a.2.2, a.1)
  left_inv a := by rcases a with ⟨i, j, k⟩; rfl
  right_inv a := by rcases a with ⟨k, i, j⟩; rfl

@[simp] theorem mmTripleCycleEquiv_apply (m n p : ℕ)
    (i : Fin m) (j : Fin n) (k : Fin p) :
    mmTripleCycleEquiv m n p (i, j, k) = (k, i, j) := rfl

/-- Retype each cyclically permuted leg as the corresponding rotated matrix space. -/
def mmCycleLegEquiv (m n p : ℕ) (c : Leg) :
    MMSpace K m n p (cycle.symm c) ≃ₗ[K] MMSpace K p m n c := by
  cases c <;> exact LinearEquiv.refl K _

/-- The canonical cyclic equivalence `⟨m,n,p⟩ ≃ ⟨p,m,n⟩` on ambient tensor spaces. -/
noncomputable def mmCycleEquiv (m n p : ℕ) :
    Tensor3 K (MMSpace K m n p) ≃ₗ[K] Tensor3 K (MMSpace K p m n) :=
  (permute cycle).trans (PiTensorProduct.congr (mmCycleLegEquiv (K := K) m n p))

/-- Cyclically permuting a defining matrix-multiplication term rotates its dimensions. -/
@[simp] theorem mmCycleEquiv_mmTerm (m n p : ℕ)
    (i : Fin m) (j : Fin n) (k : Fin p) :
    mmCycleEquiv (K := K) m n p
        (pure (K := K) (mmTerm (K := K) m n p i j k)) =
      pure (K := K) (mmTerm (K := K) p m n k i j) := by
  simp only [mmCycleEquiv, LinearEquiv.trans_apply, permute_pure,
    PiTensorProduct.congr_tprod]
  congr 1
  funext c
  cases c <;> rfl

@[simp] theorem mmCycleEquiv_mmTermOfTriple (m n p : ℕ) (a : MMTriple m n p) :
    mmCycleEquiv (K := K) m n p
        (pure (K := K) (mmTermOfTriple (K := K) m n p a)) =
      pure (K := K)
        (mmTermOfTriple (K := K) p m n (mmTripleCycleEquiv m n p a)) := by
  rcases a with ⟨i, j, k⟩
  exact mmCycleEquiv_mmTerm m n p i j k

/-- Matrix-multiplication tensors are invariant under cyclic rotation of the three roles. -/
theorem mmCycleEquiv_matrixMultiplication (m n p : ℕ) :
    mmCycleEquiv (K := K) m n p (matrixMultiplication (K := K) m n p) =
      matrixMultiplication (K := K) p m n := by
  unfold matrixMultiplication
  rw [map_sum]
  simp_rw [mmCycleEquiv_mmTermOfTriple]
  exact Equiv.sum_comp (mmTripleCycleEquiv m n p)
    (fun a : MMTriple p m n ↦
      pure (K := K) (mmTermOfTriple (K := K) p m n a))

/-- Swap the first two summation indices. -/
def mmTripleSwapEquiv (m n p : ℕ) : MMTriple m n p ≃ MMTriple n m p where
  toFun a := (a.2.1, a.1, a.2.2)
  invFun a := (a.2.1, a.1, a.2.2)
  left_inv a := by rcases a with ⟨i, j, k⟩; rfl
  right_inv a := by rcases a with ⟨j, i, k⟩; rfl

@[simp] theorem mmTripleSwapEquiv_apply (m n p : ℕ)
    (i : Fin m) (j : Fin n) (k : Fin p) :
    mmTripleSwapEquiv m n p (i, j, k) = (j, i, k) := rfl

/-- Retype the `XZY` leg permutation by reversing each matrix-coordinate pair. -/
noncomputable def mmSwapYZLegEquiv (m n p : ℕ) (c : Leg) :
    MMSpace K m n p (xzy.symm c) ≃ₗ[K] MMSpace K n m p c := by
  cases c with
  | X => exact LinearEquiv.funCongrLeft K K (Equiv.prodComm (Fin m) (Fin n)).symm
  | Y => exact LinearEquiv.funCongrLeft K K (Equiv.prodComm (Fin p) (Fin m)).symm
  | Z => exact LinearEquiv.funCongrLeft K K (Equiv.prodComm (Fin n) (Fin p)).symm

/-- Canonical equivalence induced by swapping the `Y` and `Z` tensor legs. -/
noncomputable def mmSwapYZEquiv (m n p : ℕ) :
    Tensor3 K (MMSpace K m n p) ≃ₗ[K] Tensor3 K (MMSpace K n m p) :=
  (permute xzy).trans (PiTensorProduct.congr (mmSwapYZLegEquiv (K := K) m n p))

@[simp] theorem mmSwapYZEquiv_mmTerm (m n p : ℕ)
    (i : Fin m) (j : Fin n) (k : Fin p) :
    mmSwapYZEquiv (K := K) m n p
        (pure (K := K) (mmTerm (K := K) m n p i j k)) =
      pure (K := K) (mmTerm (K := K) n m p j i k) := by
  simp only [mmSwapYZEquiv, LinearEquiv.trans_apply, permute_pure,
    PiTensorProduct.congr_tprod]
  congr 1
  funext c
  cases c with
  | X =>
      change LinearEquiv.funCongrLeft K K (Equiv.prodComm (Fin m) (Fin n)).symm
        (Pi.single (i, j) 1) = Pi.single (j, i) 1
      exact funCongrLeft_symm_single (K := K)
        (Equiv.prodComm (Fin m) (Fin n)) (i, j) 1
  | Y =>
      change LinearEquiv.funCongrLeft K K (Equiv.prodComm (Fin p) (Fin m)).symm
        (Pi.single (k, i) 1) = Pi.single (i, k) 1
      exact funCongrLeft_symm_single (K := K)
        (Equiv.prodComm (Fin p) (Fin m)) (k, i) 1
  | Z =>
      change LinearEquiv.funCongrLeft K K (Equiv.prodComm (Fin n) (Fin p)).symm
        (Pi.single (j, k) 1) = Pi.single (k, j) 1
      exact funCongrLeft_symm_single (K := K)
        (Equiv.prodComm (Fin n) (Fin p)) (j, k) 1

@[simp] theorem mmSwapYZEquiv_mmTermOfTriple (m n p : ℕ) (a : MMTriple m n p) :
    mmSwapYZEquiv (K := K) m n p
        (pure (K := K) (mmTermOfTriple (K := K) m n p a)) =
      pure (K := K)
        (mmTermOfTriple (K := K) n m p (mmTripleSwapEquiv m n p a)) := by
  rcases a with ⟨i, j, k⟩
  exact mmSwapYZEquiv_mmTerm m n p i j k

/-- Swapping two tensor roles carries `⟨m,n,p⟩` to the transposed tensor `⟨n,m,p⟩`. -/
theorem mmSwapYZEquiv_matrixMultiplication (m n p : ℕ) :
    mmSwapYZEquiv (K := K) m n p (matrixMultiplication (K := K) m n p) =
      matrixMultiplication (K := K) n m p := by
  unfold matrixMultiplication
  rw [map_sum]
  simp_rw [mmSwapYZEquiv_mmTermOfTriple]
  exact Equiv.sum_comp (mmTripleSwapEquiv m n p)
    (fun a : MMTriple n m p ↦
      pure (K := K) (mmTermOfTriple (K := K) n m p a))

end Cyclic

section DimensionRestriction

variable {K : Type u} [CommSemiring K]

/-- Include the indices of a smaller matrix product into those of a larger one. -/
def mmIndexInclusion {m n p M N P : ℕ}
    (hm : m ≤ M) (hn : n ≤ N) (hp : p ≤ P) :
    ∀ c, MMIndex m n p c → MMIndex M N P c
  | .X => fun a ↦ (Fin.castLE hm a.1, Fin.castLE hn a.2)
  | .Y => fun a ↦ (Fin.castLE hn a.1, Fin.castLE hp a.2)
  | .Z => fun a ↦ (Fin.castLE hp a.1, Fin.castLE hm a.2)

/-- Restrict coordinate functions from a larger matrix space to embedded smaller indices. -/
def mmDimensionMap {m n p M N P : ℕ}
    (hm : m ≤ M) (hn : n ≤ N) (hp : p ≤ P) :
    ∀ c, MMSpace K M N P c →ₗ[K] MMSpace K m n p c :=
  fun c ↦ LinearMap.funLeft K K (mmIndexInclusion hm hn hp c)

/-- Applying the coordinate restriction to a larger matrix tensor gives the smaller one. -/
theorem map_mmDimensionMap {m n p M N P : ℕ}
    (hm : m ≤ M) (hn : n ≤ N) (hp : p ≤ P) :
    map (mmDimensionMap (K := K) hm hn hp)
        (matrixMultiplication (K := K) M N P) =
      matrixMultiplication (K := K) m n p := by
  apply standardCoordinate_ext
  intro a
  unfold mmDimensionMap
  rw [standardCoordinateEquiv_map_funLeft]
  simp only [standardCoordinateEquiv_matrixMultiplication]
  simp [MMCompatible, mmIndexInclusion]

/-- Matrix-multiplication tensors restrict monotonically in all three dimensions. -/
theorem matrixMultiplication_restricts {m n p M N P : ℕ}
    (hm : m ≤ M) (hn : n ≤ N) (hp : p ≤ P) :
    Restricts (matrixMultiplication (K := K) M N P)
      (matrixMultiplication (K := K) m n p) := by
  exact ⟨mmDimensionMap (K := K) hm hn hp, map_mmDimensionMap hm hn hp⟩

end DimensionRestriction

section Products

variable {K : Type u} [CommSemiring K]

/-- Legwise map multiplying three matrix-multiplication spaces, with the first two factors
parenthesized together. -/
noncomputable def mmExternal3Map
    (m n p m' n' p' m'' n'' p'' : ℕ) : ∀ c,
    TensorProduct K
        (TensorProduct K (MMSpace K m n p c) (MMSpace K m' n' p' c))
        (MMSpace K m'' n'' p'' c) →ₗ[K]
      MMSpace K ((m * m') * m'') ((n * n') * n'') ((p * p') * p'') c :=
  fun c ↦
    (mmProductLegEquiv (K := K)
      (m * m') (n * n') (p * p') m'' n'' p'' c).toLinearMap ∘ₗ
      TensorProduct.map
        (mmProductLegEquiv (K := K) m n p m' n' p' c).toLinearMap
        (LinearMap.id (R := K) (M := MMSpace K m'' n'' p'' c))

/-- Three matrix-multiplication tensors multiply under the factorwise external product. -/
theorem map_mmExternal3Map_matrixMultiplication
    (m n p m' n' p' m'' n'' p'' : ℕ) :
    map (mmExternal3Map (K := K) m n p m' n' p' m'' n'' p'')
        (external
          (external (matrixMultiplication (K := K) m n p)
            (matrixMultiplication (K := K) m' n' p'))
          (matrixMultiplication (K := K) m'' n'' p'')) =
      matrixMultiplication (K := K)
        ((m * m') * m'') ((n * n') * n'') ((p * p') * p'') := by
  unfold mmExternal3Map
  rw [map_comp]
  simp only [LinearMap.comp_apply]
  rw [map_external]
  simp only [map_id, LinearMap.id_apply]
  rw [show map
      (fun c ↦ (mmProductLegEquiv (K := K) m n p m' n' p' c).toLinearMap)
      (external (matrixMultiplication (K := K) m n p)
        (matrixMultiplication (K := K) m' n' p')) =
      matrixMultiplication (K := K) (m * m') (n * n') (p * p') by
        simpa [mmExternalEquiv, PiTensorProduct.congr] using
          mmExternalEquiv_matrixMultiplication (K := K) m n p m' n' p']
  simpa [mmExternalEquiv, PiTensorProduct.congr] using
    mmExternalEquiv_matrixMultiplication (K := K)
      (m * m') (n * n') (p * p') m'' n'' p''

namespace Tensor.RankLE

/-- Cyclically rotating the three roles of a matrix-multiplication tensor preserves every
constructive rank upper bound. -/
theorem matrixMultiplication_cycle
    {m n p r : ℕ}
    (h : RankLE r (matrixMultiplication (K := K) m n p)) :
    RankLE r (matrixMultiplication (K := K) p m n) := by
  have h' := (h.permute cycle).map
    (fun c ↦ (mmCycleLegEquiv (K := K) m n p c).toLinearMap)
  have heq :
      Tensor.map (fun c ↦ (mmCycleLegEquiv (K := K) m n p c).toLinearMap)
          (Tensor.permute cycle (matrixMultiplication (K := K) m n p)) =
        mmCycleEquiv (K := K) m n p
          (matrixMultiplication (K := K) m n p) := by
    rfl
  rw [heq, mmCycleEquiv_matrixMultiplication] at h'
  exact h'

/-- Rank certificates for matrix-multiplication tensors multiply after the canonical reindexing
of an external tensor product. -/
theorem matrixMultiplication_mul
    {m n p m' n' p' r s : ℕ}
    (h : RankLE r (matrixMultiplication (K := K) m n p))
    (h' : RankLE s (matrixMultiplication (K := K) m' n' p')) :
    RankLE (r * s)
      (matrixMultiplication (K := K) (m * m') (n * n') (p * p')) := by
  have hproduct := (h.external h').map
    (fun c ↦ (mmProductLegEquiv (K := K) m n p m' n' p' c).toLinearMap)
  rw [← mmExternalEquiv_matrixMultiplication]
  simpa [mmExternalEquiv, PiTensorProduct.congr] using hproduct

/-- Iterating a square matrix-multiplication rank certificate gives the expected power bound. -/
theorem matrixMultiplication_pow {n r : ℕ}
    (h : RankLE r (matrixMultiplication (K := K) n n n)) (k : ℕ) :
    RankLE (r ^ k)
      (matrixMultiplication (K := K) (n ^ k) (n ^ k) (n ^ k)) := by
  induction k with
  | zero =>
      change RankLE 1 (matrixMultiplication (K := K) 1 1 1)
      simpa using matrixMultiplication_rankLE (K := K) 1 1 1
  | succ k ih =>
      rw [pow_succ]
      exact ih.matrixMultiplication_mul h

end Tensor.RankLE

end Products

end AlgebraicComplexity
