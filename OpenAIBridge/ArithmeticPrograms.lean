/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.RankComplexityConverse
import AlgebraicComplexity.MatrixMultiplication.RectangularExponent
import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Exponent
import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.LowerBound

/-!
# From the vendored arithmetic-program model to tensor rank

The vendored development in `ThirdParty/OAI/` states its theorems in an arithmetic model: a
`Program` is a list of gates (constants, inputs, `+`, `−`, `×` on earlier registers), a
`MatrixAlgorithm F a b c` is a program with designated output registers, and
`Arithmetic.omega F`, `Arithmetic.rectangularOmega F k` are the infima of the exponents `τ` for
which correct programs of cost `O(n^(τ+ε))` exist.

This repository's exponents are defined by tensor rank.  The two are compared here in the
direction needed to import upper bounds:

```text
omega F ≤ Arithmetic.omega F,        rectangularOmega F k ≤ Arithmetic.rectangularOmega F k
```

over every **infinite** field `F`.  The argument is Strassen's, as proved in
`AlgebraicComplexity/MatrixMultiplication/RankComplexityConverse.lean` for this repository's own
straight-line programs: a program with `M` multiplication gates that computes a bilinear map
gives a bilinear algorithm of length at most `2M`.  All that is new here is a translation of the
vendored `Program` into a `Straightline` program with the same values and the same number of
multiplication gates:

* the register context after `r` gates is `ProgramContext Input r`, an `r`-fold `Option` over the
  inputs, with the newest register at `none` — the same convention as the vendored
  `Program.eval`, which puts the newest register at index `0`;
* a gate becomes a one-gate circuit over that context (`gateCircuit`), with subtraction written
  as addition of a `(−1)`-multiple, which is a scalar multiplication and costs no
  multiplication gate;
* a program becomes a nest of `letBind`s around a continuation (`toStraightline`).

The comparison uses nothing about the vendored proofs: it is a statement about the two models.

## Main results

* `toStraightline_eval`, `mulOps_toStraightline`: the translation preserves values and
  multiplication counts.
* `rankLE_matrixMultiplication_of_matrixAlgorithm`: a correct `MatrixAlgorithm F a b c` of cost
  `c₀` gives `RankLE (2 · c₀) ⟨a,b,c⟩`.
* `omega_le_arithmeticOmega`, `rectangularOmega_le_arithmeticRectangularOmega`: the comparison
  of exponents.
-/

namespace AlgebraicComplexity.OpenAIBridge

open Tensor
open OAI.MatrixMultiplication.Arithmetic (Gate Program MatrixAlgorithm MatrixInput)

universe u

/-! ### Register contexts -/

/-- The index type of the values available after `r` gates: the inputs, extended `r` times by
one fresh register. -/
def ProgramContext (Input : Type) : ℕ → Type
  | 0 => Input
  | r + 1 => Option (ProgramContext Input r)

namespace ProgramContext

variable {Input : Type}

/-- An input, as an index of the context after `r` gates. -/
def ofInput : (r : ℕ) → Input → ProgramContext Input r
  | 0, i => i
  | r + 1, i => some (ofInput r i)

/-- A register, as an index of the context after `r` gates.  Register `0` is the newest. -/
def ofRegister : (r : ℕ) → Fin r → ProgramContext Input r
  | 0, j => j.elim0
  | r + 1, j => Fin.cases (motive := fun _ ↦ Option (ProgramContext Input r)) none
      (fun j' ↦ some (ofRegister r j')) j

end ProgramContext

section Translation

variable {F : Type u} {Input : Type}

/-- The one-gate circuit of a vendored gate, over the context of the registers before it. -/
def gateCircuit [Neg F] [One F] {r : ℕ} :
    Gate F Input (Fin r) → Circuit F (ProgramContext Input r)
  | .constant z => .const z
  | .input i => .input (ProgramContext.ofInput r i)
  | .add i j => .add (.input (ProgramContext.ofRegister r i))
      (.input (ProgramContext.ofRegister r j))
  | .sub i j => .add (.input (ProgramContext.ofRegister r i))
      (.smul (-1) (.input (ProgramContext.ofRegister r j)))
  | .mul i j => .mul (.input (ProgramContext.ofRegister r i))
      (.input (ProgramContext.ofRegister r j))

/-- Whether a gate is a multiplication gate, as a number. -/
def gateMulCount {Register : Type} : Gate F Input Register → ℕ
  | .mul _ _ => 1
  | _ => 0

/-- The number of multiplication gates of a vendored program. -/
def programMulCount : {r : ℕ} → Program F Input r → ℕ
  | 0, .nil => 0
  | _ + 1, .step p g => programMulCount p + gateMulCount g

/-- Multiplication gates are among the gates that cost one. -/
theorem programMulCount_le_cost : ∀ {r : ℕ} (p : Program F Input r), programMulCount p ≤ p.cost
  | 0, .nil => le_rfl
  | _ + 1, .step p g => by
    have h := programMulCount_le_cost p
    have hg : gateMulCount g ≤ g.cost := by cases g <;> simp [gateMulCount, Gate.cost]
    simp only [programMulCount, Program.cost]
    omega

/-- The translation of a vendored program, given what to do with its registers: one `letBind`
per gate, the first gate outermost. -/
def toStraightline [Neg F] [One F] {μ : Type} :
    {r : ℕ} → Program F Input r → Straightline F μ (ProgramContext Input r) →
      Straightline F μ Input
  | 0, .nil, k => k
  | _ + 1, .step p g, k => toStraightline p (.letBind (gateCircuit g) k)

theorem toStraightline_nil [Neg F] [One F] {μ : Type}
    (k : Straightline F μ (ProgramContext Input 0)) :
    toStraightline (Program.nil : Program F Input 0) k = k := rfl

theorem toStraightline_step [Neg F] [One F] {μ : Type} {r : ℕ} (p : Program F Input r)
    (g : Gate F Input (Fin r)) (k : Straightline F μ (ProgramContext Input (r + 1))) :
    toStraightline (p.step g) k = toStraightline p (.letBind (gateCircuit g) k) := rfl

theorem programMulCount_step {r : ℕ} (p : Program F Input r) (g : Gate F Input (Fin r)) :
    programMulCount (p.step g) = programMulCount p + gateMulCount g := rfl

/-- The circuit of a gate has one multiplication gate exactly when the gate is one. -/
theorem mulOps_gateCircuit [Neg F] [One F] {r : ℕ} (g : Gate F Input (Fin r)) :
    (gateCircuit g).mulOps = gateMulCount g := by
  cases g <;> rfl

/-- The multiplication gates of the translation are those of the program and those of the
continuation. -/
theorem mulOps_toStraightline [Neg F] [One F] {μ : Type} [Fintype μ] {r : ℕ}
    (p : Program F Input r) :
    ∀ k : Straightline F μ (ProgramContext Input r),
      (toStraightline p k).mulOps = programMulCount p + k.mulOps := by
  induction p with
  | nil =>
    intro k
    rw [toStraightline_nil]
    exact (Nat.zero_add _).symm
  | step p g ih =>
    intro k
    have h : (Straightline.letBind (gateCircuit g) k).mulOps =
        (gateCircuit g).mulOps + k.mulOps := Straightline.mulOps_letBind _ _
    rw [toStraightline_step, ih, h, mulOps_gateCircuit, programMulCount_step, Nat.add_assoc]

variable [Field F]

/-- The values of a program's context: its inputs, and the values of its registers. -/
def programEnv : {r : ℕ} → Program F Input r → (Input → F) → ProgramContext Input r → F
  | 0, .nil, x => x
  | _ + 1, .step p g, x => extendEnv (g.eval x (p.eval x)) (programEnv p x)

theorem programEnv_step {r : ℕ} (p : Program F Input r) (g : Gate F Input (Fin r))
    (x : Input → F) :
    programEnv (p.step g) x = extendEnv (g.eval x (p.eval x)) (programEnv p x) := rfl

/-- The context value of an input is the input. -/
theorem programEnv_ofInput {r : ℕ} (p : Program F Input r) (x : Input → F) (i : Input) :
    programEnv p x (ProgramContext.ofInput r i) = x i := by
  induction p with
  | nil => rfl
  | step p g ih => exact ih

/-- The context value of a register is the value the vendored evaluation assigns to it. -/
theorem programEnv_ofRegister {r : ℕ} (p : Program F Input r) (x : Input → F) (j : Fin r) :
    programEnv p x (ProgramContext.ofRegister r j) = p.eval x j := by
  induction p with
  | nil => exact j.elim0
  | step p g ih =>
    induction j using Fin.cases with
    | zero => rfl
    | succ j' => exact ih j'

/-- The circuit of a gate evaluates, in the context of the earlier registers, to the gate. -/
theorem eval_gateCircuit {r : ℕ} (p : Program F Input r) (x : Input → F)
    (g : Gate F Input (Fin r)) :
    (gateCircuit g).eval (programEnv p x) = g.eval x (p.eval x) := by
  cases g with
  | constant z => rfl
  | input i => exact programEnv_ofInput p x i
  | add i j =>
    show programEnv p x _ + programEnv p x _ = _
    rw [programEnv_ofRegister, programEnv_ofRegister]
    rfl
  | sub i j =>
    show programEnv p x _ + -1 * programEnv p x _ = _
    rw [programEnv_ofRegister, programEnv_ofRegister]
    show p.eval x i + -1 * p.eval x j = p.eval x i - p.eval x j
    ring
  | mul i j =>
    show programEnv p x _ * programEnv p x _ = _
    rw [programEnv_ofRegister, programEnv_ofRegister]
    rfl

/-- The translation evaluates to its continuation in the context of the program. -/
theorem toStraightline_eval {μ : Type} {r : ℕ} (p : Program F Input r) :
    ∀ (k : Straightline F μ (ProgramContext Input r)) (x : Input → F) (m : μ),
      (toStraightline p k).eval x m = k.eval (programEnv p x) m := by
  induction p with
  | nil => intro k x m; rfl
  | step p g ih =>
    intro k x m
    have h : (Straightline.letBind (gateCircuit g) k).eval (programEnv p x) m =
        k.eval (extendEnv ((gateCircuit g).eval (programEnv p x)) (programEnv p x)) m :=
      Straightline.eval_letBind _ _ _ _
    rw [toStraightline_step, ih, h, eval_gateCircuit]
    rfl

end Translation

/-! ### Rank from a correct matrix algorithm -/

section Rank

variable {F : Type u} [Field F] [Infinite F]

/-- **A correct arithmetic program for matrix multiplication bounds the rank of the
matrix-multiplication tensor by twice its cost.** -/
theorem rankLE_matrixMultiplication_of_matrixAlgorithm {a b c : ℕ}
    (P : MatrixAlgorithm F a b c) (hP : P.Correct) :
    RankLE (2 * P.cost) (matrixMultiplication (K := F) a b c) := by
  let prog : Straightline F (Fin c × Fin a) (MatrixInput a b c) :=
    toStraightline P.program
      (.ret fun z ↦ .input (ProgramContext.ofRegister P.registers (P.output z.2 z.1)))
  have heval : ∀ (x : Fin a × Fin b → F) (y : Fin b × Fin c → F) (z : Fin c × Fin a),
      prog.eval (Sum.elim x y) z = matrixProductMap (K := F) a b c x y z := by
    intro x y z
    have hin : OAI.MatrixMultiplication.Arithmetic.matrixInputs
        (Matrix.of fun i j ↦ x (i, j)) (Matrix.of fun j k ↦ y (j, k)) = Sum.elim x y := by
      funext s
      rcases s with ⟨i, j⟩ | ⟨j, k⟩ <;> rfl
    have hcorrect := congrFun (congrFun
      (hP (Matrix.of fun i j ↦ x (i, j)) (Matrix.of fun j k ↦ y (j, k))) z.2) z.1
    simp only [MatrixAlgorithm.eval, hin, Matrix.mul_apply, Matrix.of_apply] at hcorrect
    simp only [prog, toStraightline_eval, Straightline.eval_ret, Circuit.eval_input,
      programEnv_ofRegister, matrixProductMap_apply]
    exact hcorrect
  have hmul : prog.mulOps ≤ P.cost := by
    simp only [prog, mulOps_toStraightline, Straightline.mulOps_ret, Circuit.mulOps_input,
      Finset.sum_const_zero, add_zero]
    exact programMulCount_le_cost P.program
  exact (rankLE_matrixMultiplication_of_straightline prog heval).mono
    (Nat.mul_le_mul_left 2 hmul)

/-- **The rank-growth exponent is at most the arithmetic exponent** of the vendored model, over
every infinite field. -/
theorem omega_le_arithmeticOmega (F : Type u) [Field F] [Infinite F] :
    omega F ≤ OAI.MatrixMultiplication.Arithmetic.omega F := by
  have hadm := (OAI.MatrixMultiplication.Arithmetic.admissibleExponent_iff_omega_le
    (F := F)).mpr le_rfl
  have h2 := OAI.MatrixMultiplication.Arithmetic.admissibleExponent_two_le hadm
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨C, hC, hbound⟩ := hadm ε hε
  refine omega_le F ⟨by linarith, 2 * C, by positivity, fun n hn ↦ ?_⟩
  obtain ⟨P, hP, hcost⟩ := hbound n hn
  have hrank : squareMatrixRankSequence F n ≤ 2 * P.cost :=
    rank_le_iff.mpr (rankLE_matrixMultiplication_of_matrixAlgorithm P hP)
  calc (squareMatrixRankSequence F n : ℝ) ≤ ((2 * P.cost : ℕ) : ℝ) := by exact_mod_cast hrank
    _ = 2 * (P.cost : ℝ) := by push_cast; ring
    _ ≤ 2 * (C * (n : ℝ) ^ (OAI.MatrixMultiplication.Arithmetic.omega F + ε)) := by linarith
    _ = 2 * C * (n : ℝ) ^ (OAI.MatrixMultiplication.Arithmetic.omega F + ε) := by ring

/-- **The rank-based rectangular exponent is at most the arithmetic one** of the vendored model,
over every infinite field and for every aspect `k`. -/
theorem rectangularOmega_le_arithmeticRectangularOmega (F : Type u) [Field F] [Infinite F]
    (k : ℝ) :
    rectangularOmega F k ≤ OAI.MatrixMultiplication.Arithmetic.rectangularOmega F k := by
  have hadm := (OAI.MatrixMultiplication.Arithmetic.rectangularAdmissibleExponent_iff_omega_le
    (F := F) (k := k)).mpr le_rfl
  have h2 := OAI.MatrixMultiplication.Arithmetic.rectangularAdmissibleExponent_two_le hadm
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨C, hC, hbound⟩ := hadm ε hε
  refine rectangularOmega_le F ⟨by linarith, 2 * C, by positivity, fun n hn ↦ ?_⟩
  obtain ⟨P, hP, hcost⟩ := hbound n hn
  have hrank : rectangularMatrixRankSequence F k n ≤ 2 * P.cost :=
    rank_le_iff.mpr (rankLE_matrixMultiplication_of_matrixAlgorithm P hP)
  calc (rectangularMatrixRankSequence F k n : ℝ) ≤ ((2 * P.cost : ℕ) : ℝ) := by
        exact_mod_cast hrank
    _ = 2 * (P.cost : ℝ) := by push_cast; ring
    _ ≤ 2 * (C * (n : ℝ) ^
          (OAI.MatrixMultiplication.Arithmetic.rectangularOmega F k + ε)) := by linarith
    _ = 2 * C * (n : ℝ) ^
          (OAI.MatrixMultiplication.Arithmetic.rectangularOmega F k + ε) := by ring

end Rank

end AlgebraicComplexity.OpenAIBridge
