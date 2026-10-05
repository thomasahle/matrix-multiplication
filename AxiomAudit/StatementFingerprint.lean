/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Lean.Elab.Command
import Lean.Util.FoldConsts

/-!
# The `#assert_statement_fingerprint` command

`#assert_axioms` (in `AxiomAudit/Command.lean`) enforces *how* an audited theorem was proved.
This module enforces *what it says*.

`#assert_statement_fingerprint id "<hex>"` recomputes a structural hash of

* `id` itself — its type always, and its **value** when `id` is a definition rather than a
  theorem; and
* the **transitive definitional closure** of every project-local constant reached that way, each
  hashed by the same rule.

A proof term never enters: on a theorem the digest sees the statement only.  On a *definition* it
sees the body, which is what makes the command useful on statement *shapes* (`Frontier.OmegaBound`)
and on the definition of `omega` itself.

Elaboration fails unless the recomputed hash equals the committed one.  A committed hash line is
therefore a machine-checked assertion that a public statement still *means* what it meant when it
was reviewed: not only that the top-level `Prop` is textually the same, but that nothing in the
chain of definitions it is phrased in terms of has been quietly redefined.  `#statement_fingerprint
id` prints the current value so a deliberate change can be re-committed after review.

The intended division of labour: fingerprint the **shapes** (`omega`, `OmegaBound`), which are
record-independent, so that adding a sharper record never touches a committed hash; and use
`#assert_axioms` plus the strict-improvement CI check on the record itself.

## The boundary

Constants are classified by the root component of the module they were declared in.

* Roots in `projectRoots` are **unfolded**: their types and values enter the hash.
* Roots in `externalRoots` (the toolchain, Mathlib, and the other Lake dependencies) are an
  **opaque boundary**: such a constant enters the hash by *name only* and is not unfolded.
  A Mathlib refactor that preserves the names a statement mentions therefore does not disturb a
  committed hash, while a rename does.
* A constant from any *other* root is a hard error.  The classification is deliberately total:
  a new top-level project library must be added to `projectRoots` (or, if it is a new
  dependency, to `externalRoots`) before it can appear in an audited statement.  Silently
  treating an unrecognized root as opaque would be exactly the failure mode this command exists
  to prevent.

Constants declared in the module currently being elaborated have no module index yet and count as
project-local.

## What the hash deliberately ignores

Binder names, universe *parameter names* (they are replaced by their index in the declaration's
own `levelParams`, so `u` and `u_1` agree), `Expr.mdata`, the `theorem`/`lemma` keyword, docstrings,
attributes, and the entire proof term of the audited declaration and of every theorem in its
closure.  Definition *values* are hashed; theorem values are not, since a proof is exactly the
thing `#assert_axioms` is responsible for and a proof term is neither stable nor part of a
statement.

## Documented limits

1. **Inductive fields.** For an inductive type the hash covers its own type, its parameter and
   index counts, and its constructor *names* and *types* (the constructors are pushed onto the
   closure worklist).  It does not cover attributes such as `@[ext]`, nor which projections are
   `abbrev`-reducible.
2. **Binder info is significant.** Changing `[Field K]` to `(inst : Field K)` in a shape
   definition changes the hash even though the resulting `Prop` is the same up to definitional
   unfolding. This is a false alarm by design: such an edit changes how every client applies the
   statement and should be re-reviewed.
3. **Definitional, not semantic.** Two statements that are provably — even definitionally —
   equivalent but syntactically different have different hashes.  The command detects drift; it
   does not decide equivalence.
4. **Macro-scoped auxiliary names.** If a project constant in the closure is an auxiliary
   declaration whose *name* carries hygiene information (`…_@._hyg.123`), its name is hashed as
   written and can in principle shift when unrelated declarations in the same file are reordered.
   Top-level auxiliaries (`f.match_1`, `f._proof_2`) are not macro-scoped, so this has not been
   observed in practice; a spurious mismatch of this kind is diagnosable by re-running
   `#statement_fingerprint`.
5. **Toolchain scope.** The digest is FNV-1a over an encoding written here rather than over
   Lean's internal `Expr.hash`, so it does not move with the compiler's hashing internals.  It
   can still move across a toolchain upgrade that changes how a statement *elaborates* (a changed
   instance path, a new coercion) — which is a review-worthy event, not noise.
-/

namespace AxiomAudit.StatementFingerprint

open Lean Elab Command

/-! ## Module classification -/

/-- Root components of module names whose declarations are unfolded into a fingerprint. -/
def projectRoots : List Name :=
  [`AlgebraicComplexity, `AlgebraicComplexityClients, `MatrixMultiplication,
    `MatrixMultiplicationCertificate, `AxiomAudit, `AxiomAuditCertificate, `Frontier]

/-- Root components of module names forming the opaque external boundary: constants declared
there enter a fingerprint by name only. -/
def externalRoots : List Name :=
  [`Init, `Lean, `Std, `Batteries, `Mathlib, `Aesop, `Qq, `Cslib, `Plausible, `ProofWidgets,
    `ImportGraph, `LeanSearchClient, `Cli, `Lake]

/-- First component of a name (`Mathlib.Order.Basic ↦ Mathlib`). -/
def nameRoot : Name → Name
  | .anonymous => .anonymous
  | .str .anonymous s => .str .anonymous s
  | .num .anonymous i => .num .anonymous i
  | .str p _ => nameRoot p
  | .num p _ => nameRoot p

/-- Which side of the fingerprint boundary a constant lies on. -/
inductive Side where
  /-- Unfold: hash the constant's type, and its value when it is a definition. -/
  | project
  /-- Opaque: hash the constant's name only. -/
  | external
  /-- The declaring module's root is in neither list; a hard error. -/
  | unclassified (moduleName : Name)

/-- Classify a constant by the module it was declared in. -/
def classify (env : Environment) (n : Name) : Side :=
  match env.getModuleIdxFor? n with
  | none => .project
  | some idx =>
    match env.header.moduleNames[idx.toNat]? with
    | none => .project
    | some m =>
      let root := nameRoot m
      if projectRoots.contains root then .project
      else if externalRoots.contains root then .external
      else .unclassified m

/-! ## The digest

FNV-1a, 64 bit, over an explicit canonical encoding.  Both halves are written out here rather
than delegated to `Expr.hash` / `String.hash`, so that a committed hash is a function of this
module's source and the Lean declarations it reads, and of nothing else.
-/

/-- Version tag of the encoding scheme.  Bump it when the encoding below changes; every committed
hash must then be recomputed. -/
def schemeTag : String := "AxiomAudit.StatementFingerprint/1"

private def fnvPrime : UInt64 := 1099511628211
private def fnvOffset : UInt64 := 14695981039346656037

/-- Absorb bytes. -/
private def feedBytes (h : UInt64) (bs : ByteArray) : UInt64 :=
  ByteArray.foldl (fun h b => (h ^^^ b.toUInt64) * fnvPrime) h bs

/-- Absorb a string. -/
private def feed (h : UInt64) (s : String) : UInt64 :=
  feedBytes h s.toUTF8

/-- Absorb a tagged, length-prefixed string, so that adjacent variable-length fields cannot be
re-parsed into one another. -/
private def feedTok (h : UInt64) (tag : String) (s : String) : UInt64 :=
  feed (feed (feed h tag) (toString s.utf8ByteSize)) s

private def hexDigit (v : Nat) : Char :=
  if v < 10 then Char.ofNat (48 + v) else Char.ofNat (87 + v)

/-- Sixteen lowercase hex digits. -/
def hex16 (n : UInt64) : String :=
  let rec go (i : Nat) (v : UInt64) (acc : String) : String :=
    match i with
    | 0 => acc
    | i + 1 => go i (v / 16) (String.singleton (hexDigit (v % 16).toNat) ++ acc)
  go 16 n ""

private def binderCode : BinderInfo → String
  | .default => "d"
  | .implicit => "i"
  | .strictImplicit => "s"
  | .instImplicit => "n"

/-- Absorb a universe level.  Level *parameters* are encoded by their position in `lp`, the
declaration's own `levelParams`, so that renaming `u` to `u_1` is invisible. -/
private partial def feedLevel (lp : List Name) (h : UInt64) : Level → UInt64
  | .zero => feed h "Uz"
  | .succ l => feedLevel lp (feed h "Us") l
  | .max a b => feedLevel lp (feedLevel lp (feed h "Um") a) b
  | .imax a b => feedLevel lp (feedLevel lp (feed h "Ui") a) b
  | .param n =>
    match lp.findIdx? (· == n) with
    | some i => feed (feed h "Up") (toString i)
    | none => feedTok h "UP" n.toString
  | .mvar _ => feed h "U?"

/-- Absorb an expression.  Binder names and `mdata` are dropped; binder info is kept. -/
private partial def feedExpr (lp : List Name) (h : UInt64) : Expr → UInt64
  | .bvar i => feed (feed h "b") (toString i)
  | .fvar id => feedTok h "f" id.name.toString
  | .mvar id => feedTok h "m" id.name.toString
  | .sort l => feedLevel lp (feed h "s") l
  | .const n us => us.foldl (feedLevel lp) (feedTok h "c" n.toString)
  | .app fn a => feedExpr lp (feedExpr lp (feed h "a") fn) a
  | .lam _ t body bi => feedExpr lp (feedExpr lp (feed (feed h "l") (binderCode bi)) t) body
  | .forallE _ t body bi => feedExpr lp (feedExpr lp (feed (feed h "p") (binderCode bi)) t) body
  | .letE _ t v body _ => feedExpr lp (feedExpr lp (feedExpr lp (feed h "e") t) v) body
  | .lit (.natVal n) => feed (feed h "n") (toString n)
  | .lit (.strVal s) => feedTok h "t" s
  | .mdata _ e => feedExpr lp h e
  | .proj s i e => feedExpr lp (feed (feedTok h "j" s.toString) (toString i)) e

/-! ## The definitional closure -/

/-- The expression whose *value* contributes to a constant's hash: a definition's body.  A
theorem's or axiom's proof term is deliberately excluded — it is `#assert_axioms`' subject, not a
statement's. -/
private def hashedValue? : ConstantInfo → Option Expr
  | .defnInfo v => some v.value
  | _ => none

/-- Extra constants that a declaration's shape depends on but that its type expression does not
mention: an inductive type's constructors. -/
private def structuralNames : ConstantInfo → List Name
  | .inductInfo v => v.ctors
  | _ => []

/-- The per-constant hash: its arity in universe parameters, its type, its value if it is a
definition, and its structural names. -/
private def constHash (info : ConstantInfo) : UInt64 :=
  let lp := info.levelParams
  let h := feed fnvOffset schemeTag
  let h := feed (feed h "arity") (toString lp.length)
  let h := feedExpr lp (feed h "type") info.type
  let h :=
    match hashedValue? info with
    | some v => feedExpr lp (feed h "value") v
    | none => feed h "novalue"
  let h :=
    match info with
    | .inductInfo v =>
      feed (feed (feed (feed h "ind") (toString v.numParams)) "idx") (toString v.numIndices)
    | _ => h
  (structuralNames info).foldl (fun h n => feedTok h "sub" n.toString) h

/-- Constants a project-local declaration's shape depends on. -/
private def successors (info : ConstantInfo) : List Name :=
  let fromType := info.type.getUsedConstants.toList
  let fromValue :=
    match hashedValue? info with
    | some v => v.getUsedConstants.toList
    | none => []
  structuralNames info ++ fromType ++ fromValue

/-- Worklist traversal of the definitional closure.  A constant is recorded before its successors
are pushed, so a cyclic reference (should the environment ever contain one) terminates rather than
diverging. -/
private partial def walk (env : Environment) :
    List Name → Std.HashMap Name UInt64 → Std.HashSet Name →
      CoreM (Std.HashMap Name UInt64 × Std.HashSet Name)
  | [], visited, external => return (visited, external)
  | n :: rest, visited, external => do
    if visited.contains n || external.contains n then
      walk env rest visited external
    else
      match classify env n with
      | .external => walk env rest visited (external.insert n)
      | .unclassified m =>
        throwError "statement fingerprint: constant '{n}' was declared in module '{m}', whose \
          root component '{nameRoot m}' is classified neither as a project root nor as an \
          external boundary. Add it to `AxiomAudit.StatementFingerprint.projectRoots` (a new \
          library of this project, whose definitions must be covered) or to `externalRoots` (a \
          new upstream dependency, referenced by name only)."
      | .project =>
        let some info := env.find? n
          | throwError "statement fingerprint: unknown constant '{n}'"
        walk env (successors info ++ rest) (visited.insert n (constHash info)) external

/-- The result of a fingerprint computation. -/
structure Result where
  /-- The digest. -/
  hash : UInt64
  /-- Number of project-local constants unfolded. -/
  projectConsts : Nat
  /-- Number of distinct external constants met at the boundary. -/
  externalConsts : Nat

/-- Structural fingerprint of the *statement* of `root`: `root` itself, hashed by exactly the rule
used for every project-local constant, together with the transitive definitional closure of the
project-local constants it depends on.

The root is treated uniformly with its closure, which makes the command serve both idioms:

* on a **theorem**, only the type is hashed, so the digest pins the statement and is blind to the
  proof;
* on a **definition** — a statement *shape* such as `Frontier.OmegaBound`, or the definition of
  `omega` itself — the value is hashed too, so the digest pins the `Prop` the shape unfolds to and
  the whole chain of definitions underneath it.

Closure entries are sorted by name before being absorbed, so the digest does not depend on
traversal order.  `root`'s own *name* is not hashed: renaming a declaration does not change what
it says. -/
def fingerprint (root : Name) : CoreM Result := do
  let env ← getEnv
  let info ← getConstInfo root
  let (visited, external) ← walk env (successors info) {} {}
  let entries := (visited.erase root).toArray.qsort (fun a b => a.1.toString < b.1.toString)
  let h := feed fnvOffset schemeTag
  let h := feed (feed h "root") (hex16 (constHash info))
  let h := feed (feed h "closure") (toString entries.size)
  let h := entries.foldl (fun h (n, ch) => feed (feedTok h "K" n.toString) (hex16 ch)) h
  return { hash := h, projectConsts := entries.size, externalConsts := external.size }

/-! ## Commands -/

/-- `#statement_fingerprint id` reports the structural fingerprint of `id`'s statement, in the
exact form a `#assert_statement_fingerprint` line expects. -/
elab "#statement_fingerprint " id:ident : command => do
  let names ← liftCoreM <| realizeGlobalConstWithInfos id
  for name in names do
    let r ← liftCoreM <| fingerprint name
    logInfo m!"#assert_statement_fingerprint {name} \"{hex16 r.hash}\"\n\
      -- project closure: {r.projectConsts} constants; external boundary: {r.externalConsts} names"

/-- `#assert_statement_fingerprint id "<hex>"` fails elaboration unless the structural fingerprint
of `id`'s statement is exactly `<hex>`. -/
elab "#assert_statement_fingerprint " id:ident expected:str : command => do
  let names ← liftCoreM <| realizeGlobalConstWithInfos id
  for name in names do
    let r ← liftCoreM <| fingerprint name
    let got := hex16 r.hash
    unless got == expected.getString do
      throwError "statement fingerprint of '{name}' is \"{got}\", not the committed \
        \"{expected.getString}\" ({r.projectConsts} project constants in the closure, \
        {r.externalConsts} external names).\n\
        Either the statement or a definition it is phrased in terms of has changed. Review the \
        change, then re-commit the value printed by `#statement_fingerprint {name}`."

end AxiomAudit.StatementFingerprint
