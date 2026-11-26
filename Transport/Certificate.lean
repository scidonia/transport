import Std

/-!
# A first supercompilation certificate

Stage 2 of the research programme starts with a pure, total, first-order list
fragment.  This file fixes the fragment, the reverse-accumulator
generalisation, and a checked certificate for it.

The certificate is data: the source expression, the generalised expression, the
fold parameter, the accumulator parameter, and the initial accumulator.  The
checker decides a syntactic predicate on that data.  Soundness is a theorem
about the evaluation of the expressions, quantified over the closing
substitution of the input list.
-/

namespace Transport.Certificate

universe u

/-- First-order expressions over lists: variables, nil, cons, append, reverse. -/
inductive LExp (α : Type u) where
  | var : Nat → LExp α
  | nil : LExp α
  | cons : α → LExp α → LExp α
  | append : LExp α → LExp α → LExp α
  | reverse : LExp α → LExp α
  deriving Repr, DecidableEq

namespace LExp

/-- Evaluation under a closing environment. -/
def eval {α : Type u} (ρ : Nat → List α) : LExp α → List α
  | var n => ρ n
  | nil => []
  | cons x xs => x :: eval ρ xs
  | append xs ys => eval ρ xs ++ eval ρ ys
  | reverse xs => (eval ρ xs).reverse

end LExp

open LExp

/-- A closing substitution for the single input variable. -/
def env₁ {α : Type u} (xs : List α) : Nat → List α :=
  fun _ => xs

/-- The generalisation's parameter environment: variable 0 is the input list,
variable 1 is the accumulator. -/
def env₂ {α : Type u} (xs a : List α) : Nat → List α
  | 0 => xs
  | 1 => a
  | _ => []

/-- The source program: reverse the input. -/
def sourceExpr {α : Type u} : LExp α := .reverse (.var 0)

/-- The generalised configuration: `reverse xs ++ a`. -/
def genExpr {α : Type u} : LExp α := .append (.reverse (.var 0)) (.var 1)

def genEval {α : Type u} (xs a : List α) : List α :=
  (genExpr (α := α)).eval (env₂ xs a)

theorem genEval_eq {α : Type u} (xs a : List α) :
    genEval xs a = xs.reverse ++ a := by
  simp [genEval, genExpr, LExp.eval, env₂]

theorem genEval_nil {α : Type u} (xs : List α) :
    genEval xs [] = xs.reverse := by
  rw [genEval_eq]
  simp

theorem genEval_step {α : Type u} (x : α) (xs a : List α) :
    genEval (x :: xs) a = genEval xs (x :: a) := by
  rw [genEval_eq, genEval_eq, List.reverse_cons, List.append_assoc]
  simp

/-- The residual worker: reverse with an accumulator. -/
def revAcc {α : Type u} : List α → List α → List α
  | [], a => a
  | x :: xs, a => revAcc xs (x :: a)

@[simp] theorem revAcc_nil {α : Type u} (a : List α) : revAcc [] a = a := rfl

@[simp] theorem revAcc_cons {α : Type u} (x : α) (xs a : List α) :
    revAcc (x :: xs) a = revAcc xs (x :: a) := rfl

theorem revAcc_eq_genEval {α : Type u} (xs a : List α) :
    revAcc xs a = genEval xs a := by
  induction xs generalizing a with
  | nil => simp [genEval_eq]
  | cons x xs ih =>
      rw [revAcc_cons, ih, genEval_step]

theorem revAcc_reverse {α : Type u} (xs : List α) :
    revAcc xs [] = xs.reverse := by
  rw [revAcc_eq_genEval, genEval_eq]
  simp

/-- The fold's decrease: the recursive list is a proper subterm. -/
theorem fold_decrease {α : Type u} (x : α) (xs _a : List α) :
    List.length xs < List.length (x :: xs) := by
  simp

/-- The data a reverse certificate retains. -/
structure RevCert (α : Type u) where
  source : LExp α
  generalisation : LExp α
  foldVar : Nat
  accVar : Nat
  init : LExp α
  deriving Repr

namespace RevCert

/-- The syntactic checker: the certificate must name the reverse source, the
append-of-reverse generalisation, the input as the fold parameter, and the
accumulator initialised to nil. -/
def Check {α : Type u} (c : RevCert α) : Prop :=
  c.source = .reverse (.var 0) ∧
  c.generalisation = .append (.reverse (.var 0)) (.var 1) ∧
  c.foldVar = 0 ∧
  c.accVar = 1 ∧
  c.init = .nil

/-- The checker's decision procedure. -/
instance decidableCheck {α : Type u} [DecidableEq α] (c : RevCert α) :
    Decidable c.Check := by
  unfold Check
  infer_instance

/-- Executable form of `Check`. -/
def check {α : Type u} [DecidableEq α] (c : RevCert α) : Bool :=
  decide c.Check

theorem check_eq_true_iff {α : Type u} [DecidableEq α] (c : RevCert α) :
    c.check = true ↔ c.Check := by
  simp [check]

end RevCert

/-- The canonical reverse certificate. -/
def revCert {α : Type u} : RevCert α where
  source := .reverse (.var 0)
  generalisation := .append (.reverse (.var 0)) (.var 1)
  foldVar := 0
  accVar := 1
  init := .nil

theorem revCert_check {α : Type u} [DecidableEq α] :
    (revCert (α := α)).check = true := by
  simp [RevCert.check, RevCert.Check, revCert]

/-- Soundness: a checked certificate names the source expression, and the
residual worker at the initial accumulator returns the source value for every
closing substitution. -/
theorem revCert_sound {α : Type u} [DecidableEq α] (c : RevCert α)
    (h : c.check = true) :
    ∀ xs : List α,
      revAcc xs [] = c.source.eval (env₁ xs) := by
  have hc : c.Check := (RevCert.check_eq_true_iff c).mp h
  rcases hc with ⟨hsrc, _hgen, _hfold, _hacc, _hinit⟩
  intro xs
  rw [hsrc]
  simp [LExp.eval, env₁, revAcc_reverse]

/-- Stage 2 in one statement: the certificate checks, the worker is the
residual of the source for every input, and the fold decreases. -/
theorem revCert_sound_and_decreases {α : Type u} [DecidableEq α] :
    (revCert (α := α)).check = true ∧
    (∀ xs : List α, revAcc xs [] = (revCert (α := α)).source.eval (env₁ xs)) ∧
    (∀ (x : α) (xs _a : List α), List.length xs < List.length (x :: xs)) :=
  ⟨revCert_check, fun xs => revCert_sound revCert revCert_check xs,
    fun x xs _ => fold_decrease x xs []⟩

end Transport.Certificate
