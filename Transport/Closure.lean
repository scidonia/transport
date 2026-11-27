import Std
import Transport.ActionRel

/-!
# Positive closures and a higher-order logical relation

`Val` is a strictly positive closure language: `nat` or a syntactic closure over
an environment of values.  Evaluation and application are fuel-indexed; `LR` is
a step-indexed logical relation with a function-space clause.
-/

namespace Transport.Closure

universe u

inductive Ty where
  | nat : Ty
  | arr : Ty → Ty → Ty
  deriving Repr

inductive Tm where
  | var : Nat → Tm
  | zero : Tm
  | succ : Tm → Tm
  | lam : Tm → Tm
  | app : Tm → Tm → Tm

inductive Val where
  | nat : Nat → Val
  | closure : Tm → List Val → Val

def eval : Nat → Tm → List Val → Option Val
  | 0, _, _ => none
  | _ + 1, .var i, env => env[i]?
  | _ + 1, .zero, _ => some (.nat 0)
  | n + 1, .succ t, env =>
      match eval n t env with
      | some (.nat k) => some (.nat (k + 1))
      | _ => none
  | _ + 1, .lam body, env => some (.closure body env)
  | n + 1, .app f a, env =>
      match eval n f env with
      | some (.closure body env') =>
          match eval n a env with
          | some av => eval n body (av :: env')
          | none => none
      | _ => none

def apply : Nat → Val → Val → Option Val
  | 0, _, _ => none
  | n + 1, .closure body env, a => eval n body (a :: env)
  | _ + 1, .nat _, _ => none

def LR : Nat → Ty → Val → Val → Prop
  | 0, _, _, _ => True
  | _ + 1, .nat, .nat a, .nat b => a = b
  | n + 1, .arr A B, f, g =>
      ∀ a b, LR n A a b →
        match apply n f a, apply n g b with
        | some x, some y => LR n B x y
        | _, _ => False
  | _ + 1, _, _, _ => False

example : LR 1 .nat (.nat 0) (.nat 0) := by
  simp [LR]

example : eval 2 (.lam .zero) [] = some (.closure .zero []) := by
  rfl




/-! ## Substitution and small-step evaluation -/

def shift (d c : Nat) : Tm → Tm
  | .var x => if x < c then .var x else .var (x + d)
  | .zero => .zero
  | .succ t => .succ (shift d c t)
  | .lam t => .lam (shift d (c + 1) t)
  | .app f a => .app (shift d c f) (shift d c a)

def subst0 (u : Tm) : Tm → Tm
  | .var 0 => u
  | .var (x + 1) => .var x
  | .zero => .zero
  | .succ t => .succ (subst0 u t)
  | .lam t => .lam (subst0 (shift 1 0 u) t)
  | .app f a => .app (subst0 u f) (subst0 u a)

def step : Tm → Option Tm
  | .app (.lam body) a => some (subst0 a body)
  | .app f a =>
      match step f with
      | some f' => some (.app f' a)
      | none =>
          match step a with
          | some a' => some (.app f a')
          | none => none
  | .succ t =>
      match step t with
      | some t' => some (.succ t')
      | none => none
  | _ => none

example : subst0 (.lam (.var 0)) (.var 0) = .lam (.var 0) := by
  rfl

example : step (.app (.lam (.var 0)) (.lam (.var 0))) =
    some (.lam (.var 0)) := by
  rfl

/-- A term process: small-step evaluation, with a fuel-indexed observation. -/
def termProcess (fuel : Nat) : Transport.Action.Process Val where
  Config := Tm
  step := step
  obs := fun t => eval fuel t []

/-! ## A process/action instance at the closure relation -/

def LRAll (ty : Ty) (v w : Val) : Prop := ∀ n, LR n ty v w

def valueProcess (_ty : Ty) : Transport.Action.Process Val where
  Config := Val
  step := fun _ => none
  obs := fun v => some v

theorem valueBisim {ty : Ty} {v : Val} (h : LRAll ty v v) :
    ∀ n, Transport.ActionRel.BisimRel (LRAll ty)
      (valueProcess ty) (valueProcess ty) n v v := by
  intro n
  cases n with
  | zero => trivial
  | succ n =>
      simpa [Transport.ActionRel.BisimRel, valueProcess] using h

def valueCert (ty : Ty) (v : Val) (h : LRAll ty v v) :
    Transport.ActionRel.DerivationRel (LRAll ty) (valueProcess ty) (valueProcess ty)
      (fun _ => 0) v v :=
  Transport.ActionRel.DerivationRel.cert
    (rel := LRAll ty) (P := valueProcess ty) (Q := valueProcess ty)
    (measure := fun _ => 0) v v (valueBisim h)

theorem valueCert_sound (ty : Ty) (v : Val) (h : LRAll ty v v) :
    ∀ n, Transport.ActionRel.BisimRel (LRAll ty)
      (valueProcess ty) (valueProcess ty) n v v :=
  Transport.ActionRel.DerivationRel.sound (valueCert ty v h)

theorem nat_zero_LRAll : LRAll .nat (.nat 0) (.nat 0) := by
  intro n
  cases n with
  | zero => trivial
  | succ n => simp [LR]

example : Transport.ActionRel.DerivationRel (LRAll .nat)
    (valueProcess .nat) (valueProcess .nat) (fun _ => 0) (.nat 0) (.nat 0) :=
  valueCert .nat (.nat 0) nat_zero_LRAll



/-- A closed numeral term. -/
def numeral : Nat → Tm
  | 0 => .zero
  | n + 1 => .succ (numeral n)

theorem step_numeral (n : Nat) : step (numeral n) = none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [numeral, step, ih]

theorem eval_numeral : ∀ n, eval (n + 1) (numeral n) [] = some (.nat n)
  | 0 => rfl
  | n + 1 => by
      simp [numeral, eval, eval_numeral n]

theorem LRAll_nat (n : Nat) : LRAll .nat (.nat n) (.nat n) := by
  intro k
  cases k with
  | zero => trivial
  | succ k => simp [LR]

theorem termBisimNat (n : Nat) :
    ∀ k, Transport.ActionRel.BisimRel (LRAll .nat)
      (termProcess (n + 1)) (termProcess (n + 1)) k (numeral n) (numeral n) := by
  intro k
  cases k with
  | zero => trivial
  | succ k =>
      simp [Transport.ActionRel.BisimRel, termProcess, step_numeral, eval_numeral]
      exact LRAll_nat n

def termCertNat (n : Nat) :
    Transport.ActionRel.DerivationRel (LRAll .nat)
      (termProcess (n + 1)) (termProcess (n + 1)) (fun _ => 0)
      (numeral n) (numeral n) :=
  Transport.ActionRel.DerivationRel.cert
    (rel := LRAll .nat) (P := termProcess (n + 1)) (Q := termProcess (n + 1))
    (measure := fun _ => 0) (numeral n) (numeral n) (termBisimNat n)

theorem termCertNat_sound (n : Nat) :
    ∀ k, Transport.ActionRel.BisimRel (LRAll .nat)
      (termProcess (n + 1)) (termProcess (n + 1)) k (numeral n) (numeral n) :=
  Transport.ActionRel.DerivationRel.sound (termCertNat n)

example : Transport.ActionRel.DerivationRel (LRAll .nat)
    (termProcess 3) (termProcess 3) (fun _ => 0) (numeral 2) (numeral 2) :=
  termCertNat 2


end Transport.Closure
