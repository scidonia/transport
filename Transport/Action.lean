import Std

/-!
# The action interface

A supercompiler action is parameterised by a process (`Config`, `Step`, `Obs`),
not by the reverse worker.  `Bisim` is the step-indexed source/residual
relation; `FoldCert` and `Derivation` are the proof-carrying actions.
-/

namespace Transport.Action

universe u

structure Process (Result : Type u) where
  Config : Type u
  step : Config → Option Config
  obs : Config → Option Result

/-- Step-indexed bisimulation between two processes at a common result type. -/
def Bisim {Result : Type u} (P Q : Process Result) :
    Nat → P.Config → Q.Config → Prop
  | 0, _, _ => True
  | n + 1, p, q =>
      match P.step p, Q.step q with
      | none, none => P.obs p = Q.obs q
      | some p', some q' => Bisim P Q n p' q'
      | _, _ => False

/-- A proof-carrying fold: step, unfolding, bisimulation, guarded decrease. -/
structure FoldCert {Result : Type u} (P Q : Process Result)
    (measure : Q.Config → Nat) (p : P.Config) (q : Q.Config) where
  p' : P.Config
  q' : Q.Config
  step_p : P.step p = some p'
  step_q : Q.step q = some q'
  bisim : ∀ n, Bisim P Q n p q
  guarded : measure q' < measure q

/-- A proof-carrying generalisation: a source family and a residual schema,
related for every parameter. -/
structure GenCert {Result : Type u} (P Q : Process Result) (Params : Type u) where
  source : Params → P.Config
  schema : Params → Q.Config
  sound : ∀ σ, ∀ n, Bisim P Q n (source σ) (schema σ)

/-- A derivation tree of actions. -/
inductive Derivation {Result : Type u} (P Q : Process Result)
    (measure : Q.Config → Nat) : P.Config → Q.Config → Type (u + 1)
  | halt (p : P.Config) (q : Q.Config)
      (hp : P.step p = none) (hq : Q.step q = none) (hobs : P.obs p = Q.obs q) :
      Derivation P Q measure p q
  | cert (p : P.Config) (q : Q.Config)
      (h : ∀ n, Bisim P Q n p q) : Derivation P Q measure p q
  | fold (p : P.Config) (q : Q.Config)
      (cert : FoldCert P Q measure p q)
      (rest : Derivation P Q measure cert.p' cert.q') :
      Derivation P Q measure p q
  | generalise (p : P.Config) {Params : Type u}
      (g : GenCert P Q Params) (σ : Params)
      (hsource : g.source σ = p)
      (rest : Derivation P Q measure p (g.schema σ)) :
      Derivation P Q measure p (g.schema σ)

namespace Derivation

theorem sound {Result : Type u} {P Q : Process Result} {measure : Q.Config → Nat}
    {p : P.Config} {q : Q.Config} (d : Derivation P Q measure p q) :
    ∀ n, Bisim P Q n p q := by
  induction d with
  | halt p q hp hq hobs =>
      intro n
      cases n with
      | zero => trivial
      | succ n => simp [Bisim, hp, hq, hobs]
  | cert p q h => exact h
  | fold p q cert rest ih => exact cert.bisim
  | generalise p g σ hsource rest ih =>
      intro n
      rw [← hsource]
      exact g.sound σ n

end Derivation

end Transport.Action
