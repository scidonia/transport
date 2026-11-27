import Transport.Action

/-!
# Action calculus at a result relation

Source and residual processes may have different result types.  `BisimRel`
observes through a heterogeneous relation `rel : S -> R -> Prop`; the fold,
generalisation, and derivation certificates are parameterised by it.
-/

namespace Transport.ActionRel

open Transport.Action

universe u

def BisimRel {S R : Type u} (rel : S → R → Prop)
    (P : Process S) (Q : Process R) : Nat → P.Config → Q.Config → Prop
  | 0, _, _ => True
  | n + 1, p, q =>
      match P.step p, Q.step q with
      | none, none =>
          match P.obs p, Q.obs q with
          | some s, some r => rel s r
          | none, none => True
          | _, _ => False
      | some p', some q' => BisimRel rel P Q n p' q'
      | _, _ => False

structure FoldCertRel {S R : Type u} (rel : S → R → Prop)
    (P : Process S) (Q : Process R) (measure : Q.Config → Nat)
    (p : P.Config) (q : Q.Config) where
  p' : P.Config
  q' : Q.Config
  step_p : P.step p = some p'
  step_q : Q.step q = some q'
  bisim : ∀ n, BisimRel rel P Q n p q
  guarded : measure q' < measure q

structure GenCertRel {S R : Type u} (rel : S → R → Prop)
    (P : Process S) (Q : Process R) (Params : Type u) where
  source : Params → P.Config
  schema : Params → Q.Config
  sound : ∀ σ, ∀ n, BisimRel rel P Q n (source σ) (schema σ)

inductive DerivationRel {S R : Type u} (rel : S → R → Prop)
    (P : Process S) (Q : Process R) (measure : Q.Config → Nat) :
    P.Config → Q.Config → Type (u + 1)
  | halt (p : P.Config) (q : Q.Config)
      (hp : P.step p = none) (hq : Q.step q = none)
      (h : BisimRel rel P Q 1 p q) :
      DerivationRel rel P Q measure p q
  | cert (p : P.Config) (q : Q.Config)
      (h : ∀ n, BisimRel rel P Q n p q) :
      DerivationRel rel P Q measure p q
  | fold (p : P.Config) (q : Q.Config)
      (cert : FoldCertRel rel P Q measure p q)
      (rest : DerivationRel rel P Q measure cert.p' cert.q') :
      DerivationRel rel P Q measure p q
  | generalise (p : P.Config) {Params : Type u}
      (g : GenCertRel rel P Q Params) (σ : Params)
      (hsource : g.source σ = p)
      (rest : DerivationRel rel P Q measure p (g.schema σ)) :
      DerivationRel rel P Q measure p (g.schema σ)

namespace DerivationRel

theorem sound {S R : Type u} {rel : S → R → Prop} {P : Process S}
    {Q : Process R} {measure : Q.Config → Nat} {p : P.Config} {q : Q.Config}
    (d : DerivationRel rel P Q measure p q) :
    ∀ n, BisimRel rel P Q n p q := by
  induction d with
  | halt p q hp hq h =>
      intro n
      cases n with
      | zero => trivial
      | succ n =>
          simpa [BisimRel, hp, hq] using h
  | cert p q h => exact h
  | fold p q cert rest ih => exact cert.bisim
  | generalise p g σ hsource rest ih =>
      intro n
      rw [← hsource]
      exact g.sound σ n

end DerivationRel

end Transport.ActionRel
