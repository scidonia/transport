import Transport.GeneralTransport

/-!
# Substitution coherence for transport

`transport_theorem` composes a typing direction with a sound transport.
`transport_theorem_comp` composes two transports.  This file adds the remaining
general coherence square: transport is stable under a context morphism.

The coherence data is explicit.  A `TransportData.Subst` supplies the action of
a pair of substitutions on the context/type relations and the equation that
transport commutes with substitution.  The theorem then reads a substituted
residual term back at the substituted source context and type.

No particular supercompiler or substitution is fixed.
-/

namespace Transport

open Transport.Mltt

/-- Substitute a context pointwise. -/
def Ctx.subst (σ : Nat → Tm) (Γ : Ctx) : Ctx := Γ.map (Tm.subst σ)

namespace TransportData

/-- Coherence data for substitution.  `σ` is the source substitution and `σ'`
the residual substitution. -/
structure Subst (td : TransportData) : Type 2 where
  substRel : (Nat → Tm) → (Nat → Tm) → Type
  ctxSubst : ∀ {Γ Γ' : Ctx} (σ σ' : Nat → Tm), substRel σ σ' →
    td.ctxRel Γ Γ' → td.ctxRel (Ctx.subst σ Γ) (Ctx.subst σ' Γ')
  tySubst : ∀ {A A' : Tm} (σ σ' : Nat → Tm), substRel σ σ' →
    td.tyRel A A' → td.tyRel (Tm.subst σ A) (Tm.subst σ' A')
  transport_subst : ∀ {Γ Γ' : Ctx} {A A' : Tm} {t : Tm}
    (σ σ' : Nat → Tm) (hσ : substRel σ σ')
    (hΓ : td.ctxRel Γ Γ') (hA : td.tyRel A A'),
    td.transport (ctxSubst σ σ' hσ hΓ) (tySubst σ σ' hσ hA) (Tm.subst σ' t)
      = Tm.subst σ (td.transport hΓ hA t)


/-- The identity transport has substitution coherence when the substitution
relation is equality of substitutions. -/
def identitySubst : identity.Subst where
  substRel := fun σ σ' => EqT σ σ'
  ctxSubst := by
    intro Γ Γ' σ σ' hσ hΓ
    cases hσ.eq
    cases hΓ.eq
    exact ⟨rfl⟩
  tySubst := by
    intro A A' σ σ' hσ hA
    cases hσ.eq
    cases hA.eq
    exact ⟨rfl⟩
  transport_subst := by
    intro Γ Γ' A A' t σ σ' hσ hΓ hA
    cases hσ.eq
    rfl

end TransportData

/-- The coherence square: given substitution-stable transport data, a
substituted residual term transports to the substituted source term. -/
theorem transport_subst_typing (td : TransportData) (ts : td.Subst)
    {env : Env} {Γ Γ' : Ctx} {A A' t : Tm} {σ σ' : Nat → Tm}
    (hσ : ts.substRel σ σ')
    (hΓ : td.ctxRel Γ Γ') (hA : td.tyRel A A')
    (hsub : HasType env (Ctx.subst σ' Γ') (Tm.subst σ' t) (Tm.subst σ' A')) :
    HasType env (Ctx.subst σ Γ)
      (Tm.subst σ (td.transport hΓ hA t)) (Tm.subst σ A) := by
  have h := td.sound (ts.ctxSubst σ σ' hσ hΓ) (ts.tySubst σ σ' hσ hA) hsub
  rw [ts.transport_subst] at h
  exact h


namespace TransportData

/-- Type-former congruence data.  The Pi clause is the fiberwise body relation
that a dependent transport must respect. -/
structure Congruence (td : TransportData) : Type 1 where
  sort : ∀ i, td.tyRel (.sort i) (.sort i)
  pi : ∀ {A A' B B' : Tm},
    td.tyRel A A' →
    (∀ (x x' : Tm), td.tyRel x x' →
      td.tyRel (Tm.subst0 x B) (Tm.subst0 x' B')) →
    td.tyRel (.pi A B) (.pi A' B')

end TransportData

/-- The general Pi transport lemma from type-former congruence. -/
def transport_ty_pi (td : TransportData) (c : td.Congruence)
    {A A' B B' : Tm}
    (hA : td.tyRel A A')
    (hB : ∀ (x x' : Tm), td.tyRel x x' →
      td.tyRel (Tm.subst0 x B) (Tm.subst0 x' B')) :
    td.tyRel (.pi A B) (.pi A' B') :=
  c.pi hA hB

end Transport
