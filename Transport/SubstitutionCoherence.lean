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
structure Subst (td : TransportData) : Type where
  ctxSubst : ∀ {Γ Γ' : Ctx} (σ σ' : Nat → Tm),
    td.ctxRel Γ Γ' → td.ctxRel (Ctx.subst σ Γ) (Ctx.subst σ' Γ')
  tySubst : ∀ {A A' : Tm} (σ σ' : Nat → Tm),
    td.tyRel A A' → td.tyRel (Tm.subst σ A) (Tm.subst σ' A')
  transport_subst : ∀ {Γ Γ' : Ctx} {A A' : Tm} {t : Tm}
    (σ σ' : Nat → Tm) (hΓ : td.ctxRel Γ Γ') (hA : td.tyRel A A'),
    td.transport (ctxSubst σ σ' hΓ) (tySubst σ σ' hA) (Tm.subst σ' t)
      = Tm.subst σ (td.transport hΓ hA t)

end TransportData

/-- The coherence square: given substitution-stable transport data, a
substituted residual term transports to the substituted source term. -/
theorem transport_subst_typing (td : TransportData) (ts : td.Subst)
    {env : Env} {Γ Γ' : Ctx} {A A' t : Tm} {σ σ' : Nat → Tm}
    (hΓ : td.ctxRel Γ Γ') (hA : td.tyRel A A')
    (hsub : HasType env (Ctx.subst σ' Γ') (Tm.subst σ' t) (Tm.subst σ' A')) :
    HasType env (Ctx.subst σ Γ) (Tm.subst σ (td.transport hΓ hA t)) (Tm.subst σ A) := by
  have h := td.sound (ts.ctxSubst σ σ' hΓ) (ts.tySubst σ σ' hA) hsub
  rw [ts.transport_subst] at h
  exact h

end Transport
