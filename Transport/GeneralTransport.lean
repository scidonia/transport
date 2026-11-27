import Transport.Spec

/-!
# General transport composition

`Transport.transport_theorem` composes a supercompiler's typing direction with
a sound transport operation.  This file adds the general composition law: two
successive translations and their transports compose, without choosing a
particular supercompiler or a particular relation.

This is the general form of the transport theorem.  The relations remain
`Type`-valued data, so definitional, propositional, and semantic regimes are
instances rather than separate theorems.
-/

namespace Transport

open Transport.Mltt

/-- The general transport step: a sound transport reads a residual term at a
related context and type back at the source. -/
theorem transport_along (td : TransportData)
    {env : Env} {Γ Γ' : Ctx} {A A' : Tm} {t : Tm}
    (hΓ : td.ctxRel Γ Γ') (hA : td.tyRel A A')
    (ht : HasType env Γ' t A') :
    HasType env Γ (td.transport hΓ hA t) A :=
  td.sound hΓ hA ht

/-- Composition of two translation/transport stages.  The second stage
transports the residual of the first back to the intermediate context and type;
the first stage then transports the result to the source. -/
theorem transport_theorem_comp
    (sc₁ sc₂ : Supercompiler) (td₁ td₂ : TransportData)
    (hctx₁ : ∀ Γ, td₁.ctxRel Γ (sc₁.translation.scCtx Γ))
    (hty₁ : ∀ A, td₁.tyRel A (sc₁.translation.scTy A))
    (htm₁ : ∀ {env : Env} {Γ : Ctx} {t A : Tm},
      HasType env Γ t A →
      HasType env (sc₁.translation.scCtx Γ)
        (sc₁.translation.scTm t) (sc₁.translation.scTy A))
    (hctx₂ : ∀ Γ, td₂.ctxRel Γ (sc₂.translation.scCtx Γ))
    (hty₂ : ∀ A, td₂.tyRel A (sc₂.translation.scTy A))
    (htm₂ : ∀ {env : Env} {Γ : Ctx} {t A : Tm},
      HasType env Γ t A →
      HasType env (sc₂.translation.scCtx Γ)
        (sc₂.translation.scTm t) (sc₂.translation.scTy A)) :
    ∀ {env : Env} {Γ : Ctx} {t A : Tm}, HasType env Γ t A →
      HasType env Γ
        (td₁.transport (hctx₁ Γ) (hty₁ A)
          (td₂.transport
            (hctx₂ (sc₁.translation.scCtx Γ))
            (hty₂ (sc₁.translation.scTy A))
            (sc₂.translation.scTm (sc₁.translation.scTm t)))) A := by
  intro env Γ t A ht
  exact td₁.sound (hctx₁ Γ) (hty₁ A)
    (td₂.sound
      (hctx₂ (sc₁.translation.scCtx Γ))
      (hty₂ (sc₁.translation.scTy A))
      (htm₂ (htm₁ ht)))

end Transport
