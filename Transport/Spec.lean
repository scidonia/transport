import Transport.Mltt.Beta

/-!
# The transport specification

A supercompiler is a translation of contexts, types, and terms.  It produces a
residual program in a translated context and at a translated type, not a reduct
of the source program.  The transport theorem says how the residual program is
read back at the source context and type.

This file fixes the shape of that theorem and the three equality regimes.  It
does not assume a particular supercompiler: `TransportData` is the transport
operation and its soundness, and `Supercompiler` is the typing direction of the
translation.  The theorem is their composite.
-/

namespace Transport

open Transport.Mltt

/-- A syntactic translation: residual context, type, and term. -/
structure Translation where
  scCtx : Ctx → Ctx
  scTy : Tm → Tm
  scTm : Tm → Tm

/-- A relation between source and residual contexts. -/
abbrev CtxRel := Ctx → Ctx → Prop

/-- A relation between source and residual types. -/
abbrev TyRel := Tm → Tm → Prop

/-- A transport operation and the typing fact that makes it sound.  `transport`
takes a residual term in `Γ'` at `A'` to a source-context term in `Γ` at `A`. -/
structure TransportData where
  ctxRel : CtxRel
  tyRel : TyRel
  transport : ∀ {Γ Γ' : Ctx} {A A' : Tm},
    ctxRel Γ Γ' → tyRel A A' → Tm → Tm
  sound : ∀ {env : Env} {Γ Γ' : Ctx} {A A' : Tm} {t : Tm}
    (hΓ : ctxRel Γ Γ') (hA : tyRel A A'),
    HasType env Γ' t A' → HasType env Γ (transport hΓ hA t) A

/-- A supercompiler together with the relations its result is compared under. -/
structure Supercompiler where
  translation : Translation
  ctxRel : CtxRel
  tyRel : TyRel

/-- The transport theorem, §4 of the specification: if the residual term is
typed at the translated context and type, and the transport data is sound for
the relations relating source to translated data, then the transported residual
term has the source type in the source context. -/
theorem transport_theorem (sc : Supercompiler) (td : TransportData)
    (hctx : ∀ Γ, td.ctxRel Γ (sc.translation.scCtx Γ))
    (hty : ∀ A, td.tyRel A (sc.translation.scTy A))
    (htm : ∀ {env : Env} {Γ : Ctx} {t A : Tm},
      HasType env Γ t A →
      HasType env (sc.translation.scCtx Γ)
        (sc.translation.scTm t) (sc.translation.scTy A)) :
    ∀ {env : Env} {Γ : Ctx} {t A : Tm}, HasType env Γ t A →
      HasType env Γ
        (td.transport (hctx Γ) (hty A) (sc.translation.scTm t)) A := by
  intro env Γ t A h
  exact td.sound (hctx Γ) (hty A) (htm h)

/-- The fragment version of the theorem: the typing direction is only
available for terms of the simple fragment.  This is the regime the current
formalisation covers, because general weakening for the indexed families is
still an open prerequisite. -/
theorem transport_theorem_fragment (sc : Supercompiler) (td : TransportData)
    (hctx : ∀ Γ, td.ctxRel Γ (sc.translation.scCtx Γ))
    (hty : ∀ A, td.tyRel A (sc.translation.scTy A))
    (htm : ∀ {env : Env} {Γ : Ctx} {t A : Tm},
      HasType env Γ t A → Mltt.Subst.Simple t →
      HasType env (sc.translation.scCtx Γ)
        (sc.translation.scTm t) (sc.translation.scTy A)) :
    ∀ {env : Env} {Γ : Ctx} {t A : Tm}, HasType env Γ t A →
      Mltt.Subst.Simple t →
      HasType env Γ
        (td.transport (hctx Γ) (hty A) (sc.translation.scTm t)) A := by
  intro env Γ t A h hs
  exact td.sound (hctx Γ) (hty A) (htm h hs)

namespace TransportData

/-- The identity regime: source and residual contexts and types are
syntactically equal, and the transport is the identity on terms. -/
def identity : TransportData where
  ctxRel := Eq
  tyRel := Eq
  transport := fun _ _ t => t
  sound := by
    intro env Γ Γ' A A' t hΓ hA ht
    cases hΓ
    cases hA
    exact ht

end TransportData

namespace BetaInstance

open Transport.Mltt.Beta

/-- Beta contraction as a supercompiler: the residual term is the contractum,
the context and type are unchanged, and the transport is `refl`. -/
def asSupercompiler : Supercompiler where
  translation := { scCtx := id, scTy := id, scTm := beta }
  ctxRel := Eq
  tyRel := Eq

/-- The transport theorem instantiated at beta contraction.  This is a
non-identity supercompiler: `beta t` is not definitionally `t` on a redex. -/
theorem transport {env : Env} {Γ : Ctx} {t A : Tm}
    (h : HasType env Γ t A) (hs : Mltt.Subst.Simple t) :
    HasType env Γ (beta t) A :=
  transport_theorem_fragment asSupercompiler TransportData.identity
    (fun _ => rfl) (fun _ => rfl)
    (fun h hs => beta_preserves_hasType h hs) h hs

end BetaInstance

end Transport
