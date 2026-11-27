import Transport.Mltt.ScopedSubst
import Transport.Mltt.Conventions
import Transport.Mltt.Subst

/-!
# Well-formed typing

The scoped substitution layer is independent of `HasType`.  This file adds the
invariants a full-core substitution theorem must carry:

* a well-formed environment (the full-argument signature convention);
* a well-scoped context;
* scoped term and type.

`HasTypeWF` bundles a typing derivation with those invariants.  It is a design
layer: the substitution theorem that consumes it is not proved here.

The identity context morphism is proved, because it only uses the variable rule
and `subst_var`.
-/

namespace Transport.Mltt

open Transport.Mltt.Scoped
open Transport.Mltt.Conventions

/-- Every family in the environment satisfies the full-argument convention. -/
def WellFormedEnvFull (env : Env) : Prop :=
  ∀ (I : Nat) (sig : IndSig), lookupInd env I = some sig → WellFormedSigFull sig

/-- A context whose looked-up types are well scoped at their position. -/
def WellScopedCtx (Γ : Ctx) : Prop :=
  ∀ x A, ctxLookup Γ x = some A → WellScoped (x + 1) A

/-- A typing derivation carrying the invariants needed by full substitution. -/
structure HasTypeWF (env : Env) (Γ : Ctx) (t A : Tm) : Prop where
  hasType : HasType env Γ t A
  envWF : WellFormedEnvFull env
  ctxScoped : WellScopedCtx Γ
  termScoped : WellScoped Γ.length t
  typeScoped : WellScoped Γ.length A

namespace HasTypeWF

theorem hasType' {env Γ t A} (h : HasTypeWF env Γ t A) : HasType env Γ t A :=
  h.hasType

end HasTypeWF

/-- The identity context morphism: the variable rule plus `subst_var`. -/
theorem CtxMap.id (env : Env) (Γ : Ctx) : CtxMap env Tm.var Γ Γ := by
  intro x A hx
  simpa [Subst.subst_var] using HasType.var (env := env) Γ x A hx

end Transport.Mltt
