# Lean 4 and HoTT: survey and decision

The univalent layer uses **Cubical Agda**, a type theory designed for HoTT with
computational univalence and higher inductive types.  Lean remains the
syntactic transport core.  No univalence axiom is added over Lean's `Eq`.

## Why not Lean's `Eq`

Lean's `Eq` is proof-irrelevant and `Prop` permits large elimination.  A
univalence map with the round-trip law over `Eq` is inconsistent; the
obstruction is mechanised in `Transport/UnivalenceObstruction.lean`.

This is not merely our observation:

- The accepted Proof Assistants Stack Exchange answer (Jason Rute, 2025):
  “Lean is meant only for working with a particular type theory… the kernel
  can't be changed (except via adding axioms)… Lean type theory isn't
  compatible with homotopy or cubical type theory.”
  <https://proofassistants.stackexchange.com/questions/4790/can-cubical-type-theory-be-done-in-lean-4-somehow>
- Lean Zulip, “Univalence axiom” (2019): “The univalence axiom is inconsistent
  with proof irrelevance which is baked into Lean's logic.”  Floris van Doorn
  adds that a separate `Type`-valued `hott_eq` is also inconsistent unless the
  large elimination is blocked, because Lean's `Eq` is equivalent to it.
  <https://leanprover-community.github.io/archive/stream/113488-general/topic/Univalence.20axiom.html>
- The HoTT blog (2017 update): “the newest version of Lean currently doesn’t
  support HoTT, but there is a frozen version which does support HoTT.”
  <https://homotopytypetheory.org/2015/12/02/the-proof-assistant-lean>

A synthetic `Type`-valued equality is not enough by itself; a large-elimination
checker or a model is required.

## Survey

| project | what it is | status |
| --- | --- | --- |
| [`rzrn/ground_zero`](https://github.com/rzrn/ground_zero) | Lean 4 synthetic HoTT library: proof-relevant `Id`/`Path`, `ua`/`uaβ`, HITs via quotients, large-elimination checker; Apache-2.0 | Evaluated and built on Lean 4.27; `notTransport` checked. Not used: synthetic library pinned to an older Lean, and it does not mechanise a consistency model. |
| [`sinhp/HoTTLean`](https://github.com/sinhp/HoTTLean) | groupoid model of HoTT and SynthLean proof mode; Mathlib + Poly; Lean 4.25.0-rc2 | Evaluated. A serious meta-theory development, but not a drop-in univalence library. |
| [`mitschabaude-bot/kubus`](https://github.com/mitschabaude-bot/kubus) | verified kernel for CCHM cubical type theory, univalence and canonicity in its object language; Lean 4.30 | Trust anchor: separate proof assistant and `.ktt` language, not an importable Lean library. |
| [`theckl/cHoTT4`](https://github.com/theckl/cHoTT4) | Lean 4 model of cubical type theory (2024) | Model development, low activity; not used. |
| [`merzougao/HoTT_Lean4`](https://github.com/merzougao/HoTT_Lean4) | early 2023 start | One basic file; not viable. |
| [`gebner/hott3`](https://github.com/gebner/hott3), [Lean 2 HoTT](https://github.com/leanprover/lean2/blob/master/hott/hott.md) | Lean 3/2 HoTT libraries | Not Lean 4. |

## Decision

- **Cubical Agda** (`cubical/`) for computational univalence, vector packing,
  and the three-vector coherence.  This is the theory designed for HoTT.
- **Lean 4.35** for the syntactic transport theorem, certificates, derivation,
  and index migration.
- **Kubus** is cited as the trust anchor for a verified kernel, a cubical-sets
  model, and canonicity; it is not a dependency.

Ground Zero remains an evaluated experiment: it showed that a synthetic Lean 4
`ua`/`uaβ` is possible on Lean 4.27, but it is not the active univalent layer.
