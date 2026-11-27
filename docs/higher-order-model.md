# Higher-order values: positivity and closures

A direct semantic value type

```lean
inductive Val
  | nat : Nat -> Val
  | fun : (Val -> Val) -> Val
```

is rejected by Lean: `Val.fun` has a non-positive occurrence of `Val` in the
function domain.  This is not a temporary elaboration issue; it is the
strict-positivity requirement of the kernel.

## The closure representation

Use a syntactic, positive value representation:

```text
Tm  ::= var Nat | zero | succ Tm | lam Tm | app Tm Tm
Val ::= nat Nat | closure Tm Env
Env = List Val
```

`Val` is positive (`List Val` is positive).  Evaluation and application are
defined by substitution/environment extension.  The function-space logical
relation is defined on **terms/closures**, not on a semantic function field:

```text
LR (arr A B) t u :=
  for all closed a b, LR A a b -> LR B (app t a) (app u b)
```

At `nat`, `LR` observes the evaluated numeral.  This is a syntactic logical
relation with a function clause; it avoids the negative value constructor.

Alternatives are defunctionalised codes (`Val.fun : Code`) with an `apply`
function, or a PER/CwF model with a separate function-space object.  The action
interface does not change: `BisimRel` takes the relation chosen at the result
type, and the certificate is the typed relation.

## Consequence for the programme

The higher-order layer should be built as:

1. a positive `Tm`/`Val` closure language;
2. evaluation/substitution and a step relation;
3. a syntactic `LR` with the function clause;
4. the process/action instance at a chosen type relation;
5. HOSC generalisation/fold actions over the closure language.

The existing `ActionRel`/`ActionReverseRel` typed relation and the certified
generalisation+fold demo are unaffected; they remain the first-order/base
regression.
