import Std

/-!
# Finite-index migration

Stage 3 of the research programme: a length-indexed residual type, the
migration of an index along the length equation, and its coherence.  This is
the identity eliminator at `Fin`; it is the definitional/propositional regime,
not the univalent one.
-/

namespace Transport.IndexMigration

universe u

/-- Migrate a finite index along an equality of its bound.  The value is
unchanged; only the bound's proof changes. -/
def migrate {m n : Nat} (h : m = n) (i : Fin m) : Fin n :=
  ⟨i.val, by rw [← h]; exact i.isLt⟩

@[simp] theorem migrate_val {m n : Nat} (h : m = n) (i : Fin m) :
    (migrate h i).val = i.val := rfl

theorem migrate_refl {m : Nat} (i : Fin m) : migrate rfl i = i := by
  apply Fin.ext
  rfl

/-- Reindexing along a composite equality is the composite reindexing. -/
theorem migrate_trans {m n p : Nat} (h : m = n) (k : n = p) (i : Fin m) :
    migrate (h.trans k) i = migrate k (migrate h i) := by
  apply Fin.ext
  rfl

/-- Reindexing commutes with the successor constructor. -/
theorem migrate_succ {m n : Nat} (h : m = n) (i : Fin m) :
    migrate (congrArg Nat.succ h) i.succ = (migrate h i).succ := by
  apply Fin.ext
  rfl

/-- The source index of the append example. -/
abbrev SourceIndex {α : Type u} (xs ys : List α) : Type :=
  Fin (xs ++ ys).length

/-- The residual index: the two lengths added before the family is applied. -/
abbrev ResidualIndex {α : Type u} (xs ys : List α) : Type :=
  Fin (xs.length + ys.length)

/-- Migrate an index of `xs ++ ys` to the residual index `xs.length +
ys.length`. -/
def migrateIndex {α : Type u} (xs ys : List α)
    (i : SourceIndex xs ys) : ResidualIndex xs ys :=
  migrate (by rw [List.length_append]) i

theorem migrateIndex_val {α : Type u} (xs ys : List α)
    (i : SourceIndex xs ys) :
    (migrateIndex xs ys i).val = i.val := rfl

/-- Reindexing is stable under mapping the element type: the transported
index keeps its value. -/
theorem migrateIndex_map {α β : Type u} (f : α → β)
    (xs ys : List α) (i : SourceIndex xs ys) :
    (migrateIndex (xs.map f) (ys.map f)
      ⟨i.val, by
        simpa [List.length_append, List.length_map] using i.isLt⟩).val = i.val := rfl

end Transport.IndexMigration
