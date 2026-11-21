import Mathlib.CategoryTheory.PathCategory.Basic
import TypedAuthz.Lens

/-! # Nested records -/

namespace TypedAuthz

open CategoryTheory

/-- The structure of a nested database, giving each record's fields and the kind of value at each
leaf. -/
inductive Schema (Field Kind : Type) where
  | leaf (kind : Kind)
  | node (fields : List Field) (child : Field -> Schema Field Kind)

namespace Schema

variable {Field Kind : Type}

/-- A step from a record into one of its fields. -/
inductive Step : Schema Field Kind -> Schema Field Kind -> Type where
  | field {fields : List Field} {child : Field -> Schema Field Kind}
      (field : Field) (isField : Membership.mem fields field) :
      Step (.node fields child) (child field)

instance : Quiver (Schema Field Kind) := Quiver.mk Step

/-- The type of databases with this structure. -/
def denote (Leaf : Kind -> Type) : Schema Field Kind -> Type
  | .leaf kind => Leaf kind
  | .node fields child => (field : Subtype (Membership.mem fields)) -> (child field.1).denote Leaf

variable [DecidableEq Field]

/-- The lens for the field that `step` goes into. -/
def Step.lens (Leaf : Kind -> Type) :
    {source target : Schema Field Kind} -> Step source target ->
      Lens (source.denote Leaf) (target.denote Leaf)
  | _, _, @Step.field _ _ fields child name isName => {
      get := fun record => record (Subtype.mk name isName)
      set := fun record value => Function.update record (Subtype.mk name isName) value
      get_set := fun _ _ => Function.update_self _ _ _
      set_get := fun _ => Function.update_eq_self _ _
      set_set := fun _ _ _ => Function.update_idem _ _ _ }

/-- Lets `composePath` build the lens of a path from the lenses of its steps. -/
def lens (Leaf : Kind -> Type) : Prefunctor (Schema Field Kind) LensCat where
  obj schema := schema.denote Leaf
  map step := step.lens Leaf

/-- The lens of two joined paths is the composite of their lenses. -/
theorem composePath_mapPath_comp (Leaf : Kind -> Type) {first middle last : Schema Field Kind}
    (path1 : Quiver.Path first middle) (path2 : Quiver.Path middle last) :
    composePath ((lens Leaf).mapPath (path1.comp path2)) =
      CategoryStruct.comp (composePath ((lens Leaf).mapPath path1))
        (composePath ((lens Leaf).mapPath path2)) := by
  simp [Prefunctor.mapPath_comp, composePath_comp]

end Schema

end TypedAuthz
