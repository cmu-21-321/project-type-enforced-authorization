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

/-- A path that starts at a leaf has no steps. -/
theorem length_eq_zero_of_path_from_leaf {kind : Kind} {target : Schema Field Kind}
    (path : Quiver.Path (leaf kind) target) : path.length = 0 := by
  induction path with
  | nil => rfl
  | cons rest step ih =>
    have same := Quiver.Path.eq_of_length_zero rest ih
    subst same
    cases step

variable [DecidableEq Field]

/-- The lens for the field that `step` goes into. -/
def Step.lens (Leaf : Kind -> Type) :
    {source target : Schema Field Kind} -> Step source target ->
      Lens (source.denote Leaf) (target.denote Leaf)
  | _, _, @Step.field _ _ _ _ name isName => Lens.eval (Subtype.mk name isName)

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

/-- The lens of a path that starts with `step` is the step's lens followed by the rest's lens. -/
theorem composePath_mapPath_toPath_comp (Leaf : Kind -> Type)
    {first middle last : Schema Field Kind} (step : Step first middle)
    (rest : Quiver.Path middle last) :
    composePath ((lens Leaf).mapPath ((show Quiver.Hom first middle from step).toPath.comp rest)) =
      (step.lens Leaf).comp (composePath ((lens Leaf).mapPath rest)) := by
  rw [composePath_mapPath_comp, Prefunctor.mapPath_toPath, composePath_toPath]
  rfl

/-- Writing through one path to a leaf leaves the value at every other path to a leaf unchanged. -/
theorem get_set_of_ne (Leaf : Kind -> Type) {schema : Schema Field Kind}
    {kind1 kind2 : Kind} (path1 : Quiver.Path schema (leaf kind1))
    (path2 : Quiver.Path schema (leaf kind2))
    (different : Ne (Sigma.mk kind1 path1 : Sigma fun kind => Quiver.Path schema (leaf kind))
      (Sigma.mk kind2 path2))
    (database : schema.denote Leaf) (value : Leaf kind1) :
    Lens.get (composePath ((lens Leaf).mapPath path2))
        (Lens.set (composePath ((lens Leaf).mapPath path1)) database value) =
      Lens.get (composePath ((lens Leaf).mapPath path2)) database := by
  generalize length : path1.length = n
  induction n generalizing schema value with
  | zero =>
    -- an empty path starts at a leaf, so both paths are empty
    have same := Quiver.Path.eq_of_length_zero path1 length
    subst same
    have length2 := length_eq_zero_of_path_from_leaf path2
    have kinds := Quiver.Path.eq_of_length_zero path2 length2
    cases kinds
    obtain rfl := Quiver.Path.eq_nil_of_length_zero path1 length
    obtain rfl := Quiver.Path.eq_nil_of_length_zero path2 length2
    exact absurd rfl different
  | succ n ih =>
    match Quiver.Path.eq_toPath_comp_of_length_eq_succ path1 length with
    | Exists.intro middle1 (Exists.intro step1 (Exists.intro rest1
        (Exists.intro restLength equation1))) =>
      subst equation1
      -- path2 is not empty either, since path1 shows the schema is not a leaf
      have nonzero : Ne path2.length 0 := by
        intro zero
        have same := Quiver.Path.eq_of_length_zero path2 zero
        subst same
        cases step1
      match (Quiver.Path.length_ne_zero_iff_eq_comp path2).mp nonzero with
      | Exists.intro middle2 (Exists.intro step2 (Exists.intro rest2 (And.intro equation2 _))) =>
        subst equation2
        rw [composePath_mapPath_toPath_comp, composePath_mapPath_toPath_comp]
        cases step1 with
        | field name1 isName1 =>
          cases step2 with
          | field name2 isName2 =>
            by_cases same : name1 = name2
            case pos =>
              -- the paths start with the same field, so the rests differ
              subst same
              apply Lens.comp_get_comp_set
              intro middleDatabase part
              apply ih rest1 rest2 _ middleDatabase part restLength
              intro equal
              cases equal
              exact different rfl
            case neg =>
              -- the paths start with different fields
              apply Lens.comp_get_comp_set_of_get_set
              intro whole part
              exact Lens.eval_get_set_of_ne (index := Subtype.mk name1 isName1)
                (other := Subtype.mk name2 isName2)
                (fun equal => same (congrArg Subtype.val equal)) whole part

end Schema

end TypedAuthz
