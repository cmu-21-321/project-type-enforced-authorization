import Mathlib.CategoryTheory.Category.Basic

/-! # Lenses -/

namespace TypedAuthz

open CategoryTheory

/-- `get` reads a `Part` from a `Whole`, and `set` replaces it. -/
@[ext] structure Lens (Whole Part : Type) where
  get : Whole -> Part
  set : Whole -> Part -> Whole
  /-- Reading after a write gives the written value. -/
  get_set : forall whole part, get (set whole part) = part
  /-- Writing back the current value changes nothing. -/
  set_get : forall whole, set whole (get whole) = whole
  /-- A second write replaces the first. -/
  set_set : forall whole part1 part2, set (set whole part1) part2 = set whole part2

namespace Lens

variable {Whole Middle Middle1 Middle2 Part Part1 Part2 : Type}

protected def id (Whole : Type) : Lens Whole Whole where
  get whole := whole
  set _ part := part
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Focus with `outer`, then with `inner`. -/
def comp (outer : Lens Whole Middle) (inner : Lens Middle Part) : Lens Whole Part where
  get whole := inner.get (outer.get whole)
  set whole part := outer.set whole (inner.set (outer.get whole) part)
  get_set whole part := by simp [outer.get_set, inner.get_set]
  set_get whole := by simp [outer.set_get, inner.set_get]
  set_set whole part1 part2 := by simp [outer.get_set, inner.set_set, outer.set_set]

/-- If writing through `first` leaves `second` unchanged, the same holds after putting `shared`
in front of both. -/
theorem comp_get_comp_set (shared : Lens Whole Middle)
    (first : Lens Middle Part1) (second : Lens Middle Part2)
    (unchanged : forall middle part, second.get (first.set middle part) = second.get middle)
    (whole : Whole) (part : Part1) :
    (shared.comp second).get ((shared.comp first).set whole part) =
      (shared.comp second).get whole := by
  simp only [comp, shared.get_set, unchanged]

/-- If writing through `first` leaves `second` unchanged, the same holds after following each with
another lens. -/
theorem comp_get_comp_set_of_get_set
    (first : Lens Whole Middle1) (second : Lens Whole Middle2)
    (unchanged : forall whole part, second.get (first.set whole part) = second.get whole)
    (rest1 : Lens Middle1 Part1) (rest2 : Lens Middle2 Part2) (whole : Whole) (part : Part1) :
    (second.comp rest2).get ((first.comp rest1).set whole part) =
      (second.comp rest2).get whole := by
  simp only [comp, unchanged]

variable {Index : Type} [DecidableEq Index] {Family : Index -> Type}

/-- The lens for the value of a dependent function at `index`. -/
def eval (index : Index) :
    Lens ((other : Index) -> Family other) (Family index) where
  get function := function index
  set function value := Function.update function index value
  get_set _ _ := Function.update_self _ _ _
  set_get _ := Function.update_eq_self _ _
  set_set _ _ _ := Function.update_idem _ _ _

/-- Writing at one index leaves every other index unchanged. -/
theorem eval_get_set_of_ne {index other : Index} (different : Ne index other)
    (function : (i : Index) -> Family i)
    (value : Family index) :
    (eval other).get ((eval index).set function value) = (eval other).get function :=
  Function.update_of_ne (Ne.symm different) value function

end Lens

/-- A synonym for `Type` whose morphisms are lenses instead of functions. -/
def LensCat := Type

instance : Category LensCat where
  Hom Whole Part := Lens Whole Part
  id Whole := Lens.id Whole
  comp outer inner := outer.comp inner

end TypedAuthz
