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

variable {Whole Middle Part : Type}

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

end Lens

/-- A synonym for `Type` whose morphisms are lenses instead of functions. -/
def LensCat := Type

instance : Category LensCat where
  Hom Whole Part := Lens Whole Part
  id Whole := Lens.id Whole
  comp outer inner := outer.comp inner

end TypedAuthz
