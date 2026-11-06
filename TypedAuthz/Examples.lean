import TypedAuthz.Program

/-! # Example: Lucy's psychiatric booth -/

namespace TypedAuthz.Examples

deriving instance Repr for Event

inductive Peanut | charlieBrown | lucy | linus

inductive Field | name | fee | diagnosis
  deriving Repr

abbrev FieldValue : Field -> Type
  | .name => String
  | .fee => Nat
  | .diagnosis => String

def booth : Policy Peanut Unit Field
  | .lucy, _, _ => true
  | _, _, .diagnosis => false
  | _, _, _ => true

def chart : Database FieldValue
  | .name => "Charlie Brown"
  | .fee => 5
  | .diagnosis => "pantophobia"

def revisedChart : Database FieldValue
  | .name => "Charlie Brown"
  | .fee => 5
  | .diagnosis => "hypengyophobia"

def bill : Program FieldValue [] String :=
  .check .name
    (.check .fee
      (.read .name (by simp) fun name =>
        .read .fee (by simp) fun fee =>
          .pure s!"{name} owes {fee} cents")
      (.pure "no fee"))
    (.pure "no name")

def diagnosis : Program FieldValue [] String :=
  .check .diagnosis
    (.read .diagnosis (by simp) .pure)
    (.pure "The Doctor is Out")

#eval bill.run booth .charlieBrown () chart

#eval diagnosis.run booth .lucy () chart
#eval diagnosis.run booth .lucy () revisedChart

#eval diagnosis.run booth .linus () chart
#eval diagnosis.run booth .linus () revisedChart

-- rejected, since `.diagnosis` is not in the empty checked list
-- def leak : Program FieldValue [] String := .read .diagnosis (by simp) .pure

end TypedAuthz.Examples
