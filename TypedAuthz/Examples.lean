import TypedAuthz.Noninterference
import TypedAuthz.Schema

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

/-- Only Lucy may read a diagnosis. -/
def booth : Peanut -> Unit -> Field -> Bool
  | .lucy, _, _ => true
  | _, _, .diagnosis => false
  | _, _, _ => true

def chart : (field : Field) -> FieldValue field
  | .name => "Charlie Brown"
  | .fee => 5
  | .diagnosis => "pantophobia"

/-- `chart` with a different diagnosis. -/
def revisedChart : (field : Field) -> FieldValue field
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

/-! ## A nested chart -/

example {Key Kind : Type} [DecidableEq Key] {User Input : Type} {Leaf : Kind -> Type}
    {schema : Schema Key Kind}
    (policy : User -> Input -> (Sigma fun kind => Quiver.Path schema (.leaf kind)) -> Bool)
    (user : User) (input : Input) (database1 database2 : schema.denote Leaf)
    (agree : forall location, policy user input location = true ->
      Lens.get (CategoryTheory.composePath ((Schema.lens Leaf).mapPath location.2)) database1 =
        Lens.get (CategoryTheory.composePath ((Schema.lens Leaf).mapPath location.2)) database2)
    {Result : Type}
    (program : Program (fun (location : Sigma fun kind => Quiver.Path schema (.leaf kind)) =>
      Leaf location.1) [] Result) :
    program.run policy user input (fun location =>
        Lens.get (CategoryTheory.composePath ((Schema.lens Leaf).mapPath location.2)) database1) =
      program.run policy user input (fun location =>
        Lens.get (CategoryTheory.composePath ((Schema.lens Leaf).mapPath location.2)) database2) :=
  noninterference policy user input _ _ agree program

inductive ChartField | name | contact | email | phone
  deriving DecidableEq

def contactFields : ChartField -> Schema ChartField Unit := fun _ => .leaf ()

def chartFields : ChartField -> Schema ChartField Unit
  | .contact => .node [.email, .phone] contactFields
  | _ => .leaf ()

def patient : Schema ChartField Unit := .node [.name, .contact] chartFields

def nestedChart : patient.denote (fun _ => String) := fun
  | Subtype.mk .name _ => "Charlie Brown"
  | Subtype.mk .contact _ => fun
    | Subtype.mk .email _ => "cb@peanuts.com"
    | Subtype.mk .phone _ => "555-0100"

def emailPath : Quiver.Path patient (Schema.leaf ()) :=
  (Quiver.Path.nil.cons
      (Schema.Step.field (child := chartFields) ChartField.contact (by simp))).cons
    (Schema.Step.field (child := contactFields) ChartField.email (by simp))

def phonePath : Quiver.Path patient (Schema.leaf ()) :=
  (Quiver.Path.nil.cons
      (Schema.Step.field (child := chartFields) ChartField.contact (by simp))).cons
    (Schema.Step.field (child := contactFields) ChartField.phone (by simp))

def emailLens : Lens (patient.denote (fun _ => String)) String :=
  CategoryTheory.composePath ((Schema.lens (fun _ => String)).mapPath emailPath)

def phoneLens : Lens (patient.denote (fun _ => String)) String :=
  CategoryTheory.composePath ((Schema.lens (fun _ => String)).mapPath phonePath)

#eval emailLens.get nestedChart
#eval emailLens.get (emailLens.set nestedChart "charlie@peanuts.com")
#eval phoneLens.get (emailLens.set nestedChart "charlie@peanuts.com")

end TypedAuthz.Examples
