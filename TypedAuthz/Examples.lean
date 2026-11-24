import TypedAuthz.Noninterference
import TypedAuthz.Schema

/-! # Example: Lucy's psychiatric booth -/

namespace TypedAuthz.Examples

inductive Peanut | charlieBrown | lucy | linus

inductive Field | name | fee | diagnosis
  deriving DecidableEq

abbrev FieldValue : Field -> Type
  | .name => String
  | .fee => Nat
  | .diagnosis => String

/-- Only Lucy may read a diagnosis or change the chart. -/
def booth : Peanut -> Unit -> Action -> Field -> Bool
  | .lucy, _, _, _ => true
  | _, _, .read, .diagnosis => false
  | _, _, .read, _ => true
  | _, _, .write, _ => false

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
  .check .read .name
    (.check .read .fee
      (.read .name (by simp) fun name =>
        .read .fee (by simp) fun fee =>
          .pure s!"{name} owes {fee} cents")
      (.pure "no fee"))
    (.pure "no name")

def diagnosis : Program FieldValue [] String :=
  .check .read .diagnosis
    (.read .diagnosis (by simp) .pure)
    (.pure "The Doctor is Out")

def rediagnose : Program FieldValue [] String :=
  .check .write .diagnosis
    (.write .diagnosis (by simp) "hypengyophobia" (.pure "rediagnosed"))
    (.pure "only Lucy can do that")

example : (bill.run booth .charlieBrown () Lens.eval chart).1 =
    ("Charlie Brown owes 5 cents",
      [.query .read .name true, .query .read .fee true, .access .read .name, .access .read .fee]) :=
  rfl

example : (diagnosis.run booth .lucy () Lens.eval chart).1 =
    ("pantophobia", [.query .read .diagnosis true, .access .read .diagnosis]) := rfl
example : (diagnosis.run booth .lucy () Lens.eval revisedChart).1 =
    ("hypengyophobia", [.query .read .diagnosis true, .access .read .diagnosis]) := rfl

example : (diagnosis.run booth .linus () Lens.eval chart).1 =
    ("The Doctor is Out", [.query .read .diagnosis false]) := rfl
example : (diagnosis.run booth .linus () Lens.eval revisedChart).1 =
    ("The Doctor is Out", [.query .read .diagnosis false]) := rfl

example : (rediagnose.run booth .lucy () Lens.eval chart).1 =
    ("rediagnosed", [.query .write .diagnosis true, .access .write .diagnosis]) := rfl
example : (rediagnose.run booth .lucy () Lens.eval chart).2 .diagnosis = "hypengyophobia" := rfl
example : (rediagnose.run booth .linus () Lens.eval chart).1 =
    ("only Lucy can do that", [.query .write .diagnosis false]) := rfl
example : (rediagnose.run booth .linus () Lens.eval chart).2 .diagnosis = "pantophobia" := rfl

-- rejected, since reading `.diagnosis` was never checked
-- def leak : Program FieldValue [] String := .read .diagnosis (by simp) .pure

/-! ## A nested chart -/

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

/-- The lens for a path to a value in the nested chart. -/
def chartLens (path : Quiver.Path patient (Schema.leaf ())) :
    Lens (patient.denote (fun _ => String)) String :=
  (CategoryTheory.Paths.lift (Schema.lens (fun _ => String))).map path

example : (chartLens emailPath).get nestedChart = "cb@peanuts.com" := rfl
example : (chartLens emailPath).get ((chartLens emailPath).set nestedChart "charlie@peanuts.com") =
    "charlie@peanuts.com" := rfl
example : (chartLens phonePath).get ((chartLens emailPath).set nestedChart "charlie@peanuts.com") =
    "555-0100" := rfl

/-- Everyone may read the nested chart, but only Lucy may change it. -/
def contactPolicy : Peanut -> Unit -> Action -> Quiver.Path patient (Schema.leaf ()) -> Bool
  | .lucy, _, _, _ => true
  | _, _, .read, _ => true
  | _, _, .write, _ => false

def updateEmail :
    Program (fun (_ : Quiver.Path patient (Schema.leaf ())) => String) [] String :=
  .check .write emailPath
    (.write emailPath (by simp) "charlie@peanuts.com" (.pure "updated"))
    (.pure "only Lucy can do that")

example : (updateEmail.run contactPolicy .lucy () chartLens nestedChart).1.1 = "updated" := rfl
example :
    (chartLens emailPath).get (updateEmail.run contactPolicy .lucy () chartLens nestedChart).2 =
    "charlie@peanuts.com" := rfl
example : (updateEmail.run contactPolicy .linus () chartLens nestedChart).1.1 =
    "only Lucy can do that" := rfl
example :
    (chartLens emailPath).get (updateEmail.run contactPolicy .linus () chartLens nestedChart).2 =
    "cb@peanuts.com" := rfl

-- noninterference for the nested chart, with distinct paths independent by `get_set_of_ne`
example (user : Peanut) (chart1 chart2 : patient.denote (fun _ => String))
    (agree : forall path, contactPolicy user () .read path = true ->
      (chartLens path).get chart1 = (chartLens path).get chart2) :
    (updateEmail.run contactPolicy user () chartLens chart1).1 =
      (updateEmail.run contactPolicy user () chartLens chart2).1 :=
  noninterference contactPolicy user () chartLens
    (fun path other different => Schema.get_set_of_ne (fun _ => String) path other
      (fun equal => different (@sigma_mk_injective Unit
        (fun kind => Quiver.Path patient (Schema.leaf kind)) () path other equal)))
    chart1 chart2 agree updateEmail

end TypedAuthz.Examples
