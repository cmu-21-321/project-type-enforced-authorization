import TypedAuthz.Program

/-! # Access control -/

namespace TypedAuthz

variable {User Input Location : Type} {Value : Location -> Type}

def Justified (trace : List (Event Location)) : Prop :=
  forall before location after, trace = before ++ Event.access location :: after ->
    List.Mem (Event.query location true) before

theorem access_checked (policy : Policy User Input Location) (user : User) (input : Input)
    (database : Database Value) {Result : Type} (program : Program Value [] Result) :
    Justified (program.run policy user input database).2 := by
  sorry

theorem access_allowed (policy : Policy User Input Location) (user : User) (input : Input)
    (database : Database Value) {Result : Type} (program : Program Value [] Result)
    (location : Location)
    (accessed : List.Mem (Event.access location) (program.run policy user input database).2) :
    policy user input location = true := by
  sorry

end TypedAuthz
