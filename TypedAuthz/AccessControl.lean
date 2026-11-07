import TypedAuthz.Program

/-! # Access control -/

namespace TypedAuthz

variable {User Input Location : Type} {Value : Location -> Type}

def Justified (trace : List (Event Location)) : Prop :=
  forall before location after, trace = before ++ Event.access location :: after ->
    Membership.mem before (Event.query location true)

theorem checked_or_queried (policy : Policy User Input Location) (user : User) (input : Input)
    (database : Database Value) {checked : List Location} {Result : Type}
    (program : Program Value checked Result)
    (before after : List (Event Location)) (location : Location)
    (split : (program.run policy user input database).2 =
      before ++ Event.access location :: after) :
    Membership.mem checked location \/ Membership.mem before (Event.query location true) := by
  sorry

theorem query_eq_policy (policy : Policy User Input Location) (user : User) (input : Input)
    (database : Database Value) {checked : List Location} {Result : Type}
    (program : Program Value checked Result) (location : Location) (allowed : Bool)
    (queried :
      Membership.mem (program.run policy user input database).2 (Event.query location allowed)) :
    policy user input location = allowed := by
  sorry

theorem access_checked (policy : Policy User Input Location) (user : User) (input : Input)
    (database : Database Value) {Result : Type} (program : Program Value [] Result) :
    Justified (program.run policy user input database).2 := by
  sorry

theorem access_allowed (policy : Policy User Input Location) (user : User) (input : Input)
    (database : Database Value) {Result : Type} (program : Program Value [] Result)
    (location : Location)
    (accessed :
      Membership.mem (program.run policy user input database).2 (Event.access location)) :
    policy user input location = true := by
  sorry

end TypedAuthz
