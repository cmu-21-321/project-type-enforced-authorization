import TypedAuthz.Program

/-! # Access control -/

namespace TypedAuthz

variable {User Input Location : Type} {Value : Location -> Type}

/-- Every access in the trace comes after an allowed query of the same location. -/
def Justified (trace : List (Event Location)) : Prop :=
  forall before location after, trace = before ++ Event.access location :: after ->
    Membership.mem before (Event.query location true)

/-- Each location a program reads was either checked before it started, or allowed by a query earlier in the trace. -/
theorem checked_or_queried (policy : Policy User Input Location) (user : User) (input : Input)
    (database : Database Value) {checked : List Location} {Result : Type}
    (program : Program Value checked Result)
    (before after : List (Event Location)) (location : Location)
    (split : (program.run policy user input database).2 =
      before ++ Event.access location :: after) :
    Membership.mem checked location \/ Membership.mem before (Event.query location true) := by
  sorry

/-- Each query in the trace records `policy user input location`. -/
theorem query_eq_policy (policy : Policy User Input Location) (user : User) (input : Input)
    (database : Database Value) {checked : List Location} {Result : Type}
    (program : Program Value checked Result) (location : Location) (allowed : Bool)
    (queried :
      Membership.mem (program.run policy user input database).2 (Event.query location allowed)) :
    policy user input location = allowed := by
  induction program with
  | pure result => simp [Program.run] at queried
  | read location' isChecked next ih =>
    simp [Program.run] at queried
    exact ih _ queried
  | check location' yes no ihYes ihNo =>
    simp [Program.run] at queried
    cases queried with
    | inl same =>
      -- the query this check just recorded
      rw [same.1]
      exact same.2.symm
    | inr queried =>
      -- a query from whichever branch ran
      split at queried
      . exact ihYes queried
      . exact ihNo queried

/-- A handler checks every location before reading it. -/
theorem access_checked (policy : Policy User Input Location) (user : User) (input : Input)
    (database : Database Value) {Result : Type} (program : Program Value [] Result) :
    Justified (program.run policy user input database).2 := by
  sorry

/-- A handler reads only locations the policy allows. -/
theorem access_allowed (policy : Policy User Input Location) (user : User) (input : Input)
    (database : Database Value) {Result : Type} (program : Program Value [] Result)
    (location : Location)
    (accessed :
      Membership.mem (program.run policy user input database).2 (Event.access location)) :
    policy user input location = true := by
  sorry

end TypedAuthz
