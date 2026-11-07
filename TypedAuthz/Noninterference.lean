import TypedAuthz.Program

/-! # Noninterference -/

namespace TypedAuthz

variable {User Input Location : Type} {Value : Location -> Type}

theorem run_eq_of_agree (policy : Policy User Input Location) (user : User) (input : Input)
    (database1 database2 : Database Value)
    (agree : forall location, policy user input location = true ->
      database1 location = database2 location)
    {checked : List Location}
    (checkedAllowed : forall location, Membership.mem checked location ->
      policy user input location = true)
    {Result : Type} (program : Program Value checked Result) :
    program.run policy user input database1 = program.run policy user input database2 := by
  sorry

theorem noninterference (policy : Policy User Input Location) (user : User) (input : Input)
    (database1 database2 : Database Value)
    (agree : forall location, policy user input location = true ->
      database1 location = database2 location)
    {Result : Type} (program : Program Value [] Result) :
    program.run policy user input database1 = program.run policy user input database2 := by
  sorry

end TypedAuthz
