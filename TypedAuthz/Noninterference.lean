import TypedAuthz.Program

/-! # Noninterference -/

namespace TypedAuthz

variable {User Input Location : Type} {Value : Location -> Type}

theorem noninterference (policy : Policy User Input Location) (user : User) (input : Input)
    (database1 database2 : Database Value)
    (agree : forall location, policy user input location = true ->
      database1 location = database2 location)
    {Result : Type} (program : Program Value [] Result) :
    program.run policy user input database1 = program.run policy user input database2 := by
  sorry

end TypedAuthz
