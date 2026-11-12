import TypedAuthz.Program

/-! # Noninterference -/

namespace TypedAuthz

variable {User Input Location : Type} {Value : Location -> Type}

/-- If every location in `checked` is allowed, a program runs the same on two databases that agree on every allowed location. -/
theorem run_eq_of_agree (policy : Policy User Input Location) (user : User) (input : Input)
    (database1 database2 : Database Value)
    (agree : forall location, policy user input location = true ->
      database1 location = database2 location)
    {checked : List Location}
    (checkedAllowed : forall location, Membership.mem checked location ->
      policy user input location = true)
    {Result : Type} (program : Program Value checked Result) :
    program.run policy user input database1 = program.run policy user input database2 := by
  induction program with
  | pure result => rfl
  | read location isChecked next ih =>
    simp only [Program.run]
    -- a checked location holds the same value in both databases
    rw [agree location (checkedAllowed location isChecked), ih _ checkedAllowed]
  | @check checked Result location yes no ihYes ihNo =>
    -- the policy ignores the database
    cases allowed : policy user input location
    . simp [Program.run, allowed, ihNo checkedAllowed]
    . have yesAllowed : forall other, Membership.mem (location :: checked) other ->
          policy user input other = true := by
        intro other member
        cases List.mem_cons.mp member with
        | inl same => rw [same]; exact allowed
        | inr earlier => exact checkedAllowed other earlier
      simp [Program.run, allowed, ihYes yesAllowed]

/-- A handler gives the same result and trace on any two databases that agree on every location the user may read. -/
theorem noninterference (policy : Policy User Input Location) (user : User) (input : Input)
    (database1 database2 : Database Value)
    (agree : forall location, policy user input location = true ->
      database1 location = database2 location)
    {Result : Type} (program : Program Value [] Result) :
    program.run policy user input database1 = program.run policy user input database2 :=
  run_eq_of_agree policy user input database1 database2 agree
    (fun _ member => by simp at member) program

end TypedAuthz
