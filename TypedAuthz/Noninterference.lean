import TypedAuthz.Program

/-! # Noninterference -/

namespace TypedAuthz

variable {User Input Location Database : Type} {Value : Location -> Type}

/-- If every location in `checked` is allowed, a program runs the same on two databases that agree
on every allowed location. -/
theorem run_eq_of_agree (policy : User -> Input -> Action -> Location -> Bool) (user : User)
    (input : Input) (lens : (location : Location) -> Lens Database (Value location))
    (independent : forall location other, Ne location other -> forall database value,
      (lens other).get ((lens location).set database value) = (lens other).get database)
    (database1 database2 : Database)
    (agree : forall location, policy user input .read location = true ->
      (lens location).get database1 = (lens location).get database2)
    {checked : List (Prod Action Location)}
    (checkedAllowed : forall action location, Membership.mem checked (action, location) ->
      policy user input action location = true)
    {Result : Type} (program : Program Value checked Result) :
    (program.run policy user input lens database1).1 =
      (program.run policy user input lens database2).1 := by
  induction program generalizing database1 database2 with
  | pure result => rfl
  | read location isChecked next ih =>
    simp only [Program.run]
    -- a checked location holds the same value in both databases
    rw [agree location (checkedAllowed _ location isChecked),
      ih _ database1 database2 agree checkedAllowed]
  | write location isChecked value next ih =>
    simp only [Program.run]
    rw [ih ((lens location).set database1 value) ((lens location).set database2 value) ?_
      checkedAllowed]
    -- both databases get the same value at location, and other locations are untouched
    intro other allowed
    by_cases same : location = other
    case pos =>
      subst same
      rw [(lens location).get_set, (lens location).get_set]
    case neg =>
      rw [independent location other same, independent location other same]
      exact agree other allowed
  | @check checked Result action location yes no ihYes ihNo =>
    -- the policy ignores the database
    cases allowed : policy user input action location with
    | false => simp [Program.run, allowed, ihNo database1 database2 agree checkedAllowed]
    | true =>
      have yesAllowed : forall action' other,
          Membership.mem ((action, location) :: checked) (action', other) ->
          policy user input action' other = true := by
        intro action' other member
        cases List.mem_cons.mp member with
        | inl same => cases same; exact allowed
        | inr earlier => exact checkedAllowed action' other earlier
      simp [Program.run, allowed, ihYes database1 database2 agree yesAllowed]

/-- If writing one location leaves the others unchanged, a handler gives the same result and trace
on any two databases that agree on every location the user may read. -/
theorem noninterference (policy : User -> Input -> Action -> Location -> Bool) (user : User)
    (input : Input) (lens : (location : Location) -> Lens Database (Value location))
    (independent : forall location other, Ne location other -> forall database value,
      (lens other).get ((lens location).set database value) = (lens other).get database)
    (database1 database2 : Database)
    (agree : forall location, policy user input .read location = true ->
      (lens location).get database1 = (lens location).get database2)
    {Result : Type} (program : Program Value [] Result) :
    (program.run policy user input lens database1).1 =
      (program.run policy user input lens database2).1 :=
  run_eq_of_agree policy user input lens independent database1 database2 agree
    (fun _ _ member => by simp at member) program

end TypedAuthz
