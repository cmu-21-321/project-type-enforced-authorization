import TypedAuthz.Program

/-! # Noninterference -/

namespace TypedAuthz

variable {User Input Location Database : Type} {Value : Location -> Type}
variable (policy : User -> Input -> Action -> Location -> Bool) (user : User) (input : Input)
  (lens : (location : Location) -> Lens Database (Value location))
  (independent : forall location other, Ne location other -> forall database value,
    (lens other).get ((lens location).set database value) = (lens other).get database)
  (database1 database2 : Database)
  (agree : forall location, policy user input .read location = true ->
    (lens location).get database1 = (lens location).get database2)

/-- After a check the policy allowed, every pair in the longer `checked` list is allowed. -/
theorem allowed_of_mem_cons {checked : List (Prod Action Location)} {action : Action}
    {location : Location} (allowed : policy user input action location = true)
    (checkedAllowed : forall action location, Membership.mem checked (action, location) ->
      policy user input action location = true) :
    forall action' other, Membership.mem ((action, location) :: checked) (action', other) ->
      policy user input action' other = true := by
  intro action' other member
  cases List.mem_cons.mp member with
  | inl same => cases same; exact allowed
  | inr earlier => exact checkedAllowed action' other earlier

include independent agree in
/-- Writing the same value at the same location keeps two databases in agreement on every location
the user may read. -/
theorem agree_set (location : Location) (value : Value location) :
    forall other, policy user input .read other = true ->
      (lens other).get ((lens location).set database1 value) =
        (lens other).get ((lens location).set database2 value) := by
  intro other allowed
  -- both databases get the same value at location, and other locations are untouched
  by_cases same : location = other
  case pos =>
    subst same
    rw [(lens location).get_set, (lens location).get_set]
  case neg =>
    rw [independent location other same, independent location other same]
    exact agree other allowed

include independent agree in
/-- If every location in `checked` is allowed, a program runs the same on two databases that agree
on every allowed location. -/
theorem run_eq_of_agree {checked : List (Prod Action Location)}
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
    rw [ih _ _ (agree_set policy user input lens independent database1 database2 agree location
      value) checkedAllowed]
  | @check checked Result action location yes no ihYes ihNo =>
    -- the policy ignores the database
    cases allowed : policy user input action location with
    | false => simp [Program.run, allowed, ihNo database1 database2 agree checkedAllowed]
    | true =>
      simp [Program.run, allowed, ihYes database1 database2 agree
        (allowed_of_mem_cons policy user input allowed checkedAllowed)]

include independent agree in
/-- If every location in `checked` is allowed, the final databases of two runs agree on every
allowed location when the starting databases do. -/
theorem final_agree_of_agree {checked : List (Prod Action Location)}
    (checkedAllowed : forall action location, Membership.mem checked (action, location) ->
      policy user input action location = true)
    {Result : Type} (program : Program Value checked Result) :
    forall location, policy user input .read location = true ->
      (lens location).get (program.run policy user input lens database1).2 =
        (lens location).get (program.run policy user input lens database2).2 := by
  induction program generalizing database1 database2 with
  | pure result => exact agree
  | read location isChecked next ih =>
    simp only [Program.run]
    -- a checked location holds the same value in both databases
    rw [agree location (checkedAllowed _ location isChecked)]
    exact ih _ database1 database2 agree checkedAllowed
  | write location isChecked value next ih =>
    exact ih _ _ (agree_set policy user input lens independent database1 database2 agree location
      value) checkedAllowed
  | @check checked Result action location yes no ihYes ihNo =>
    -- the policy ignores the database
    cases allowed : policy user input action location with
    | false =>
      simp only [Program.run, allowed, Bool.false_eq_true, reduceIte]
      exact ihNo database1 database2 agree checkedAllowed
    | true =>
      simp only [Program.run, allowed, reduceIte]
      exact ihYes database1 database2 agree
        (allowed_of_mem_cons policy user input allowed checkedAllowed)

include independent agree in
/-- If writing one location leaves the others unchanged, a handler gives the same result and trace
on any two databases that agree on every location the user may read. -/
theorem noninterference {Result : Type} (program : Program Value [] Result) :
    (program.run policy user input lens database1).1 =
      (program.run policy user input lens database2).1 :=
  run_eq_of_agree policy user input lens independent database1 database2 agree
    (fun _ _ member => by simp at member) program

include independent agree in
/-- If writing one location leaves the others unchanged, a handler leaves two databases that agree
on every location the user may read still agreeing on those locations. -/
theorem noninterference_final {Result : Type} (program : Program Value [] Result) :
    forall location, policy user input .read location = true ->
      (lens location).get (program.run policy user input lens database1).2 =
        (lens location).get (program.run policy user input lens database2).2 :=
  final_agree_of_agree policy user input lens independent database1 database2 agree
    (fun _ _ member => by simp at member) program

end TypedAuthz
