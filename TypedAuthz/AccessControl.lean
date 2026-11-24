import TypedAuthz.Program

/-! # Access control -/

namespace TypedAuthz

variable {User Input Location Database : Type} {Value : Location -> Type}
variable (policy : User -> Input -> Action -> Location -> Bool) (user : User) (input : Input)
  (lens : (location : Location) -> Lens Database (Value location)) (database : Database)

/-- Each action a program does at a location was either checked before it started, or allowed by a
query earlier in the trace. -/
theorem checked_or_queried {checked : List (Prod Action Location)} {Result : Type}
    (program : Program Value checked Result)
    (before after : List (Event Location)) (action : Action) (location : Location)
    (split : (program.run policy user input lens database).1.2 =
      before ++ Event.access action location :: after) :
    Membership.mem checked (action, location) \/
      Membership.mem before (Event.query action location true) := by
  -- each case passes the tail of before to the hypothesis
  induction program generalizing database before with
  | pure result => simp [Program.run] at split
  | @read checked Result location' isChecked next ih =>
    simp only [Program.run] at split
    -- whether the access is this read or a later one
    cases before with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, Event.access.injEq] at split
      rw [<- split.1.1, <- split.1.2]
      exact Or.inl isChecked
    | cons event before' =>
      simp only [List.cons_append, List.cons.injEq] at split
      exact (ih _ _ before' split.2).imp_right (List.mem_cons_of_mem _)
  | @write checked Result location' isChecked value next ih =>
    simp only [Program.run] at split
    -- whether the access is this write or a later one
    cases before with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, Event.access.injEq] at split
      rw [<- split.1.1, <- split.1.2]
      exact Or.inl isChecked
    | cons event before' =>
      simp only [List.cons_append, List.cons.injEq] at split
      exact (ih _ before' split.2).imp_right (List.mem_cons_of_mem _)
  | @check checked Result action' location' yes no ihYes ihNo =>
    simp only [Program.run] at split
    cases before with
    | nil => simp at split
    | cons event before' =>
      cases allowed : policy user input action' location' with
      | false =>
        simp only [allowed, Bool.false_eq_true, reduceIte, List.cons_append, List.cons.injEq]
          at split
        exact (ihNo database before' split.2).imp_right (List.mem_cons_of_mem _)
      | true =>
        simp only [allowed, reduceIte, List.cons_append, List.cons.injEq] at split
        cases ihYes database before' split.2 with
        | inl member =>
          cases List.mem_cons.mp member with
          | inl same =>
            -- the action and location this check just allowed
            cases same
            rw [<- split.1]
            exact Or.inr (List.mem_cons_self ..)
          | inr earlier => exact Or.inl earlier
        | inr queried => exact Or.inr (List.mem_cons_of_mem _ queried)

/-- Each query in the trace records `policy user input action location`. -/
theorem query_eq_policy {checked : List (Prod Action Location)} {Result : Type}
    (program : Program Value checked Result) (action : Action) (location : Location)
    (allowed : Bool)
    (queried : Membership.mem (program.run policy user input lens database).1.2
      (Event.query action location allowed)) :
    policy user input action location = allowed := by
  induction program generalizing database with
  | pure result => simp [Program.run] at queried
  | read location' isChecked next ih =>
    simp only [Program.run, List.mem_cons, reduceCtorEq, false_or] at queried
    exact ih _ _ queried
  | write location' isChecked value next ih =>
    simp only [Program.run, List.mem_cons, reduceCtorEq, false_or] at queried
    exact ih _ queried
  | check action' location' yes no ihYes ihNo =>
    simp only [Program.run, List.mem_cons, Event.query.injEq] at queried
    cases queried with
    | inl same =>
      -- the query this check just recorded
      rw [same.1, same.2.1]
      exact same.2.2.symm
    | inr queried =>
      -- a query from whichever branch ran
      split at queried
      next => exact ihYes _ queried
      next => exact ihNo _ queried

/-- A handler checks every action at a location before doing it. -/
theorem access_checked {Result : Type} (program : Program Value [] Result)
    (before after : List (Event Location)) (action : Action) (location : Location)
    (split : (program.run policy user input lens database).1.2 =
      before ++ Event.access action location :: after) :
    Membership.mem before (Event.query action location true) := by
  cases checked_or_queried policy user input lens database program before after action location
    split with
  | inl member => simp at member
  | inr queried => exact queried

/-- A handler does only the actions the policy allows. -/
theorem access_allowed {Result : Type} (program : Program Value [] Result)
    (action : Action) (location : Location)
    (accessed : Membership.mem (program.run policy user input lens database).1.2
      (Event.access action location)) :
    policy user input action location = true := by
  match List.append_of_mem accessed with
  | Exists.intro before (Exists.intro after split) =>
    have queried :=
      access_checked policy user input lens database program before after action location split
    apply query_eq_policy policy user input lens database program action location true
    rw [split]
    exact List.mem_append_left _ queried

end TypedAuthz
