import TypedAuthz.Program

/-! # Access control -/

namespace TypedAuthz

variable {User Input Location : Type} {Value : Location -> Type}

/-- Each location a program reads was either checked before it started, or allowed by a query earlier in the trace. -/
theorem checked_or_queried (policy : User -> Input -> Location -> Bool) (user : User)
    (input : Input) (database : (location : Location) -> Value location)
    {checked : List Location} {Result : Type}
    (program : Program Value checked Result)
    (before after : List (Event Location)) (location : Location)
    (split : (program.run policy user input database).2 =
      before ++ Event.access location :: after) :
    Membership.mem checked location \/ Membership.mem before (Event.query location true) := by
  -- each case passes the tail of before to the hypothesis
  induction program generalizing before with
  | pure result => simp [Program.run] at split
  | @read checked Result location' isChecked next ih =>
    simp only [Program.run] at split
    -- whether the access is this read or a later one
    cases before with
    | nil =>
      simp at split
      rw [<- split.1]
      exact Or.inl isChecked
    | cons event before' =>
      simp at split
      exact (ih _ before' split.2).imp_right (List.mem_cons_of_mem _)
  | @check checked Result location' yes no ihYes ihNo =>
    simp only [Program.run] at split
    cases before with
    | nil => simp at split
    | cons event before' =>
      cases allowed : policy user input location' with
      | false =>
        simp [allowed] at split
        exact (ihNo before' split.2).imp_right (List.mem_cons_of_mem _)
      | true =>
        simp [allowed] at split
        cases ihYes before' split.2 with
        | inl member =>
          cases List.mem_cons.mp member with
          | inl same =>
            -- the location this check just allowed
            rw [<- split.1, same]
            exact Or.inr (List.mem_cons_self ..)
          | inr earlier => exact Or.inl earlier
        | inr queried => exact Or.inr (List.mem_cons_of_mem _ queried)

/-- Each query in the trace records `policy user input location`. -/
theorem query_eq_policy (policy : User -> Input -> Location -> Bool) (user : User)
    (input : Input) (database : (location : Location) -> Value location)
    {checked : List Location} {Result : Type}
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
theorem access_checked (policy : User -> Input -> Location -> Bool) (user : User)
    (input : Input) (database : (location : Location) -> Value location) {Result : Type}
    (program : Program Value [] Result)
    (before after : List (Event Location)) (location : Location)
    (split : (program.run policy user input database).2 =
      before ++ Event.access location :: after) :
    Membership.mem before (Event.query location true) := by
  cases checked_or_queried policy user input database program before after location split with
  | inl member => simp at member
  | inr queried => exact queried

/-- A handler reads only locations the policy allows. -/
theorem access_allowed (policy : User -> Input -> Location -> Bool) (user : User)
    (input : Input) (database : (location : Location) -> Value location) {Result : Type}
    (program : Program Value [] Result)
    (location : Location)
    (accessed :
      Membership.mem (program.run policy user input database).2 (Event.access location)) :
    policy user input location = true := by
  match List.append_of_mem accessed with
  | Exists.intro before (Exists.intro after split) =>
    have queried := access_checked policy user input database program before after location split
    apply query_eq_policy policy user input database program location true
    rw [split]
    exact List.mem_append_left _ queried

end TypedAuthz
