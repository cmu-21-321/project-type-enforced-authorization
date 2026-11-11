/-! # Programs with authorization checks -/

namespace TypedAuthz

variable {User Input Location : Type} {Value : Location -> Type}

/-- Whether a user may read a location, given the request input. -/
abbrev Policy (User Input Location : Type) := User -> Input -> Location -> Bool

/-- A database maps each `location` to a value of type `Value location`. -/
abbrev Database (Value : Location -> Type) := (location : Location) -> Value location

/-- A request handler that may read only the locations in `checked`. -/
inductive Program (Value : Location -> Type) : List Location -> Type -> Type 1 where
  | pure {checked : List Location} {Result : Type} (result : Result) :
      Program Value checked Result
  /-- Reads `location`, which must be in `checked`. -/
  | read {checked : List Location} {Result : Type} (location : Location)
      (isChecked : Membership.mem checked location)
      (next : Value location -> Program Value checked Result) : Program Value checked Result
  /-- Asks the policy about `location`. If allowed, runs `yes`, which may also read `location`. Otherwise runs `no`. -/
  | check {checked : List Location} {Result : Type} (location : Location)
      (yes : Program Value (location :: checked) Result) (no : Program Value checked Result) :
      Program Value checked Result

/-- An entry in a run's trace. -/
inductive Event (Location : Type) where
  /-- The policy answered `allowed` for `location`. -/
  | query (location : Location) (allowed : Bool)
  /-- The program read `location`. -/
  | access (location : Location)

/-- Runs `program` for `user` with `input` against `database`, giving its result and trace. -/
def Program.run (policy : Policy User Input Location) (user : User) (input : Input)
    (database : Database Value) {checked : List Location} {Result : Type} :
    Program Value checked Result -> Prod Result (List (Event Location))
  | .pure result => (result, [])
  | .read location _ next =>
      let rest := run policy user input database (next (database location))
      (rest.1, .access location :: rest.2)
  | .check location yes no =>
      let allowed := policy user input location
      let rest :=
        if allowed then run policy user input database yes else run policy user input database no
      (rest.1, .query location allowed :: rest.2)

end TypedAuthz
