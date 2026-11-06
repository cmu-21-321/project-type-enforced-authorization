/-! # Programs with authorization checks -/

namespace TypedAuthz

variable {User Input Location : Type} {Value : Location -> Type}

abbrev Policy (User Input Location : Type) := User -> Input -> Location -> Bool

abbrev Database (Value : Location -> Type) := (location : Location) -> Value location

inductive Program (Value : Location -> Type) : List Location -> Type -> Type 1 where
  | pure {checked : List Location} {Result : Type} (result : Result) :
      Program Value checked Result
  | read {checked : List Location} {Result : Type} (location : Location)
      (isChecked : Membership.mem checked location)
      (next : Value location -> Program Value checked Result) : Program Value checked Result
  | check {checked : List Location} {Result : Type} (location : Location)
      (yes : Program Value (location :: checked) Result) (no : Program Value checked Result) :
      Program Value checked Result

inductive Event (Location : Type) where
  | query (location : Location) (allowed : Bool)
  | access (location : Location)

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
