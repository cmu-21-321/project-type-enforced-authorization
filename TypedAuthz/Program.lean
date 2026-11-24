import TypedAuthz.Lens

/-! # Programs with authorization checks -/

namespace TypedAuthz

variable {User Input Location Database : Type} {Value : Location -> Type}

inductive Action | read | write

/-- A request handler that may do an action at a location only if that pair is in `checked`. -/
inductive Program (Value : Location -> Type) : List (Prod Action Location) -> Type -> Type 1 where
  | pure {checked : List (Prod Action Location)} {Result : Type} (result : Result) :
      Program Value checked Result
  /-- Reads `location`, which must be checked for reading. -/
  | read {checked : List (Prod Action Location)} {Result : Type} (location : Location)
      (isChecked : Membership.mem checked (Action.read, location))
      (next : Value location -> Program Value checked Result) : Program Value checked Result
  /-- Writes `value` to `location`, which must be checked for writing. -/
  | write {checked : List (Prod Action Location)} {Result : Type} (location : Location)
      (isChecked : Membership.mem checked (Action.write, location)) (value : Value location)
      (next : Program Value checked Result) : Program Value checked Result
  /-- Asks the policy whether `action` is allowed at `location`. If allowed, runs `yes`, which may
  also do `action` at `location`. Otherwise runs `no`. -/
  | check {checked : List (Prod Action Location)} {Result : Type} (action : Action)
      (location : Location) (yes : Program Value ((action, location) :: checked) Result)
      (no : Program Value checked Result) : Program Value checked Result

/-- An entry in a run's trace. -/
inductive Event (Location : Type) where
  /-- The policy answered `allowed` for `action` at `location`. -/
  | query (action : Action) (location : Location) (allowed : Bool)
  /-- The program did `action` at `location`. -/
  | access (action : Action) (location : Location)

/-- Runs `program` for `user` with `input` against `database`, reading and writing each location
through `lens`, and gives its result, its trace, and the final database. -/
def Program.run (policy : User -> Input -> Action -> Location -> Bool) (user : User)
    (input : Input) (lens : (location : Location) -> Lens Database (Value location))
    (database : Database) {checked : List (Prod Action Location)} {Result : Type} :
    Program Value checked Result -> Prod (Prod Result (List (Event Location))) Database
  | .pure result => ((result, []), database)
  | .read location _ next =>
      let rest := run policy user input lens database (next ((lens location).get database))
      ((rest.1.1, .access .read location :: rest.1.2), rest.2)
  | .write location _ value next =>
      let rest := run policy user input lens ((lens location).set database value) next
      ((rest.1.1, .access .write location :: rest.1.2), rest.2)
  | .check action location yes no =>
      let allowed := policy user input action location
      let rest :=
        if allowed then run policy user input lens database yes
        else run policy user input lens database no
      ((rest.1.1, .query action location allowed :: rest.1.2), rest.2)

end TypedAuthz
