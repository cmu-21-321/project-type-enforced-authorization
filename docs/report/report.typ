#set document(title: "Type-Enforced Authorization Checks in Lean", author: "Anish Pallati")

= Introduction

Broken access control is the most common class of security vulnerability in web applications. It refers to when a path or resource that should be restricted to a certain group of users is accessible to others. Using Google Drive as an example, one instance of this vulnerability may be forgetting to check that the user deleting a document has permissions to do so.

In most backend web frameworks, these patterns are implemented via API handlers, where functions like `is_admin(requesting_user)` or `is_owner(requesting_user)` are dedicated to performing these checks. A mistake as simple as forgetting the `is_owner` call, or mistakenly calling `is_owner(document_owner)` instead, can lead to this vulnerability.

One way we can combat this is by enforcing at the type level that all data must pass through such a function before it is accessible at all. This project defines a small language of request handlers in Lean, and proves that well-typed programs cannot reveal to their user any data that the user was not permitted to read.

In this formalization, a handler runs for one user on one input, reads and writes a database, and may ask a "policy" whether one action at a given location is allowed. Reads or writes of given locations only type-check inside the branch of a check allowed by the policy.

In particular, for every policy and every handler that type-checks, we prove the following:

- Access control. A handler only reads or writes a location after asking the policy about that exact action and location, and only if the policy allowed it.
- Noninterference. If two databases agree on every location the user may read, the handler returns the same result and produces the same trace on both, and after the run, the two databases agree on those locations.

The project also handles nested data, such as a patient's chart that contains a record of their contact information. Each field is read and written through a lens, a getter and setter pair satisfying the usual lens laws. Lawful lenses form a category, which provides the composition used for paths. For example, reading through the path `contact.email` reads the contact record out of the chart and then the email out of that record, and writing through it updates the email inside the contact record and puts that record back into the chart. For noninterference to hold with writes, we also prove that writing through one path never changes the value at a different path.

= Policies and databases

- `User` is a parameter for the user making a request.
- `Input` is a parameter for the input to a request, such as the id of a document.
- `Location` is a parameter for the places a program can read or write, such as a patient's diagnosis, each holding a single value.
- `Value : Location -> Type` is a parameter that gives the type of value stored at each location.
- `Action` is an inductive type with two values, `read` and `write`.
- `Database` is a parameter for the type of the database.

A policy is a function `User -> Input -> Action -> Location -> Bool` that answers whether a given user, making a request with a given input, may perform an action at a location. For example, a psychiatric booth run by Lucy might have a policy that returns `true` for anything Lucy asks to do, `true` for anyone reading a patient's name or fee, and `false` otherwise. Note that the policy cannot see the database, since otherwise a user could learn something about hidden data just from whether their request was allowed. Anything the policy needs to make its decision, like which user owns which document in Google Drive, is part of the policy function itself.

The database itself can be any type, as long as each location comes with a lens `lens location : Lens Database (Value location)`, which a program uses to read the location with `get` and to write to it with `set`. In the simplest case, the database is a dependent function from locations to values. We then read a location by applying the function to it, and write to it using Mathlib's `Function.update`, which together form the lens `Lens.eval`. For a database of nested records, the lens for a location is built from the lenses of the fields along its path.

= Programs

- `Program Value checked Result` is an inductive type of handlers that may only act on the action and location pairs in `checked`, and that return a `Result`.
- `Event Location` is an inductive type of trace entries, each either a query to the policy or an access.

We represent a program as a tree of effects, where each continuation is an ordinary Lean function. Its four constructors, shown without their implicit arguments, correspond to returning a result, reading a location, writing to a location, and asking the policy.

```lean
inductive Program (Value : Location -> Type) :
    List (Prod Action Location) -> Type -> Type 1 where
  | pure (result : Result) : Program Value checked Result
  | read (location : Location)
      (isChecked : Membership.mem checked (Action.read, location))
      (next : Value location -> Program Value checked Result) :
      Program Value checked Result
  | write (location : Location)
      (isChecked : Membership.mem checked (Action.write, location))
      (value : Value location) (next : Program Value checked Result) :
      Program Value checked Result
  | check (action : Action) (location : Location)
      (yes : Program Value ((action, location) :: checked) Result)
      (no : Program Value checked Result) : Program Value checked Result
```

The index `checked` keeps track of which action and location pairs have already been checked by the `check`s around the current point in the program. Every handler starts with `checked = []`, so to read or write a location, a handler first has to check it and then act inside the `yes` branch. The same handler runs for every user, so `checked` cannot say whether the policy allowed a check, only that the check was made.

Running a program with `Program.run policy user input lens database program` gives back its result, a trace of what it did, and the final database. When the program reaches a `check`, it asks the policy, adds `query action location allowed` to the trace, and continues with whichever branch the policy chose. Each `read` or `write` also adds an entry to the trace, `access action location`, recording which location it touched. Everything else a handler does, like formatting a response, is ordinary Lean code inside the continuations.

In Lucy's psychiatric booth, the chart holds a patient's name, fee, and diagnosis. The program `diagnosis` checks whether the diagnosis may be read, and then either reads it or answers "The Doctor is Out". When Lucy runs it, it returns the diagnosis, and when Linus runs it on two charts that differ only in the diagnosis, it returns "The Doctor is Out" with the same trace both times. A program that tries to read the diagnosis without checking first does not type-check, since it would need a proof that `(read, diagnosis)` is in the empty list.

= Access control

The main access control theorem says that in the trace of a complete handler, every access comes after a query that allowed it.

```lean
theorem access_checked {Result : Type} (program : Program Value [] Result)
    (before after : List (Event Location)) (action : Action) (location : Location)
    (split : (program.run policy user input lens database).1.2 =
      before ++ Event.access action location :: after) :
    Membership.mem before (Event.query action location true)
```

Splitting the trace as `before ++ access :: after` lets us talk about what happened before an access without indexing into the trace.

This statement cannot be proved by induction directly, since inside a `check`, the rest of the program has a nonempty `checked` list. So we prove a more general lemma, `checked_or_queried`, that works for any `checked`. It says that each access is either to a pair already in `checked`, or comes after an approving query in the same trace. We prove it by induction on the program, generalizing over `before`, since each step applies the induction hypothesis to a shorter `before`. For a `read` or `write`, if the access is this step itself, its pair is in `checked`, since the constructor carries a proof of that. If the access happens later in the trace, the induction hypothesis covers it instead. For a `check`, the new query sits at the front of the trace, so if the induction hypothesis says the access is to the pair this check just added, this query is the one that approved it. When `checked = []`, the first case is impossible, which gives us `access_checked`.

Separately, `query_eq_policy` says that every query in a trace records the policy's answer, since `run` builds each query from `policy user input action location`. Putting this together with `access_checked` gives `access_allowed`, which says that the policy allows every access in the trace of a complete handler.

= Noninterference

The noninterference theorems share two hypotheses, which are declared once as Lean variables.

```lean
variable (independent : forall location other, Ne location other ->
    forall database value,
      (lens other).get ((lens location).set database value) = (lens other).get database)
  (agree : forall location, policy user input .read location = true ->
    (lens location).get database1 = (lens location).get database2)
```

The first, `independent`, says that writing to one location leaves the value at every other location unchanged. We prove it for flat databases in `Lens.eval_get_set_of_ne`, and for nested records in `Schema.get_set_of_ne`. The second, `agree`, says that the two databases agree everywhere the user may read. Under these two hypotheses, we prove two theorems about running the same program on both databases, `noninterference` and `noninterference_final`.

```lean
theorem noninterference {Result : Type} (program : Program Value [] Result) :
    (program.run policy user input lens database1).1 =
      (program.run policy user input lens database2).1

theorem noninterference_final {Result : Type} (program : Program Value [] Result) :
    forall location, policy user input .read location = true ->
      (lens location).get (program.run policy user input lens database1).2 =
        (lens location).get (program.run policy user input lens database2).2
```

The first says that both runs give the same result and the same trace. The second says that after the runs, the two databases agree on every location the user may read, so a run cannot copy hidden data into a location the user can read.

Both follow from more general lemmas, `run_eq_of_agree` and `final_agree_of_agree`, which allow any `checked` list whose pairs the policy allows. We run the program on both databases side by side, and since writes change the databases along the way, the induction on the program generalizes over both of them.

- For `pure`, both runs return the same result with an empty trace, and the databases agree by assumption.
- For `read`, the location is in `checked`, so the policy allows reading it, so both databases hold the same value there, and both runs then continue with the same program.
- For `write`, both databases get the same value at the same location. The lemma `agree_set` shows that the databases agree after the write as well, since reading that location gives back the written value in both by the lens law `get_set`, and every other location is unchanged by independence.
- For `check`, the policy does not depend on the database, so both runs take the same branch. In the `yes` branch, the new pair is allowed, so the lemma `allowed_of_mem_cons` shows that every pair in the longer `checked` list is allowed too.

= Lenses and nested data

- `Lens Whole Part` is a structure for lenses from `Whole` to `Part`, with the lens laws as fields.
- `LensCat` is a synonym for `Type` whose morphisms are lenses.

```lean
@[ext] structure Lens (Whole Part : Type) where
  get : Whole -> Part
  set : Whole -> Part -> Whole
  get_set : forall whole part, get (set whole part) = part
  set_get : forall whole, set whole (get whole) = whole
  set_set : forall whole part1 part2, set (set whole part1) part2 = set whole part2
```

The composite of two lenses focuses with the first and then with the second, and each of its laws follows from the laws of the two lenses by `simp`. Lenses form a category on `LensCat` rather than on `Type` itself, because Mathlib already makes `Type` a category whose morphisms are functions. Since composing with the identity lens or regrouping a composition gives back the same `get` and `set` functions, the identity and associativity laws hold by definition, and we did not have to prove them by hand.

- `Schema Field Kind` is an inductive type describing the shape of nested records.
- `Leaf : Kind -> Type` is a family giving the type of value stored at each kind of leaf.
- `Schema.Step` is an inductive type of steps from a record into one of its fields.

A leaf holds a single value labeled by a kind from `Kind`, and a node is a record with a list of field names from `Field`, each with its own schema. `denote` gives the type of databases with a given schema, where a record is a dependent function from its fields to their values. We give schemas a Mathlib `Quiver` instance whose arrows are steps, so we can use Mathlib's `Quiver.Path` for paths and `Quiver.Path.comp` to join them. `Schema.lens` gives each step the lens `Lens.eval` at the field it goes into, and Mathlib's `Paths.lift` extends this to a functor out of the path category, which we use to get the lens for a whole path. Because it is a functor, Mathlib's `Functor.map_comp` tells us that the lens for two joined paths is the composite of their lenses.

We only count paths that end at a leaf as locations, because a program that could read a whole record would also get any hidden fields inside it. In that case, assuming the databases agree at readable locations would also assume that those hidden fields agree.

Our main theorem about nested data, `Schema.get_set_of_ne`, says that writing through one path to a leaf does not change the value at any other path to a leaf. The proof is by induction on the length of the first path. If the first path is empty, the schema must be a leaf, and a path starting at a leaf has no steps, so both paths are empty and therefore equal, which contradicts the assumption. Otherwise, both paths start with a step out of the same record, and Mathlib's `eq_toPath_comp_of_length_eq_succ` splits off that first step. If both steps go into the same field, the rest of the paths must differ, so the induction hypothesis applies after the shared field lens, using `Lens.comp_get_comp_set`. If they go into different fields, `Function.update_of_ne` shows that writing to one field leaves the other unchanged. `Lens.comp_get_comp_set_of_get_set` then extends this from the two field lenses to the full paths, which follow each field with the rest of its path. The examples use this theorem to apply `noninterference` to a program that updates an email address inside a nested chart.

= Design decisions

== Traces

We compare traces in the noninterference theorem as well as results. In practice, a handler's code is often public, and someone who can tell which checks and reads a request went through could learn more from that than from the result alone.

== Program representation

Using Lean functions as continuations, instead of an imperative language with local variables, expressions, and conditionals, saves us from defining a separate expression language or a store of variables, and lets a location depend on the input or on something read earlier. However, Lean cannot print a function or check whether two functions are equal, so we cannot do either for programs.

== Check evidence

When we write a handler, we do not know which user will call it, so its type can only record which checks it makes, not a proof that the policy allowed them.

== Value types

If the whole database shared one value type, such as a sum of strings and numbers, every program that reads a fee would also have to handle the case where it gets a string. Giving each location its own type avoids this, although agreement then cannot be stated with Mathlib's `Set.EqOn`, which needs a single value type.

== Database access

We could have written to a flat database directly with `Function.update`, but that needs decidable equality on locations. Paths do not have decidable equality, since a record's schema contains a function, so this would not work for nested records. Going through a lens for each location works for both kinds of database, but then the noninterference theorems need the `independent` hypothesis, which we prove for paths in `Schema.get_set_of_ne`.

== Result type

We put the result type last among the arguments of `Program`, so that programs could later be made into a monad. Since `checked` changes between constructors, it has to be an index, and so the result type after it has to be an index too. Every constructor then takes the result type as an argument, and a constructor argument of type `Type` puts `Program` in `Type 1`.

== Leaf kinds

If a leaf held its type directly instead of a kind, schemas would contain types and live in `Type 1`, and so would paths. Locations have to live in `Type`, so we label leaves with kinds and give their types separately with `Leaf : Kind -> Type`.

= Limitations

- Public data still has to be checked before a program reads it.
- Authorization decisions cannot depend on stored data, and authorization state cannot change during a run.
- Each theorem is about a single run, so if a user who may write a location copies data they can read into a location another user can read, the theorems do not rule this out.
- There are no loops, so every program terminates and `run` is defined by structural recursion.

= Inspiration and acknowledgments

We use the notion of noninterference introduced by Goguen and Meseguer in "Security Policies and Security Models" (IEEE Symposium on Security and Privacy, 1982), in the form for programs surveyed by Sabelfeld and Myers in "Language-Based Information-Flow Security" (IEEE Journal on Selected Areas in Communications 21(1), 2003).

We rely on Mathlib (The mathlib Community, "The Lean Mathematical Library", CPP 2020) for quivers and path categories, category theory, and lemmas about `Function.update`.
