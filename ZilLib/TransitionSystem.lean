import Lean

/-!
# Semantic Transition System Layer (TS-01)

This module defines the foundational transition-system representation for `zil-lib`:
1. `TSSort`, `TSVar`, `TSExpr`, `TSModule`: deep embedding AST for transition systems in the safety fragment.
2. `typeOf` and `WellTyped`: typing judgment enforcing QF_LIA constraints (linear multiplication with constants).
3. `TSVal` and `TSState`: aligned state vector for comparison, serialization, and trace verification.
4. `TransitionSystem`: denotational typeclass giving the mathematical semantics in Lean 4.
5. `Reachable` and `ReachableIn`: inductive reachability with equivalence theorem `reachable_iff_reachableIn`.
6. `denote`: translation from the deep embedding `TSModule` into a `TransitionSystem TSState`.
7. `denote_agree`: agreement theorem between AST evaluation and denotation semantics.
8. `replayTrace`: bounded reachability reference evaluator in Lean.
9. `Counter` example and `counter_safe` proved by induction.
10. Axiom guard confirming no proof depends on axioms beyond standard classical logic.
-/

namespace ZilLib.TransitionSystem

/-- Supported types in the safety fragment. -/
inductive TSSort where
  | bool : TSSort
  | int : TSSort
  | enumSort (name : String) (elements : List String) : TSSort
deriving Inhabited, BEq, Repr, DecidableEq

/-- A typed state variable. -/
structure TSVar where
  name : String
  sort : TSSort
deriving Inhabited, BEq, Repr, DecidableEq

/-- Expressions in the safety fragment. Primed variables denote next-state values. -/
inductive TSExpr where
  | constBool (b : Bool) : TSExpr
  | constInt (i : Int) : TSExpr
  | constEnum (sortName : String) (val : String) : TSExpr
  | var (name : String) (primed : Bool) : TSExpr
  | not (e : TSExpr) : TSExpr
  | and (e1 e2 : TSExpr) : TSExpr
  | or (e1 e2 : TSExpr) : TSExpr
  | implies (e1 e2 : TSExpr) : TSExpr
  | eq (e1 e2 : TSExpr) : TSExpr
  | neq (e1 e2 : TSExpr) : TSExpr
  | lt (e1 e2 : TSExpr) : TSExpr
  | le (e1 e2 : TSExpr) : TSExpr
  | gt (e1 e2 : TSExpr) : TSExpr
  | ge (e1 e2 : TSExpr) : TSExpr
  | add (e1 e2 : TSExpr) : TSExpr
  | sub (e1 e2 : TSExpr) : TSExpr
  | mul (e1 e2 : TSExpr) : TSExpr
  | ite (cond thn els : TSExpr) : TSExpr
deriving Inhabited, BEq, Repr, DecidableEq

/-- A discrete transition system specification AST. -/
structure TSModule where
  name : String
  variables : List TSVar
  init : TSExpr
  next : TSExpr
  invariants : List (String × TSExpr)
deriving Inhabited, BEq, Repr, DecidableEq

/-- Dynamic runtime values during trace evaluation. -/
inductive TSVal where
  | bool (b : Bool) : TSVal
  | int (i : Int) : TSVal
  | enumVal (sortName : String) (val : String) : TSVal
deriving Inhabited, BEq, Repr, DecidableEq

/--
State vector aligned by index with `m.variables`.
Comparing two states is a direct vector equality check (`s1 == s2`).
-/
structure TSState where
  values : Array TSVal
deriving Inhabited, BEq, Repr, DecidableEq

/-- Find the variable index in a module. -/
def TSModule.indexOfVar (m : TSModule) (varName : String) : Option Nat :=
  m.variables.findIdx? (·.name == varName)

/-- Look up a variable in a state by name according to module schema. -/
def TSState.getVar (m : TSModule) (s : TSState) (varName : String) : Option TSVal :=
  match m.indexOfVar varName with
  | some idx => s.values[idx]?
  | none => none

/-- Update a state variable by name. -/
def TSState.setVar (m : TSModule) (s : TSState) (varName : String) (v : TSVal) : TSState :=
  match m.indexOfVar varName with
  | some idx => if idx < s.values.size then ⟨s.values.set! idx v⟩ else s
  | none => s

/-- Static type synthesis and check for QF_LIA compliance. -/
def typeOf (m : TSModule) : TSExpr → Option TSSort
  | .constBool _ => some .bool
  | .constInt _ => some .int
  | .constEnum sn _ =>
      match m.variables.find? (fun v => match v.sort with | .enumSort n _ => n == sn | _ => false) with
      | some v => some v.sort
      | none => some (.enumSort sn [])
  | .var x _ => (m.variables.find? (·.name == x)).map (·.sort)
  | .not e => match typeOf m e with | some .bool => some .bool | _ => none
  | .and e1 e2 | .or e1 e2 | .implies e1 e2 =>
      match typeOf m e1, typeOf m e2 with
      | some .bool, some .bool => some .bool
      | _, _ => none
  | .eq e1 e2 | .neq e1 e2 =>
      match typeOf m e1, typeOf m e2 with
      | some t1, some t2 => if t1 == t2 then some .bool else none
      | _, _ => none
  | .lt e1 e2 | .le e1 e2 | .gt e1 e2 | .ge e1 e2 =>
      match typeOf m e1, typeOf m e2 with
      | some .int, some .int => some .bool
      | _, _ => none
  | .add e1 e2 | .sub e1 e2 =>
      match typeOf m e1, typeOf m e2 with
      | some .int, some .int => some .int
      | _, _ => none
  | .mul e1 e2 =>
      match typeOf m e1, typeOf m e2 with
      | some .int, some .int =>
          -- Enforce QF_LIA: at least one operand must be a constant integer
          if (match e1 with | .constInt _ => true | _ => false) ||
             (match e2 with | .constInt _ => true | _ => false) then
            some .int
          else none
      | _, _ => none
  | .ite cond thn els =>
      match typeOf m cond, typeOf m thn, typeOf m els with
      | some .bool, some t1, some t2 => if t1 == t2 then some t1 else none
      | _, _, _ => none

/-- Proposition that an expression is well-typed under module `m`. -/
def WellTyped (m : TSModule) (e : TSExpr) (expectedSort : TSSort) : Prop :=
  typeOf m e = some expectedSort

/-- Evaluate an expression in current state `s` (unprimed) and next state `s'` (primed). -/
def evalExpr (m : TSModule) (s s' : TSState) : TSExpr → Option TSVal
  | .constBool b => some (.bool b)
  | .constInt i => some (.int i)
  | .constEnum sn v => some (.enumVal sn v)
  | .var x false => s.getVar m x
  | .var x true => s'.getVar m x
  | .not e => match evalExpr m s s' e with
    | some (.bool b) => some (.bool (!b))
    | _ => none
  | .and e1 e2 => match evalExpr m s s' e1, evalExpr m s s' e2 with
    | some (.bool b1), some (.bool b2) => some (.bool (b1 && b2))
    | _, _ => none
  | .or e1 e2 => match evalExpr m s s' e1, evalExpr m s s' e2 with
    | some (.bool b1), some (.bool b2) => some (.bool (b1 || b2))
    | _, _ => none
  | .implies e1 e2 => match evalExpr m s s' e1, evalExpr m s s' e2 with
    | some (.bool b1), some (.bool b2) => some (.bool (!b1 || b2))
    | _, _ => none
  | .eq e1 e2 => match evalExpr m s s' e1, evalExpr m s s' e2 with
    | some v1, some v2 => some (.bool (v1 == v2))
    | _, _ => none
  | .neq e1 e2 => match evalExpr m s s' e1, evalExpr m s s' e2 with
    | some v1, some v2 => some (.bool (v1 != v2))
    | _, _ => none
  | .lt e1 e2 => match evalExpr m s s' e1, evalExpr m s s' e2 with
    | some (.int i1), some (.int i2) => some (.bool (i1 < i2))
    | _, _ => none
  | .le e1 e2 => match evalExpr m s s' e1, evalExpr m s s' e2 with
    | some (.int i1), some (.int i2) => some (.bool (i1 <= i2))
    | _, _ => none
  | .gt e1 e2 => match evalExpr m s s' e1, evalExpr m s s' e2 with
    | some (.int i1), some (.int i2) => some (.bool (i1 > i2))
    | _, _ => none
  | .ge e1 e2 => match evalExpr m s s' e1, evalExpr m s s' e2 with
    | some (.int i1), some (.int i2) => some (.bool (i1 >= i2))
    | _, _ => none
  | .add e1 e2 => match evalExpr m s s' e1, evalExpr m s s' e2 with
    | some (.int i1), some (.int i2) => some (.int (i1 + i2))
    | _, _ => none
  | .sub e1 e2 => match evalExpr m s s' e1, evalExpr m s s' e2 with
    | some (.int i1), some (.int i2) => some (.int (i1 - i2))
    | _, _ => none
  | .mul e1 e2 => match evalExpr m s s' e1, evalExpr m s s' e2 with
    | some (.int i1), some (.int i2) => some (.int (i1 * i2))
    | _, _ => none
  | .ite cond thn els => match evalExpr m s s' cond with
    | some (.bool true) => evalExpr m s s' thn
    | some (.bool false) => evalExpr m s s' els
    | _ => none

/-- Evaluate a boolean expression in context of module `m`. -/
def evalBool (m : TSModule) (s s' : TSState) (e : TSExpr) : Bool :=
  match evalExpr m s s' e with
  | some (.bool b) => b
  | _ => false

/-- Evaluate the initial predicate of a module. -/
def evalInit (m : TSModule) (s : TSState) : Bool :=
  evalBool m s default m.init

/-- Evaluate the transition predicate of a module from `s` to `s'`. -/
def evalNext (m : TSModule) (s s' : TSState) : Bool :=
  evalBool m s s' m.next

/-- Evaluate an invariant predicate of a module in state `s`. -/
def evalInv (m : TSModule) (s : TSState) (invExpr : TSExpr) : Bool :=
  evalBool m s default invExpr

/-! ## Denotational Semantics -/

/-- The denotational class for transition systems in Lean 4. -/
class TransitionSystem (α : Type) where
  Init : α → Prop
  Next : α → α → Prop

/-- Inductive definition of reachable states. -/
inductive Reachable [TransitionSystem α] : α → Prop where
  | init {s : α} (h : TransitionSystem.Init s) : Reachable s
  | step {s s' : α} (hr : Reachable s) (hn : TransitionSystem.Next s s') : Reachable s'

/-- Step-bounded reachability for replay and k-induction. -/
inductive ReachableIn [TransitionSystem α] : Nat → α → Prop where
  | init {s : α} (h : TransitionSystem.Init s) : ReachableIn 0 s
  | step {n : Nat} {s s' : α} (hr : ReachableIn n s) (hn : TransitionSystem.Next s s') : ReachableIn (n + 1) s'

/-- Agreement theorem: Reachable is equivalent to step-bounded reachability at some depth n. -/
theorem reachable_iff_reachableIn [TransitionSystem α] (s : α) :
    Reachable s ↔ ∃ n, ReachableIn n s := by
  constructor
  · intro hr
    induction hr with
    | init h => exact ⟨0, .init h⟩
    | step hr hn ih =>
        rcases ih with ⟨n, hIn⟩
        exact ⟨n + 1, .step hIn hn⟩
  · rintro ⟨n, hIn⟩
    induction hIn with
    | init h => exact .init h
    | step hr hn ih => exact .step ih hn

/-- Denotation of a `TSModule` into a `TransitionSystem TSState`. -/
@[reducible]
def denote (m : TSModule) : TransitionSystem TSState where
  Init s := evalInit m s = true
  Next s s' := evalNext m s s' = true

/-- Agreement theorem: Initial predicate evaluation in deep embedding agrees with denotation. -/
theorem denote_init_agree (m : TSModule) (s : TSState) :
    (denote m).Init s ↔ evalInit m s = true := Iff.rfl

/-- Agreement theorem: Transition relation evaluation in deep embedding agrees with denotation. -/
theorem denote_next_agree (m : TSModule) (s s' : TSState) :
    (denote m).Next s s' ↔ evalNext m s s' = true := Iff.rfl

/-- Agreement theorem: `evalNext` evaluates to true if and only if `Next` holds in the denotation. -/
theorem denote_agree (m : TSModule) (s s' : TSState) :
    (denote m).Next s s' ↔ evalNext m s s' = true := Iff.rfl

/-! ## Reference Evaluator for Witness Replay -/

/--
Authoritative reference evaluator in Lean for replaying solver-produced traces.
Given a trace of concrete states `[s0, s1, ..., sk]` and the name of an invariant:
1. Verifies that `evalInit m s0 = true`.
2. Verifies that for every step $i$, `evalNext m s_i s_{i+1} = true`.
3. Verifies that the terminal state `sk` violates the named invariant (`evalInv m sk inv = false`).
Returns `true` if and only if the candidate trace is a genuine, verified counterexample.
-/
def replayTrace (m : TSModule) (trace : List TSState) (invName : String) : Bool :=
  match trace with
  | [] => false
  | s0 :: rest =>
      if !evalInit m s0 then false
      else
        let rec checkTransitions (prev : TSState) : List TSState → Bool
          | [] => true
          | curr :: remaining =>
              if !evalNext m prev curr then false
              else checkTransitions curr remaining
        if !checkTransitions s0 rest then false
        else
          match m.invariants.find? (·.1 == invName) with
          | none => false
          | some (_, invExpr) =>
              let terminalState := trace.getLast!
              evalInv m terminalState invExpr == false

/-! ## The Counter Model and Safety Theorem -/

/-- The Counter specification: `x = 0`, `x' = x + 1`, invariant `x >= 0`. -/
def counterModule : TSModule := {
  name := "Counter"
  variables := [{ name := "x", sort := .int }]
  init := .eq (.var "x" false) (.constInt 0)
  next := .eq (.var "x" true) (.add (.var "x" false) (.constInt 1))
  invariants := [("x_nonneg", .ge (.var "x" false) (.constInt 0))]
}

/-- Direct mathematical transition system for `Counter` over integer state. -/
@[reducible]
def CounterTS : TransitionSystem Int where
  Init x := x = 0
  Next x x' := x' = x + 1

attribute [local instance] CounterTS

/--
Safety proof for `Counter`: every reachable state is non-negative (`s >= 0`).
Proved by ordinary induction over `Reachable`.
-/
theorem counter_safe : ∀ (s : Int), Reachable s → s ≥ 0 := by
  intro s h
  induction h with
  | init hInit =>
      dsimp [TransitionSystem.Init, CounterTS] at hInit
      omega
  | step hr hn ih =>
      dsimp [TransitionSystem.Next, CounterTS] at hn
      omega

/-! ## Axiom Guard -/

-- Verify that no theorem in this module depends on axioms beyond standard classical logic.
open Lean Elab Command in
run_cmd do
  for thm in [``counter_safe, ``reachable_iff_reachableIn, ``denote_agree, ``denote_init_agree, ``denote_next_agree] do
    let axioms ← liftCoreM <| collectAxioms thm
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{thm} depends on {ax}"

end ZilLib.TransitionSystem
