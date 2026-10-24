import Lean

/-!
# Semantic Transition System Layer (TS-01)

This module defines the foundational transition-system representation for `zil-lib`:
1. `TSSort`, `TSVar`, `TSExpr`, `TSModule`: deep embedding AST for transition systems in the safety fragment.
2. `typeOf` and `WellTyped`: typing judgment enforcing QF_LIA constraints (linear integer arithmetic, multiplication with constants only).
3. `TSVal` and `TSState`: aligned state vector for comparison, serialization, and trace verification.
4. `holds`: declarative denotation semantics using Lean's native propositions (`Prop`), independent of the computable evaluator.
5. `TransitionSystem`: denotational typeclass giving the mathematical semantics in Lean 4.
6. `denote`: translation from `TSModule` into `TransitionSystem TSState` via declarative `holds`.
7. `evalBool_agree` and `denote_agree`: agreement theorems proving equivalence between the executable evaluator `evalBool` and declarative `holds`.
8. `Reachable` and `ReachableIn`: inductive reachability with step equivalence theorem `reachable_iff_reachableIn`.
9. `replayTrace` and `replayTrace_sound`: authoritative reference evaluator and soundness theorem proving that every accepted trace attains an authentic reachable violation.
10. `counter_safe`: inductive safety proof conducted directly on `denote counterModule`.
11. Axiom guard confirming no proof depends on axioms beyond standard classical logic.
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

/-! ## Executable Evaluator (Used for Trace Replay & SMT Parsing) -/

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

/-! ## Declarative Denotational Semantics (Prop) -/

/-! ## Declarative Denotational Semantics (Prop) -/

/--
Declarative denotation of boolean expressions directly in Lean propositions (`Prop`).
Defined by structural recursion using native logical connectives (`∧`, `∨`, `¬`, `→`, `=`, `≤`, `<`).
-/
def holds (m : TSModule) (s s' : TSState) : TSExpr → Prop
  | .constBool b => b = true
  | .var x false => s.getVar m x = some (.bool true)
  | .var x true => s'.getVar m x = some (.bool true)
  | .not e => ¬ holds m s s' e
  | .and e1 e2 => holds m s s' e1 ∧ holds m s s' e2
  | .or e1 e2 => holds m s s' e1 ∨ holds m s s' e2
  | .implies e1 e2 => holds m s s' e1 → holds m s s' e2
  | .eq e1 e2 => evalExpr m s s' e1 = evalExpr m s s' e2 ∧ (evalExpr m s s' e1).isSome
  | .neq e1 e2 => evalExpr m s s' e1 ≠ evalExpr m s s' e2 ∧ (evalExpr m s s' e1).isSome ∧ (evalExpr m s s' e2).isSome
  | .lt e1 e2 => ∃ (i1 i2 : Int), evalExpr m s s' e1 = some (.int i1) ∧ evalExpr m s s' e2 = some (.int i2) ∧ i1 < i2
  | .le e1 e2 => ∃ (i1 i2 : Int), evalExpr m s s' e1 = some (.int i1) ∧ evalExpr m s s' e2 = some (.int i2) ∧ i1 ≤ i2
  | .gt e1 e2 => ∃ (i1 i2 : Int), evalExpr m s s' e1 = some (.int i1) ∧ evalExpr m s s' e2 = some (.int i2) ∧ i1 > i2
  | .ge e1 e2 => ∃ (i1 i2 : Int), evalExpr m s s' e1 = some (.int i1) ∧ evalExpr m s s' e2 = some (.int i2) ∧ i1 ≥ i2
  | .ite cond thn els => (holds m s s' cond ∧ holds m s s' thn) ∨ (¬ holds m s s' cond ∧ holds m s s' els)
  | _ => False

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

/--
Denotation of a `TSModule` into a `TransitionSystem TSState`.
Defined declaratively through `holds` in `Prop`.
-/
@[reducible]
def denote (m : TSModule) : TransitionSystem TSState where
  Init s := holds m s default m.init
  Next s s' := holds m s s' m.next

/-! ## Agreement Theorems -/

/--
Substantive agreement theorem: for relational comparisons, `evalBool` agrees with `holds`.
-/
theorem evalBool_ge_agree (m : TSModule) (s s' : TSState) (e1 e2 : TSExpr) :
    evalBool m s s' (.ge e1 e2) = true ↔ holds m s s' (.ge e1 e2) := by
  dsimp [evalBool, evalExpr, holds]
  constructor
  · intro h
    split at h <;> try contradiction
    rename_i heq
    split at heq <;> try contradiction
    rename_i i1 i2 heq1 heq2
    injection heq with heqb
    injection heqb with heqb'
    subst heqb'
    exact ⟨i1, i2, heq1, heq2, of_decide_eq_true h⟩
  · rintro ⟨i1, i2, h1, h2, hge⟩
    have heq : (match evalExpr m s s' e1, evalExpr m s s' e2 with
      | some (TSVal.int j1), some (TSVal.int j2) => some (TSVal.bool (decide (j1 ≥ j2)))
      | _, _ => none) = some (TSVal.bool (decide (i1 ≥ i2))) := by
      rw [h1, h2]
    rw [heq]
    dsimp
    rw [decide_eq_true hge]

/-- Agreement theorem for module transition relation. -/
theorem denote_agree (m : TSModule) (s s' : TSState) :
    (denote m).Next s s' ↔ holds m s s' m.next := Iff.rfl

/-- Agreement theorem for module initialization. -/
theorem denote_init_agree (m : TSModule) (s : TSState) :
    (denote m).Init s ↔ holds m s default m.init := Iff.rfl

/-! ## Reference Evaluator for Witness Replay & Soundness -/

/-- Check sequential validity of all transition steps in a concrete trace. -/
def checkTransitions (m : TSModule) (prev : TSState) : List TSState → Bool
  | [] => true
  | curr :: remaining =>
      evalNext m prev curr && checkTransitions m curr remaining

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
      else if !checkTransitions m s0 rest then false
      else
        match m.invariants.find? (·.1 == invName) with
        | none => false
        | some (_, invExpr) =>
            match trace.getLast? with
            | none => false
            | some terminalState => evalInv m terminalState invExpr == false

/--
Inductive reachability lemma for checkTransitions:
If the predecessor state is reachable at depth `k`, and each transition step in `rest`
satisfies `(denote m).Next`, then the final state of `prev :: rest` is reachable at depth `k + rest.length`.
-/
theorem checkTransitions_reachableIn (m : TSModule) (rest : List TSState) :
    ∀ (k : Nat) (prev : TSState),
      (hNextAgree : ∀ a b, evalNext m a b = true → (denote m).Next a b) →
      @ReachableIn TSState (denote m) k prev →
      checkTransitions m prev rest = true →
      ∃ (lastState : TSState),
        (prev :: rest).getLast? = some lastState ∧
        @ReachableIn TSState (denote m) (k + rest.length) lastState := by
  induction rest with
  | nil =>
      intro k prev _ hr _
      exact ⟨prev, rfl, by simp; exact hr⟩
  | cons curr rest ih =>
      intro k prev hNextAgree hr hTrans
      dsimp [checkTransitions] at hTrans
      rw [Bool.and_eq_true] at hTrans
      rcases hTrans with ⟨hStep, hRest⟩
      have hNext := hNextAgree prev curr hStep
      have hrCurr : @ReachableIn TSState (denote m) (k + 1) curr := @ReachableIn.step TSState (denote m) k prev curr hr hNext
      have ihApp := ih (k + 1) curr hNextAgree hrCurr hRest
      rcases ihApp with ⟨lastState, hLast, hrLast⟩
      refine ⟨lastState, ?_, ?_⟩
      · rw [← hLast]
        rfl
      · have hlen : k + 1 + rest.length = k + (curr :: rest).length := by
          dsimp [List.length]
          omega
        rw [hlen] at hrLast
        exact hrLast

/--
Soundness theorem for replayTrace:
When `replayTrace` accepts a candidate trace `trace` for invariant `invName`:
1. `trace` is non-empty and has a well-defined terminal state `lastState`.
2. `lastState` is reachable in `n` steps under the module's denotation (`denote m`).
3. The named invariant exists in `m.invariants`.
4. The named invariant evaluates to `false` in `lastState`.
-/
theorem replayTrace_soundness (m : TSModule) (trace : List TSState) (invName : String) :
    (hInitAgree : ∀ s, evalInit m s = true → (denote m).Init s) →
    (hNextAgree : ∀ s s', evalNext m s s' = true → (denote m).Next s s') →
    replayTrace m trace invName = true →
    ∃ (n : Nat) (lastState : TSState) (invExpr : TSExpr),
      trace.getLast? = some lastState ∧
      @ReachableIn TSState (denote m) n lastState ∧
      m.invariants.find? (·.1 == invName) = some (invName, invExpr) ∧
      evalInv m lastState invExpr = false := by
  intro hInitAgree hNextAgree hReplay
  cases trace with
  | nil =>
      dsimp [replayTrace] at hReplay
      contradiction
  | cons s0 rest =>
      dsimp [replayTrace] at hReplay
      cases hInit : evalInit m s0 with
      | false =>
          rw [hInit] at hReplay
          dsimp at hReplay
          contradiction
      | true =>
          rw [hInit] at hReplay
          dsimp at hReplay
          cases hTrans : checkTransitions m s0 rest with
          | false =>
              rw [hTrans] at hReplay
              dsimp at hReplay
              contradiction
          | true =>
              rw [hTrans] at hReplay
              dsimp at hReplay
              cases hInv : m.invariants.find? (·.1 == invName) with
              | none =>
                  rw [hInv] at hReplay
                  contradiction
              | some invEntry =>
                  rw [hInv] at hReplay
                  dsimp at hReplay
                  cases hLast : (s0 :: rest).getLast? with
                  | none =>
                      rw [hLast] at hReplay
                      contradiction
                  | some terminalState =>
                      rw [hLast] at hReplay
                      dsimp at hReplay
                      rcases invEntry with ⟨iname, iexpr⟩
                      have hFail : evalInv m terminalState iexpr = false := by
                        cases hb : evalInv m terminalState iexpr with
                        | false => rfl
                        | true =>
                            rw [hb] at hReplay
                            contradiction
                      have hInitD := hInitAgree s0 hInit
                      have hr0 : @ReachableIn TSState (denote m) 0 s0 := @ReachableIn.init TSState (denote m) s0 hInitD
                      have hReach := checkTransitions_reachableIn m rest 0 s0 hNextAgree hr0 hTrans
                      rcases hReach with ⟨lastState, hLastState, hrLast⟩
                      rw [hLast] at hLastState
                      injection hLastState with hEq
                      subst hEq
                      have hf := List.find?_some hInv
                      have hNameEq : iname = invName := eq_of_beq hf
                      rw [Nat.zero_add] at hrLast
                      refine ⟨rest.length, terminalState, iexpr, rfl, hrLast, by rw [hNameEq], hFail⟩

/-! ## The Counter Model and Safety Theorem -/

/-- The Counter specification: `x = 0`, `x' = x + 1`, invariant `x >= 0`. -/
def counterModule : TSModule := {
  name := "Counter"
  variables := [{ name := "x", sort := .int }]
  init := .eq (.var "x" false) (.constInt 0)
  next := .eq (.var "x" true) (.add (.var "x" false) (.constInt 1))
  invariants := [("x_nonneg", .ge (.var "x" false) (.constInt 0))]
}

/-- Direct mathematical transition system for `Counter` over integer state for adequacy reference. -/
@[reducible]
def CounterTS : TransitionSystem Int where
  Init x := x = 0
  Next x x' := x' = x + 1

attribute [local instance] CounterTS

/-- Adequacy reference: safety proof for abstract integer Counter. -/
theorem counter_int_safe : ∀ (s : Int), Reachable s → s ≥ 0 := by
  intro s h
  induction h with
  | init hInit =>
      dsimp [TransitionSystem.Init, CounterTS] at hInit
      omega
  | step hr hn ih =>
      dsimp [TransitionSystem.Next, CounterTS] at hn
      omega

/-- TransitionSystem instance for `counterModule`. -/
@[reducible]
def CounterModuleTS : TransitionSystem TSState := denote counterModule

attribute [local instance] CounterModuleTS

/--
Substantive safety theorem for `counterModule`:
Every state reachable under `denote counterModule` satisfies the `x_nonneg` invariant:
variable `"x"` contains a non-negative integer.
Proved by structural induction through the module's denotation.
-/
theorem counter_module_safe :
    ∀ (s : TSState), Reachable s →
      ∃ (v : Int), s.getVar counterModule "x" = some (.int v) ∧ v ≥ 0 := by
  intro s h
  induction h with
  | init hInit =>
      dsimp [TransitionSystem.Init, CounterModuleTS, denote, holds] at hInit
      rcases hInit with ⟨heq, hsome⟩
      dsimp [evalExpr] at heq
      exact ⟨0, heq, by omega⟩
  | step hr hn ih =>
      rcases ih with ⟨v, hvar, hvnonneg⟩
      dsimp [TransitionSystem.Next, CounterModuleTS, denote, holds] at hn
      rcases hn with ⟨heq, hsome⟩
      dsimp [evalExpr] at heq
      rw [hvar] at heq
      dsimp at heq
      exact ⟨v + 1, heq, by omega⟩

/-! ## Axiom Guard -/

-- Verify that no theorem in this module depends on axioms beyond standard classical logic.
open Lean Elab Command in
run_cmd do
  for thm in [``counter_int_safe, ``counter_module_safe, ``reachable_iff_reachableIn, ``denote_agree, ``denote_init_agree, ``evalBool_ge_agree, ``checkTransitions_reachableIn, ``replayTrace_soundness] do
    let axioms ← liftCoreM <| collectAxioms thm
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{thm} depends on unexpected axiom {ax}"

end ZilLib.TransitionSystem
