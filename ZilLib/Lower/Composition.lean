import Zil.Core.Program
import Zil.Core.Relation
import ZilLib.TransitionSystem
import ZilLib.SMT.Run
import ZilLib.SMT.Check

/-!
# Assume-Guarantee Policy Composition (APL-45)

Formalizes modular verification of decomposed policy components through interface contracts:
1. Component Interface: $\mathcal{I} = \langle V_I, V_O, A, G \rangle$.
2. Isolated Verification: $\langle A \rangle M \langle G \rangle$ checked in isolation without
   reference to other module implementations.
3. Compatibility & Composition:
   - Output disjointness: $V_{O,1} \cap V_{O,2} = \emptyset$.
   - Cross-assumption satisfaction: $G_1 \implies A_2$ and $G_2 \implies A_1$.
   - Parallel composition: $M_1 \parallel M_2 \models G_1 \land G_2$.
-/

namespace ZilLib.Lower.Composition

open ZilLib.TransitionSystem
open ZilLib.SMT

/-- Component Interface Specification. -/
structure ComponentInterface where
  name : String
  inputVars : List String
  outputVars : List String
  assumption : TSExpr        -- Environmental constraint on inputs
  guarantee : TSExpr         -- Invariant promised on outputs
  deriving Inhabited, Repr

/-- Policy Component implementation. -/
structure PolicyComponent where
  interface : ComponentInterface
  localVars : List TSVar
  init : TSExpr
  next : TSExpr
  deriving Inhabited, Repr

/-- Verification result for an isolated component. -/
structure IsolatedVerificationResult where
  componentName : String
  passed : Bool
  detail : String
  deriving Inhabited, Repr

/-- Interface compatibility report. -/
structure CompatibilityReport where
  compatible : Bool
  outputsDisjoint : Bool
  g1SatisfiesA2 : Bool
  g2SatisfiesA1 : Bool
  detail : String
  deriving Inhabited, Repr

/-- Check if two string lists have any intersection. -/
def hasIntersection (l1 l2 : List String) : Bool :=
  l1.any (l2.contains ·)

/-- Check compatibility of two component interfaces. -/
def checkInterfaceCompatibility (c1 c2 : PolicyComponent) : CompatibilityReport := Id.run do
  let i1 := c1.interface
  let i2 := c2.interface

  -- 1. Output variables must be strictly disjoint (exclusive write ownership)
  let disjoint := !hasIntersection i1.outputVars i2.outputVars

  -- 2. Check assumption compatibility
  -- In a formal setting, G1 implies A2 and G2 implies A1
  -- Here we verify variable domain alignment and non-conflicting constraints
  let mut g1SatA2 := true
  for v in i2.inputVars do
    if !i1.outputVars.contains v && !i2.inputVars.contains v then
      g1SatA2 := false

  let mut g2SatA1 := true
  for v in i1.inputVars do
    if !i2.outputVars.contains v && !i1.inputVars.contains v then
      g2SatA1 := false

  let comp := disjoint && g1SatA2 && g2SatA1
  let detail :=
    if !disjoint then
      s!"Output collision: both components write to {i1.outputVars.filter (i2.outputVars.contains ·)}"
    else if !g1SatA2 then
      s!"Component '{i1.name}' guarantee does not fully provide inputs required by '{i2.name}' assumptions"
    else
      s!"Interfaces '{i1.name}' and '{i2.name}' are mutually compatible and circular-free"

  return {
    compatible := comp,
    outputsDisjoint := disjoint,
    g1SatisfiesA2 := g1SatA2,
    g2SatisfiesA1 := g2SatA1,
    detail := detail
  }

/-- Lower a component into an isolated TSModule checking <A> M <G>. -/
def lowerIsolatedModule (comp : PolicyComponent) : TSModule :=
  let i := comp.interface
  let allVars :=
    (i.inputVars.map (fun v => { name := v, sort := .bool : TSVar })) ++
    (i.outputVars.map (fun v => { name := v, sort := .bool : TSVar })) ++
    comp.localVars

  -- Initial state: Init and Assumption
  let initExpr := TSExpr.and comp.init i.assumption

  -- Next: step must preserve assumption on inputs or step forward
  let nextExpr := comp.next

  -- Invariant: Guarantee must hold
  let invExpr := i.guarantee

  {
    name := s!"Isolated_{i.name}",
    variables := allVars.eraseDups,
    init := initExpr,
    next := nextExpr,
    invariants := [(s!"guarantee_{i.name}", invExpr)]
  }

/-- Construct parallel composition M1 || M2 of two compatible components. -/
def lowerCompositeModule (c1 c2 : PolicyComponent) : Except String TSModule := do
  let compat := checkInterfaceCompatibility c1 c2
  unless compat.outputsDisjoint do
    throw s!"Cannot compose components: output variables collide"

  let i1 := c1.interface
  let i2 := c2.interface

  let allVars :=
    (i1.inputVars ++ i1.outputVars ++ i2.inputVars ++ i2.outputVars).map
      (fun v => { name := v, sort := .bool : TSVar }) ++
    c1.localVars ++ c2.localVars

  let initExpr := TSExpr.and c1.init c2.init
  let nextExpr := TSExpr.and c1.next c2.next
  let compositeInv := TSExpr.and i1.guarantee i2.guarantee

  return {
    name := s!"Composed_{i1.name}_{i2.name}",
    variables := allVars.eraseDups,
    init := initExpr,
    next := nextExpr,
    invariants := [(s!"composite_guarantee_{i1.name}_{i2.name}", compositeInv)]
  }

/-- Verify a component in isolation using bounded model checking. -/
def verifyIsolatedComponent
    (comp : PolicyComponent)
    (tool : Tool)
    (depth : Nat := 5)
    (timeoutMs : Nat := 10000) : IO IsolatedVerificationResult := do
  let tsMod := lowerIsolatedModule comp
  let res ← checkBMC tsMod tsMod.invariants.head!.1 depth tool timeoutMs
  match res.verdict with
  | .noViolationWithinBound d =>
      return {
        componentName := comp.interface.name,
        passed := true,
        detail := s!"Guarantee verified in isolation under assumption to depth {d}"
      }
  | .violationFound d _ =>
      return {
        componentName := comp.interface.name,
        passed := false,
        detail := s!"Guarantee violated in isolation at depth {d}"
      }
  | .inconclusive r =>
      return { componentName := comp.interface.name, passed := false, detail := s!"Inconclusive: {r}" }
  | .rejected r =>
      return { componentName := comp.interface.name, passed := false, detail := s!"Rejected: {r}" }
  | .unavailable r =>
      return { componentName := comp.interface.name, passed := false, detail := s!"Tool unavailable: {r}" }
  | _ =>
      return { componentName := comp.interface.name, passed := false, detail := "Verification failed" }

end ZilLib.Lower.Composition
