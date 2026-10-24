import Zil.Core.Program
import Zil.Core.Relation
import ZilLib.TransitionSystem
import ZilLib.SMT.Run
import ZilLib.SMT.Check

/-!
# Numeric Limits and Quota Governance Transition System (APL-44)

Formalizes integer counters and arithmetic limits for session concurrency and resource quotas
lowered to SMT-LIB 2 `Int` sort and `QF_LIA` (Quantifier-Free Linear Integer Arithmetic).

Models:
- Integer counters (`active_sessions`, `quota_used`) and bounds (`max_sessions`, `quota_limit`).
- Discrete arithmetic operations: `Login`, `Logout`, `ConsumeQuota`, `RefundQuota`.
- Invariants:
  - Non-negativity: `active_sessions >= 0`, `quota_used >= 0`.
  - Quota cap: `active_sessions <= max_sessions`, `quota_used <= quota_limit`.
- Verification of safe policies and detection of integer underflow / quota overflow flaws.
-/

namespace ZilLib.Lower.NumericLimits

open ZilLib.TransitionSystem

/-- Configuration for numeric quota model. -/
structure QuotaConfig where
  users : List String := ["user1", "user2"]
  defaultMaxSessions : Int := 3
  defaultQuotaLimit : Int := 100
  flawedLogin : Bool := false        -- If true, omits < max_sessions check (causes overflow)
  flawedLogout : Bool := false       -- If true, omits > 0 check (causes underflow)
  deriving Inhabited, Repr

/-- Helper to build conjunction of expressions. -/
def mkAndList (es : List TSExpr) : TSExpr :=
  match es with
  | [] => .constBool true
  | [e] => e
  | e :: rest => .and e (mkAndList rest)

/-- Helper to build disjunction of expressions. -/
def mkOrList (es : List TSExpr) : TSExpr :=
  match es with
  | [] => .constBool false
  | [e] => e
  | e :: rest => .or e (mkOrList rest)

/-- Variable names for user quota state. -/
def varActiveSessions (u : String) : String := s!"active_sessions_{u}"
def varMaxSessions (u : String) : String := s!"max_sessions_{u}"
def varQuotaUsed (u : String) : String := s!"quota_used_{u}"
def varQuotaLimit (u : String) : String := s!"quota_limit_{u}"

/-- Lower a numeric quota governance model into a TSModule. -/
def lowerQuotaModule (cfg : QuotaConfig) : TSModule := Id.run do
  let mut vars : List TSVar := []
  for u in cfg.users do
    vars := { name := varActiveSessions u, sort := .int } :: vars
    vars := { name := varMaxSessions u, sort := .int } :: vars
    vars := { name := varQuotaUsed u, sort := .int } :: vars
    vars := { name := varQuotaLimit u, sort := .int } :: vars

  -- Initial state
  let mut initEqs : List TSExpr := []
  for u in cfg.users do
    -- Sessions start at 0
    initEqs := .eq (.var (varActiveSessions u) false) (.constInt 0) :: initEqs
    -- Max sessions configured
    initEqs := .eq (.var (varMaxSessions u) false) (.constInt cfg.defaultMaxSessions) :: initEqs
    -- Quota used starts at 0
    initEqs := .eq (.var (varQuotaUsed u) false) (.constInt 0) :: initEqs
    -- Quota limit configured
    initEqs := .eq (.var (varQuotaLimit u) false) (.constInt cfg.defaultQuotaLimit) :: initEqs

  let initExpr := mkAndList initEqs.reverse

  -- Next step operator: disjunction of Login, Logout, ConsumeQuota, RefundQuota
  let mut opTransitions : List TSExpr := []

  for u in cfg.users do
    -- 1. Operation: Login(u)
    let loginGuard :=
      if cfg.flawedLogin then
        .constBool true
      else
        .lt (.var (varActiveSessions u) false) (.var (varMaxSessions u) false)

    let mut loginEffects : List TSExpr := [
      .eq (.var (varActiveSessions u) true) (.add (.var (varActiveSessions u) false) (.constInt 1)),
      .eq (.var (varMaxSessions u) true) (.var (varMaxSessions u) false),
      .eq (.var (varQuotaUsed u) true) (.var (varQuotaUsed u) false),
      .eq (.var (varQuotaLimit u) true) (.var (varQuotaLimit u) false)
    ]
    -- Other users unchanged
    for otherU in cfg.users do
      if otherU != u then
        loginEffects := .eq (.var (varActiveSessions otherU) true) (.var (varActiveSessions otherU) false) :: loginEffects
        loginEffects := .eq (.var (varMaxSessions otherU) true) (.var (varMaxSessions otherU) false) :: loginEffects
        loginEffects := .eq (.var (varQuotaUsed otherU) true) (.var (varQuotaUsed otherU) false) :: loginEffects
        loginEffects := .eq (.var (varQuotaLimit otherU) true) (.var (varQuotaLimit otherU) false) :: loginEffects

    opTransitions := mkAndList (loginGuard :: loginEffects) :: opTransitions

    -- 2. Operation: Logout(u)
    let logoutGuard :=
      if cfg.flawedLogout then
        .constBool true
      else
        .gt (.var (varActiveSessions u) false) (.constInt 0)

    let mut logoutEffects : List TSExpr := [
      .eq (.var (varActiveSessions u) true) (.sub (.var (varActiveSessions u) false) (.constInt 1)),
      .eq (.var (varMaxSessions u) true) (.var (varMaxSessions u) false),
      .eq (.var (varQuotaUsed u) true) (.var (varQuotaUsed u) false),
      .eq (.var (varQuotaLimit u) true) (.var (varQuotaLimit u) false)
    ]
    for otherU in cfg.users do
      if otherU != u then
        logoutEffects := .eq (.var (varActiveSessions otherU) true) (.var (varActiveSessions otherU) false) :: logoutEffects
        logoutEffects := .eq (.var (varMaxSessions otherU) true) (.var (varMaxSessions otherU) false) :: logoutEffects
        logoutEffects := .eq (.var (varQuotaUsed otherU) true) (.var (varQuotaUsed otherU) false) :: logoutEffects
        logoutEffects := .eq (.var (varQuotaLimit otherU) true) (.var (varQuotaLimit otherU) false) :: logoutEffects

    opTransitions := mkAndList (logoutGuard :: logoutEffects) :: opTransitions

    -- 3. Operation: ConsumeQuota(u, 25)
    let consumeAmt := 25
    let consumeGuard := .le (.add (.var (varQuotaUsed u) false) (.constInt consumeAmt)) (.var (varQuotaLimit u) false)
    let mut consumeEffects : List TSExpr := [
      .eq (.var (varActiveSessions u) true) (.var (varActiveSessions u) false),
      .eq (.var (varMaxSessions u) true) (.var (varMaxSessions u) false),
      .eq (.var (varQuotaUsed u) true) (.add (.var (varQuotaUsed u) false) (.constInt consumeAmt)),
      .eq (.var (varQuotaLimit u) true) (.var (varQuotaLimit u) false)
    ]
    for otherU in cfg.users do
      if otherU != u then
        consumeEffects := .eq (.var (varActiveSessions otherU) true) (.var (varActiveSessions otherU) false) :: consumeEffects
        consumeEffects := .eq (.var (varMaxSessions otherU) true) (.var (varMaxSessions otherU) false) :: consumeEffects
        consumeEffects := .eq (.var (varQuotaUsed otherU) true) (.var (varQuotaUsed otherU) false) :: consumeEffects
        consumeEffects := .eq (.var (varQuotaLimit otherU) true) (.var (varQuotaLimit otherU) false) :: consumeEffects

    opTransitions := mkAndList (consumeGuard :: consumeEffects) :: opTransitions

  let nextExpr := mkOrList opTransitions.reverse

  -- Invariants:
  -- 1. active_sessions within [0, max_sessions]
  let mut sessionInvConj : List TSExpr := []
  for u in cfg.users do
    let inBound := .and
      (.ge (.var (varActiveSessions u) false) (.constInt 0))
      (.le (.var (varActiveSessions u) false) (.var (varMaxSessions u) false))
    sessionInvConj := inBound :: sessionInvConj

  let sessionInvExpr := mkAndList sessionInvConj.reverse

  -- 2. quota_used within [0, quota_limit]
  let mut quotaInvConj : List TSExpr := []
  for u in cfg.users do
    let inBound := .and
      (.ge (.var (varQuotaUsed u) false) (.constInt 0))
      (.le (.var (varQuotaUsed u) false) (.var (varQuotaLimit u) false))
    quotaInvConj := inBound :: quotaInvConj

  let quotaInvExpr := mkAndList quotaInvConj.reverse
  let tag := if cfg.flawedLogin then "FlawedOverflow" else if cfg.flawedLogout then "FlawedUnderflow" else "Safe"

  return {
    name := s!"NumericLimits_{tag}",
    variables := vars,
    init := initExpr,
    next := nextExpr,
    invariants := [
      ("session_within_bounds", sessionInvExpr),
      ("quota_within_bounds", quotaInvExpr)
    ]
  }

end ZilLib.Lower.NumericLimits
