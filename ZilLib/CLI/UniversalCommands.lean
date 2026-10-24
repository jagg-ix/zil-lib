import ZilLib.Model
import ZilLib.SMT
import ZilLib.Lower.Universal
import ZilLib.Lower.Replay

/-!
# Universal Checking CLI Command (APL-30, S1)

Executes symbolic universal contract checking over domains of size $N = \min N \dots \max N$.
-/

namespace ZilLib.CLI.UniversalCommands

open Zil
open ZilLib.SMT
open ZilLib.Lower
open ZilLib.Lower.Universal
open ZilLib.Lower.Replay

def usage : String :=
  "zilLib universal <file.zc> [--inv QUERY] [--min-n N] [--max-n N] [--depth D] [--timeout SEC] [--solver SOLVER]"

structure UniversalRow where
  n : Nat
  depth : Nat
  durationMs : Nat
  verdict : String
  violation : Bool

private structure ParsedArgs where
  positional : List String := []
  options : List (String × String) := []

private def parseArgs (args : List String) : ParsedArgs := Id.run do
  let mut pos : List String := []
  let mut opts : List (String × String) := []
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | opt :: val :: tail =>
        if opt.startsWith "--" then
          opts := (opt, val) :: opts
          rest := tail
        else
          pos := opt :: pos
          rest := val :: tail
    | [single] =>
        pos := single :: pos
        rest := []
    | [] => rest := []
  { positional := pos.reverse, options := opts.reverse }

private def getOption (p : ParsedArgs) (key : String) : Option String :=
  p.options.find? (·.1 == key) |>.map (·.2)

def runUniversal (args : List String) : IO UInt32 := do
  let parsed := parseArgs args
  if parsed.positional.isEmpty then
    IO.eprintln usage
    return 2

  let file := parsed.positional.head!
  let p ← match ← (ZilLib.loadProgram file).toBaseIO with
    | .ok prog => pure prog
    | .error err =>
        IO.eprintln s!"failed to load program '{file}': {err}"
        return 2

  let invName := getOption parsed "--inv"
  let minN := (getOption parsed "--min-n" >>= String.toNat?).getD 2
  let maxN := (getOption parsed "--max-n" >>= String.toNat?).getD 6
  let depthOpt := getOption parsed "--depth" >>= String.toNat?
  let timeoutSec := (getOption parsed "--timeout" >>= String.toNat?).getD 30
  let timeoutMs := timeoutSec * 1000
  let solverName := getOption parsed "--solver" |>.getD "z3"

  let tool ← match ← locateInEnvironment solverName with
    | .found t => pure t
    | .missing name =>
        IO.eprintln s!"solver '{name}' not found on PATH"
        return 3
    | .broken path detail =>
        IO.eprintln s!"solver '{path}' broken: {detail}"
        return 3

  IO.println s!"Universal Contract Check: {file}"
  IO.println "------------------------------------------------------------"
  IO.println "  N  Depth  Time (ms)  Verdict"
  IO.println "------------------------------------------------------------"

  let mut rows : List UniversalRow := []
  let mut anyViolation := false

  for n in [minN:maxN + 1] do
    let depth := depthOpt.getD (n + 1)
    let (domain, tsMod) ← match lowerUniversalProgram p n invName with
      | .ok res => pure res
      | .error err =>
          IO.eprintln s!"lowering error at N={n}: {err}"
          return 2

    let targetInvName := match invName with
      | some name => name
      | none => tsMod.invariants.head?.map (·.1) |>.getD "invariant"

    let res ← checkBMC tsMod targetInvName depth tool timeoutMs
    let duration := res.elapsedMs

    match res.verdict with
    | .noViolationWithinBound _ =>
        rows := { n, depth, durationMs := duration, verdict := "no-violation", violation := false } :: rows
        IO.println s!"  {n}      {depth}       {duration}  no-violation"

    | .violationFound d trace =>
        anyViolation := true
        let replay := replayAndCertify domain tsMod trace targetInvName
        if replay.valid then
          rows := { n, depth, durationMs := duration, verdict := s!"violation-found (depth {d}, replayed)", violation := true } :: rows
          IO.println s!"  {n}      {depth}       {duration}  violation-found (depth {d}, replayed)"
        else
          rows := { n, depth, durationMs := duration, verdict := s!"violation-found (replay mismatch: {replay.detail})", violation := true } :: rows
          IO.println s!"  {n}      {depth}       {duration}  violation-found (replay mismatch)"

    | .inconclusive reason =>
        rows := { n, depth, durationMs := duration, verdict := s!"inconclusive ({reason})", violation := false } :: rows
        IO.println s!"  {n}      {depth}       {duration}  inconclusive ({reason})"

    | .inductiveProved step =>
        rows := { n, depth, durationMs := duration, verdict := s!"inductive-proved (step {step})", violation := false } :: rows
        IO.println s!"  {n}      {depth}       {duration}  inductive-proved"

    | .nonInductive step _ =>
        rows := { n, depth, durationMs := duration, verdict := s!"not-inductive (step {step})", violation := true } :: rows
        IO.println s!"  {n}      {depth}       {duration}  not-inductive"

    | .rejected reason =>
        rows := { n, depth, durationMs := duration, verdict := s!"rejected ({reason})", violation := false } :: rows
        IO.println s!"  {n}      {depth}       {duration}  rejected ({reason})"

    | .unavailable reason =>
        IO.eprintln s!"solver unavailable at N={n}: {reason}"
        return 3

  IO.println "------------------------------------------------------------"
  if anyViolation then
    return 1
  else
    return 0

end ZilLib.CLI.UniversalCommands
