import Lake
open Lake DSL

package «zil-lib» where
  version := v!"0.1.0"

/-- The pinned core. Moving this commit is a deliberate act: run `scripts/test.sh` after it. -/
require «zil-lean» from git "https://github.com/jagg-ix/zil-lean.git" @ "4f6e1f5b701c440e49166fc6c287eb3f6f703d62"

@[default_target] lean_lib ZilLib where
  roots := #[`ZilLib]

@[default_target] lean_exe zilLib where
  root := `ZilLib.CLI.Main

/-- Tests whose `run_cmd` blocks read the shipped library files; they run when the module is compiled. -/
lean_exe zilLibTests where
  root := `ZilLib.Test.Main
