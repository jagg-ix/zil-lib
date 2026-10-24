import Lake
open Lake DSL

package «zil-lib» where
  version := v!"0.1.0"
  license := "Apache-2.0"
  licenseFiles := #["LICENSE"]

/-- The pinned core. Moving this commit is a deliberate act: run `scripts/test.sh` after it. -/
require «zil-lean» from git "https://github.com/jagg-ix/zil-lean.git" @ "022896d0e1bf8c1faec7f2779a40365c18b0dd92"

@[default_target] lean_lib ZilLib where
  roots := #[`ZilLib]

@[default_target] lean_exe zilLib where
  root := `ZilLib.CLI.Main

/-- Tests whose `run_cmd` blocks read the shipped library files; they run when the module is compiled. -/
lean_exe zilLibTests where
  root := `ZilLib.Test.Main

/-- Tests of the Apalache modules. Run from the repository root; `--with-tool` also starts the real tool. -/
lean_exe zilLibApalacheTests where
  root := `ZilLib.Test.ApalacheMain

/-- Tests of the certificate checker. Run from the repository root. -/
lean_exe zilLibCertifyTests where
  root := `ZilLib.Test.CertifyMain
