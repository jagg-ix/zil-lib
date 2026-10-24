import Lake
open Lake DSL

package «zil-lib» where
  version := v!"0.1.0"
  license := "Apache-2.0"
  licenseFiles := #["LICENSE"]

/-- The pinned core. Moving this commit is a deliberate act: run `scripts/test.sh` after it. -/
require «zil-lean» from git "https://github.com/jagg-ix/zil-lean.git" @ "9790f04de1f059881d6afa67fcad06e63ce220b7"

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

/-- Tests of the SMT-LIB 2 backend (TS-03). -/
lean_exe zilLibSmtTests where
  root := `ZilLib.Test.SMTMain

/-- Tests of ZIL lowering, step operator, and witness replay (Batch 2). -/
lean_exe zilLibLowerTests where
  root := `ZilLib.Test.LowerMain

/-- Tests of check vocabulary and universal contract checking (Batch 3: APL-05 and APL-30). -/
lean_exe zilLibBatch3Tests where
  root := `ZilLib.Test.Batch3Main

/-- Tests of operations, temporal governance, and non-interference (Batch 4: APL-31, APL-32, APL-33). -/
lean_exe zilLibBatch4Tests where
  root := `ZilLib.Test.Batch4Main

/-- Tests of Batch 5 (APL-40, APL-42, APL-43, APL-44, APL-45, APL-46). -/
lean_exe zilLibBatch5Tests where
  root := `ZilLib.Test.Batch5Main

