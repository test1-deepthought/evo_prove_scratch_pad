import Lake
open Lake

package «evo_prove_scratch_pad» where
  moreLinkArgs := #[]

@[default_target]
lean_lib «EvoProveScratchPad» where
  roots := #["Proofs"]
  globs := #[Glob.one (Name.mkSimple "test_theorem")]
