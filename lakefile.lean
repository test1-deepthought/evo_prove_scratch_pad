import Lake
open Lake DSL

package "evo_prove" where
  moreServerArgs := #["-Dpp.unicode=true"]

require mathlib from
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib "Proofs" where
  globs := #[.submodules `Proofs]
