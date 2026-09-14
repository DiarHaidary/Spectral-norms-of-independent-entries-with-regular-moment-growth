import Lake
open Lake DSL

package mi32 where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "db584cd6d46c92f209a44c0f1c829460d327499d"

lean_lib GraphMatrices where
  srcDir := "vendor/graph-matrices"

@[default_target]
lean_lib MI32 where
  roots := #[`MI32]

lean_lib Challenge where
  roots := #[`Challenge]

lean_lib Solution where
  roots := #[`Solution]
