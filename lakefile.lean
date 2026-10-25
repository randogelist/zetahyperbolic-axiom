import Lake
open Lake DSL

package zetahyperbolic where

-- Exact Mathlib commit used by the historical Lean 4.33.0 project.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "db584cd6d46c92f209a44c0f1c829460d327499d"

@[default_target]
lean_lib Zetahyperbolic where
