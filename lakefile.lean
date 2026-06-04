import Lake
open Lake DSL

package «LeanModularForms» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require VersoBlueprint from git
  "https://github.com/leanprover/verso-blueprint" @ "v4.30.0"

-- mathlib must come LAST so its transitive pins (proofwidgets, plausible, …)
-- take precedence over VersoBlueprint's on `lake update`.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0"

@[default_target]
lean_lib «LeanModularForms» where
  -- add any library configuration options here

lean_exe «blueprint-gen» where
  root := `LeanModularFormsMain
