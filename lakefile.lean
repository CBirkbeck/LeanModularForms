import Lake
open Lake DSL

package «LeanModularForms» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

-- TEMP(v4.31 bump, 2026-06-14): verso-blueprint has no v4.31 release yet — every
-- branch/PR tops out at lean v4.30.0. Disabled so the math tree builds on v4.31.0-rc2.
-- Restore (and bump the pin, keeping it BEFORE mathlib so mathlib's transitive pins win)
-- once verso-blueprint ships v4.31.
-- require VersoBlueprint from git
--   "https://github.com/leanprover/verso-blueprint" @ "v4.30.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0-rc2"

@[default_target]
lean_lib «LeanModularForms» where
  -- add any library configuration options here

-- TEMP(v4.31 bump): blueprint-gen depends on VersoBlueprint (disabled above).
-- lean_exe «blueprint-gen» where
--   root := `LeanModularFormsMain

-- TEMP(v4.31 bump): aggregates the Hecke/SMO math surface (the modules the Verso
-- Chapters import) so `lake build LeanModularFormsHecke` builds the math without
-- blueprint-gen/Verso. Remove once blueprint-gen is restored.
lean_lib «LeanModularFormsHecke» where
