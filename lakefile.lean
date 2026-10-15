import Lake
open Lake DSL

package «JacobiSum» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]
  -- The files here predate the module system; this silences Lake's "consider adding `module`"
  -- warning on every Mathlib import.
  allowNonModules := true
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

@[default_target]
lean_lib «JacobiSum» where
  -- add any library configuration options here
