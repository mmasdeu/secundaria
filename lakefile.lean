import Lake
open Lake DSL

package «secundaria» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require verbose from git
  "https://github.com/mmasdeu/verbose-lean4"

@[default_target]
lean_lib «Secundaria» {
  -- add any library configuration options here
}
