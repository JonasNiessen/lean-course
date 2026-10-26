import Lake
open Lake DSL

package "CourseNotes" where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.35.0"

lean_lib «CourseNotes» where
  -- add library configuration options here

@[default_target]
lean_exe "coursenotes" where
  root := `Main
