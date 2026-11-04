import Lake
open Lake DSL

package "CourseNotes" where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.35.0"

@[default_target]
lean_lib «CourseNotes» where
  globs := #[.submodules `CourseNotes]

@[default_target]
lean_lib «Formalization» where
  -- our own AI-assisted formalizations; root file `Formalization.lean` imports all modules
