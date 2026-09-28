import Lake
open Lake DSL

package «schrodingerMapsScattering» where
  version := v!"0.1.0"

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "a98628e16c11f5167f16124105ddce53efa9bfe5"


lean_lib SMScattering where
  srcDir := "lean"
