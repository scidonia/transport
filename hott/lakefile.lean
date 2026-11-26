import Lake
open Lake DSL

package hott

-- The pinned Lean 4 HoTT library lives in the repository, not on a forge:
-- the worker cannot fetch GitHub, and the library pins its own toolchain.
require GroundZero from "../vendor/ground_zero"

@[default_target]
lean_lib Hott
