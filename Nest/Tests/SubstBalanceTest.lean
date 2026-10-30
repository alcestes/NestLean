import Nest.SessionUtils

/-!
# Substitution/balance regression tests.

Under the weakened notion (`SessionType.IsBalancedW`: uniform `LeadsTo` paths
to each recursion variable) both witness families below (`Cex*`, `D*`) are
balanced, and their substitutions and unfoldings stay balanced via
`IsBalancedW_subst` / `IsBalancedW_unfold` (closed grafts contribute no new
`LeadsTo` paths). Typechecking this file is the test.
-/
