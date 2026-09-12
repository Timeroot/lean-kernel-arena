import Lean
open Lean Meta Elab Tactic

structure T where
  val : Bool
  proof : True

set_option debug.skipKernelTC true in
def etaCtor :
  ∀ (x : True → T), (T.mk (x True.intro).val) = x :=
  fun x => by
    run_tac closeMainGoalUsing `unchecked fun goalType _ => do
      let some (_, _, rhs) := goalType.eq? | throwError "goal is not an equality"
      mkEqRefl rhs
