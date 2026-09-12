import Lean
open Lean Meta Elab Tactic

set_option debug.skipKernelTC true in
def etaRuleK : ∀ (a : true = true → Bool),
  @Eq (true = true → Bool)
    (@Eq.rec Bool true (fun _ _ => Bool) (a (Eq.refl true)) _)
    a :=
  fun a => by
    run_tac closeMainGoalUsing `unchecked fun goalType _ => do
      let some (_, _, rhs) := goalType.eq? | throwError "goal is not an equality"
      mkEqRefl rhs
