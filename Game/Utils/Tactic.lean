import Lean
import Mathlib.CategoryTheory.Category.Basic

open Lean Elab Tactic

syntax (name := custom) "refine_struct " term : tactic

-- Work in progress
elab "refine_struct " stx:term : tactic => do
  Lean.Elab.Tactic.withMainContext do
    let goal ← getMainGoal
    let (val, mvarIds') ← elabTermWithHoles stx (← getMainTarget) `refine True
    if mvarIds'.isEmpty then
      Lean.logInfo "It is empty"
    else
      -- Lean.logInfo <| MessageData.joinSep (mvarIds'.map MessageData.ofGoal) "\n"
      goal.assign val
      replaceMainGoal mvarIds'

instance : Category Type := by
  refine_struct {Hom := ?_, id := ?_, comp := ?_}


-- Example:
-- structure Category' (C : Type) where
--   Hom : C → C → Type
--   id X : Hom X X
--   comp (f : Hom X Y) (g : Hom Y Z) : Hom X Z

-- variable {C : Type}
-- def Hom : C → C → Type := sorry
-- def id' (X : C) : Hom X X := sorry

-- example : Category' C := by
--   refine_struct ({Hom := ?_, id := ?_, comp := ?_} : Category' C)
--   · exact Hom
--   · exact id'
--   sorry
