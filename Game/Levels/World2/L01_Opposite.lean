import Game.Metadata

World "World2"
Level 1

Title "Hello World"

Introduction "This level introduces the opposite category."

open Quiver' Category' Opposite

example {C : Type} [Category' C] : Category' (Opposite C) := by
  refine {Hom := ?_, id := ?_, comp := ?_, comp_id := ?_, id_comp := ?_, assoc := ?_}
  · exact fun X Y => Hom Y.unop X.unop
  · exact fun X => id X.unop
  · exact fun f g => comp g f
  · exact comp_id
  · exact id_comp
  · exact fun _ _ _ => Eq.symm (assoc _ _ _)

Statement (preamble := refine { Hom := ?_, id := ?_, comp := ?_, comp_id := ?_, id_comp := ?_, assoc := ?_})
    {C : Type} [Category' C] {x : C} : Category' (Opposite C) := by
  · exact fun X Y => Hom Y.unop X.unop
  · exact fun X => id X.unop
  · exact fun f g => comp g f
  · exact comp_id
  · exact id_comp
  · exact fun _ _ _ => Eq.symm (assoc _ _ _)
