import Game.Metadata

World "World1"
Level 5

Title "Hello World"

Introduction "This level introduces the slice category."

open CategoryTheory Category'

structure Slice (C : Type) [Category' C] (c : C) where
  x : C
  obj : Quiver'.Hom c x

structure Triangle {C : Type} [Category' C] {x : C} (f g : Slice C x) where
  h : Quiver'.Hom f.x g.x
  naturality : comp f.obj h = g.obj

example {C : Type} [Category' C] {x : C} : Category' (Slice C x) := by
  refine { Hom := ?_, id := ?_, comp := ?_, comp_id := ?_, id_comp := ?_, assoc := ?_}
  · exact fun f g => Triangle f g
  · refine fun f => Triangle.mk (Category'.id _) ?_
    exact Category'.comp_id
  refine fun f g => ?_
  refine Triangle.mk ?_ ?_
  · exact comp f.h g.h
  · rw [assoc, f.naturality, g.naturality]
  · dsimp
    intro X Y f
    -- this is a good place to introduce simp
    simp [Category'.id_comp]
  · dsimp
    intro X Y f
    simp [Category'.comp_id]
  dsimp
  intro W X Y Z f g h
  simp [Category'.assoc]


Statement (preamble := refine { Hom := ?_, id := ?_, comp := ?_, comp_id := ?_, id_comp := ?_, assoc := ?_})
    {C : Type} [Category' C] {x : C} : Category' (Slice C x) := by
  · exact fun f g => Triangle f g
  · refine fun f => Triangle.mk (Category'.id _) ?_
    exact Category'.comp_id
  refine fun f g => ?_
  refine Triangle.mk ?_ ?_
  · exact comp f.h g.h
  · rw [assoc, f.naturality, g.naturality]
  · dsimp
    intro X Y f
    -- this is a good place to introduce simp
    simp [Category'.id_comp]
  · dsimp
    intro X Y f
    simp [Category'.comp_id]
  dsimp
  intro W X Y Z f g h
  simp [Category'.assoc]

NewDefinition Triangle Triangle.mk
