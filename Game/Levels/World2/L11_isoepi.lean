import Game.Metadata

World "World2"
Level 11

Title "Hello World"

Introduction "This level introduces split epimorhisms."

open CategoryTheory

variable {C : Type} [Category C] {X Y : C} (f : X ⟶ Y)

example [IsIso f] : IsSplitEpi f := IsSplitEpi.mk' { section_ := inv f }

Statement [IsIso f] : IsSplitEpi f := by exact IsSplitEpi.mk' { section_ := inv f }
