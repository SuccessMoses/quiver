import Game.Metadata

World "World2"
Level 10

Title "Hello World"

Introduction "This level introduces split epimorhisms."

open CategoryTheory

variable {C : Type} [Category C] {X Y : C} (f : X ⟶ Y)

example [IsIso f] : IsSplitMono f := IsSplitMono.mk' { retraction := inv f }

Statement [IsIso f] : IsSplitMono f := by exact IsSplitMono.mk' { retraction := inv f }
