import Game.Metadata

World "World2"
Level 9

Title "Hello World"

Introduction "This level introduces split epimorhisms."

open CategoryTheory

variable {C : Type} [Category C] {X Y : C} (f : X ⟶ Y)

example (se : SplitEpi f) : Epi f := by
  refine ⟨?_⟩
  refine fun  g h w => ?_
  replace w := se.section_ ≫= w
  simpa using w

Statement (se : SplitEpi f) : Epi f := by
  refine ⟨?_⟩
  refine fun  g h w => ?_
  replace w := se.section_ ≫= w
  simpa using w
