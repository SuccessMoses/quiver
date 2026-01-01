import Game.Metadata

World "World2"
Level 5

Title "Hello World"

Introduction "This level introduces epimorhisms."

open CategoryTheory Category Opposite

open CategoryTheory

variable {C : Type} [Category C]

example {A B : Cᵒᵖ} (f : A ⟶ B) [Mono f] : Epi f.unop :=
  ⟨fun _ _ eq => Quiver.Hom.op_inj ((cancel_mono f).1 (Quiver.Hom.unop_inj eq))⟩

Statement {A B : Cᵒᵖ} (f : A ⟶ B) [Mono f] : Epi f.unop := by
  exact ⟨fun _ _ eq => Quiver.Hom.op_inj ((cancel_mono f).1 (Quiver.Hom.unop_inj eq))⟩
