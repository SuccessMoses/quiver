import Game.Metadata

World "World2"
Level 4

Title "Hello World"

Introduction "This level introduces the monomoprhisms."

open CategoryTheory Category Opposite

open CategoryTheory

variable {C : Type} [Category C]

/-- A verbose by pedagogical proof-/
example {A B : C} (f : A ⟶ B) [Epi f] : Mono f.op := by
  refine ⟨?_⟩
  refine fun h k eq => ?_
  refine Quiver.Hom.unop_inj ?_
  refine (cancel_epi f).1 ?_
  refine Quiver.Hom.op_inj ?_
  exact eq

Statement {A B : C} (f : A ⟶ B) [Epi f] : Mono f.op := by
  Hint "Try `refine ⟨fun h k eq => ?_⟩`"
  refine ⟨fun h k eq => ?_⟩
  Hint "Try `refine Quiver.Hom.unop_inj ?_`"
  refine Quiver.Hom.unop_inj ?_
  Hint "Try `refine (cancel_epi f).1 ?_`"
  refine (cancel_epi f).1 ?_
  Hint "Try `refine Quiver.Hom.op_inj ?_`"
  refine Quiver.Hom.op_inj ?_
  Hint "Recall that for `a b : Cᵒᵖ`, `a ⟶ b := (unop b ⟶ unop a).op`"
  exact eq
