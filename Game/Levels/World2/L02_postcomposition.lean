import Game.Metadata

World "World2"
Level 2

Title "Hello World"

Introduction "This level introduces the opposite category."

open CategoryTheory Category Opposite Function

abbrev fstar {C : Type} [Category C] {x y : C} (f : x ⟶ y) (c : C) : (c ⟶ x) → (c ⟶ y) :=
  fun g => g ≫ f

def HasInverse {α β : Type} (f : α → β) := HasLeftInverse f ∧ HasRightInverse f

variable {C : Type} [Category C] {x y : C} (f : x ⟶ y)

theorem t1 : IsIso f ↔ ∀ c : C, HasInverse (fstar f _ : (c ⟶ x) → (c ⟶ y)) := by
  constructor
  · intro ⟨g, h₁, h₂⟩ c; refine ⟨?_, ?_⟩
    · use (fun g' => g' ≫ g)
      intro f'; dsimp
      unfold fstar
      rw [assoc, h₁, Category.comp_id]
    · use (fun g' => g' ≫ g)
      intro f'; dsimp
      unfold fstar
      rw [assoc, h₂, Category.comp_id]
  · intro h
    obtain h₁ := HasRightInverse.surjective (h y).right
    obtain h₂ := HasLeftInverse.injective (h x).left
    obtain ⟨g, cat⟩ := h₁ (𝟙 _)
    refine ⟨⟨g, h₂ ?_, cat⟩⟩
    unfold fstar at *
    rw [assoc, cat, Category.comp_id, Category.id_comp]

Statement : IsIso f ↔ ∀ c : C, HasInverse (fstar f _ : (c ⟶ x) → (c ⟶ y)) := by
  constructor
  · intro ⟨g, h₁, h₂⟩ c; refine ⟨?_, ?_⟩
    · use (fun g' => g' ≫ g)
      intro f'; dsimp
      unfold fstar
      rw [assoc, h₁, Category.comp_id]
    · use (fun g' => g' ≫ g)
      intro f'; dsimp
      unfold fstar
      rw [assoc, h₂, Category.comp_id]
  · intro h
    obtain h₁ := HasRightInverse.surjective (h y).right
    obtain h₂ := HasLeftInverse.injective (h x).left
    obtain ⟨g, cat⟩ := h₁ (𝟙 _)
    refine ⟨⟨g, h₂ ?_, cat⟩⟩
    unfold fstar at *
    rw [assoc, cat, Category.comp_id, Category.id_comp]
