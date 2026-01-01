import GameServer

import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Opposites

-- import Mathlib.Tactic.Common

/-! Use this file to add things that should be available in all levels.

For example, this demo imports the mathlib tactics

*Note*: As long as `Game.lean` exists and ends with the `MakeGame` command,
you are completely free how you structure your lean project, this is merely
a suggestion.

*Bug*: However, things are bugged out if the levels of different worlds are imported
in a random order. Therefore, you should keep the structure of one file Lean file per world
which imports all its levels.
-/

class Quiver' (C : Type) where
  Hom (X : C) (Y : C) : Type

class Category' (C : Type) extends Quiver' (C : Type) where
  id X : Hom X X
  comp {X Y Z : C} (f : Hom X Y) (g : Hom Y Z) : Hom X Z
  id_comp {X Y : C} {f : Hom X Y} : comp (id X) f = f
  comp_id {X Y : C} {f : Hom X Y} : comp f (id Y) = f
  assoc {W X Y Z : C} (f : Hom X Y) (g : Hom Y Z) (h : Hom Z W) :
    comp f (comp g h) = comp (comp f g) h

class Groupoid' (C : Type) extends Category' C where
  inv : ∀ {X Y : C}, (Hom X Y) → (Hom Y X)
  inv_comp : ∀ {X Y : C} (f : Hom X Y), comp (inv f) f = id Y
  comp_inv : ∀ {X Y : C} (f : Hom X Y), comp f (inv f) = id X
