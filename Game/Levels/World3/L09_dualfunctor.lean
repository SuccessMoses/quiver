import Game.Metadata
import Mathlib.LinearAlgebra.Dual.Defs

World "Functors"
Level 9

Title "Hello World"

Introduction "This level introduces the dual functor"

open CategoryTheory Module

variable {R : Type} [CommRing R]

example : (ModuleCat R)ᵒᵖ ⥤ (ModuleCat R) := by
  refine {obj := ?_, map := ?_, map_id := ?_, map_comp := ?_}
  · exact fun M => ModuleCat.of _ <| Dual R M.unop
  · refine fun f => ModuleCat.ofHom <| LinearMap.dualMap f.unop.hom
  · aesop
  · aesop

Statement
(preamble := refine {obj := ?_, map := ?_, map_id := ?_, map_comp := ?_})
: (ModuleCat R)ᵒᵖ ⥤ (ModuleCat R) := by
  · exact fun M => ModuleCat.of _ <| Dual R M.unop
  · refine fun f => ModuleCat.ofHom <| LinearMap.dualMap f.unop.hom
  · aesop
  · aesop
