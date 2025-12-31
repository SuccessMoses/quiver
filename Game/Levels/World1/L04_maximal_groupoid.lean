import Game.Metadata

World "World1"
Level 4

Title "Hello World"

Introduction "This level introduces the groupoid and the maximal groupoid."

open CategoryTheory Category Iso

structure MaximalGroupoid (C : Type) where
  of : C

example {C : Type} [Category C] : Groupoid' (MaximalGroupoid C) := by
  refine {
    Hom := ?_,
    id := ?_,
    comp := ?_,
    comp_id := ?_,
    id_comp := ?_,
    assoc := ?_,
    inv := ?_,
    inv_comp := ?_,
    comp_inv := ?_
  }
  · exact fun X Y => X.of ≅ Y.of
  · exact fun X => Iso.refl X.of
  · exact fun f g => Iso.trans f g
  · exact refl_trans _
  · exact trans_refl _
  · exact fun _ _ _ => Eq.symm (trans_assoc _ _ _)
  · exact Iso.symm
  · exact symm_self_id
  · exact self_symm_id

Statement (preamble := refine { Hom := ?_, id := ?_, comp := ?_, comp_id := ?_, id_comp := ?_, assoc := ?_})
    {C : Type} [Category C] : Category' (MaximalGroupoid C) := by
  · exact fun X Y => X.of ≅ Y.of
  · exact fun X => Iso.refl X.of
  · exact fun f g => Iso.trans f g
  · exact refl_trans _
  · exact trans_refl _
  · exact fun _ _ _ => Eq.symm (trans_assoc _ _ _)

NewTheorem CategoryTheory.Iso.trans CategoryTheory.Iso.refl CategoryTheory.Iso.refl_trans
           CategoryTheory.Iso.trans_refl CategoryTheory.Iso.trans_assoc
