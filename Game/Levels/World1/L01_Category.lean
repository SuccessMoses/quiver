import Game.Metadata

World "World1"
Level 1

Title "Hello World"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."

example : Category' (Unit) := by
  refine {Hom := ?_, id := ?_, comp := ?_, comp_id := ?_, id_comp := ?_, assoc := ?_}
  · exact fun _ _ => Nat
  · exact fun _ => 0
  · exact (. + .)
  simp; simp
  exact fun f g h => (Nat.add_assoc f g h).symm


Statement (preamble := refine {Hom := ?_, id := ?_, comp := ?_, comp_id := ?_, id_comp := ?_, assoc := ?_})
    : Category' (Unit) := by
  · exact fun _ _ => Nat
  · exact fun _ => 0
  · exact (. + .)
  · simp
  · simp
  · exact fun f g h => Eq.symm (Nat.add_assoc f g h)

NewTactic exact simp intro refine dsimp
NewDefinition Nat
NewTheorem Eq.symm Nat.add_assoc Category'.id Category'.assoc Category'.comp Category'.id_comp
           Category'.comp_id
