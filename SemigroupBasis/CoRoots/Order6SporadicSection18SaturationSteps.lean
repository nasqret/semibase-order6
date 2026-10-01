import SemigroupBasis.CoRoots.Order6SporadicSection18SaturationMeasure

/-! Every productive overlap/crossing saturation preserves the gaps, is an
actual derivation from Prop18.1, and strictly increases the bounded score. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
open SemigroupBasis

inductive Step (alphabet : List Nat) : List Slot → List Slot → Prop where
  | overlap (before middle after : List Slot) (g1 g2 left right : List Nat)
      (x : Nat) (inLeft : x ∈ left) (inRight : x ∈ right) (different : left ≠ right) :
      Step alphabet
        (before ++ (⟨g1, left⟩ :: (middle ++ (⟨g2, right⟩ :: after))))
        (before ++ (⟨g1, joinBlock alphabet left right⟩ ::
          (middle ++ (⟨g2, joinBlock alphabet left right⟩ :: after))))
  | crossing (before middle1 middle2 middle3 after : List Slot)
      (g1 g2 g3 g4 left right : List Nat) (different : left ≠ right) :
      Step alphabet
        (before ++ (⟨g1, left⟩ :: (middle1 ++ (⟨g2, right⟩ ::
          (middle2 ++ (⟨g3, left⟩ :: (middle3 ++ (⟨g4, right⟩ :: after))))))))
        (before ++ (⟨g1, joinBlock alphabet left right⟩ ::
          (middle1 ++ (⟨g2, joinBlock alphabet left right⟩ ::
          (middle2 ++ (⟨g3, joinBlock alphabet left right⟩ ::
          (middle3 ++ (⟨g4, joinBlock alphabet left right⟩ :: after))))))))

theorem Step.valid {alphabet : List Nat} {input output : List Slot}
    (move : Step alphabet input output) (valid : Valid alphabet input) : Valid alphabet output := by
  cases move with
  | overlap before middle after g1 g2 left right x inLeft inRight different =>
      simp only [valid_append_iff, valid_cons_iff] at valid ⊢
      rcases valid with ⟨beforeValid, leftGood, middleValid, rightGood, afterValid⟩
      have joinedGood := joinBlock_good alphabet left right leftGood rightGood
      exact ⟨beforeValid, joinedGood, middleValid, joinedGood, afterValid⟩
  | crossing before middle1 middle2 middle3 after g1 g2 g3 g4 left right different =>
      simp only [valid_append_iff, valid_cons_iff] at valid ⊢
      rcases valid with ⟨beforeValid, leftGood, middle1Valid, rightGood, middle2Valid, _, middle3Valid, _, afterValid⟩
      have joinedGood := joinBlock_good alphabet left right leftGood rightGood
      exact ⟨beforeValid, joinedGood, middle1Valid, joinedGood, middle2Valid, joinedGood, middle3Valid, joinedGood, afterValid⟩

theorem Step.gaps {alphabet : List Nat} {input output : List Slot}
    (move : Step alphabet input output) : input.map Slot.gap = output.map Slot.gap := by
  cases move <;> simp only [List.map_append, List.map_cons]

theorem Step.length {alphabet : List Nat} {input output : List Slot}
    (move : Step alphabet input output) : input.length = output.length := by
  have equal := congrArg List.length move.gaps
  simpa only [List.length_map] using equal

theorem Step.growth {alphabet : List Nat} {input output : List Slot}
    (move : Step alphabet input output) (valid : Valid alphabet input) : score input < score output := by
  cases move with
  | overlap before middle after g1 g2 left right x inLeft inRight different =>
      simp only [valid_append_iff, valid_cons_iff] at valid
      rcases valid with ⟨_, leftGood, _, rightGood, _⟩
      have growth := joinBlock_growth alphabet left right leftGood rightGood different
      simp only [score_append, score]
      omega
  | crossing before middle1 middle2 middle3 after g1 g2 g3 g4 left right different =>
      simp only [valid_append_iff, valid_cons_iff] at valid
      rcases valid with ⟨_, leftGood, _, rightGood, _, _, _, _, _⟩
      have growth := joinBlock_growth alphabet left right leftGood rightGood different
      simp only [score_append, score]
      omega

theorem Step.sound {alphabet : List Nat} {input output : List Slot}
    (move : Step alphabet input output) (valid : Valid alphabet input) :
    ListDerives (render input) (render output) := by
  cases move with
  | overlap before middle after g1 g2 left right x inLeft inRight different =>
      simp only [valid_append_iff, valid_cons_iff] at valid
      rcases valid with ⟨_, leftGood, _, rightGood, _⟩
      have merged := mergeSquareBlocks_to left right (joinBlock alphabet left right)
        (render middle ++ g2) x inLeft inRight (joinBlock_content alphabet left right leftGood rightGood)
      simpa only [render_append, render, List.append_assoc] using
        merged.context (render before ++ g1) (render after)
  | crossing before middle1 middle2 middle3 after g1 g2 g3 g4 left right different =>
      simp only [valid_append_iff, valid_cons_iff] at valid
      rcases valid with ⟨_, leftGood, _, rightGood, _, _, _, _, _⟩
      let joined := joinBlock alphabet left right
      let h := render middle1 ++ g2
      let k := render middle2 ++ g3
      let t := render middle3 ++ g4
      have normalize : ListDerives (squareList (left ++ right)) (squareList joined) :=
        squareBlocks_same_content (left ++ right) joined (joinBlock_content alphabet left right leftGood rightGood)
      have normalizeFour : ListDerives
          (squareList (left ++ right) ++ h ++ squareList (left ++ right) ++ k ++
            squareList (left ++ right) ++ t ++ squareList (left ++ right))
          (squareList joined ++ h ++ squareList joined ++ k ++ squareList joined ++ t ++ squareList joined) := by
        simpa only [List.append_assoc] using
          append_derivations normalize (append_derivations (S5_107.ListDerives.refl h)
            (append_derivations normalize (append_derivations (S5_107.ListDerives.refl k)
              (append_derivations normalize (append_derivations (S5_107.ListDerives.refl t) normalize)))))
      have merged := (mergeCrossing left right h k t leftGood.1 rightGood.1).trans normalizeFour
      simpa only [render_append, render, h, k, t, joined, List.append_assoc] using
        merged.context (render before ++ g1) (render after)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.Step.valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.Step.gaps
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.Step.length
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.Step.growth
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.Step.sound

end SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
