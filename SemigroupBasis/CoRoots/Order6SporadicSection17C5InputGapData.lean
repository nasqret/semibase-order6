import SemigroupBasis.CoRoots.Order6SporadicSection17C5SimpleBlockOverlap

/-! Split the actual gap list into nonempty internal gaps and its terminal
gap. Internal-gap multiplicity one is obtained from actual letter counts,
not from a set abstraction that could forget repeated or empty slots. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
open SemigroupBasis

def bodyInternalGaps : List BodyPiece → List (List Nat)
  | [] => []
  | [_] => []
  | (_,gap) :: next :: rest => gap :: bodyInternalGaps (next :: rest)

theorem bodyPieces_gaps_split (pieces : List BodyPiece) : pieces ≠ [] →
    pieces.map Prod.snd = bodyInternalGaps pieces ++ [bodyTerminal pieces] := by
  induction pieces with
  | nil => intro nonempty; exact False.elim (nonempty rfl)
  | cons piece rest ih =>
      rcases piece with ⟨tiles,gap⟩
      intro nonempty
      cases rest with
      | nil => rfl
      | cons next rest =>
          change gap :: ((next :: rest).map Prod.snd) =
            gap :: (bodyInternalGaps (next :: rest) ++ [bodyTerminal (next :: rest)])
          exact congrArg (List.cons gap) (ih (by simp))

theorem bodyInternalGaps_member_split (pieces : List BodyPiece) :
    ∀ gap ∈ bodyInternalGaps pieces,
      ∃ before tiles after, pieces = before ++ (tiles,gap) :: after ∧ after ≠ [] := by
  induction pieces with
  | nil => intro gap member; cases member
  | cons piece rest ih =>
      rcases piece with ⟨tiles,current⟩
      cases rest with
      | nil => intro gap member; cases member
      | cons next rest =>
          intro gap member
          rcases List.mem_cons.mp member with equal | found
          · subst gap
            exact ⟨[],tiles,next :: rest,rfl,by simp⟩
          · rcases ih gap found with ⟨before,otherTiles,after,shape,nonempty⟩
            refine ⟨(tiles,current) :: before,otherTiles,after,?_,nonempty⟩
            simpa only [List.cons_append] using congrArg (List.cons (tiles,current)) shape

theorem BodyPiecesGood.drop_prefix (original : List Nat) (before after : List BodyPiece) :
    BodyPiecesGood original (before ++ after) → BodyPiecesGood original after := by
  induction before with
  | nil => intro good; exact good
  | cons piece rest ih => intro good; exact ih good.2.2

theorem bodyInternalGaps_nonempty (original : List Nat) (pieces : List BodyPiece)
    (good : BodyPiecesGood original pieces) : ∀ gap ∈ bodyInternalGaps pieces, gap ≠ [] := by
  intro gap member
  rcases bodyInternalGaps_member_split pieces gap member with ⟨before,tiles,after,shape,nonempty⟩
  rw [shape] at good
  have tail := BodyPiecesGood.drop_prefix original before ((tiles,gap) :: after) good
  exact tail.2.1 nonempty

theorem bodyInternalGaps_simple (original : List Nat) (pieces : List BodyPiece)
    (good : BodyPiecesGood original pieces) :
    ∀ gap ∈ bodyInternalGaps pieces, ∀ x ∈ gap, original.count x = 1 := by
  intro gap member
  rcases bodyInternalGaps_member_split pieces gap member with ⟨before,tiles,after,shape,nonempty⟩
  rw [shape] at good
  have tail := BodyPiecesGood.drop_prefix original before ((tiles,gap) :: after) good
  exact tail.1.2.2

theorem bodyInternalGaps_count_le (pieces : List BodyPiece) (gap : List Nat) (x : Nat) (present : x ∈ gap) :
    (bodyInternalGaps pieces).count gap ≤ (bodyPiecesWord pieces).count x := by
  induction pieces with
  | nil => simp only [bodyInternalGaps,bodyPiecesWord,List.count_nil,Nat.le_refl]
  | cons piece rest ih =>
      rcases piece with ⟨tiles,current⟩
      cases rest with
      | nil => exact Nat.zero_le _
      | cons next rest =>
          have positive : 0 < gap.count x := List.count_pos_iff.mpr present
          change (current :: bodyInternalGaps (next :: rest)).count gap ≤
            (powerTileBody tiles ++ current ++ bodyPiecesWord (next :: rest)).count x
          by_cases equal : current = gap
          · subst current
            simp only [List.count_cons_self,List.count_append]
            omega
          · simp only [List.count_cons_of_ne equal,List.count_append]
            omega

def populatedInternal (original : List Nat) : List (List Nat) :=
  bodyInternalGaps (populatedInputForm original).pieces

theorem populatedInternal_nonempty (original : List Nat) :
    ∀ gap ∈ populatedInternal original, gap ≠ [] :=
  bodyInternalGaps_nonempty original (populatedInputForm original).pieces (populatedInputForm_good original).2

theorem populatedInternal_simple (original : List Nat) :
    ∀ gap ∈ populatedInternal original, ∀ x ∈ gap, original.count x = 1 :=
  bodyInternalGaps_simple original (populatedInputForm original).pieces (populatedInputForm_good original).2

theorem populatedInternal_nodup (original : List Nat) : (populatedInternal original).Nodup := by
  apply List.nodup_iff_count.mpr
  intro gap
  by_cases present : gap ∈ populatedInternal original
  · have nonempty := populatedInternal_nonempty original gap present
    cases gap with
    | nil => exact False.elim (nonempty rfl)
    | cons x xs =>
        have one := populatedInternal_simple original (x :: xs) present x List.mem_cons_self
        have derived := Semantics.derives_sameEval false (populatedInputForm_derives original)
        have actualOne := (derived.countOne x).mp one
        have bound := bodyInternalGaps_count_le (populatedInputForm original).pieces (x :: xs) x List.mem_cons_self
        change ((populatedInputForm original).initial ++ bodyPiecesWord (populatedInputForm original).pieces).count x = 1 at actualOne
        rw [List.count_append] at actualOne
        change (bodyInternalGaps (populatedInputForm original).pieces).count (x :: xs) ≤ 1
        omega
  · rw [List.count_eq_zero_of_not_mem present]
    omega

theorem betaInputWord_presentation (original : List Nat) (beta : ∃ x, Unrestricted x original) :
    betaInputWord original = betaPresentation (populatedInputForm original).initial
      (bodySquares (populatedInputForm original).pieces) (unrestrictedMarkers original)
      (populatedInternal original) (populatedTerminal original) := by
  have split := bodyPieces_gaps_split (populatedInputForm original).pieces (populatedInputForm_pieces_nonempty original beta)
  simp only [betaInputWord,betaPresentation,populatedInternal,populatedTerminal,split]

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.bodyPieces_gaps_split
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.bodyInternalGaps_member_split
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.BodyPiecesGood.drop_prefix
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.bodyInternalGaps_nonempty
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.bodyInternalGaps_simple
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.bodyInternalGaps_count_le
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.populatedInternal_nonempty
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.populatedInternal_simple
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.populatedInternal_nodup
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.betaInputWord_presentation

end SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
