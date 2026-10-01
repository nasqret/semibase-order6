import SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroupGuardedSwap
import SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroupNormalForm

namespace SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroup

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev ListDerives : List Nat -> List Nat -> Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

theorem source_mem_of_parityReduce_mem
    {letter : Nat} {letters : List Nat}
    (member : letter ∈ parityReduce letters) :
    letter ∈ letters := by
  have odd := (mem_parityReduce_iff letter letters).mp member
  apply List.count_pos_iff.mp
  omega

theorem listDerivesReverse
    {left right : List Nat}
    (derivation : ListDerives left right) :
    ListDerives left.reverse right.reverse := by
  cases derivation with
  | empty =>
      exact SemigroupBasis.CoRoots.S5_107.ListDerives.empty
  | words wordDerivation =>
      simpa only [Word.toList_reverse] using
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (derivesReverse wordDerivation)

private theorem perm_append_singleton_cons
    (letter : Nat) :
    forall gap : List Nat,
      (gap ++ [letter]).Perm (letter :: gap)
  | [] => List.Perm.refl _
  | head :: tail => by
      have induction := perm_append_singleton_cons letter tail
      have prefixed := List.Perm.cons head induction
      exact by
        simpa using
          prefixed.trans (List.Perm.swap letter head tail)

/-- Toggle a parity letter when the fixed leftContext and suffix both contain every
letter in the changing block. -/
theorem listDerivesToggleBetweenGuards
    (leftContext block suffix : List Nat) (letter : Nat)
    (letterLeft : letter ∈ leftContext)
    (letterRight : letter ∈ suffix)
    (blockLeft :
      forall selected, selected ∈ block -> selected ∈ leftContext)
    (blockRight :
      forall selected, selected ∈ block -> selected ∈ suffix) :
    ListDerives
      (leftContext ++ [letter] ++ block ++ suffix)
      (leftContext ++ affineParityToggle letter block ++ suffix) := by
  by_cases member : letter ∈ block
  · have expose :
        (letter :: block).Perm
          (letter :: letter :: block.erase letter) :=
      List.Perm.cons letter (List.perm_cons_erase member)
    have changingLeft :
        forall selected, selected ∈ letter :: block ->
          selected ∈ leftContext := by
      intro selected selectedMember
      rcases List.mem_cons.mp selectedMember with equal | blockMember
      · simpa [equal] using letterLeft
      · exact blockLeft selected blockMember
    have changingRight :
        forall selected, selected ∈ letter :: block ->
          selected ∈ suffix := by
      intro selected selectedMember
      rcases List.mem_cons.mp selectedMember with equal | blockMember
      · simpa [equal] using letterRight
      · exact blockRight selected blockMember
    have arranged :=
      listDerivesTwoSidedGuardedPermutation
        leftContext suffix changingLeft changingRight expose
    have deleted :=
      listDerivesDeleteAdjacentPairWithGuards
        letter leftContext (block.erase letter ++ suffix)
        letterLeft
        (List.mem_append.mpr (Or.inr letterRight))
    have arranged' : ListDerives
        (leftContext ++ [letter] ++ block ++ suffix)
        (leftContext ++ [letter, letter] ++ block.erase letter ++ suffix) := by
      simpa [List.append_assoc] using arranged
    have deleted' : ListDerives
        (leftContext ++ [letter, letter] ++ block.erase letter ++ suffix)
        (leftContext ++ block.erase letter ++ suffix) := by
      simpa [List.append_assoc] using deleted
    simpa [affineParityToggle, member, List.append_assoc] using
      arranged'.trans deleted'
  · simpa [affineParityToggle, member, List.append_assoc] using
      (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
        (basis := basis)
        (leftContext ++ [letter] ++ block ++ suffix))

/-- Delete two separated copies of a letter. Every gap letter is required in
both external guards so guarded permutation may expose the pair first. -/
theorem listDerivesDeleteSeparatedPair
    (leftContext gap suffix : List Nat) (letter : Nat)
    (letterLeft : letter ∈ leftContext)
    (letterRight : letter ∈ suffix)
    (gapLeft :
      forall selected, selected ∈ gap -> selected ∈ leftContext)
    (gapRight :
      forall selected, selected ∈ gap -> selected ∈ suffix) :
    ListDerives
      (leftContext ++ [letter] ++ gap ++ [letter] ++ suffix)
      (leftContext ++ gap ++ suffix) := by
  have expose :
      ([letter] ++ gap ++ [letter]).Perm
        ([letter, letter] ++ gap) := by
    simpa [List.append_assoc] using
      List.Perm.cons letter
        (perm_append_singleton_cons letter gap)
  have middleLeft :
      forall selected,
        selected ∈ [letter] ++ gap ++ [letter] ->
          selected ∈ leftContext := by
    intro selected member
    simp only [List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with member | equal
    · rcases member with equal | gapMember
      · simpa [equal] using letterLeft
      · exact gapLeft selected gapMember
    · simpa [equal] using letterLeft
  have middleRight :
      forall selected,
        selected ∈ [letter] ++ gap ++ [letter] ->
          selected ∈ suffix := by
    intro selected member
    simp only [List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with member | equal
    · rcases member with equal | gapMember
      · simpa [equal] using letterRight
      · exact gapRight selected gapMember
    · simpa [equal] using letterRight
  have arranged :=
    listDerivesTwoSidedGuardedPermutation
      leftContext suffix middleLeft middleRight expose
  have deleted :=
    listDerivesDeleteAdjacentPairWithGuards
      letter leftContext (gap ++ suffix)
      letterLeft
      (List.mem_append.mpr (Or.inr letterRight))
  have arranged' : ListDerives
      (leftContext ++ [letter] ++ gap ++ [letter] ++ suffix)
      (leftContext ++ [letter, letter] ++ gap ++ suffix) := by
    simpa [List.append_assoc] using arranged
  have deleted' : ListDerives
      (leftContext ++ [letter, letter] ++ gap ++ suffix)
      (leftContext ++ gap ++ suffix) := by
    simpa [List.append_assoc] using deleted
  exact by
    simpa [List.append_assoc] using arranged'.trans deleted'

/-- Reduce an arbitrary middle block to its duplicate-free parity residue.
The fixed leftContext and suffix contain every source letter and remain untouched
throughout the induction. -/
theorem listDerivesParityReduceBetweenGuards
    (leftContext letters suffix : List Nat)
    (leftGuard :
      forall letter, letter ∈ letters -> letter ∈ leftContext)
    (rightGuard :
      forall letter, letter ∈ letters -> letter ∈ suffix) :
    ListDerives
      (leftContext ++ letters ++ suffix)
      (leftContext ++ parityReduce letters ++ suffix) := by
  induction letters generalizing leftContext with
  | nil =>
      simpa [parityReduce] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis) (leftContext ++ suffix))
  | cons head tail induction =>
      have tailLeft :
          forall letter, letter ∈ tail ->
            letter ∈ leftContext ++ [head] := by
        intro letter member
        exact List.mem_append.mpr <| Or.inl <|
          leftGuard letter (List.Mem.tail head member)
      have tailRight :
          forall letter, letter ∈ tail -> letter ∈ suffix := by
        intro letter member
        exact rightGuard letter (List.Mem.tail head member)
      have tailDerivation :=
        induction (leftContext ++ [head]) tailLeft tailRight
      by_cases member : head ∈ parityReduce tail
      · have headLeft : head ∈ leftContext :=
          leftGuard head (List.Mem.head tail)
        have headRight : head ∈ suffix :=
          rightGuard head (List.Mem.head tail)
        have reducedLeft :
            forall letter, letter ∈ parityReduce tail ->
              letter ∈ leftContext := by
          intro letter reducedMember
          exact leftGuard letter <| List.Mem.tail head <|
            source_mem_of_parityReduce_mem reducedMember
        have reducedRight :
            forall letter, letter ∈ parityReduce tail ->
              letter ∈ suffix := by
          intro letter reducedMember
          exact rightGuard letter <| List.Mem.tail head <|
            source_mem_of_parityReduce_mem reducedMember
        have blockLeft :
            forall letter, letter ∈ head :: parityReduce tail ->
              letter ∈ leftContext := by
          intro letter blockMember
          rcases List.mem_cons.mp blockMember with equal | reducedMember
          · simpa [equal] using headLeft
          · exact reducedLeft letter reducedMember
        have blockRight :
            forall letter, letter ∈ head :: parityReduce tail ->
              letter ∈ suffix := by
          intro letter blockMember
          rcases List.mem_cons.mp blockMember with equal | reducedMember
          · simpa [equal] using headRight
          · exact reducedRight letter reducedMember
        have expose :
            (head :: parityReduce tail).Perm
              (head :: head :: (parityReduce tail).erase head) :=
          List.Perm.cons head (List.perm_cons_erase member)
        have arranged :=
          listDerivesTwoSidedGuardedPermutation
            leftContext suffix blockLeft blockRight expose
        have deleted :=
          listDerivesDeleteAdjacentPairWithGuards
            head leftContext ((parityReduce tail).erase head ++ suffix)
            headLeft
            (List.mem_append.mpr (Or.inr headRight))
        have arranged' : ListDerives
            (leftContext ++ [head] ++ parityReduce tail ++ suffix)
            (leftContext ++ [head, head] ++
              (parityReduce tail).erase head ++ suffix) := by
          simpa [List.append_assoc] using arranged
        have deleted' : ListDerives
            (leftContext ++ [head, head] ++
              (parityReduce tail).erase head ++ suffix)
            (leftContext ++ (parityReduce tail).erase head ++ suffix) := by
          simpa [List.append_assoc] using deleted
        have cancelled :
            ListDerives
              (leftContext ++ [head] ++ parityReduce tail ++ suffix)
              (leftContext ++ (parityReduce tail).erase head ++ suffix) := by
          simpa [List.append_assoc] using arranged'.trans deleted'
        simpa [parityReduce, member, List.append_assoc] using
          tailDerivation.trans cancelled
      · simpa [parityReduce, member, List.append_assoc] using
          tailDerivation

/-- Normalize a changing suffix to its complete affine segment profile. Every
source letter is retained in the fixed leftContext, which supplies the left-hand
witnesses absent from the one-sided affine proof. -/
theorem listDerivesAffineNormalWithLeftGuard
    (leftContext : List Nat) :
    forall letters : List Nat,
      (forall letter, letter ∈ letters -> letter ∈ leftContext) ->
      ListDerives
        (leftContext ++ letters)
        (leftContext ++ affineNormalList letters)
  | [], _ => by
      simpa [affineNormalList, affineParityNormalSegments,
        affineParityRender] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis) leftContext)
  | head :: tail, leftGuard => by
      have tailLeftGuard :
          forall letter, letter ∈ tail ->
            letter ∈ leftContext ++ [head] := by
        intro letter member
        exact List.mem_append.mpr <| Or.inl <|
          leftGuard letter (List.Mem.tail head member)
      have tailDerivation :=
        listDerivesAffineNormalWithLeftGuard
          (leftContext ++ [head]) tail tailLeftGuard
      cases segmentsEq :
          affineParityNormalSegments tail with
      | nil =>
          have whole :
              affineParityNormalSegments (head :: tail) =
                [⟨[], head⟩] := by
            rw [affineParityNormalSegments, segmentsEq]
          simpa [affineNormalList, segmentsEq, whole,
            affineParityRender, List.append_assoc] using tailDerivation
      | cons segment rest =>
          cases segment with
          | mk parity marker =>
              have segmentsNormal :=
                affineParityNormalSegments_normal tail
              rw [segmentsEq] at segmentsNormal
              cases segmentsNormal with
              | cons parityNodup markerFresh parityGuard restNormal =>
                  by_cases headMarker :
                      head ∈ affineParityMarkers
                        (⟨parity, marker⟩ :: rest)
                  · have whole :
                        affineParityNormalSegments (head :: tail) =
                          ⟨affineParityToggle head parity, marker⟩ ::
                            rest := by
                        rw [affineParityNormalSegments, segmentsEq]
                        exact if_pos headMarker
                    have markerSource :
                        forall letter,
                          letter ∈ affineParityMarkers
                              (⟨parity, marker⟩ :: rest) ->
                            letter ∈ tail := by
                      intro letter member
                      apply
                        (mem_affineBarrierSequence_iff
                          letter tail).mp
                      simpa [affineBarrierSequence, segmentsEq] using member
                    have headLeft : head ∈ leftContext :=
                      leftGuard head (List.Mem.head tail)
                    have headRight :
                        head ∈ marker :: affineParityRender rest := by
                      have markerCases :
                          head = marker ∨
                            head ∈ affineParityMarkers rest := by
                        simpa [affineParityMarkers] using headMarker
                      rcases markerCases with equal | member
                      · simpa [equal]
                      · exact List.Mem.tail marker <|
                          affineParityMarker_mem_render member
                    have parityLeft :
                        forall letter, letter ∈ parity ->
                          letter ∈ leftContext := by
                      intro letter member
                      have markerMember :
                          letter ∈ affineParityMarkers
                              (⟨parity, marker⟩ :: rest) := by
                        rcases parityGuard letter member with equal | restMember
                        · simpa [affineParityMarkers, equal]
                        · simp [affineParityMarkers, restMember]
                      exact leftGuard letter <| List.Mem.tail head <|
                        markerSource letter markerMember
                    have parityRight :
                        forall letter, letter ∈ parity ->
                          letter ∈ marker :: affineParityRender rest := by
                      intro letter member
                      rcases parityGuard letter member with equal | restMember
                      · simpa [equal]
                      · exact List.Mem.tail marker <|
                          affineParityMarker_mem_render restMember
                    have toggled :=
                      listDerivesToggleBetweenGuards
                        leftContext parity
                        (marker :: affineParityRender rest)
                        head headLeft headRight parityLeft parityRight
                    have second :
                        ListDerives
                          (leftContext ++ [head] ++ affineNormalList tail)
                          (leftContext ++
                            affineNormalList (head :: tail)) := by
                      simpa [affineNormalList, segmentsEq, whole,
                        affineParityRender, List.append_assoc] using toggled
                    simpa [List.append_assoc] using
                      tailDerivation.trans second
                  · have whole :
                        affineParityNormalSegments (head :: tail) =
                          ⟨[], head⟩ :: ⟨parity, marker⟩ :: rest := by
                      rw [affineParityNormalSegments, segmentsEq]
                      exact if_neg headMarker
                    simpa [affineNormalList, segmentsEq, whole,
                      affineParityRender, List.append_assoc] using
                        tailDerivation

/-- Dual one-sided affine normalization. Reversal exchanges the fixed left
guard with a fixed right guard and is admissible for the candidate basis. -/
theorem listDerivesAffineNormalWithRightGuard
    (letters suffix : List Nat)
    (rightGuard :
      forall letter, letter ∈ letters -> letter ∈ suffix) :
    ListDerives
      (letters ++ suffix)
      (reverseAffineNormalList letters ++ suffix) := by
  have reversedGuard :
      forall letter, letter ∈ letters.reverse ->
        letter ∈ suffix.reverse := by
    intro letter member
    have sourceMember : letter ∈ letters := by
      simpa using member
    have suffixMember := rightGuard letter sourceMember
    simpa using suffixMember
  have forward :=
    listDerivesAffineNormalWithLeftGuard
      suffix.reverse letters.reverse reversedGuard
  have reversed := listDerivesReverse forward
  simpa [reverseAffineNormalList, List.reverse_append,
    List.append_assoc] using reversed

theorem listDerivesPowerExpansion :
    forall letters : List Nat,
      ListDerives letters ((letters ++ letters) ++ letters)
  | [] =>
      SemigroupBasis.CoRoots.S5_107.ListDerives.empty
  | head :: tail => by
      have expanded :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
          derivesPowerExpansion
            (SemigroupBasis.CoRoots.S5_107.listWordOfCons head tail)
      simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
        Word.toList_append, List.append_assoc] using expanded

/-- Every list derives to the complete three-block normal form. The outer
copies retain the forward and reversed affine segment profiles; after those
copies have been fixed, they guard parity reduction of the middle copy. -/
theorem listDerivesRegularOrthogroupNormal
    (letters : List Nat) :
    ListDerives letters (regularOrthogroupNormalList letters) := by
  have expanded := listDerivesPowerExpansion letters
  have leftNormalized :=
    listDerivesAffineNormalWithRightGuard
      letters (letters ++ letters)
      (fun letter member =>
        List.mem_append.mpr (Or.inl member))
  have rightNormalized :=
    listDerivesAffineNormalWithLeftGuard
      (reverseAffineNormalList letters ++ letters)
      letters
      (fun letter member =>
        List.mem_append.mpr (Or.inr member))
  have middleNormalized :=
    listDerivesParityReduceBetweenGuards
      (reverseAffineNormalList letters)
      letters
      (affineNormalList letters)
      (fun _ member => mem_reverseAffineNormalList_of_mem member)
      (fun _ member => mem_affineNormalList_of_mem member)
  have leftNormalized' : ListDerives
      ((letters ++ letters) ++ letters)
      ((reverseAffineNormalList letters ++ letters) ++ letters) := by
    simpa only [List.append_assoc] using leftNormalized
  have combined :=
    expanded.trans <| leftNormalized'.trans <|
      rightNormalized.trans middleNormalized
  simpa [regularOrthogroupNormalList, oddParitySupport,
    List.append_assoc] using combined

end SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroup
