import SemigroupBasis.CoRoots.Order6SporadicSection22E7Detectors

/-! Canonical uniqueness for E7, transcribing the observations on paper p99.
The last-letter probe handles differing old tails. The power probe handles
the only ambiguity it leaves: no tail versus a second current first letter.
Both probes explicitly include the final-block/right-guard boundary. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection22.E7
open SemigroupBasis

theorem shortList_cases (letters : List Nat) (short : letters.length ≤ 1) :
    letters = [] ∨ ∃ x, letters = [x] := by
  cases letters with
  | nil => exact Or.inl rfl
  | cons x xs =>
      cases xs with
      | nil => exact Or.inr ⟨x,rfl⟩
      | cons y ys => simp at short

def lastLetter (block : CanonicalBlock) : Nat := block.extra.headD block.letter

theorem lastLetter_known (seen : List Nat) (first : CanonicalBlock) (rest : List CanonicalBlock)
    (good : WellFormed seen (first :: rest)) : lastLetter first ∈ first.letter :: seen := by
  rcases shortList_cases first.extra good.2.1 with empty | ⟨x,single⟩
  · simp [lastLetter,empty]
  · have member := good.2.2.1 x (by simp [single])
    simpa [lastLetter,single] using member

theorem block_last_value (seen stem : List Nat) (first : CanonicalBlock) (rest : List CanonicalBlock)
    (good : WellFormed seen (first :: rest)) (known : ∀ x ∈ stem, x ∈ seen)
    (mark : Nat) (markKnown : mark ∈ first.letter :: seen) :
    sandwich (markerVal mark (nextLetter rest) 4) (stem ++ renderBlocks (first :: rest)) =
      if lastLetter first = mark then 2 else 0 := by
  have noStop : ∀ x ∈ first.letter :: seen, nextLetter rest ≠ some x :=
    fun x member => nextLetter_fresh _ rest good.2.2.2 x member
  have ready := marker_ready rest mark 4 (noStop mark markKnown)
  rcases shortList_cases first.extra good.2.1 with empty | ⟨x,single⟩
  · have observed := sandwich_marker_last stem first.letter (renderBlocks rest) mark (nextLetter rest)
      (fun x member => noStop x (List.mem_cons_of_mem first.letter (known x member)))
      (noStop first.letter (by simp)) ready
    simpa [renderBlocks,empty,lastLetter,List.append_assoc] using observed
  · have xKnown := good.2.2.1 x (by simp [single])
    have stemKnown : ∀ y ∈ stem ++ [first.letter], y ∈ first.letter :: seen := by
      intro y member
      rcases List.mem_append.mp member with prior | current
      · exact List.mem_cons_of_mem first.letter (known y prior)
      · have same : y = first.letter := by simpa using current
        simp [same]
    have observed := sandwich_marker_last (stem ++ [first.letter]) x (renderBlocks rest)
      mark (nextLetter rest) (fun y member => noStop y (stemKnown y member)) (noStop x xKnown) ready
    simpa [renderBlocks,single,lastLetter,List.append_assoc] using observed

theorem empty_self_impossible (seen stem : List Nat) (head : Nat)
    (left right : List CanonicalBlock) (fresh : head ∉ seen)
    (leftGood : WellFormed (head :: seen) left) (rightGood : WellFormed (head :: seen) right)
    (known : ∀ x ∈ stem, x ∈ seen) (sameStop : nextLetter left = nextLetter right)
    (equal : ∀ valuation,
      sandwich valuation (stem ++ [head] ++ renderBlocks left) =
      sandwich valuation (stem ++ [head,head] ++ renderBlocks right)) : False := by
  have noMark : ∀ x ∈ stem, x ≠ head := by
    intro x member same
    exact fresh (by simpa [same] using known x member)
  have noStop : ∀ x ∈ stem, nextLetter left ≠ some x :=
    fun x member => nextLetter_fresh _ left leftGood x (List.mem_cons_of_mem head (known x member))
  have leftReady := marker_ready left head 1 (nextLetter_fresh _ left leftGood head (by simp))
  have rightReady := marker_ready right head 1 (nextLetter_fresh _ right rightGood head (by simp))
  rw [← sameStop] at rightReady
  have leftValue := (sandwich_marker_power stem (renderBlocks left) head (nextLetter left) noMark noStop leftReady).1
  have rightValue := (sandwich_marker_power stem (renderBlocks right) head (nextLetter left) noMark noStop rightReady).2
  have contradiction := equal (markerVal head (nextLetter left) 1)
  rw [leftValue,rightValue] at contradiction
  exact (by decide : (2 : Fin 6) ≠ 0) contradiction

theorem block_extra_eq (seen stem : List Nat) (first second : CanonicalBlock)
    (left right : List CanonicalBlock)
    (leftGood : WellFormed seen (first :: left)) (rightGood : WellFormed seen (second :: right))
    (known : ∀ x ∈ stem, x ∈ seen) (sameHead : first.letter = second.letter)
    (sameStop : nextLetter left = nextLetter right)
    (equal : ∀ valuation,
      sandwich valuation (stem ++ renderBlocks (first :: left)) =
      sandwich valuation (stem ++ renderBlocks (second :: right))) : first.extra = second.extra := by
  have lastEq : lastLetter first = lastLetter second := by
    have markKnown := lastLetter_known seen first left leftGood
    have leftValue := block_last_value seen stem first left leftGood known (lastLetter first) markKnown
    have rightKnown : lastLetter first ∈ second.letter :: seen := by simpa [← sameHead] using markKnown
    have rightValue := block_last_value seen stem second right rightGood known (lastLetter first) rightKnown
    rw [← sameStop] at rightValue
    have observed := equal (markerVal (lastLetter first) (nextLetter left) 4)
    rw [leftValue,rightValue] at observed
    by_cases same : lastLetter first = lastLetter second
    · exact same
    · have reverseDifferent : lastLetter second ≠ lastLetter first := Ne.symm same
      have impossible : (2 : Fin 6) = 0 := by simpa [reverseDifferent] using observed
      exact False.elim ((by decide : (2 : Fin 6) ≠ 0) impossible)
  rcases shortList_cases first.extra leftGood.2.1 with leftEmpty | ⟨x,leftSingle⟩
  · rcases shortList_cases second.extra rightGood.2.1 with rightEmpty | ⟨y,rightSingle⟩
    · exact leftEmpty.trans rightEmpty.symm
    · have repeated : y = first.letter := by simpa [lastLetter,leftEmpty,rightSingle] using lastEq.symm
      apply False.elim
      apply empty_self_impossible seen stem first.letter left right leftGood.1 leftGood.2.2.2
        (by simpa [← sameHead] using rightGood.2.2.2) known sameStop
      intro valuation
      simpa [renderBlocks,leftEmpty,rightSingle,repeated,← sameHead,List.append_assoc] using equal valuation
  · rcases shortList_cases second.extra rightGood.2.1 with rightEmpty | ⟨y,rightSingle⟩
    · have repeated : x = first.letter := by simpa [lastLetter,leftSingle,rightEmpty,← sameHead] using lastEq
      apply False.elim
      apply empty_self_impossible seen stem first.letter right left leftGood.1
        (by simpa [← sameHead] using rightGood.2.2.2) leftGood.2.2.2 known sameStop.symm
      intro valuation
      simpa [renderBlocks,leftSingle,rightEmpty,repeated,← sameHead,List.append_assoc] using (equal valuation).symm
    · have same : x = y := by simpa [lastLetter,leftSingle,rightSingle] using lastEq
      simp [leftSingle,rightSingle,same]

theorem render_unique : ∀ left right : List CanonicalBlock, ∀ seen stem : List Nat,
    WellFormed seen left → WellFormed seen right →
    left.map CanonicalBlock.letter = right.map CanonicalBlock.letter →
    (∀ x ∈ stem, x ∈ seen) →
    (∀ valuation, sandwich valuation (stem ++ renderBlocks left) =
      sandwich valuation (stem ++ renderBlocks right)) → left = right := by
  intro left
  induction left with
  | nil =>
      intro right seen stem leftGood rightGood labels known equal
      cases right with
      | nil => rfl
      | cons second rest => simp at labels
  | cons first left ih =>
      intro right seen stem leftGood rightGood labels known equal
      cases right with
      | nil => simp at labels
      | cons second right =>
          have pair := List.cons.inj labels
          have extras := block_extra_eq seen stem first second left right leftGood rightGood known pair.1
            (nextLetter_eq_of_labels pair.2) equal
          have firstEq : first = second := by
            cases first with
            | mk a xs =>
                cases second with
                | mk b ys =>
                    have heads : a = b := pair.1
                    have tails : xs = ys := extras
                    cases heads; cases tails; rfl
          subst second
          have knownNext : ∀ x ∈ stem ++ [first.letter] ++ first.extra, x ∈ first.letter :: seen := by
            intro x member
            rcases List.mem_append.mp member with prior | extra
            · rcases List.mem_append.mp prior with old | current
              · exact List.mem_cons_of_mem first.letter (known x old)
              · have same : x = first.letter := by simpa using current
                simp [same]
            · exact leftGood.2.2.1 x extra
          have tailEq := ih right (first.letter :: seen) (stem ++ [first.letter] ++ first.extra)
            leftGood.2.2.2 rightGood.2.2.2 pair.2 knownNext
            (fun valuation => by simpa [renderBlocks,List.append_assoc] using equal valuation)
          exact congrArg (List.cons first) tailEq

#print axioms block_last_value
#print axioms empty_self_impossible
#print axioms block_extra_eq
#print axioms render_unique

end SemigroupBasis.CoRoots.Order6SporadicSection22.E7
