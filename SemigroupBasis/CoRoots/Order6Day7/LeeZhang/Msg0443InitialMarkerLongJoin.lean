import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0442InitialMarkerJoin

/-! Long-word initial-marker joins. Short square words are not expanded;
nontrivial lower derivations must first supply the length-at-least-three stratum. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.InitialMarkerLongJoin

open SemigroupBasis InitialMarkerJoin
universe u

structure Rules (basis lowerBasis : List (Identity Nat)) where
  lift : ∀ {left right : Word Nat}, Derives lowerBasis left right → ∀ stem : Word Nat,
    Derives basis (stem ++ left) (stem ++ right)
  squarePrefix : ∀ word suffix : Word Nat,
    Derives basis ((word ++ word) ++ suffix) (((word ++ word) ++ word) ++ suffix)
  headInside : ∀ x y : Word Nat,
    Derives basis ((x ++ y) ++ x) (((x ++ x) ++ y) ++ x)
  mix : ∀ a b word : Word Nat,
    Derives basis ((((a ++ b) ++ a) ++ a) ++ word) ((((b ++ a) ++ a) ++ b) ++ word)

namespace Rules

variable {basis lowerBasis : List (Identity Nat)}

theorem repeatedHeadInsert (rules : Rules basis lowerBasis) (word : Word Nat)
    (repeated : word.head ∈ word.tail) (long : 3 ≤ word.toList.length) :
    Derives basis word (Word.singleton word.head ++ word) := by
  rcases word with ⟨a, tail⟩
  obtain ⟨p, q, equal⟩ := splitMember a tail repeated
  subst tail
  rcases p with _ | ⟨b, rest⟩
  · rcases q with _ | ⟨b, rest⟩
    · simp [Word.toList] at long
    · simpa [Word.singleton, Word.append] using rules.squarePrefix (Word.singleton a) (Word.mk b rest)
  · simpa [Word.singleton, Word.append, List.append_assoc] using
      appendList (rules.headInside (Word.singleton a) (Word.mk b rest)) q

/-- Mixing two repeated heads through the lower theory. The two padding
derivations are proved, not assumed to preserve the upper factor. -/
theorem repeatedComplete {A : Type u} (rules : Rules basis lowerBasis) (G : Semigroup A)
    (models : Models G basis) (lowerComplete : BasisFor G lowerBasis)
    (identity : Identity Nat) (valid : identity.SatisfiedBy G)
    (leftRepeated : identity.lhs.head ∈ identity.lhs.tail)
    (rightRepeated : identity.rhs.head ∈ identity.rhs.tail)
    (leftLong : 3 ≤ identity.lhs.toList.length) (rightLong : 3 ≤ identity.rhs.toList.length) :
    Derives basis identity.lhs identity.rhs := by
  let a := Word.singleton identity.lhs.head
  let b := Word.singleton identity.rhs.head
  have ownLeft := rules.repeatedHeadInsert identity.lhs leftRepeated leftLong
  have ownRight := rules.repeatedHeadInsert identity.rhs rightRepeated rightLong
  have lower := lowerComplete.2 identity valid
  have da : Derives lowerBasis identity.lhs (a ++ identity.lhs) :=
    lowerComplete.2 ⟨identity.lhs, a ++ identity.lhs⟩ (Derives.sound models ownLeft)
  have dbRight : Derives lowerBasis identity.rhs (b ++ identity.rhs) :=
    lowerComplete.2 ⟨identity.rhs, b ++ identity.rhs⟩ (Derives.sound models ownRight)
  have db : Derives lowerBasis identity.lhs (b ++ identity.lhs) :=
    lower.trans (dbRight.trans (Derives.prepend b lower).symm)
  have padLeft : Derives lowerBasis identity.lhs (b ++ (a ++ (a ++ identity.lhs))) :=
    db.trans (Derives.prepend b (da.trans (Derives.prepend a da)))
  have padRight : Derives lowerBasis identity.lhs (a ++ (a ++ (b ++ identity.lhs))) :=
    da.trans (Derives.prepend a (da.trans (Derives.prepend a db)))
  have toMixed : Derives basis (a ++ identity.lhs) ((((a ++ b) ++ a) ++ a) ++ identity.lhs) := by
    simpa [Word.append_assoc] using rules.lift padLeft a
  have fromMixed : Derives basis ((((b ++ a) ++ a) ++ b) ++ identity.lhs) (b ++ identity.lhs) := by
    simpa [Word.append_assoc] using rules.lift padRight.symm b
  exact ownLeft.trans (toMixed.trans ((rules.mix a b identity.lhs).trans
    (fromMixed.trans ((rules.lift lower b).trans ownRight.symm))))

/-- The complete join argument: repeated heads use mixing, while a simple
head is common and fresh, so actual left reductivity cancels it. -/
theorem complete {A : Type u} (rules : Rules basis lowerBasis) (G : Semigroup A)
    (models : Models G basis) (lowerComplete : BasisFor G lowerBasis) (reductive : LeftReductive G)
    (identity : Identity Nat) (markerValid : identity.SatisfiedBy markerTable.semigroup)
    (rightValid : identity.SatisfiedBy G)
    (strata : identity.lhs = identity.rhs ∨ (3 ≤ identity.lhs.toList.length ∧ 3 ≤ identity.rhs.toList.length)) :
    Derives basis identity.lhs identity.rhs := by
  rcases strata with equal | long
  · rw [equal]
    exact Derives.refl _
  rcases identity with ⟨⟨a, p⟩, ⟨b, q⟩⟩
  have members := tailMembership ⟨Word.mk a p, Word.mk b q⟩ markerValid
  by_cases repeated : a ∈ p
  · have rightRepeated : b ∈ q := by
      apply Decidable.byContradiction
      intro absent
      have forced := (simpleHead ⟨Word.mk a p, Word.mk b q⟩ markerValid b).mpr ⟨rfl, absent⟩
      exact forced.2 (by simpa only [← forced.1] using repeated)
    exact rules.repeatedComplete G models lowerComplete ⟨Word.mk a p, Word.mk b q⟩
      rightValid repeated rightRepeated long.1 long.2
  · have forced := (simpleHead ⟨Word.mk a p, Word.mk b q⟩ markerValid a).mp ⟨rfl, repeated⟩
    have equal : b = a := forced.1
    subst b
    rcases p with _ | ⟨pHead, pTail⟩
    · rcases q with _ | ⟨qHead, qTail⟩
      · exact Derives.refl _
      · have impossible := (members qHead).mpr (by simp)
        simp at impossible
    · rcases q with _ | ⟨qHead, qTail⟩
      · have impossible := (members pHead).mp (by simp)
        simp at impossible
      · have tailValid := freshHeadCancel G reductive a (Word.mk pHead pTail) (Word.mk qHead qTail)
          (by simpa [Word.toList] using repeated) (by simpa [Word.toList] using forced.2) rightValid
        have lower := lowerComplete.2 ⟨Word.mk pHead pTail, Word.mk qHead qTail⟩ tailValid
        exact rules.lift lower (Word.singleton a)

end Rules
end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.InitialMarkerLongJoin
