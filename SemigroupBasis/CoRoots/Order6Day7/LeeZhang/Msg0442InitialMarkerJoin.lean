import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0442CyclicSemantics

/-! A reusable initial-marker join proof. The assumptions are derivational
rules, an already proved lower basis, and actual left reductivity. All are
discharged for each literal approved system before any class endpoint. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.InitialMarkerJoin

open SemigroupBasis Examples
open Msg0442Cyclic (bindAppend bindBind bindSingleton)

universe u

abbrev markerTable := Msg0442Cyclic.initialTable

theorem initialEval (word : Word Nat) (tested : Nat) :
    markerTable.semigroup.eval (Msg0442Cyclic.separator tested) word =
      if tested ∈ word.tail then (0 : Fin 3) else if word.head = tested then 1 else 2 := by
  change Msg0442Cyclic.markerTable.semigroup.opposite.eval (Msg0442Cyclic.separator tested) word = _
  rw [Semigroup.eval_opposite_eq_reverse]
  have reversed : word.reverse = wordOfPrefixFinal word.tail.reverse word.head := by
    apply Word.toList_injective
    rw [Word.toList_reverse, toList_wordOfPrefixFinal]
    exact List.reverse_cons
  rw [reversed, Msg0442Cyclic.separatorEval]
  simp

theorem tailMembership (identity : Identity Nat) (valid : identity.SatisfiedBy markerTable.semigroup)
    (tested : Nat) : tested ∈ identity.lhs.tail ↔ tested ∈ identity.rhs.tail := by
  have evaluated := valid (Msg0442Cyclic.separator tested)
  rw [initialEval, initialEval] at evaluated
  by_cases left : tested ∈ identity.lhs.tail <;> by_cases right : tested ∈ identity.rhs.tail
  · exact iff_of_true left right
  · simp only [left, right, if_true, if_false] at evaluated
    split at evaluated <;> contradiction
  · simp only [left, right, if_true, if_false] at evaluated
    split at evaluated <;> contradiction
  · exact iff_of_false left right

theorem simpleHead (identity : Identity Nat) (valid : identity.SatisfiedBy markerTable.semigroup)
    (tested : Nat) :
    (identity.lhs.head = tested ∧ tested ∉ identity.lhs.tail) ↔
      (identity.rhs.head = tested ∧ tested ∉ identity.rhs.tail) := by
  have evaluated := valid (Msg0442Cyclic.separator tested)
  have observe (word : Word Nat) :
      markerTable.semigroup.eval (Msg0442Cyclic.separator tested) word = (1 : Fin 3) ↔
        word.head = tested ∧ tested ∉ word.tail := by
    rw [initialEval]
    by_cases member : tested ∈ word.tail <;> by_cases equal : word.head = tested <;> simp [member, equal]
  rw [← observe identity.lhs, ← observe identity.rhs, evaluated]

def LeftReductive {A : Type u} (G : Semigroup A) : Prop :=
  ∀ x y, (∀ c, G.mul c x = G.mul c y) → x = y

theorem evalAgree {A : Type u} (G : Semigroup A) (first second : Nat → A)
    (word : Word Nat) (agree : ∀ x, x ∈ word.toList → first x = second x) :
    G.eval first word = G.eval second word := by
  rcases word with ⟨head, tail⟩
  induction tail generalizing head with
  | nil => exact agree head (by simp [Word.toList])
  | cons next rest ih =>
      have tailAgree : ∀ x, x ∈ (Word.mk next rest).toList → first x = second x :=
        fun x member => agree x (by simpa [Word.toList] using List.mem_cons_of_mem head member)
      have tailEqual := ih next tailAgree
      change G.eval first (Word.singleton head ++ Word.mk next rest) =
        G.eval second (Word.singleton head ++ Word.mk next rest)
      rw [Semigroup.eval_append, Semigroup.eval_append, Semigroup.eval_singleton,
        Semigroup.eval_singleton, agree head (by simp [Word.toList]), tailEqual]

/-- A fresh variable is varied independently; no identity element is assumed. -/
theorem freshHeadCancel {A : Type u} (G : Semigroup A) (reductive : LeftReductive G)
    (head : Nat) (left right : Word Nat) (leftAbsent : head ∉ left.toList)
    (rightAbsent : head ∉ right.toList)
    (valid : (Identity.mk (Word.singleton head ++ left) (Word.singleton head ++ right)).SatisfiedBy G) :
    (Identity.mk left right).SatisfiedBy G := by
  intro valuation
  apply reductive
  intro test
  let replaced : Nat → A := fun x => if x = head then test else valuation x
  have unchanged (word : Word Nat) (absent : head ∉ word.toList) :
      G.eval replaced word = G.eval valuation word := by
    apply evalAgree
    intro x member
    have different : x ≠ head := by intro equal; subst x; exact absent member
    simp [replaced, different]
  have value : replaced head = test := by simp [replaced]
  have evaluated := valid replaced
  simp only [Semigroup.eval_append, Semigroup.eval_singleton, value,
    unchanged left leftAbsent, unchanged right rightAbsent] at evaluated
  exact evaluated

structure Rules (basis lowerBasis : List (Identity Nat)) where
  lift : ∀ {left right : Word Nat}, Derives lowerBasis left right → ∀ stem : Word Nat,
    Derives basis (stem ++ left) (stem ++ right)
  power : ∀ word : Word Nat, Derives basis (word ++ word) ((word ++ word) ++ word)
  headInside : ∀ x y : Word Nat,
    Derives basis ((x ++ y) ++ x) (((x ++ x) ++ y) ++ x)
  mix : ∀ a b word : Word Nat,
    Derives basis ((((a ++ b) ++ a) ++ a) ++ word) ((((b ++ a) ++ a) ++ b) ++ word)

theorem splitMember (tested : Nat) (letters : List Nat) (member : tested ∈ letters) :
    ∃ p q, letters = p ++ tested :: q := by
  induction letters with
  | nil => simp at member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with equal | later
      · subst head
        exact ⟨[], tail, rfl⟩
      · obtain ⟨p, q, equal⟩ := ih later
        exact ⟨head :: p, q, by rw [equal]; rfl⟩

theorem appendList {basis : List (Identity Nat)} {left right : Word Nat}
    (derivation : Derives basis left right) (suffix : List Nat) :
    Derives basis (Word.mk left.head (left.tail ++ suffix)) (Word.mk right.head (right.tail ++ suffix)) := by
  rcases suffix with _ | ⟨head, tail⟩
  · simpa using derivation
  · exact Derives.appendRight derivation (Word.mk head tail)

namespace Rules

variable {basis lowerBasis : List (Identity Nat)}

theorem repeatedHeadInsert (rules : Rules basis lowerBasis) (word : Word Nat)
    (repeated : word.head ∈ word.tail) :
    Derives basis word (Word.singleton word.head ++ word) := by
  rcases word with ⟨a, tail⟩
  obtain ⟨p, q, equal⟩ := splitMember a tail repeated
  subst tail
  rcases p with _ | ⟨b, rest⟩
  · simpa [Word.singleton, Word.append] using appendList (rules.power (Word.singleton a)) q
  · simpa [Word.singleton, Word.append, List.append_assoc] using
      appendList (rules.headInside (Word.singleton a) (Word.mk b rest)) q

/-- Mixing two repeated heads through the lower theory. The two padding
derivations are proved, not assumed to preserve the upper factor. -/
theorem repeatedComplete {A : Type u} (rules : Rules basis lowerBasis) (G : Semigroup A)
    (models : Models G basis) (lowerComplete : BasisFor G lowerBasis)
    (identity : Identity Nat) (valid : identity.SatisfiedBy G)
    (leftRepeated : identity.lhs.head ∈ identity.lhs.tail)
    (rightRepeated : identity.rhs.head ∈ identity.rhs.tail) :
    Derives basis identity.lhs identity.rhs := by
  let a := Word.singleton identity.lhs.head
  let b := Word.singleton identity.rhs.head
  have ownLeft := rules.repeatedHeadInsert identity.lhs leftRepeated
  have ownRight := rules.repeatedHeadInsert identity.rhs rightRepeated
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
    (rightValid : identity.SatisfiedBy G) : Derives basis identity.lhs identity.rhs := by
  rcases identity with ⟨⟨a, p⟩, ⟨b, q⟩⟩
  have members := tailMembership ⟨Word.mk a p, Word.mk b q⟩ markerValid
  by_cases repeated : a ∈ p
  · have rightRepeated : b ∈ q := by
      apply Decidable.byContradiction
      intro absent
      have forced := (simpleHead ⟨Word.mk a p, Word.mk b q⟩ markerValid b).mpr ⟨rfl, absent⟩
      exact forced.2 (by simpa only [← forced.1] using repeated)
    exact rules.repeatedComplete G models lowerComplete ⟨Word.mk a p, Word.mk b q⟩
      rightValid repeated rightRepeated
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
end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.InitialMarkerJoin
