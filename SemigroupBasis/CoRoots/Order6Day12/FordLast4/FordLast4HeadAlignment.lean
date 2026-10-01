import SemigroupBasis.CoRoots.Order6Day12.FordLast4.FordLast4PrefixLift

/-! Equal heads and lower-core validity suffice without any rank or length
bound. Repeated heads are duplicated. Simple heads are evaluated at the
actual left identity, only after proving absence from both nonempty tails. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day12.FordLast4

open SemigroupBasis

theorem appendList {left right : Word Nat} (derivation : Derives basis left right)
    (suffix : List Nat) :
    Derives basis (Word.mk left.head (left.tail ++ suffix))
      (Word.mk right.head (right.tail ++ suffix)) := by
  cases suffix with
  | nil => simpa using derivation
  | cons letter rest => exact derivation.appendRight (Word.mk letter rest)

theorem duplicateRepeatedHead (head : Nat) (tail : List Nat) (occurs : head ∈ tail) :
    Derives basis (Word.mk head tail) (Word.mk head (head :: tail)) := by
  obtain ⟨front, back, rfl⟩ := List.mem_iff_append.mp occurs
  cases front with
  | nil =>
      simpa [Word.singleton, Word.append] using
        appendList (rawLaw00 (Word.singleton head)) back
  | cons next rest =>
      simpa [Word.singleton, Word.append, List.append_assoc] using
        appendList (rawLaw01 (Word.singleton head) (Word.mk next rest)).symm back

theorem headSimple_iff (head : Nat) (tail : List Nat) :
    SemigroupBasis.CoRoots.S5_107.SimpleIn (Word.mk head tail) head ↔ head ∉ tail := by
  have count : (head :: tail).count head = tail.count head + 1 := by simp
  constructor
  · intro simple
    change (head :: tail).count head = 1 at simple
    rw [count] at simple
    have zero : tail.count head = 0 := by omega
    exact List.count_eq_zero.mp zero
  · intro absent
    have zero : tail.count head = 0 := List.count_eq_zero.mpr absent
    change (head :: tail).count head = 1
    rw [count, zero]

theorem singletonRigid (head : Nat) (word : Word Nat)
    (same : LowerSignature (Word.singleton head) word) : Word.singleton head = word := by
  have onlyHead : ∀ letter, letter ∈ word.toList → letter = head := by
    intro letter member
    have oldMember := (same.support letter).mpr member
    simpa using oldMember
  cases word with
  | mk first tail =>
      have firstEq : first = head := onlyHead first (by simp [Word.toList])
      subst first
      have simple : SemigroupBasis.CoRoots.S5_107.SimpleIn (Word.mk head tail) head :=
        (same.simple head).mp (by simp [SemigroupBasis.CoRoots.S5_107.SimpleIn])
      have absent : head ∉ tail := (headSimple_iff head tail).mp simple
      have tailNil : tail = [] := by
        cases tail with
        | nil => rfl
        | cons letter rest =>
            have letterEq : letter = head := onlyHead letter (by simp [Word.toList])
            exact False.elim (absent (by simp [letterEq]))
      subst tail
      rfl

theorem evalCongrOnLetters {S : Type} (semigroup : Semigroup S) (word : Word Nat)
    (first second : Nat → S)
    (agree : ∀ letter, letter ∈ word.toList → first letter = second letter) :
    semigroup.eval first word = semigroup.eval second word := by
  have fold : ∀ (letters : List Nat) (initial : S),
      (∀ letter, letter ∈ letters → first letter = second letter) →
      letters.foldl (fun acc letter => semigroup.mul acc (first letter)) initial =
        letters.foldl (fun acc letter => semigroup.mul acc (second letter)) initial := by
    intro letters
    induction letters with
    | nil => intro initial _; rfl
    | cons letter rest induction =>
        intro initial agrees
        simp only [List.foldl_cons]
        rw [agrees letter (by simp)]
        exact induction _ (fun next member => agrees next (by simp [member]))
  cases word with
  | mk head tail =>
      change tail.foldl (fun acc letter => semigroup.mul acc (first letter)) (first head) =
        tail.foldl (fun acc letter => semigroup.mul acc (second letter)) (second head)
      rw [agree head (by simp [Word.toList])]
      exact fold tail _ (fun letter member => agree letter (by simp [Word.toList, member]))

theorem eraseSimpleHead (head : Nat) (left right : Word Nat)
    (absentLeft : head ∉ left.toList) (absentRight : head ∉ right.toList)
    (valid : (Identity.mk (Word.singleton head ++ left) (Word.singleton head ++ right)).SatisfiedBy
      coreTable.semigroup) :
    (Identity.mk left right).SatisfiedBy coreTable.semigroup := by
  intro valuation
  let modified : Nat → Fin 5 := fun letter => if letter = head then 4 else valuation letter
  have agreeLeft : coreTable.semigroup.eval modified left = coreTable.semigroup.eval valuation left := by
    apply evalCongrOnLetters
    intro letter member
    have different : letter ≠ head := by
      intro equal
      subst letter
      exact absentLeft member
    simp [modified, different]
  have agreeRight : coreTable.semigroup.eval modified right = coreTable.semigroup.eval valuation right := by
    apply evalCongrOnLetters
    intro letter member
    have different : letter ≠ head := by
      intro equal
      subst letter
      exact absentRight member
    simp [modified, different]
  have tested := valid modified
  change coreTable.semigroup.eval modified (Word.singleton head ++ left) =
    coreTable.semigroup.eval modified (Word.singleton head ++ right) at tested
  rw [Semigroup.eval_append, Semigroup.eval_append, Semigroup.eval_singleton] at tested
  have headValue : modified head = 4 := by simp [modified]
  rw [headValue] at tested
  change coreTable.mul (4 : Fin 5) (coreTable.semigroup.eval modified left) =
    coreTable.mul (4 : Fin 5) (coreTable.semigroup.eval modified right) at tested
  rw [coreLeftUnit, coreLeftUnit, agreeLeft, agreeRight] at tested
  exact tested

theorem derivesOfHeadAndLowerValid (left right : Word Nat) (heads : left.head = right.head)
    (valid : (Identity.mk left right).SatisfiedBy coreTable.semigroup) : Derives basis left right := by
  have same := validLowerSignature
    (Identity.mk left right) valid
  rcases left with ⟨head, leftTail⟩
  rcases right with ⟨other, rightTail⟩
  change head = other at heads
  subst other
  cases leftTail with
  | nil =>
      have equal : Word.mk head [] = Word.mk head rightTail := singletonRigid head _ same
      rw [equal]
      exact Derives.refl _
  | cons first rest =>
      cases rightTail with
      | nil =>
          have equal : Word.mk head [] = Word.mk head (first :: rest) := singletonRigid head _ same.symm
          rw [← equal]
          exact Derives.refl _
      | cons second remaining =>
          by_cases repeated : head ∈ first :: rest
          · have repeatedRight : head ∈ second :: remaining := by
              apply Decidable.byContradiction
              intro missing
              have rightSimple := (headSimple_iff head (second :: remaining)).mpr missing
              have leftSimple := (same.simple head).mpr rightSimple
              exact (headSimple_iff head (first :: rest)).mp leftSimple repeated
            have duplicateLeft := duplicateRepeatedHead head (first :: rest) repeated
            have duplicateRight := duplicateRepeatedHead head (second :: remaining) repeatedRight
            have middle := samePrefixOfLowerValid (Word.mk head (first :: rest))
              (Word.mk head (second :: remaining)) (Word.singleton head) valid
            exact duplicateLeft.trans (middle.trans duplicateRight.symm)
          · have leftSimple := (headSimple_iff head (first :: rest)).mpr repeated
            have rightSimple := (same.simple head).mp leftSimple
            have absentRight := (headSimple_iff head (second :: remaining)).mp rightSimple
            have tailValid := eraseSimpleHead head (Word.mk first rest) (Word.mk second remaining)
              repeated absentRight valid
            exact samePrefixOfLowerValid (Word.mk first rest) (Word.mk second remaining)
              (Word.singleton head) tailValid

end SemigroupBasis.CoRoots.Order6Day12.FordLast4

