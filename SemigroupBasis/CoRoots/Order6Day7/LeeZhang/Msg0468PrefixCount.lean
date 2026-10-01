import SemigroupBasis.CoRoots.S5_107ListDerives

/-! Unbounded, table-independent bookkeeping for counts before a first
occurrence. The crossing theorem is an actual induction on arbitrary lists,
not an assertion that the proposed signature is complete for any table. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.PrefixCount

def before (letter : Nat) : List Nat → List Nat
  | [] => []
  | head :: tail => if head = letter then [] else head :: before letter tail

@[simp] theorem before_nil (letter : Nat) : before letter [] = [] := rfl

@[simp] theorem before_self (letter : Nat) (tail : List Nat) :
    before letter (letter :: tail) = [] := by simp [before]

theorem before_cons_of_ne (letter head : Nat) (tail : List Nat) (different : head ≠ letter) :
    before letter (head :: tail) = head :: before letter tail := by simp [before, different]

theorem mem_before (letter tested : Nat) :
    ∀ {letters : List Nat}, tested ∈ before letter letters → tested ∈ letters
  | [], member => by simp at member
  | head :: tail, member => by
      by_cases equal : head = letter
      · simp [before, equal] at member
      · rw [before_cons_of_ne letter head tail equal] at member
        rcases List.mem_cons.mp member with same | rest
        · exact List.mem_cons.mpr (Or.inl same)
        · exact List.mem_cons_of_mem head (mem_before letter tested rest)

theorem not_mem_before (letter : Nat) : ∀ letters : List Nat, letter ∉ before letter letters
  | [] => by simp
  | head :: tail => by
      by_cases equal : head = letter
      · simp [before, equal]
      · simp [before, equal, Ne.symm equal, not_mem_before letter tail]

theorem before_eq_self_of_not_mem (letter : Nat) :
    ∀ {letters : List Nat}, letter ∉ letters → before letter letters = letters
  | [], _ => rfl
  | head :: tail, absent => by
      have different : head ≠ letter := fun same => absent (by simp [same])
      have restAbsent : letter ∉ tail := fun member => absent (List.mem_cons_of_mem head member)
      rw [before_cons_of_ne letter head tail different, before_eq_self_of_not_mem letter restAbsent]

theorem before_append_of_not_mem (letter : Nat) (left right : List Nat)
    (absent : letter ∉ left) : before letter (left ++ right) = left ++ before letter right := by
  induction left with
  | nil => rfl
  | cons head tail induction =>
      have different : head ≠ letter := fun same => absent (by simp [same])
      have restAbsent : letter ∉ tail := fun member => absent (List.mem_cons_of_mem head member)
      simp only [List.cons_append, before_cons_of_ne letter head _ different, induction restAbsent]

theorem before_append_of_mem (letter : Nat) (left right : List Nat)
    (member : letter ∈ left) : before letter (left ++ right) = before letter left := by
  induction left with
  | nil => simp at member
  | cons head tail induction =>
      by_cases equal : head = letter
      · simp [before, equal]
      · have restMember : letter ∈ tail := by simpa [Ne.symm equal] using member
        simp only [List.cons_append, before_cons_of_ne letter head _ equal, induction restMember]

def SameBeforeTwo (left right : List Nat) : Prop :=
  ∀ tested separator, min 2 ((before separator left).count tested) =
    min 2 ((before separator right).count tested)

theorem SameBeforeTwo.refl (letters : List Nat) : SameBeforeTwo letters letters := by
  intro tested separator
  rfl

theorem SameBeforeTwo.symm {left right : List Nat} (same : SameBeforeTwo left right) :
    SameBeforeTwo right left := fun tested separator => (same tested separator).symm

theorem SameBeforeTwo.trans {left middle right : List Nat}
    (first : SameBeforeTwo left middle) (second : SameBeforeTwo middle right) :
    SameBeforeTwo left right := fun tested separator => (first tested separator).trans (second tested separator)

/-- Two old letters can cross; a third occurrence can cross even a new
letter. This definition is symmetric and depends only on actual past counts. -/
def Crossable (prefixWords : List Nat) (left right : Nat) : Prop :=
  2 ≤ prefixWords.count left ∨ 2 ≤ prefixWords.count right ∨
    (1 ≤ prefixWords.count left ∧ 1 ≤ prefixWords.count right)

theorem Crossable.symm {prefixWords : List Nat} {left right : Nat}
    (allowed : Crossable prefixWords left right) : Crossable prefixWords right left := by
  rcases allowed with leftTwice | rightTwice | both
  · exact Or.inr (Or.inl leftTwice)
  · exact Or.inl rightTwice
  · exact Or.inr (Or.inr ⟨both.2, both.1⟩)

theorem Crossable.append {prefixWords : List Nat} {left right : Nat}
    (allowed : Crossable prefixWords left right) (extra : List Nat) :
    Crossable (prefixWords ++ extra) left right := by
  simp only [Crossable, List.count_append] at allowed ⊢
  omega

/-- Equal capped prefix counts force every letter before a desired first
remaining occurrence to be crossable. The desired occurrence may be first,
second, third, or later globally; all cases are included. -/
theorem first_remaining_crossable (prefixWords gap leftTail rightTail : List Nat) (letter : Nat)
    (first : letter ∉ gap)
    (same : SameBeforeTwo (prefixWords ++ letter :: leftTail)
      (prefixWords ++ gap ++ letter :: rightTail)) :
    ∀ tested ∈ gap, Crossable prefixWords letter tested := by
  intro tested member
  by_cases twice : 2 ≤ prefixWords.count letter
  · exact Or.inl twice
  by_cases zero : prefixWords.count letter = 0
  · have absent := List.not_mem_of_count_eq_zero zero
    have extendedAbsent : letter ∉ prefixWords ++ gap := by simp [absent, first]
    have equality := same tested letter
    rw [before_append_of_not_mem letter prefixWords _ absent,
      before_append_of_not_mem letter (prefixWords ++ gap) _ extendedAbsent] at equality
    simp only [before_self, List.append_nil, List.count_append] at equality
    have positive := List.count_pos_iff.mpr member
    exact Or.inr (Or.inl (by omega))
  · have one : prefixWords.count letter = 1 := by omega
    by_cases seen : 1 ≤ prefixWords.count tested
    · exact Or.inr (Or.inr ⟨by omega, seen⟩)
    · have testedZero : prefixWords.count tested = 0 := by omega
      have testedAbsent := List.not_mem_of_count_eq_zero testedZero
      have different : letter ≠ tested := by
        intro equal
        subst tested
        omega
      have gapBeforeZero : (before tested gap).count letter = 0 :=
        List.count_eq_zero_of_not_mem (fun inside => first (mem_before tested letter inside))
      have equality := same letter tested
      rw [before_append_of_not_mem tested prefixWords _ testedAbsent,
        before_cons_of_ne tested letter leftTail different] at equality
      have rightShape : before tested (prefixWords ++ gap ++ letter :: rightTail) =
          prefixWords ++ before tested gap := by
        rw [List.append_assoc, before_append_of_not_mem tested prefixWords _ testedAbsent,
          before_append_of_mem tested gap _ member]
      rw [rightShape] at equality
      simp only [List.count_append, List.count_cons_self, gapBeforeZero, one] at equality
      omega

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.PrefixCount
