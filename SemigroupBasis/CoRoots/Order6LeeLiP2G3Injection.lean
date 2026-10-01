import SemigroupBasis.CoRoots.Order6LeeLiP2G3
import SemigroupBasis.CoRoots.Order6LeeLiP2G3SeparationDataS6_8221
import SemigroupBasis.FiniteCertificate

/-!
# Lee--Li P2 group G3: finite-fingerprint injection bridge

The G3 tuple invariant is a reduced-word invariant: a finite renaming may
create a word with more than two copies of one letter, so raw
`mergeCollapse` output cannot be sent directly to the four-generator
fingerprint table.  This module closes that gap constructively.

The derivation-stable signature consists of capped occurrence counts and the
last two letters.  On reduced words it determines `G3Inv`.  Two tiny semantic
models prove that both parts survive the count-reduction derivation.  A stable
collapse then uses at most four fixed labels, and every reduced endpoint lies
in one fixed finite inventory of G3 invariants.

Concrete order-six members provide only `Models`, separator valuations, and a
`Nodup` certificate for semantic fingerprints on `canonicalInventory`.
-/

namespace SemigroupBasis.CoRoots.Order6LeeLiP2G3.Injection

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6LeeLiP2G3
open SemigroupBasis.CoRoots.Order6LeeLiP2G4 (wordOfD)

/-! ## Two derivation-stable finite signatures -/

inductive CappedCount where
  | zero
  | one
  | many
deriving DecidableEq, Repr

namespace CappedCount

def add : CappedCount → CappedCount → CappedCount
  | zero, right => right
  | left, zero => left
  | one, one => many
  | one, many => many
  | many, one => many
  | many, many => many

theorem add_assoc (left middle right : CappedCount) :
    add (add left middle) right = add left (add middle right) := by
  cases left <;> cases middle <;> cases right <;> rfl

@[simp]
theorem add_zero (left : CappedCount) : add left zero = left := by
  cases left <;> rfl

def capNat : Nat → CappedCount
  | 0 => zero
  | 1 => one
  | _ + 2 => many

theorem capNat_add (left right : Nat) :
    capNat (left + right) = add (capNat left) (capNat right) := by
  cases left with
  | zero => simp [capNat, add]
  | succ left =>
      cases left with
      | zero =>
          cases right with
          | zero => rfl
          | succ right => cases right <;> rfl
      | succ left =>
          cases right with
          | zero => rfl
          | succ right => cases right <;> rfl

theorem capNat_eq_of_le_two {left right : Nat}
    (leftBound : left ≤ 2) (rightBound : right ≤ 2)
    (equal : capNat left = capNat right) : left = right := by
  have leftCases : left = 0 ∨ left = 1 ∨ left = 2 := by omega
  have rightCases : right = 0 ∨ right = 1 ∨ right = 2 := by omega
  rcases leftCases with rfl | rfl | rfl <;>
    rcases rightCases with rfl | rfl | rfl <;>
      simp [capNat] at equal ⊢

theorem positive_left_of_capNat_eq {left right : Nat}
    (equal : capNat left = capNat right) (rightPositive : 0 < right) :
    0 < left := by
  cases left with
  | zero =>
      cases right with
      | zero => omega
      | succ right => cases right <;> simp [capNat] at equal
  | succ left => omega

end CappedCount

def cappedCountSemigroup : Semigroup CappedCount where
  mul := CappedCount.add
  assoc := CappedCount.add_assoc

private theorem cappedCount_models : Models cappedCountSemigroup basis := by
  intro identity member
  have lawCases : identity = capLaw ∨
      identity = interiorCommutationLaw ∨ identity = headDupLaw := by
    simpa [basis] using member
  rcases lawCases with rfl | rfl | rfl
  · intro valuation
    change CappedCount.add (valuation 1) (valuation 1) =
      CappedCount.add
        (CappedCount.add (valuation 1) (valuation 1)) (valuation 1)
    cases valuation 1 <;> rfl
  · intro valuation
    change CappedCount.add
        (CappedCount.add
          (CappedCount.add (valuation 1) (valuation 0)) (valuation 2))
        (valuation 3) =
      CappedCount.add
        (CappedCount.add
          (CappedCount.add (valuation 0) (valuation 1)) (valuation 2))
        (valuation 3)
    cases valuation 1 <;> cases valuation 0 <;>
      cases valuation 2 <;> cases valuation 3 <;> rfl
  · intro valuation
    change CappedCount.add
        (CappedCount.add (valuation 1) (valuation 0)) (valuation 1) =
      CappedCount.add
        (CappedCount.add
          (CappedCount.add (valuation 1) (valuation 1)) (valuation 0))
        (valuation 1)
    cases valuation 1 <;> cases valuation 0 <;> rfl

private def countValuation (tested letter : Nat) : CappedCount :=
  if letter = tested then CappedCount.one else CappedCount.zero

private theorem foldl_countValuation (tested : Nat) :
    ∀ (letters : List Nat) (acc : CappedCount) (amount : Nat),
      acc = CappedCount.capNat amount →
      letters.foldl
          (fun current letter =>
            CappedCount.add current (countValuation tested letter)) acc =
        CappedCount.capNat (amount + letters.count tested)
  | [], acc, amount, accEq => by simpa [accEq]
  | head :: tail, acc, amount, accEq => by
      rw [List.foldl_cons]
      by_cases same : head = tested
      · subst head
        have next :
            CappedCount.add acc (countValuation tested tested) =
              CappedCount.capNat (amount + 1) := by
          calc
            CappedCount.add acc (countValuation tested tested) =
                CappedCount.add (CappedCount.capNat amount)
                  CappedCount.one := by
              simp [accEq, countValuation]
            _ = CappedCount.capNat (amount + 1) :=
              (CappedCount.capNat_add amount 1).symm
        have folded := foldl_countValuation tested tail _ (amount + 1) next
        simpa [List.count_cons, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using folded
      · have next :
            CappedCount.add acc (countValuation tested head) =
              CappedCount.capNat amount := by
          simpa [accEq, countValuation, same, CappedCount.add_zero]
        have folded := foldl_countValuation tested tail _ amount next
        simpa [List.count_cons, same] using folded

private theorem eval_cappedCount (letters : List Nat) (nonempty : letters ≠ [])
    (tested : Nat) :
    cappedCountSemigroup.eval (countValuation tested) (wordOfD letters) =
      CappedCount.capNat (letters.count tested) := by
  cases letters with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail =>
      unfold Semigroup.eval wordOfD
      have start : countValuation tested head =
          CappedCount.capNat ([head].count tested) := by
        by_cases same : head = tested
        · subst head
          simp [countValuation, CappedCount.capNat]
        · simp [countValuation, same, CappedCount.capNat]
      have folded := foldl_countValuation tested tail
        (countValuation tested head) ([head].count tested) start
      simpa [List.count_cons, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using folded

inductive SuffixTwo where
  | empty
  | one (last : Nat)
  | two (penultimate last : Nat)
deriving DecidableEq, Repr

namespace SuffixTwo

def append : SuffixTwo → SuffixTwo → SuffixTwo
  | left, empty => left
  | _, two penultimate last => two penultimate last
  | empty, one last => one last
  | one left, one right => two left right
  | two _ left, one right => two left right

theorem append_assoc (left middle right : SuffixTwo) :
    append (append left middle) right = append left (append middle right) := by
  cases left <;> cases middle <;> cases right <;> rfl

def map (rename : Nat → Nat) : SuffixTwo → SuffixTwo
  | empty => empty
  | one last => one (rename last)
  | two penultimate last => two (rename penultimate) (rename last)

def letters : SuffixTwo → List Nat
  | empty => []
  | one last => [last]
  | two penultimate last => [penultimate, last]

theorem letters_length_le_two (state : SuffixTwo) :
    state.letters.length ≤ 2 := by
  cases state <;> simp [letters]

end SuffixTwo

def suffixTwoSemigroup : Semigroup SuffixTwo where
  mul := SuffixTwo.append
  assoc := SuffixTwo.append_assoc

private inductive NonemptySuffixTwo where
  | one (last : Nat)
  | two (penultimate last : Nat)
deriving DecidableEq, Repr

namespace NonemptySuffixTwo

def append : NonemptySuffixTwo → NonemptySuffixTwo → NonemptySuffixTwo
  | _, two penultimate last => two penultimate last
  | one left, one right => two left right
  | two _ left, one right => two left right

theorem append_assoc (left middle right : NonemptySuffixTwo) :
    append (append left middle) right = append left (append middle right) := by
  cases left <;> cases middle <;> cases right <;> rfl

def toSuffixTwo : NonemptySuffixTwo → SuffixTwo
  | one last => SuffixTwo.one last
  | two penultimate last => SuffixTwo.two penultimate last

theorem toSuffixTwo_append (left right : NonemptySuffixTwo) :
    toSuffixTwo (append left right) =
      SuffixTwo.append (toSuffixTwo left) (toSuffixTwo right) := by
  cases left <;> cases right <;> rfl

end NonemptySuffixTwo

private def nonemptySuffixTwoSemigroup : Semigroup NonemptySuffixTwo where
  mul := NonemptySuffixTwo.append
  assoc := NonemptySuffixTwo.append_assoc

private theorem nonemptySuffixTwo_models :
    Models nonemptySuffixTwoSemigroup basis := by
  intro identity member
  have lawCases : identity = capLaw ∨
      identity = interiorCommutationLaw ∨ identity = headDupLaw := by
    simpa [basis] using member
  rcases lawCases with rfl | rfl | rfl
  · intro valuation
    change NonemptySuffixTwo.append (valuation 1) (valuation 1) =
      NonemptySuffixTwo.append
        (NonemptySuffixTwo.append (valuation 1) (valuation 1)) (valuation 1)
    cases valuation 1 <;> rfl
  · intro valuation
    change NonemptySuffixTwo.append
        (NonemptySuffixTwo.append
          (NonemptySuffixTwo.append (valuation 1) (valuation 0)) (valuation 2))
        (valuation 3) =
      NonemptySuffixTwo.append
        (NonemptySuffixTwo.append
          (NonemptySuffixTwo.append (valuation 0) (valuation 1)) (valuation 2))
        (valuation 3)
    cases valuation 1 <;> cases valuation 0 <;>
      cases valuation 2 <;> cases valuation 3 <;> rfl
  · intro valuation
    change NonemptySuffixTwo.append
        (NonemptySuffixTwo.append (valuation 1) (valuation 0)) (valuation 1) =
      NonemptySuffixTwo.append
        (NonemptySuffixTwo.append
          (NonemptySuffixTwo.append (valuation 1) (valuation 1)) (valuation 0))
        (valuation 1)
    cases valuation 1 <;> cases valuation 0 <;> rfl

private def suffixValuation (letter : Nat) : SuffixTwo := SuffixTwo.one letter

private def nonemptySuffixValuation (letter : Nat) : NonemptySuffixTwo :=
  NonemptySuffixTwo.one letter

def suffixSignature (letters : List Nat) : SuffixTwo :=
  match letters with
  | [] => SuffixTwo.empty
  | _ => suffixTwoSemigroup.eval suffixValuation (wordOfD letters)

private theorem suffixSignature_nonempty (head : Nat) (tail : List Nat) :
    suffixSignature (head :: tail) =
      tail.foldl
        (fun current letter => SuffixTwo.append current (SuffixTwo.one letter))
        (SuffixTwo.one head) := by
  rfl

private theorem nonemptySuffixFold_value :
    ∀ (tail : List Nat) (state : NonemptySuffixTwo),
      NonemptySuffixTwo.toSuffixTwo
          (tail.foldl
            (fun current letter =>
              nonemptySuffixTwoSemigroup.mul current
                (nonemptySuffixValuation letter)) state) =
        tail.foldl
          (fun current letter =>
            SuffixTwo.append current (SuffixTwo.one letter))
          (NonemptySuffixTwo.toSuffixTwo state)
  | [], state => rfl
  | head :: tail, state => by
      rw [List.foldl_cons, List.foldl_cons,
        nonemptySuffixFold_value tail]
      congr 1
      exact NonemptySuffixTwo.toSuffixTwo_append state
        (nonemptySuffixValuation head)

private theorem eval_nonemptySuffixTwo (head : Nat) (tail : List Nat) :
    NonemptySuffixTwo.toSuffixTwo
        (nonemptySuffixTwoSemigroup.eval nonemptySuffixValuation
          (wordOfD (head :: tail))) =
      suffixSignature (head :: tail) := by
  rw [suffixSignature_nonempty]
  exact nonemptySuffixFold_value tail (nonemptySuffixValuation head)

private theorem suffixMap_append (rename : Nat → Nat)
    (left right : SuffixTwo) :
    SuffixTwo.map rename (SuffixTwo.append left right) =
      SuffixTwo.append (SuffixTwo.map rename left)
        (SuffixTwo.map rename right) := by
  cases left <;> cases right <;> rfl

private theorem suffixMap_fold (rename : Nat → Nat) :
    ∀ (tail : List Nat) (state : SuffixTwo),
      SuffixTwo.map rename
          (tail.foldl
            (fun current letter =>
              SuffixTwo.append current (SuffixTwo.one letter)) state) =
        (tail.map rename).foldl
          (fun current letter =>
            SuffixTwo.append current (SuffixTwo.one letter))
          (SuffixTwo.map rename state)
  | [], state => rfl
  | head :: tail, state => by
      rw [List.foldl_cons, List.map_cons, List.foldl_cons,
        suffixMap_fold rename tail]
      congr 1
      exact suffixMap_append rename state (SuffixTwo.one head)

theorem suffixSignature_map (letters : List Nat) (rename : Nat → Nat) :
    suffixSignature (letters.map rename) =
      SuffixTwo.map rename (suffixSignature letters) := by
  cases letters with
  | nil => rfl
  | cons head tail =>
      simp only [List.map_cons]
      rw [suffixSignature_nonempty, suffixSignature_nonempty]
      exact (suffixMap_fold rename tail (SuffixTwo.one head)).symm

private theorem wordOfD_map (letters : List Nat) (rename : Nat → Nat)
    (nonempty : letters ≠ []) :
    (wordOfD letters).map rename = wordOfD (letters.map rename) := by
  cases letters with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail => rfl

private theorem map_ne_nil {letters : List Nat} (nonempty : letters ≠ [])
    (rename : Nat → Nat) : letters.map rename ≠ [] := by
  cases letters with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail => simp

private theorem cappedCount_eq_of_derives
    {left right : List Nat} (leftNonempty : left ≠ [])
    (rightNonempty : right ≠ [])
    (derivation : Derives basis (wordOfD left) (wordOfD right))
    (tested : Nat) :
    CappedCount.capNat (left.count tested) =
      CappedCount.capNat (right.count tested) := by
  have sound := Derives.sound cappedCount_models derivation
    (countValuation tested)
  simpa [eval_cappedCount left leftNonempty tested,
    eval_cappedCount right rightNonempty tested] using sound

private theorem suffixSignature_eq_of_derives
    {left right : List Nat} (leftNonempty : left ≠ [])
    (rightNonempty : right ≠ [])
    (derivation : Derives basis (wordOfD left) (wordOfD right)) :
    suffixSignature left = suffixSignature right := by
  cases left with
  | nil => exact False.elim (leftNonempty rfl)
  | cons leftHead leftTail =>
      cases right with
      | nil => exact False.elim (rightNonempty rfl)
      | cons rightHead rightTail =>
          have sound := Derives.sound nonemptySuffixTwo_models derivation
            nonemptySuffixValuation
          have valuesEqual := congrArg NonemptySuffixTwo.toSuffixTwo sound
          rw [eval_nonemptySuffixTwo, eval_nonemptySuffixTwo] at valuesEqual
          exact valuesEqual

/-! ## The reduced invariant is exactly the finite signature -/

private def sortedSupport (letters : List Nat) : List Nat :=
  (SemigroupBasis.CoRoots.Order6LeeLiP2G2.deduplicateSupport letters).mergeSort
    (fun left right => decide (left ≤ right))

private theorem deduplicateSupport_mem (letter : Nat) (letters : List Nat) :
    letter ∈
        SemigroupBasis.CoRoots.Order6LeeLiP2G2.deduplicateSupport letters ↔
      letter ∈ letters := by
  induction letters with
  | nil =>
      simp [SemigroupBasis.CoRoots.Order6LeeLiP2G2.deduplicateSupport]
  | cons head tail ih =>
      by_cases present : head ∈ tail
      · have headCase : letter = head → letter ∈ tail := by
          intro equal
          simpa [equal] using present
        simpa [SemigroupBasis.CoRoots.Order6LeeLiP2G2.deduplicateSupport,
          present, ih] using headCase
      · simp [SemigroupBasis.CoRoots.Order6LeeLiP2G2.deduplicateSupport,
          present, ih]

private theorem sortedSupport_mem (letters : List Nat) (letter : Nat) :
    letter ∈ sortedSupport letters ↔ letter ∈ letters := by
  rw [sortedSupport, List.mem_mergeSort, deduplicateSupport_mem]

private theorem deduplicateSupport_nodup (letters : List Nat) :
    (SemigroupBasis.CoRoots.Order6LeeLiP2G2.deduplicateSupport letters).Nodup := by
  induction letters with
  | nil => simp [SemigroupBasis.CoRoots.Order6LeeLiP2G2.deduplicateSupport]
  | cons head tail ih =>
      by_cases present : head ∈ tail
      · simpa [SemigroupBasis.CoRoots.Order6LeeLiP2G2.deduplicateSupport,
          present] using ih
      · simp [SemigroupBasis.CoRoots.Order6LeeLiP2G2.deduplicateSupport,
          present, ih, deduplicateSupport_mem]

private theorem sortedSupport_nodup (letters : List Nat) :
    (sortedSupport letters).Nodup := by
  exact (List.mergeSort_perm
      (SemigroupBasis.CoRoots.Order6LeeLiP2G2.deduplicateSupport letters)
      (fun left right : Nat => decide (left ≤ right))).nodup_iff.mpr
    (deduplicateSupport_nodup letters)

private theorem sortedSupport_sorted (letters : List Nat) :
    (sortedSupport letters).Pairwise (fun left right => left ≤ right) := by
  unfold sortedSupport
  have sorted := List.pairwise_mergeSort
    (le := fun left right : Nat => decide (left ≤ right))
    (fun _ _ _ => by simp; omega)
    (fun _ _ => by simp; omega)
    (SemigroupBasis.CoRoots.Order6LeeLiP2G2.deduplicateSupport letters)
  exact sorted.imp (by intro _ _ relation; simpa using relation)

private theorem sortedNodup_eq_of_mem_iff
    (left right : List Nat)
    (leftSorted : left.Pairwise (fun a b => a ≤ b))
    (rightSorted : right.Pairwise (fun a b => a ≤ b))
    (leftNodup : left.Nodup) (rightNodup : right.Nodup)
    (sameMembers : ∀ letter, letter ∈ left ↔ letter ∈ right) :
    left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons head tail =>
          have := (sameMembers head).mpr (by simp)
          simp at this
  | cons leftHead leftTail ih =>
      cases right with
      | nil =>
          have := (sameMembers leftHead).mp (by simp)
          simp at this
      | cons rightHead rightTail =>
          have leftHeadInRight : leftHead ∈ rightHead :: rightTail :=
            (sameMembers leftHead).mp (by simp)
          have rightHeadInLeft : rightHead ∈ leftHead :: leftTail :=
            (sameMembers rightHead).mpr (by simp)
          have leftLeRight : leftHead ≤ rightHead := by
            rcases List.mem_cons.mp rightHeadInLeft with equal | inTail
            · omega
            · exact (List.pairwise_cons.mp leftSorted).1 rightHead inTail
          have rightLeLeft : rightHead ≤ leftHead := by
            rcases List.mem_cons.mp leftHeadInRight with equal | inTail
            · omega
            · exact (List.pairwise_cons.mp rightSorted).1 leftHead inTail
          have headsEqual : leftHead = rightHead := Nat.le_antisymm leftLeRight rightLeLeft
          subst rightHead
          congr 1
          apply ih rightTail
          · exact (List.pairwise_cons.mp leftSorted).2
          · exact (List.pairwise_cons.mp rightSorted).2
          · exact (List.nodup_cons.mp leftNodup).2
          · exact (List.nodup_cons.mp rightNodup).2
          · intro letter
            have leftFresh := (List.nodup_cons.mp leftNodup).1
            have rightFresh := (List.nodup_cons.mp rightNodup).1
            have whole := sameMembers letter
            constructor
            · intro inLeftTail
              have inWholeLeft : letter ∈ leftHead :: leftTail := by
                simp [inLeftTail]
              have inWholeRight := whole.mp inWholeLeft
              rcases List.mem_cons.mp inWholeRight with equal | inRightTail
              · subst letter
                exact False.elim (leftFresh inLeftTail)
              · exact inRightTail
            · intro inRightTail
              have inWholeRight : letter ∈ leftHead :: rightTail := by
                simp [inRightTail]
              have inWholeLeft := whole.mpr inWholeRight
              rcases List.mem_cons.mp inWholeLeft with equal | inLeftTail
              · subst letter
                exact False.elim (rightFresh inRightTail)
              · exact inLeftTail

private theorem profile_pair_mem (letters : List Nat) (letter : Nat)
    (flag : Bool) :
    (letter, flag) ∈ profile letters ↔
      letter ∈ letters ∧ flag = decide (letters.count letter = 2) := by
  unfold profile
  rw [List.mem_map]
  constructor
  · rintro ⟨source, sourceMember, equal⟩
    have sourceEq : source = letter := by
      exact congrArg Prod.fst equal
    subst source
    exact ⟨(sortedSupport_mem letters letter).mp sourceMember,
      (congrArg Prod.snd equal).symm⟩
  · rintro ⟨letterMember, rfl⟩
    exact ⟨letter, (sortedSupport_mem letters letter).mpr letterMember, rfl⟩

private theorem profile_eq_of_counts
    {left right : List Nat}
    (countsEqual : ∀ letter, left.count letter = right.count letter) :
    profile left = profile right := by
  have supportEqual : sortedSupport left = sortedSupport right := by
    apply sortedNodup_eq_of_mem_iff
    · exact sortedSupport_sorted left
    · exact sortedSupport_sorted right
    · exact sortedSupport_nodup left
    · exact sortedSupport_nodup right
    · intro letter
      rw [sortedSupport_mem, sortedSupport_mem,
        ← List.count_pos_iff, ← List.count_pos_iff, countsEqual]
  change
    (sortedSupport left).map
        (fun letter => (letter, decide (left.count letter = 2))) =
      (sortedSupport right).map
        (fun letter => (letter, decide (right.count letter = 2)))
  rw [supportEqual]
  apply List.map_congr_left
  intro letter _
  simp [countsEqual letter]

private theorem counts_eq_of_profile_eq_reduced
    {left right : List Nat} (leftReduced : Reduced left)
    (rightReduced : Reduced right) (profilesEqual : profile left = profile right) :
    ∀ letter, left.count letter = right.count letter := by
  intro letter
  have leftBound := leftReduced letter
  have rightBound := rightReduced letter
  by_cases leftMember : letter ∈ left
  · have leftPair := (profile_pair_mem left letter
        (decide (left.count letter = 2))).mpr ⟨leftMember, rfl⟩
    have rightPair :
        (letter, decide (left.count letter = 2)) ∈ profile right := by
      rw [← profilesEqual]
      exact leftPair
    have rightData := (profile_pair_mem right letter _).mp rightPair
    have leftPositive := List.count_pos_iff.mpr leftMember
    have rightPositive := List.count_pos_iff.mpr rightData.1
    by_cases leftTwo : left.count letter = 2
    · have rightTwo : right.count letter = 2 := by
        simpa [leftTwo] using rightData.2
      omega
    · have rightNotTwo : right.count letter ≠ 2 := by
        simpa [leftTwo] using rightData.2
      omega
  · have leftZero : left.count letter = 0 := List.count_eq_zero.mpr leftMember
    have rightAbsent : letter ∉ right := by
      intro rightMember
      have rightPair := (profile_pair_mem right letter
          (decide (right.count letter = 2))).mpr ⟨rightMember, rfl⟩
      have leftPair :
          (letter, decide (right.count letter = 2)) ∈ profile left := by
        rw [profilesEqual]
        exact rightPair
      have leftData := (profile_pair_mem left letter _).mp leftPair
      exact leftMember leftData.1
    rw [leftZero, List.count_eq_zero.mpr rightAbsent]

private def boundaryState (key : G3Inv) : SuffixTwo :=
  match key.p2, key.p1 with
  | some penultimate, some last => SuffixTwo.two penultimate.1 last.1
  | none, some last => SuffixTwo.one last.1
  | _, none => SuffixTwo.empty

private theorem suffixSignature_singleton (letter : Nat) :
    suffixSignature [letter] = SuffixTwo.one letter := rfl

private theorem suffixSignature_append_pair
    (stem : List Nat) (penultimate last : Nat) :
    suffixSignature (stem ++ [penultimate, last]) =
      SuffixTwo.two penultimate last := by
  cases stem with
  | nil => rfl
  | cons head tail =>
      change
        (tail ++ [penultimate, last]).foldl
            (fun current letter =>
              SuffixTwo.append current (SuffixTwo.one letter))
            (SuffixTwo.one head) =
          SuffixTwo.two penultimate last
      rw [List.foldl_append]
      generalize
        tail.foldl
          (fun current letter =>
            SuffixTwo.append current (SuffixTwo.one letter))
          (SuffixTwo.one head) = state
      cases state <;> rfl

private theorem singleton_or_append_pair (letters : List Nat)
    (nonempty : letters ≠ []) :
    (∃ letter, letters = [letter]) ∨
      ∃ stem penultimate last,
        letters = stem ++ [penultimate, last] := by
  generalize reverseEq : letters.reverse = reversed
  cases reversed with
  | nil =>
      have lettersEq : letters = [] := by
        have restored := congrArg List.reverse reverseEq
        simpa using restored
      exact False.elim (nonempty lettersEq)
  | cons last rest =>
      cases rest with
      | nil =>
          left
          refine ⟨last, ?_⟩
          have restored := congrArg List.reverse reverseEq
          simpa using restored
      | cons penultimate reversedStem =>
          right
          refine ⟨reversedStem.reverse, penultimate, last, ?_⟩
          have restored := congrArg List.reverse reverseEq
          simpa [List.reverse_cons, List.append_assoc] using restored

private theorem suffixSignature_letters_nonempty (letters : List Nat)
    (nonempty : letters ≠ []) : (suffixSignature letters).letters ≠ [] := by
  obtain ⟨letter, shape⟩ | ⟨stem, penultimate, last, shape⟩ :=
    singleton_or_append_pair letters nonempty
  · subst letters
    simp [suffixSignature_singleton, SuffixTwo.letters]
  · subst letters
    simp [suffixSignature_append_pair, SuffixTwo.letters]

private theorem getD_append_pair_left
    (stem : List Nat) (penultimate last : Nat) :
    (stem ++ [penultimate, last]).getD stem.length 0 = penultimate := by
  induction stem with
  | nil => rfl
  | cons head tail ih => simpa using ih

private theorem getD_append_pair_right
    (stem : List Nat) (penultimate last : Nat) :
    (stem ++ [penultimate, last]).getD (stem.length + 1) 0 = last := by
  induction stem with
  | nil => rfl
  | cons head tail ih => simpa [Nat.add_assoc] using ih

private theorem take_append_pair_left
    (stem : List Nat) (penultimate last : Nat) :
    (stem ++ [penultimate, last]).take stem.length = stem := by
  induction stem with
  | nil => rfl
  | cons head tail ih => simpa using ih

private theorem take_append_pair_right
    (stem : List Nat) (penultimate last : Nat) :
    (stem ++ [penultimate, last]).take (stem.length + 1) =
      stem ++ [penultimate] := by
  induction stem with
  | nil => rfl
  | cons head tail ih => simpa [Nat.add_assoc] using ih

private theorem occTag_append_pair_left
    (stem : List Nat) (penultimate last : Nat) :
    occTag (stem ++ [penultimate, last]) stem.length =
      decide (stem.count penultimate ≠ 0) := by
  unfold occTag
  rw [take_append_pair_left, getD_append_pair_left]

private theorem occTag_append_pair_right
    (stem : List Nat) (penultimate last : Nat) :
    occTag (stem ++ [penultimate, last]) (stem.length + 1) =
      decide ((stem ++ [penultimate]).count last ≠ 0) := by
  unfold occTag
  rw [take_append_pair_right, getD_append_pair_right]

private theorem invariant_p2_append_pair
    (stem : List Nat) (penultimate last : Nat) :
    (invariant (stem ++ [penultimate, last])).p2 =
      some (penultimate, decide (stem.count penultimate ≠ 0)) := by
  have long : 2 ≤ (stem ++ [penultimate, last]).length := by simp
  have index : (stem ++ [penultimate, last]).length - 2 = stem.length := by
    simp
  change
    (if h : 2 ≤ (stem ++ [penultimate, last]).length then
      some ((stem ++ [penultimate, last]).getD
        ((stem ++ [penultimate, last]).length - 2) 0,
        occTag (stem ++ [penultimate, last])
          ((stem ++ [penultimate, last]).length - 2))
    else none) = _
  rw [dif_pos long, index, getD_append_pair_left,
    occTag_append_pair_left]

private theorem invariant_p1_append_pair
    (stem : List Nat) (penultimate last : Nat) :
    (invariant (stem ++ [penultimate, last])).p1 =
      some (last, decide ((stem ++ [penultimate]).count last ≠ 0)) := by
  have nonempty : 1 ≤ (stem ++ [penultimate, last]).length := by simp
  have index : (stem ++ [penultimate, last]).length - 1 = stem.length + 1 := by
    simp
  change
    (if h : 1 ≤ (stem ++ [penultimate, last]).length then
      some ((stem ++ [penultimate, last]).getD
        ((stem ++ [penultimate, last]).length - 1) 0,
        occTag (stem ++ [penultimate, last])
          ((stem ++ [penultimate, last]).length - 1))
    else none) = _
  rw [dif_pos nonempty, index, getD_append_pair_right,
    occTag_append_pair_right]

private theorem invariant_p2_singleton (letter : Nat) :
    (invariant [letter]).p2 = none := by
  simp [invariant]

private theorem invariant_p1_singleton (letter : Nat) :
    (invariant [letter]).p1 = some (letter, false) := by
  simp [invariant, occTag]

private theorem boundaryState_invariant (letters : List Nat) :
    boundaryState (invariant letters) = suffixSignature letters := by
  by_cases empty : letters = []
  · subst letters
    rfl
  · obtain ⟨letter, shape⟩ | ⟨stem, penultimate, last, shape⟩ :=
      singleton_or_append_pair letters empty
    · subst letters
      unfold boundaryState
      rw [invariant_p2_singleton, invariant_p1_singleton,
        suffixSignature_singleton]
    · subst letters
      unfold boundaryState
      rw [invariant_p2_append_pair, invariant_p1_append_pair,
        suffixSignature_append_pair]

private theorem g3Inv_eq_of_fields {left right : G3Inv}
    (profileEq : left.profile = right.profile)
    (p2Eq : left.p2 = right.p2) (p1Eq : left.p1 = right.p1) :
    left = right := by
  cases left
  cases right
  simp_all

private theorem invariant_eq_iff_signature
    {left right : List Nat} (leftNonempty : left ≠ [])
    (rightNonempty : right ≠ []) (leftReduced : Reduced left)
    (rightReduced : Reduced right) :
    invariant left = invariant right ↔
      (∀ letter, left.count letter = right.count letter) ∧
        suffixSignature left = suffixSignature right := by
  constructor
  · intro equal
    refine ⟨?_, ?_⟩
    · exact counts_eq_of_profile_eq_reduced leftReduced rightReduced
        (congrArg G3Inv.profile equal)
    · rw [← boundaryState_invariant left,
        ← boundaryState_invariant right, equal]
  · rintro ⟨countsEqual, suffixEqual⟩
    have profilesEqual := profile_eq_of_counts countsEqual
    obtain ⟨leftLast, leftShape⟩ | ⟨leftStem, leftPenultimate,
        leftLast, leftShape⟩ := singleton_or_append_pair left leftNonempty
    · obtain ⟨rightLast, rightShape⟩ | ⟨rightStem,
          rightPenultimate, rightLast, rightShape⟩ :=
        singleton_or_append_pair right rightNonempty
      · subst left
        subst right
        have lastEqual : leftLast = rightLast := by
          simpa [suffixSignature_singleton] using suffixEqual
        subst rightLast
        apply g3Inv_eq_of_fields
        · exact profilesEqual
        · rfl
        · rfl
      · subst left
        subst right
        rw [suffixSignature_singleton,
          suffixSignature_append_pair] at suffixEqual
        cases suffixEqual
    · obtain ⟨rightLast, rightShape⟩ | ⟨rightStem,
          rightPenultimate, rightLast, rightShape⟩ :=
        singleton_or_append_pair right rightNonempty
      · subst left
        subst right
        rw [suffixSignature_append_pair,
          suffixSignature_singleton] at suffixEqual
        cases suffixEqual
      · subst left
        subst right
        have boundaryEqual :
            leftPenultimate = rightPenultimate ∧ leftLast = rightLast := by
          simpa [suffixSignature_append_pair] using suffixEqual
        rcases boundaryEqual with ⟨rfl, rfl⟩
        have stemCountsEqual : ∀ letter,
            leftStem.count letter = rightStem.count letter := by
          intro letter
          have total := countsEqual letter
          simp only [List.count_append, List.count_cons,
            List.count_nil, Nat.add_zero] at total
          omega
        apply g3Inv_eq_of_fields
        · exact profilesEqual
        · rw [invariant_p2_append_pair, invariant_p2_append_pair,
            stemCountsEqual leftPenultimate]
        · rw [invariant_p1_append_pair, invariant_p1_append_pair]
          congr 2
          simp only [List.count_append, List.count_cons,
            List.count_nil, Nat.add_zero]
          rw [stemCountsEqual leftLast]

/-! ## Fixed four-generator inventory -/

/-- Reduced four-generator words of a fixed length, in lexicographic order.
Pruning while extending a word avoids materializing the 87,380-word ambient
search while preserving the order of the former filter-based enumeration. -/
def wordsOfLengthFour : Nat → List (List Nat)
  | 0 => [[]]
  | length + 1 =>
      (List.range 4).flatMap fun head =>
        ((wordsOfLengthFour length).filter fun tail =>
          decide (tail.count head < 2)).map (List.cons head)

/-- The general G3 invariant specialized to the fixed four-letter inventory.
Its profile is definitionally finite and avoids reducing `mergeSort` inside
the kernel certificates below. -/
def invariantFour (w : List Nat) : G3Inv :=
  { profile := profileFour w
    p2 :=
      if h : 2 ≤ w.length then
        some (w.getD (w.length - 2) 0, occTag w (w.length - 2))
      else none
    p1 :=
      if h : 1 ≤ w.length then
        some (w.getD (w.length - 1) 0, occTag w (w.length - 1))
      else none }

private theorem invariant_eq_invariantFour_of_bound {w : List Nat}
    (bounded : ∀ c, c ∈ w → c < 4) :
    invariant w = invariantFour w := by
  unfold invariant invariantFour
  rw [profile_eq_profileFour_of_bound bounded]

def canonicalInventoryAtLength (length : Nat) : List G3Inv :=
  ((wordsOfLengthFour length).map invariantFour).eraseDups

/-- The 544 admissible G3 invariants over four fixed generators. -/
def canonicalInventory : List G3Inv :=
  (List.range 8).flatMap fun offset =>
    canonicalInventoryAtLength (offset + 1)

/-- The canonical word represented by one entry of the finite G3 inventory. -/
abbrev canonicalWord (key : G3Inv) : Word Nat :=
  wordOfD (canonical key)

/-!
The separation-data emitter orders its canonical words exactly as the
first-occurrence order of `canonicalInventory`.  Certify that family-level
bridge once, before the six concrete semigroup modules reuse it.  This is an
ordinary kernel reduction, so the axiom gate sees no external reduction
oracle.
-/
section InventoryKernelChecks

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

private theorem canonicalWords_length_one :
    (canonicalInventoryAtLength 1).map canonicalWord =
      S6_8221Data.canonicalsLength1 := by
  simp (config := { maxSteps := 5000000 }) +decide
    [canonicalInventoryAtLength, canonicalWord, wordsOfLengthFour,
      S6_8221Data.canonicalsLength1,
      S6_8221Data.canonicalsLength1Chunk0, canonical, invariantFour,
      profileFour, supportFour,
      occTag, interiorList, interiorBlock, interiorMultiplicity,
      wordOfD,
      List.flatMap, List.flatten, List.filter, List.map, List.range,
      List.range.loop, List.count, Function.comp_def]

private theorem canonicalWords_length_two :
    (canonicalInventoryAtLength 2).map canonicalWord =
      S6_8221Data.canonicalsLength2 := by
  simp (config := { maxSteps := 5000000 }) +decide
    [canonicalInventoryAtLength, canonicalWord, wordsOfLengthFour,
      S6_8221Data.canonicalsLength2,
      S6_8221Data.canonicalsLength2Chunk0, canonical, invariantFour,
      profileFour, supportFour,
      occTag, interiorList, interiorBlock, interiorMultiplicity,
      wordOfD,
      List.flatMap, List.flatten, List.filter, List.map, List.range,
      List.range.loop, List.count, Function.comp_def]

private theorem canonicalWords_length_three :
    (canonicalInventoryAtLength 3).map canonicalWord =
      S6_8221Data.canonicalsLength3 := by
  simp (config := { maxSteps := 5000000 }) +decide
    [canonicalInventoryAtLength, canonicalWord, wordsOfLengthFour,
      S6_8221Data.canonicalsLength3,
      S6_8221Data.canonicalsLength3Chunk0, canonical, invariantFour,
      profileFour, supportFour,
      occTag, interiorList, interiorBlock, interiorMultiplicity,
      wordOfD,
      List.flatMap, List.flatten, List.filter, List.map, List.range,
      List.range.loop, List.count, Function.comp_def]

private theorem canonicalWords_length_four :
    (canonicalInventoryAtLength 4).map canonicalWord =
      S6_8221Data.canonicalsLength4 := by
  simp (config := { maxSteps := 5000000 }) +decide
    [canonicalInventoryAtLength, canonicalWord, wordsOfLengthFour,
      S6_8221Data.canonicalsLength4,
      S6_8221Data.canonicalsLength4Chunk0, canonical, invariantFour,
      profileFour, supportFour,
      occTag, interiorList, interiorBlock, interiorMultiplicity,
      wordOfD,
      List.flatMap, List.flatten, List.filter, List.map, List.range,
      List.range.loop, List.count, Function.comp_def]

private theorem canonicalWords_length_five :
    (canonicalInventoryAtLength 5).map canonicalWord =
      S6_8221Data.canonicalsLength5 := by
  simp (config := { maxSteps := 5000000 }) +decide
    [canonicalInventoryAtLength, canonicalWord, wordsOfLengthFour,
      S6_8221Data.canonicalsLength5,
      S6_8221Data.canonicalsLength5Chunk0,
      S6_8221Data.canonicalsLength5Chunk1, canonical, invariantFour,
      profileFour, supportFour,
      occTag, interiorList, interiorBlock, interiorMultiplicity,
      wordOfD,
      List.flatMap, List.flatten, List.filter, List.map, List.range,
      List.range.loop, List.count, Function.comp_def]

private theorem canonicalWords_length_six :
    (canonicalInventoryAtLength 6).map canonicalWord =
      S6_8221Data.canonicalsLength6 := by
  simp (config := { maxSteps := 5000000 }) +decide
    [canonicalInventoryAtLength, canonicalWord, wordsOfLengthFour,
      S6_8221Data.canonicalsLength6,
      S6_8221Data.canonicalsLength6Chunk0, canonical, invariantFour,
      profileFour, supportFour,
      occTag, interiorList, interiorBlock, interiorMultiplicity,
      wordOfD,
      List.flatMap, List.flatten, List.filter, List.map, List.range,
      List.range.loop, List.count, Function.comp_def]

private theorem canonicalWords_length_seven :
    (canonicalInventoryAtLength 7).map canonicalWord =
      S6_8221Data.canonicalsLength7 := by
  simp (config := { maxSteps := 5000000 }) +decide
    [canonicalInventoryAtLength, canonicalWord, wordsOfLengthFour,
      S6_8221Data.canonicalsLength7,
      S6_8221Data.canonicalsLength7Chunk0, canonical, invariantFour,
      profileFour, supportFour,
      occTag, interiorList, interiorBlock, interiorMultiplicity,
      wordOfD,
      List.flatMap, List.flatten, List.filter, List.map, List.range,
      List.range.loop, List.count, Function.comp_def]

private theorem canonicalWords_length_eight :
    (canonicalInventoryAtLength 8).map canonicalWord =
      S6_8221Data.canonicalsLength8 := by
  simp (config := { maxSteps := 5000000 }) +decide
    [canonicalInventoryAtLength, canonicalWord, wordsOfLengthFour,
      S6_8221Data.canonicalsLength8,
      S6_8221Data.canonicalsLength8Chunk0, canonical, invariantFour,
      profileFour, supportFour,
      occTag, interiorList, interiorBlock, interiorMultiplicity,
      wordOfD,
      List.flatMap, List.flatten, List.filter, List.map, List.range,
      List.range.loop, List.count, Function.comp_def]

theorem canonicalWords_eq_separationData :
    canonicalInventory.map canonicalWord = S6_8221Data.canonicals := by
  have inventory_eq :
      canonicalInventory =
        canonicalInventoryAtLength 1 ++
          canonicalInventoryAtLength 2 ++
          canonicalInventoryAtLength 3 ++
          canonicalInventoryAtLength 4 ++
          canonicalInventoryAtLength 5 ++
          canonicalInventoryAtLength 6 ++
          canonicalInventoryAtLength 7 ++
          canonicalInventoryAtLength 8 := by
    simp [canonicalInventory, List.range, List.range.loop]
  rw [inventory_eq]
  simp only [List.map_append]
  rw [canonicalWords_length_one, canonicalWords_length_two,
    canonicalWords_length_three, canonicalWords_length_four,
    canonicalWords_length_five, canonicalWords_length_six,
    canonicalWords_length_seven, canonicalWords_length_eight]
  rfl

end InventoryKernelChecks

private theorem mem_eraseDups_iff [BEq α] [LawfulBEq α] :
    ∀ (entry : α) (entries : List α),
      entry ∈ entries.eraseDups ↔ entry ∈ entries
  | entry, [] => by simp
  | entry, head :: tail => by
      rw [List.eraseDups_cons]
      simp only [List.mem_cons]
      rw [mem_eraseDups_iff entry
        (tail.filter fun candidate => !candidate == head)]
      by_cases same : entry = head
      · subst entry
        simp
      · simp [same]
termination_by
  _ entries => entries.length
decreasing_by
  have filteredLength :
      (tail.filter fun candidate => !candidate == head).length ≤
        tail.length := List.filter_sublist.length_le
  simpa only [List.length_cons] using Nat.lt_succ_of_le filteredLength

private theorem mem_wordsOfLengthFour_of_bound
    {length : Nat} {letters : List Nat}
    (lengthEq : letters.length = length)
    (bounded : ∀ letter, letter ∈ letters → letter < 4)
    (reduced : Reduced letters) :
    letters ∈ wordsOfLengthFour length := by
  induction length generalizing letters with
  | zero =>
      have lettersEq : letters = [] := List.eq_nil_of_length_eq_zero lengthEq
      subst letters
      simp [wordsOfLengthFour]
  | succ length ih =>
      cases letters with
      | nil => simp at lengthEq
      | cons head tail =>
          have headBound : head < 4 := bounded head (by simp)
          have tailBound : ∀ letter, letter ∈ tail → letter < 4 := by
            intro letter member
            exact bounded letter (by simp [member])
          have tailLength : tail.length = length := by
            simpa using Nat.succ.inj lengthEq
          have tailReduced : Reduced tail := by
            intro letter
            have countBound := reduced letter
            by_cases same : letter = head
            · subst letter
              rw [List.count_cons_self] at countBound
              omega
            · simpa only [List.count_cons_of_ne (Ne.symm same)] using countBound
          have headCount : tail.count head < 2 := by
            have countBound := reduced head
            rw [List.count_cons_self] at countBound
            omega
          rw [wordsOfLengthFour]
          apply List.mem_flatMap.mpr
          refine ⟨head, List.mem_range.mpr headBound, ?_⟩
          apply List.mem_map.mpr
          refine ⟨tail, List.mem_filter.mpr ⟨?_, decide_eq_true headCount⟩, rfl⟩
          exact ih tailLength tailBound tailReduced

private theorem length_eq_four_counts (letters : List Nat)
    (bounded : ∀ letter, letter ∈ letters → letter < 4) :
    letters.length = letters.count 0 + letters.count 1 +
      letters.count 2 + letters.count 3 := by
  induction letters with
  | nil => simp
  | cons head tail ih =>
      have headBound : head < 4 := bounded head (by simp)
      have tailBound : ∀ letter, letter ∈ tail → letter < 4 := by
        intro letter member
        exact bounded letter (by simp [member])
      have headCases : head = 0 ∨ head = 1 ∨ head = 2 ∨ head = 3 := by
        omega
      rcases headCases with rfl | rfl | rfl | rfl <;>
        simp [ih tailBound, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private theorem length_le_eight_of_reduced_four
    {letters : List Nat} (reduced : Reduced letters)
    (bounded : ∀ letter, letter ∈ letters → letter < 4) :
    letters.length ≤ 8 := by
  have lengthEq := length_eq_four_counts letters bounded
  have count0 := reduced 0
  have count1 := reduced 1
  have count2 := reduced 2
  have count3 := reduced 3
  omega

theorem invariant_mem_canonicalInventory
    {letters : List Nat} (nonempty : letters ≠ [])
    (reduced : Reduced letters)
    (bounded : ∀ letter, letter ∈ letters → letter < 4) :
    invariant letters ∈ canonicalInventory := by
  have lengthPositive : 0 < letters.length := List.length_pos_iff.mpr nonempty
  have lengthBound := length_le_eight_of_reduced_four reduced bounded
  have offsetBound : letters.length - 1 < 8 := by omega
  have lengthEq : letters.length = (letters.length - 1) + 1 := by omega
  unfold canonicalInventory
  apply List.mem_flatMap.mpr
  refine ⟨letters.length - 1, List.mem_range.mpr offsetBound, ?_⟩
  unfold canonicalInventoryAtLength
  rw [invariant_eq_invariantFour_of_bound bounded]
  apply (mem_eraseDups_iff (invariantFour letters) _).mpr
  apply List.mem_map.mpr
  exact ⟨letters,
    mem_wordsOfLengthFour_of_bound lengthEq bounded reduced, rfl⟩

/-! ## Finite relabeling and stable collapse -/

def encodeImage (image : List Nat) (letter : Nat) : Nat :=
  if letter ∈ image then List.idxOf letter image else 0

def decodeImage : List Nat → Nat → Nat
  | [], _ => 0
  | head :: _, 0 => head
  | _ :: tail, code + 1 => decodeImage tail code

private theorem decodeImage_encodeImage_of_mem
    {image : List Nat} {letter : Nat} (member : letter ∈ image) :
    decodeImage image (encodeImage image letter) = letter := by
  simp only [encodeImage, if_pos member]
  induction image with
  | nil => simp at member
  | cons head tail ih =>
      by_cases same : letter = head
      · subst letter
        simp [decodeImage, List.idxOf_cons]
      · have tailMember : letter ∈ tail :=
          (List.mem_cons.mp member).resolve_left same
        have different : head ≠ letter := fun equal => same equal.symm
        have indexEq : List.idxOf letter (head :: tail) =
            List.idxOf letter tail + 1 := by
          rw [List.idxOf_cons, beq_eq_false_iff_ne.mpr different]
          rfl
        rw [indexEq]
        exact ih tailMember

private theorem encodeImage_lt_four
    {image : List Nat} (imageNonempty : image ≠ [])
    (imageLength : image.length ≤ 4) (letter : Nat) :
    encodeImage image letter < 4 := by
  by_cases member : letter ∈ image
  · simpa only [encodeImage, if_pos member] using
      Nat.lt_of_lt_of_le (List.idxOf_lt_length_of_mem member) imageLength
  · simp [encodeImage, member]

private theorem suffixMap_decode_encode
    (state : SuffixTwo) (image : List Nat)
    (covered : ∀ letter, letter ∈ state.letters → letter ∈ image) :
    SuffixTwo.map (decodeImage image)
        (SuffixTwo.map (encodeImage image) state) = state := by
  cases state with
  | empty => rfl
  | one last =>
      simp only [SuffixTwo.map] at covered ⊢
      rw [decodeImage_encodeImage_of_mem (covered last (by simp [SuffixTwo.letters]))]
  | two penultimate last =>
      simp only [SuffixTwo.map] at covered ⊢
      rw [decodeImage_encodeImage_of_mem
          (covered penultimate (by simp [SuffixTwo.letters])),
        decodeImage_encodeImage_of_mem
          (covered last (by simp [SuffixTwo.letters]))]

private theorem count_map_of_fiber (rename : Nat → Nat) (source : Nat)
    (fiber : ∀ letter, rename letter = rename source → letter = source) :
    ∀ letters : List Nat,
      (letters.map rename).count (rename source) = letters.count source
  | [] => rfl
  | head :: tail => by
      by_cases same : head = source
      · subst head
        simp [count_map_of_fiber rename source fiber tail]
      · have imageDifferent : rename head ≠ rename source := by
          intro equal
          exact same (fiber head equal)
        simp [same, imageDifferent, count_map_of_fiber rename source fiber tail]

private def collapseAt (chosen letter : Nat) : Nat :=
  if letter = chosen then 0 else 1

private theorem collapseAt_fiber (chosen letter : Nat)
    (equal : collapseAt chosen letter = collapseAt chosen chosen) :
    letter = chosen := by
  simp [collapseAt] at equal ⊢
  exact equal

private theorem reducedOutput_count_preserved
    (letters : List Nat) (nonempty : letters ≠ []) (tested : Nat)
    (sourceBound : letters.count tested ≤ 2) :
    (normalizationWitness.countReduce letters).count tested =
      letters.count tested := by
  let reduced := normalizationWitness.countReduce letters
  have reducedNonempty : reduced ≠ [] :=
    normalizationWitness.reduce_nonempty letters nonempty
  have preserved := cappedCount_eq_of_derives nonempty reducedNonempty
    (normalizationWitness.reduce_derives letters nonempty) tested
  have reducedBound := normalizationWitness.reduce_reduced letters tested
  change CappedCount.capNat (letters.count tested) =
    CappedCount.capNat (reduced.count tested) at preserved
  exact (CappedCount.capNat_eq_of_le_two
    sourceBound reducedBound preserved).symm

private theorem reducedOutput_suffix_preserved
    (letters : List Nat) (nonempty : letters ≠ []) :
    suffixSignature (normalizationWitness.countReduce letters) =
      suffixSignature letters := by
  exact (suffixSignature_eq_of_derives nonempty
    (normalizationWitness.reduce_nonempty letters nonempty)
    (normalizationWitness.reduce_derives letters nonempty)).symm

private theorem reducedOutput_bounded
    (letters : List Nat) (nonempty : letters ≠ [])
    (bounded : ∀ letter, letter ∈ letters → letter < 4) :
    ∀ letter,
      letter ∈ normalizationWitness.countReduce letters → letter < 4 := by
  intro letter targetMember
  let reduced := normalizationWitness.countReduce letters
  have reducedNonempty : reduced ≠ [] :=
    normalizationWitness.reduce_nonempty letters nonempty
  have preserved := cappedCount_eq_of_derives nonempty reducedNonempty
    (normalizationWitness.reduce_derives letters nonempty) letter
  have targetPositive : 0 < reduced.count letter :=
    List.count_pos_iff.mpr targetMember
  have sourcePositive : 0 < letters.count letter :=
    CappedCount.positive_left_of_capNat_eq preserved targetPositive
  exact bounded letter (List.count_pos_iff.mp sourcePositive)

/-- Corrected G3 merge-collapse for finite fingerprints.  Separation is
stated only after count reduction, so callers cannot accidentally use the raw
renamed invariant when a renaming creates a third occurrence. -/
theorem mergeCollapseForFingerprints
    {left right : List Nat} (leftNonempty : left ≠ [])
    (rightNonempty : right ≠ []) (leftReduced : Reduced left)
    (rightReduced : Reduced right)
    (different : invariant left ≠ invariant right) :
    ∃ rename : Nat → Nat,
      (∀ letter ∈ left ++ right, rename letter < 4) ∧
      invariant
          (normalizationWitness.countReduce (left.map rename)) ≠
        invariant
          (normalizationWitness.countReduce (right.map rename)) := by
  have signatureDifferent :
      ¬ ((∀ letter, left.count letter = right.count letter) ∧
        suffixSignature left = suffixSignature right) := by
    intro same
    exact different ((invariant_eq_iff_signature leftNonempty rightNonempty
      leftReduced rightReduced).mpr same)
  by_cases countsEqual : ∀ letter, left.count letter = right.count letter
  · have suffixDifferent : suffixSignature left ≠ suffixSignature right := by
      intro equal
      exact signatureDifferent ⟨countsEqual, equal⟩
    let image := (suffixSignature left).letters ++
      (suffixSignature right).letters
    have imageLength : image.length ≤ 4 := by
      dsimp [image]
      have leftLength := (suffixSignature left).letters_length_le_two
      have rightLength := (suffixSignature right).letters_length_le_two
      simp only [List.length_append]
      omega
    have leftStateNonempty : (suffixSignature left).letters ≠ [] := by
      exact suffixSignature_letters_nonempty left leftNonempty
    have imageNonempty : image ≠ [] := by
      intro empty
      have := congrArg List.length empty
      simp [image, leftStateNonempty] at this
    let rename := encodeImage image
    refine ⟨rename, ?_, ?_⟩
    · intro letter _
      exact encodeImage_lt_four imageNonempty imageLength letter
    · let leftMapped := left.map rename
      let rightMapped := right.map rename
      have leftMappedNonempty : leftMapped ≠ [] :=
        map_ne_nil leftNonempty rename
      have rightMappedNonempty : rightMapped ≠ [] :=
        map_ne_nil rightNonempty rename
      have mappedSuffixDifferent :
          suffixSignature leftMapped ≠ suffixSignature rightMapped := by
        rw [suffixSignature_map, suffixSignature_map]
        intro equal
        apply suffixDifferent
        have leftCovered : ∀ letter,
            letter ∈ (suffixSignature left).letters → letter ∈ image := by
          intro letter member
          exact List.mem_append_left _ member
        have rightCovered : ∀ letter,
            letter ∈ (suffixSignature right).letters → letter ∈ image := by
          intro letter member
          exact List.mem_append_right _ member
        have leftRoundTrip := suffixMap_decode_encode
          (suffixSignature left) image leftCovered
        have rightRoundTrip := suffixMap_decode_encode
          (suffixSignature right) image rightCovered
        calc
          suffixSignature left =
              SuffixTwo.map (decodeImage image)
                (SuffixTwo.map (encodeImage image)
                  (suffixSignature left)) := leftRoundTrip.symm
          _ = SuffixTwo.map (decodeImage image)
                (SuffixTwo.map (encodeImage image)
                  (suffixSignature right)) :=
            congrArg (SuffixTwo.map (decodeImage image)) equal
          _ = suffixSignature right := rightRoundTrip
      intro invariantEqual
      have reducedLeft := normalizationWitness.reduce_reduced leftMapped
      have reducedRight := normalizationWitness.reduce_reduced rightMapped
      have signatureEqual := (invariant_eq_iff_signature
        (normalizationWitness.reduce_nonempty leftMapped leftMappedNonempty)
        (normalizationWitness.reduce_nonempty rightMapped rightMappedNonempty)
        reducedLeft reducedRight).mp invariantEqual
      apply mappedSuffixDifferent
      rw [← reducedOutput_suffix_preserved leftMapped leftMappedNonempty,
        ← reducedOutput_suffix_preserved rightMapped rightMappedNonempty]
      exact signatureEqual.2
  · have countWitness : ∃ letter, left.count letter ≠ right.count letter :=
      Classical.not_forall.mp countsEqual
    obtain ⟨chosen, countDifferent⟩ := countWitness
    let rename := collapseAt chosen
    refine ⟨rename, ?_, ?_⟩
    · intro letter _
      by_cases same : letter = chosen <;>
        simp [rename, collapseAt, same]
    · let leftMapped := left.map rename
      let rightMapped := right.map rename
      have leftMappedNonempty : leftMapped ≠ [] :=
        map_ne_nil leftNonempty rename
      have rightMappedNonempty : rightMapped ≠ [] :=
        map_ne_nil rightNonempty rename
      have leftMappedCount : leftMapped.count 0 = left.count chosen := by
        simpa [leftMapped, rename, collapseAt] using
          count_map_of_fiber rename chosen
            (collapseAt_fiber chosen) left
      have rightMappedCount : rightMapped.count 0 = right.count chosen := by
        simpa [rightMapped, rename, collapseAt] using
          count_map_of_fiber rename chosen
            (collapseAt_fiber chosen) right
      have leftOutputCount :
          (normalizationWitness.countReduce leftMapped).count 0 =
            left.count chosen := by
        rw [reducedOutput_count_preserved leftMapped leftMappedNonempty 0]
        · exact leftMappedCount
        · rw [leftMappedCount]
          exact leftReduced chosen
      have rightOutputCount :
          (normalizationWitness.countReduce rightMapped).count 0 =
            right.count chosen := by
        rw [reducedOutput_count_preserved rightMapped rightMappedNonempty 0]
        · exact rightMappedCount
        · rw [rightMappedCount]
          exact rightReduced chosen
      intro invariantEqual
      have signatureEqual := (invariant_eq_iff_signature
        (normalizationWitness.reduce_nonempty leftMapped leftMappedNonempty)
        (normalizationWitness.reduce_nonempty rightMapped rightMappedNonempty)
        (normalizationWitness.reduce_reduced leftMapped)
        (normalizationWitness.reduce_reduced rightMapped)).mp invariantEqual
      apply countDifferent
      rw [← leftOutputCount, ← rightOutputCount]
      exact signatureEqual.1 0

/-! ## Semantic fingerprints and the reusable endpoint -/

def separatorValuation (values : List Nat) (letter : Nat) : Fin 6 :=
  ⟨values.getD letter 0 % 6, Nat.mod_lt _ (by decide)⟩

def memberFingerprint (semigroup : Semigroup (Fin 6))
    (separatorValuations : List (List Nat)) (key : G3Inv) : List Nat :=
  separatorValuations.map fun values =>
    (semigroup.eval (separatorValuation values) (wordOfD (canonical key))).val

private theorem map_injective_on_of_nodup
    {entries : List α} {project : α → β}
    (mappedNodup : (entries.map project).Nodup)
    {left right : α} (leftMember : left ∈ entries)
    (rightMember : right ∈ entries)
    (sameImage : project left = project right) : left = right := by
  induction entries with
  | nil => simp at leftMember
  | cons head tail ih =>
      simp only [List.map_cons, List.nodup_cons] at mappedNodup
      rcases mappedNodup with ⟨headAbsent, tailNodup⟩
      simp only [List.mem_cons] at leftMember rightMember
      rcases leftMember with rfl | leftMember <;>
        rcases rightMember with rfl | rightMember
      · rfl
      · exfalso
        apply headAbsent
        rw [sameImage]
        exact List.mem_map.mpr ⟨right, rightMember, rfl⟩
      · exfalso
        apply headAbsent
        rw [← sameImage]
        exact List.mem_map.mpr ⟨left, leftMember, rfl⟩
      · exact ih tailNodup leftMember rightMember

theorem invariantSeparation_of_fingerprints
    (semigroup : Semigroup (Fin 6)) (models : Models semigroup basis)
    (separatorValuations : List (List Nat))
    (fingerprintsNodup :
      (canonicalInventory.map
        (memberFingerprint semigroup separatorValuations)).Nodup) :
    InvariantSeparation semigroup := by
  intro left right leftNonempty rightNonempty leftReduced rightReduced valid
  apply Classical.byContradiction
  intro different
  obtain ⟨rename, renameBounded, reducedDifferent⟩ :=
    mergeCollapseForFingerprints leftNonempty rightNonempty
      leftReduced rightReduced different
  let leftMapped := left.map rename
  let rightMapped := right.map rename
  let leftOutput := normalizationWitness.countReduce leftMapped
  let rightOutput := normalizationWitness.countReduce rightMapped
  have leftMappedNonempty : leftMapped ≠ [] := map_ne_nil leftNonempty rename
  have rightMappedNonempty : rightMapped ≠ [] := map_ne_nil rightNonempty rename
  have leftOutputNonempty : leftOutput ≠ [] :=
    normalizationWitness.reduce_nonempty leftMapped leftMappedNonempty
  have rightOutputNonempty : rightOutput ≠ [] :=
    normalizationWitness.reduce_nonempty rightMapped rightMappedNonempty
  have leftOutputReduced : Reduced leftOutput :=
    normalizationWitness.reduce_reduced leftMapped
  have rightOutputReduced : Reduced rightOutput :=
    normalizationWitness.reduce_reduced rightMapped
  have leftMappedBounded : ∀ letter, letter ∈ leftMapped → letter < 4 := by
    intro letter member
    rcases List.mem_map.mp member with ⟨source, sourceMember, rfl⟩
    exact renameBounded source (by simp [sourceMember])
  have rightMappedBounded : ∀ letter, letter ∈ rightMapped → letter < 4 := by
    intro letter member
    rcases List.mem_map.mp member with ⟨source, sourceMember, rfl⟩
    exact renameBounded source (by simp [sourceMember])
  have leftOutputBounded : ∀ letter, letter ∈ leftOutput → letter < 4 :=
    reducedOutput_bounded leftMapped leftMappedNonempty leftMappedBounded
  have rightOutputBounded : ∀ letter, letter ∈ rightOutput → letter < 4 :=
    reducedOutput_bounded rightMapped rightMappedNonempty rightMappedBounded
  have leftMember : invariant leftOutput ∈ canonicalInventory :=
    invariant_mem_canonicalInventory leftOutputNonempty leftOutputReduced
      leftOutputBounded
  have rightMember : invariant rightOutput ∈ canonicalInventory :=
    invariant_mem_canonicalInventory rightOutputNonempty rightOutputReduced
      rightOutputBounded
  have mappedValid :
      ({ lhs := wordOfD leftMapped, rhs := wordOfD rightMapped } :
        Identity Nat).SatisfiedBy semigroup := by
    simpa only [Identity.map,
      wordOfD_map left rename leftNonempty,
      wordOfD_map right rename rightNonempty] using
      Identity.satisfiedBy_map
        ({ lhs := wordOfD left, rhs := wordOfD right } : Identity Nat)
        rename semigroup valid
  have fingerprintEqual :
      memberFingerprint semigroup separatorValuations
          (invariant leftOutput) =
        memberFingerprint semigroup separatorValuations
          (invariant rightOutput) := by
    unfold memberFingerprint
    apply List.map_congr_left
    intro values _
    apply congrArg Fin.val
    have leftSound := Derives.sound models
      (normalizationWitness.derives_normalForm leftMapped leftMappedNonempty)
      (separatorValuation values)
    have rightSound := Derives.sound models
      (normalizationWitness.derives_normalForm rightMapped rightMappedNonempty)
      (separatorValuation values)
    have validValues := mappedValid (separatorValuation values)
    simpa [leftOutput, rightOutput, normalForm] using
      leftSound.symm.trans (validValues.trans rightSound)
  apply reducedDifferent
  exact map_injective_on_of_nodup fingerprintsNodup
    leftMember rightMember fingerprintEqual

/-- Finite table validity plus one finite fingerprint certificate proves that
the three displayed G3 laws form a basis. -/
theorem basisFor_of_fingerprints
    (semigroup : Semigroup (Fin 6)) (models : Models semigroup basis)
    (separatorValuations : List (List Nat))
    (fingerprintsNodup :
      (canonicalInventory.map
        (memberFingerprint semigroup separatorValuations)).Nodup) :
    BasisFor semigroup basis :=
  basisFor_of_models_invariantSeparation models normalizationWitness
    (invariantSeparation_of_fingerprints semigroup models
      separatorValuations fingerprintsNodup)

end SemigroupBasis.CoRoots.Order6LeeLiP2G3.Injection
