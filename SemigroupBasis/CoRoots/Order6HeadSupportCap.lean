import SemigroupBasis.CoRoots.S5_530Normalization
import SemigroupBasis.Examples.CommutativeCappedSupportFive
import SemigroupBasis.Examples.LeftNormalBandThree
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Subdirect

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6HeadSupportCap

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_530

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xxx : Word Nat := w 0 [0, 0]
def xxxx : Word Nat := w 0 [0, 0, 0]
def xxy : Word Nat := w 0 [0, 1]
def xxxy : Word Nat := w 0 [0, 0, 1]
def xyx : Word Nat := w 0 [1, 0]
def xyy : Word Nat := w 0 [1, 1]
def xyyy : Word Nat := w 0 [1, 1, 1]
def xyz : Word Nat := w 0 [1, 2]
def xzy : Word Nat := w 0 [2, 1]

def unaryCapLaw : Identity Nat := ⟨xxx, xxxx⟩
def prefixCapLaw : Identity Nat := ⟨xxxy, xxy⟩
def gatherLaw : Identity Nat := ⟨xxy, xyx⟩
def suffixCapLaw : Identity Nat := ⟨xyy, xyyy⟩
def suffixCommutationLaw : Identity Nat := ⟨xyz, xzy⟩

/-- The exact head-support-cap basis from the committed order-six contract. -/
def basis : List (Identity Nat) :=
  [unaryCapLaw, prefixCapLaw, gatherLaw,
    suffixCapLaw, suffixCommutationLaw]

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

private def instantiateTwoWords
    (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

private def instantiateThreeWords
    (p u v : Word Nat) : Nat → Word Nat
  | 0 => p
  | 1 => u
  | 2 => v
  | n + 3 => Word.singleton (n + 3)

/-- Swap two nonempty blocks after a fixed nonempty prefix. -/
theorem derivesSuffixSwap (pre u v : Word Nat) :
    Derives basis
      ((pre ++ u) ++ v) ((pre ++ v) ++ u) := by
  have base : Derives basis xyz xzy :=
    Derives.fromBasis (e := suffixCommutationLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateThreeWords pre u v)
  have sourceEq :
      xyz.bind (instantiateThreeWords pre u v) = (pre ++ u) ++ v := by
    apply Word.toList_injective
    simp [xyz, w, instantiateThreeWords, Word.toList_bind,
      Word.toList_append, Word.bind, Word.append, Word.toList,
      List.append_assoc]
  have targetEq :
      xzy.bind (instantiateThreeWords pre u v) = (pre ++ v) ++ u := by
    apply Word.toList_injective
    simp [xzy, w, instantiateThreeWords, Word.toList_bind,
      Word.toList_append, Word.bind, Word.append, Word.toList,
      List.append_assoc]
  rw [sourceEq, targetEq] at substituted
  exact substituted

/-- Contract a triple block after an arbitrary nonempty prefix. -/
theorem derivesSuffixTripleContraction (pre u : Word Nat) :
    Derives basis
      (pre ++ ((u ++ u) ++ u)) (pre ++ (u ++ u)) := by
  have base : Derives basis xyyy xyy :=
    Derives.symm <|
      Derives.fromBasis (e := suffixCapLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateTwoWords pre u)
  have sourceEq :
      xyyy.bind (instantiateTwoWords pre u) =
        pre ++ ((u ++ u) ++ u) := by
    apply Word.toList_injective
    simp [xyyy, w, instantiateTwoWords, Word.toList_bind,
      Word.toList_append, Word.bind, Word.append, Word.toList,
      List.append_assoc]
  have targetEq :
      xyy.bind (instantiateTwoWords pre u) = pre ++ (u ++ u) := by
    apply Word.toList_injective
    simp [xyy, w, instantiateTwoWords, Word.toList_bind,
      Word.toList_append, Word.bind, Word.append, Word.toList,
      List.append_assoc]
  rw [sourceEq, targetEq] at substituted
  exact substituted

/-- Contract an initial triple block while retaining a nonempty suffix. -/
theorem derivesPrefixTripleContraction (u suffix : Word Nat) :
    Derives basis
      (((u ++ u) ++ u) ++ suffix) ((u ++ u) ++ suffix) := by
  have base : Derives basis xxxy xxy :=
    Derives.fromBasis (e := prefixCapLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateTwoWords u suffix)
  have sourceEq :
      xxxy.bind (instantiateTwoWords u suffix) =
        ((u ++ u) ++ u) ++ suffix := by
    apply Word.toList_injective
    simp [xxxy, w, instantiateTwoWords, Word.toList_bind,
      Word.toList_append, Word.bind, Word.append, Word.toList,
      List.append_assoc]
  have targetEq :
      xxy.bind (instantiateTwoWords u suffix) = (u ++ u) ++ suffix := by
    apply Word.toList_injective
    simp [xxy, w, instantiateTwoWords, Word.toList_bind,
      Word.toList_append, Word.bind, Word.append, Word.toList,
      List.append_assoc]
  rw [sourceEq, targetEq] at substituted
  exact substituted

/-- Permute the tail while preserving the first letter. -/
theorem derivesTailPermutation (head : Nat) {left right : List Nat}
    (permutation : left.Perm right) :
    Derives basis (w head left) (w head right) := by
  induction permutation generalizing head with
  | nil =>
      exact Derives.refl _
  | cons letter _ ih =>
      have suffix := ih (head := letter)
      simpa [w, Word.singleton, Word.append] using
        Derives.prepend (Word.singleton head) suffix
  | swap left right suffix =>
      cases suffix with
      | nil =>
          simpa [w, Word.singleton, Word.append,
            Word.append_assoc] using
              derivesSuffixSwap (Word.singleton head)
                (Word.singleton right) (Word.singleton left)
      | cons next rest =>
          have swapped :=
            Derives.appendRight
              (derivesSuffixSwap (Word.singleton head)
                (Word.singleton right) (Word.singleton left))
              (w next rest)
          simpa [w, Word.singleton, Word.append,
            Word.append_assoc] using swapped
  | trans _ _ first second =>
      exact Derives.trans (first (head := head)) (second (head := head))

private theorem s5_530AxiomsDerive
    (identity : Identity Nat) (member : identity ∈ s5_530Basis) :
    Derives basis identity.lhs identity.rhs := by
  simp only [s5_530Basis, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl
  · have source : Derives basis xxx xxxx :=
      Derives.fromBasis (e := unaryCapLaw) (by simp [basis])
    simpa [s5_530PowerLaw, s5_530XXX, s5_530XXXX,
      unaryCapLaw, xxx, xxxx, w] using source
  · have source : Derives basis xxy xyx :=
      Derives.fromBasis (e := gatherLaw) (by simp [basis])
    simpa [s5_530GatherLaw, s5_530XXY, s5_530XYX,
      gatherLaw, xxy, xyx, w] using source

private def appendLetters (pre : Word Nat) (letters : List Nat) :
    Word Nat :=
  letters.foldl
    (fun word letter => word ++ Word.singleton letter) pre

@[simp] private theorem appendLetters_nil (pre : Word Nat) :
    appendLetters pre [] = pre := rfl

@[simp] private theorem appendLetters_cons
    (pre : Word Nat) (letter : Nat) (letters : List Nat) :
    appendLetters pre (letter :: letters) =
      appendLetters (pre ++ Word.singleton letter) letters := rfl

private theorem appendLetters_derives {left right : Word Nat}
    (derivation : Derives basis left right) (letters : List Nat) :
    Derives basis
      (appendLetters left letters) (appendLetters right letters) := by
  induction letters generalizing left right with
  | nil => exact derivation
  | cons letter letters ih =>
      simp only [appendLetters_cons]
      exact ih (Derives.appendRight derivation (Word.singleton letter))

private theorem appendLetters_wordOfCons
    (head : Nat) (pre rest : List Nat) :
    appendLetters (s5_530WordOfCons head pre) rest =
      s5_530WordOfCons head (pre ++ rest) := by
  induction rest generalizing pre with
  | nil => simp
  | cons letter rest ih =>
      simp only [appendLetters_cons]
      simpa [s5_530WordOfCons, Word.append,
        Word.singleton, List.append_assoc] using
          ih (pre ++ [letter])

private theorem derivesTailTripleList
    (pre : Word Nat) (letter : Nat) (rest : List Nat) :
    Derives basis
      (appendLetters pre (letter :: letter :: letter :: rest))
      (appendLetters pre (letter :: letter :: rest)) := by
  have contracted :=
    derivesSuffixTripleContraction pre (Word.singleton letter)
  have extended := appendLetters_derives contracted rest
  simpa [appendLetters, Word.singleton,
    Word.append_assoc] using extended

private theorem derivesHeadTripleList
    (head next : Nat) (rest : List Nat) :
    Derives basis
      (s5_530WordOfCons head (head :: head :: next :: rest))
      (s5_530WordOfCons head (head :: next :: rest)) := by
  have contracted :=
    derivesPrefixTripleContraction (Word.singleton head)
      (s5_530WordOfCons next rest)
  simpa [s5_530WordOfCons, Word.singleton,
    Word.append, Word.append_assoc] using contracted

/-- A block normal form with every triple block shortened to a double. -/
private inductive CapTwoNormal : List Nat → List Nat → Prop
  | nil : CapTwoNormal [] []
  | single (x : Nat) {source target : List Nat} :
      CapTwoNormal source target →
      x ∉ source →
      CapTwoNormal (x :: source) (x :: target)
  | double (x : Nat) {source target : List Nat} :
      CapTwoNormal source target →
      x ∉ source →
      CapTwoNormal (x :: x :: source) (x :: x :: target)
  | triple (x : Nat) {source target : List Nat} :
      CapTwoNormal source target →
      x ∉ source →
      CapTwoNormal (x :: x :: x :: source) (x :: x :: target)

private theorem CapTwoNormal.exists_of_s5_530Normal
    {source : List Nat} (normal : S5_530Normal source) :
    ∃ target, CapTwoNormal source target := by
  induction normal with
  | nil =>
      exact ⟨[], CapTwoNormal.nil⟩
  | single x source _ notMem ih =>
      obtain ⟨target, capped⟩ := ih
      exact ⟨x :: target, CapTwoNormal.single x capped notMem⟩
  | double x source _ notMem ih =>
      obtain ⟨target, capped⟩ := ih
      exact ⟨x :: x :: target, CapTwoNormal.double x capped notMem⟩
  | triple x source _ notMem ih =>
      obtain ⟨target, capped⟩ := ih
      exact ⟨x :: x :: target, CapTwoNormal.triple x capped notMem⟩

private theorem CapTwoNormal.count_eq
    {source target : List Nat} (capped : CapTwoNormal source target)
    (letter : Nat) :
    target.count letter = min (source.count letter) 2 := by
  induction capped generalizing letter with
  | nil => simp
  | @single x source target capped notMem ih =>
      by_cases same : letter = x
      · subst letter
        have sourceZero : source.count x = 0 :=
          List.count_eq_zero.mpr notMem
        have targetZero : target.count x = 0 := by
          have state := ih x
          rw [sourceZero] at state
          simpa using state
        simp [sourceZero, targetZero]
      · simpa [List.count_cons_of_ne (Ne.symm same)] using ih letter
  | @double x source target capped notMem ih =>
      by_cases same : letter = x
      · subst letter
        have sourceZero : source.count x = 0 :=
          List.count_eq_zero.mpr notMem
        have targetZero : target.count x = 0 := by
          have state := ih x
          rw [sourceZero] at state
          simpa using state
        simp [sourceZero, targetZero]
      · simpa [List.count_cons_of_ne (Ne.symm same)] using ih letter
  | @triple x source target capped notMem ih =>
      by_cases same : letter = x
      · subst letter
        have sourceZero : source.count x = 0 :=
          List.count_eq_zero.mpr notMem
        have targetZero : target.count x = 0 := by
          have state := ih x
          rw [sourceZero] at state
          simpa using state
        simp [sourceZero, targetZero]
      · simpa [List.count_cons_of_ne (Ne.symm same)] using ih letter

private theorem CapTwoNormal.derivesAfter
    {source target : List Nat} (capped : CapTwoNormal source target)
    (pre : Word Nat) :
    Derives basis
      (appendLetters pre source) (appendLetters pre target) := by
  induction capped generalizing pre with
  | nil =>
      exact Derives.refl _
  | single x capped _ ih =>
      simpa only [appendLetters_cons] using
        ih (pre ++ Word.singleton x)
  | double x capped _ ih =>
      simpa only [appendLetters_cons] using
        ih ((pre ++ Word.singleton x) ++ Word.singleton x)
  | @triple x source target capped _ ih =>
      have contracted := derivesTailTripleList pre x source
      have remaining :=
        ih ((pre ++ Word.singleton x) ++ Word.singleton x)
      have remaining' :
          Derives basis
            (appendLetters pre (x :: x :: source))
            (appendLetters pre (x :: x :: target)) := by
        simpa only [appendLetters_cons] using remaining
      exact contracted.trans remaining'

private theorem derivesCappedNormal
    {head : Nat} {tail : List Nat}
    (normal : S5_530Normal (head :: tail))
    (multipleSupport :
      ∃ letter, letter ∈ head :: tail ∧ letter ≠ head) :
    ∃ target : Word Nat,
      Derives basis (s5_530WordOfCons head tail) target ∧
      CapTwoNormal (head :: tail) target.toList ∧
      target.head = head := by
  cases normal with
  | single head tail tailNormal notMem =>
      obtain ⟨targetTail, capped⟩ :=
        CapTwoNormal.exists_of_s5_530Normal tailNormal
      let target : Word Nat := ⟨head, targetTail⟩
      have derivation := capped.derivesAfter (Word.singleton head)
      refine ⟨target, ?_, ?_, rfl⟩
      · change Derives basis
          (appendLetters (s5_530WordOfCons head []) tail)
          (appendLetters (s5_530WordOfCons head []) targetTail)
          at derivation
        simpa only [appendLetters_wordOfCons] using derivation
      · simpa [target, Word.toList] using
          CapTwoNormal.single head capped notMem
  | double head tail tailNormal notMem =>
      obtain ⟨targetTail, capped⟩ :=
        CapTwoNormal.exists_of_s5_530Normal tailNormal
      let target : Word Nat := ⟨head, head :: targetTail⟩
      have derivation :=
        capped.derivesAfter (s5_530WordOfCons head [head])
      refine ⟨target, ?_, ?_, rfl⟩
      · simpa only [appendLetters_wordOfCons] using derivation
      · simpa [target, Word.toList] using
          CapTwoNormal.double head capped notMem
  | triple head tail tailNormal notMem =>
      have tailNonempty : tail ≠ [] := by
        intro empty
        subst tail
        obtain ⟨letter, member, different⟩ := multipleSupport
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        all_goals exact different rfl
      cases tail with
      | nil => contradiction
      | cons next rest =>
          obtain ⟨targetTail, capped⟩ :=
            CapTwoNormal.exists_of_s5_530Normal tailNormal
          let target : Word Nat := ⟨head, head :: targetTail⟩
          have first := derivesHeadTripleList head next rest
          have remaining :=
            capped.derivesAfter (s5_530WordOfCons head [head])
          have remaining' :
              Derives basis
                (s5_530WordOfCons head (head :: next :: rest))
                target := by
            simpa only [appendLetters_wordOfCons] using remaining
          refine ⟨target, first.trans remaining', ?_, rfl⟩
          simpa [target, Word.toList] using
            CapTwoNormal.triple head capped notMem

private theorem derivesOfHeadAndCounts
    (left right : Word Nat)
    (heads : left.head = right.head)
    (counts : ∀ letter,
      left.toList.count letter = right.toList.count letter) :
    Derives basis left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simp only at heads
          subst rightHead
          apply derivesTailPermutation leftHead
          rw [List.perm_iff_count]
          intro letter
          have whole := counts letter
          simp only [Word.toList] at whole
          by_cases same : letter = leftHead
          · subst letter
            simpa using whole
          · simpa [List.count_cons_of_ne (Ne.symm same)] using whole

private theorem firstOccurrenceSequence_eq_singleton
    (head : Nat) (tail : List Nat)
    (unary : ∀ letter, letter ∈ head :: tail → letter = head) :
    firstOccurrenceSequence (head :: tail) = [head] := by
  induction tail generalizing head with
  | nil => simp [firstOccurrenceSequence]
  | cons next rest ih =>
      have nextEq : next = head := unary next (by simp)
      subst next
      have restUnary :
          ∀ letter, letter ∈ head :: rest → letter = head := by
        intro letter member
        exact unary letter (by simp [member])
      rw [firstOccurrenceSequence, ih head restUnary]
      simp

private theorem firstOccurrenceSequence_word_eq_singleton
    (word : Word Nat)
    (unary : ∀ letter, letter ∈ word.toList →
      letter = word.head) :
    firstOccurrenceSequence word.toList = [word.head] := by
  cases word with
  | mk head tail =>
      exact firstOccurrenceSequence_eq_singleton head tail unary

private theorem count_eq_length_of_all_eq
    (head : Nat) (letters : List Nat)
    (unary : ∀ letter, letter ∈ letters → letter = head) :
    letters.count head = letters.length := by
  induction letters with
  | nil => rfl
  | cons letter letters ih =>
      have letterEq := unary letter (by simp)
      subst letter
      rw [List.count_cons_self, List.length_cons]
      congr 1
      exact ih (fun tested member => unary tested (by simp [member]))

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem leftFactorModels :
    Models leftNormalBandThree.semigroup basis :=
  FiniteCertificate.checkModels_sound
    leftNormalBandThree basis toFinThree (by decide)

theorem rightFactorModels :
    Models commutativeCappedSupportFive.semigroup basis :=
  FiniteCertificate.checkModels_sound
    commutativeCappedSupportFive basis toFinThree (by decide)

/-- Unrestricted completeness for the exact intersection
`Id(S3_13) ∩ Id(S5_201)`. -/
theorem derives_of_factor_valid (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftNormalBandThree.semigroup)
    (rightValid :
      identity.SatisfiedBy commutativeCappedSupportFive.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have heads := leftNormalBandValid_head_eq identity leftValid
  have support := leftNormalBandValid_support_eq identity leftValid
  have cappedTwo :=
    cappedSupportValid_cappedCountTwo identity rightValid
  have cappedLength :=
    cappedSupportValid_cappedLengthThree identity rightValid
  by_cases multipleSupport :
      ∃ letter,
        letter ∈ identity.lhs.toList ∧
          letter ≠ identity.lhs.head
  · obtain ⟨witness, witnessLeft, witnessDifferent⟩ :=
      multipleSupport
    have witnessRight : witness ∈ identity.rhs.toList :=
      (support witness).mp witnessLeft
    have witnessDifferentRight : witness ≠ identity.rhs.head := by
      simpa [heads] using witnessDifferent
    have leftNormal := s5_530DerivesNormal identity.lhs
    have rightNormal := s5_530DerivesNormal identity.rhs
    cases leftEquation : s5_530NormalList identity.lhs.toList with
    | nil =>
        exact False.elim <|
          s5_530NormalList_cons_ne_nil
            identity.lhs.head identity.lhs.tail <| by
              simpa [Word.toList] using leftEquation
    | cons leftHead leftTail =>
        cases rightEquation : s5_530NormalList identity.rhs.toList with
        | nil =>
            exact False.elim <|
              s5_530NormalList_cons_ne_nil
                identity.rhs.head identity.rhs.tail <| by
                  simpa [Word.toList] using rightEquation
        | cons rightHead rightTail =>
            rw [leftEquation] at leftNormal
            rw [rightEquation] at rightNormal
            have leftForm : S5_530Normal (leftHead :: leftTail) := by
              rw [← leftEquation]
              exact s5_530NormalList_normal identity.lhs.toList
            have rightForm : S5_530Normal (rightHead :: rightTail) := by
              rw [← rightEquation]
              exact s5_530NormalList_normal identity.rhs.toList
            have firstOccurrenceHead (word : Word Nat) :
                (firstOccurrenceSequence word.toList).head? =
                  some word.head := by
              rfl
            have leftHeadEq : leftHead = identity.lhs.head := by
              have preserved :=
                s5_530Derives_firstOccurrenceSequence_eq leftNormal
              have firsts := congrArg List.head? preserved
              rw [firstOccurrenceHead identity.lhs,
                firstOccurrenceHead
                  (s5_530WordOfCons leftHead leftTail)] at firsts
              simpa [s5_530WordOfCons] using firsts.symm
            have rightHeadEq : rightHead = identity.rhs.head := by
              have preserved :=
                s5_530Derives_firstOccurrenceSequence_eq rightNormal
              have firsts := congrArg List.head? preserved
              rw [firstOccurrenceHead identity.rhs,
                firstOccurrenceHead
                  (s5_530WordOfCons rightHead rightTail)] at firsts
              simpa [s5_530WordOfCons] using firsts.symm
            have leftNormalCount (letter : Nat) :
                (leftHead :: leftTail).count letter =
                  s5_530Exponent
                    (identity.lhs.toList.count letter) := by
              calc
                (leftHead :: leftTail).count letter =
                    (s5_530NormalList identity.lhs.toList).count letter := by
                      rw [leftEquation]
                _ = s5_530Exponent
                      (identity.lhs.toList.count letter) :=
                    s5_530NormalList_count letter identity.lhs.toList
            have rightNormalCount (letter : Nat) :
                (rightHead :: rightTail).count letter =
                  s5_530Exponent
                    (identity.rhs.toList.count letter) := by
              calc
                (rightHead :: rightTail).count letter =
                    (s5_530NormalList identity.rhs.toList).count letter := by
                      rw [rightEquation]
                _ = s5_530Exponent
                      (identity.rhs.toList.count letter) :=
                    s5_530NormalList_count letter identity.rhs.toList
            have leftNormalMultiple :
                ∃ letter,
                  letter ∈ leftHead :: leftTail ∧
                    letter ≠ leftHead := by
              have positive :
                  0 < (leftHead :: leftTail).count witness := by
                rw [leftNormalCount witness]
                exact s5_530Exponent_pos
                  (List.count_pos_iff.mpr witnessLeft)
              exact ⟨witness, List.count_pos_iff.mp positive, by
                simpa [leftHeadEq] using witnessDifferent⟩
            have rightNormalMultiple :
                ∃ letter,
                  letter ∈ rightHead :: rightTail ∧
                    letter ≠ rightHead := by
              have positive :
                  0 < (rightHead :: rightTail).count witness := by
                rw [rightNormalCount witness]
                exact s5_530Exponent_pos
                  (List.count_pos_iff.mpr witnessRight)
              exact ⟨witness, List.count_pos_iff.mp positive, by
                simpa [rightHeadEq] using witnessDifferentRight⟩
            obtain ⟨leftCapped, leftCapDerivation,
                leftCapRelation, leftCapHead⟩ :=
              derivesCappedNormal leftForm leftNormalMultiple
            obtain ⟨rightCapped, rightCapDerivation,
                rightCapRelation, rightCapHead⟩ :=
              derivesCappedNormal rightForm rightNormalMultiple
            have leftCappedCount (letter : Nat) :
                leftCapped.toList.count letter =
                  min (identity.lhs.toList.count letter) 2 := by
              calc
                leftCapped.toList.count letter =
                    min ((leftHead :: leftTail).count letter) 2 :=
                  leftCapRelation.count_eq letter
                _ = min
                    (s5_530Exponent
                      (identity.lhs.toList.count letter)) 2 := by
                  rw [leftNormalCount]
                _ = min (identity.lhs.toList.count letter) 2 := by
                  simp [s5_530Exponent, Nat.min_assoc]
            have rightCappedCount (letter : Nat) :
                rightCapped.toList.count letter =
                  min (identity.rhs.toList.count letter) 2 := by
              calc
                rightCapped.toList.count letter =
                    min ((rightHead :: rightTail).count letter) 2 :=
                  rightCapRelation.count_eq letter
                _ = min
                    (s5_530Exponent
                      (identity.rhs.toList.count letter)) 2 := by
                  rw [rightNormalCount]
                _ = min (identity.rhs.toList.count letter) 2 := by
                  simp [s5_530Exponent, Nat.min_assoc]
            have cappedHeads : leftCapped.head = rightCapped.head := by
              calc
                leftCapped.head = leftHead := leftCapHead
                _ = identity.lhs.head := leftHeadEq
                _ = identity.rhs.head := heads
                _ = rightHead := rightHeadEq.symm
                _ = rightCapped.head := rightCapHead.symm
            have cappedCounts : ∀ letter,
                leftCapped.toList.count letter =
                  rightCapped.toList.count letter := by
              intro letter
              rw [leftCappedCount, rightCappedCount,
                cappedTwo letter]
            have middle :=
              derivesOfHeadAndCounts leftCapped rightCapped
                cappedHeads cappedCounts
            have leftNormalized :
                Derives basis identity.lhs
                  (s5_530WordOfCons leftHead leftTail) :=
              leftNormal.transport s5_530AxiomsDerive
            have rightNormalized :
                Derives basis identity.rhs
                  (s5_530WordOfCons rightHead rightTail) :=
              rightNormal.transport s5_530AxiomsDerive
            exact leftNormalized.trans <|
              leftCapDerivation.trans <|
                middle.trans <|
                  rightCapDerivation.symm.trans rightNormalized.symm
  · have leftUnary : ∀ letter,
        letter ∈ identity.lhs.toList →
          letter = identity.lhs.head := by
      intro letter member
      apply Decidable.byContradiction
      intro different
      exact multipleSupport ⟨letter, member, different⟩
    have rightUnary : ∀ letter,
        letter ∈ identity.rhs.toList →
          letter = identity.rhs.head := by
      intro letter member
      have leftMember := (support letter).mpr member
      exact (leftUnary letter leftMember).trans heads
    have occurrenceOrder :
        firstOccurrenceSequence identity.lhs.toList =
          firstOccurrenceSequence identity.rhs.toList := by
      rw [firstOccurrenceSequence_word_eq_singleton
          identity.lhs leftUnary,
        firstOccurrenceSequence_word_eq_singleton
          identity.rhs rightUnary,
        heads]
    have exponentCounts : ∀ letter,
        s5_530Exponent (identity.lhs.toList.count letter) =
          s5_530Exponent (identity.rhs.toList.count letter) := by
      intro letter
      by_cases same : letter = identity.lhs.head
      · subst letter
        have leftCount :=
          count_eq_length_of_all_eq identity.lhs.head
            identity.lhs.toList leftUnary
        have rightCount :=
          count_eq_length_of_all_eq identity.rhs.head
            identity.rhs.toList rightUnary
        rw [leftCount]
        rw [show identity.rhs.toList.count identity.lhs.head =
            identity.rhs.toList.length by
          simpa [heads] using rightCount]
        simpa [s5_530Exponent] using cappedLength
      · have leftAbsent : letter ∉ identity.lhs.toList := by
          intro member
          exact same (leftUnary letter member)
        have rightAbsent : letter ∉ identity.rhs.toList := by
          intro member
          have equalRight := rightUnary letter member
          exact same (equalRight.trans heads.symm)
        simp [s5_530Exponent,
          List.count_eq_zero.mpr leftAbsent,
          List.count_eq_zero.mpr rightAbsent]
    exact (s5_530DerivesOfInvariantEq
      identity.lhs identity.rhs occurrenceOrder exponentCounts).transport
        s5_530AxiomsDerive

def intersectionBasis :
    IntersectionBasis leftNormalBandThree.semigroup
      commutativeCappedSupportFive.semigroup basis where
  leftModels := leftFactorModels
  rightModels := rightFactorModels
  complete := derives_of_factor_valid

namespace S6_5552

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- The exact zero-based Smallsemi table `S6_5552`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 0 0 right else
      if left = 2 then row6 0 0 0 0 0 2 right else
        if left = 3 then row6 0 0 0 1 0 0 right else
          if left = 4 then row6 4 4 4 4 4 4 right else
            row6 0 0 2 0 0 5 right

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 =>
      (table.semigroup.mul left right).val + 1

theorem tableOneBased_certificate :
    tableOneBased =
      [[1, 1, 1, 1, 1, 1],
       [1, 1, 1, 1, 1, 1],
       [1, 1, 1, 1, 1, 3],
       [1, 1, 1, 2, 1, 1],
       [5, 5, 5, 5, 5, 5],
       [1, 1, 3, 1, 1, 6]] := by
  decide

/-- The quotient `[1,1,1,1,3,2]` onto `S3_13`. -/
def contentMap (value : Fin 6) : Fin 3 :=
  if value = 4 then 2 else
    if value = 5 then 1 else 0

def contentPreimage (value : Fin 3) : Fin 6 :=
  if value = 0 then 0 else if value = 1 then 5 else 4

def contentQuotient : SplitSurjection table.semigroup
    leftNormalBandThree.semigroup where
  toFun := contentMap
  map_mul := by decide
  preimage := contentPreimage
  right_inverse := by decide

/-- The recorded quotient `[1,2,3,4,1,5]` onto `S5_201`. -/
def multiplicityMap (value : Fin 6) : Fin 5 :=
  if value = 0 then 0 else
    if value = 1 then 1 else
      if value = 2 then 2 else
        if value = 3 then 3 else
          if value = 4 then 0 else 4

def multiplicityPreimage (value : Fin 5) : Fin 6 :=
  if value = 0 then 0 else
    if value = 1 then 1 else
      if value = 2 then 2 else
        if value = 3 then 3 else 5

def multiplicityQuotient : SplitSurjection table.semigroup
    commutativeCappedSupportFive.semigroup where
  toFun := multiplicityMap
  map_mul := by decide
  preimage := multiplicityPreimage
  right_inverse := by decide

def subdirectPair : SubdirectPair table.semigroup
    leftNormalBandThree.semigroup
    commutativeCappedSupportFive.semigroup where
  left := contentQuotient
  right := multiplicityQuotient
  jointlyInjective := by
    intro left right equal
    revert left right
    decide

theorem representative_basis :
    BasisFor table.semigroup basis :=
  intersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using representative_basis.oppositeReversed

end S6_5552

end SemigroupBasis.CoRoots.Order6HeadSupportCap
