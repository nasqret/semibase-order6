import SemigroupBasis.CoRoots.S5_207Family
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S3_13
import SemigroupBasis.Subdirect

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6Head3Tail2

open SemigroupBasis
open SemigroupBasis.Examples

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xxx : Word Nat := w 0 [0, 0]
def xxxx : Word Nat := w 0 [0, 0, 0]
def xxy : Word Nat := w 0 [0, 1]
def xyx : Word Nat := w 0 [1, 0]
def xyy : Word Nat := w 0 [1, 1]
def xyyy : Word Nat := w 0 [1, 1, 1]
def xyz : Word Nat := w 0 [1, 2]
def xzy : Word Nat := w 0 [2, 1]

def powerLaw : Identity Nat := ⟨xxx, xxxx⟩
def gatherLaw : Identity Nat := ⟨xxy, xyx⟩
def tailMultiplicityLaw : Identity Nat := ⟨xyy, xyyy⟩
def suffixCommutationLaw : Identity Nat := ⟨xyz, xzy⟩

/-- The committed head-three/tail-two basis, in contract order. -/
def basis : List (Identity Nat) :=
  [powerLaw, gatherLaw, tailMultiplicityLaw, suffixCommutationLaw]

def candidateBasisUpToOppositeSHA256 : String :=
  "688dec5e5253d59f558f8981db483d66d6badd0b89b25d37938b418de5505931"

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem s3_13_models :
    Models SemigroupBasis.Generated.S3_13.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S3_13.table basis toFinThree (by decide)

private def s5_207Opposite : FiniteTable where
  order := 5
  mul := fun left right =>
    SemigroupBasis.CoRoots.S5_207.table.mul right left
  assoc := by decide

theorem s5_207_opposite_models :
    Models
      SemigroupBasis.CoRoots.S5_207.table.semigroup.opposite basis := by
  have checked :=
    FiniteCertificate.checkModels_sound
      s5_207Opposite basis toFinThree (by decide)
  simpa [s5_207Opposite, FiniteTable.semigroup,
    Semigroup.opposite] using checked

private def instantiateThreeWords
    (pre first second : Word Nat) : Nat → Word Nat
  | 0 => pre
  | 1 => first
  | 2 => second
  | n + 3 => Word.singleton (n + 3)

/-- Swap arbitrary nonempty blocks in the suffix of a word. -/
theorem derivesSuffixSwap (pre first second : Word Nat) :
    Derives basis
      ((pre ++ first) ++ second)
      ((pre ++ second) ++ first) := by
  have base : Derives basis xyz xzy :=
    Derives.fromBasis (e := suffixCommutationLaw) (by simp [basis])
  have substituted :=
    Derives.subst base
      (instantiateThreeWords pre first second)
  have sourceEq :
      xyz.bind (instantiateThreeWords pre first second) =
        (pre ++ first) ++ second := by
    apply Word.toList_injective
    simp [xyz, w, instantiateThreeWords, Word.toList_bind,
      Word.toList_append, Word.bind, Word.append, Word.toList,
      List.append_assoc]
  have targetEq :
      xzy.bind (instantiateThreeWords pre first second) =
        (pre ++ second) ++ first := by
    apply Word.toList_injective
    simp [xzy, w, instantiateThreeWords, Word.toList_bind,
      Word.toList_append, Word.bind, Word.append, Word.toList,
      List.append_assoc]
  rw [sourceEq, targetEq] at substituted
  exact substituted

/-- Contract three copies of a nonempty suffix block to two copies. -/
theorem derivesTailTripleContraction (pre block : Word Nat) :
    Derives basis
      (((pre ++ block) ++ block) ++ block)
      ((pre ++ block) ++ block) := by
  have base : Derives basis xyyy xyy :=
    Derives.symm <|
      Derives.fromBasis (e := tailMultiplicityLaw) (by simp [basis])
  have substituted :=
    Derives.subst base
      (instantiateThreeWords pre block block)
  have sourceEq :
      xyyy.bind (instantiateThreeWords pre block block) =
        ((pre ++ block) ++ block) ++ block := by
    apply Word.toList_injective
    simp [xyyy, w, instantiateThreeWords, Word.toList_bind,
      Word.toList_append, Word.bind, Word.append, Word.toList,
      List.append_assoc]
  have targetEq :
      xyy.bind (instantiateThreeWords pre block block) =
        (pre ++ block) ++ block := by
    apply Word.toList_injective
    simp [xyy, w, instantiateThreeWords, Word.toList_bind,
      Word.toList_append, Word.bind, Word.append, Word.toList,
      List.append_assoc]
  rw [sourceEq, targetEq] at substituted
  exact substituted

/-- Every permutation behind a fixed first letter is derivable. -/
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
  | swap first second rest =>
      cases rest with
      | nil =>
          simpa [w, Word.singleton, Word.append,
            Word.append_assoc] using
              derivesSuffixSwap
                (Word.singleton head) (Word.singleton second)
                (Word.singleton first)
      | cons next tail =>
          have swapped :=
            Derives.appendRight
              (derivesSuffixSwap
                (Word.singleton head) (Word.singleton second)
                (Word.singleton first))
              (w next tail)
          simpa [w, Word.singleton, Word.append,
            Word.append_assoc] using swapped
  | trans _ _ first second =>
      exact Derives.trans (first (head := head)) (second (head := head))

/-- Retain the last two occurrences of every suffix letter. -/
def tailCapTwo (tail : List Nat) : List Nat :=
  SemigroupBasis.CoRoots.S5_207.prefixCapTwo tail

theorem count_tailCapTwo (tested : Nat) (tail : List Nat) :
    (tailCapTwo tail).count tested = min (tail.count tested) 2 := by
  simpa [tailCapTwo] using
    SemigroupBasis.CoRoots.S5_207.count_prefixCapTwo tested tail

private theorem tailCapTwo_count_le_two
    (tested : Nat) (tail : List Nat) :
    (tailCapTwo tail).count tested ≤ 2 := by
  rw [count_tailCapTwo]
  exact Nat.min_le_right _ _

private theorem contractTailTriple
    (head letter : Nat) (suffix : List Nat) :
    Derives basis
      (w head (letter :: letter :: letter :: suffix))
      (w head (letter :: letter :: suffix)) := by
  cases suffix with
  | nil =>
      simpa [w, Word.append, Word.singleton,
        Word.append_assoc] using
          derivesTailTripleContraction
            (Word.singleton head) (Word.singleton letter)
  | cons next rest =>
      have contracted :=
        Derives.appendRight
          (derivesTailTripleContraction
            (Word.singleton head) (Word.singleton letter))
          (w next rest)
      simpa [w, Word.append, Word.singleton,
        Word.append_assoc] using contracted

private theorem deleteThirdTailCopy
    (head letter : Nat) (pre remainder : List Nat)
    (countEq : remainder.count letter = 2) :
    Derives basis
      (w head (pre ++ letter :: remainder))
      (w head (pre ++ remainder)) := by
  let without := (remainder.erase letter).erase letter
  have sourcePerm :
      (pre ++ letter :: remainder).Perm
        (letter :: letter :: letter :: pre ++ without) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases equal : tested = letter
    · subst tested
      simp only [List.count_cons_self]
      have firstErase : (remainder.erase letter).count letter = 1 := by
        rw [List.count_erase_self, countEq]
      have secondErase :
          ((remainder.erase letter).erase letter).count letter = 0 := by
        rw [List.count_erase_self, firstErase]
      simp only [without, secondErase, countEq] <;> omega
    · simp only [List.count_cons_of_ne (Ne.symm equal),
        List.count_erase_of_ne equal, without]
  have targetPerm :
      (pre ++ remainder).Perm
        (letter :: letter :: pre ++ without) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases equal : tested = letter
    · subst tested
      simp only [List.count_cons_self]
      have firstErase : (remainder.erase letter).count letter = 1 := by
        rw [List.count_erase_self, countEq]
      have secondErase :
          ((remainder.erase letter).erase letter).count letter = 0 := by
        rw [List.count_erase_self, firstErase]
      simp only [without, secondErase, countEq] <;> omega
    · simp only [List.count_cons_of_ne (Ne.symm equal),
        List.count_erase_of_ne equal, without]
  exact
    (derivesTailPermutation head sourcePerm).trans <|
      (contractTailTriple head letter (pre ++ without)).trans <|
        derivesTailPermutation head targetPerm.symm

private theorem derivesNormalizeTail :
    ∀ head pre tail,
      Derives basis
        (w head (pre ++ tail))
        (w head (pre ++ tailCapTwo tail))
  | head, pre, [] => Derives.refl _
  | head, pre, letter :: suffix => by
      have suffixNormal :=
        derivesNormalizeTail head (pre ++ [letter]) suffix
      let reduced := tailCapTwo suffix
      have firstStep :
          Derives basis
            (w head (pre ++ letter :: suffix))
            (w head (pre ++ letter :: reduced)) := by
        simpa [reduced, List.append_assoc] using suffixNormal
      by_cases countSmall : reduced.count letter < 2
      · have countSmall' :
            (SemigroupBasis.CoRoots.S5_207.prefixCapTwo suffix).count letter <
              2 := by
          simpa [reduced, tailCapTwo] using countSmall
        have reducedEq :
            tailCapTwo (letter :: suffix) = letter :: reduced := by
          simp [tailCapTwo,
            SemigroupBasis.CoRoots.S5_207.prefixCapTwo,
            reduced, countSmall']
        rw [reducedEq]
        exact firstStep
      · have countLe : reduced.count letter ≤ 2 := by
          simpa [reduced] using
            tailCapTwo_count_le_two letter suffix
        have countEq : reduced.count letter = 2 := by
          omega
        have countLarge' :
            ¬(SemigroupBasis.CoRoots.S5_207.prefixCapTwo suffix).count letter <
              2 := by
          simpa [reduced, tailCapTwo] using countSmall
        have reducedEq :
            tailCapTwo (letter :: suffix) = reduced := by
          simp [tailCapTwo,
            SemigroupBasis.CoRoots.S5_207.prefixCapTwo,
            reduced, countLarge']
        rw [reducedEq]
        exact firstStep.trans <|
          deleteThirdTailCopy head letter pre reduced countEq
termination_by
  _ _ tail => tail.length

def normal (word : Word Nat) : Word Nat :=
  w word.head (tailCapTwo word.tail)

theorem derivesNormal (word : Word Nat) :
    Derives basis word (normal word) := by
  cases word with
  | mk head tail =>
      simpa [normal, w] using derivesNormalizeTail head [] tail

/-- Equal heads and equal tail multiplicities capped at two are complete for
the four displayed laws. -/
theorem derivesOfHeadAndTailCaps
    (left right : Word Nat)
    (heads : left.head = right.head)
    (counts : ∀ tested,
      min (left.tail.count tested) 2 =
        min (right.tail.count tested) 2) :
    Derives basis left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simp only at heads counts
          subst rightHead
          have tailPerm :
              (tailCapTwo leftTail).Perm (tailCapTwo rightTail) := by
            rw [List.perm_iff_count]
            intro tested
            simpa only [count_tailCapTwo] using counts tested
          exact
            (derivesNormal (w leftHead leftTail)).trans <|
              (derivesTailPermutation leftHead tailPerm).trans <|
                (derivesNormal (w leftHead rightTail)).symm

private theorem reverse_eq_wordOfTailHead (word : Word Nat) :
    word.reverse =
      wordOfPrefixFinal word.tail.reverse word.head := by
  cases word with
  | mk head tail =>
      apply Word.toList_injective
      rw [Word.toList_reverse, toList_wordOfPrefixFinal]
      simp [Word.toList]

private theorem head_eq_of_s3_13_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemigroupBasis.Generated.S3_13.table.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  rw [SemigroupBasis.Generated.S3_13.table_eq_catalogue_model] at valid
  exact leftNormalBandValid_head_eq identity valid

private theorem tail_caps_of_s5_207_opposite_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemigroupBasis.CoRoots.S5_207.table.semigroup.opposite)
    (heads : identity.lhs.head = identity.rhs.head) :
    ∀ tested,
      min (identity.lhs.tail.count tested) 2 =
        min (identity.rhs.tail.count tested) 2 := by
  have directValid :
      identity.reversed.SatisfiedBy
        SemigroupBasis.CoRoots.S5_207.table.semigroup :=
    (Identity.satisfiedBy_opposite_iff_reversed identity
      SemigroupBasis.CoRoots.S5_207.table.semigroup).mp valid
  have directDerivation :=
    SemigroupBasis.CoRoots.S5_207Family.S5_207.basisFor.2
      identity.reversed directValid
  have sameMarker :=
    SemigroupBasis.CoRoots.S5_207.derives_sameMarkerSignature
      directDerivation
  intro tested
  have stateEq := sameMarker tested
  change
    SemigroupBasis.CoRoots.S5_207.DirectCompletenessArchitecture.markerState
        identity.lhs.reverse tested =
      SemigroupBasis.CoRoots.S5_207.DirectCompletenessArchitecture.markerState
        identity.rhs.reverse tested at stateEq
  rw [reverse_eq_wordOfTailHead, reverse_eq_wordOfTailHead,
    SemigroupBasis.CoRoots.S5_207.DirectCompletenessArchitecture.markerState_wordOfPrefixFinal,
    SemigroupBasis.CoRoots.S5_207.DirectCompletenessArchitecture.markerState_wordOfPrefixFinal]
      at stateEq
  have countEq := congrArg
    SemigroupBasis.CoRoots.S5_207.DirectCompletenessArchitecture.prefixMultiplicityOfState
    stateEq
  simpa [
    SemigroupBasis.CoRoots.S5_207.DirectCompletenessArchitecture.splitMarkerState,
    heads, List.count_reverse] using countEq

/-- Unrestricted completeness for the exact intersection of the direct
`S3_13` theory and the opposite `S5_207` theory. -/
theorem derives_of_factor_valid
    (identity : Identity Nat)
    (contentValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S3_13.table.semigroup)
    (multiplicityValid : identity.SatisfiedBy
      SemigroupBasis.CoRoots.S5_207.table.semigroup.opposite) :
    Derives basis identity.lhs identity.rhs := by
  have heads := head_eq_of_s3_13_valid identity contentValid
  exact derivesOfHeadAndTailCaps identity.lhs identity.rhs heads
    (tail_caps_of_s5_207_opposite_valid
      identity multiplicityValid heads)

def intersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.CoRoots.S5_207.table.semigroup.opposite basis where
  leftModels := s3_13_models
  rightModels := s5_207_opposite_models
  complete := derives_of_factor_valid

end SemigroupBasis.CoRoots.Order6Head3Tail2
