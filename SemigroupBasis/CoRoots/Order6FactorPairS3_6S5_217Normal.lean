import SemigroupBasis.CoRoots.Order6FactorIntersectionSpecialRoots
import SemigroupBasis.CoRoots.S5_217
import SemigroupBasis.Generated.S3_6
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Subdirect

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_6S5_217Normal

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6FactorIntersectionSpecialRoots

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xxxx : Word Nat := w 0 [0, 0, 0]
def xxxxx : Word Nat := w 0 [0, 0, 0, 0]
def xxyy : Word Nat := w 0 [0, 1, 1]
def xyyx : Word Nat := w 0 [1, 1, 0]
def xyx : Word Nat := w 0 [1, 0]
def yxx : Word Nat := w 1 [0, 0]
def xyz : Word Nat := w 0 [1, 2]
def yxz : Word Nat := w 1 [0, 2]

def powerLaw : Identity Nat := ⟨xxxx, xxxxx⟩
def repeatedFinalLaw : Identity Nat := ⟨xxyy, xyyx⟩
def rotateLaw : Identity Nat := ⟨xyx, yxx⟩
def prefixCommutationLaw : Identity Nat := ⟨xyz, yxz⟩

/-- The exact candidate basis for the `S3_6`/`S5_217` intersection. -/
def basis : List (Identity Nat) :=
  [powerLaw, repeatedFinalLaw, rotateLaw, prefixCommutationLaw]

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

theorem prefixSwap (u v q : Word Nat) :
    Derives basis ((u ++ v) ++ q) ((v ++ u) ++ q) := by
  apply Common.derivesPrefixSwap (basis := basis)
      (xyz := xyz) (yxz := yxz) rfl rfl
  exact List.Mem.tail _ <| List.Mem.tail _ <|
    List.Mem.tail _ <| List.Mem.head _

theorem terminalSwitch (u v : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ v)
      (((u ++ v) ++ v) ++ u) := by
  apply Common.derivesRepeatedFinalSwitch (basis := basis)
      (xxyy := xxyy) (xyyx := xyyx) rfl rfl
  exact List.Mem.tail _ (List.Mem.head _)

private def instantiateOneWord (u : Word Nat) : Nat → Word Nat
  | 0 => u
  | n + 1 => Word.singleton (n + 1)

theorem fiveToFour (u : Word Nat) :
    Derives basis ((((u ++ u) ++ u) ++ u) ++ u)
      (((u ++ u) ++ u) ++ u) := by
  have base : Derives basis xxxxx xxxx :=
    Derives.symm <| Derives.fromBasis (e := powerLaw) <|
      List.Mem.head _
  have substituted := Derives.subst base (instantiateOneWord u)
  simpa [basis, powerLaw, xxxxx, xxxx, w, instantiateOneWord,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Prefix copies are capped at three for the retained final and at four
for every other letter. -/
def prefixCap (final letter : Nat) : Nat :=
  if letter = final then 3 else 4

def prefixState (final letter count : Nat) : Nat :=
  min count (prefixCap final letter)

theorem prefixState_succ (final letter count : Nat) :
    prefixState final letter (count + 1) =
      if prefixState final letter count < prefixCap final letter then
        prefixState final letter count + 1
      else
        prefixState final letter count := by
  unfold prefixState
  by_cases below : count < prefixCap final letter
  · rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega),
      if_pos (by omega)]
  · rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega),
      if_neg (by omega)]

theorem prefixState_le_cap (final letter count : Nat) :
    prefixState final letter count ≤ prefixCap final letter :=
  Nat.min_le_right _ _

/-- Right-to-left capped reduction, retaining the displayed final copy. -/
def prefixReduce (final : Nat) : List Nat → List Nat
  | [] => []
  | letter :: rest =>
      let reduced := prefixReduce final rest
      if reduced.count letter < prefixCap final letter then
        letter :: reduced
      else
        reduced

theorem count_prefixReduce (final letter : Nat) (letters : List Nat) :
    (prefixReduce final letters).count letter =
      prefixState final letter (letters.count letter) := by
  induction letters with
  | nil =>
      simp [prefixReduce, prefixState, prefixCap]
  | cons head tail ih =>
      simp only [prefixReduce]
      split <;> rename_i countCase
      · by_cases same : letter = head
        · subst head
          rw [List.count_cons_self, List.count_cons_self, ih]
          rw [ih] at countCase
          rw [prefixState_succ, if_pos countCase]
        · rw [List.count_cons_of_ne (Ne.symm same),
            List.count_cons_of_ne (Ne.symm same), ih]
      · by_cases same : letter = head
        · subst head
          rw [List.count_cons_self, ih]
          rw [ih] at countCase
          rw [prefixState_succ, if_neg countCase]
        · rw [List.count_cons_of_ne (Ne.symm same), ih]

private theorem min_succ_four_sub_one (count : Nat) :
    min (count + 1) 4 - 1 = min count 3 := by
  by_cases small : count ≤ 3
  · rw [Nat.min_eq_left (by omega), Nat.min_eq_left small]
    omega
  · rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]

theorem prefixReduce_perm_of_totalCapped_eq
    (final : Nat) {left right : List Nat}
    (total : ∀ letter,
      min ((left ++ [final]).count letter) 4 =
        min ((right ++ [final]).count letter) 4) :
    (prefixReduce final left).Perm (prefixReduce final right) := by
  rw [List.perm_iff_count]
  intro letter
  rw [count_prefixReduce, count_prefixReduce]
  by_cases same : letter = final
  · subst letter
    have equality := total final
    unfold prefixState
    rw [show prefixCap final final = 3 by simp [prefixCap]]
    rw [← min_succ_four_sub_one, ← min_succ_four_sub_one]
    simpa [List.count_append] using
      congrArg (fun value : Nat => value - 1) equality
  · have equality := total letter
    simpa [prefixState, prefixCap, same, List.count_append,
      Ne.symm same] using equality

theorem derivesNormalPrefix :
    ∀ (letters : List Nat) (final : Nat),
      Derives basis
        (wordOfPrefixFinal letters final)
        (wordOfPrefixFinal (prefixReduce final letters) final)
  | [], final => Derives.refl _
  | head :: tail, final => by
      have tailNormal := derivesNormalPrefix tail final
      have prefixed :=
        Derives.prepend (Word.singleton head) tailNormal
      let reduced := prefixReduce final tail
      have reducedDef : reduced = prefixReduce final tail := rfl
      by_cases below : reduced.count head < prefixCap final head
      · have next :
            prefixReduce final (head :: tail) = head :: reduced := by
          simp [prefixReduce, reduced, below]
        rw [next]
        simpa [wordOfPrefixFinal, reduced] using prefixed
      · have upper : reduced.count head ≤ prefixCap final head := by
          rw [reducedDef, count_prefixReduce]
          exact prefixState_le_cap final head (tail.count head)
        have exactCount :
            reduced.count head = prefixCap final head := by
          omega
        have next : prefixReduce final (head :: tail) = reduced := by
          simp [prefixReduce, reduced, below]
        by_cases isFinal : head = final
        · subst final
          have countThree : reduced.count head = 3 := by
            simpa [prefixCap] using exactCount
          let remainder := Common.eraseCopies head 3 reduced
          have extracted :
              reduced.Perm
                (List.replicate 3 head ++ remainder) := by
            simpa [remainder] using
              Common.perm_extractCopies head 3 reduced countThree
          have arrangeFront :
              (head :: reduced).Perm
                (List.replicate 4 head ++ remainder) := by
            simpa [List.replicate_succ] using
              List.Perm.cons head extracted
          have arrangeEnd :
              (head :: reduced).Perm
                (remainder ++ List.replicate 4 head) := by
            refine arrangeFront.trans ?_
            rw [List.perm_iff_count]
            intro letter
            rw [List.count_append, List.count_append, Nat.add_comm]
          have arranged :=
            Common.derivesPrefixPermutation prefixSwap arrangeEnd head
          have contraction :
              Derives basis
                (wordOfPrefixFinal
                  (remainder ++ List.replicate 4 head) head)
                (wordOfPrefixFinal
                  (remainder ++ List.replicate 3 head) head) := by
            cases remainder with
            | nil =>
                simpa [wordOfPrefixFinal, List.replicate_succ,
                  Word.append, Word.singleton, Word.append_assoc] using
                    fiveToFour (Word.singleton head)
            | cons first rest =>
                have contextual :=
                  Derives.prepend
                    (SemigroupBasis.CoRoots.S5_107.listWordOfCons
                      first rest)
                    (fiveToFour (Word.singleton head))
                rw [Common.wordOfPrefixFinal_cons_append,
                  Common.wordOfPrefixFinal_cons_append]
                simpa [wordOfPrefixFinal, List.replicate_succ,
                  Word.append, Word.singleton, Word.append_assoc,
                  List.append_assoc] using contextual
          have restorePerm :
              (remainder ++ List.replicate 3 head).Perm reduced := by
            dsimp [remainder]
            rw [List.perm_iff_count]
            intro letter
            rw [List.count_append]
            by_cases same : letter = head
            · subst letter
              rw [Common.count_eraseCopies_self head 3 reduced (by omega)]
              simp
              omega
            · rw [Common.count_eraseCopies_of_ne same]
              simp [List.count_cons_of_ne (Ne.symm same)]
          have restore :=
            Common.derivesPrefixPermutation prefixSwap restorePerm head
          rw [next]
          have start :
              Derives basis
                (wordOfPrefixFinal (head :: tail) head)
                (wordOfPrefixFinal (head :: reduced) head) := by
            simpa [wordOfPrefixFinal, reduced] using prefixed
          exact start.trans <| arranged.trans <| contraction.trans restore
        · have countFour : reduced.count head = 4 := by
            simpa [prefixCap, isFinal] using exactCount
          let remainder := Common.eraseCopies head 4 reduced
          have extracted :
              reduced.Perm
                (List.replicate 4 head ++ remainder) := by
            simpa [remainder] using
              Common.perm_extractCopies head 4 reduced countFour
          have arrange :
              (head :: reduced).Perm
                (List.replicate 5 head ++ remainder) := by
            simpa [List.replicate_succ] using
              List.Perm.cons head extracted
          have arranged :=
            Common.derivesPrefixPermutation prefixSwap arrange final
          have contraction :
              Derives basis
                (wordOfPrefixFinal
                  (List.replicate 5 head ++ remainder) final)
                (wordOfPrefixFinal
                  (List.replicate 4 head ++ remainder) final) := by
            have contextual :=
              Derives.appendRight
                (fiveToFour (Word.singleton head))
                (wordOfPrefixFinal remainder final)
            simpa [wordOfPrefixFinal, List.replicate_succ,
              Word.append_assoc, List.append_assoc] using contextual
          have restorePerm :
              (List.replicate 4 head ++ remainder).Perm reduced := by
            rw [List.perm_iff_count]
            intro letter
            rw [List.count_append]
            by_cases same : letter = head
            · subst letter
              rw [Common.count_eraseCopies_self head 4 reduced (by omega)]
              simp
              omega
            · rw [Common.count_eraseCopies_of_ne same]
              simp [List.count_cons_of_ne (Ne.symm same)]
          have restore :=
            Common.derivesPrefixPermutation prefixSwap restorePerm final
          rw [next]
          have start :
              Derives basis
                (wordOfPrefixFinal (head :: tail) final)
                (wordOfPrefixFinal (head :: reduced) final) := by
            simpa [wordOfPrefixFinal, reduced] using prefixed
          exact start.trans <| arranged.trans <| contraction.trans restore
termination_by
  letters final => letters.length

theorem markerModels :
    Models finalMarkerThree.semigroup basis :=
  FiniteCertificate.checkModels_sound
    finalMarkerThree basis Common.toFinThree (by decide)

theorem cappedModels :
    Models SemigroupBasis.CoRoots.S5_217.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.CoRoots.S5_217.table basis Common.toFinThree (by decide)

theorem derivesSameFinal
    (leftPrefix rightPrefix : List Nat) (final : Nat)
    (valid :
      (⟨wordOfPrefixFinal leftPrefix final,
          wordOfPrefixFinal rightPrefix final⟩ : Identity Nat).SatisfiedBy
        SemigroupBasis.CoRoots.S5_217.table.semigroup) :
    Derives basis
      (wordOfPrefixFinal leftPrefix final)
      (wordOfPrefixFinal rightPrefix final) := by
  let identity : Identity Nat :=
    ⟨wordOfPrefixFinal leftPrefix final,
      wordOfPrefixFinal rightPrefix final⟩
  have total : ∀ letter,
      min ((leftPrefix ++ [final]).count letter) 4 =
        min ((rightPrefix ++ [final]).count letter) 4 := by
    intro letter
    have equality :=
      SemigroupBasis.CoRoots.S5_217.valid_capped_count
        identity valid letter
    simpa [identity, toList_wordOfPrefixFinal] using equality
  have normalPermutation :=
    prefixReduce_perm_of_totalCapped_eq final total
  exact (derivesNormalPrefix leftPrefix final).trans <|
    (Common.derivesPrefixPermutation prefixSwap normalPermutation final).trans <|
      (derivesNormalPrefix rightPrefix final).symm

private theorem count_ge_two_of_capped_eq
    {leftCount rightCount : Nat}
    (equalState : min leftCount 4 = min rightCount 4)
    (rightAtLeast : 2 ≤ rightCount) :
    2 ≤ leftCount := by
  have rightStateAtLeast : 2 ≤ min rightCount 4 := by
    by_cases below : rightCount ≤ 4
    · rw [Nat.min_eq_left below]
      exact rightAtLeast
    · rw [Nat.min_eq_right (by omega)]
      omega
  rw [← equalState] at rightStateAtLeast
  have stateLeCount := Nat.min_le_left leftCount 4
  omega

/-- Completeness of the displayed four laws for
`Id(S3_6) ∩ Id(S5_217)`. -/
theorem derives_of_factor_valid (identity : Identity Nat)
    (markerValid : identity.SatisfiedBy finalMarkerThree.semigroup)
    (cappedValid : identity.SatisfiedBy
      SemigroupBasis.CoRoots.S5_217.table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  let leftSplit := splitPrefixFinal identity.lhs
  let rightSplit := splitPrefixFinal identity.rhs
  have leftReconstruct :
      wordOfPrefixFinal leftSplit.1 leftSplit.2 = identity.lhs :=
    wordOfPrefixFinal_split identity.lhs
  have rightReconstruct :
      wordOfPrefixFinal rightSplit.1 rightSplit.2 = identity.rhs :=
    wordOfPrefixFinal_split identity.rhs
  by_cases sameFinal : leftSplit.2 = rightSplit.2
  · have rightReconstructSame :
        wordOfPrefixFinal rightSplit.1 leftSplit.2 = identity.rhs := by
      rw [sameFinal]
      exact rightReconstruct
    have sameValid :
        (⟨wordOfPrefixFinal leftSplit.1 leftSplit.2,
            wordOfPrefixFinal rightSplit.1 leftSplit.2⟩ :
          Identity Nat).SatisfiedBy
            SemigroupBasis.CoRoots.S5_217.table.semigroup := by
      simpa only [leftReconstruct, rightReconstructSame] using cappedValid
    rw [← leftReconstruct, ← rightReconstructSame]
    exact derivesSameFinal leftSplit.1 rightSplit.1 leftSplit.2 sameValid
  · have oldRepeated : leftSplit.2 ∈ leftSplit.1 := by
      apply Decidable.byContradiction
      intro oldSimple
      have transported :=
        (finalMarkerValid_splitSimpleFinal_iff
          identity markerValid leftSplit.2).mp ⟨rfl, oldSimple⟩
      exact sameFinal transported.1.symm
    have newRepeated : rightSplit.2 ∈ rightSplit.1 := by
      apply Decidable.byContradiction
      intro newSimple
      have transported :=
        (finalMarkerValid_splitSimpleFinal_iff
          identity markerValid rightSplit.2).mpr ⟨rfl, newSimple⟩
      exact sameFinal transported.1
    have stateEquality :=
      SemigroupBasis.CoRoots.S5_217.valid_capped_count
        identity cappedValid rightSplit.2
    have rightAtLeast :
        2 ≤ identity.rhs.toList.count rightSplit.2 := by
      rw [← rightReconstruct, toList_wordOfPrefixFinal,
        List.count_append]
      have positive := List.count_pos_iff.mpr newRepeated
      simp
      omega
    have leftAtLeast :
        2 ≤ identity.lhs.toList.count rightSplit.2 :=
      count_ge_two_of_capped_eq stateEquality rightAtLeast
    have twoNew : 2 ≤ leftSplit.1.count rightSplit.2 := by
      rw [← leftReconstruct, toList_wordOfPrefixFinal,
        List.count_append] at leftAtLeast
      simp [sameFinal, Ne.symm sameFinal] at leftAtLeast
      exact leftAtLeast
    obtain ⟨switchedPrefix, switchDerivation, _, _⟩ :=
      Common.switchRepeatedFinal prefixSwap terminalSwitch
        leftSplit.1 leftSplit.2 rightSplit.2 oldRepeated twoNew
    have alignedValid :
        (⟨wordOfPrefixFinal switchedPrefix rightSplit.2,
            wordOfPrefixFinal rightSplit.1 rightSplit.2⟩ :
          Identity Nat).SatisfiedBy
            SemigroupBasis.CoRoots.S5_217.table.semigroup := by
      intro valuation
      have switchSound := switchDerivation.sound cappedModels valuation
      have original := cappedValid valuation
      rw [← leftReconstruct, ← rightReconstruct] at original
      exact switchSound.symm.trans original
    have aligned :=
      derivesSameFinal switchedPrefix rightSplit.1 rightSplit.2 alignedValid
    rw [← leftReconstruct, ← rightReconstruct]
    exact switchDerivation.trans aligned

def canonicalIntersectionBasis :
    IntersectionBasis finalMarkerThree.semigroup
      SemigroupBasis.CoRoots.S5_217.table.semigroup basis where
  leftModels := markerModels
  rightModels := cappedModels
  complete := derives_of_factor_valid

/-- Shared endpoint consumed by every order-six root with the authenticated
`S3_6`/`S5_217` factor pair. -/
def intersectionBasis :
    IntersectionBasis SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.CoRoots.S5_217.table.semigroup basis := by
  simpa [SemigroupBasis.Generated.S3_6.table] using
    canonicalIntersectionBasis

end SemigroupBasis.CoRoots.Order6FactorPairS3_6S5_217Normal
