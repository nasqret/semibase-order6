import SemigroupBasis.CoRoots.S5_870Family
import SemigroupBasis.Examples.CommutativePeriodTwoFromTwo
import SemigroupBasis.Examples.CyclicTwo
import SemigroupBasis.Subdirect

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeLiCondition8Join

open SemigroupBasis
open SemigroupBasis.Examples

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxxx : Word Nat := w 0 [0, 0, 0]
def xxxz : Word Nat := w 0 [0, 0, 2]
def xxzx : Word Nat := w 0 [0, 2, 0]
def xyx : Word Nat := w 0 [1, 0]
def xyxxx : Word Nat := w 0 [1, 0, 0, 0]
def xyxxz : Word Nat := w 0 [1, 0, 0, 2]
def xyxzx : Word Nat := w 0 [1, 0, 2, 0]
def xyxy : Word Nat := w 0 [2, 0, 2]
def xyyx : Word Nat := w 0 [2, 2, 0]
def xytxy : Word Nat := w 0 [2, 3, 0, 2]
def xytyx : Word Nat := w 0 [2, 3, 2, 0]
def xhyxy : Word Nat := w 0 [1, 2, 0, 2]
def xhyyx : Word Nat := w 0 [1, 2, 2, 0]
def xhytxy : Word Nat := w 0 [1, 2, 3, 0, 2]
def xhytyx : Word Nat := w 0 [1, 2, 3, 2, 0]

def powerLaw : Identity Nat := ⟨xx, xxxx⟩
def gatherInitialGapEmptyLaw : Identity Nat := ⟨xxxz, xxzx⟩
def rightPeriodLaw : Identity Nat := ⟨xyx, xyxxx⟩
def gatherGeneralLaw : Identity Nat := ⟨xyxxz, xyxzx⟩
def sortBothEmptyLaw : Identity Nat := ⟨xyxy, xyyx⟩
def sortInitialGapEmptyLaw : Identity Nat := ⟨xytxy, xytyx⟩
def sortFinalGapEmptyLaw : Identity Nat := ⟨xhyxy, xhyyx⟩
def sortGeneralLaw : Identity Nat := ⟨xhytxy, xhytyx⟩

/-- Lee-Li Proposition 6.4 at `p = 2`, in the exact direct packet order.
The four sorting laws are the `S5_870` gap-block laws. -/
def directBasis : List (Identity Nat) :=
  [sortGeneralLaw, sortFinalGapEmptyLaw,
    powerLaw, gatherInitialGapEmptyLaw,
    sortInitialGapEmptyLaw, rightPeriodLaw,
    gatherGeneralLaw, sortBothEmptyLaw]

/-- Literal packet orientation assigned to nine unresolved order-six rows. -/
def basis : List (Identity Nat) :=
  reversedBasis directBasis

def basisSha256 : String :=
  "8ab847ee4900ea2806a8c053ab6341024f8d7d2c29a4454d1b4b9e668205dadc"

def packetSha256 : String :=
  "54d7c44d876c04e41eadf640c4c47e93c83d2062b0d22680f74d578e7a1ca5f2"

def proofRoute : String :=
  "lee-li-constructive-condition-branch"

/-- Metadata inventory only. Concrete transfer wrappers are required before
any listed root is closed. -/
def coveredRootIds : List String :=
  ["S6_11550", "S6_11554", "S6_11552", "S6_8932", "S6_9073",
    "S6_11162", "S6_11170", "S6_11602", "S6_11782"]

/-! ## The factor join -/

/-- A concrete representative of the join of the `S5_870` and cyclic-two
varieties. -/
def directJoinSemigroup : Semigroup (Fin 5 × Fin 2) where
  mul left right :=
    (S5_870.table.semigroup.mul left.1 right.1,
      cyclicTwo.semigroup.mul left.2 right.2)
  assoc := by
    intro left middle right
    apply Prod.ext
    · exact S5_870.table.semigroup.assoc left.1 middle.1 right.1
    · exact cyclicTwo.semigroup.assoc left.2 middle.2 right.2

/-- The orientation represented by the packet basis hash. -/
def joinSemigroup : Semigroup (Fin 5 × Fin 2) :=
  directJoinSemigroup.opposite

private def leftProjection :
    SplitSurjection directJoinSemigroup S5_870.table.semigroup where
  toFun := Prod.fst
  map_mul := by intros; rfl
  preimage := fun value => (value, 0)
  right_inverse := by intros; rfl

private def rightProjection :
    SplitSurjection directJoinSemigroup cyclicTwo.semigroup where
  toFun := Prod.snd
  map_mul := by intros; rfl
  preimage := fun value => (0, value)
  right_inverse := by intros; rfl

private def directJoinPair :
    SubdirectPair directJoinSemigroup S5_870.table.semigroup
      cyclicTwo.semigroup where
  left := leftProjection
  right := rightProjection
  jointlyInjective := by
    intro left right equality
    exact Prod.ext (congrArg Prod.fst equality)
      (congrArg Prod.snd equality)

/-! ## Soundness in both factors -/

private def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

private def finiteDirectBasis : List (Identity (Fin 4)) :=
  directBasis.map fun identity => identity.map toFinFour

private theorem directBasis_roundTrip_checked :
    directBasis.all (fun identity =>
      decide ((identity.map toFinFour).map Fin.val = identity)) = true := by
  decide

private theorem directBasis_roundTrip
    (identity : Identity Nat) (member : identity ∈ directBasis) :
    (identity.map toFinFour).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp directBasis_roundTrip_checked) identity member

private theorem models_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteDirectBasis.all candidate.checkIdentity = true) :
    Models candidate.semigroup directBasis := by
  intro identity member
  have finiteMember : identity.map toFinFour ∈ finiteDirectBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityNat_sound (identity.map toFinFour)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [directBasis_roundTrip identity member] at finiteValid
  exact finiteValid

private theorem s5Models :
    Models S5_870.table.semigroup directBasis :=
  models_of_finite_checks S5_870.table (by decide)

private theorem cyclicModels :
    Models cyclicTwo.semigroup directBasis :=
  models_of_finite_checks cyclicTwo (by decide)

/-! ## Primitive Lee-Li derivations -/

private def instantiateFourWords
    (x h y t : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => h
  | 2 => y
  | 3 => t
  | n + 4 => Word.singleton (n + 4)

private theorem basisPower : Derives directBasis xx xxxx :=
  Derives.fromBasis (e := powerLaw) <| by simp [directBasis]

private theorem basisGatherInitialGapEmpty :
    Derives directBasis xxxz xxzx :=
  Derives.fromBasis (e := gatherInitialGapEmptyLaw) <| by
    simp [directBasis]

private theorem basisRightPeriod : Derives directBasis xyx xyxxx :=
  Derives.fromBasis (e := rightPeriodLaw) <| by simp [directBasis]

private theorem basisGatherGeneral : Derives directBasis xyxxz xyxzx :=
  Derives.fromBasis (e := gatherGeneralLaw) <| by simp [directBasis]

theorem derivesFourToTwo (x : Word Nat) :
    Derives directBasis (((x ++ x) ++ x) ++ x) (x ++ x) := by
  have substituted :=
    Derives.subst basisPower (instantiateFourWords x x x x)
  simpa [powerLaw, xx, xxxx, w, instantiateFourWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted.symm

theorem derivesRightPeriodContraction (x h : Word Nat) :
    Derives directBasis ((((x ++ h) ++ x) ++ x) ++ x)
      ((x ++ h) ++ x) := by
  have substituted :=
    Derives.subst basisRightPeriod (instantiateFourWords x h x x)
  simpa [rightPeriodLaw, xyx, xyxxx, w, instantiateFourWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted.symm

theorem derivesGatherInitialGapEmpty (x z : Word Nat) :
    Derives directBasis (((x ++ x) ++ z) ++ x)
      (((x ++ x) ++ x) ++ z) := by
  have substituted :=
    Derives.subst basisGatherInitialGapEmpty
      (instantiateFourWords x x z z)
  simpa [gatherInitialGapEmptyLaw, xxxz, xxzx, w,
    instantiateFourWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted.symm

theorem derivesGatherGeneral (x h z : Word Nat) :
    Derives directBasis ((((x ++ h) ++ x) ++ z) ++ x)
      ((((x ++ h) ++ x) ++ x) ++ z) := by
  have substituted :=
    Derives.subst basisGatherGeneral
      (instantiateFourWords x h z z)
  simpa [gatherGeneralLaw, xyxxz, xyxzx, w,
    instantiateFourWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted.symm

/-! ## `S5_870` gap-block sorting under the Lee-Li basis -/

private theorem basisSortBothEmpty :
    Derives directBasis xyxy xyyx :=
  Derives.fromBasis (e := sortBothEmptyLaw) <| by
    simp [directBasis]

private theorem basisSortInitialGapEmpty :
    Derives directBasis xytxy xytyx :=
  Derives.fromBasis (e := sortInitialGapEmptyLaw) <| by
    simp [directBasis]

private theorem basisSortFinalGapEmpty :
    Derives directBasis xhyxy xhyyx :=
  Derives.fromBasis (e := sortFinalGapEmptyLaw) <| by
    simp [directBasis]

private theorem basisSortGeneral :
    Derives directBasis xhytxy xhytyx :=
  Derives.fromBasis (e := sortGeneralLaw) <| by
    simp [directBasis]

private theorem derivesSortBothEmpty (x y : Word Nat) :
    Derives directBasis (((x ++ y) ++ x) ++ y)
      (((x ++ y) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisSortBothEmpty
      (instantiateFourWords x x y y)
  simpa [xyxy, xyyx, w, instantiateFourWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

private theorem derivesSortInitialGapEmpty
    (x y t : Word Nat) :
    Derives directBasis ((((x ++ y) ++ t) ++ x) ++ y)
      ((((x ++ y) ++ t) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisSortInitialGapEmpty
      (instantiateFourWords x x y t)
  simpa [xytxy, xytyx, w, instantiateFourWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

private theorem derivesSortFinalGapEmpty
    (x h y : Word Nat) :
    Derives directBasis ((((x ++ h) ++ y) ++ x) ++ y)
      ((((x ++ h) ++ y) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisSortFinalGapEmpty
      (instantiateFourWords x h y y)
  simpa [xhyxy, xhyyx, w, instantiateFourWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

private theorem derivesSortGeneral
    (x h y t : Word Nat) :
    Derives directBasis (((((x ++ h) ++ y) ++ t) ++ x) ++ y)
      (((((x ++ h) ++ y) ++ t) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisSortGeneral (instantiateFourWords x h y t)
  simpa [xhytxy, xhytyx, w, instantiateFourWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

private abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives directBasis

private abbrev listWordOfCons :=
  S5_107.listWordOfCons

private theorem listDerivesSortBothEmpty
    (first second : Nat) :
    ListDerives [first, second, first, second]
      [first, second, second, first] := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := directBasis)
        (derivesSortBothEmpty
          (Word.singleton first) (Word.singleton second)))

private theorem listDerivesSortInitialGapEmpty
    (first second gapHead : Nat) (gapTail : List Nat) :
    ListDerives
      ([first, second] ++ (gapHead :: gapTail) ++ [first, second])
      ([first, second] ++ (gapHead :: gapTail) ++ [second, first]) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc, List.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := directBasis)
        (derivesSortInitialGapEmpty
          (Word.singleton first) (Word.singleton second)
          (listWordOfCons gapHead gapTail)))

private theorem listDerivesSortFinalGapEmpty
    (first gapHead second : Nat) (gapTail : List Nat) :
    ListDerives
      ([first] ++ (gapHead :: gapTail) ++ [second, first, second])
      ([first] ++ (gapHead :: gapTail) ++ [second, second, first]) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc, List.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := directBasis)
        (derivesSortFinalGapEmpty
          (Word.singleton first)
          (listWordOfCons gapHead gapTail)
          (Word.singleton second)))

private theorem listDerivesSortGeneral
    (first firstGapHead second secondGapHead : Nat)
    (firstGapTail secondGapTail : List Nat) :
    ListDerives
      ([first] ++ (firstGapHead :: firstGapTail) ++ [second] ++
        (secondGapHead :: secondGapTail) ++ [first, second])
      ([first] ++ (firstGapHead :: firstGapTail) ++ [second] ++
        (secondGapHead :: secondGapTail) ++ [second, first]) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc, List.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := directBasis)
        (derivesSortGeneral
          (Word.singleton first)
          (listWordOfCons firstGapHead firstGapTail)
          (Word.singleton second)
          (listWordOfCons secondGapHead secondGapTail)))

private theorem listDerivesSwapDisplayedSeconds
    (first second : Nat)
    (before firstGap secondGap after : List Nat) :
    ListDerives
      (before ++ [first] ++ firstGap ++ [second] ++ secondGap ++
        [first, second] ++ after)
      (before ++ [first] ++ firstGap ++ [second] ++ secondGap ++
        [second, first] ++ after) := by
  cases firstGap with
  | nil =>
      cases secondGap with
      | nil =>
          simpa [List.append_assoc] using
            S5_107.ListDerives.context before after
              (listDerivesSortBothEmpty first second)
      | cons secondGapHead secondGapTail =>
          simpa [List.append_assoc] using
            S5_107.ListDerives.context before after
              (listDerivesSortInitialGapEmpty
                first second secondGapHead secondGapTail)
  | cons firstGapHead firstGapTail =>
      cases secondGap with
      | nil =>
          simpa [List.append_assoc] using
            S5_107.ListDerives.context before after
              (listDerivesSortFinalGapEmpty
                first firstGapHead second firstGapTail)
      | cons secondGapHead secondGapTail =>
          simpa [List.append_assoc] using
            S5_107.ListDerives.context before after
              (listDerivesSortGeneral
                first firstGapHead second secondGapHead
                firstGapTail secondGapTail)

private theorem listDerivesSwapAfterSeen
    (stem suffix : List Nat) (left right : Nat)
    (leftSeen : left ∈ stem) (rightSeen : right ∈ stem) :
    ListDerives
      (stem ++ [left, right] ++ suffix)
      (stem ++ [right, left] ++ suffix) := by
  by_cases equal : left = right
  · subst right
    exact S5_107.ListDerives.refl _
  · obtain ⟨leftBefore, leftAfter, prefixSplit⟩ :=
      List.mem_iff_append.mp leftSeen
    have rightInSplit :
        right ∈ leftBefore ∨ right ∈ leftAfter := by
      rw [prefixSplit] at rightSeen
      have split := List.mem_append.mp rightSeen
      rcases split with beforeMember | afterMember
      · exact Or.inl beforeMember
      · rcases List.mem_cons.mp afterMember with atLeft | inAfter
        · exact (equal atLeft.symm).elim
        · exact Or.inr inAfter
    rcases rightInSplit with rightBefore | rightAfter
    · obtain ⟨before, middle, beforeSplit⟩ :=
        List.mem_iff_append.mp rightBefore
      have displayed :=
        listDerivesSwapDisplayedSeconds
          right left before middle leftAfter suffix
      simpa [prefixSplit, beforeSplit, List.append_assoc] using
        displayed.symm
    · obtain ⟨middle, tail, afterSplit⟩ :=
        List.mem_iff_append.mp rightAfter
      simpa [prefixSplit, afterSplit, List.append_assoc] using
        listDerivesSwapDisplayedSeconds
          left right leftBefore middle tail suffix

theorem listDerivesPermuteAfterSeen
    (stem suffix : List Nat) {source target : List Nat}
    (sourceSeen : ∀ letter, letter ∈ source → letter ∈ stem)
    (permutation : source.Perm target) :
    ListDerives
      (stem ++ source ++ suffix)
      (stem ++ target ++ suffix) := by
  induction permutation generalizing stem with
  | nil =>
      exact S5_107.ListDerives.refl _
  | cons head _ induction =>
      have derivation := induction (stem ++ [head]) (by
        intro letter member
        have inPrefix : letter ∈ stem :=
          sourceSeen letter (List.Mem.tail head member)
        exact List.mem_append.mpr (Or.inl inPrefix))
      simpa [List.append_assoc] using derivation
  | swap first second rest =>
      have firstSeen : first ∈ stem :=
        sourceSeen first (by simp)
      have secondSeen : second ∈ stem :=
        sourceSeen second (by simp)
      simpa [List.append_assoc] using
        listDerivesSwapAfterSeen
          stem (rest ++ suffix) second first secondSeen firstSeen
  | trans firstPermutation _ firstInduction secondInduction =>
      have firstDerivation := firstInduction stem sourceSeen
      have secondDerivation := secondInduction stem (by
        intro letter member
        exact sourceSeen letter
          ((firstPermutation.mem_iff).mpr member))
      exact firstDerivation.trans secondDerivation

/-! ## Parity-preserving multiplicity reduction -/

private theorem listDerivesGatherDisplayed
    (letter : Nat) (before firstGap secondGap after : List Nat) :
    ListDerives
      (before ++ [letter] ++ firstGap ++ [letter] ++ secondGap ++
        [letter] ++ after)
      (before ++ [letter] ++ firstGap ++ [letter, letter] ++
        secondGap ++ after) := by
  cases secondGap with
  | nil =>
      simpa [List.append_assoc] using
        (S5_107.ListDerives.refl (basis := directBasis)
          (before ++ [letter] ++ firstGap ++ [letter, letter] ++ after))
  | cons gapHead gapTail =>
      let gapWord := listWordOfCons gapHead gapTail
      cases firstGap with
      | nil =>
          have gathered :=
            S5_107.ListDerives.ofWord (basis := directBasis)
              (derivesGatherInitialGapEmpty
                (Word.singleton letter) gapWord)
          simpa [gapWord, listWordOfCons, Word.singleton,
            Word.append, Word.append_assoc, List.append_assoc] using
              S5_107.ListDerives.context before after gathered
      | cons firstHead firstTail =>
          let firstWord := listWordOfCons firstHead firstTail
          have gathered :=
            S5_107.ListDerives.ofWord (basis := directBasis)
              (derivesGatherGeneral
                (Word.singleton letter) firstWord gapWord)
          simpa [firstWord, gapWord, listWordOfCons, Word.singleton,
            Word.append, Word.append_assoc, List.append_assoc] using
              S5_107.ListDerives.context before after gathered

private theorem listDerivesContractDisplayedTriple
    (letter : Nat) (before firstGap after : List Nat) :
    ListDerives
      (before ++ [letter] ++ firstGap ++
        [letter, letter, letter] ++ after)
      (before ++ [letter] ++ firstGap ++ [letter] ++ after) := by
  cases firstGap with
  | nil =>
      have contracted :=
        S5_107.ListDerives.ofWord (basis := directBasis)
          (derivesFourToTwo (Word.singleton letter))
      simpa [listWordOfCons, Word.singleton, Word.append,
        Word.append_assoc, List.append_assoc] using
          S5_107.ListDerives.context before after contracted
  | cons gapHead gapTail =>
      let gapWord := listWordOfCons gapHead gapTail
      have contracted :=
        S5_107.ListDerives.ofWord (basis := directBasis)
          (derivesRightPeriodContraction
            (Word.singleton letter) gapWord)
      simpa [gapWord, listWordOfCons, Word.singleton, Word.append,
        Word.append_assoc, List.append_assoc] using
          S5_107.ListDerives.context before after contracted

/-- Delete the third and fourth displayed copies together. This is the
`p = 2` power/period replacement for the forbidden `x² = x³` cap. -/
theorem listDerivesDeleteThirdAndFourth
    (letter : Nat)
    (before firstGap secondGap thirdGap after : List Nat) :
    ListDerives
      (before ++ [letter] ++ firstGap ++ [letter] ++ secondGap ++
        [letter] ++ thirdGap ++ [letter] ++ after)
      (before ++ [letter] ++ firstGap ++ [letter] ++ secondGap ++
        thirdGap ++ after) := by
  have gatherFourth :=
    listDerivesGatherDisplayed letter before firstGap
      (secondGap ++ [letter] ++ thirdGap) after
  have gatherThird :=
    listDerivesGatherDisplayed letter before firstGap
      ([letter] ++ secondGap) (thirdGap ++ after)
  have contract :=
    listDerivesContractDisplayedTriple letter before firstGap
      (secondGap ++ thirdGap ++ after)
  have first :
      ListDerives
        (before ++ [letter] ++ firstGap ++ [letter] ++ secondGap ++
          [letter] ++ thirdGap ++ [letter] ++ after)
        (before ++ [letter] ++ firstGap ++ [letter, letter] ++
          secondGap ++ [letter] ++ thirdGap ++ after) := by
    simpa [List.append_assoc] using gatherFourth
  have second :
      ListDerives
        (before ++ [letter] ++ firstGap ++ [letter, letter] ++
          secondGap ++ [letter] ++ thirdGap ++ after)
        (before ++ [letter] ++ firstGap ++
          [letter, letter, letter] ++ secondGap ++ thirdGap ++ after) := by
    simpa [List.append_assoc] using gatherThird
  have third :
      ListDerives
        (before ++ [letter] ++ firstGap ++
          [letter, letter, letter] ++ secondGap ++ thirdGap ++ after)
        (before ++ [letter] ++ firstGap ++ [letter] ++ secondGap ++
          thirdGap ++ after) := by
    simpa [List.append_assoc] using contract
  exact first.trans (second.trans third)

private theorem exists_two_occurrence_split_of_count_ge_two
    (letter : Nat) :
    ∀ {letters : List Nat},
      2 ≤ letters.count letter →
        ∃ before middle after,
          letters = before ++ letter :: middle ++ letter :: after
  | [], count => by
      simp at count
  | first :: rest, count => by
      by_cases equality : first = letter
      · subst first
        have restPositive : 0 < rest.count letter := by
          simp only [List.count_cons_self] at count
          omega
        have restMember : letter ∈ rest :=
          List.count_pos_iff.mp restPositive
        obtain ⟨middle, after, split⟩ :=
          List.mem_iff_append.mp restMember
        exact ⟨[], middle, after, by simp [split, List.append_assoc]⟩
      · have restCount : 2 ≤ rest.count letter := by
          simpa [equality] using count
        obtain ⟨before, middle, after, split⟩ :=
          exists_two_occurrence_split_of_count_ge_two
            letter restCount
        exact ⟨first :: before, middle, after,
          by simp [split, List.append_assoc]⟩

private theorem exists_three_occurrence_split_of_count_ge_three
    (letter : Nat) :
    ∀ {letters : List Nat},
      3 ≤ letters.count letter →
        ∃ before firstGap secondGap after,
          letters = before ++ letter :: firstGap ++ letter ::
            secondGap ++ letter :: after
  | [], count => by
      simp at count
  | first :: rest, count => by
      by_cases equality : first = letter
      · subst first
        have restCount : 2 ≤ rest.count letter := by
          simp only [List.count_cons_self] at count
          omega
        obtain ⟨firstGap, secondGap, after, split⟩ :=
          exists_two_occurrence_split_of_count_ge_two
            letter restCount
        exact ⟨[], firstGap, secondGap, after,
          by simp [split, List.append_assoc]⟩
      · have restCount : 3 ≤ rest.count letter := by
          simpa [equality] using count
        obtain ⟨before, firstGap, secondGap, after, split⟩ :=
          exists_three_occurrence_split_of_count_ge_three
            letter restCount
        exact ⟨first :: before, firstGap, secondGap, after,
          by simp [split, List.append_assoc]⟩

private theorem periodExponent_eq_self_of_le_three
    {n : Nat} (bound : n ≤ 3) :
    periodTwoFromTwoExponent n = n := by
  unfold periodTwoFromTwoExponent
  split <;> omega

private theorem periodExponent_add_two
    {n : Nat} (atLeastTwo : 2 ≤ n) :
    periodTwoFromTwoExponent (n + 2) =
      periodTwoFromTwoExponent n := by
  unfold periodTwoFromTwoExponent
  simp only [show ¬n + 2 < 2 by omega, show ¬n < 2 by omega,
    if_false]
  omega

private theorem existsPeriodReductionFrom :
    ∀ (remaining kept : List Nat),
      (∀ tested, kept.count tested ≤ 3) →
        ∃ reduced : List Nat,
          (∀ tested, reduced.count tested ≤ 3) ∧
          (∀ tested,
            periodTwoFromTwoExponent
                ((kept ++ remaining).count tested) =
              reduced.count tested) ∧
          ListDerives (kept ++ remaining) reduced
  | [], kept, keptBound => by
      refine ⟨kept, keptBound, ?_, ?_⟩
      · intro tested
        simpa using periodExponent_eq_self_of_le_three
          (keptBound tested)
      · simpa using S5_107.ListDerives.refl (basis := directBasis) kept
  | letter :: rest, kept, keptBound => by
      by_cases room : kept.count letter < 3
      · have nextBound :
            ∀ tested, (kept ++ [letter]).count tested ≤ 3 := by
          intro tested
          rw [List.count_append]
          by_cases equality : letter = tested
          · subst letter
            simp only [List.count_cons_self, List.count_nil]
            omega
          · have singletonZero : [letter].count tested = 0 := by
              simp [equality]
            rw [singletonZero, Nat.add_zero]
            exact keptBound tested
        obtain ⟨reduced, reducedBound, counts, derivation⟩ :=
          existsPeriodReductionFrom rest (kept ++ [letter]) nextBound
        refine ⟨reduced, reducedBound, ?_, ?_⟩
        · simpa [List.append_assoc] using counts
        · simpa [List.append_assoc] using derivation
      · have full : kept.count letter = 3 := by
          have bound := keptBound letter
          omega
        obtain ⟨before, firstGap, secondGap, after, split⟩ :=
          exists_three_occurrence_split_of_count_ge_three
            letter (letters := kept) (by omega)
        let nextKept :=
          before ++ [letter] ++ firstGap ++ [letter] ++
            secondGap ++ after
        have nextBound :
            ∀ tested, nextKept.count tested ≤ 3 := by
          intro tested
          by_cases equality : tested = letter
          · subst tested
            simp only [nextKept, List.count_append,
              List.count_cons_self, List.count_nil]
            have splitCount := congrArg (List.count letter) split
            simp only [List.count_append, List.count_cons_self] at splitCount
            omega
          · have countEq : nextKept.count tested = kept.count tested := by
              rw [split]
              simp [nextKept, List.count_append, equality,
                Ne.symm equality]
            rw [countEq]
            exact keptBound tested
        have stateCounts :
            ∀ tested,
              periodTwoFromTwoExponent
                  ((kept ++ letter :: rest).count tested) =
                periodTwoFromTwoExponent
                  ((nextKept ++ rest).count tested) := by
          intro tested
          by_cases equality : tested = letter
          · subst tested
            have splitCount := congrArg (List.count letter) split
            simp only [List.count_append, List.count_cons_self] at splitCount
            have sourceShape :
                (kept ++ letter :: rest).count letter =
                  (nextKept ++ rest).count letter + 2 := by
              simp only [List.count_append, List.count_cons_self,
                nextKept]
              simp only [List.count_append, List.count_cons_self,
                List.count_nil]
              omega
            rw [sourceShape]
            apply periodExponent_add_two
            rw [List.count_append]
            have nextLetterCount : nextKept.count letter = 2 := by
              simp only [nextKept, List.count_append,
                List.count_cons_self, List.count_nil]
              omega
            omega
          · have countEq :
                (kept ++ letter :: rest).count tested =
                  (nextKept ++ rest).count tested := by
              rw [split]
              simp [nextKept, List.count_append, equality,
                Ne.symm equality]
            rw [countEq]
        obtain ⟨reduced, reducedBound, counts, recurse⟩ :=
          existsPeriodReductionFrom rest nextKept nextBound
        have deletePair :
            ListDerives (kept ++ letter :: rest)
              (nextKept ++ rest) := by
          rw [split]
          simpa [nextKept, List.append_assoc] using
            listDerivesDeleteThirdAndFourth letter before firstGap
              secondGap after rest
        refine ⟨reduced, reducedBound, ?_, deletePair.trans recurse⟩
        intro tested
        exact (stateCounts tested).trans (counts tested)

theorem existsPeriodReduction (letters : List Nat) :
    ∃ reduced : List Nat,
      (∀ tested, reduced.count tested ≤ 3) ∧
      (∀ tested,
        periodTwoFromTwoExponent (letters.count tested) =
          reduced.count tested) ∧
      ListDerives letters reduced := by
  simpa using existsPeriodReductionFrom letters [] (by simp)

/-! ## Gap localization -/

private theorem perm_cons_to_end (letter : Nat) :
    ∀ letters : List Nat,
      (letter :: letters).Perm (letters ++ [letter])
  | [] => List.Perm.refl _
  | head :: tail =>
      (List.Perm.swap head letter tail).trans <|
        List.Perm.cons head (perm_cons_to_end letter tail)

private theorem listDerivesPullToSeconds
    (letter : Nat) (stemPrefix seconds between after : List Nat)
    (prefixMember : letter ∈ stemPrefix)
    (secondsMember : letter ∈ seconds)
    (secondsSeen :
      ∀ tested, tested ∈ seconds → tested ∈ stemPrefix) :
    ListDerives
      (stemPrefix ++ seconds ++ between ++ [letter] ++ after)
      (stemPrefix ++ (seconds ++ [letter]) ++ between ++ after) := by
  obtain ⟨prefixBefore, prefixAfter, prefixSplit⟩ :=
    List.mem_iff_append.mp prefixMember
  obtain ⟨secondsBefore, secondsAfter, secondsSplit⟩ :=
    List.mem_iff_append.mp secondsMember
  have gather :=
    listDerivesGatherDisplayed letter prefixBefore
      (prefixAfter ++ secondsBefore) (secondsAfter ++ between) after
  have gatheredShape :
      ListDerives
        (stemPrefix ++ seconds ++ between ++ [letter] ++ after)
        (stemPrefix ++
          (secondsBefore ++ [letter, letter] ++ secondsAfter) ++
          between ++ after) := by
    simpa [prefixSplit, secondsSplit, List.append_assoc] using gather
  have secondsPermutation :
      (secondsBefore ++ [letter, letter] ++ secondsAfter).Perm
        (seconds ++ [letter]) := by
    rw [secondsSplit]
    simpa [List.append_assoc] using
      List.Perm.append_left secondsBefore <|
        List.Perm.cons letter (perm_cons_to_end letter secondsAfter)
  have allSeen :
      ∀ tested,
        tested ∈ secondsBefore ++ [letter, letter] ++ secondsAfter →
          tested ∈ stemPrefix := by
    intro tested member
    apply secondsSeen tested
    rw [secondsSplit]
    simpa [List.append_assoc] using member
  have sorted :=
    listDerivesPermuteAfterSeen stemPrefix (between ++ after)
      allSeen secondsPermutation
  exact gatheredShape.trans <| by
    simpa [List.append_assoc] using sorted

private theorem listDerivesPartitionSelected :
    ∀ (stemPrefix selected seconds rejected remaining : List Nat),
      (∀ tested, tested ∈ selected → tested ∈ stemPrefix) →
      (∀ tested, tested ∈ seconds ↔ tested ∈ selected) →
      ListDerives
        (stemPrefix ++ seconds ++ rejected ++ remaining)
        (stemPrefix ++
          (seconds ++ remaining.filter (fun tested =>
            decide (tested ∈ selected))) ++
          (rejected ++ remaining.filter (fun tested =>
            !decide (tested ∈ selected))))
  | stemPrefix, selected, seconds, rejected, [], _, _ => by
      simpa [List.append_assoc] using
        (S5_107.ListDerives.refl (basis := directBasis)
          (stemPrefix ++ seconds ++ rejected))
  | stemPrefix, selected, seconds, rejected, letter :: rest,
      selectedSeen, secondsSupport => by
      by_cases selectedMember : (letter ∈ selected)
      · have prefixMember : letter ∈ stemPrefix :=
          selectedSeen letter selectedMember
        have secondsMember : letter ∈ seconds :=
          (secondsSupport letter).mpr selectedMember
        have secondsSeen :
            ∀ tested, tested ∈ seconds → tested ∈ stemPrefix := by
          intro tested member
          exact selectedSeen tested ((secondsSupport tested).mp member)
        have pull :=
          listDerivesPullToSeconds letter stemPrefix seconds rejected rest
            prefixMember secondsMember secondsSeen
        have nextSupport :
            ∀ tested,
              tested ∈ seconds ++ [letter] ↔ tested ∈ selected := by
          intro tested
          simp only [List.mem_append, List.mem_singleton]
          constructor
          · rintro (inSeconds | atLetter)
            · exact (secondsSupport tested).mp inSeconds
            · subst tested
              exact selectedMember
          · intro inSelected
            exact Or.inl ((secondsSupport tested).mpr inSelected)
        have recurse :=
          listDerivesPartitionSelected stemPrefix selected
            (seconds ++ [letter]) rejected rest
            selectedSeen nextSupport
        have pullShape :
            ListDerives
              (stemPrefix ++ seconds ++ rejected ++ letter :: rest)
              (stemPrefix ++ (seconds ++ [letter]) ++ rejected ++ rest) := by
          simpa [List.append_assoc] using pull
        have combined := pullShape.trans recurse
        simpa [selectedMember, List.append_assoc] using combined
      · have recurse :=
          listDerivesPartitionSelected stemPrefix selected seconds
            (rejected ++ [letter]) rest selectedSeen secondsSupport
        simpa [selectedMember, List.append_assoc] using recurse

private abbrev GapBlock := S5_870.FirstOccurrenceGapBlock

private def filterBlockSeconds
    (selected : List Nat) (block : GapBlock) : GapBlock where
  marker := block.marker
  seconds := block.seconds.filter (fun tested =>
    !decide (tested ∈ selected))

private def filterGapBlockSeconds
    (selected : List Nat) : List GapBlock → List GapBlock
  | [] => []
  | block :: rest =>
      filterBlockSeconds selected block ::
        filterGapBlockSeconds selected rest

@[simp]
private theorem length_filterGapBlockSeconds
    (selected : List Nat) (blocks : List GapBlock) :
    (filterGapBlockSeconds selected blocks).length = blocks.length := by
  induction blocks with
  | nil => rfl
  | cons block rest induction =>
      simp [filterGapBlockSeconds, induction]

@[simp]
private theorem filterBlockSeconds_marker
    (selected : List Nat) (block : GapBlock) :
    (filterBlockSeconds selected block).marker = block.marker := rfl

@[simp]
private theorem filterBlockSeconds_seconds
    (selected : List Nat) (block : GapBlock) :
    (filterBlockSeconds selected block).seconds =
      block.seconds.filter (fun tested =>
        !decide (tested ∈ selected)) := rfl

private theorem filterGapBlockSeconds_wellFormed
    {seen : List Nat} {blocks : List GapBlock}
    (formed : S5_870.GapBlocksWellFormed seen blocks)
    (selected : List Nat) :
    S5_870.GapBlocksWellFormed seen
      (filterGapBlockSeconds selected blocks) := by
  induction formed with
  | nil =>
      exact S5_870.GapBlocksWellFormed.nil _
  | cons seen block rest markerFresh secondsSeen tail induction =>
      exact S5_870.GapBlocksWellFormed.cons seen
        (filterBlockSeconds selected block)
        (filterGapBlockSeconds selected rest)
        (by simpa using markerFresh)
        (by
          intro tested member
          exact secondsSeen tested (List.mem_filter.mp member).1)
        induction

private theorem gapBlockMarkers_filterGapBlockSeconds
    (selected : List Nat) (blocks : List GapBlock) :
    S5_870.gapBlockMarkers (filterGapBlockSeconds selected blocks) =
      S5_870.gapBlockMarkers blocks := by
  induction blocks with
  | nil => rfl
  | cons block rest induction =>
      simpa only [filterGapBlockSeconds, S5_870.gapBlockMarkers,
        List.map_cons, filterBlockSeconds_marker] using
          congrArg (List.cons block.marker) induction

private theorem gapBlockSeconds_filterGapBlockSeconds
    (selected : List Nat) (blocks : List GapBlock) :
    S5_870.gapBlockSeconds (filterGapBlockSeconds selected blocks) =
      (S5_870.gapBlockSeconds blocks).filter (fun tested =>
        !decide (tested ∈ selected)) := by
  induction blocks with
  | nil => rfl
  | cons block rest induction =>
      simpa only [filterGapBlockSeconds, S5_870.gapBlockSeconds,
        List.flatMap_cons, filterBlockSeconds_seconds,
        List.filter_append] using
          congrArg
            (List.append
              (block.seconds.filter (fun tested =>
                !decide (tested ∈ selected)))) induction

private theorem filter_renderGapBlocks_selected
    {seen selected : List Nat} {blocks : List GapBlock}
    (formed : S5_870.GapBlocksWellFormed seen blocks)
    (selectedSeen :
      ∀ tested, tested ∈ selected → tested ∈ seen) :
    (S5_870.renderGapBlocks blocks).filter (fun tested =>
        decide (tested ∈ selected)) =
      (S5_870.gapBlockSeconds blocks).filter (fun tested =>
        decide (tested ∈ selected)) := by
  induction formed with
  | nil => rfl
  | cons seen block rest markerFresh secondsSeen tail induction =>
      have markerAbsent : block.marker ∉ selected := by
        intro member
        exact markerFresh (selectedSeen block.marker member)
      have nextSelectedSeen :
          ∀ tested, tested ∈ selected →
            tested ∈ block.marker :: seen := by
        intro tested member
        exact List.Mem.tail block.marker (selectedSeen tested member)
      simp [S5_870.renderGapBlocks, S5_870.gapBlockSeconds,
        markerAbsent, List.filter_append,
        induction nextSelectedSeen]

private theorem filter_renderGapBlocks_unselected
    {seen selected : List Nat} {blocks : List GapBlock}
    (formed : S5_870.GapBlocksWellFormed seen blocks)
    (selectedSeen :
      ∀ tested, tested ∈ selected → tested ∈ seen) :
    (S5_870.renderGapBlocks blocks).filter (fun tested =>
        !decide (tested ∈ selected)) =
      S5_870.renderGapBlocks (filterGapBlockSeconds selected blocks) := by
  induction formed with
  | nil => rfl
  | cons seen block rest markerFresh secondsSeen tail induction =>
      have markerAbsent : block.marker ∉ selected := by
        intro member
        exact markerFresh (selectedSeen block.marker member)
      have nextSelectedSeen :
          ∀ tested, tested ∈ selected →
            tested ∈ block.marker :: seen := by
        intro tested member
        exact List.Mem.tail block.marker (selectedSeen tested member)
      simp [S5_870.renderGapBlocks, filterGapBlockSeconds,
        markerAbsent, List.filter_append,
        induction nextSelectedSeen]

private def sortSeconds (seconds : List Nat) : List Nat :=
  seconds.mergeSort (fun left right : Nat => decide (left ≤ right))

private theorem sortSeconds_perm (seconds : List Nat) :
    (sortSeconds seconds).Perm seconds := by
  exact List.mergeSort_perm _ _

private theorem sortSeconds_pairwise (seconds : List Nat) :
    (sortSeconds seconds).Pairwise (· ≤ ·) := by
  have transitive :
      ∀ left middle right : Nat,
        decide (left ≤ middle) = true →
        decide (middle ≤ right) = true →
        decide (left ≤ right) = true := by
    intro left middle right first second
    exact decide_eq_true <|
      Nat.le_trans (of_decide_eq_true first) (of_decide_eq_true second)
  have total :
      ∀ left right : Nat,
        (decide (left ≤ right) || decide (right ≤ left)) = true := by
    intro left right
    rcases Nat.le_total left right with first | second
    · simp [first]
    · simp [second]
  exact (List.pairwise_mergeSort transitive total seconds).imp
    (fun relation => of_decide_eq_true relation)

inductive CanonicalGapBlocks : List GapBlock → Prop
  | nil : CanonicalGapBlocks []
  | cons {block : GapBlock} {rest : List GapBlock}
      (sorted : block.seconds.Pairwise (· ≤ ·))
      (localized :
        ∀ tested, tested ∈ block.seconds →
          tested ∉ S5_870.gapBlockSeconds rest)
      (tail : CanonicalGapBlocks rest) :
      CanonicalGapBlocks (block :: rest)

private theorem perm_filter_partition
    (selected : List Nat) :
    ∀ remaining : List Nat,
      remaining.Perm
        (remaining.filter (fun tested => decide (tested ∈ selected)) ++
          remaining.filter (fun tested => !decide (tested ∈ selected)))
  | [] => List.Perm.refl _
  | letter :: rest => by
      by_cases member : letter ∈ selected
      · simpa [member] using
          List.Perm.cons letter (perm_filter_partition selected rest)
      · have first :=
          List.Perm.cons letter (perm_filter_partition selected rest)
        have move :
            (letter ::
              (rest.filter (fun tested => decide (tested ∈ selected)) ++
                rest.filter (fun tested =>
                  !decide (tested ∈ selected)))).Perm
              (rest.filter (fun tested => decide (tested ∈ selected)) ++
                letter :: rest.filter (fun tested =>
                  !decide (tested ∈ selected))) := by
          simpa [List.append_assoc] using
            List.Perm.append_right
              (rest.filter (fun tested =>
                !decide (tested ∈ selected)))
              (perm_cons_to_end letter <|
                rest.filter (fun tested =>
                  decide (tested ∈ selected)))
        simpa [member, List.append_assoc] using first.trans move

private theorem mem_renderGapBlocks_of_mem_seconds
    {tested : Nat} {blocks : List GapBlock}
    (member : tested ∈ S5_870.gapBlockSeconds blocks) :
    tested ∈ S5_870.renderGapBlocks blocks := by
  induction blocks with
  | nil => simp [S5_870.gapBlockSeconds] at member
  | cons block rest induction =>
      simp only [S5_870.gapBlockSeconds, List.flatMap_cons,
        List.mem_append] at member
      simp only [S5_870.renderGapBlocks, List.mem_cons,
        List.mem_append]
      rcases member with current | later
      · exact Or.inr (Or.inl current)
      · exact Or.inr (Or.inr (induction later))

private theorem normalizeGapBlocks :
    ∀ (seen stem : List Nat) (blocks : List GapBlock),
      S5_870.GapBlocksWellFormed seen blocks →
      (∀ tested, tested ∈ seen → tested ∈ stem) →
      ∃ normalized : List GapBlock,
        S5_870.GapBlocksWellFormed seen normalized ∧
        CanonicalGapBlocks normalized ∧
        ListDerives
          (stem ++ S5_870.renderGapBlocks blocks)
          (stem ++ S5_870.renderGapBlocks normalized) ∧
        (S5_870.renderGapBlocks blocks).Perm
          (S5_870.renderGapBlocks normalized)
  | seen, stem, [], formed, seenInStem => by
      refine ⟨[], formed, CanonicalGapBlocks.nil, ?_, List.Perm.refl []⟩
      simpa [S5_870.renderGapBlocks] using
        (S5_107.ListDerives.refl (basis := directBasis) stem)
  | seen, stem, block :: rest, formed, seenInStem => by
      cases formed with
      | cons _ _ _ markerFresh secondsSeen tailFormed =>
          let stemPrefix := stem ++ [block.marker]
          let pulled :=
            (S5_870.gapBlockSeconds rest).filter (fun tested =>
              decide (tested ∈ block.seconds))
          let localizedSeconds := block.seconds ++ pulled
          let remainingBlocks :=
            filterGapBlockSeconds block.seconds rest
          let sortedSeconds := sortSeconds localizedSeconds
          have selectedSeen :
              ∀ tested, tested ∈ block.seconds →
                tested ∈ block.marker :: seen := secondsSeen
          have selectedSeenPrefix :
              ∀ tested, tested ∈ block.seconds →
                tested ∈ stemPrefix := by
            intro tested member
            rcases List.mem_cons.mp (secondsSeen tested member) with
              atMarker | inSeen
            · subst tested
              simp [stemPrefix]
            · exact List.mem_append.mpr <| Or.inl <|
                seenInStem tested inSeen
          have selectedFilter :=
            filter_renderGapBlocks_selected tailFormed selectedSeen
          have unselectedFilter :=
            filter_renderGapBlocks_unselected tailFormed selectedSeen
          have partitionRaw :=
            listDerivesPartitionSelected stemPrefix block.seconds
              block.seconds [] (S5_870.renderGapBlocks rest)
              selectedSeenPrefix (by simp)
          have partition :
              ListDerives
                (stemPrefix ++ block.seconds ++
                  S5_870.renderGapBlocks rest)
                (stemPrefix ++ localizedSeconds ++
                  S5_870.renderGapBlocks remainingBlocks) := by
            rw [selectedFilter, unselectedFilter] at partitionRaw
            simpa [pulled, localizedSeconds, remainingBlocks,
              List.append_assoc] using partitionRaw
          have localizedSeen :
              ∀ tested, tested ∈ localizedSeconds →
                tested ∈ stemPrefix := by
            intro tested member
            rcases List.mem_append.mp member with original | inPulled
            · exact selectedSeenPrefix tested original
            · exact selectedSeenPrefix tested <|
                of_decide_eq_true (List.mem_filter.mp inPulled).2
          have sortDerivation :
              ListDerives
                (stemPrefix ++ localizedSeconds ++
                  S5_870.renderGapBlocks remainingBlocks)
                (stemPrefix ++ sortedSeconds ++
                  S5_870.renderGapBlocks remainingBlocks) := by
            exact listDerivesPermuteAfterSeen stemPrefix
              (S5_870.renderGapBlocks remainingBlocks)
              localizedSeen (sortSeconds_perm localizedSeconds).symm
          have remainingFormed :
              S5_870.GapBlocksWellFormed
                (block.marker :: seen) remainingBlocks := by
            exact filterGapBlockSeconds_wellFormed tailFormed _
          have nextSeenInStem :
              ∀ tested, tested ∈ block.marker :: seen →
                tested ∈ stemPrefix ++ sortedSeconds := by
            intro tested member
            rcases List.mem_cons.mp member with atMarker | inSeen
            · subst tested
              exact List.mem_append.mpr <| Or.inl <| by simp [stemPrefix]
            · exact List.mem_append.mpr <| Or.inl <|
                List.mem_append.mpr <| Or.inl <|
                  seenInStem tested inSeen
          obtain ⟨normalizedRest, normalizedFormed,
              normalizedCanonical, recurse, restPermutation⟩ :=
            normalizeGapBlocks (block.marker :: seen)
              (stemPrefix ++ sortedSeconds) remainingBlocks
              remainingFormed nextSeenInStem
          let normalizedBlock : GapBlock :=
            { marker := block.marker, seconds := sortedSeconds }
          have sortedPairwise :
              sortedSeconds.Pairwise (· ≤ ·) :=
            sortSeconds_pairwise localizedSeconds
          have sortedSelected :
              ∀ tested, tested ∈ sortedSeconds →
                tested ∈ block.seconds := by
            intro tested member
            have inLocalized : tested ∈ localizedSeconds :=
              ((sortSeconds_perm localizedSeconds).mem_iff).mp member
            rcases List.mem_append.mp inLocalized with original | inPulled
            · exact original
            · exact of_decide_eq_true (List.mem_filter.mp inPulled).2
          have remainingExcludes :
              ∀ tested, tested ∈ block.seconds →
                tested ∉ S5_870.renderGapBlocks remainingBlocks := by
            intro tested selectedMember renderedMember
            have filteredMember :
                tested ∈
                  (S5_870.renderGapBlocks rest).filter (fun value =>
                    !decide (value ∈ block.seconds)) := by
              rw [unselectedFilter]
              exact renderedMember
            have absent : tested ∉ block.seconds := by
              simpa using (List.mem_filter.mp filteredMember).2
            exact absent selectedMember
          have localized :
              ∀ tested, tested ∈ sortedSeconds →
                tested ∉ S5_870.gapBlockSeconds normalizedRest := by
            intro tested sortedMember normalizedMember
            have targetRendered :=
              mem_renderGapBlocks_of_mem_seconds normalizedMember
            have sourceRendered :
                tested ∈ S5_870.renderGapBlocks remainingBlocks :=
              restPermutation.mem_iff.mpr targetRendered
            exact remainingExcludes tested
              (sortedSelected tested sortedMember) sourceRendered
          have normalizedTail :
              S5_870.GapBlocksWellFormed
                (normalizedBlock.marker :: seen) normalizedRest := by
            simpa [normalizedBlock] using normalizedFormed
          have normalizedWellFormed :
              S5_870.GapBlocksWellFormed seen
                (normalizedBlock :: normalizedRest) :=
            S5_870.GapBlocksWellFormed.cons seen normalizedBlock
              normalizedRest (by simpa [normalizedBlock] using markerFresh)
              (by
                intro tested member
                exact selectedSeen tested <|
                  sortedSelected tested <| by
                    simpa [normalizedBlock] using member)
              normalizedTail
          have normalizedBlocksCanonical :
              CanonicalGapBlocks (normalizedBlock :: normalizedRest) :=
            CanonicalGapBlocks.cons
              (by simpa [normalizedBlock] using sortedPairwise)
              (by
                intro tested member
                exact localized tested <| by
                  simpa [normalizedBlock] using member)
              normalizedCanonical
          have fullDerivation :
              ListDerives
                (stem ++ S5_870.renderGapBlocks (block :: rest))
                (stem ++ S5_870.renderGapBlocks
                  (normalizedBlock :: normalizedRest)) := by
            have recurseShape :
                ListDerives
                  (stemPrefix ++ sortedSeconds ++
                    S5_870.renderGapBlocks remainingBlocks)
                  (stemPrefix ++ sortedSeconds ++
                    S5_870.renderGapBlocks normalizedRest) := by
              simpa [List.append_assoc] using recurse
            simpa [stemPrefix, normalizedBlock, S5_870.renderGapBlocks,
              List.append_assoc] using
                partition.trans (sortDerivation.trans recurseShape)
          have restPartition :=
            perm_filter_partition block.seconds
              (S5_870.renderGapBlocks rest)
          rw [selectedFilter, unselectedFilter] at restPartition
          have partitionPermutation :
              (S5_870.renderGapBlocks (block :: rest)).Perm
                (block.marker ::
                  (localizedSeconds ++
                    S5_870.renderGapBlocks remainingBlocks)) := by
            have withSeconds :=
              List.Perm.append_left block.seconds restPartition
            exact List.Perm.cons block.marker <| by
              simpa [pulled, localizedSeconds, remainingBlocks,
                List.append_assoc] using withSeconds
          have sortedPermutation :
              (block.marker ::
                (localizedSeconds ++
                  S5_870.renderGapBlocks remainingBlocks)).Perm
                (block.marker ::
                  (sortedSeconds ++
                    S5_870.renderGapBlocks remainingBlocks)) :=
            List.Perm.cons block.marker <|
              List.Perm.append_right
                (S5_870.renderGapBlocks remainingBlocks)
                (sortSeconds_perm localizedSeconds).symm
          have recursePermutation :
              (block.marker ::
                (sortedSeconds ++
                  S5_870.renderGapBlocks remainingBlocks)).Perm
                (S5_870.renderGapBlocks
                  (normalizedBlock :: normalizedRest)) := by
            simpa [normalizedBlock, S5_870.renderGapBlocks] using
              List.Perm.cons block.marker <|
                List.Perm.append_left sortedSeconds restPermutation
          exact ⟨normalizedBlock :: normalizedRest,
            normalizedWellFormed, normalizedBlocksCanonical,
            fullDerivation,
            partitionPermutation.trans <|
              sortedPermutation.trans recursePermutation⟩
termination_by _ _ blocks _ _ => blocks.length
decreasing_by
  simp

/-! ## Canonical block comparison -/

private theorem takeSeen_append_of_all_mem (seen : List Nat) :
    ∀ (seconds suffix : List Nat),
      (∀ tested, tested ∈ seconds → tested ∈ seen) →
        S5_870.takeSeen seen (seconds ++ suffix) =
          seconds ++ S5_870.takeSeen seen suffix
  | [], _, _ => rfl
  | letter :: rest, suffix, allSeen => by
      have letterSeen : letter ∈ seen :=
        allSeen letter (List.Mem.head rest)
      have restSeen :
          ∀ tested, tested ∈ rest → tested ∈ seen := by
        intro tested member
        exact allSeen tested (List.Mem.tail letter member)
      simp [S5_870.takeSeen, letterSeen,
        takeSeen_append_of_all_mem seen rest suffix restSeen]

private theorem takeSeen_renderGapBlocks_eq_nil
    {seen : List Nat} {blocks : List GapBlock}
    (formed : S5_870.GapBlocksWellFormed seen blocks) :
    S5_870.takeSeen seen (S5_870.renderGapBlocks blocks) = [] := by
  cases formed with
  | nil => rfl
  | cons seen block rest markerFresh secondsSeen tail =>
      simp [S5_870.renderGapBlocks, S5_870.takeSeen, markerFresh]

private theorem takeSeen_append_renderGapBlocks
    {seen seconds : List Nat} {blocks : List GapBlock}
    (secondsSeen : ∀ tested, tested ∈ seconds → tested ∈ seen)
    (formed : S5_870.GapBlocksWellFormed seen blocks) :
    S5_870.takeSeen seen
        (seconds ++ S5_870.renderGapBlocks blocks) =
      seconds := by
  rw [takeSeen_append_of_all_mem seen seconds
    (S5_870.renderGapBlocks blocks) secondsSeen]
  rw [takeSeen_renderGapBlocks_eq_nil formed]
  simp

private theorem wellFormed_render_injective
    {seen : List Nat} {left : List GapBlock}
    (leftFormed : S5_870.GapBlocksWellFormed seen left) :
    ∀ {right : List GapBlock},
      S5_870.GapBlocksWellFormed seen right →
      S5_870.renderGapBlocks left = S5_870.renderGapBlocks right →
        left = right := by
  induction leftFormed with
  | nil =>
      intro right rightFormed rendered
      cases right with
      | nil => rfl
      | cons block rest =>
          simp [S5_870.renderGapBlocks] at rendered
  | cons seen leftBlock leftRest leftFresh leftSeen leftTail induction =>
      intro right rightFormed rendered
      cases right with
      | nil =>
          simp [S5_870.renderGapBlocks] at rendered
      | cons rightBlock rightRest =>
          cases rightFormed with
          | cons _ _ _ rightFresh rightSeen rightTail =>
              simp only [S5_870.renderGapBlocks] at rendered
              injection rendered with markerEq tailsEq
              have rightTailNormalized :
                  S5_870.GapBlocksWellFormed
                    (leftBlock.marker :: seen) rightRest := by
                simpa [markerEq] using rightTail
              have rightSeenNormalized :
                  ∀ tested, tested ∈ rightBlock.seconds →
                    tested ∈ leftBlock.marker :: seen := by
                simpa [markerEq] using rightSeen
              have secondsEq :
                  leftBlock.seconds = rightBlock.seconds := by
                have taken := congrArg
                  (S5_870.takeSeen (leftBlock.marker :: seen)) tailsEq
                rw [takeSeen_append_renderGapBlocks leftSeen leftTail,
                  takeSeen_append_renderGapBlocks rightSeenNormalized
                    rightTailNormalized] at taken
                exact taken
              have restRendered :
                  S5_870.renderGapBlocks leftRest =
                    S5_870.renderGapBlocks rightRest := by
                rw [secondsEq] at tailsEq
                exact List.append_cancel_left tailsEq
              have restEq : leftRest = rightRest :=
                induction rightTailNormalized restRendered
              have blockEq : leftBlock = rightBlock := by
                cases leftBlock with
                | mk leftMarker leftSeconds =>
                    cases rightBlock with
                    | mk rightMarker rightSeconds =>
                        simp only [S5_870.FirstOccurrenceGapBlock.marker]
                          at markerEq
                        simp only [S5_870.FirstOccurrenceGapBlock.seconds]
                          at secondsEq
                        subst rightMarker
                        subst rightSeconds
                        rfl
              subst rightBlock
              subst rightRest
              rfl

private theorem gapBlocksList_render_eq
    {blocks : List GapBlock}
    (formed : S5_870.GapBlocksWellFormed [] blocks) :
    S5_870.gapBlocksList (S5_870.renderGapBlocks blocks) = blocks := by
  apply wellFormed_render_injective
    (S5_870.gapBlocksList_wellFormed
      (S5_870.renderGapBlocks blocks)) formed
  exact S5_870.render_gapBlocksList _

private theorem pointwise_of_map_eq
    {alpha beta : Type} (left right : alpha → beta) :
    ∀ {keys : List alpha},
      keys.map left = keys.map right →
        ∀ key, key ∈ keys → left key = right key
  | [], _, _, member => by simp at member
  | head :: tail, equality, key, member => by
      simp only [List.map_cons] at equality
      injection equality with headEq tailEq
      rcases List.mem_cons.mp member with atHead | inTail
      · simpa [atHead] using headEq
      · exact pointwise_of_map_eq left right tailEq key inTail

private theorem correspondingCanonicalGapBlocksOfData
    {seen : List Nat} {left : List GapBlock}
    (leftFormed : S5_870.GapBlocksWellFormed seen left) :
    ∀ {right : List GapBlock},
      S5_870.GapBlocksWellFormed seen right →
      CanonicalGapBlocks left →
      CanonicalGapBlocks right →
      S5_870.gapBlockMarkers left = S5_870.gapBlockMarkers right →
      (∀ tested,
        (S5_870.renderGapBlocks left).count tested =
          (S5_870.renderGapBlocks right).count tested) →
      (∀ selected,
        selected ∈ seen ∨ selected ∈ S5_870.gapBlockMarkers left →
          S5_870.blockSecondGapAux selected seen left =
            S5_870.blockSecondGapAux selected seen right) →
      S5_870.CorrespondingGapBlocks left right := by
  induction leftFormed with
  | nil =>
      intro right rightFormed leftCanonical rightCanonical markers counts gaps
      cases right with
      | nil => exact S5_870.CorrespondingGapBlocks.nil
      | cons block rest =>
          simp [S5_870.gapBlockMarkers] at markers
  | cons seen leftBlock leftRest leftFresh leftSeen leftTail induction =>
      intro right rightFormed leftCanonical rightCanonical markers counts gaps
      cases right with
      | nil =>
          simp [S5_870.gapBlockMarkers] at markers
      | cons rightBlock rightRest =>
          cases rightFormed with
          | cons _ _ _ rightFresh rightSeen rightTail =>
              cases leftCanonical with
              | cons leftSorted leftLocalized leftCanonicalTail =>
                cases rightCanonical with
                | cons rightSorted rightLocalized rightCanonicalTail =>
                  simp only [S5_870.gapBlockMarkers, List.map_cons] at markers
                  injection markers with markerEq tailMarkers
                  have rightTailNormalized :
                      S5_870.GapBlocksWellFormed
                        (leftBlock.marker :: seen) rightRest := by
                    simpa [markerEq] using rightTail
                  have currentMembers :
                      ∀ selected,
                        selected ∈ leftBlock.seconds ↔
                          selected ∈ rightBlock.seconds := by
                    intro selected
                    constructor
                    · intro member
                      have known := leftSeen selected member
                      have gapEq := gaps selected <| by
                        rcases List.mem_cons.mp known with atMarker | inSeen
                        · exact Or.inr <| by
                            simp [S5_870.gapBlockMarkers, atMarker, markerEq]
                        · exact Or.inl inSeen
                      have sourceGap :=
                        (S5_870.blockSecondGapAux_eq_current_iff
                          selected seen leftBlock leftRest).2 member
                      have targetGap :
                          S5_870.blockSecondGapAux selected seen
                              (rightBlock :: rightRest) =
                            some (rightBlock.marker :: seen).length := by
                        calc
                          S5_870.blockSecondGapAux selected seen
                              (rightBlock :: rightRest) =
                              S5_870.blockSecondGapAux selected seen
                                (leftBlock :: leftRest) := gapEq.symm
                          _ = some (leftBlock.marker :: seen).length :=
                            sourceGap
                          _ = some (rightBlock.marker :: seen).length := by
                            simp [markerEq]
                      exact
                        (S5_870.blockSecondGapAux_eq_current_iff
                          selected seen rightBlock rightRest).1 targetGap
                    · intro member
                      have known := rightSeen selected member
                      have gapEq := gaps selected <| by
                        rcases List.mem_cons.mp known with atMarker | inSeen
                        · exact Or.inr <| by
                            simp [S5_870.gapBlockMarkers, atMarker, markerEq]
                        · exact Or.inl inSeen
                      have targetGap :=
                        (S5_870.blockSecondGapAux_eq_current_iff
                          selected seen rightBlock rightRest).2 member
                      have sourceGap :
                          S5_870.blockSecondGapAux selected seen
                              (leftBlock :: leftRest) =
                            some (leftBlock.marker :: seen).length := by
                        calc
                          S5_870.blockSecondGapAux selected seen
                              (leftBlock :: leftRest) =
                              S5_870.blockSecondGapAux selected seen
                                (rightBlock :: rightRest) := gapEq
                          _ = some (rightBlock.marker :: seen).length :=
                            targetGap
                          _ = some (leftBlock.marker :: seen).length := by
                            simp [markerEq]
                      exact
                        (S5_870.blockSecondGapAux_eq_current_iff
                          selected seen leftBlock leftRest).1 sourceGap
                  have currentPermutation :
                      leftBlock.seconds.Perm rightBlock.seconds := by
                    rw [List.perm_iff_count]
                    intro selected
                    by_cases leftMember : selected ∈ leftBlock.seconds
                    · have rightMember : selected ∈ rightBlock.seconds :=
                        (currentMembers selected).1 leftMember
                      have leftRestAbsent :
                          selected ∉ S5_870.gapBlockSeconds leftRest :=
                        leftLocalized selected leftMember
                      have rightRestAbsent :
                          selected ∉ S5_870.gapBlockSeconds rightRest :=
                        rightLocalized selected rightMember
                      have markerCounts :
                          (S5_870.gapBlockMarkers
                              (leftBlock :: leftRest)).count selected =
                            (S5_870.gapBlockMarkers
                              (rightBlock :: rightRest)).count selected := by
                        simp [S5_870.gapBlockMarkers, markerEq, tailMarkers]
                      have total := counts selected
                      rw [S5_870.count_renderGapBlocks,
                        S5_870.count_renderGapBlocks] at total
                      change
                        (S5_870.gapBlockMarkers
                              (leftBlock :: leftRest)).count selected +
                            (leftBlock.seconds ++
                              S5_870.gapBlockSeconds leftRest).count selected =
                          (S5_870.gapBlockMarkers
                              (rightBlock :: rightRest)).count selected +
                            (rightBlock.seconds ++
                              S5_870.gapBlockSeconds rightRest).count selected
                        at total
                      rw [List.count_append, List.count_append] at total
                      rw [List.count_eq_zero.mpr leftRestAbsent,
                        List.count_eq_zero.mpr rightRestAbsent] at total
                      omega
                    · have rightAbsent : selected ∉ rightBlock.seconds := by
                        intro member
                        exact leftMember ((currentMembers selected).2 member)
                      exact (List.count_eq_zero.mpr leftMember).trans
                        (List.count_eq_zero.mpr rightAbsent).symm
                  have restCounts :
                      ∀ tested,
                        (S5_870.renderGapBlocks leftRest).count tested =
                          (S5_870.renderGapBlocks rightRest).count tested := by
                    intro tested
                    have total := counts tested
                    have currentCount :=
                      (List.perm_iff_count.mp currentPermutation) tested
                    simp only [S5_870.renderGapBlocks, List.count_cons,
                      List.count_append] at total
                    rw [markerEq, currentCount] at total
                    omega
                  have restGaps :
                      ∀ selected,
                        selected ∈ leftBlock.marker :: seen ∨
                            selected ∈ S5_870.gapBlockMarkers leftRest →
                          S5_870.blockSecondGapAux selected
                              (leftBlock.marker :: seen) leftRest =
                            S5_870.blockSecondGapAux selected
                              (leftBlock.marker :: seen) rightRest := by
                    intro selected relevant
                    by_cases current : selected ∈ leftBlock.seconds
                    · have targetCurrent : selected ∈ rightBlock.seconds :=
                        (currentMembers selected).1 current
                      rw [S5_870.blockSecondGapAux_eq_none_of_not_mem_seconds
                          selected (leftBlock.marker :: seen) leftRest
                          (leftLocalized selected current),
                        S5_870.blockSecondGapAux_eq_none_of_not_mem_seconds
                          selected (leftBlock.marker :: seen) rightRest
                          (rightLocalized selected targetCurrent)]
                    · have targetCurrent : selected ∉ rightBlock.seconds := by
                        intro member
                        exact current ((currentMembers selected).2 member)
                      have fullRelevant :
                          selected ∈ seen ∨
                            selected ∈ S5_870.gapBlockMarkers
                              (leftBlock :: leftRest) := by
                        rcases relevant with inNextSeen | inRestMarkers
                        · rcases List.mem_cons.mp inNextSeen with
                            atMarker | inSeen
                          · exact Or.inr <| by
                              simp [S5_870.gapBlockMarkers, atMarker]
                          · exact Or.inl inSeen
                        · exact Or.inr <| by
                            change selected ∈
                              leftBlock.marker ::
                                S5_870.gapBlockMarkers leftRest
                            exact List.Mem.tail leftBlock.marker inRestMarkers
                      have full := gaps selected fullRelevant
                      simp only [S5_870.blockSecondGapAux, current,
                        targetCurrent, if_false] at full
                      rw [← markerEq] at full
                      exact full
                  exact S5_870.CorrespondingGapBlocks.cons markerEq
                    currentPermutation
                    (induction rightTailNormalized leftCanonicalTail
                      rightCanonicalTail tailMarkers restCounts restGaps)

private theorem correspondingCanonicalGapBlocksOfSameData
    {left right : List GapBlock}
    (leftFormed : S5_870.GapBlocksWellFormed [] left)
    (rightFormed : S5_870.GapBlocksWellFormed [] right)
    (leftCanonical : CanonicalGapBlocks left)
    (rightCanonical : CanonicalGapBlocks right)
    (counts : ∀ tested,
      (S5_870.renderGapBlocks left).count tested =
        (S5_870.renderGapBlocks right).count tested)
    (same :
      S5_870.gapSignatureList (S5_870.renderGapBlocks left) =
        S5_870.gapSignatureList (S5_870.renderGapBlocks right)) :
    S5_870.CorrespondingGapBlocks left right := by
  have firsts :
      S5_870.firstOccurrenceSequenceList
          (S5_870.renderGapBlocks left) =
        S5_870.firstOccurrenceSequenceList
          (S5_870.renderGapBlocks right) := by
    simpa [S5_870.gapSignatureList] using
      congrArg S5_870.GapSignature.firstOccurrences same
  have leftParsed := gapBlocksList_render_eq leftFormed
  have rightParsed := gapBlocksList_render_eq rightFormed
  have leftMarkers :
      S5_870.gapBlockMarkers left =
        S5_870.firstOccurrenceSequenceList
          (S5_870.renderGapBlocks left) := by
    rw [← S5_870.gapBlockMarkers_gapBlocksList]
    rw [leftParsed]
  have rightMarkers :
      S5_870.gapBlockMarkers right =
        S5_870.firstOccurrenceSequenceList
          (S5_870.renderGapBlocks right) := by
    rw [← S5_870.gapBlockMarkers_gapBlocksList]
    rw [rightParsed]
  have markers :
      S5_870.gapBlockMarkers left =
        S5_870.gapBlockMarkers right :=
    leftMarkers.trans (firsts.trans rightMarkers.symm)
  have secondGaps :
      S5_870.secondOccurrenceGapsList
          (S5_870.renderGapBlocks left) =
        S5_870.secondOccurrenceGapsList
          (S5_870.renderGapBlocks right) := by
    simpa [S5_870.gapSignatureList] using
      congrArg S5_870.GapSignature.secondOccurrenceGaps same
  have mappedGaps :
      (S5_870.firstOccurrenceSequenceList
          (S5_870.renderGapBlocks left)).map
          (S5_870.secondOccurrenceGapList
            (S5_870.renderGapBlocks left)) =
        (S5_870.firstOccurrenceSequenceList
          (S5_870.renderGapBlocks left)).map
          (S5_870.secondOccurrenceGapList
            (S5_870.renderGapBlocks right)) := by
    unfold S5_870.secondOccurrenceGapsList at secondGaps
    rw [← firsts] at secondGaps
    exact secondGaps
  have gapEq :
      ∀ selected,
        selected ∈ S5_870.gapBlockMarkers left →
          S5_870.blockSecondGapAux selected [] left =
            S5_870.blockSecondGapAux selected [] right := by
    intro selected member
    have inFirsts :
        selected ∈ S5_870.firstOccurrenceSequenceList
          (S5_870.renderGapBlocks left) := by
      rw [← leftMarkers]
      exact member
    have pointwise := pointwise_of_map_eq
      (S5_870.secondOccurrenceGapList
        (S5_870.renderGapBlocks left))
      (S5_870.secondOccurrenceGapList
        (S5_870.renderGapBlocks right))
      mappedGaps selected inFirsts
    rw [S5_870.secondOccurrenceGapList_eq_blockSecondGapAux,
      S5_870.secondOccurrenceGapList_eq_blockSecondGapAux,
      leftParsed, rightParsed] at pointwise
    exact pointwise
  apply correspondingCanonicalGapBlocksOfData leftFormed rightFormed
    leftCanonical rightCanonical markers counts
  intro selected relevant
  exact gapEq selected (relevant.resolve_left (by simp))

private theorem listDerivesCorrespondingGapBlocks
    {seen : List Nat} {left right : List GapBlock}
    (corresponding : S5_870.CorrespondingGapBlocks left right)
    (formed : S5_870.GapBlocksWellFormed seen left)
    (stem : List Nat)
    (seenInStem : ∀ tested, tested ∈ seen → tested ∈ stem) :
    ListDerives
      (stem ++ S5_870.renderGapBlocks left)
      (stem ++ S5_870.renderGapBlocks right) := by
  induction corresponding generalizing seen stem with
  | nil =>
      simpa [S5_870.renderGapBlocks] using
        (S5_107.ListDerives.refl (basis := directBasis) stem)
  | @cons leftBlock rightBlock leftRest rightRest
      markerEq secondsPermutation restCorrespondence induction =>
      cases formed with
      | cons _ _ _ markerFresh secondsSeen tailFormed =>
          have sourceSeen :
              ∀ tested, tested ∈ leftBlock.seconds →
                tested ∈ stem ++ [leftBlock.marker] := by
            intro tested member
            have known := secondsSeen tested member
            rcases List.mem_cons.mp known with atMarker | inSeen
            · subst tested
              simp
            · exact List.mem_append.mpr
                (Or.inl (seenInStem tested inSeen))
          have move := listDerivesPermuteAfterSeen
            (stem ++ [leftBlock.marker])
            (S5_870.renderGapBlocks leftRest)
            sourceSeen secondsPermutation
          have nextSeenInStem :
              ∀ tested, tested ∈ leftBlock.marker :: seen →
                tested ∈ stem ++ [leftBlock.marker] ++
                  rightBlock.seconds := by
            intro tested member
            rcases List.mem_cons.mp member with atMarker | inSeen
            · subst tested
              simp
            · exact List.mem_append.mpr <| Or.inl <|
                List.mem_append.mpr <| Or.inl <|
                  seenInStem tested inSeen
          have recurse := induction tailFormed
            (stem ++ [leftBlock.marker] ++ rightBlock.seconds)
            nextSeenInStem
          simpa [S5_870.renderGapBlocks, markerEq,
            List.append_assoc] using move.trans recurse

/-! ## Lee-Li Proposition 6.1 and the factor intersection -/

private theorem periodExponentEqOfCappedAndParity
    {left right : Nat}
    (capped : min left 2 = min right 2)
    (parity : left % 2 = right % 2) :
    periodTwoFromTwoExponent left =
      periodTwoFromTwoExponent right := by
  by_cases leftSmall : left < 2
  · have leftMin : min left 2 = left :=
      Nat.min_eq_left (by omega)
    have rightSmall : right < 2 := by
      by_cases small : right < 2
      · exact small
      · have rightMin : min right 2 = 2 :=
          Nat.min_eq_right (by omega)
        rw [leftMin, rightMin] at capped
        omega
    have rightMin : min right 2 = right :=
      Nat.min_eq_left (by omega)
    have equal : left = right := by
      rw [leftMin, rightMin] at capped
      exact capped
    subst right
    rfl
  · have leftLarge : 2 ≤ left := by omega
    have rightLarge : 2 ≤ right := by
      by_cases large : 2 ≤ right
      · exact large
      · have leftMin : min left 2 = 2 :=
          Nat.min_eq_right leftLarge
        have rightMin : min right 2 = right :=
          Nat.min_eq_left (by omega)
        rw [leftMin, rightMin] at capped
        omega
    unfold periodTwoFromTwoExponent
    rw [if_neg leftSmall, if_neg (by omega : ¬ right < 2), parity]

private theorem factorValid_periodExponentEq
    (identity : Identity Nat)
    (s5Valid : identity.SatisfiedBy S5_870.table.semigroup)
    (cyclicValid : identity.SatisfiedBy cyclicTwo.semigroup) :
    ∀ tested,
      periodTwoFromTwoExponent (identity.lhs.toList.count tested) =
        periodTwoFromTwoExponent (identity.rhs.toList.count tested) := by
  intro tested
  exact periodExponentEqOfCappedAndParity
    (S5_870.valid_capped_count_eq identity s5Valid tested)
    (cyclicValid_parity_eq identity cyclicValid tested)

private theorem gapSignatureListEqOfListDerives
    {left right : List Nat} (derivation : ListDerives left right) :
    S5_870.gapSignatureList left =
      S5_870.gapSignatureList right := by
  cases derivation with
  | empty => rfl
  | @words leftHead rightHead leftTail rightTail wordDerivation =>
      have valid :
          (⟨S5_107.listWordOfCons leftHead leftTail,
            S5_107.listWordOfCons rightHead rightTail⟩ :
              Identity Nat).SatisfiedBy S5_870.table.semigroup := by
        intro valuation
        exact Derives.sound s5Models wordDerivation valuation
      simpa [S5_870.gapSignature] using
        S5_870.tableGapSignatureSeparation.separate
          ⟨S5_107.listWordOfCons leftHead leftTail,
            S5_107.listWordOfCons rightHead rightTail⟩ valid

private theorem derivesOfFactorValid
    (identity : Identity Nat)
    (s5Valid : identity.SatisfiedBy S5_870.table.semigroup)
    (cyclicValid : identity.SatisfiedBy cyclicTwo.semigroup) :
    Derives directBasis identity.lhs identity.rhs := by
  obtain ⟨leftReduced, leftBound, leftCounts, leftReduction⟩ :=
    existsPeriodReduction identity.lhs.toList
  obtain ⟨rightReduced, rightBound, rightCounts, rightReduction⟩ :=
    existsPeriodReduction identity.rhs.toList
  have exponentEq :=
    factorValid_periodExponentEq identity s5Valid cyclicValid
  have reducedCounts :
      ∀ tested, leftReduced.count tested = rightReduced.count tested := by
    intro tested
    calc
      leftReduced.count tested =
          periodTwoFromTwoExponent
            (identity.lhs.toList.count tested) := (leftCounts tested).symm
      _ = periodTwoFromTwoExponent
            (identity.rhs.toList.count tested) := exponentEq tested
      _ = rightReduced.count tested := rightCounts tested
  have originalSignature :
      S5_870.gapSignatureList identity.lhs.toList =
        S5_870.gapSignatureList identity.rhs.toList := by
    simpa [S5_870.gapSignature] using
      S5_870.tableGapSignatureSeparation.separate identity s5Valid
  have reducedSignature :
      S5_870.gapSignatureList leftReduced =
        S5_870.gapSignatureList rightReduced := by
    calc
      S5_870.gapSignatureList leftReduced =
          S5_870.gapSignatureList identity.lhs.toList :=
        (gapSignatureListEqOfListDerives leftReduction).symm
      _ = S5_870.gapSignatureList identity.rhs.toList :=
        originalSignature
      _ = S5_870.gapSignatureList rightReduced :=
        gapSignatureListEqOfListDerives rightReduction
  obtain ⟨leftBlocks, leftFormed, leftCanonical,
      leftBlockDerivation, leftBlockPermutation⟩ :=
    normalizeGapBlocks [] [] (S5_870.gapBlocksList leftReduced)
      (S5_870.gapBlocksList_wellFormed leftReduced) (by simp)
  obtain ⟨rightBlocks, rightFormed, rightCanonical,
      rightBlockDerivation, rightBlockPermutation⟩ :=
    normalizeGapBlocks [] [] (S5_870.gapBlocksList rightReduced)
      (S5_870.gapBlocksList_wellFormed rightReduced) (by simp)
  have leftNormalization :
      ListDerives leftReduced (S5_870.renderGapBlocks leftBlocks) := by
    simpa [S5_870.render_gapBlocksList] using leftBlockDerivation
  have rightNormalization :
      ListDerives rightReduced (S5_870.renderGapBlocks rightBlocks) := by
    simpa [S5_870.render_gapBlocksList] using rightBlockDerivation
  have leftPermutation :
      leftReduced.Perm (S5_870.renderGapBlocks leftBlocks) := by
    simpa [S5_870.render_gapBlocksList] using leftBlockPermutation
  have rightPermutation :
      rightReduced.Perm (S5_870.renderGapBlocks rightBlocks) := by
    simpa [S5_870.render_gapBlocksList] using rightBlockPermutation
  have normalizedCounts :
      ∀ tested,
        (S5_870.renderGapBlocks leftBlocks).count tested =
          (S5_870.renderGapBlocks rightBlocks).count tested := by
    intro tested
    calc
      (S5_870.renderGapBlocks leftBlocks).count tested =
          leftReduced.count tested :=
        ((List.perm_iff_count.mp leftPermutation) tested).symm
      _ = rightReduced.count tested := reducedCounts tested
      _ = (S5_870.renderGapBlocks rightBlocks).count tested :=
        (List.perm_iff_count.mp rightPermutation) tested
  have normalizedSignature :
      S5_870.gapSignatureList (S5_870.renderGapBlocks leftBlocks) =
        S5_870.gapSignatureList
          (S5_870.renderGapBlocks rightBlocks) := by
    calc
      S5_870.gapSignatureList (S5_870.renderGapBlocks leftBlocks) =
          S5_870.gapSignatureList leftReduced :=
        (gapSignatureListEqOfListDerives leftNormalization).symm
      _ = S5_870.gapSignatureList rightReduced := reducedSignature
      _ = S5_870.gapSignatureList
          (S5_870.renderGapBlocks rightBlocks) :=
        gapSignatureListEqOfListDerives rightNormalization
  have corresponding := correspondingCanonicalGapBlocksOfSameData
    leftFormed rightFormed leftCanonical rightCanonical
    normalizedCounts normalizedSignature
  have middle :
      ListDerives (S5_870.renderGapBlocks leftBlocks)
        (S5_870.renderGapBlocks rightBlocks) := by
    simpa using listDerivesCorrespondingGapBlocks
      corresponding leftFormed [] (by simp)
  have full :
      ListDerives identity.lhs.toList identity.rhs.toList :=
    leftReduction.trans <| leftNormalization.trans <|
      middle.trans <| rightNormalization.symm.trans rightReduction.symm
  cases identity with
  | mk left right =>
      cases left with
      | mk leftHead leftTail =>
          cases right with
          | mk rightHead rightTail =>
              simpa [S5_107.listWordOfCons] using
                S5_107.ListDerives.toWord full

private def intersectionBasis :
    IntersectionBasis S5_870.table.semigroup cyclicTwo.semigroup
      directBasis where
  leftModels := s5Models
  rightModels := cyclicModels
  complete := derivesOfFactorValid

private theorem directLeeLiCondition8JoinBasisFor :
    BasisFor directJoinSemigroup directBasis :=
  IntersectionBasis.basisFor intersectionBasis directJoinPair

/-- Unconditional basis theorem for the ten-element Condition 8 factor join.
This source theorem alone closes none of the nine recorded order-six roots. -/
theorem leeLiCondition8JoinBasisFor :
    BasisFor joinSemigroup basis := by
  simpa [joinSemigroup, basis] using
    directLeeLiCondition8JoinBasisFor.oppositeReversed

end SemigroupBasis.CoRoots.Order6LeeLiCondition8Join
