import SemigroupBasis.CoRoots.S5_870Family
import SemigroupBasis.CoRoots.S5_345Factors
import SemigroupBasis.Examples.FinalMarkerThree
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SemigroupBasis.CoRoots.Order6LeeZhangClass356

open SemigroupBasis
open SemigroupBasis.Examples

def boundedClassIndex : Nat := 356

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

/-! ## The seven ordinary identities in Lee--Zhang Condition 20 -/

def xxx : Word Nat := w 0 [0, 0]
def xx : Word Nat := w 0 [0]
def xhxx : Word Nat := w 0 [2, 0, 0]
def xhx : Word Nat := w 0 [2, 0]
def xxhxk : Word Nat := w 0 [0, 2, 0, 3]
def xxhk : Word Nat := w 0 [0, 2, 3]
def xyxy : Word Nat := w 0 [1, 0, 1]
def xyyx : Word Nat := w 0 [1, 1, 0]
def xykxy : Word Nat := w 0 [1, 3, 0, 1]
def xykyx : Word Nat := w 0 [1, 3, 1, 0]
def xhyxy : Word Nat := w 0 [2, 1, 0, 1]
def xhyyx : Word Nat := w 0 [2, 1, 1, 0]
def xhykxy : Word Nat := w 0 [2, 1, 3, 0, 1]
def xhykyx : Word Nat := w 0 [2, 1, 3, 1, 0]

def powerLaw : Identity Nat := ⟨xxx, xx⟩
def finalCapLaw : Identity Nat := ⟨xhxx, xhx⟩
def retainedCapLaw : Identity Nat := ⟨xxhxk, xxhk⟩
def sortBothEmptyLaw : Identity Nat := ⟨xyxy, xyyx⟩
def sortFirstGapEmptyLaw : Identity Nat := ⟨xykxy, xykyx⟩
def sortSecondGapEmptyLaw : Identity Nat := ⟨xhyxy, xhyyx⟩
def sortGeneralLaw : Identity Nat := ⟨xhykxy, xhykyx⟩

/-- The direct orientation of Lee--Zhang (10.1). -/
def directBasis : List (Identity Nat) :=
  [powerLaw, finalCapLaw, retainedCapLaw, sortGeneralLaw,
    sortSecondGapEmptyLaw, sortFirstGapEmptyLaw, sortBothEmptyLaw]

/-- The authenticated i94 orientation:
`xxx=xx`, `xxhx=xhx`, `kxhxx=khxx`, and the four reversed sorting laws. -/
def basis : List (Identity Nat) :=
  reversedBasis directBasis

theorem basis_is_authenticated_orientation :
    basis =
      [⟨w 0 [0, 0], w 0 [0]⟩,
       ⟨w 0 [0, 2, 0], w 0 [2, 0]⟩,
       ⟨w 3 [0, 2, 0, 0], w 3 [2, 0, 0]⟩,
       ⟨w 1 [0, 3, 1, 2, 0], w 0 [1, 3, 1, 2, 0]⟩,
       ⟨w 1 [0, 1, 2, 0], w 0 [1, 1, 2, 0]⟩,
       ⟨w 1 [0, 3, 1, 0], w 0 [1, 3, 1, 0]⟩,
       ⟨w 1 [0, 1, 0], w 0 [1, 1, 0]⟩] := by
  decide

private def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

def finiteBasis : List (Identity (Fin 4)) :=
  basis.map fun identity => identity.map toFinFour

private theorem basis_roundTrip_checked :
    basis.all (fun identity =>
      decide ((identity.map toFinFour).map Fin.val = identity)) = true := by
  decide

private theorem basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ basis) :
    (identity.map toFinFour).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basis_roundTrip_checked) identity member

/-- Exhaustive checks on the four displayed variables lift to `Nat`. -/
theorem models_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteBasis.all candidate.checkIdentity = true) :
    Models candidate.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinFour ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityNat_sound (identity.map toFinFour)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [basis_roundTrip identity member] at finiteValid
  exact finiteValid

/-! ## Primitive direct-orientation deductions -/

private def instantiateFourWords
    (x y h k : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | 2 => h
  | 3 => k
  | n + 4 => Word.singleton (n + 4)

private theorem basisPower : Derives directBasis xxx xx :=
  Derives.fromBasis (e := powerLaw) (by simp [directBasis])

private theorem basisFinalCap : Derives directBasis xhxx xhx :=
  Derives.fromBasis (e := finalCapLaw) (by simp [directBasis])

private theorem basisRetainedCap : Derives directBasis xxhxk xxhk :=
  Derives.fromBasis (e := retainedCapLaw) (by simp [directBasis])

private theorem basisSortBothEmpty : Derives directBasis xyxy xyyx :=
  Derives.fromBasis (e := sortBothEmptyLaw) (by simp [directBasis])

private theorem basisSortFirstGapEmpty : Derives directBasis xykxy xykyx :=
  Derives.fromBasis (e := sortFirstGapEmptyLaw) (by simp [directBasis])

private theorem basisSortSecondGapEmpty : Derives directBasis xhyxy xhyyx :=
  Derives.fromBasis (e := sortSecondGapEmptyLaw) (by simp [directBasis])

private theorem basisSortGeneral : Derives directBasis xhykxy xhykyx :=
  Derives.fromBasis (e := sortGeneralLaw) (by simp [directBasis])

theorem derivesPower (x : Word Nat) :
    Derives directBasis ((x ++ x) ++ x) (x ++ x) := by
  have substituted :=
    Derives.subst basisPower (instantiateFourWords x x x x)
  simpa [xxx, xx, w, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesFinalCap (x h : Word Nat) :
    Derives directBasis (((x ++ h) ++ x) ++ x) ((x ++ h) ++ x) := by
  have substituted :=
    Derives.subst basisFinalCap (instantiateFourWords x x h x)
  simpa [xhxx, xhx, w, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesRetainedCap (x h k : Word Nat) :
    Derives directBasis ((((x ++ x) ++ h) ++ x) ++ k)
      (((x ++ x) ++ h) ++ k) := by
  have substituted :=
    Derives.subst basisRetainedCap (instantiateFourWords x x h k)
  simpa [xxhxk, xxhk, w, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesSortBothEmpty (x y : Word Nat) :
    Derives directBasis (((x ++ y) ++ x) ++ y)
      (((x ++ y) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisSortBothEmpty (instantiateFourWords x y x y)
  simpa [xyxy, xyyx, w, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesSortFirstGapEmpty (x y k : Word Nat) :
    Derives directBasis ((((x ++ y) ++ k) ++ x) ++ y)
      ((((x ++ y) ++ k) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisSortFirstGapEmpty (instantiateFourWords x y x k)
  simpa [xykxy, xykyx, w, instantiateFourWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesSortSecondGapEmpty (x h y : Word Nat) :
    Derives directBasis ((((x ++ h) ++ y) ++ x) ++ y)
      ((((x ++ h) ++ y) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisSortSecondGapEmpty (instantiateFourWords x y h y)
  simpa [xhyxy, xhyyx, w, instantiateFourWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesSortGeneral (x h y k : Word Nat) :
    Derives directBasis (((((x ++ h) ++ y) ++ k) ++ x) ++ y)
      (((((x ++ h) ++ y) ++ k) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisSortGeneral (instantiateFourWords x y h k)
  simpa [xhykxy, xhykyx, w, instantiateFourWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-! ## Replaying the sealed `S5_870` normalizer before a retained suffix -/

private theorem bind_append
    (left right : Word Nat) (sigma : Nat → Word Nat) :
    (left ++ right).bind sigma = left.bind sigma ++ right.bind sigma := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (word : Word Nat) (tau sigma : Nat → Word Nat) :
    (word.bind tau).bind sigma =
      word.bind (fun letter => (tau letter).bind sigma) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem derivesS5GeneralBeforeSuffix
    (x h t suffix : Word Nat) :
    Derives directBasis
      (((((x ++ h) ++ x) ++ t) ++ x) ++ suffix)
      ((((x ++ h) ++ x) ++ t) ++ suffix) := by
  have expand :=
    Derives.appendRight (derivesFinalCap x h).symm
      ((t ++ x) ++ suffix)
  have delete :=
    Derives.prepend (x ++ h) (derivesRetainedCap x t suffix)
  have contract :=
    Derives.appendRight (derivesFinalCap x h) (t ++ suffix)
  have expanded :
      Derives directBasis
        (x ++ (h ++ (x ++ (t ++ (x ++ suffix)))))
        (x ++ (h ++ (x ++ (x ++ (t ++ (x ++ suffix)))))) := by
    simpa only [Word.append_assoc] using expand
  have deleted :
      Derives directBasis
        (x ++ (h ++ (x ++ (x ++ (t ++ (x ++ suffix))))))
        (x ++ (h ++ (x ++ (x ++ (t ++ suffix))))) := by
    simpa only [Word.append_assoc] using delete
  have contracted :
      Derives directBasis
        (x ++ (h ++ (x ++ (x ++ (t ++ suffix)))))
        (x ++ (h ++ (x ++ (t ++ suffix)))) := by
    simpa only [Word.append_assoc] using contract
  simpa only [Word.append_assoc] using
    expanded.trans (deleted.trans contracted)

/-- Every derivation in the sealed `S5_870` basis remains derivable when it
is placed immediately before a fixed nonempty suffix.  The two cap laws that
need a right context use that suffix as Lee--Zhang's ordinary variable `k`.
The substitution parameter makes the statement closed under every constructor
of `Derives`. -/
theorem liftS5DerivationBeforeSuffix
    {left right : Word Nat}
    (derivation : Derives S5_870.basis left right)
    (suffix : Word Nat) (sigma : Nat → Word Nat) :
    Derives directBasis
      (left.bind sigma ++ suffix) (right.bind sigma ++ suffix) := by
  induction derivation generalizing suffix sigma with
  | fromBasis member =>
      simp only [S5_870.basis, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · change Derives directBasis
          (((sigma 0 ++ sigma 0) ++ sigma 0) ++ suffix)
          ((sigma 0 ++ sigma 0) ++ suffix)
        exact Derives.appendRight (derivesPower (sigma 0)) suffix
      · change Derives directBasis
          ((((sigma 0 ++ sigma 0) ++ sigma 3) ++ sigma 0) ++ suffix)
          (((sigma 0 ++ sigma 0) ++ sigma 3) ++ suffix)
        exact derivesRetainedCap (sigma 0) (sigma 3) suffix
      · change Derives directBasis
          ((((sigma 0 ++ sigma 1) ++ sigma 0) ++ sigma 0) ++ suffix)
          (((sigma 0 ++ sigma 1) ++ sigma 0) ++ suffix)
        exact Derives.appendRight
          (derivesFinalCap (sigma 0) (sigma 1)) suffix
      · change Derives directBasis
          (((((sigma 0 ++ sigma 1) ++ sigma 0) ++ sigma 3) ++
              sigma 0) ++ suffix)
          ((((sigma 0 ++ sigma 1) ++ sigma 0) ++ sigma 3) ++ suffix)
        exact derivesS5GeneralBeforeSuffix
          (sigma 0) (sigma 1) (sigma 3) suffix
      · change Derives directBasis
          ((((sigma 0 ++ sigma 2) ++ sigma 0) ++ sigma 2) ++ suffix)
          ((((sigma 0 ++ sigma 2) ++ sigma 2) ++ sigma 0) ++ suffix)
        exact Derives.appendRight
          (derivesSortBothEmpty (sigma 0) (sigma 2)) suffix
      · change Derives directBasis
          (((((sigma 0 ++ sigma 2) ++ sigma 3) ++ sigma 0) ++
              sigma 2) ++ suffix)
          (((((sigma 0 ++ sigma 2) ++ sigma 3) ++ sigma 2) ++
              sigma 0) ++ suffix)
        exact Derives.appendRight
          (derivesSortFirstGapEmpty (sigma 0) (sigma 2) (sigma 3))
          suffix
      · change Derives directBasis
          (((((sigma 0 ++ sigma 1) ++ sigma 2) ++ sigma 0) ++
              sigma 2) ++ suffix)
          (((((sigma 0 ++ sigma 1) ++ sigma 2) ++ sigma 2) ++
              sigma 0) ++ suffix)
        exact Derives.appendRight
          (derivesSortSecondGapEmpty (sigma 0) (sigma 1) (sigma 2))
          suffix
      · change Derives directBasis
          ((((((sigma 0 ++ sigma 1) ++ sigma 2) ++ sigma 3) ++
                sigma 0) ++ sigma 2) ++ suffix)
          ((((((sigma 0 ++ sigma 1) ++ sigma 2) ++ sigma 3) ++
                sigma 2) ++ sigma 0) ++ suffix)
        exact Derives.appendRight
          (derivesSortGeneral
            (sigma 0) (sigma 1) (sigma 2) (sigma 3)) suffix
  | refl =>
      exact Derives.refl _
  | symm _ induction =>
      exact (induction suffix sigma).symm
  | trans _ _ first second =>
      exact (first suffix sigma).trans (second suffix sigma)
  | prepend p _ ih =>
      simpa [bind_append, Word.append_assoc] using
        Derives.prepend (p.bind sigma) (ih suffix sigma)
  | appendRight _ q ih =>
      simpa [bind_append, Word.append_assoc] using
        ih (q.bind sigma ++ suffix) sigma
  | subst _ tau ih =>
      simpa [bind_bind] using
        ih suffix (fun letter => (tau letter).bind sigma)

/-! ## List-level boundary moves used in the nonsimple-final branch -/

private abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives directBasis

private abbrev listWordOfCons := S5_107.listWordOfCons

private theorem derives_of_listDerives_toList
    {sourceBasis : List (Identity Nat)} (left right : Word Nat)
    (derivation :
      S5_107.ListDerives sourceBasis left.toList right.toList) :
    Derives sourceBasis left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simpa [S5_107.listWordOfCons] using
            S5_107.ListDerives.toWord derivation

private theorem listDerivesPower (letter : Nat) :
    ListDerives [letter, letter, letter] [letter, letter] := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := directBasis)
        (derivesPower (Word.singleton letter)))

private theorem listDerivesFinalCap
    (letter gapHead : Nat) (gapTail : List Nat) :
    ListDerives
      ([letter] ++ (gapHead :: gapTail) ++ [letter, letter])
      ([letter] ++ (gapHead :: gapTail) ++ [letter]) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc, List.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := directBasis)
        (derivesFinalCap
          (Word.singleton letter) (listWordOfCons gapHead gapTail)))

/-- Duplicate the final letter when an earlier copy occurs in the prefix. -/
private theorem listDerivesDuplicateFinal
    (stem : List Nat) (final : Nat) (seen : final ∈ stem) :
    ListDerives (stem ++ [final]) (stem ++ [final, final]) := by
  obtain ⟨before, gap, shape⟩ := List.mem_iff_append.mp seen
  cases gap with
  | nil =>
      simpa [shape, List.append_assoc] using
        (listDerivesPower final).symm.prepend before
  | cons gapHead gapTail =>
      simpa [shape, List.append_assoc] using
        (listDerivesFinalCap final gapHead gapTail).symm.prepend before

private theorem listDerivesSortBothEmpty
    (first second : Nat) :
    ListDerives [first, second, first, second]
      [first, second, second, first] := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := directBasis)
        (derivesSortBothEmpty
          (Word.singleton first) (Word.singleton second)))

private theorem listDerivesSortFirstGapEmpty
    (first second gapHead : Nat) (gapTail : List Nat) :
    ListDerives
      ([first, second] ++ (gapHead :: gapTail) ++ [first, second])
      ([first, second] ++ (gapHead :: gapTail) ++ [second, first]) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc, List.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := directBasis)
        (derivesSortFirstGapEmpty
          (Word.singleton first) (Word.singleton second)
          (listWordOfCons gapHead gapTail)))

private theorem listDerivesSortSecondGapEmpty
    (first gapHead second : Nat) (gapTail : List Nat) :
    ListDerives
      ([first] ++ (gapHead :: gapTail) ++ [second, first, second])
      ([first] ++ (gapHead :: gapTail) ++ [second, second, first]) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc, List.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := directBasis)
        (derivesSortSecondGapEmpty
          (Word.singleton first) (listWordOfCons gapHead gapTail)
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
          (Word.singleton first) (listWordOfCons firstGapHead firstGapTail)
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
              (listDerivesSortFirstGapEmpty
                first second secondGapHead secondGapTail)
  | cons firstGapHead firstGapTail =>
      cases secondGap with
      | nil =>
          simpa [List.append_assoc] using
            S5_107.ListDerives.context before after
              (listDerivesSortSecondGapEmpty
                first firstGapHead second firstGapTail)
      | cons secondGapHead secondGapTail =>
          simpa [List.append_assoc] using
            S5_107.ListDerives.context before after
              (listDerivesSortGeneral first firstGapHead second
                secondGapHead firstGapTail secondGapTail)

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
    have rightInSplit : right ∈ leftBefore ∨ right ∈ leftAfter := by
      rw [prefixSplit] at rightSeen
      rcases List.mem_append.mp rightSeen with beforeMember | afterMember
      · exact Or.inl beforeMember
      · rcases List.mem_cons.mp afterMember with atLeft | inAfter
        · exact False.elim (equal atLeft.symm)
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

private theorem exists_two_occurrence_split
    (letter : Nat) :
    ∀ {letters : List Nat},
      2 ≤ letters.count letter →
        ∃ before middle after,
          letters = before ++ letter :: middle ++ letter :: after
  | [], enough => by simp at enough
  | head :: rest, enough => by
      by_cases equal : head = letter
      · subst head
        have positive : 0 < rest.count letter := by
          simp only [List.count_cons_self] at enough
          omega
        obtain ⟨middle, after, shape⟩ :=
          List.mem_iff_append.mp (List.count_pos_iff.mp positive)
        exact ⟨[], middle, after, by simp [shape, List.append_assoc]⟩
      · have restEnough : 2 ≤ rest.count letter := by
          simpa [List.count_cons_of_ne equal] using enough
        obtain ⟨before, middle, after, shape⟩ :=
          exists_two_occurrence_split letter restEnough
        exact ⟨head :: before, middle, after,
          by simp [shape, List.append_assoc]⟩

/-- In `S5_870`, a third occurrence can be appended after two displayed
occurrences. -/
private theorem s5DerivesAppendThird
    (word : Word Nat) (letter : Nat)
    (repeated : 2 ≤ word.toList.count letter) :
    Derives S5_870.basis word (word ++ Word.singleton letter) := by
  obtain ⟨before, middle, after, shape⟩ :=
    exists_two_occurrence_split letter repeated
  have listed :=
    S5_870.listDerivesDeleteThirdOccurrence
      letter before middle after []
  have wordDerivation :
      Derives S5_870.basis
        (word ++ Word.singleton letter) word := by
    apply derives_of_listDerives_toList
    simpa [shape, Word.toList_append, List.append_assoc] using listed
  exact wordDerivation.symm

/-! ## Prefix/final semantics -/

private theorem final_wordOfPrefixFinal
    (stem : List Nat) (final : Nat) :
    (wordOfPrefixFinal stem final).final = final := by
  induction stem with
  | nil => rfl
  | cons letter rest induction =>
      rw [wordOfPrefixFinal_cons, Word.final_append]
      exact induction

private theorem split_final_eq (word : Word Nat) :
    (splitPrefixFinal word).2 = word.final := by
  have reconstructed := congrArg Word.final (wordOfPrefixFinal_split word)
  rw [final_wordOfPrefixFinal] at reconstructed
  exact reconstructed

private theorem toList_eq_splitPrefixFinal (word : Word Nat) :
    word.toList =
      (splitPrefixFinal word).1 ++ [(splitPrefixFinal word).2] := by
  have reconstructed :=
    congrArg Word.toList (wordOfPrefixFinal_split word)
  rw [toList_wordOfPrefixFinal] at reconstructed
  exact reconstructed.symm

private theorem split_final_and_absent_of_simple
    {word : Word Nat} {final : Nat}
    (simple : S5_345.simpleFinalVariable word = some final) :
    (splitPrefixFinal word).2 = final ∧
      final ∉ (splitPrefixFinal word).1 := by
  have specification :=
    (S5_345.simpleFinalVariable_eq_some_iff word final).1 simple
  have finalEq : (splitPrefixFinal word).2 = final :=
    (split_final_eq word).trans specification.2
  have countOne := specification.1
  unfold S5_107.SimpleIn at countOne
  rw [toList_eq_splitPrefixFinal, finalEq, List.count_append] at countOne
  have prefixZero : (splitPrefixFinal word).1.count final = 0 := by
    simp only [List.count_singleton_self] at countOne
    omega
  exact ⟨finalEq, List.count_eq_zero.mp prefixZero⟩

private theorem split_final_mem_of_nonsimple
    (word : Word Nat)
    (nonsimple : S5_345.simpleFinalVariable word = none) :
    word.final ∈ (splitPrefixFinal word).1 := by
  have finalEq := split_final_eq word
  apply Decidable.byContradiction
  intro absent
  have countOne : word.toList.count word.final = 1 := by
    rw [toList_eq_splitPrefixFinal, finalEq, List.count_append]
    simp [List.count_eq_zero.mpr absent]
  have contradiction : False := by
    simpa [S5_345.simpleFinalVariable, countOne] using nonsimple
  exact contradiction.elim

private theorem jValid_simpleFinalVariable_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy finalMarkerThree.semigroup) :
    S5_345.simpleFinalVariable identity.lhs =
      S5_345.simpleFinalVariable identity.rhs :=
  S5_345Factors.finalMarkerThreeValid_simpleFinalVariable_eq identity valid

private theorem s5Valid_mem_iff
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy S5_870.table.semigroup)
    (letter : Nat) :
    letter ∈ identity.lhs.toList ↔ letter ∈ identity.rhs.toList := by
  rw [← List.count_pos_iff, ← List.count_pos_iff]
  have capped := S5_870.valid_capped_count_eq identity valid letter
  omega

private theorem s5RightIdentity (value : Fin 5) :
    S5_870.table.semigroup.mul value (3 : Fin 5) = value := by
  apply Fin.ext
  revert value
  decide

private theorem foldl_eval_congr
    (semigroup : Semigroup S)
    (leftValuation rightValuation : Nat → S) :
    ∀ (letters : List Nat) (initial : S),
      (∀ letter, letter ∈ letters →
        leftValuation letter = rightValuation letter) →
      letters.foldl
          (fun value letter =>
            semigroup.mul value (leftValuation letter)) initial =
        letters.foldl
          (fun value letter =>
            semigroup.mul value (rightValuation letter)) initial
  | [], _, _ => rfl
  | letter :: rest, initial, agree => by
      simp only [List.foldl_cons]
      rw [agree letter (List.Mem.head rest)]
      apply foldl_eval_congr semigroup
      intro tested member
      exact agree tested (List.Mem.tail letter member)

private theorem eval_congr_on_support
    (semigroup : Semigroup S)
    (leftValuation rightValuation : Nat → S)
    (word : Word Nat)
    (agree :
      ∀ letter, letter ∈ word.toList →
        leftValuation letter = rightValuation letter) :
    semigroup.eval leftValuation word =
      semigroup.eval rightValuation word := by
  cases word with
  | mk head tail =>
      simp only [Semigroup.eval]
      rw [agree head (by simp [Word.toList])]
      apply foldl_eval_congr semigroup
      intro letter member
      exact agree letter (List.Mem.tail head member)

/- Assigning the simple terminal variable to the identity of `S5_870`
erases it and exposes an identity between the two nonempty prefixes. -/
private theorem nonemptyPrefixIdentity_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy S5_870.table.semigroup)
    (final leftHead rightHead : Nat)
    (leftTail rightTail : List Nat)
    (leftShape : identity.lhs =
      listWordOfCons leftHead leftTail ++ Word.singleton final)
    (rightShape : identity.rhs =
      listWordOfCons rightHead rightTail ++ Word.singleton final)
    (leftAbsent : final ∉ leftHead :: leftTail)
    (rightAbsent : final ∉ rightHead :: rightTail) :
    (Identity.mk (listWordOfCons leftHead leftTail)
        (listWordOfCons rightHead rightTail)).SatisfiedBy
      S5_870.table.semigroup := by
  intro valuation
  let erased : Nat → Fin 5 := fun letter =>
    if letter = final then 3 else valuation letter
  have whole := valid erased
  rw [leftShape, rightShape, Semigroup.eval_append,
    Semigroup.eval_append] at whole
  simp only [Semigroup.eval_singleton] at whole
  have erasedFinal : erased final = (3 : Fin 5) := by
    simp [erased]
  rw [erasedFinal, s5RightIdentity, s5RightIdentity] at whole
  have leftEval :=
    eval_congr_on_support S5_870.table.semigroup erased valuation
      (listWordOfCons leftHead leftTail) (by
        intro letter member
        have different : letter ≠ final := by
          intro equal
          subst letter
          apply leftAbsent
          simpa [listWordOfCons, Word.toList] using member
        simp [erased, different])
  have rightEval :=
    eval_congr_on_support S5_870.table.semigroup erased valuation
      (listWordOfCons rightHead rightTail) (by
        intro letter member
        have different : letter ≠ final := by
          intro equal
          subst letter
          apply rightAbsent
          simpa [listWordOfCons, Word.toList] using member
        simp [erased, different])
  exact leftEval.symm.trans (whole.trans rightEval)

/-! ## Simple-final completeness -/

private theorem derives_of_factors_of_simpleFinal
    (identity : Identity Nat)
    (s5Valid : identity.SatisfiedBy S5_870.table.semigroup)
    (jValid : identity.SatisfiedBy finalMarkerThree.semigroup)
    {final : Nat}
    (leftSimple : S5_345.simpleFinalVariable identity.lhs = some final) :
    Derives directBasis identity.lhs identity.rhs := by
  have simpleEqual := jValid_simpleFinalVariable_eq identity jValid
  have rightSimple :
      S5_345.simpleFinalVariable identity.rhs = some final :=
    simpleEqual.symm.trans leftSimple
  obtain ⟨leftFinal, leftAbsent⟩ :=
    split_final_and_absent_of_simple leftSimple
  obtain ⟨rightFinal, rightAbsent⟩ :=
    split_final_and_absent_of_simple rightSimple
  let leftPrefix := (splitPrefixFinal identity.lhs).1
  let rightPrefix := (splitPrefixFinal identity.rhs).1
  have leftShapeList :
      identity.lhs.toList = leftPrefix ++ [final] := by
    simpa [leftPrefix, leftFinal] using
      toList_eq_splitPrefixFinal identity.lhs
  have rightShapeList :
      identity.rhs.toList = rightPrefix ++ [final] := by
    simpa [rightPrefix, rightFinal] using
      toList_eq_splitPrefixFinal identity.rhs
  have leftAbsent' : final ∉ leftPrefix := by
    simpa [leftPrefix] using leftAbsent
  have rightAbsent' : final ∉ rightPrefix := by
    simpa [rightPrefix] using rightAbsent
  cases leftPrefixEq : leftPrefix with
  | nil =>
      cases rightPrefixEq : rightPrefix with
      | nil =>
          have equalWords : identity.lhs = identity.rhs := by
            apply Word.toList_injective
            rw [leftShapeList, rightShapeList,
              leftPrefixEq, rightPrefixEq]
          rw [equalWords]
          exact Derives.refl _
      | cons rightHead rightTail =>
          have rightMember : rightHead ∈ identity.rhs.toList := by
            rw [rightShapeList, rightPrefixEq]
            simp
          have leftMember : rightHead ∈ identity.lhs.toList :=
            (s5Valid_mem_iff identity s5Valid rightHead).2 rightMember
          have equalFinal : rightHead = final := by
            rw [leftShapeList, leftPrefixEq] at leftMember
            simpa using leftMember
          have rightHeadInPrefix : rightHead ∈ rightPrefix := by
            rw [rightPrefixEq]
            exact List.Mem.head _
          exact (rightAbsent' (equalFinal ▸ rightHeadInPrefix)).elim
  | cons leftHead leftTail =>
      cases rightPrefixEq : rightPrefix with
      | nil =>
          have leftMember : leftHead ∈ identity.lhs.toList := by
            rw [leftShapeList, leftPrefixEq]
            simp
          have rightMember : leftHead ∈ identity.rhs.toList :=
            (s5Valid_mem_iff identity s5Valid leftHead).1 leftMember
          have equalFinal : leftHead = final := by
            rw [rightShapeList, rightPrefixEq] at rightMember
            simpa using rightMember
          have leftHeadInPrefix : leftHead ∈ leftPrefix := by
            rw [leftPrefixEq]
            exact List.Mem.head _
          exact (leftAbsent' (equalFinal ▸ leftHeadInPrefix)).elim
      | cons rightHead rightTail =>
          have leftShape : identity.lhs =
              listWordOfCons leftHead leftTail ++
                Word.singleton final := by
            apply Word.toList_injective
            simpa [leftPrefixEq, S5_107.listWordOfCons,
              Word.toList] using leftShapeList
          have rightShape : identity.rhs =
              listWordOfCons rightHead rightTail ++
                Word.singleton final := by
            apply Word.toList_injective
            simpa [rightPrefixEq, S5_107.listWordOfCons,
              Word.toList] using rightShapeList
          let prefixIdentity : Identity Nat :=
            ⟨listWordOfCons leftHead leftTail,
              listWordOfCons rightHead rightTail⟩
          have prefixValid :
              prefixIdentity.SatisfiedBy S5_870.table.semigroup := by
            exact nonemptyPrefixIdentity_valid identity s5Valid final
              leftHead rightHead leftTail rightTail leftShape rightShape
              (by simpa [leftPrefixEq] using leftAbsent')
              (by simpa [rightPrefixEq] using rightAbsent')
          have prefixDerivation :
              Derives S5_870.basis prefixIdentity.lhs prefixIdentity.rhs :=
            S5_870Family.S5_870.basisFor.2 prefixIdentity prefixValid
          have lifted :=
            liftS5DerivationBeforeSuffix prefixDerivation
              (Word.singleton final) Word.singleton
          rw [bind_singleton, bind_singleton] at lifted
          simpa [prefixIdentity, leftShape, rightShape] using lifted

/-! ## Nonsimple-final completeness (Lee--Zhang Lemma 10.6) -/

private def appendFreshIdentity
    (identity : Identity Nat) (fresh : Nat) : Identity Nat :=
  ⟨identity.lhs ++ Word.singleton fresh,
    identity.rhs ++ Word.singleton fresh⟩

private theorem appendFreshIdentity_valid
    {S : Type u} (semigroup : Semigroup S)
    (identity : Identity Nat) (fresh : Nat)
    (valid : identity.SatisfiedBy semigroup) :
    (appendFreshIdentity identity fresh).SatisfiedBy semigroup := by
  intro valuation
  simp only [appendFreshIdentity, Semigroup.eval_append,
    Semigroup.eval_singleton]
  rw [valid valuation]

private theorem appendFreshIdentity_left_simple
    (identity : Identity Nat) (fresh : Nat)
    (freshAbsent : fresh ∉ identity.lhs.toList) :
    S5_345.simpleFinalVariable
        (appendFreshIdentity identity fresh).lhs = some fresh := by
  apply (S5_345.simpleFinalVariable_eq_some_iff
    (appendFreshIdentity identity fresh).lhs fresh).2
  constructor
  · unfold S5_107.SimpleIn
    simp [appendFreshIdentity, Word.toList_append,
      List.count_eq_zero.mpr freshAbsent]
  · rw [appendFreshIdentity, Word.final_append]
    rfl

private def freshSubstitution
    (fresh : Nat) (replacement : Word Nat) : Nat → Word Nat :=
  fun selected =>
    if selected = fresh then replacement else Word.singleton selected

private theorem flatMap_freshSubstitution_of_not_mem
    (fresh : Nat) (replacement : Word Nat) :
    ∀ (letters : List Nat), fresh ∉ letters →
      letters.flatMap
          (fun selected =>
            (freshSubstitution fresh replacement selected).toList) =
        letters
  | [], _ => rfl
  | selected :: rest, absent => by
      have selectedNe : selected ≠ fresh := by
        intro equal
        apply absent
        simp [equal]
      have restAbsent : fresh ∉ rest := by
        intro member
        exact absent (List.Mem.tail selected member)
      simp only [List.flatMap_cons]
      rw [flatMap_freshSubstitution_of_not_mem
        fresh replacement rest restAbsent]
      simp [freshSubstitution, selectedNe]

private theorem bind_append_fresh
    (word : Word Nat) (fresh : Nat) (replacement : Word Nat)
    (freshAbsent : fresh ∉ word.toList) :
    (word ++ Word.singleton fresh).bind
        (freshSubstitution fresh replacement) =
      word ++ replacement := by
  apply Word.toList_injective
  rw [Word.toList_bind, Word.toList_append,
    Word.toList_singleton, List.flatMap_append,
    flatMap_freshSubstitution_of_not_mem
      fresh replacement word.toList freshAbsent,
    Word.toList_append]
  simp [freshSubstitution]

private def freshAbove : List Nat → Nat
  | [] => 0
  | selected :: rest => max (selected + 1) (freshAbove rest)

private theorem lt_freshAbove_of_mem
    (selected : Nat) :
    ∀ letters : List Nat,
      selected ∈ letters → selected < freshAbove letters
  | [], member => by simp at member
  | head :: rest, member => by
      rcases List.mem_cons.mp member with atHead | inRest
      · subst selected
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self head)
          (Nat.le_max_left (head + 1) (freshAbove rest))
      · exact Nat.lt_of_lt_of_le
          (lt_freshAbove_of_mem selected rest inRest)
          (Nat.le_max_right (head + 1) (freshAbove rest))

private def freshVariable (identity : Identity Nat) : Nat :=
  freshAbove (identity.lhs.toList ++ identity.rhs.toList)

private theorem freshVariable_not_mem_left
    (identity : Identity Nat) :
    freshVariable identity ∉ identity.lhs.toList := by
  intro member
  have impossible :=
    lt_freshAbove_of_mem (freshVariable identity)
      (identity.lhs.toList ++ identity.rhs.toList)
      (List.mem_append.mpr (Or.inl member))
  exact Nat.lt_irrefl _ impossible

private theorem freshVariable_not_mem_right
    (identity : Identity Nat) :
    freshVariable identity ∉ identity.rhs.toList := by
  intro member
  have impossible :=
    lt_freshAbove_of_mem (freshVariable identity)
      (identity.lhs.toList ++ identity.rhs.toList)
      (List.mem_append.mpr (Or.inr member))
  exact Nat.lt_irrefl _ impossible

private theorem derivesDuplicateFinal
    (word : Word Nat)
    (seen : word.final ∈ (splitPrefixFinal word).1) :
    Derives directBasis word (word ++ Word.singleton word.final) := by
  have listed :=
    listDerivesDuplicateFinal
      (splitPrefixFinal word).1 word.final seen
  apply derives_of_listDerives_toList
  rw [Word.toList_append, Word.toList_singleton,
    toList_eq_splitPrefixFinal, split_final_eq]
  simpa [List.append_assoc] using listed

private theorem derives_substituted_appendedFresh
    (identity : Identity Nat) (fresh replacement : Nat)
    (freshLeft : fresh ∉ identity.lhs.toList)
    (freshRight : fresh ∉ identity.rhs.toList)
    (appended : Derives directBasis
      (appendFreshIdentity identity fresh).lhs
      (appendFreshIdentity identity fresh).rhs) :
    Derives directBasis
      (identity.lhs ++ Word.singleton replacement)
      (identity.rhs ++ Word.singleton replacement) := by
  have substituted :=
    Derives.subst appended
      (freshSubstitution fresh (Word.singleton replacement))
  rw [appendFreshIdentity,
    bind_append_fresh identity.lhs fresh
      (Word.singleton replacement) freshLeft,
    bind_append_fresh identity.rhs fresh
      (Word.singleton replacement) freshRight] at substituted
  exact substituted

private theorem derives_of_factors_of_nonsimpleFinal
    (identity : Identity Nat)
    (s5Valid : identity.SatisfiedBy S5_870.table.semigroup)
    (jValid : identity.SatisfiedBy finalMarkerThree.semigroup)
    (leftNonsimple :
      S5_345.simpleFinalVariable identity.lhs = none) :
    Derives directBasis identity.lhs identity.rhs := by
  have simpleEqual := jValid_simpleFinalVariable_eq identity jValid
  have rightNonsimple :
      S5_345.simpleFinalVariable identity.rhs = none :=
    simpleEqual.symm.trans leftNonsimple
  let leftFinal := identity.lhs.final
  let rightFinal := identity.rhs.final
  have leftFinalSeen :
      leftFinal ∈ (splitPrefixFinal identity.lhs).1 := by
    simpa [leftFinal] using
      split_final_mem_of_nonsimple identity.lhs leftNonsimple
  have rightFinalSeen :
      rightFinal ∈ (splitPrefixFinal identity.rhs).1 := by
    simpa [rightFinal] using
      split_final_mem_of_nonsimple identity.rhs rightNonsimple
  have rightShape :
      identity.rhs.toList =
        (splitPrefixFinal identity.rhs).1 ++ [rightFinal] := by
    simpa [rightFinal, split_final_eq] using
      toList_eq_splitPrefixFinal identity.rhs
  have rightRepeated :
      2 ≤ identity.rhs.toList.count rightFinal := by
    rw [rightShape, List.count_append]
    have positive :
        0 < (splitPrefixFinal identity.rhs).1.count rightFinal :=
      List.count_pos_iff.mpr rightFinalSeen
    simp only [List.count_singleton_self]
    omega
  have leftRepeated :
      2 ≤ identity.lhs.toList.count rightFinal :=
    (S5_870.valid_repeated_iff identity s5Valid rightFinal).2
      rightRepeated
  have leftFinalInWord : leftFinal ∈ identity.lhs.toList := by
    rw [toList_eq_splitPrefixFinal, split_final_eq]
    simp [leftFinal]
  have rightFinalInLeftWord : rightFinal ∈ identity.lhs.toList :=
    List.count_pos_iff.mp (by omega)
  have expandLeft :
      Derives directBasis identity.lhs
        (identity.lhs ++ Word.singleton leftFinal) := by
    simpa [leftFinal] using
      derivesDuplicateFinal identity.lhs leftFinalSeen
  have insertRightBeforeLeft :
      Derives directBasis
        (identity.lhs ++ Word.singleton leftFinal)
        ((identity.lhs ++ Word.singleton rightFinal) ++
          Word.singleton leftFinal) := by
    have appendThird :=
      s5DerivesAppendThird identity.lhs rightFinal leftRepeated
    have lifted :=
      liftS5DerivationBeforeSuffix appendThird
        (Word.singleton leftFinal) Word.singleton
    rw [bind_singleton, bind_singleton] at lifted
    simpa [Word.append_assoc] using lifted
  have swapFinals :
      Derives directBasis
        ((identity.lhs ++ Word.singleton rightFinal) ++
          Word.singleton leftFinal)
        ((identity.lhs ++ Word.singleton leftFinal) ++
          Word.singleton rightFinal) := by
    apply derives_of_listDerives_toList
    have listed :=
      listDerivesSwapAfterSeen identity.lhs.toList []
        rightFinal leftFinal rightFinalInLeftWord leftFinalInWord
    simpa [Word.toList_append, List.append_assoc] using listed
  have contractLeft :
      Derives directBasis
        ((identity.lhs ++ Word.singleton leftFinal) ++
          Word.singleton rightFinal)
        (identity.lhs ++ Word.singleton rightFinal) := by
    have appended :=
      Derives.appendRight expandLeft (Word.singleton rightFinal)
    simpa [Word.append_assoc] using appended.symm
  let fresh := freshVariable identity
  have freshLeft : fresh ∉ identity.lhs.toList := by
    simpa [fresh] using freshVariable_not_mem_left identity
  have freshRight : fresh ∉ identity.rhs.toList := by
    simpa [fresh] using freshVariable_not_mem_right identity
  let extended := appendFreshIdentity identity fresh
  have extendedS5 :
      extended.SatisfiedBy S5_870.table.semigroup :=
    appendFreshIdentity_valid S5_870.table.semigroup
      identity fresh s5Valid
  have extendedJ :
      extended.SatisfiedBy finalMarkerThree.semigroup :=
    appendFreshIdentity_valid finalMarkerThree.semigroup
      identity fresh jValid
  have extendedSimple :
      S5_345.simpleFinalVariable extended.lhs = some fresh := by
    exact appendFreshIdentity_left_simple identity fresh freshLeft
  have appended :
      Derives directBasis extended.lhs extended.rhs :=
    derives_of_factors_of_simpleFinal
      extended extendedS5 extendedJ extendedSimple
  have substituted :
      Derives directBasis
        (identity.lhs ++ Word.singleton rightFinal)
        (identity.rhs ++ Word.singleton rightFinal) :=
    derives_substituted_appendedFresh identity fresh rightFinal
      freshLeft freshRight appended
  have contractRight :
      Derives directBasis
        (identity.rhs ++ Word.singleton rightFinal) identity.rhs := by
    simpa [rightFinal] using
      (derivesDuplicateFinal identity.rhs rightFinalSeen).symm
  exact expandLeft.trans <| insertRightBeforeLeft.trans <|
    swapFinals.trans <| contractLeft.trans <|
      substituted.trans contractRight

/-- Derivational content of Lee--Zhang Proposition 10.7 for the exact
`P2^1` and `J` representatives used in this repository. -/
theorem derives_of_factors
    (identity : Identity Nat)
    (s5Valid : identity.SatisfiedBy S5_870.table.semigroup)
    (jValid : identity.SatisfiedBy finalMarkerThree.semigroup) :
    Derives directBasis identity.lhs identity.rhs := by
  cases leftSimple : S5_345.simpleFinalVariable identity.lhs with
  | some final =>
      exact derives_of_factors_of_simpleFinal
        identity s5Valid jValid leftSimple
  | none =>
      exact derives_of_factors_of_nonsimpleFinal
        identity s5Valid jValid leftSimple

/-! ## Exact authenticated i94 source tables -/

private def row6
    (c0 c1 c2 c3 c4 c5 column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

namespace S6_7676

/-- Exact one-based authenticated table:
`[[1,1,1,4,1,6],[1,1,1,4,2,6],[1,1,1,4,3,6],
  [1,1,1,4,4,6],[1,1,3,4,5,6],[1,1,4,4,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then row6 0 0 0 3 0 5 b else
    if a = 1 then row6 0 0 0 3 1 5 b else
      if a = 2 then row6 0 0 0 3 2 5 b else
        if a = 3 then row6 0 0 0 3 3 5 b else
          if a = 4 then row6 0 0 2 3 4 5 b else
            row6 0 0 3 3 5 5 b

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "971693d7ebc173612c5892e41c2baed927709753b0aebcaa8e3d2d5af75ec92d"

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (table.mul left right).val + 1

theorem table_certificate :
    tableRowsOneBased =
      [[1,1,1,4,1,6],[1,1,1,4,2,6],[1,1,1,4,3,6],
       [1,1,1,4,4,6],[1,1,3,4,5,6],[1,1,4,4,6,6]] := by
  decide

theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide)

theorem directModels : Models table.semigroup.opposite directBasis := by
  simpa [basis] using models.oppositeReversed

def s5Embedding :
    Embedding S5_870.table.semigroup table.semigroup.opposite where
  toFun := fun value : Fin 5 =>
    if value = 0 then (0 : Fin 6) else
      if value = 1 then (2 : Fin 6) else
        if value = 2 then (3 : Fin 6) else
          if value = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

def jEmbedding :
    Embedding finalMarkerThree.semigroup table.semigroup.opposite where
  toFun := fun value : Fin 3 =>
    if value = 0 then (0 : Fin 6) else
      if value = 1 then (1 : Fin 6) else (4 : Fin 6)
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

theorem directBasisFor :
    BasisFor table.semigroup.opposite directBasis := by
  refine ⟨directModels, ?_⟩
  intro identity valid
  exact derives_of_factors identity
    (s5Embedding.pullback_identity identity valid)
    (jEmbedding.pullback_identity identity valid)

/-- Unconditional endpoint for the exact authenticated source orientation. -/
theorem basisFor : BasisFor table.semigroup basis := by
  simpa [basis] using directBasisFor.oppositeReversed

end S6_7676

namespace S6_8500

/-- Exact one-based authenticated table:
`[[1,1,1,4,1,6],[1,1,1,4,2,6],[1,1,1,4,3,6],
  [1,1,1,4,4,6],[1,2,2,4,5,6],[1,4,4,4,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then row6 0 0 0 3 0 5 b else
    if a = 1 then row6 0 0 0 3 1 5 b else
      if a = 2 then row6 0 0 0 3 2 5 b else
        if a = 3 then row6 0 0 0 3 3 5 b else
          if a = 4 then row6 0 1 1 3 4 5 b else
            row6 0 3 3 3 5 5 b

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "00df52efd8c23ae672f3a19e9953551decfeb7d33d7a9636b2c87a626fbcc8a0"

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (table.mul left right).val + 1

theorem table_certificate :
    tableRowsOneBased =
      [[1,1,1,4,1,6],[1,1,1,4,2,6],[1,1,1,4,3,6],
       [1,1,1,4,4,6],[1,2,2,4,5,6],[1,4,4,4,6,6]] := by
  decide

theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide)

theorem directModels : Models table.semigroup.opposite directBasis := by
  simpa [basis] using models.oppositeReversed

def s5Embedding :
    Embedding S5_870.table.semigroup table.semigroup.opposite where
  toFun := fun value : Fin 5 =>
    if value = 0 then (0 : Fin 6) else
      if value = 1 then (1 : Fin 6) else
        if value = 2 then (3 : Fin 6) else
          if value = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

/-- The direct target has quotient values `[1,1,2,1,3,1]` onto `J`. -/
def jQuotient :
    SplitSurjection table.semigroup.opposite
      finalMarkerThree.semigroup where
  toFun := fun value : Fin 6 =>
    if value = 0 then (0 : Fin 3) else
      if value = 1 then (0 : Fin 3) else
        if value = 2 then (1 : Fin 3) else
          if value = 3 then (0 : Fin 3) else
            if value = 4 then (2 : Fin 3) else (0 : Fin 3)
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  preimage := fun value : Fin 3 =>
    if value = 0 then (0 : Fin 6) else
      if value = 1 then (2 : Fin 6) else (4 : Fin 6)
  right_inverse := by
    intro value
    apply Fin.ext
    revert value
    decide

theorem directBasisFor :
    BasisFor table.semigroup.opposite directBasis := by
  refine ⟨directModels, ?_⟩
  intro identity valid
  exact derives_of_factors identity
    (s5Embedding.pullback_identity identity valid)
    (jQuotient.pushforwardIdentity identity valid)

/-- Unconditional endpoint for the exact authenticated source orientation. -/
theorem basisFor : BasisFor table.semigroup basis := by
  simpa [basis] using directBasisFor.oppositeReversed

end S6_8500

namespace S6_10426

/-- Exact one-based authenticated table:
`[[1,1,3,3,5,1],[1,1,3,3,5,2],[1,1,3,3,5,3],
  [1,1,3,3,5,4],[1,1,3,1,5,5],[1,1,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then row6 0 0 2 2 4 0 b else
    if a = 1 then row6 0 0 2 2 4 1 b else
      if a = 2 then row6 0 0 2 2 4 2 b else
        if a = 3 then row6 0 0 2 2 4 3 b else
          if a = 4 then row6 0 0 2 0 4 4 b else
            row6 0 0 2 3 4 5 b

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "2b78a46cdec9b100595709967e98069e1dc59d8b56f560c032cfde480aa08fd6"

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (table.mul left right).val + 1

theorem table_certificate :
    tableRowsOneBased =
      [[1,1,3,3,5,1],[1,1,3,3,5,2],[1,1,3,3,5,3],
       [1,1,3,3,5,4],[1,1,3,1,5,5],[1,1,3,4,5,6]] := by
  decide

theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide)

theorem directModels : Models table.semigroup.opposite directBasis := by
  simpa [basis] using models.oppositeReversed

def s5Embedding :
    Embedding S5_870.table.semigroup table.semigroup.opposite where
  toFun := fun value : Fin 5 =>
    if value = 0 then (2 : Fin 6) else
      if value = 1 then (3 : Fin 6) else
        if value = 2 then (0 : Fin 6) else
          if value = 3 then (5 : Fin 6) else (4 : Fin 6)
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

def jEmbedding :
    Embedding finalMarkerThree.semigroup table.semigroup.opposite where
  toFun := fun value : Fin 3 =>
    if value = 0 then (0 : Fin 6) else
      if value = 1 then (1 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

theorem directBasisFor :
    BasisFor table.semigroup.opposite directBasis := by
  refine ⟨directModels, ?_⟩
  intro identity valid
  exact derives_of_factors identity
    (s5Embedding.pullback_identity identity valid)
    (jEmbedding.pullback_identity identity valid)

/-- Unconditional endpoint for the exact authenticated source orientation. -/
theorem basisFor : BasisFor table.semigroup basis := by
  simpa [basis] using directBasisFor.oppositeReversed

end S6_10426

namespace S6_10643

/-- Exact one-based authenticated table:
`[[1,1,3,5,5,1],[1,1,3,5,5,2],[1,1,3,3,5,3],
  [1,1,3,3,5,4],[1,1,3,3,5,5],[1,1,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then row6 0 0 2 4 4 0 b else
    if a = 1 then row6 0 0 2 4 4 1 b else
      if a = 2 then row6 0 0 2 2 4 2 b else
        if a = 3 then row6 0 0 2 2 4 3 b else
          if a = 4 then row6 0 0 2 2 4 4 b else
            row6 0 0 2 3 4 5 b

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "a23f1c6bc4f8999f443ce32cd3686c1d7fa50bc705b1f6f7c111c5fa96ac9a50"

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (table.mul left right).val + 1

theorem table_certificate :
    tableRowsOneBased =
      [[1,1,3,5,5,1],[1,1,3,5,5,2],[1,1,3,3,5,3],
       [1,1,3,3,5,4],[1,1,3,3,5,5],[1,1,3,4,5,6]] := by
  decide

theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide)

theorem directModels : Models table.semigroup.opposite directBasis := by
  simpa [basis] using models.oppositeReversed

def s5Embedding :
    Embedding S5_870.table.semigroup table.semigroup.opposite where
  toFun := fun value : Fin 5 =>
    if value = 0 then (2 : Fin 6) else
      if value = 1 then (3 : Fin 6) else
        if value = 2 then (4 : Fin 6) else
          if value = 3 then (5 : Fin 6) else (0 : Fin 6)
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

def jEmbedding :
    Embedding finalMarkerThree.semigroup table.semigroup.opposite where
  toFun := fun value : Fin 3 =>
    if value = 0 then (0 : Fin 6) else
      if value = 1 then (1 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

theorem directBasisFor :
    BasisFor table.semigroup.opposite directBasis := by
  refine ⟨directModels, ?_⟩
  intro identity valid
  exact derives_of_factors identity
    (s5Embedding.pullback_identity identity valid)
    (jEmbedding.pullback_identity identity valid)

/-- Unconditional endpoint for the exact authenticated source orientation. -/
theorem basisFor : BasisFor table.semigroup basis := by
  simpa [basis] using directBasisFor.oppositeReversed

end S6_10643

end SemigroupBasis.CoRoots.Order6LeeZhangClass356
