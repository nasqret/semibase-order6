import SemigroupBasis.CoRoots.S5_55
import SemigroupBasis.Examples.CommutativeExponentThree
import SemigroupBasis.Generated.S3_8
import SemigroupBasis.Generated.S4_9
import SemigroupBasis.Generated.S4_35
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Subdirect

namespace SemigroupBasis.CoRoots.Order6ShortWordMultiplicityJoin

open SemigroupBasis
open SemigroupBasis.Examples

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xxx : Word Nat := w 0 [0, 0]
def xxxx : Word Nat := w 0 [0, 0, 0]
def yxx : Word Nat := w 1 [0, 0]
def yxxx : Word Nat := w 1 [0, 0, 0]
def xyx : Word Nat := w 0 [1, 0]
def xxy : Word Nat := w 0 [0, 1]
def zyx : Word Nat := w 2 [1, 0]
def yzx : Word Nat := w 1 [2, 0]
def zxy : Word Nat := w 2 [0, 1]

def unaryPowerLaw : Identity Nat := ⟨xxx, xxxx⟩
def contextualPowerLaw : Identity Nat := ⟨yxxx, yxx⟩
def repeatedMiddleLaw : Identity Nat := ⟨yxx, xyx⟩
def repeatedPrefixLaw : Identity Nat := ⟨yxx, xxy⟩
def prefixCommutationLaw : Identity Nat := ⟨zyx, yzx⟩
def suffixCommutationLaw : Identity Nat := ⟨zyx, zxy⟩

/-- The six-law basis recorded for `S6_2612` and `S6_5158`:
`xxx = xxxx`, `yxxx = yxx`, `yxx = xyx`, `yxx = xxy`,
`zyx = yzx`, and `zyx = zxy`. -/
def basis : List (Identity Nat) :=
  [unaryPowerLaw, contextualPowerLaw, repeatedMiddleLaw,
    repeatedPrefixLaw, prefixCommutationLaw, suffixCommutationLaw]

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

/-- Finite truth-table check of all six laws in the multiplicity factor. -/
theorem s3_8_models :
    Models SemigroupBasis.Generated.S3_8.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S3_8.table basis toFinThree (by decide)

/-- Finite truth-table check of all six laws in the `S4_9` short-word
factor. -/
theorem s4_9_models :
    Models SemigroupBasis.Generated.S4_9.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S4_9.table basis toFinThree (by decide)

/-- Finite truth-table check of all six laws in the identity-equivalent
`S4_35` short-word factor. -/
theorem s4_35_models :
    Models SemigroupBasis.Generated.S4_35.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S4_35.table basis toFinThree (by decide)

private def instantiateThreeWords
    (x y z : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private def instantiateTwoWords
    (x y : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | n + 2 => Word.singleton (n + 2)

/-- Swap the first two nonempty blocks before a fixed nonempty suffix. -/
theorem derivesPrefixSwap (u v suffix : Word Nat) :
    Derives basis ((u ++ v) ++ suffix) ((v ++ u) ++ suffix) := by
  have base : Derives basis zyx yzx :=
    Derives.fromBasis (e := prefixCommutationLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateThreeWords suffix v u)
  simpa [prefixCommutationLaw, zyx, yzx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Swap the last two nonempty blocks after a fixed nonempty prefix. -/
theorem derivesSuffixSwap (pre u v : Word Nat) :
    Derives basis ((pre ++ u) ++ v) ((pre ++ v) ++ u) := by
  have base : Derives basis zyx zxy :=
    Derives.fromBasis (e := suffixCommutationLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateThreeWords v u pre)
  simpa [suffixCommutationLaw, zyx, zxy, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

private inductive ListDerives : List Nat → List Nat → Prop
  | empty : ListDerives [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives basis (w x xs) (w y ys) →
      ListDerives (x :: xs) (y :: ys)

private theorem ListDerives.trans {xs ys zs : List Nat}
    (first : ListDerives xs ys) (second : ListDerives ys zs) :
    ListDerives xs zs := by
  cases first with
  | empty =>
      cases second
      exact ListDerives.empty
  | words firstProof =>
      cases second with
      | words secondProof =>
          exact ListDerives.words
            (Derives.trans firstProof secondProof)

private theorem listDerives_of_perm_with_prefix
    (pre : List Nat) {xs ys : List Nat}
    (permutation : xs.Perm ys)
    (long : 3 ≤ (pre ++ xs).length) :
    ListDerives (pre ++ xs) (pre ++ ys) := by
  induction permutation generalizing pre with
  | nil =>
      cases pre with
      | nil => simp at long
      | cons p ps => exact ListDerives.words (Derives.refl _)
  | cons x permutation ih =>
      have next :=
        ih (pre := pre ++ [x]) <| by
          simpa [List.append_assoc] using long
      simpa [List.append_assoc] using next
  | swap x y xs =>
      cases pre with
      | nil =>
          cases xs with
          | nil => simp at long
          | cons z zs =>
              exact ListDerives.words <| by
                simpa [w, Word.singleton, Word.append,
                  Word.append_assoc] using
                    derivesPrefixSwap
                      (Word.singleton y) (Word.singleton x)
                      (w z zs)
      | cons p ps =>
          cases xs with
          | nil =>
              exact ListDerives.words <| by
                simpa [w, Word.singleton, Word.append,
                  Word.append_assoc] using
                    derivesSuffixSwap
                      (w p ps) (Word.singleton y)
                      (Word.singleton x)
          | cons z zs =>
              have swapped :=
                Derives.appendRight
                  (derivesSuffixSwap
                    (w p ps) (Word.singleton y)
                    (Word.singleton x))
                  (w z zs)
              exact ListDerives.words <| by
                simpa [w, Word.singleton, Word.append,
                  Word.append_assoc] using swapped
  | trans first second ihFirst ihSecond =>
      have firstDerivation := ihFirst (pre := pre) long
      have secondDerivation :=
        ihSecond (pre := pre) <| by
          rw [List.length_append, ← first.length_eq]
          simpa [List.length_append] using long
      exact firstDerivation.trans secondDerivation

/-- Every permutation of a word of length at least three follows from the
two ternary commutation laws. -/
theorem derivesLongPermutation (left right : Word Nat)
    (long : 3 ≤ left.toList.length)
    (permutation : left.toList.Perm right.toList) :
    Derives basis left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          have lifted :=
            listDerives_of_perm_with_prefix []
              (xs := leftHead :: leftTail)
              (ys := rightHead :: rightTail)
              permutation long
          cases lifted with
          | words derivation => exact derivation

/-- Contract four copies of a nonempty block to three. -/
theorem derivesFourthPowerContraction (u : Word Nat) :
    Derives basis (((u ++ u) ++ u) ++ u) ((u ++ u) ++ u) := by
  have base : Derives basis xxxx xxx :=
    Derives.symm <|
      Derives.fromBasis (e := unaryPowerLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateTwoWords u u)
  simpa [unaryPowerLaw, xxx, xxxx, w, instantiateTwoWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- A fixed nonempty marker permits a third copy of any nonempty block to
be inserted or removed. -/
theorem derivesContextTriple (marker u : Word Nat) :
    Derives basis
      (marker ++ ((u ++ u) ++ u))
      (marker ++ (u ++ u)) := by
  have base : Derives basis yxxx yxx :=
    Derives.fromBasis (e := contextualPowerLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateTwoWords u marker)
  simpa [contextualPowerLaw, yxxx, yxx, w, instantiateTwoWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

private theorem bind_append
    (u v : Word Nat) (substitution : Nat → Word Nat) :
    (u ++ v).bind substitution =
      u.bind substitution ++ v.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (word : Word Nat)
    (first second : Nat → Word Nat) :
    (word.bind first).bind second =
      word.bind (fun x => (first x).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- Replay the commutative exponent-three normalizer behind one fixed
nonempty marker. The marker supplies the context required by
`yxxx = yxx`, while the ternary swap laws supply commutativity. -/
theorem liftExponentThree
    {u v : Word Nat}
    (derivation : Derives commutativeExponentThreeBasis u v)
    (marker : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis
      (marker ++ u.bind substitution)
      (marker ++ v.bind substitution) := by
  induction derivation generalizing marker substitution with
  | fromBasis member =>
      simp only [commutativeExponentThreeBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simpa [exponentThreeLaw, exponentXX, exponentXXX,
          Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          Derives.symm (derivesContextTriple marker (substitution 0))
      · simpa [exponentCommutativityLaw, exponentXY, exponentYX,
          Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          derivesSuffixSwap marker (substitution 0) (substitution 1)
  | refl =>
      exact Derives.refl _
  | symm _ ih =>
      exact Derives.symm (ih marker substitution)
  | trans _ _ first second =>
      exact Derives.trans
        (first marker substitution) (second marker substitution)
  | prepend stem _ ih =>
      simpa [bind_append, Word.append_assoc] using
        ih (marker ++ stem.bind substitution) substitution
  | appendRight _ suffix ih =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight
          (ih marker substitution) (suffix.bind substitution)
  | subst _ first ih =>
      simpa [bind_bind] using
        ih marker (fun x => (first x).bind substitution)

private def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

private def frontedWord (letter : Nat) (word : Word Nat) : Word Nat :=
  wordOfCons letter (word.toList.erase letter)

private def markerReduce (letter : Nat) (word : Word Nat) : Word Nat :=
  wordOfCons letter (exponentReduce (word.toList.erase letter))

private def doubleMarkerReduce
    (first second : Nat) (word : Word Nat) : Word Nat :=
  markerReduce second (markerReduce first word)

private theorem word_perm_frontedWord
    (letter : Nat) (word : Word Nat)
    (present : letter ∈ word.toList) :
    word.toList.Perm (frontedWord letter word).toList := by
  simpa [frontedWord, wordOfCons, Word.toList] using
    List.perm_cons_erase present

private theorem exponentReduce_cons_ne_nil
    (head : Nat) (tail : List Nat) :
    exponentReduce (head :: tail) ≠ [] := by
  intro empty
  have count := count_exponentReduce head (head :: tail)
  rw [empty] at count
  simp at count
  omega

private theorem exponentReduce_length_at_least_two
    (letters : List Nat) (long : 2 ≤ letters.length) :
    2 ≤ (exponentReduce letters).length := by
  cases letters with
  | nil => simp at long
  | cons first rest =>
      cases rest with
      | nil => simp at long
      | cons second tail =>
          by_cases equal : first = second
          · subst second
            have count := count_exponentReduce first (first :: first :: tail)
            have countLe :=
              List.count_le_length
                (a := first) (l := exponentReduce (first :: first :: tail))
            simp only [List.count_cons_self] at count
            omega
          · have firstPositive :
                0 < (exponentReduce (first :: second :: tail)).count first := by
              rw [count_exponentReduce]
              simp only [List.count_cons_self]
              omega
            have secondPositive :
                0 < (exponentReduce (first :: second :: tail)).count second := by
              rw [count_exponentReduce]
              simp only [List.count_cons]
              simp [equal]
              omega
            have firstMember := List.count_pos_iff.mp firstPositive
            have secondMember := List.count_pos_iff.mp secondPositive
            cases reduced : exponentReduce (first :: second :: tail) with
            | nil => simp [reduced] at firstMember
            | cons only remainder =>
                cases remainder with
                | nil =>
                    simp [reduced] at firstMember secondMember
                    exact False.elim (equal (firstMember.trans secondMember.symm))
                | cons next more => simp

private theorem markerReduce_long
    (letter : Nat) (word : Word Nat)
    (present : letter ∈ word.toList)
    (long : 3 ≤ word.toList.length) :
    3 ≤ (markerReduce letter word).toList.length := by
  have eraseLength := List.length_erase_of_mem present
  have erasedLong : 2 ≤ (word.toList.erase letter).length := by
    omega
  have reducedLong :=
    exponentReduce_length_at_least_two
      (word.toList.erase letter) erasedLong
  simpa [markerReduce, wordOfCons, Word.toList] using
    Nat.succ_le_succ reducedLong

/-- Move one supported marker to the front and cap every multiplicity in
the remaining word at two. -/
theorem derivesMarkerReduce
    (letter : Nat) (word : Word Nat)
    (present : letter ∈ word.toList)
    (long : 3 ≤ word.toList.length) :
    Derives basis word (markerReduce letter word) := by
  have arrange :=
    derivesLongPermutation word (frontedWord letter word) long
      (word_perm_frontedWord letter word present)
  have eraseLength := List.length_erase_of_mem present
  have erasedNonempty : word.toList.erase letter ≠ [] := by
    intro empty
    rw [empty] at eraseLength
    simp at eraseLength
    omega
  cases erased : word.toList.erase letter with
  | nil => contradiction
  | cons head tail =>
      let rest : Word Nat := wordOfCons head tail
      have oldNormal := exponentDerivesNormal rest
      cases reduced : exponentReduce rest.toList with
      | nil =>
          exact False.elim <|
            exponentReduce_cons_ne_nil head tail <| by
              simpa [rest, wordOfCons, Word.toList] using reduced
      | cons normalHead normalTail =>
          rw [reduced] at oldNormal
          change
            Derives commutativeExponentThreeBasis
              rest (wordOfCons normalHead normalTail) at oldNormal
          have lifted :=
            liftExponentThree oldNormal
              (Word.singleton letter) Word.singleton
          rw [bind_singleton, bind_singleton] at lifted
          change
            Derives basis
              (wordOfCons letter (head :: tail))
              (wordOfCons letter (normalHead :: normalTail)) at lifted
          have reduced' :
              exponentReduce (head :: tail) =
                normalHead :: normalTail := by
            simpa [rest, wordOfCons, Word.toList] using reduced
          exact Derives.trans arrange <| by
            change
              Derives basis
                (wordOfCons letter (word.toList.erase letter))
                (wordOfCons letter
                  (exponentReduce (word.toList.erase letter)))
            rw [erased, reduced']
            exact lifted

theorem count_markerReduce
    (tested marker : Nat) (word : Word Nat)
    (_present : marker ∈ word.toList) :
    (markerReduce marker word).toList.count tested =
      if tested = marker then
        1 + min (word.toList.count tested - 1) 2
      else
        min (word.toList.count tested) 2 := by
  by_cases same : tested = marker
  · subst tested
    rw [show (markerReduce marker word).toList =
        marker :: exponentReduce (word.toList.erase marker) by rfl]
    rw [List.count_cons_self, count_exponentReduce,
      List.count_erase_self]
    simp
    omega
  · rw [show (markerReduce marker word).toList =
        marker :: exponentReduce (word.toList.erase marker) by rfl]
    rw [List.count_cons_of_ne (Ne.symm same),
      count_exponentReduce, List.count_erase_of_ne same]
    simp [same]

private theorem markerReduce_mem_of_ne
    (first second : Nat) (word : Word Nat)
    (firstPresent : first ∈ word.toList)
    (secondPresent : second ∈ word.toList)
    (different : second ≠ first) :
    second ∈ (markerReduce first word).toList := by
  rw [← List.count_pos_iff,
    count_markerReduce second first word firstPresent]
  simp only [if_neg different]
  have positive : 0 < word.toList.count second :=
    List.count_pos_iff.mpr secondPresent
  omega

theorem count_doubleMarkerReduce
    (tested first second : Nat) (word : Word Nat)
    (firstPresent : first ∈ word.toList)
    (secondPresent : second ∈ word.toList)
    (different : first ≠ second) :
    (doubleMarkerReduce first second word).toList.count tested =
      min (word.toList.count tested) 2 := by
  let firstWord := markerReduce first word
  have secondInFirst : second ∈ firstWord.toList :=
    markerReduce_mem_of_ne first second word firstPresent secondPresent
      (Ne.symm different)
  by_cases testedSecond : tested = second
  · subst tested
    rw [doubleMarkerReduce,
      count_markerReduce second second firstWord secondInFirst,
      if_pos rfl,
      count_markerReduce second first word firstPresent,
      if_neg (Ne.symm different)]
    have positive : 0 < word.toList.count second :=
      List.count_pos_iff.mpr secondPresent
    omega
  · rw [doubleMarkerReduce,
      count_markerReduce tested second firstWord secondInFirst,
      if_neg testedSecond]
    by_cases testedFirst : tested = first
    · subst tested
      rw [count_markerReduce first first word firstPresent, if_pos rfl]
      have positive : 0 < word.toList.count first :=
        List.count_pos_iff.mpr firstPresent
      omega
    · rw [count_markerReduce tested first word firstPresent,
        if_neg testedFirst]
      omega

/-- Normalize a long word twice, using two distinct supported markers, so
that every variable multiplicity is exactly capped at two. -/
theorem derivesDoubleMarkerReduce
    (first second : Nat) (word : Word Nat)
    (firstPresent : first ∈ word.toList)
    (secondPresent : second ∈ word.toList)
    (different : first ≠ second)
    (long : 3 ≤ word.toList.length) :
    Derives basis word (doubleMarkerReduce first second word) := by
  have firstDerivation :=
    derivesMarkerReduce first word firstPresent long
  have secondInFirst : second ∈ (markerReduce first word).toList :=
    markerReduce_mem_of_ne first second word firstPresent secondPresent
      (Ne.symm different)
  have firstLong := markerReduce_long first word firstPresent long
  have secondDerivation :=
    derivesMarkerReduce second (markerReduce first word)
      secondInFirst firstLong
  exact Derives.trans firstDerivation secondDerivation

private theorem doubleMarkerReduce_long
    (first second : Nat) (word : Word Nat)
    (firstPresent : first ∈ word.toList)
    (secondPresent : second ∈ word.toList)
    (different : first ≠ second)
    (long : 3 ≤ word.toList.length) :
    3 ≤ (doubleMarkerReduce first second word).toList.length := by
  have secondInFirst : second ∈ (markerReduce first word).toList :=
    markerReduce_mem_of_ne first second word firstPresent secondPresent
      (Ne.symm different)
  exact markerReduce_long second (markerReduce first word)
    secondInFirst (markerReduce_long first word firstPresent long)

private theorem support_of_capped_count_eq
    {left right : Word Nat}
    (capped : ∀ letter,
      min (left.toList.count letter) 2 =
        min (right.toList.count letter) 2) :
    SemigroupBasis.CoRoots.S5_55.SameSupport left right := by
  intro letter
  constructor
  · intro member
    have positive : 0 < left.toList.count letter :=
      List.count_pos_iff.mpr member
    have rightPositive : 0 < right.toList.count letter := by
      have equal := capped letter
      omega
    exact List.count_pos_iff.mp rightPositive
  · intro member
    have positive : 0 < right.toList.count letter :=
      List.count_pos_iff.mpr member
    have leftPositive : 0 < left.toList.count letter := by
      have equal := capped letter
      omega
    exact List.count_pos_iff.mp leftPositive

private theorem all_letters_eq_head
    (word : Word Nat)
    (noOther : ¬ ∃ letter,
      letter ∈ word.toList ∧ letter ≠ word.head) :
    ∀ letter, letter ∈ word.toList → letter = word.head := by
  intro letter member
  apply Decidable.byContradiction
  intro different
  exact noOther ⟨letter, member, different⟩

private theorem list_eq_replicate_of_all_eq
    (letter : Nat) : ∀ letters : List Nat,
    (∀ value, value ∈ letters → value = letter) →
      letters = List.replicate letters.length letter
  | [], _ => rfl
  | value :: rest, all => by
      have valueEq : value = letter := all value (by simp)
      subst value
      have tailEq :=
        list_eq_replicate_of_all_eq letter rest <| by
          intro value member
          exact all value (by simp [member])
      simpa only [List.length_cons, List.replicate_succ] using
        congrArg (List.cons letter) tailEq

private theorem derivesReplicateTailToCube (letter : Nat) :
    ∀ tailLength : Nat, 2 ≤ tailLength →
      Derives basis
        (wordOfCons letter (List.replicate tailLength letter))
        (wordOfCons letter [letter, letter])
  | 0, bound => by omega
  | 1, bound => by omega
  | 2, _ => Derives.refl _
  | n + 3, _ => by
      have step :
          Derives basis
            (wordOfCons letter (List.replicate (n + 3) letter))
            (wordOfCons letter (List.replicate (n + 2) letter)) := by
        cases n with
        | zero =>
            simpa [wordOfCons, Word.singleton, Word.append,
              Word.append_assoc] using
                derivesFourthPowerContraction (Word.singleton letter)
        | succ k =>
            have contracted :=
              Derives.appendRight
                (derivesFourthPowerContraction (Word.singleton letter))
                (wordOfCons letter (List.replicate k letter))
            simpa [wordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.replicate_succ,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                contracted
      exact Derives.trans step
        (derivesReplicateTailToCube letter (n + 2) (by omega))
termination_by tailLength => tailLength
decreasing_by omega

private theorem derivesUnaryToCube
    (word : Word Nat) (letter : Nat)
    (long : 3 ≤ word.toList.length)
    (all : ∀ value, value ∈ word.toList → value = letter) :
    Derives basis word (wordOfCons letter [letter, letter]) := by
  cases word with
  | mk head tail =>
      have headEq : head = letter := all head (by simp [Word.toList])
      subst head
      have tailEq : tail = List.replicate tail.length letter :=
        list_eq_replicate_of_all_eq letter tail <| by
          intro value member
          exact all value (by simp [Word.toList, member])
      rw [tailEq]
      apply derivesReplicateTailToCube letter
      simpa [Word.toList] using long

/-- Long words with the same multiplicities capped at two have the same
derivable normal form. With at least two support variables, two marker
passes produce the capped multiset; with singleton support, every power of
length at least three contracts to the cube. -/
theorem derivesLongOfCappedCountEq
    (left right : Word Nat)
    (leftLong : 3 ≤ left.toList.length)
    (rightLong : 3 ≤ right.toList.length)
    (capped : ∀ letter,
      min (left.toList.count letter) 2 =
        min (right.toList.count letter) 2) :
    Derives basis left right := by
  let first := left.head
  by_cases multiple :
      ∃ second, second ∈ left.toList ∧ second ≠ first
  · obtain ⟨second, secondLeft, secondNe⟩ := multiple
    have firstLeft : first ∈ left.toList := by
      simp [first, Word.toList]
    have support := support_of_capped_count_eq capped
    have firstRight : first ∈ right.toList :=
      (support first).mp firstLeft
    have secondRight : second ∈ right.toList :=
      (support second).mp secondLeft
    have leftNormal :=
      derivesDoubleMarkerReduce first second left
        firstLeft secondLeft (Ne.symm secondNe) leftLong
    have rightNormal :=
      derivesDoubleMarkerReduce first second right
        firstRight secondRight (Ne.symm secondNe) rightLong
    have normalPermutation :
        (doubleMarkerReduce first second left).toList.Perm
          (doubleMarkerReduce first second right).toList := by
      rw [List.perm_iff_count]
      intro letter
      rw [count_doubleMarkerReduce letter first second left
          firstLeft secondLeft (Ne.symm secondNe),
        count_doubleMarkerReduce letter first second right
          firstRight secondRight (Ne.symm secondNe),
        capped letter]
    have middle :=
      derivesLongPermutation
        (doubleMarkerReduce first second left)
        (doubleMarkerReduce first second right)
        (doubleMarkerReduce_long first second left
          firstLeft secondLeft (Ne.symm secondNe) leftLong)
        normalPermutation
    exact leftNormal.trans (middle.trans rightNormal.symm)
  · have leftAll := all_letters_eq_head left multiple
    have support := support_of_capped_count_eq capped
    have rightAll :
        ∀ value, value ∈ right.toList → value = first := by
      intro value member
      exact leftAll value ((support value).mpr member)
    have leftCube := derivesUnaryToCube left first leftLong leftAll
    have rightCube := derivesUnaryToCube right first rightLong rightAll
    exact leftCube.trans rightCube.symm

/-- Sort the capped multiplicity multiset. This is the deterministic class
key for long words; singleton-support long words are represented separately
by the cube in `derivesLongOfCappedCountEq`. -/
def sortedCappedList (letters : List Nat) : List Nat :=
  (exponentReduce letters).mergeSort
    (fun left right : Nat => decide (left ≤ right))

theorem sortedCappedList_count (letters : List Nat) (tested : Nat) :
    (sortedCappedList letters).count tested =
      min (letters.count tested) 2 := by
  have permutation :=
    List.mergeSort_perm (exponentReduce letters)
      (fun left right : Nat => decide (left ≤ right))
  unfold sortedCappedList
  rw [permutation.count_eq tested, count_exponentReduce]

theorem sortedCappedList_pairwise (letters : List Nat) :
    (sortedCappedList letters).Pairwise (· ≤ ·) := by
  have transitive :
      ∀ left middle right : Nat,
        decide (left ≤ middle) = true →
        decide (middle ≤ right) = true →
        decide (left ≤ right) = true := by
    intro left middle right first second
    exact decide_eq_true
      (Nat.le_trans
        (of_decide_eq_true first)
        (of_decide_eq_true second))
  have total :
      ∀ left right : Nat,
        (decide (left ≤ right) ||
          decide (right ≤ left)) = true := by
    intro left right
    rcases Nat.le_total left right with first | second
    · simp [first]
    · simp [second]
  have sorted :=
    List.pairwise_mergeSort transitive total (exponentReduce letters)
  simpa [sortedCappedList] using
    (sorted.imp fun relation => of_decide_eq_true relation)

/-- Equality of capped multiplicities is equivalent to equality of the
sorted capped renderer. -/
theorem sortedCappedList_eq_of_capped_count_eq
    {left right : List Nat}
    (capped : ∀ letter,
      min (left.count letter) 2 = min (right.count letter) 2) :
    sortedCappedList left = sortedCappedList right := by
  have permutation :
      (sortedCappedList left).Perm (sortedCappedList right) := by
    rw [List.perm_iff_count]
    intro letter
    rw [sortedCappedList_count, sortedCappedList_count, capped letter]
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ leftLe rightLe => Nat.le_antisymm leftLe rightLe)
    (sortedCappedList_pairwise left)
    (sortedCappedList_pairwise right)
    permutation

/-- Exact congruence class of the six laws: words of lengths one and two
are literal; from length three onward only the sorted multiplicity vector
capped at two remains. -/
def ExactBasisClass (left right : Word Nat) : Prop :=
  left = right ∨
    (3 ≤ left.toList.length ∧
      3 ≤ right.toList.length ∧
      ∀ letter,
        min (left.toList.count letter) 2 =
          min (right.toList.count letter) 2)

private def shortLengthState (length : Nat) : Fin 4 :=
  if length = 1 then 3 else if length = 2 then 1 else 0

private theorem s4_9_eval_constant_three (word : Word Nat) :
    SemigroupBasis.Generated.S4_9.table.semigroup.eval
        (fun _ => (3 : Fin 4)) word =
      shortLengthState word.toList.length := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil => rfl
      | cons second rest =>
          cases rest with
          | nil => rfl
          | cons third suffix =>
              change
                threeNilpotentFour.semigroup.eval
                    (fun _ => (3 : Fin 4))
                    (wordOfCons head (second :: third :: suffix)) = _
              have evaluated :
                  threeNilpotentFour.semigroup.eval
                      (fun _ => (3 : Fin 4))
                      (wordOfCons head (second :: third :: suffix)) =
                        (0 : Fin 4) :=
                threeNilpotentEval_long
                  (fun _ => (3 : Fin 4)) head second third suffix
              rw [evaluated]
              simp [shortLengthState, Word.toList]

private theorem shortLengthState_injective
    {left right : Nat} (leftPositive : 0 < left)
    (rightPositive : 0 < right)
    (equal : shortLengthState left = shortLengthState right) :
    min left 3 = min right 3 := by
  have values := congrArg Fin.val equal
  by_cases leftOne : left = 1
  · subst left
    by_cases rightOne : right = 1
    · subst right
      rfl
    · by_cases rightTwo : right = 2
      · subst right
        simp [shortLengthState] at values
        omega
      · simp [shortLengthState, rightOne, rightTwo] at values
  · by_cases leftTwo : left = 2
    · subst left
      by_cases rightOne : right = 1
      · subst right
        simp [shortLengthState] at values
        omega
      · by_cases rightTwo : right = 2
        · subst right
          rfl
        · simp [shortLengthState, rightOne, rightTwo] at values
    · have leftLong : 3 ≤ left := by omega
      by_cases rightOne : right = 1
      · subst right
        simp [shortLengthState, leftOne, leftTwo] at values
        omega
      · by_cases rightTwo : right = 2
        · subst right
          simp [shortLengthState, leftOne, leftTwo] at values
        · have rightLong : 3 ≤ right := by omega
          simp [Nat.min_eq_right leftLong,
            Nat.min_eq_right rightLong]

private theorem s4_9_valid_capped_length
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemigroupBasis.Generated.S4_9.table.semigroup) :
    min identity.lhs.toList.length 3 =
      min identity.rhs.toList.length 3 := by
  have evaluated := valid (fun _ => (3 : Fin 4))
  rw [s4_9_eval_constant_three,
    s4_9_eval_constant_three] at evaluated
  exact shortLengthState_injective
    (by cases identity.lhs; simp [Word.toList])
    (by cases identity.rhs; simp [Word.toList]) evaluated

private theorem exactBasisClass_of_factor_valid
    (identity : Identity Nat)
    (multiplicityValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S3_8.table.semigroup)
    (shortValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S4_9.table.semigroup) :
    ExactBasisClass identity.lhs identity.rhs := by
  have capped := exponentValid_capped_count_eq identity <| by
    simpa [SemigroupBasis.Generated.S3_8.table,
      commutativeExponentThree] using multiplicityValid
  have support := support_of_capped_count_eq capped
  have cappedLength := s4_9_valid_capped_length identity shortValid
  have leftPositive : 0 < identity.lhs.toList.length := by
    cases identity.lhs
    simp [Word.toList]
  have rightPositive : 0 < identity.rhs.toList.length := by
    cases identity.rhs
    simp [Word.toList]
  by_cases leftOne : identity.lhs.toList.length = 1
  · have rightOne : identity.rhs.toList.length = 1 := by omega
    exact Or.inl <|
      SemigroupBasis.CoRoots.S5_55.lengthOne_eq_of_support
        identity.lhs identity.rhs leftOne rightOne support
  · by_cases leftTwo : identity.lhs.toList.length = 2
    · have rightTwo : identity.rhs.toList.length = 2 := by omega
      have orderNe :
          SemigroupBasis.Generated.S4_9.table.mul
              ⟨3, by decide⟩ ⟨2, by decide⟩ ≠
            SemigroupBasis.Generated.S4_9.table.mul
              ⟨2, by decide⟩ ⟨3, by decide⟩ := by decide
      exact Or.inl <|
        SemigroupBasis.CoRoots.S5_55.validLengthTwo_eq_of_support_and_order
          SemigroupBasis.Generated.S4_9.table
          ⟨3, by decide⟩ ⟨2, by decide⟩ orderNe
          identity shortValid support leftTwo rightTwo
    · have leftLong : 3 ≤ identity.lhs.toList.length := by omega
      have rightLong : 3 ≤ identity.rhs.toList.length := by omega
      exact Or.inr ⟨leftLong, rightLong, capped⟩

/-- Complete unrestricted normal-form theorem. It is not a bounded-rank
claim: it quantifies over all `Nat`-variable identities. -/
theorem derives_iff_exactBasisClass {left right : Word Nat} :
    Derives basis left right ↔ ExactBasisClass left right := by
  constructor
  · intro derivation
    let identity : Identity Nat := ⟨left, right⟩
    have multiplicityValid : identity.SatisfiedBy
        SemigroupBasis.Generated.S3_8.table.semigroup := by
      intro valuation
      exact Derives.sound s3_8_models derivation valuation
    have shortValid : identity.SatisfiedBy
        SemigroupBasis.Generated.S4_9.table.semigroup := by
      intro valuation
      exact Derives.sound s4_9_models derivation valuation
    exact exactBasisClass_of_factor_valid
      identity multiplicityValid shortValid
  · intro same
    rcases same with equal | ⟨leftLong, rightLong, capped⟩
    · subst right
      exact Derives.refl _
    · exact derivesLongOfCappedCountEq
        left right leftLong rightLong capped

/-- Deterministic unrestricted normal form: words below length three remain
literal, while every longer word is represented by its sorted multiplicity
list with each count capped at two. -/
theorem derives_iff_sortedCappedNormalForm {left right : Word Nat} :
    Derives basis left right ↔
      left = right ∨
        (3 ≤ left.toList.length ∧
          3 ≤ right.toList.length ∧
          sortedCappedList left.toList =
            sortedCappedList right.toList) := by
  constructor
  · intro derivation
    rcases derives_iff_exactBasisClass.mp derivation with
      equal | ⟨leftLong, rightLong, capped⟩
    · exact Or.inl equal
    · exact Or.inr
        ⟨leftLong, rightLong,
          sortedCappedList_eq_of_capped_count_eq capped⟩
  · rintro (equal | ⟨leftLong, rightLong, sorted⟩)
    · subst right
      exact Derives.refl _
    · apply derivesLongOfCappedCountEq
        left right leftLong rightLong
      intro letter
      have countEqual := congrArg
        (fun letters : List Nat => letters.count letter) sorted
      change
        (sortedCappedList left.toList).count letter =
          (sortedCappedList right.toList).count letter at countEqual
      rw [sortedCappedList_count,
        sortedCappedList_count] at countEqual
      exact countEqual

/-- The six laws form a basis for the intersection of the multiplicity
factor `S3_8` and the ordered-short-word factor `S4_9`. -/
theorem intersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.S4_9.table.semigroup basis where
  leftModels := s3_8_models
  rightModels := s4_9_models
  complete := by
    intro identity multiplicityValid shortValid
    exact derives_iff_exactBasisClass.mpr <|
      exactBasisClass_of_factor_valid
        identity multiplicityValid shortValid

/-- `S4_9` and `S4_35` have the same unrestricted identity theory because
the already sealed lower-order library gives both the same complete basis. -/
theorem s4_9_s4_35_sameIdentityTheory
    (identity : Identity Nat) :
    identity.SatisfiedBy SemigroupBasis.Generated.S4_9.table.semigroup ↔
      identity.SatisfiedBy
        SemigroupBasis.Generated.S4_35.table.semigroup := by
  constructor
  · intro valid
    have derivation :=
      SemigroupBasis.Generated.S4_9.representative_basis.2 identity valid
    intro valuation
    exact Derives.sound
      SemigroupBasis.Generated.S4_35.representative_basis.1
      derivation valuation
  · intro valid
    have derivation :=
      SemigroupBasis.Generated.S4_35.representative_basis.2 identity valid
    intro valuation
    exact Derives.sound
      SemigroupBasis.Generated.S4_9.representative_basis.1
      derivation valuation

/-- The same intersection theorem with `S4_35` as the short-word factor. -/
theorem intersectionBasisS4_35 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.S4_35.table.semigroup basis where
  leftModels := s3_8_models
  rightModels := s4_35_models
  complete := by
    intro identity multiplicityValid shortValid
    exact intersectionBasis.complete identity multiplicityValid
      ((s4_9_s4_35_sameIdentityTheory identity).mpr shortValid)

end SemigroupBasis.CoRoots.Order6ShortWordMultiplicityJoin
