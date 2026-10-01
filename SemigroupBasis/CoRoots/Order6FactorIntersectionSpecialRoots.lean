import SemigroupBasis.CoRoots.S5_1007Family
import SemigroupBasis.CoRoots.S5_505Family
import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.Examples.CommutativePeriodThreeFromTwoOrderFive
import SemigroupBasis.Examples.FinalMarkerThree
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Subdirect

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6FactorIntersectionSpecialRoots

open SemigroupBasis
open SemigroupBasis.Examples

namespace Common

private def instantiateThreeWords
    (u v q : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => q
  | n + 3 => Word.singleton (n + 3)

private def instantiateTwoWords
    (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

/-- Move three displayed letters from the front of a list to its end. -/
theorem permThreeToEnd (a b c : Nat) (rest : List Nat) :
    (a :: b :: c :: rest).Perm (rest ++ [a, b, c]) := by
  rw [List.perm_iff_count]
  intro z
  simp only [List.count_cons, List.count_append, List.count_nil]
  omega

/-- Remove `copies` occurrences of `letter`. -/
def eraseCopies (letter : Nat) : Nat → List Nat → List Nat
  | 0, letters => letters
  | copies + 1, letters =>
      eraseCopies letter copies (letters.erase letter)

theorem erase_eraseCopies (letter copies : Nat) (letters : List Nat) :
    (eraseCopies letter copies letters).erase letter =
      eraseCopies letter (copies + 1) letters := by
  induction copies generalizing letters with
  | zero => rfl
  | succ copies ih =>
      rw [eraseCopies, ih]
      rfl

theorem count_eraseCopies_of_ne
    {tested letter : Nat} (different : tested ≠ letter)
    (copies : Nat) (letters : List Nat) :
    (eraseCopies letter copies letters).count tested =
      letters.count tested := by
  induction copies generalizing letters with
  | zero => simp [eraseCopies]
  | succ copies ih =>
      rw [eraseCopies, ih, List.count_erase_of_ne]
      exact different

theorem count_replicate_of_ne
    {tested letter : Nat} (different : tested ≠ letter) :
    ∀ copies : Nat,
      (List.replicate copies letter).count tested = 0
  | 0 => rfl
  | copies + 1 => by
      rw [List.replicate_succ,
        List.count_cons_of_ne (Ne.symm different),
        count_replicate_of_ne different copies]

theorem count_eraseCopies_self
    (letter : Nat) (copies : Nat) (letters : List Nat)
    (enough : copies ≤ letters.count letter) :
    (eraseCopies letter copies letters).count letter =
      letters.count letter - copies := by
  induction copies generalizing letters with
  | zero => simp [eraseCopies]
  | succ copies ih =>
      have present : letter ∈ letters :=
        List.count_pos_iff.mp (by omega)
      rw [eraseCopies, ih]
      · rw [List.count_erase_self]
        omega
      · rw [List.count_erase_self]
        omega

theorem perm_extractCopies
    (letter : Nat) (copies : Nat) (letters : List Nat)
    (exactCount : letters.count letter = copies) :
    letters.Perm
      (List.replicate copies letter ++
        eraseCopies letter copies letters) := by
  induction copies generalizing letters with
  | zero =>
      simpa [eraseCopies] using List.Perm.refl letters
  | succ copies ih =>
      have present : letter ∈ letters :=
        List.count_pos_iff.mp (by omega)
      have erasedCount : (letters.erase letter).count letter = copies := by
        rw [List.count_erase_self]
        omega
      exact (List.perm_cons_erase present).trans <| by
        simpa [eraseCopies, List.replicate_succ] using
          List.Perm.cons letter (ih (letters.erase letter) erasedCount)

theorem eraseCopies_perm_cons
    (letter : Nat) (copies : Nat) (letters : List Nat)
    (remaining : copies < letters.count letter) :
    (eraseCopies letter copies letters).Perm
      (letter :: eraseCopies letter (copies + 1) letters) := by
  have positive :
      0 < (eraseCopies letter copies letters).count letter := by
    rw [count_eraseCopies_self letter copies letters (by omega)]
    omega
  have present : letter ∈ eraseCopies letter copies letters :=
    List.count_pos_iff.mp positive
  simpa [erase_eraseCopies] using List.perm_cons_erase present

/-- Lift a permutation of the prefix while retaining a fixed final letter.
The caller supplies the three-variable prefix-swap law. -/
theorem derivesPrefixPermutation
    {basis : List (Identity Nat)}
    (prefixSwap : ∀ u v q : Word Nat,
      Derives basis ((u ++ v) ++ q) ((v ++ u) ++ q))
    {left right : List Nat} (permutation : left.Perm right)
    (final : Nat) :
    Derives basis
      (wordOfPrefixFinal left final)
      (wordOfPrefixFinal right final) := by
  induction permutation with
  | nil =>
      exact Derives.refl _
  | cons head _ ih =>
      simpa [wordOfPrefixFinal] using
        Derives.prepend (Word.singleton head) ih
  | swap left right suffix =>
      simpa [wordOfPrefixFinal, Word.append_assoc] using
        prefixSwap (Word.singleton right) (Word.singleton left)
          (wordOfPrefixFinal suffix final)
  | trans _ _ ihFirst ihSecond =>
      exact Derives.trans ihFirst ihSecond

/-- Split a nonempty prefix from an appended suffix in the canonical
prefix/final word representation. -/
theorem wordOfPrefixFinal_cons_append
    (head : Nat) (front suffix : List Nat) (final : Nat) :
    wordOfPrefixFinal ((head :: front) ++ suffix) final =
      SemigroupBasis.CoRoots.S5_107.listWordOfCons head front ++
        wordOfPrefixFinal suffix final := by
  apply Word.toList_injective
  rw [toList_wordOfPrefixFinal, Word.toList_append,
    toList_wordOfPrefixFinal]
  change ((head :: front) ++ suffix) ++ [final] =
    (head :: front) ++ (suffix ++ [final])
  rw [List.append_assoc]

/-- A basis law `xyz = yxz` gives arbitrary adjacent prefix swaps. -/
theorem derivesPrefixSwap
    {basis : List (Identity Nat)}
    {xyz yxz : Word Nat}
    (xyzDef : xyz = ⟨0, [1, 2]⟩)
    (yxzDef : yxz = ⟨1, [0, 2]⟩)
    (member : (⟨xyz, yxz⟩ : Identity Nat) ∈ basis)
    (u v q : Word Nat) :
    Derives basis ((u ++ v) ++ q) ((v ++ u) ++ q) := by
  have base : Derives basis xyz yxz :=
    Derives.fromBasis member
  have substituted :=
    Derives.subst base (instantiateThreeWords u v q)
  subst xyz
  subst yxz
  simpa [instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Instantiate `xxyy = xyyx` on two nonempty blocks. -/
theorem derivesRepeatedFinalSwitch
    {basis : List (Identity Nat)}
    {xxyy xyyx : Word Nat}
    (xxyyDef : xxyy = ⟨0, [0, 1, 1]⟩)
    (xyyxDef : xyyx = ⟨0, [1, 1, 0]⟩)
    (member : (⟨xxyy, xyyx⟩ : Identity Nat) ∈ basis)
    (u v : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ v)
      (((u ++ v) ++ v) ++ u) := by
  have base : Derives basis xxyy xyyx :=
    Derives.fromBasis member
  have substituted :=
    Derives.subst base (instantiateTwoWords u v)
  subst xxyy
  subst xyyx
  simpa [instantiateTwoWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Switch a repeated final from `oldFinal` to `newFinal`. The output prefix
is explicit and the full words are permutations of one another. -/
theorem switchRepeatedFinal
    {basis : List (Identity Nat)}
    (prefixSwap : ∀ u v q : Word Nat,
      Derives basis ((u ++ v) ++ q) ((v ++ u) ++ q))
    (terminalSwitch : ∀ u v : Word Nat,
      Derives basis (((u ++ u) ++ v) ++ v)
        (((u ++ v) ++ v) ++ u))
    (letters : List Nat) (oldFinal newFinal : Nat)
    (oldIn : oldFinal ∈ letters)
    (twoNew : 2 ≤ letters.count newFinal) :
    ∃ switchedPrefix,
      Derives basis
        (wordOfPrefixFinal letters oldFinal)
        (wordOfPrefixFinal switchedPrefix newFinal) ∧
      (letters ++ [oldFinal]).Perm
        (switchedPrefix ++ [newFinal]) ∧
      newFinal ∈ switchedPrefix := by
  by_cases same : oldFinal = newFinal
  · subst newFinal
    exact ⟨letters, Derives.refl _, List.Perm.refl _, oldIn⟩
  · have firstNew : newFinal ∈ letters :=
      List.count_pos_iff.mp (by omega)
    have secondNewCount :
        (letters.erase newFinal).count newFinal =
          letters.count newFinal - 1 := by
      rw [List.count_erase_self]
    have secondNew : newFinal ∈ letters.erase newFinal :=
      List.count_pos_iff.mp (by omega)
    have oldAfterFirst :
        (letters.erase newFinal).count oldFinal =
          letters.count oldFinal := by
      rw [List.count_erase_of_ne]
      exact same
    have oldAfterSecond :
        ((letters.erase newFinal).erase newFinal).count oldFinal =
          letters.count oldFinal := by
      rw [List.count_erase_of_ne, oldAfterFirst]
      exact same
    have oldAfter :
        oldFinal ∈ (letters.erase newFinal).erase newFinal :=
      List.count_pos_iff.mp <| by
        rw [oldAfterSecond]
        exact List.count_pos_iff.mpr oldIn
    let rest :=
      ((letters.erase newFinal).erase newFinal).erase oldFinal
    have arrangeFront :
        letters.Perm (newFinal :: newFinal :: oldFinal :: rest) := by
      exact (List.perm_cons_erase firstNew).trans <|
        List.Perm.cons newFinal <|
          (List.perm_cons_erase secondNew).trans <|
            List.Perm.cons newFinal <| by
              simpa [rest] using List.perm_cons_erase oldAfter
    have arrange :
        letters.Perm (rest ++ [newFinal, newFinal, oldFinal]) :=
      arrangeFront.trans (permThreeToEnd _ _ _ rest)
    have arranged := derivesPrefixPermutation prefixSwap arrange oldFinal
    have atEnd :
        Derives basis
          (wordOfPrefixFinal
            (rest ++ [newFinal, newFinal, oldFinal]) oldFinal)
          (wordOfPrefixFinal
            (rest ++ [newFinal, oldFinal, oldFinal]) newFinal) := by
      cases rest with
      | nil =>
          simpa [wordOfPrefixFinal,
            Word.append, Word.singleton, Word.append_assoc] using
              terminalSwitch (Word.singleton newFinal)
                (Word.singleton oldFinal)
      | cons head tail =>
          have contextual :=
            Derives.prepend
              (SemigroupBasis.CoRoots.S5_107.listWordOfCons head tail)
              (terminalSwitch (Word.singleton newFinal)
                (Word.singleton oldFinal))
          rw [wordOfPrefixFinal_cons_append,
            wordOfPrefixFinal_cons_append]
          simpa [wordOfPrefixFinal,
            SemigroupBasis.CoRoots.S5_107.listWordOfCons,
            Word.append, Word.singleton, Word.append_assoc,
            List.append_assoc] using contextual
    let switchedPrefix := rest ++ [newFinal, oldFinal, oldFinal]
    have arrangedWords :
        Derives basis
          (wordOfPrefixFinal letters oldFinal)
          (wordOfPrefixFinal
            (rest ++ [newFinal, newFinal, oldFinal]) oldFinal) :=
      arranged
    have fullPermutation :
        (letters ++ [oldFinal]).Perm
          (switchedPrefix ++ [newFinal]) := by
      have appended := arrange.append_right [oldFinal]
      have suffixPermutation :
          [newFinal, newFinal, oldFinal, oldFinal].Perm
            [newFinal, oldFinal, oldFinal, newFinal] := by
        rw [List.perm_iff_count]
        intro z
        simp only [List.count_cons, List.count_nil]
        omega
      exact appended.trans <| by
        simpa [switchedPrefix, List.append_assoc] using
          List.Perm.append_left rest suffixPermutation
    exact ⟨switchedPrefix, arrangedWords.trans atEnd,
      fullPermutation, by simp [switchedPrefix]⟩

def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

end Common

namespace IndexTwoPeriodThree

open Common

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxxxx : Word Nat := w 0 [0, 0, 0, 0]
def xxyy : Word Nat := w 0 [0, 1, 1]
def xyyx : Word Nat := w 0 [1, 1, 0]
def xyx : Word Nat := w 0 [1, 0]
def yxx : Word Nat := w 1 [0, 0]
def xyz : Word Nat := w 0 [1, 2]
def yxz : Word Nat := w 1 [0, 2]

def powerLaw : Identity Nat := ⟨xx, xxxxx⟩
def repeatedFinalLaw : Identity Nat := ⟨xxyy, xyyx⟩
def rotateLaw : Identity Nat := ⟨xyx, yxx⟩
def prefixCommutationLaw : Identity Nat := ⟨xyz, yxz⟩

/-- The representative-orientation basis from the final-index-two,
period-three contract. -/
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

theorem fiveToTwo (u : Word Nat) :
    Derives basis ((((u ++ u) ++ u) ++ u) ++ u) (u ++ u) := by
  have base : Derives basis xxxxx xx :=
    Derives.symm <| Derives.fromBasis (e := powerLaw) <|
      List.Mem.head _
  have substituted := Derives.subst base (instantiateOneWord u)
  simpa [basis, powerLaw, xxxxx, xx, w, instantiateOneWord,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Prefix state for the variable which is also retained as the final
letter. Its total exponent state is one larger. -/
def finalPrefixExponent (n : Nat) : Nat :=
  periodThreeFromTwoExponent (n + 1) - 1

theorem finalPrefixExponent_succ (n : Nat) :
    finalPrefixExponent (n + 1) =
      if finalPrefixExponent n < 3 then
        finalPrefixExponent n + 1
      else
        finalPrefixExponent n - 2 := by
  unfold finalPrefixExponent
  rw [periodThreeFromTwoExponent_succ]
  have positive : 0 < periodThreeFromTwoExponent (n + 1) :=
    periodThreeFromTwoExponent_pos (by omega)
  split <;> rename_i exponentCase
  · have prefixCase :
        periodThreeFromTwoExponent (n + 1) - 1 < 3 := by
      omega
    rw [if_pos prefixCase]
    omega
  · have prefixCase :
        ¬ periodThreeFromTwoExponent (n + 1) - 1 < 3 := by
      omega
    rw [if_neg prefixCase]
    omega

def prefixState (final letter count : Nat) : Nat :=
  if letter = final then finalPrefixExponent count
  else periodThreeFromTwoExponent count

def prefixCap (final letter : Nat) : Nat :=
  if letter = final then 3 else 4

theorem prefixState_succ (final letter count : Nat) :
    prefixState final letter (count + 1) =
      if prefixState final letter count < prefixCap final letter then
        prefixState final letter count + 1
      else
        prefixState final letter count - 2 := by
  by_cases same : letter = final
  · simp [prefixState, prefixCap, same, finalPrefixExponent_succ]
  · simp [prefixState, prefixCap, same,
      periodThreeFromTwoExponent_succ]

private theorem periodThreeFromTwoExponent_le_four (n : Nat) :
    periodThreeFromTwoExponent n ≤ 4 := by
  unfold periodThreeFromTwoExponent
  split
  · omega
  · have bound : (n + 1) % 3 < 3 := Nat.mod_lt _ (by omega)
    omega

theorem prefixState_le_cap (final letter count : Nat) :
    prefixState final letter count ≤ prefixCap final letter := by
  by_cases same : letter = final
  · have positive : 0 < periodThreeFromTwoExponent (count + 1) :=
      periodThreeFromTwoExponent_pos (by omega)
    have upper := periodThreeFromTwoExponent_le_four (count + 1)
    simp [prefixState, prefixCap, same, finalPrefixExponent]
    omega
  · simp [prefixState, prefixCap, same]
    exact periodThreeFromTwoExponent_le_four count

/-- Reduce nonfinal multiplicities to states one through four, and the
retained final's prefix multiplicity to states one through three. -/
def prefixReduce (final : Nat) : List Nat → List Nat
  | [] => []
  | letter :: rest =>
      let reduced := prefixReduce final rest
      if reduced.count letter < prefixCap final letter then
        letter :: reduced
      else
        (reduced.erase letter).erase letter

theorem count_prefixReduce (final letter : Nat) (letters : List Nat) :
    (prefixReduce final letters).count letter =
      prefixState final letter (letters.count letter) := by
  induction letters with
  | nil =>
      simp [prefixReduce, prefixState, finalPrefixExponent,
        periodThreeFromTwoExponent]
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
          rw [List.count_erase_self, List.count_erase_self,
            List.count_cons_self, ih]
          rw [ih] at countCase
          rw [prefixState_succ, if_neg countCase]
          have upper := prefixState_le_cap final letter (tail.count letter)
          omega
        · rw [List.count_erase_of_ne same,
            List.count_erase_of_ne same,
            List.count_cons_of_ne (Ne.symm same), ih]

theorem prefixReduce_perm_of_totalExponent_eq
    (final : Nat) {left right : List Nat}
    (total : ∀ letter,
      periodThreeFromTwoExponent
          ((left ++ [final]).count letter) =
        periodThreeFromTwoExponent
          ((right ++ [final]).count letter)) :
    (prefixReduce final left).Perm (prefixReduce final right) := by
  rw [List.perm_iff_count]
  intro letter
  rw [count_prefixReduce, count_prefixReduce]
  by_cases same : letter = final
  · subst letter
    have equality := total final
    simp only [prefixState, if_pos rfl, finalPrefixExponent]
    apply congrArg (fun value : Nat => value - 1)
    simpa [List.count_append] using equality
  · have equality := total letter
    simp only [prefixState, if_neg same]
    simpa [List.count_append, Ne.symm same] using equality

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
        have next :
            prefixReduce final (head :: tail) =
              (reduced.erase head).erase head := by
          simp [prefixReduce, reduced, below]
        by_cases isFinal : head = final
        · subst final
          have countThree : reduced.count head = 3 := by
            simpa [prefixCap] using exactCount
          let remainder := eraseCopies head 3 reduced
          have extracted :
              reduced.Perm
                (List.replicate 3 head ++ remainder) := by
            simpa [remainder] using
              perm_extractCopies head 3 reduced countThree
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
            intro z
            rw [List.count_append, List.count_append, Nat.add_comm]
          have arranged :=
            Common.derivesPrefixPermutation prefixSwap arrangeEnd head
          have contraction :
              Derives basis
                (wordOfPrefixFinal
                  (remainder ++ List.replicate 4 head) head)
                (wordOfPrefixFinal (remainder ++ [head]) head) := by
            cases remainder with
            | nil =>
                simpa [wordOfPrefixFinal, List.replicate_succ,
                  Word.append, Word.singleton, Word.append_assoc] using
                    fiveToTwo (Word.singleton head)
            | cons first rest =>
                have contextual :=
                  Derives.prepend
                    (SemigroupBasis.CoRoots.S5_107.listWordOfCons
                      first rest)
                    (fiveToTwo (Word.singleton head))
                rw [wordOfPrefixFinal_cons_append,
                  wordOfPrefixFinal_cons_append]
                simpa [wordOfPrefixFinal, List.replicate_succ,
                  Word.append, Word.singleton, Word.append_assoc,
                  List.append_assoc] using contextual
          have restorePerm :
              (remainder ++ [head]).Perm
                ((reduced.erase head).erase head) := by
            dsimp [remainder]
            rw [List.perm_iff_count]
            intro z
            rw [List.count_append]
            by_cases same : z = head
            · subst z
              rw [List.count_erase_self, List.count_erase_self,
                countThree]
              rw [count_eraseCopies_self head 3 reduced (by omega)]
              simp [List.count_append]
              omega
            · rw [List.count_erase_of_ne same,
                List.count_erase_of_ne same,
                count_eraseCopies_of_ne same]
              simp [List.count_append, same, Ne.symm same]
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
          let remainder := eraseCopies head 4 reduced
          have extracted :
              reduced.Perm
                (List.replicate 4 head ++ remainder) := by
            simpa [remainder] using
              perm_extractCopies head 4 reduced countFour
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
                  (List.replicate 2 head ++ remainder) final) := by
            have contextual :=
              Derives.appendRight
                (fiveToTwo (Word.singleton head))
                (wordOfPrefixFinal remainder final)
            simpa [wordOfPrefixFinal, List.replicate_succ,
              Word.append_assoc, List.append_assoc] using contextual
          have restorePerm :
              (List.replicate 2 head ++ remainder).Perm
                ((reduced.erase head).erase head) := by
            rw [List.perm_iff_count]
            intro z
            by_cases same : z = head
            · subst z
              rw [List.count_append,
                List.count_replicate_self,
                List.count_erase_self, List.count_erase_self,
                countFour]
              rw [count_eraseCopies_self head 4 reduced (by omega)]
              omega
            · rw [List.count_append,
                count_replicate_of_ne same,
                Nat.zero_add, List.count_erase_of_ne same,
                List.count_erase_of_ne same,
                count_eraseCopies_of_ne same]
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

theorem exponentModels :
    Models s5_1001.semigroup basis :=
  FiniteCertificate.checkModels_sound
    s5_1001 basis Common.toFinThree (by decide)

theorem derivesSameFinal
    (leftPrefix rightPrefix : List Nat) (final : Nat)
    (valid :
      (⟨wordOfPrefixFinal leftPrefix final,
          wordOfPrefixFinal rightPrefix final⟩ : Identity Nat).SatisfiedBy
        s5_1001.semigroup) :
    Derives basis
      (wordOfPrefixFinal leftPrefix final)
      (wordOfPrefixFinal rightPrefix final) := by
  let identity : Identity Nat :=
    ⟨wordOfPrefixFinal leftPrefix final,
      wordOfPrefixFinal rightPrefix final⟩
  have total : ∀ letter,
      periodThreeFromTwoExponent
          ((leftPrefix ++ [final]).count letter) =
        periodThreeFromTwoExponent
          ((rightPrefix ++ [final]).count letter) := by
    intro letter
    have separated := s5_1001Separates identity valid letter
    simpa [identity, toList_wordOfPrefixFinal] using separated
  have normalPermutation :=
    prefixReduce_perm_of_totalExponent_eq final total
  exact (derivesNormalPrefix leftPrefix final).trans <|
    (Common.derivesPrefixPermutation prefixSwap normalPermutation final).trans <|
      (derivesNormalPrefix rightPrefix final).symm

private theorem exponent_ge_two {count : Nat} (atLeast : 2 ≤ count) :
    2 ≤ periodThreeFromTwoExponent count := by
  unfold periodThreeFromTwoExponent
  rw [if_neg (by omega)]
  omega

private theorem count_ge_two_of_exponent_eq
    {leftCount rightCount : Nat}
    (equalState :
      periodThreeFromTwoExponent leftCount =
        periodThreeFromTwoExponent rightCount)
    (rightAtLeast : 2 ≤ rightCount) :
    2 ≤ leftCount := by
  apply Decidable.byContradiction
  intro tooSmall
  have rightState := exponent_ge_two rightAtLeast
  have leftState : periodThreeFromTwoExponent leftCount = leftCount := by
    unfold periodThreeFromTwoExponent
    rw [if_pos (by omega)]
  omega

/-- Unrestricted completeness of the displayed four laws for the exact
intersection `Id(S3_6) ∩ Id(S5_1001)`. -/
theorem derives_of_factor_valid (identity : Identity Nat)
    (markerValid : identity.SatisfiedBy finalMarkerThree.semigroup)
    (exponentValid : identity.SatisfiedBy s5_1001.semigroup) :
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
          Identity Nat).SatisfiedBy s5_1001.semigroup := by
      simpa only [leftReconstruct, rightReconstructSame] using exponentValid
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
    have stateEquality := s5_1001Separates identity exponentValid rightSplit.2
    have rightAtLeast :
        2 ≤ identity.rhs.toList.count rightSplit.2 := by
      rw [← rightReconstruct, toList_wordOfPrefixFinal,
        List.count_append]
      have positive := List.count_pos_iff.mpr newRepeated
      simp
      omega
    have leftAtLeast :
        2 ≤ identity.lhs.toList.count rightSplit.2 :=
      count_ge_two_of_exponent_eq stateEquality rightAtLeast
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
          Identity Nat).SatisfiedBy s5_1001.semigroup := by
      intro valuation
      have switchSound := switchDerivation.sound exponentModels valuation
      have original := exponentValid valuation
      rw [← leftReconstruct, ← rightReconstruct] at original
      exact switchSound.symm.trans original
    have aligned :=
      derivesSameFinal switchedPrefix rightSplit.1 rightSplit.2 alignedValid
    rw [← leftReconstruct, ← rightReconstruct]
    exact switchDerivation.trans aligned

def intersectionBasis :
    IntersectionBasis finalMarkerThree.semigroup
      s5_1001.semigroup basis where
  leftModels := markerModels
  rightModels := exponentModels
  complete := derives_of_factor_valid

end IndexTwoPeriodThree

namespace PrefixResidueSix

open Common

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xy : Word Nat := w 0 [1]
def xxxxxxxY : Word Nat := w 0 [0, 0, 0, 0, 0, 0, 1]
def xyx : Word Nat := w 0 [1, 0]
def yxx : Word Nat := w 1 [0, 0]
def xxyy : Word Nat := w 0 [0, 1, 1]
def xyyx : Word Nat := w 0 [1, 1, 0]
def xyz : Word Nat := w 0 [1, 2]
def yxz : Word Nat := w 1 [0, 2]

def contextualPowerLaw : Identity Nat := ⟨xy, xxxxxxxY⟩
def rotateLaw : Identity Nat := ⟨xyx, yxx⟩
def repeatedFinalLaw : Identity Nat := ⟨xxyy, xyyx⟩
def prefixCommutationLaw : Identity Nat := ⟨xyz, yxz⟩

/-- Period-six representative basis from the prefix-residue-final contract. -/
def basis : List (Identity Nat) :=
  [contextualPowerLaw, rotateLaw,
    repeatedFinalLaw, prefixCommutationLaw]

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
  exact List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _

private def instantiateTwoWords
    (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

theorem oneToSevenBefore (u suffix : Word Nat) :
    Derives basis (u ++ suffix)
      (((((((u ++ u) ++ u) ++ u) ++ u) ++ u) ++ u) ++ suffix) := by
  have base : Derives basis xy xxxxxxxY :=
    Derives.fromBasis (e := contextualPowerLaw) <| List.Mem.head _
  have substituted :=
    Derives.subst base (instantiateTwoWords u suffix)
  simpa [basis, contextualPowerLaw, xy, xxxxxxxY, w,
    instantiateTwoWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem sevenToOneBefore (u suffix : Word Nat) :
    Derives basis
      (((((((u ++ u) ++ u) ++ u) ++ u) ++ u) ++ u) ++ suffix)
      (u ++ suffix) :=
  (oneToSevenBefore u suffix).symm

theorem derivesNormalPrefix :
    ∀ (letters : List Nat) (final : Nat),
      Derives basis
        (wordOfPrefixFinal letters final)
        (wordOfPrefixFinal (positiveModSixReduce letters) final)
  | [], final => Derives.refl _
  | head :: tail, final => by
      have tailNormal := derivesNormalPrefix tail final
      have prefixed :=
        Derives.prepend (Word.singleton head) tailNormal
      let reduced := positiveModSixReduce tail
      by_cases below : reduced.count head < 6
      · have next :
            positiveModSixReduce (head :: tail) = head :: reduced := by
          simp [positiveModSixReduce, reduced, below]
        rw [next]
        simpa [wordOfPrefixFinal, reduced] using prefixed
      · have upper : reduced.count head ≤ 6 := by
          simpa [reduced] using
            positiveModSixReduce_count_le_six head tail
        have countSix : reduced.count head = 6 := by omega
        let remainder := eraseCopies head 6 reduced
        have extracted :
            reduced.Perm
              (List.replicate 6 head ++ remainder) := by
          simpa [remainder] using
            perm_extractCopies head 6 reduced countSix
        have arrange :
            (head :: reduced).Perm
              (List.replicate 7 head ++ remainder) := by
          simpa [List.replicate_succ] using
            List.Perm.cons head extracted
        have arranged :=
          Common.derivesPrefixPermutation prefixSwap arrange final
        have contraction :
            Derives basis
              (wordOfPrefixFinal
                (List.replicate 7 head ++ remainder) final)
              (wordOfPrefixFinal (head :: remainder) final) := by
          simpa [wordOfPrefixFinal, List.replicate_succ,
            Word.append, Word.singleton, Word.append_assoc,
            List.append_assoc] using
              sevenToOneBefore (Word.singleton head)
                (wordOfPrefixFinal remainder final)
        have target :
            positiveModSixReduce (head :: tail) =
              eraseCopies head 5 reduced := by
          simp [positiveModSixReduce, reduced, below,
            eraseCopies]
        have restorePerm :
            (head :: remainder).Perm
              (eraseCopies head 5 reduced) := by
          have extractedLast :=
            eraseCopies_perm_cons head 5 reduced (by omega)
          simpa [remainder] using extractedLast.symm
        have restore :=
          Common.derivesPrefixPermutation prefixSwap restorePerm final
        rw [target]
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

theorem exponentModels :
    Models S5_1007Family.S5_1007.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    S5_1007Family.S5_1007.table basis Common.toFinThree (by decide)

theorem derivesSameFinal
    (leftPrefix rightPrefix : List Nat) (final : Nat)
    (repeated : final ∈ leftPrefix ↔ final ∈ rightPrefix)
    (valid :
      (⟨wordOfPrefixFinal leftPrefix final,
          wordOfPrefixFinal rightPrefix final⟩ : Identity Nat).SatisfiedBy
        S5_1007Family.S5_1007.table.semigroup) :
    Derives basis
      (wordOfPrefixFinal leftPrefix final)
      (wordOfPrefixFinal rightPrefix final) := by
  let identity : Identity Nat :=
    ⟨wordOfPrefixFinal leftPrefix final,
      wordOfPrefixFinal rightPrefix final⟩
  have fullSupport :=
    S5_1007Family.S5_1007.valid_support identity valid
  have fullMod :=
    S5_1007Family.S5_1007.valid_count_mod_six identity valid
  have prefixSupport : ∀ letter,
      letter ∈ leftPrefix ↔ letter ∈ rightPrefix := by
    intro letter
    by_cases same : letter = final
    · subst letter
      exact repeated
    · have support := fullSupport letter
      simpa [identity, toList_wordOfPrefixFinal,
        List.mem_append, same] using support
  have prefixMod : ∀ letter,
      leftPrefix.count letter % 6 = rightPrefix.count letter % 6 := by
    intro letter
    have equality := fullMod letter
    simp only [identity, toList_wordOfPrefixFinal,
      List.count_append, List.count_cons, List.count_nil,
      Nat.add_zero] at equality
    by_cases same : letter = final
    · subst letter
      omega
    · simpa [Ne.symm same] using equality
  have normalPermutation :=
    positiveModSixReduce_perm prefixSupport prefixMod
  exact (derivesNormalPrefix leftPrefix final).trans <|
    (Common.derivesPrefixPermutation prefixSwap normalPermutation final).trans <|
      (derivesNormalPrefix rightPrefix final).symm

/-- Align two repeated finals. If the requested new final occurs only once
in the prefix, contextual period six first manufactures seven copies. -/
theorem alignRepeatedFinal
    (letters : List Nat) (oldFinal newFinal : Nat)
    (oldIn : oldFinal ∈ letters)
    (newIn : newFinal ∈ letters) :
    ∃ alignedPrefix,
      Derives basis
        (wordOfPrefixFinal letters oldFinal)
        (wordOfPrefixFinal alignedPrefix newFinal) ∧
      newFinal ∈ alignedPrefix := by
  by_cases same : oldFinal = newFinal
  · subst newFinal
    exact ⟨letters, Derives.refl _, oldIn⟩
  · by_cases twoNew : 2 ≤ letters.count newFinal
    · obtain ⟨switched, derivation, _, newRepeated⟩ :=
        Common.switchRepeatedFinal prefixSwap terminalSwitch
          letters oldFinal newFinal oldIn twoNew
      exact ⟨switched, derivation, newRepeated⟩
    · let rest := letters.erase newFinal
      have arrange : letters.Perm (newFinal :: rest) := by
        simpa [rest] using List.perm_cons_erase newIn
      have arranged :=
        Common.derivesPrefixPermutation prefixSwap arrange oldFinal
      let expandedPrefix := List.replicate 7 newFinal ++ rest
      have expand :
          Derives basis
            (wordOfPrefixFinal (newFinal :: rest) oldFinal)
            (wordOfPrefixFinal expandedPrefix oldFinal) := by
        simpa [expandedPrefix, wordOfPrefixFinal,
          List.replicate_succ, Word.append_assoc,
          List.append_assoc] using
            oneToSevenBefore (Word.singleton newFinal)
              (wordOfPrefixFinal rest oldFinal)
      have oldInRest : oldFinal ∈ rest := by
        simpa [rest, List.mem_erase_of_ne same] using oldIn
      have oldInExpanded : oldFinal ∈ expandedPrefix := by
        simp [expandedPrefix, oldInRest]
      have expandedTwo : 2 ≤ expandedPrefix.count newFinal := by
        simp [expandedPrefix]
      obtain ⟨switched, switchedDerivation, _, newRepeated⟩ :=
        Common.switchRepeatedFinal prefixSwap terminalSwitch
          expandedPrefix oldFinal newFinal oldInExpanded expandedTwo
      exact ⟨switched,
        arranged.trans <| expand.trans switchedDerivation,
        newRepeated⟩

/-- Unrestricted completeness of the displayed four laws for the exact
intersection `Id(S3_6) ∩ Id(S5_1007)`. -/
theorem derives_of_factor_valid (identity : Identity Nat)
    (markerValid : identity.SatisfiedBy finalMarkerThree.semigroup)
    (exponentValid : identity.SatisfiedBy
      S5_1007Family.S5_1007.table.semigroup) :
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
    have simpleEquivalence :=
      finalMarkerValid_splitSimpleFinal_iff
        identity markerValid leftSplit.2
    have notMemberEquivalence :
        leftSplit.2 ∉ leftSplit.1 ↔
          leftSplit.2 ∉ rightSplit.1 := by
      change
        (leftSplit.2 = leftSplit.2 ∧ leftSplit.2 ∉ leftSplit.1) ↔
          (rightSplit.2 = leftSplit.2 ∧
            leftSplit.2 ∉ rightSplit.1) at simpleEquivalence
      constructor
      · intro leftSimple
        exact (simpleEquivalence.mp ⟨rfl, leftSimple⟩).2
      · intro rightSimple
        exact (simpleEquivalence.mpr ⟨sameFinal.symm, rightSimple⟩).2
    have repeatedEquivalence :
        leftSplit.2 ∈ leftSplit.1 ↔
          leftSplit.2 ∈ rightSplit.1 := by
      simpa using not_congr notMemberEquivalence
    have sameValid :
        (⟨wordOfPrefixFinal leftSplit.1 leftSplit.2,
            wordOfPrefixFinal rightSplit.1 leftSplit.2⟩ :
          Identity Nat).SatisfiedBy
            S5_1007Family.S5_1007.table.semigroup := by
      simpa only [leftReconstruct, rightReconstructSame] using exponentValid
    rw [← leftReconstruct, ← rightReconstructSame]
    exact derivesSameFinal leftSplit.1 rightSplit.1 leftSplit.2
      repeatedEquivalence sameValid
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
    have fullSupport :=
      S5_1007Family.S5_1007.valid_support identity exponentValid
        rightSplit.2
    have newInLeftWord : rightSplit.2 ∈ identity.lhs.toList :=
      fullSupport.mpr <| by
        rw [← rightReconstruct, toList_wordOfPrefixFinal]
        simp
    have newInLeft : rightSplit.2 ∈ leftSplit.1 := by
      rw [← leftReconstruct, toList_wordOfPrefixFinal] at newInLeftWord
      simpa [sameFinal, Ne.symm sameFinal] using newInLeftWord
    obtain ⟨alignedPrefix, alignment, alignedRepeated⟩ :=
      alignRepeatedFinal leftSplit.1 leftSplit.2 rightSplit.2
        oldRepeated newInLeft
    have alignedExponentValid :
        (⟨wordOfPrefixFinal alignedPrefix rightSplit.2,
            wordOfPrefixFinal rightSplit.1 rightSplit.2⟩ :
          Identity Nat).SatisfiedBy
            S5_1007Family.S5_1007.table.semigroup := by
      intro valuation
      have alignmentSound := alignment.sound exponentModels valuation
      have original := exponentValid valuation
      rw [← leftReconstruct, ← rightReconstruct] at original
      exact alignmentSound.symm.trans original
    have aligned :=
      derivesSameFinal alignedPrefix rightSplit.1 rightSplit.2
        ⟨fun _ => newRepeated, fun _ => alignedRepeated⟩
        alignedExponentValid
    rw [← leftReconstruct, ← rightReconstruct]
    exact alignment.trans aligned

def intersectionBasis :
    IntersectionBasis finalMarkerThree.semigroup
      S5_1007Family.S5_1007.table.semigroup basis where
  leftModels := markerModels
  rightModels := exponentModels
  complete := derives_of_factor_valid

end PrefixResidueSix

namespace PrefixResidueFour

open Common

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xy : Word Nat := w 0 [1]
def xxxxxY : Word Nat := w 0 [0, 0, 0, 0, 1]
def xyx : Word Nat := w 0 [1, 0]
def yxx : Word Nat := w 1 [0, 0]
def xxyy : Word Nat := w 0 [0, 1, 1]
def xyyx : Word Nat := w 0 [1, 1, 0]
def xyz : Word Nat := w 0 [1, 2]
def yxz : Word Nat := w 1 [0, 2]

def contextualPowerLaw : Identity Nat := ⟨xy, xxxxxY⟩
def rotateLaw : Identity Nat := ⟨xyx, yxx⟩
def repeatedFinalLaw : Identity Nat := ⟨xxyy, xyyx⟩
def prefixCommutationLaw : Identity Nat := ⟨xyz, yxz⟩

/-- Period-four representative basis from the prefix-residue-final contract. -/
def basis : List (Identity Nat) :=
  [contextualPowerLaw, rotateLaw,
    repeatedFinalLaw, prefixCommutationLaw]

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
  exact List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _

private def instantiateTwoWords
    (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

theorem oneToFiveBefore (u suffix : Word Nat) :
    Derives basis (u ++ suffix)
      (((((u ++ u) ++ u) ++ u) ++ u) ++ suffix) := by
  have base : Derives basis xy xxxxxY :=
    Derives.fromBasis (e := contextualPowerLaw) <| List.Mem.head _
  have substituted :=
    Derives.subst base (instantiateTwoWords u suffix)
  simpa [basis, contextualPowerLaw, xy, xxxxxY, w,
    instantiateTwoWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem fiveToOneBefore (u suffix : Word Nat) :
    Derives basis
      (((((u ++ u) ++ u) ++ u) ++ u) ++ suffix)
      (u ++ suffix) :=
  (oneToFiveBefore u suffix).symm

theorem derivesNormalPrefix :
    ∀ (letters : List Nat) (final : Nat),
      Derives basis
        (wordOfPrefixFinal letters final)
        (wordOfPrefixFinal (positiveModFourReduce letters) final)
  | [], final => Derives.refl _
  | head :: tail, final => by
      have tailNormal := derivesNormalPrefix tail final
      have prefixed :=
        Derives.prepend (Word.singleton head) tailNormal
      let reduced := positiveModFourReduce tail
      by_cases below : reduced.count head < 4
      · have next :
            positiveModFourReduce (head :: tail) = head :: reduced := by
          simp [positiveModFourReduce, reduced, below]
        rw [next]
        simpa [wordOfPrefixFinal, reduced] using prefixed
      · have upper : reduced.count head ≤ 4 := by
          simpa [reduced] using
            positiveModFourReduce_count_le_four head tail
        have countFour : reduced.count head = 4 := by omega
        let remainder := eraseCopies head 4 reduced
        have extracted :
            reduced.Perm
              (List.replicate 4 head ++ remainder) := by
          simpa [remainder] using
            perm_extractCopies head 4 reduced countFour
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
              (wordOfPrefixFinal (head :: remainder) final) := by
          simpa [wordOfPrefixFinal, List.replicate_succ,
            Word.append, Word.singleton, Word.append_assoc,
            List.append_assoc] using
              fiveToOneBefore (Word.singleton head)
                (wordOfPrefixFinal remainder final)
        have target :
            positiveModFourReduce (head :: tail) =
              eraseCopies head 3 reduced := by
          simp [positiveModFourReduce, reduced, below,
            eraseCopies]
        have restorePerm :
            (head :: remainder).Perm
              (eraseCopies head 3 reduced) := by
          have extractedLast :=
            eraseCopies_perm_cons head 3 reduced (by omega)
          simpa [remainder] using extractedLast.symm
        have restore :=
          Common.derivesPrefixPermutation prefixSwap restorePerm final
        rw [target]
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

theorem exponentModels :
    Models S5_505Family.S5_505.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    S5_505Family.S5_505.table basis Common.toFinThree (by decide)

theorem derivesSameFinal
    (leftPrefix rightPrefix : List Nat) (final : Nat)
    (repeated : final ∈ leftPrefix ↔ final ∈ rightPrefix)
    (valid :
      (⟨wordOfPrefixFinal leftPrefix final,
          wordOfPrefixFinal rightPrefix final⟩ : Identity Nat).SatisfiedBy
        S5_505Family.S5_505.table.semigroup) :
    Derives basis
      (wordOfPrefixFinal leftPrefix final)
      (wordOfPrefixFinal rightPrefix final) := by
  let identity : Identity Nat :=
    ⟨wordOfPrefixFinal leftPrefix final,
      wordOfPrefixFinal rightPrefix final⟩
  have fullSupport :=
    S5_505Family.S5_505.valid_support identity valid
  have fullMod :=
    S5_505Family.S5_505.valid_count_mod_four identity valid
  have prefixSupport : ∀ letter,
      letter ∈ leftPrefix ↔ letter ∈ rightPrefix := by
    intro letter
    by_cases same : letter = final
    · subst letter
      exact repeated
    · have support := fullSupport letter
      simpa [identity, toList_wordOfPrefixFinal,
        List.mem_append, same] using support
  have prefixMod : ∀ letter,
      leftPrefix.count letter % 4 = rightPrefix.count letter % 4 := by
    intro letter
    have equality := fullMod letter
    simp only [identity, toList_wordOfPrefixFinal,
      List.count_append, List.count_cons, List.count_nil,
      Nat.add_zero] at equality
    by_cases same : letter = final
    · subst letter
      omega
    · simpa [Ne.symm same] using equality
  have normalPermutation :=
    positiveModFourReduce_perm prefixSupport prefixMod
  exact (derivesNormalPrefix leftPrefix final).trans <|
    (Common.derivesPrefixPermutation prefixSwap normalPermutation final).trans <|
      (derivesNormalPrefix rightPrefix final).symm

/-- Align two repeated finals. If the requested new final occurs only once
in the prefix, contextual period four first manufactures five copies. -/
theorem alignRepeatedFinal
    (letters : List Nat) (oldFinal newFinal : Nat)
    (oldIn : oldFinal ∈ letters)
    (newIn : newFinal ∈ letters) :
    ∃ alignedPrefix,
      Derives basis
        (wordOfPrefixFinal letters oldFinal)
        (wordOfPrefixFinal alignedPrefix newFinal) ∧
      newFinal ∈ alignedPrefix := by
  by_cases same : oldFinal = newFinal
  · subst newFinal
    exact ⟨letters, Derives.refl _, oldIn⟩
  · by_cases twoNew : 2 ≤ letters.count newFinal
    · obtain ⟨switched, derivation, _, newRepeated⟩ :=
        Common.switchRepeatedFinal prefixSwap terminalSwitch
          letters oldFinal newFinal oldIn twoNew
      exact ⟨switched, derivation, newRepeated⟩
    · let rest := letters.erase newFinal
      have arrange : letters.Perm (newFinal :: rest) := by
        simpa [rest] using List.perm_cons_erase newIn
      have arranged :=
        Common.derivesPrefixPermutation prefixSwap arrange oldFinal
      let expandedPrefix := List.replicate 5 newFinal ++ rest
      have expand :
          Derives basis
            (wordOfPrefixFinal (newFinal :: rest) oldFinal)
            (wordOfPrefixFinal expandedPrefix oldFinal) := by
        simpa [expandedPrefix, wordOfPrefixFinal,
          List.replicate_succ, Word.append_assoc,
          List.append_assoc] using
            oneToFiveBefore (Word.singleton newFinal)
              (wordOfPrefixFinal rest oldFinal)
      have oldInRest : oldFinal ∈ rest := by
        simpa [rest, List.mem_erase_of_ne same] using oldIn
      have oldInExpanded : oldFinal ∈ expandedPrefix := by
        simp [expandedPrefix, oldInRest]
      have expandedTwo : 2 ≤ expandedPrefix.count newFinal := by
        simp [expandedPrefix]
      obtain ⟨switched, switchedDerivation, _, newRepeated⟩ :=
        Common.switchRepeatedFinal prefixSwap terminalSwitch
          expandedPrefix oldFinal newFinal oldInExpanded expandedTwo
      exact ⟨switched,
        arranged.trans <| expand.trans switchedDerivation,
        newRepeated⟩

/-- Unrestricted completeness of the displayed four laws for the exact
intersection `Id(S3_6) ∩ Id(S5_505)`. -/
theorem derives_of_factor_valid (identity : Identity Nat)
    (markerValid : identity.SatisfiedBy finalMarkerThree.semigroup)
    (exponentValid : identity.SatisfiedBy
      S5_505Family.S5_505.table.semigroup) :
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
    have simpleEquivalence :=
      finalMarkerValid_splitSimpleFinal_iff
        identity markerValid leftSplit.2
    have notMemberEquivalence :
        leftSplit.2 ∉ leftSplit.1 ↔
          leftSplit.2 ∉ rightSplit.1 := by
      change
        (leftSplit.2 = leftSplit.2 ∧ leftSplit.2 ∉ leftSplit.1) ↔
          (rightSplit.2 = leftSplit.2 ∧
            leftSplit.2 ∉ rightSplit.1) at simpleEquivalence
      constructor
      · intro leftSimple
        exact (simpleEquivalence.mp ⟨rfl, leftSimple⟩).2
      · intro rightSimple
        exact (simpleEquivalence.mpr ⟨sameFinal.symm, rightSimple⟩).2
    have repeatedEquivalence :
        leftSplit.2 ∈ leftSplit.1 ↔
          leftSplit.2 ∈ rightSplit.1 := by
      simpa using not_congr notMemberEquivalence
    have sameValid :
        (⟨wordOfPrefixFinal leftSplit.1 leftSplit.2,
            wordOfPrefixFinal rightSplit.1 leftSplit.2⟩ :
          Identity Nat).SatisfiedBy
            S5_505Family.S5_505.table.semigroup := by
      simpa only [leftReconstruct, rightReconstructSame] using exponentValid
    rw [← leftReconstruct, ← rightReconstructSame]
    exact derivesSameFinal leftSplit.1 rightSplit.1 leftSplit.2
      repeatedEquivalence sameValid
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
    have fullSupport :=
      S5_505Family.S5_505.valid_support identity exponentValid
        rightSplit.2
    have newInLeftWord : rightSplit.2 ∈ identity.lhs.toList :=
      fullSupport.mpr <| by
        rw [← rightReconstruct, toList_wordOfPrefixFinal]
        simp
    have newInLeft : rightSplit.2 ∈ leftSplit.1 := by
      rw [← leftReconstruct, toList_wordOfPrefixFinal] at newInLeftWord
      simpa [sameFinal, Ne.symm sameFinal] using newInLeftWord
    obtain ⟨alignedPrefix, alignment, alignedRepeated⟩ :=
      alignRepeatedFinal leftSplit.1 leftSplit.2 rightSplit.2
        oldRepeated newInLeft
    have alignedExponentValid :
        (⟨wordOfPrefixFinal alignedPrefix rightSplit.2,
            wordOfPrefixFinal rightSplit.1 rightSplit.2⟩ :
          Identity Nat).SatisfiedBy
            S5_505Family.S5_505.table.semigroup := by
      intro valuation
      have alignmentSound := alignment.sound exponentModels valuation
      have original := exponentValid valuation
      rw [← leftReconstruct, ← rightReconstruct] at original
      exact alignmentSound.symm.trans original
    have aligned :=
      derivesSameFinal alignedPrefix rightSplit.1 rightSplit.2
        ⟨fun _ => newRepeated, fun _ => alignedRepeated⟩
        alignedExponentValid
    rw [← leftReconstruct, ← rightReconstruct]
    exact alignment.trans aligned

def intersectionBasis :
    IntersectionBasis finalMarkerThree.semigroup
      S5_505Family.S5_505.table.semigroup basis where
  leftModels := markerModels
  rightModels := exponentModels
  complete := derives_of_factor_valid

end PrefixResidueFour

namespace S6_5325

/-- Zero-based Smallsemi multiplication table for `S6_5325`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (1 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (3 : Fin 6)
    else if right = 4 then (4 : Fin 6)
    else (0 : Fin 6)
  else if left = 1 then
    if right = 0 then (1 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (1 : Fin 6)
    else if right = 3 then (4 : Fin 6)
    else if right = 4 then (3 : Fin 6)
    else (1 : Fin 6)
  else if left = 2 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (1 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (3 : Fin 6)
    else if right = 4 then (4 : Fin 6)
    else (0 : Fin 6)
  else if left = 3 then
    if right = 0 then (3 : Fin 6)
    else if right = 1 then (4 : Fin 6)
    else if right = 2 then (3 : Fin 6)
    else if right = 3 then (1 : Fin 6)
    else if right = 4 then (0 : Fin 6)
    else (3 : Fin 6)
  else if left = 4 then
    if right = 0 then (4 : Fin 6)
    else if right = 1 then (3 : Fin 6)
    else if right = 2 then (4 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (1 : Fin 6)
    else (4 : Fin 6)
  else right

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def publishedRows : List (List Nat) :=
  [[0, 1, 0, 3, 4, 0],
   [1, 0, 1, 4, 3, 1],
   [0, 1, 0, 3, 4, 0],
   [3, 4, 3, 1, 0, 3],
   [4, 3, 4, 0, 1, 4],
   [0, 1, 2, 3, 4, 5]]

theorem mul_matches_published :
    ((List.finRange 6).map fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
        publishedRows := by
  decide

def markerMap (value : Fin 6) : Fin 3 :=
  if value = 2 then 1
  else if value = 5 then 2
  else 0

def markerPreimage (value : Fin 3) : Fin 6 :=
  if value = 0 then 0 else if value = 1 then 2 else 5

def markerQuotient : SplitSurjection table.semigroup
    finalMarkerThree.semigroup where
  toFun := markerMap
  map_mul := by decide
  preimage := markerPreimage
  right_inverse := by decide

def exponentMap (value : Fin 6) : Fin 5 :=
  if value = 0 then 0
  else if value = 1 then 1
  else if value = 2 then 0
  else if value = 3 then 2
  else if value = 4 then 3
  else 4

def exponentPreimage (value : Fin 5) : Fin 6 :=
  if value = 0 then 0
  else if value = 1 then 1
  else if value = 2 then 3
  else if value = 3 then 4
  else 5

def exponentQuotient : SplitSurjection table.semigroup
    S5_505Family.S5_505.table.semigroup where
  toFun := exponentMap
  map_mul := by decide
  preimage := exponentPreimage
  right_inverse := by decide

def subdirectPair : SubdirectPair table.semigroup
    finalMarkerThree.semigroup
    S5_505Family.S5_505.table.semigroup where
  left := markerQuotient
  right := exponentQuotient
  jointlyInjective := by
    intro left right equality
    revert left right
    decide

theorem representative_basis :
    BasisFor table.semigroup PrefixResidueFour.basis :=
  PrefixResidueFour.intersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite PrefixResidueFour.oppositeBasis := by
  simpa [PrefixResidueFour.oppositeBasis] using
    representative_basis.oppositeReversed

end S6_5325

namespace S6_9096

/-- Zero-based Smallsemi multiplication table for `S6_9096`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then (0 : Fin 6)
  else if left = 1 then (0 : Fin 6)
  else if left = 2 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else (2 : Fin 6)
  else if left = 3 then right
  else if left = 4 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (1 : Fin 6)
    else if right = 2 then (2 : Fin 6)
    else if right = 3 then (4 : Fin 6)
    else if right = 4 then (5 : Fin 6)
    else (3 : Fin 6)
  else
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (1 : Fin 6)
    else if right = 2 then (2 : Fin 6)
    else if right = 3 then (5 : Fin 6)
    else if right = 4 then (3 : Fin 6)
    else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0],
   [0, 0, 0, 2, 2, 2],
   [0, 1, 2, 3, 4, 5],
   [0, 1, 2, 4, 5, 3],
   [0, 1, 2, 5, 3, 4]]

theorem mul_matches_published :
    ((List.finRange 6).map fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
        publishedRows := by
  decide

def markerMap (value : Fin 6) : Fin 3 :=
  if value = 0 then 0
  else if value = 1 then 1
  else if value = 2 then 0
  else 2

def markerPreimage (value : Fin 3) : Fin 6 :=
  if value = 0 then 0 else if value = 1 then 1 else 3

def markerQuotient : SplitSurjection table.semigroup
    finalMarkerThree.semigroup where
  toFun := markerMap
  map_mul := by decide
  preimage := markerPreimage
  right_inverse := by decide

def exponentMap (value : Fin 6) : Fin 5 :=
  if value = 0 then 0
  else if value = 1 then 0
  else if value = 2 then 1
  else if value = 3 then 2
  else if value = 4 then 3
  else 4

def exponentPreimage (value : Fin 5) : Fin 6 :=
  if value = 0 then 0
  else if value = 1 then 2
  else if value = 2 then 3
  else if value = 3 then 4
  else 5

def exponentQuotient : SplitSurjection table.semigroup
    s5_1001.semigroup where
  toFun := exponentMap
  map_mul := by decide
  preimage := exponentPreimage
  right_inverse := by decide

def subdirectPair : SubdirectPair table.semigroup
    finalMarkerThree.semigroup s5_1001.semigroup where
  left := markerQuotient
  right := exponentQuotient
  jointlyInjective := by
    intro left right equality
    revert left right
    decide

theorem representative_basis :
    BasisFor table.semigroup IndexTwoPeriodThree.basis :=
  IndexTwoPeriodThree.intersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      IndexTwoPeriodThree.oppositeBasis := by
  simpa [IndexTwoPeriodThree.oppositeBasis] using
    representative_basis.oppositeReversed

end S6_9096

namespace S6_9113

/-- Zero-based Smallsemi multiplication table for `S6_9113`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then
    if right = 2 then (2 : Fin 6) else (0 : Fin 6)
  else if left = 1 then
    if right = 2 then (2 : Fin 6) else (0 : Fin 6)
  else if left = 2 then
    if right = 2 then (0 : Fin 6) else (2 : Fin 6)
  else if left = 3 then right
  else if left = 4 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (1 : Fin 6)
    else if right = 2 then (2 : Fin 6)
    else if right = 3 then (4 : Fin 6)
    else if right = 4 then (5 : Fin 6)
    else (3 : Fin 6)
  else
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (1 : Fin 6)
    else if right = 2 then (2 : Fin 6)
    else if right = 3 then (5 : Fin 6)
    else if right = 4 then (3 : Fin 6)
    else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def publishedRows : List (List Nat) :=
  [[0, 0, 2, 0, 0, 0],
   [0, 0, 2, 0, 0, 0],
   [2, 2, 0, 2, 2, 2],
   [0, 1, 2, 3, 4, 5],
   [0, 1, 2, 4, 5, 3],
   [0, 1, 2, 5, 3, 4]]

theorem mul_matches_published :
    ((List.finRange 6).map fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
        publishedRows := by
  decide

def markerMap (value : Fin 6) : Fin 3 :=
  if value = 0 then 0
  else if value = 1 then 1
  else if value = 2 then 0
  else 2

def markerPreimage (value : Fin 3) : Fin 6 :=
  if value = 0 then 0 else if value = 1 then 1 else 3

def markerQuotient : SplitSurjection table.semigroup
    finalMarkerThree.semigroup where
  toFun := markerMap
  map_mul := by decide
  preimage := markerPreimage
  right_inverse := by decide

def exponentMap (value : Fin 6) : Fin 5 :=
  if value = 0 then 0
  else if value = 1 then 0
  else if value = 2 then 1
  else if value = 3 then 2
  else if value = 4 then 3
  else 4

def exponentPreimage (value : Fin 5) : Fin 6 :=
  if value = 0 then 0
  else if value = 1 then 2
  else if value = 2 then 3
  else if value = 3 then 4
  else 5

def exponentQuotient : SplitSurjection table.semigroup
    S5_1007Family.S5_1007.table.semigroup where
  toFun := exponentMap
  map_mul := by decide
  preimage := exponentPreimage
  right_inverse := by decide

def subdirectPair : SubdirectPair table.semigroup
    finalMarkerThree.semigroup
    S5_1007Family.S5_1007.table.semigroup where
  left := markerQuotient
  right := exponentQuotient
  jointlyInjective := by
    intro left right equality
    revert left right
    decide

theorem representative_basis :
    BasisFor table.semigroup PrefixResidueSix.basis :=
  PrefixResidueSix.intersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite PrefixResidueSix.oppositeBasis := by
  simpa [PrefixResidueSix.oppositeBasis] using
    representative_basis.oppositeReversed

end S6_9113

end SemigroupBasis.CoRoots.Order6FactorIntersectionSpecialRoots
