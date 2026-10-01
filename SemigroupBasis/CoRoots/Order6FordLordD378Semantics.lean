import SemigroupBasis.CoRoots.Order6FordLordD378Normal
import SemigroupBasis.CoRoots.S5_378Family
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S3_16
import SemigroupBasis.Subdirect

namespace SemigroupBasis.CoRoots.Order6FordLordD378

open SemigroupBasis
open SemigroupBasis.Examples

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def oppositeFiniteTable (table : FiniteTable) : FiniteTable where
  order := table.order
  mul := fun left right => table.mul right left
  assoc := fun left middle right =>
    (table.assoc right middle left).symm

private theorem oppositeFiniteTable_semigroup (table : FiniteTable) :
    (oppositeFiniteTable table).semigroup =
      table.semigroup.opposite := by
  rfl

/-! ## First-occurrence and multiplicity transport -/

private theorem filter_ne_length_lt_cons
    (selected : Nat) (letters : List Nat) :
    (letters.filter
        (fun letter => decide (letter ≠ selected))).length <
      (selected :: letters).length := by
  have filteredLength :
      (letters.filter
        (fun letter => decide (letter ≠ selected))).length ≤
          letters.length :=
    List.filter_sublist.length_le
  simpa only [List.length_cons] using
    Nat.lt_succ_of_le filteredLength

/-- The left-regular-band scan is definitionally the standard stable
duplicate erasure, up to the two equivalent Boolean inequality tests. -/
private theorem firstOccurrenceSequence_eq_eraseDups :
    ∀ letters : List Nat,
      firstOccurrenceSequence letters = letters.eraseDups
  | [] => rfl
  | selected :: rest => by
      rw [firstOccurrenceSequence, List.eraseDups_cons]
      congr 1
      have filtered :
          rest.filter (fun letter => !letter == selected) =
            rest.filter
              (fun letter => decide (letter ≠ selected)) := by
        apply List.filter_congr
        intro letter _
        by_cases equal : letter = selected
        · subst letter
          simp
        · simp [equal]
      rw [filtered]
      rw [← SemigroupBasis.Examples.firstOccurrenceSequence_filter]
      exact
        firstOccurrenceSequence_eq_eraseDups
          (rest.filter
            (fun letter => decide (letter ≠ selected)))
termination_by letters => letters.length
decreasing_by
  exact filter_ne_length_lt_cons selected rest

private def simpleProjection
    (whole letters : List Nat) : List Nat :=
  letters.filter fun letter => decide (whole.count letter = 1)

private theorem nodup_of_count_le_one
    {letters : List Nat}
    (bounded : ∀ letter, letters.count letter ≤ 1) :
    letters.Nodup := by
  induction letters with
  | nil => simp
  | cons first rest induction =>
      simp only [List.nodup_cons]
      constructor
      · intro member
        have positive : 1 ≤ rest.count first :=
          List.count_pos_iff.mpr member
        have bound := bounded first
        simp only [List.count_cons_self] at bound
        omega
      · apply induction
        intro letter
        have bound := bounded letter
        by_cases equal : first = letter
        · subst first
          simp only [List.count_cons_self] at bound
          omega
        · simpa [equal] using bound

private theorem simpleProjection_self_nodup (letters : List Nat) :
    (simpleProjection letters letters).Nodup := by
  apply nodup_of_count_le_one
  intro letter
  by_cases simple : letters.count letter = 1
  · exact Nat.le_trans
      (List.filter_sublist.count_le letter) (by omega)
  · have absent : letter ∉ simpleProjection letters letters := by
      intro member
      have kept := (List.mem_filter.mp member).2
      simp [simpleProjection, simple] at kept
    rw [List.count_eq_zero.mpr absent]
    omega

private theorem simpleProjection_self_eq_firstOccurrenceFilter
    (letters : List Nat) :
    simpleProjection letters letters =
      (firstOccurrenceSequence letters).filter
        (fun letter => decide (letters.count letter = 1)) := by
  calc
    simpleProjection letters letters =
        firstOccurrenceSequence (simpleProjection letters letters) :=
      (SemigroupBasis.Examples.firstOccurrenceSequence_eq_self_of_nodup
        (simpleProjection_self_nodup letters)).symm
    _ = _ := by
      simpa [simpleProjection] using
        SemigroupBasis.Examples.firstOccurrenceSequence_filter
          (fun letter => decide (letters.count letter = 1)) letters

private theorem singlesSeq_eq_simpleProjection (word : Word Nat) :
    singlesSeq word =
      simpleProjection word.toList word.toList := by
  unfold singlesSeq simpleProjection
  apply List.filter_congr
  intro letter _
  exact
    Bool.beq_eq_decide_eq
      (word.toList.count letter) 1

private theorem isPlasma_iff_mem_not_single
    (word : Word Nat) (letter : Nat) :
    IsPlasma word letter ↔
      letter ∈ word.toList ∧ ¬IsSingle word letter := by
  unfold IsPlasma IsSingle letterCount
  constructor
  · intro multiple
    constructor
    · exact List.count_pos_iff.mp (by omega)
    · omega
  · rintro ⟨member, notSingle⟩
    have positive := List.count_pos_iff.mpr member
    omega

private theorem sameIsSingle
    {left right : Word Nat}
    (same :
      SemigroupBasis.CoRoots.S5_378.SameSeparatorSimpleSignature
        left right)
    (letter : Nat) :
    IsSingle left letter ↔ IsSingle right letter := by
  simpa [IsSingle, letterCount,
    SemigroupBasis.CoRoots.S5_378.GloballySimple] using
      same.globallySimple letter

private theorem sameIsPlasma
    {left right : Word Nat}
    (same :
      SemigroupBasis.CoRoots.S5_378.SameSeparatorSimpleSignature
        left right)
    (letter : Nat) :
    IsPlasma left letter ↔ IsPlasma right letter := by
  rw [isPlasma_iff_mem_not_single,
    isPlasma_iff_mem_not_single]
  exact
    and_congr (same.support letter)
      (not_congr (sameIsSingle same letter))

private theorem head_eq_of_firstOccurrenceSequence_eq
    {left right : Word Nat}
    (same :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList) :
    left.head = right.head := by
  have data :
      left.head = right.head ∧
        (firstOccurrenceSequence left.tail).filter
            (fun letter => decide (letter ≠ left.head)) =
          (firstOccurrenceSequence right.tail).filter
            (fun letter => decide (letter ≠ right.head)) := by
    simpa only [Word.toList, firstOccurrenceSequence,
      List.cons.injEq] using same
  exact data.1

private theorem singlesSeq_eq_of_signatures
    {left right : Word Nat}
    (firstOccurrences :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList)
    (same :
      SemigroupBasis.CoRoots.S5_378.SameSeparatorSimpleSignature
        left right) :
    singlesSeq left = singlesSeq right := by
  calc
    singlesSeq left =
        simpleProjection left.toList left.toList :=
      singlesSeq_eq_simpleProjection left
    _ = (firstOccurrenceSequence left.toList).filter
          (fun letter =>
            decide (left.toList.count letter = 1)) := by
      exact
        simpleProjection_self_eq_firstOccurrenceFilter left.toList
    _ = (firstOccurrenceSequence right.toList).filter
          (fun letter =>
            decide (left.toList.count letter = 1)) := by
      rw [firstOccurrences]
    _ = (firstOccurrenceSequence right.toList).filter
          (fun letter =>
            decide (right.toList.count letter = 1)) := by
      apply List.filter_congr
      intro letter _
      exact decide_eq_decide.mpr <| by
        simpa [IsSingle, letterCount] using
          sameIsSingle same letter
    _ = simpleProjection right.toList right.toList :=
      (simpleProjection_self_eq_firstOccurrenceFilter
        right.toList).symm
    _ = singlesSeq right :=
      (singlesSeq_eq_simpleProjection right).symm

private theorem plasmaSeq_eq_of_signatures
    {left right : Word Nat}
    (firstOccurrences :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList)
    (same :
      SemigroupBasis.CoRoots.S5_378.SameSeparatorSimpleSignature
        left right) :
    plasmaSeq left = plasmaSeq right := by
  unfold plasmaSeq
  rw [← firstOccurrenceSequence_eq_eraseDups,
    ← firstOccurrenceSequence_eq_eraseDups,
    firstOccurrences]
  apply List.filter_congr
  intro letter _
  exact decide_eq_decide.mpr <| by
    simpa [IsPlasma, letterCount] using
      sameIsPlasma same letter

private theorem idxOf_filter_lt_idxOf_filter_iff
    (keep : Nat → Bool) {first second : Nat}
    (keepFirst : keep first = true)
    (keepSecond : keep second = true) :
    ∀ {letters : List Nat},
      first ∈ letters →
      second ∈ letters →
      ((letters.filter keep).idxOf first <
          (letters.filter keep).idxOf second ↔
        letters.idxOf first < letters.idxOf second) := by
  intro letters
  induction letters with
  | nil =>
      intro firstMember _
      simp at firstMember
  | cons head tail induction =>
      intro firstMember secondMember
      by_cases headFirst : head = first
      · subst head
        by_cases equal : first = second
        · subst second
          simp
        · have firstSecondBeq : (first == second) = false :=
            beq_eq_false_iff_ne.mpr equal
          simp [List.filter_cons, keepFirst,
            List.idxOf_cons, firstSecondBeq]
      · by_cases headSecond : head = second
        · subst head
          have secondFirstBeq : (second == first) = false :=
            beq_eq_false_iff_ne.mpr headFirst
          simp [List.filter_cons, keepSecond,
            List.idxOf_cons, secondFirstBeq]
        · have firstTail : first ∈ tail := by
            rcases List.mem_cons.mp firstMember with
              firstHead | firstTail
            · exact False.elim (headFirst firstHead.symm)
            · exact firstTail
          have secondTail : second ∈ tail := by
            rcases List.mem_cons.mp secondMember with
              secondHead | secondTail
            · exact False.elim (headSecond secondHead.symm)
            · exact secondTail
          have headFirstBeq : (head == first) = false :=
            beq_eq_false_iff_ne.mpr headFirst
          have headSecondBeq : (head == second) = false :=
            beq_eq_false_iff_ne.mpr headSecond
          have inductionData :=
            induction firstTail secondTail
          by_cases kept : keep head
          · simpa [List.filter_cons, kept,
              List.idxOf_cons, headFirstBeq,
              headSecondBeq] using
              inductionData
          · simpa [List.filter_cons, kept,
              List.idxOf_cons, headFirstBeq,
              headSecondBeq] using
              inductionData

private theorem idxOf_firstOccurrenceSequence_lt_iff
    (first second : Nat) :
    ∀ {letters : List Nat},
      first ∈ letters →
      second ∈ letters →
      ((firstOccurrenceSequence letters).idxOf first <
          (firstOccurrenceSequence letters).idxOf second ↔
        letters.idxOf first < letters.idxOf second) := by
  intro letters
  induction letters with
  | nil =>
      intro firstMember _
      simp at firstMember
  | cons head tail induction =>
      intro firstMember secondMember
      by_cases headFirst : head = first
      · subst head
        by_cases equal : first = second
        · subst second
          simp
        · have firstSecondBeq : (first == second) = false :=
            beq_eq_false_iff_ne.mpr equal
          simp [firstOccurrenceSequence, List.idxOf_cons,
            firstSecondBeq]
      · by_cases headSecond : head = second
        · subst head
          have secondFirstBeq : (second == first) = false :=
            beq_eq_false_iff_ne.mpr headFirst
          simp [firstOccurrenceSequence, List.idxOf_cons,
            secondFirstBeq]
        · have firstTail : first ∈ tail := by
            rcases List.mem_cons.mp firstMember with
              firstHead | firstTail
            · exact False.elim (headFirst firstHead.symm)
            · exact firstTail
          have secondTail : second ∈ tail := by
            rcases List.mem_cons.mp secondMember with
              secondHead | secondTail
            · exact False.elim (headSecond secondHead.symm)
            · exact secondTail
          have headFirstBeq : (head == first) = false :=
            beq_eq_false_iff_ne.mpr headFirst
          have headSecondBeq : (head == second) = false :=
            beq_eq_false_iff_ne.mpr headSecond
          have firstInSequence :
              first ∈ firstOccurrenceSequence tail :=
            (SemigroupBasis.Examples.mem_firstOccurrenceSequence_iff
              first tail).2 firstTail
          have secondInSequence :
              second ∈ firstOccurrenceSequence tail :=
            (SemigroupBasis.Examples.mem_firstOccurrenceSequence_iff
              second tail).2 secondTail
          have firstKept :
              decide (first ≠ head) = true :=
            decide_eq_true <| by
              intro equal
              exact headFirst equal.symm
          have secondKept :
              decide (second ≠ head) = true :=
            decide_eq_true <| by
              intro equal
              exact headSecond equal.symm
          have filtered :=
            idxOf_filter_lt_idxOf_filter_iff
              (fun letter => decide (letter ≠ head))
              (first := first) (second := second)
              firstKept secondKept
              (letters := firstOccurrenceSequence tail)
              firstInSequence secondInSequence
          have inductionData :=
            induction firstTail secondTail
          simpa [firstOccurrenceSequence, List.idxOf_cons,
            headFirstBeq, headSecondBeq] using
              filtered.trans inductionData

private theorem idxOf_lt_idxOf_iff_of_firstOccurrences
    {left right : List Nat} {first second : Nat}
    (same :
      firstOccurrenceSequence left =
        firstOccurrenceSequence right)
    (firstLeft : first ∈ left)
    (secondLeft : second ∈ left)
    (firstRight : first ∈ right)
    (secondRight : second ∈ right) :
    left.idxOf first < left.idxOf second ↔
      right.idxOf first < right.idxOf second := by
  calc
    left.idxOf first < left.idxOf second ↔
        (firstOccurrenceSequence left).idxOf first <
          (firstOccurrenceSequence left).idxOf second :=
      (idxOf_firstOccurrenceSequence_lt_iff
        first second (letters := left)
          firstLeft secondLeft).symm
    _ ↔
        (firstOccurrenceSequence right).idxOf first <
          (firstOccurrenceSequence right).idxOf second := by
      rw [same]
    _ ↔ right.idxOf first < right.idxOf second :=
      idxOf_firstOccurrenceSequence_lt_iff
        first second (letters := right)
          firstRight secondRight

private theorem mem_plasmaSeq_iff
    (word : Word Nat) (letter : Nat) :
    letter ∈ plasmaSeq word ↔ IsPlasma word letter := by
  constructor
  · intro member
    have kept := (List.mem_filter.mp member).2
    simpa [plasmaSeq, IsPlasma, letterCount] using kept
  · intro multiple
    apply List.mem_filter.mpr
    constructor
    · rw [← firstOccurrenceSequence_eq_eraseDups]
      apply
        (SemigroupBasis.Examples.mem_firstOccurrenceSequence_iff
          letter word.toList).2
      apply List.count_pos_iff.mp
      have positive : 0 < word.toList.count letter := by
        have data := multiple
        unfold IsPlasma letterCount at data
        omega
      exact positive
    · simpa [plasmaSeq, IsPlasma, letterCount] using multiple

private theorem beforeOpenList_eq_of_signatures
    {left right : Word Nat}
    (firstOccurrences :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList)
    (same :
      SemigroupBasis.CoRoots.S5_378.SameSeparatorSimpleSignature
        left right)
    (separator : Nat)
    (separatorSingle : IsSingle left separator) :
    beforeOpenList left separator =
      beforeOpenList right separator := by
  have separatorRightSingle :
      IsSingle right separator :=
    (sameIsSingle same separator).1 separatorSingle
  have separatorLeftMember : separator ∈ left.toList := by
    apply List.count_pos_iff.mp
    unfold IsSingle letterCount at separatorSingle
    omega
  have separatorRightWordMember : separator ∈ right.toList := by
    apply List.count_pos_iff.mp
    unfold IsSingle letterCount at separatorRightSingle
    omega
  have plasmaEqual :=
    plasmaSeq_eq_of_signatures firstOccurrences same
  unfold beforeOpenList
  rw [plasmaEqual]
  apply List.filter_congr
  intro plasma plasmaMember
  have plasmaRightMultiple :
      IsPlasma right plasma :=
    (mem_plasmaSeq_iff right plasma).1 plasmaMember
  have plasmaRightMember : plasma ∈ right.toList := by
    apply List.count_pos_iff.mp
    unfold IsPlasma letterCount at plasmaRightMultiple
    omega
  have plasmaLeftMember : plasma ∈ left.toList :=
    (same.support plasma).2 plasmaRightMember
  exact decide_eq_decide.mpr <|
    idxOf_lt_idxOf_iff_of_firstOccurrences
      firstOccurrences separatorLeftMember plasmaLeftMember
        separatorRightWordMember plasmaRightMember

/-! ## Exact-cut interpretation of the four-way region coordinate -/

private def HasExactCut (word : Word Nat) (separator : Nat) : Prop :=
  ∃ left right,
    UniqueSeparatorFourExactCut
      word.toList left separator right

private theorem exactCut_separator_absent_left
    {letters left right : List Nat} {separator : Nat}
    (split : letters = left ++ separator :: right)
    (countOne : letters.count separator = 1) :
    separator ∉ left := by
  intro member
  have positive : 0 < left.count separator :=
    List.count_pos_iff.mpr member
  rw [split, List.count_append, List.count_cons_self] at countOne
  omega

private theorem exactCut_separator_absent_right
    {letters left right : List Nat} {separator : Nat}
    (split : letters = left ++ separator :: right)
    (countOne : letters.count separator = 1) :
    separator ∉ right := by
  intro member
  have positive : 0 < right.count separator :=
    List.count_pos_iff.mpr member
  rw [split, List.count_append, List.count_cons_self] at countOne
  omega

private theorem exactCut_reverse
    {letters left right : List Nat} {separator : Nat}
    (cut :
      UniqueSeparatorFourExactCut
        letters left separator right) :
    UniqueSeparatorFourExactCut
      letters.reverse right.reverse separator left.reverse := by
  rcases cut with ⟨split, countOne, disjoint⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [split]
    simp [List.reverse_append, List.append_assoc]
  · simpa using countOne
  · intro letter rightMember leftMember
    have rightOriginal : letter ∈ right := by
      simpa using rightMember
    have leftOriginal : letter ∈ left := by
      simpa using leftMember
    exact disjoint letter leftOriginal rightOriginal

private theorem exactCutSignature_reverse_iff
    (word : Word Nat) (separator : Nat)
    (leftSupport rightSupport : List Nat) :
    SemigroupBasis.CoRoots.S5_378.ExactCutSignature
        word separator leftSupport rightSupport ↔
      SemigroupBasis.CoRoots.S5_378.ExactCutSignature
        word.reverse separator rightSupport leftSupport := by
  constructor
  · rintro
      ⟨left, right, cut, leftData, rightData⟩
    refine
      ⟨right.reverse, left.reverse, ?_,
        ?_, ?_⟩
    · simpa [Word.toList_reverse] using
        exactCut_reverse cut
    · intro letter
      simpa using rightData letter
    · intro letter
      simpa using leftData letter
  · rintro
      ⟨right, left, cut, rightData, leftData⟩
    have reversedCut :=
      exactCut_reverse cut
    refine
      ⟨left.reverse, right.reverse, ?_,
        ?_, ?_⟩
    · simpa [Word.toList_reverse] using reversedCut
    · intro letter
      simpa using leftData letter
    · intro letter
      simpa using rightData letter

private theorem separatorSignature_of_reversed
    {left right : Word Nat}
    (same :
      SemigroupBasis.CoRoots.S5_378.SameSeparatorSimpleSignature
        left.reverse right.reverse) :
    SemigroupBasis.CoRoots.S5_378.SameSeparatorSimpleSignature
      left right where
  support := by
    intro letter
    simpa [Word.toList_reverse] using
      same.support letter
  exactCuts := by
    intro separator leftSupport rightSupport
    calc
      SemigroupBasis.CoRoots.S5_378.ExactCutSignature
          left separator leftSupport rightSupport ↔
        SemigroupBasis.CoRoots.S5_378.ExactCutSignature
          left.reverse separator rightSupport leftSupport :=
        exactCutSignature_reverse_iff
          left separator leftSupport rightSupport
      _ ↔
        SemigroupBasis.CoRoots.S5_378.ExactCutSignature
          right.reverse separator rightSupport leftSupport :=
        same.exactCuts separator rightSupport leftSupport
      _ ↔
        SemigroupBasis.CoRoots.S5_378.ExactCutSignature
          right separator leftSupport rightSupport :=
        (exactCutSignature_reverse_iff
          right separator leftSupport rightSupport).symm
  globallySimple := by
    intro letter
    simpa [SemigroupBasis.CoRoots.S5_378.GloballySimple,
      Word.toList_reverse] using
        same.globallySimple letter

private theorem idxOf_separator_append
    (left right : List Nat) (separator : Nat)
    (separatorAbsent : separator ∉ left) :
    (left ++ separator :: right).idxOf separator =
      left.length := by
  rw [List.idxOf_append, if_neg separatorAbsent,
    List.idxOf_cons_self]
  simp

private theorem idxOf_lt_idxOf_separator_iff_mem_left
    (left right : List Nat) (separator letter : Nat)
    (separatorAbsent : separator ∉ left) :
    (left ++ separator :: right).idxOf letter <
        (left ++ separator :: right).idxOf separator ↔
      letter ∈ left := by
  rw [idxOf_separator_append left right separator
    separatorAbsent]
  by_cases member : letter ∈ left
  · rw [List.idxOf_append, if_pos member]
    simp [member, List.idxOf_lt_length_of_mem member]
  · rw [List.idxOf_append, if_neg member]
    simp [member]

private theorem idxOf_separator_lt_lastIdxOf_iff_mem_right
    (left right : List Nat) (separator letter : Nat)
    (separatorAbsent : separator ∉ left) :
    (left ++ separator :: right).idxOf separator <
        lastIdxOf (left ++ separator :: right) letter ↔
      letter ∈ right := by
  rw [idxOf_separator_append left right separator
    separatorAbsent]
  unfold lastIdxOf
  have reverseShape :
      (left ++ separator :: right).reverse =
        right.reverse ++ separator :: left.reverse := by
    simp
  rw [reverseShape]
  simp only [List.length_append, List.length_cons,
    List.length_reverse]
  by_cases member : letter ∈ right
  · have reverseMember : letter ∈ right.reverse := by
      simpa using member
    rw [List.idxOf_append, if_pos reverseMember]
    have bound :
        right.reverse.idxOf letter < right.length := by
      simpa using
        List.idxOf_lt_length_of_mem reverseMember
    simp only [member, iff_true]
    omega
  · have reverseAbsent : letter ∉ right.reverse := by
      simpa using member
    rw [List.idxOf_append, if_neg reverseAbsent]
    simp only [List.length_reverse, member, iff_false]
    omega

private theorem idxOf_separator_lt_idxOf_of_mem_right
    (left right : List Nat) (separator letter : Nat)
    (separatorAbsent : separator ∉ left)
    (letterAbsent : letter ∉ left)
    (different : separator ≠ letter)
    (_member : letter ∈ right) :
    (left ++ separator :: right).idxOf separator <
      (left ++ separator :: right).idxOf letter := by
  rw [idxOf_separator_append left right separator
    separatorAbsent]
  rw [List.idxOf_append, if_neg letterAbsent,
    List.idxOf_cons]
  have separatorBeq : (separator == letter) = false :=
    beq_eq_false_iff_ne.mpr different
  rw [separatorBeq]
  simp only [cond_false]
  omega

private theorem lastIdxOf_lt_idxOf_separator_of_mem_left
    (left right : List Nat) (separator letter : Nat)
    (separatorAbsent : separator ∉ left)
    (letterMember : letter ∈ left)
    (letterAbsent : letter ∉ right)
    (different : separator ≠ letter) :
    lastIdxOf (left ++ separator :: right) letter <
      (left ++ separator :: right).idxOf separator := by
  rw [idxOf_separator_append left right separator
    separatorAbsent]
  unfold lastIdxOf
  have reverseShape :
      (left ++ separator :: right).reverse =
        right.reverse ++ separator :: left.reverse := by
    simp
  rw [reverseShape]
  simp only [List.length_append, List.length_cons,
    List.length_reverse]
  have rightReverseAbsent : letter ∉ right.reverse := by
    simpa using letterAbsent
  rw [List.idxOf_append, if_neg rightReverseAbsent,
    List.idxOf_cons]
  have leftReverseMember : letter ∈ left.reverse := by
    simpa using letterMember
  have bound :
      left.reverse.idxOf letter < left.length := by
    simpa using
      List.idxOf_lt_length_of_mem leftReverseMember
  have separatorBeq : (separator == letter) = false :=
    beq_eq_false_iff_ne.mpr different
  rw [separatorBeq]
  simp only [List.length_reverse, cond_false]
  omega

private theorem hasExactCut_iff_of_same
    {left right : Word Nat}
    (same :
      SemigroupBasis.CoRoots.S5_378.SameSeparatorSimpleSignature
        left right)
    (separator : Nat) :
    HasExactCut left separator ↔
      HasExactCut right separator := by
  constructor
  · rintro ⟨leftPrefix, leftSuffix, cut⟩
    have signature :
        SemigroupBasis.CoRoots.S5_378.ExactCutSignature
          left separator leftPrefix leftSuffix :=
      ⟨leftPrefix, leftSuffix, cut,
        fun _ => Iff.rfl, fun _ => Iff.rfl⟩
    obtain
      ⟨rightPrefix, rightSuffix, rightCut, _, _⟩ :=
        (same.exactCuts
          separator leftPrefix leftSuffix).1 signature
    exact ⟨rightPrefix, rightSuffix, rightCut⟩
  · rintro ⟨rightPrefix, rightSuffix, cut⟩
    have signature :
        SemigroupBasis.CoRoots.S5_378.ExactCutSignature
          right separator rightPrefix rightSuffix :=
      ⟨rightPrefix, rightSuffix, cut,
        fun _ => Iff.rfl, fun _ => Iff.rfl⟩
    obtain
      ⟨leftPrefix, leftSuffix, leftCut, _, _⟩ :=
        (same.exactCuts
          separator rightPrefix rightSuffix).2 signature
    exact ⟨leftPrefix, leftSuffix, leftCut⟩

private theorem hasExactCut_iff_insideAny_eq_false
    (word : Word Nat) (separator : Nat)
    (separatorSingle : IsSingle word separator) :
    HasExactCut word separator ↔
      (plasmaSeq word).any (fun plasma =>
        word.toList.idxOf plasma < word.toList.idxOf separator &&
          word.toList.idxOf separator <
            lastIdxOf word.toList plasma) = false := by
  constructor
  · rintro
      ⟨left, right, split, countOne, disjoint⟩
    apply List.any_eq_false.mpr
    intro plasma plasmaMember inside
    have separatorAbsent :
        separator ∉ left :=
      exactCut_separator_absent_left split countOne
    have insideData :
        word.toList.idxOf plasma <
            word.toList.idxOf separator ∧
          word.toList.idxOf separator <
            lastIdxOf word.toList plasma := by
      simpa only [Bool.and_eq_true,
        decide_eq_true_eq] using inside
    have plasmaLeft : plasma ∈ left := by
      rw [split] at insideData
      exact
        (idxOf_lt_idxOf_separator_iff_mem_left
          left right separator plasma separatorAbsent).1
            insideData.1
    have plasmaRight : plasma ∈ right := by
      rw [split] at insideData
      exact
        (idxOf_separator_lt_lastIdxOf_iff_mem_right
          left right separator plasma separatorAbsent).1
            insideData.2
    exact disjoint plasma plasmaLeft plasmaRight
  · intro insideFalse
    have separatorMember : separator ∈ word.toList := by
      apply List.count_pos_iff.mp
      unfold IsSingle letterCount at separatorSingle
      omega
    obtain ⟨left, right, split⟩ :=
      List.append_of_mem separatorMember
    have countOne : word.toList.count separator = 1 := by
      simpa [IsSingle, letterCount] using separatorSingle
    have separatorAbsent :
        separator ∉ left :=
      exactCut_separator_absent_left split countOne
    refine ⟨left, right, split, countOne, ?_⟩
    intro plasma plasmaLeft plasmaRight
    have leftPositive : 0 < left.count plasma :=
      List.count_pos_iff.mpr plasmaLeft
    have rightPositive : 0 < right.count plasma :=
      List.count_pos_iff.mpr plasmaRight
    have multiple : IsPlasma word plasma := by
      unfold IsPlasma letterCount
      rw [split, List.count_append]
      simp only [List.count_cons]
      split <;> omega
    have plasmaMember :
        plasma ∈ plasmaSeq word :=
      (mem_plasmaSeq_iff word plasma).2 multiple
    have noInside :=
      (List.any_eq_false.mp insideFalse)
        plasma plasmaMember
    apply noInside
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rw [split]
      exact
        (idxOf_lt_idxOf_separator_iff_mem_left
          left right separator plasma separatorAbsent).2
            plasmaLeft
    · rw [split]
      exact
        (idxOf_separator_lt_lastIdxOf_iff_mem_right
          left right separator plasma separatorAbsent).2
            plasmaRight

private theorem allAfter_eq_true_iff_beforeOpenList_eq_nil
    (word : Word Nat) (separator : Nat)
    (separatorSingle : IsSingle word separator)
    (cut : HasExactCut word separator) :
    (plasmaSeq word).all (fun plasma =>
        lastIdxOf word.toList plasma <
          word.toList.idxOf separator) = true ↔
      beforeOpenList word separator = [] := by
  obtain
    ⟨left, right, split, countOne, disjoint⟩ := cut
  have separatorAbsentLeft :
      separator ∉ left :=
    exactCut_separator_absent_left split countOne
  have separatorAbsentRight :
      separator ∉ right :=
    exactCut_separator_absent_right split countOne
  constructor
  · intro allAfter
    unfold beforeOpenList
    apply List.filter_eq_nil_iff.mpr
    intro plasma plasmaMember opensAfter
    have plasmaMultiple :
        IsPlasma word plasma :=
      (mem_plasmaSeq_iff word plasma).1 plasmaMember
    have plasmaWordMember : plasma ∈ word.toList := by
      apply List.count_pos_iff.mp
      unfold IsPlasma letterCount at plasmaMultiple
      omega
    have different : separator ≠ plasma := by
      intro equal
      subst plasma
      unfold IsSingle letterCount at separatorSingle
      unfold IsPlasma letterCount at plasmaMultiple
      omega
    have opensAfterInequality :
        word.toList.idxOf separator <
          word.toList.idxOf plasma := by
      simpa only [decide_eq_true_eq] using opensAfter
    have allAfterData :=
      (List.all_eq_true.mp allAfter)
        plasma plasmaMember
    have closesBeforeInequality :
        lastIdxOf word.toList plasma <
          word.toList.idxOf separator := by
      simpa only [decide_eq_true_eq] using allAfterData
    have plasmaNotLeft : plasma ∉ left := by
      intro plasmaLeft
      have opensBefore :
          word.toList.idxOf plasma <
            word.toList.idxOf separator := by
        rw [split]
        exact
          (idxOf_lt_idxOf_separator_iff_mem_left
            left right separator plasma
              separatorAbsentLeft).2 plasmaLeft
      omega
    have splitMembership :
        plasma ∈ left ∨
          plasma = separator ∨ plasma ∈ right := by
      simpa [split] using plasmaWordMember
    have plasmaRight : plasma ∈ right := by
      rcases splitMembership with
        plasmaLeft | plasmaSeparator | plasmaRight
      · exact False.elim (plasmaNotLeft plasmaLeft)
      · exact False.elim (different plasmaSeparator.symm)
      · exact plasmaRight
    have closesAfter :
        word.toList.idxOf separator <
          lastIdxOf word.toList plasma := by
      rw [split]
      exact
        (idxOf_separator_lt_lastIdxOf_iff_mem_right
          left right separator plasma
            separatorAbsentLeft).2 plasmaRight
    omega
  · intro beforeOpenEmpty
    apply List.all_eq_true.mpr
    intro plasma plasmaMember
    have plasmaMultiple :
        IsPlasma word plasma :=
      (mem_plasmaSeq_iff word plasma).1 plasmaMember
    have plasmaWordMember : plasma ∈ word.toList := by
      apply List.count_pos_iff.mp
      unfold IsPlasma letterCount at plasmaMultiple
      omega
    have different : separator ≠ plasma := by
      intro equal
      subst plasma
      unfold IsSingle letterCount at separatorSingle
      unfold IsPlasma letterCount at plasmaMultiple
      omega
    have splitMembership :
        plasma ∈ left ∨
          plasma = separator ∨ plasma ∈ right := by
      simpa [split] using plasmaWordMember
    rcases splitMembership with
      plasmaLeft | plasmaSeparator | plasmaRight
    · have plasmaNotRight : plasma ∉ right :=
        disjoint plasma plasmaLeft
      have closesBefore :
          lastIdxOf word.toList plasma <
            word.toList.idxOf separator := by
        rw [split]
        exact
          lastIdxOf_lt_idxOf_separator_of_mem_left
            left right separator plasma separatorAbsentLeft
              plasmaLeft plasmaNotRight different
      exact decide_eq_true closesBefore
    · exact False.elim (different plasmaSeparator.symm)
    · have plasmaNotLeft : plasma ∉ left := by
        intro plasmaLeft
        exact disjoint plasma plasmaLeft plasmaRight
      have opensAfter :
          word.toList.idxOf separator <
            word.toList.idxOf plasma := by
        rw [split]
        exact
          idxOf_separator_lt_idxOf_of_mem_right
            left right separator plasma separatorAbsentLeft
              plasmaNotLeft different plasmaRight
      have beforeOpenMember :
          plasma ∈ beforeOpenList word separator := by
        apply List.mem_filter.mpr
        exact ⟨plasmaMember, decide_eq_true opensAfter⟩
      rw [beforeOpenEmpty] at beforeOpenMember
      simp at beforeOpenMember

private theorem allAfter_eq_false_of_insideAny_eq_true
    (word : Word Nat) (separator : Nat)
    (inside :
      (plasmaSeq word).any (fun plasma =>
        word.toList.idxOf plasma < word.toList.idxOf separator &&
          word.toList.idxOf separator <
            lastIdxOf word.toList plasma) = true) :
    (plasmaSeq word).all (fun plasma =>
      lastIdxOf word.toList plasma <
        word.toList.idxOf separator) = false := by
  obtain ⟨plasma, plasmaMember, insideData⟩ :=
    List.any_eq_true.mp inside
  have insideInequalities :
      word.toList.idxOf plasma <
          word.toList.idxOf separator ∧
        word.toList.idxOf separator <
          lastIdxOf word.toList plasma := by
    simpa only [Bool.and_eq_true,
      decide_eq_true_eq] using insideData
  apply Bool.eq_false_iff.mpr
  intro allAfter
  have closesBeforeData :=
    (List.all_eq_true.mp allAfter)
      plasma plasmaMember
  have closesBefore :
      lastIdxOf word.toList plasma <
        word.toList.idxOf separator := by
    simpa only [decide_eq_true_eq] using closesBeforeData
  omega

private def rel4Summary (word : Word Nat) (separator : Nat) : Rel4 :=
  if (plasmaSeq word).all (fun plasma =>
      word.toList.idxOf separator < word.toList.idxOf plasma) then
    Rel4.before
  else if (plasmaSeq word).any (fun plasma =>
      word.toList.idxOf plasma < word.toList.idxOf separator &&
        word.toList.idxOf separator <
          lastIdxOf word.toList plasma) then
    Rel4.inside
  else if beforeOpenList word separator = [] then
    Rel4.after
  else
    Rel4.gap

private theorem rel4_eq_summary
    (word : Word Nat) (separator : Nat)
    (separatorSingle : IsSingle word separator) :
    rel4 word separator = rel4Summary word separator := by
  unfold rel4 rel4Summary
  cases beforeData :
      (plasmaSeq word).all (fun plasma =>
        word.toList.idxOf separator <
          word.toList.idxOf plasma) with
  | true =>
      simp [beforeData]
  | false =>
      simp only [beforeData, Bool.false_eq_true,
        ↓reduceIte]
      cases insideData :
          (plasmaSeq word).any (fun plasma =>
            word.toList.idxOf plasma <
                word.toList.idxOf separator &&
              word.toList.idxOf separator <
                lastIdxOf word.toList plasma) with
      | true =>
          have afterFalse :=
            allAfter_eq_false_of_insideAny_eq_true
              word separator insideData
          simp [insideData, afterFalse]
      | false =>
          have cut :
              HasExactCut word separator :=
            (hasExactCut_iff_insideAny_eq_false
              word separator separatorSingle).2 insideData
          have afterIff :=
            allAfter_eq_true_iff_beforeOpenList_eq_nil
              word separator separatorSingle cut
          by_cases empty :
              beforeOpenList word separator = []
          · have afterTrue := afterIff.2 empty
            simp [insideData, empty, afterTrue]
          · have afterFalse :
                (plasmaSeq word).all (fun plasma =>
                  lastIdxOf word.toList plasma <
                    word.toList.idxOf separator) = false := by
              apply Bool.eq_false_iff.mpr
              intro afterTrue
              exact empty (afterIff.1 afterTrue)
            simp [insideData, empty, afterFalse]

private theorem allBefore_eq_true_iff_of_signatures
    {left right : Word Nat}
    (firstOccurrences :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList)
    (same :
      SemigroupBasis.CoRoots.S5_378.SameSeparatorSimpleSignature
        left right)
    (separator : Nat)
    (separatorSingle : IsSingle left separator) :
    (plasmaSeq left).all (fun plasma =>
        left.toList.idxOf separator <
          left.toList.idxOf plasma) = true ↔
      (plasmaSeq right).all (fun plasma =>
        right.toList.idxOf separator <
          right.toList.idxOf plasma) = true := by
  have separatorRightSingle :
      IsSingle right separator :=
    (sameIsSingle same separator).1 separatorSingle
  have separatorLeftMember : separator ∈ left.toList := by
    apply List.count_pos_iff.mp
    unfold IsSingle letterCount at separatorSingle
    omega
  have separatorRightWordMember : separator ∈ right.toList := by
    apply List.count_pos_iff.mp
    unfold IsSingle letterCount at separatorRightSingle
    omega
  have plasmaEqual :=
    plasmaSeq_eq_of_signatures firstOccurrences same
  constructor
  · intro leftAll
    apply List.all_eq_true.mpr
    intro plasma plasmaRightSequenceMember
    have plasmaLeftSequenceMember :
        plasma ∈ plasmaSeq left := by
      rw [plasmaEqual]
      exact plasmaRightSequenceMember
    have plasmaLeftMultiple :
        IsPlasma left plasma :=
      (mem_plasmaSeq_iff left plasma).1
        plasmaLeftSequenceMember
    have plasmaRightMultiple :
        IsPlasma right plasma :=
      (sameIsPlasma same plasma).1 plasmaLeftMultiple
    have plasmaLeftMember : plasma ∈ left.toList := by
      apply List.count_pos_iff.mp
      unfold IsPlasma letterCount at plasmaLeftMultiple
      omega
    have plasmaRightWordMember : plasma ∈ right.toList := by
      apply List.count_pos_iff.mp
      unfold IsPlasma letterCount at plasmaRightMultiple
      omega
    have leftData :=
      (List.all_eq_true.mp leftAll)
        plasma plasmaLeftSequenceMember
    have leftInequality :
        left.toList.idxOf separator <
          left.toList.idxOf plasma := by
      simpa only [decide_eq_true_eq] using leftData
    exact decide_eq_true <|
      (idxOf_lt_idxOf_iff_of_firstOccurrences
        firstOccurrences separatorLeftMember plasmaLeftMember
          separatorRightWordMember plasmaRightWordMember).1
            leftInequality
  · intro rightAll
    apply List.all_eq_true.mpr
    intro plasma plasmaLeftSequenceMember
    have plasmaRightSequenceMember :
        plasma ∈ plasmaSeq right := by
      rw [← plasmaEqual]
      exact plasmaLeftSequenceMember
    have plasmaLeftMultiple :
        IsPlasma left plasma :=
      (mem_plasmaSeq_iff left plasma).1
        plasmaLeftSequenceMember
    have plasmaRightMultiple :
        IsPlasma right plasma :=
      (sameIsPlasma same plasma).1 plasmaLeftMultiple
    have plasmaLeftMember : plasma ∈ left.toList := by
      apply List.count_pos_iff.mp
      unfold IsPlasma letterCount at plasmaLeftMultiple
      omega
    have plasmaRightWordMember : plasma ∈ right.toList := by
      apply List.count_pos_iff.mp
      unfold IsPlasma letterCount at plasmaRightMultiple
      omega
    have rightData :=
      (List.all_eq_true.mp rightAll)
        plasma plasmaRightSequenceMember
    have rightInequality :
        right.toList.idxOf separator <
          right.toList.idxOf plasma := by
      simpa only [decide_eq_true_eq] using rightData
    exact decide_eq_true <|
      (idxOf_lt_idxOf_iff_of_firstOccurrences
        firstOccurrences separatorLeftMember plasmaLeftMember
          separatorRightWordMember plasmaRightWordMember).2
            rightInequality

private theorem bool_eq_of_eq_false_iff
    {left right : Bool}
    (same : left = false ↔ right = false) :
    left = right := by
  cases left <;> cases right <;> simp_all

private theorem insideAny_eq_of_signatures
    {left right : Word Nat}
    (same :
      SemigroupBasis.CoRoots.S5_378.SameSeparatorSimpleSignature
        left right)
    (separator : Nat)
    (separatorSingle : IsSingle left separator) :
    (plasmaSeq left).any (fun plasma =>
        left.toList.idxOf plasma < left.toList.idxOf separator &&
          left.toList.idxOf separator <
            lastIdxOf left.toList plasma) =
      (plasmaSeq right).any (fun plasma =>
        right.toList.idxOf plasma < right.toList.idxOf separator &&
          right.toList.idxOf separator <
            lastIdxOf right.toList plasma) := by
  have separatorRightSingle :
      IsSingle right separator :=
    (sameIsSingle same separator).1 separatorSingle
  have leftCut :=
    hasExactCut_iff_insideAny_eq_false
      left separator separatorSingle
  have rightCut :=
    hasExactCut_iff_insideAny_eq_false
      right separator separatorRightSingle
  apply bool_eq_of_eq_false_iff
  exact
    leftCut.symm.trans <|
      (hasExactCut_iff_of_same same separator).trans rightCut

private theorem rel4Summary_eq_of_signatures
    {left right : Word Nat}
    (firstOccurrences :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList)
    (same :
      SemigroupBasis.CoRoots.S5_378.SameSeparatorSimpleSignature
        left right)
    (separator : Nat)
    (separatorSingle : IsSingle left separator) :
    rel4Summary left separator =
      rel4Summary right separator := by
  have beforeEqual :
      (plasmaSeq left).all (fun plasma =>
          left.toList.idxOf separator <
            left.toList.idxOf plasma) =
        (plasmaSeq right).all (fun plasma =>
          right.toList.idxOf separator <
            right.toList.idxOf plasma) :=
    Bool.eq_iff_iff.mpr <|
      allBefore_eq_true_iff_of_signatures
        firstOccurrences same separator separatorSingle
  have insideEqual :=
    insideAny_eq_of_signatures
      same separator separatorSingle
  have beforeOpenEqual :=
    beforeOpenList_eq_of_signatures
      firstOccurrences same separator separatorSingle
  unfold rel4Summary
  rw [beforeEqual, insideEqual, beforeOpenEqual]

private theorem rel4_eq_of_signatures
    {left right : Word Nat}
    (firstOccurrences :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList)
    (same :
      SemigroupBasis.CoRoots.S5_378.SameSeparatorSimpleSignature
        left right)
    (separator : Nat)
    (separatorSingle : IsSingle left separator) :
    rel4 left separator = rel4 right separator := by
  have separatorRightSingle :
      IsSingle right separator :=
    (sameIsSingle same separator).1 separatorSingle
  calc
    rel4 left separator =
        rel4Summary left separator :=
      rel4_eq_summary left separator separatorSingle
    _ = rel4Summary right separator :=
      rel4Summary_eq_of_signatures
        firstOccurrences same separator separatorSingle
    _ = rel4 right separator :=
      (rel4_eq_summary
        right separator separatorRightSingle).symm

/-- The joint semantic coordinates supplied by the two D378 factors determine
the complete public D378 signature. -/
theorem sameD378Signature_of_factor_signatures
    (identity : Identity Nat)
    (firstOccurrences :
      firstOccurrenceSequence identity.lhs.toList =
        firstOccurrenceSequence identity.rhs.toList)
    (separatorSignature :
      SemigroupBasis.CoRoots.S5_378.SameSeparatorSimpleSignature
        identity.lhs identity.rhs) :
    SameD378Signature identity.lhs identity.rhs := by
  refine
    ⟨head_eq_of_firstOccurrenceSequence_eq firstOccurrences,
      singlesSeq_eq_of_signatures
        firstOccurrences separatorSignature,
      plasmaSeq_eq_of_signatures
        firstOccurrences separatorSignature, ?_⟩
  intro separator separatorSingle
  exact
    ⟨beforeOpenList_eq_of_signatures
        firstOccurrences separatorSignature
          separator separatorSingle,
      rel4_eq_of_signatures
        firstOccurrences separatorSignature
          separator separatorSingle⟩

/-- The corrected seven-law system is sound in the left factor. -/
theorem modelsS3_16 :
    Models SemigroupBasis.Generated.S3_16.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S3_16.table basis toFinThree (by decide)

/-- The corrected seven-law system is sound in the direct right factor. -/
theorem modelsS5_378 :
    Models SemigroupBasis.CoRoots.S5_378.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.CoRoots.S5_378.table basis toFinThree (by decide)

/-- The same seven laws are sound in the opposite right factor. -/
theorem modelsS5_378Opposite :
    Models
      SemigroupBasis.CoRoots.S5_378.table.semigroup.opposite basis := by
  rw [← oppositeFiniteTable_semigroup]
  exact
    FiniteCertificate.checkModels_sound
      (oppositeFiniteTable SemigroupBasis.CoRoots.S5_378.table)
      basis toFinThree (by decide)

/-- The left factor fixes the first-occurrence sequence of every valid
identity. This is the ordered support coordinate used by the `D_378`
signature bridge. -/
theorem firstOccurrenceSequence_eq_of_s3_16_valid
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_16.table.semigroup) :
    firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList := by
  apply firstOccurrenceSequence_eq_of_valid identity
  simpa only
    [SemigroupBasis.Generated.S3_16.table_eq_catalogue_model] using valid

/-- Direct-factor validity supplies every coordinate of the D378
signature expected by the shared normalizer. -/
theorem sameD378Signature_of_direct_factor_valid
    (identity : Identity Nat)
    (leftValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_16.table.semigroup)
    (rightValid :
      identity.SatisfiedBy
        SemigroupBasis.CoRoots.S5_378.table.semigroup) :
    SameD378Signature identity.lhs identity.rhs :=
  sameD378Signature_of_factor_signatures identity
    (firstOccurrenceSequence_eq_of_s3_16_valid
      identity leftValid)
    (SemigroupBasis.CoRoots.S5_378.valid_sameSignature
      identity rightValid)

/-- Opposite-factor validity yields the same D378 coordinates: the S5
separator signature is first obtained on reversed words and then transported
back by swapping the two cut supports. -/
theorem sameD378Signature_of_opposite_factor_valid
    (identity : Identity Nat)
    (leftValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_16.table.semigroup)
    (rightValid :
      identity.SatisfiedBy
        SemigroupBasis.CoRoots.S5_378.table.semigroup.opposite) :
    SameD378Signature identity.lhs identity.rhs := by
  have reversedValid :
      identity.reversed.SatisfiedBy
        SemigroupBasis.CoRoots.S5_378.table.semigroup :=
    (Identity.satisfiedBy_opposite_iff_reversed
      identity
        SemigroupBasis.CoRoots.S5_378.table.semigroup).1
          rightValid
  have reversedSignature :
      SemigroupBasis.CoRoots.S5_378.SameSeparatorSimpleSignature
        identity.lhs.reverse identity.rhs.reverse := by
    simpa [Identity.reversed] using
      SemigroupBasis.CoRoots.S5_378.valid_sameSignature
        identity.reversed reversedValid
  exact
    sameD378Signature_of_factor_signatures identity
      (firstOccurrenceSequence_eq_of_s3_16_valid
        identity leftValid)
      (separatorSignature_of_reversed reversedSignature)

/-- Single application point between the table-side direct-factor bridge and
the shared normalizer's stable `derivesOfSameD378` interface. -/
theorem derives_of_direct_factor_valid
    (signatureComplete :
      ∀ {left right : Word Nat},
        SameD378Signature left right →
          Derives basis left right)
    (identity : Identity Nat)
    (leftValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_16.table.semigroup)
    (rightValid :
      identity.SatisfiedBy
        SemigroupBasis.CoRoots.S5_378.table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  signatureComplete <|
    sameD378Signature_of_direct_factor_valid
      identity leftValid rightValid

/-- Single application point for the opposite S5 orientation. -/
theorem derives_of_opposite_factor_valid
    (signatureComplete :
      ∀ {left right : Word Nat},
        SameD378Signature left right →
          Derives basis left right)
    (identity : Identity Nat)
    (leftValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_16.table.semigroup)
    (rightValid :
      identity.SatisfiedBy
        SemigroupBasis.CoRoots.S5_378.table.semigroup.opposite) :
    Derives basis identity.lhs identity.rhs :=
  signatureComplete <|
    sameD378Signature_of_opposite_factor_valid
      identity leftValid rightValid

/-- A completeness theorem stated against the frozen D378 signature
immediately closes the direct factor intersection. -/
def directIntersectionBasisOfSignatureComplete
    (signatureComplete :
      ∀ {left right : Word Nat},
        SameD378Signature left right →
          Derives basis left right) :
    IntersectionBasis
      SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.CoRoots.S5_378.table.semigroup basis where
  leftModels := modelsS3_16
  rightModels := modelsS5_378
  complete := fun identity leftValid rightValid =>
    derives_of_direct_factor_valid
      signatureComplete identity leftValid rightValid

/-- The same signature-completeness theorem closes the opposite factor
intersection after the reversal transport above. -/
def oppositeIntersectionBasisOfSignatureComplete
    (signatureComplete :
      ∀ {left right : Word Nat},
        SameD378Signature left right →
          Derives basis left right) :
    IntersectionBasis
      SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.CoRoots.S5_378.table.semigroup.opposite basis where
  leftModels := modelsS3_16
  rightModels := modelsS5_378Opposite
  complete := fun identity leftValid rightValid =>
    derives_of_opposite_factor_valid
      signatureComplete identity leftValid rightValid

/-- Assemble the direct factor intersection after the shared normalizer has
supplied its semantic completeness implication. -/
def directIntersectionBasisOfComplete
    (complete :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy
            SemigroupBasis.Generated.S3_16.table.semigroup →
          identity.SatisfiedBy
            SemigroupBasis.CoRoots.S5_378.table.semigroup →
          Derives basis identity.lhs identity.rhs) :
    IntersectionBasis
      SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.CoRoots.S5_378.table.semigroup basis where
  leftModels := modelsS3_16
  rightModels := modelsS5_378
  complete := complete

/-- Assemble the opposite factor intersection after the shared normalizer has
supplied its semantic completeness implication. -/
def oppositeIntersectionBasisOfComplete
    (complete :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy
            SemigroupBasis.Generated.S3_16.table.semigroup →
          identity.SatisfiedBy
            SemigroupBasis.CoRoots.S5_378.table.semigroup.opposite →
          Derives basis identity.lhs identity.rhs) :
    IntersectionBasis
      SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.CoRoots.S5_378.table.semigroup.opposite basis where
  leftModels := modelsS3_16
  rightModels := modelsS5_378Opposite
  complete := complete

/-- The corrected joint seven-law basis for the direct
`S3_16 × S5_378` factor intersection. -/
def directIntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.CoRoots.S5_378.table.semigroup basis :=
  directIntersectionBasisOfSignatureComplete derivesOfSameD378

/-- The same joint seven-law basis for the intersection with the opposite
`S5_378` factor. -/
def oppositeIntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.CoRoots.S5_378.table.semigroup.opposite basis :=
  oppositeIntersectionBasisOfSignatureComplete derivesOfSameD378

end SemigroupBasis.CoRoots.Order6FordLordD378
