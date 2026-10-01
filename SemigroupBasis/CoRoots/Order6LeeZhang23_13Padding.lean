import SemigroupBasis.CoRoots.Order6LeeZhang23_9Invariant
import SemigroupBasis.CoRoots.Order6LeeZhang23_9Moves

/-!
# Lee--Zhang Lemma 23.13 endpoint padding

This file isolates the endpoint-removal argument used after the
simple-head-and-simple-final normalization for Proposition 23.9.  The
argument is basis-local: fresh letters make the required endpoints simple,
`Derives.subst` replaces them by the common original endpoints, and the
three short B4 laws remove the resulting duplicate endpoints.

The normalization of words whose two endpoints are already simple is an
explicit callback.  This keeps the padding layer independent of the later
canonical-normalization implementation and prevents an import cycle.
-/

namespace SemigroupBasis.CoRoots.Order6LeeZhang23_13Padding

open SemigroupBasis
open Order6LeeZhang23_9Syntax
open Order6LeeZhang23_9Invariant
open Order6LeeZhang23_9Moves

/-! ## Fresh endpoint words -/

def prependFresh (fresh : Nat) (word : Word Nat) : Word Nat :=
  Word.singleton fresh ++ word

def appendFresh (word : Word Nat) (fresh : Nat) : Word Nat :=
  word ++ Word.singleton fresh

def padBoth (prefixMarker suffix : Nat) (word : Word Nat) : Word Nat :=
  appendFresh (prependFresh prefixMarker word) suffix

@[simp]
private theorem prependFresh_toList (fresh : Nat) (word : Word Nat) :
    (prependFresh fresh word).toList = fresh :: word.toList := by
  unfold prependFresh
  rw [Word.toList_append, Word.toList_singleton]
  rfl

@[simp]
private theorem appendFresh_toList (word : Word Nat) (fresh : Nat) :
    (appendFresh word fresh).toList = word.toList ++ [fresh] := by
  unfold appendFresh
  rw [Word.toList_append, Word.toList_singleton]

@[simp]
private theorem prependFresh_head (fresh : Nat) (word : Word Nat) :
    (prependFresh fresh word).head = fresh := by
  unfold prependFresh
  exact Word.append_head _ _

@[simp]
private theorem prependFresh_final (fresh : Nat) (word : Word Nat) :
    (prependFresh fresh word).final = word.final := by
  unfold prependFresh
  exact Word.final_append _ _

@[simp]
private theorem appendFresh_head (word : Word Nat) (fresh : Nat) :
    (appendFresh word fresh).head = word.head := by
  unfold appendFresh
  exact Word.append_head _ _

@[simp]
private theorem appendFresh_final (word : Word Nat) (fresh : Nat) :
    (appendFresh word fresh).final = fresh := by
  unfold appendFresh
  rw [Word.final_append]
  rfl

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

/-- The deterministic prefix marker for one identity. -/
def paddingPrefix (left right : Word Nat) : Nat :=
  freshAbove (left.toList ++ right.toList)

/-- The deterministic suffix marker is the successor of the prefix marker. -/
def paddingSuffix (left right : Word Nat) : Nat :=
  paddingPrefix left right + 1

theorem paddingPrefix_not_mem_left (left right : Word Nat) :
    paddingPrefix left right ∉ left.toList := by
  intro member
  have impossible :=
    lt_freshAbove_of_mem (paddingPrefix left right)
      (left.toList ++ right.toList)
      (List.mem_append.mpr (Or.inl member))
  exact Nat.lt_irrefl _ impossible

theorem paddingPrefix_not_mem_right (left right : Word Nat) :
    paddingPrefix left right ∉ right.toList := by
  intro member
  have impossible :=
    lt_freshAbove_of_mem (paddingPrefix left right)
      (left.toList ++ right.toList)
      (List.mem_append.mpr (Or.inr member))
  exact Nat.lt_irrefl _ impossible

theorem paddingSuffix_not_mem_left (left right : Word Nat) :
    paddingSuffix left right ∉ left.toList := by
  intro member
  have belowPrefix :=
    lt_freshAbove_of_mem (paddingSuffix left right)
      (left.toList ++ right.toList)
      (List.mem_append.mpr (Or.inl member))
  unfold paddingSuffix paddingPrefix at belowPrefix
  omega

theorem paddingSuffix_not_mem_right (left right : Word Nat) :
    paddingSuffix left right ∉ right.toList := by
  intro member
  have belowPrefix :=
    lt_freshAbove_of_mem (paddingSuffix left right)
      (left.toList ++ right.toList)
      (List.mem_append.mpr (Or.inr member))
  unfold paddingSuffix paddingPrefix at belowPrefix
  omega

theorem paddingPrefix_ne_paddingSuffix (left right : Word Nat) :
    paddingPrefix left right ≠ paddingSuffix left right := by
  unfold paddingSuffix
  omega

/-! ## Elementary support, simplicity, and adjacency facts -/

private theorem word_final_mem_toList (word : Word Nat) :
    word.final ∈ word.toList := by
  cases word with
  | mk head tail =>
      simpa [Word.final, Word.toList] using
        (List.getLastD_mem_cons (l := tail) (a := head))

private theorem adjacentPair_letters_mem_toList
    {word : Word Nat} {source target : Nat}
    (edge : (source, target) ∈ word.adjacentPairs) :
    source ∈ word.toList ∧ target ∈ word.toList := by
  cases word with
  | mk head tail =>
      change
        (source, target) ∈ Word.adjacentPairsFrom head tail at edge
      change source ∈ head :: tail ∧ target ∈ head :: tail
      induction tail generalizing head with
      | nil =>
          simp [Word.adjacentPairsFrom] at edge
      | cons next rest induction =>
          simp only [Word.adjacentPairsFrom, List.mem_cons] at edge
          rcases edge with edge | edge
          · cases edge
            exact ⟨by simp, by simp⟩
          · obtain ⟨sourceMember, targetMember⟩ := induction next edge
            exact
              ⟨List.Mem.tail head sourceMember,
                List.Mem.tail head targetMember⟩

theorem globallySimple_prependFresh
    (word : Word Nat) (fresh : Nat)
    (freshAbsent : fresh ∉ word.toList) :
    S5_402.GloballySimple (prependFresh fresh word) fresh := by
  unfold S5_402.GloballySimple S5_107.SimpleIn
  rw [prependFresh_toList]
  simp [List.count_eq_zero.mpr freshAbsent]

theorem globallySimple_appendFresh
    (word : Word Nat) (fresh : Nat)
    (freshAbsent : fresh ∉ word.toList) :
    S5_402.GloballySimple (appendFresh word fresh) fresh := by
  unfold S5_402.GloballySimple S5_107.SimpleIn
  rw [appendFresh_toList]
  simp [List.count_eq_zero.mpr freshAbsent]

theorem globallySimple_prependFresh_iff_of_ne
    (word : Word Nat) (fresh letter : Nat)
    (different : letter ≠ fresh) :
    S5_402.GloballySimple (prependFresh fresh word) letter ↔
      S5_402.GloballySimple word letter := by
  unfold S5_402.GloballySimple S5_107.SimpleIn
  rw [prependFresh_toList]
  simp [different, Ne.symm different]

theorem globallySimple_appendFresh_iff_of_ne
    (word : Word Nat) (fresh letter : Nat)
    (different : letter ≠ fresh) :
    S5_402.GloballySimple (appendFresh word fresh) letter ↔
      S5_402.GloballySimple word letter := by
  unfold S5_402.GloballySimple S5_107.SimpleIn
  rw [appendFresh_toList]
  simp [different, Ne.symm different]

theorem mem_adjacentPairs_prependFresh_iff
    (word : Word Nat) (fresh source target : Nat) :
    (source, target) ∈ (prependFresh fresh word).adjacentPairs ↔
      (source = fresh ∧ target = word.head) ∨
        (source, target) ∈ word.adjacentPairs := by
  simp [prependFresh, Word.adjacentPairs_append,
    Word.adjacentPairs, Word.adjacentPairsFrom, Word.final]

theorem mem_adjacentPairs_appendFresh_iff
    (word : Word Nat) (fresh source target : Nat) :
    (source, target) ∈ (appendFresh word fresh).adjacentPairs ↔
      (source, target) ∈ word.adjacentPairs ∨
        (source = word.final ∧ target = fresh) := by
  change
    (source, target) ∈
        (word ++ Word.singleton fresh).adjacentPairs ↔
      (source, target) ∈ word.adjacentPairs ∨
        (source = word.final ∧ target = fresh)
  rw [Word.adjacentPairs_append]
  simp [Word.adjacentPairs, Word.adjacentPairsFrom]

/-! ## The compact signature survives fresh padding -/

private theorem sameSimpleSuccessorSignature_prependFresh
    {left right : Word Nat} {fresh : Nat}
    (same : S5_402.SameSimpleSuccessorSignature left right)
    (freshLeft : fresh ∉ left.toList)
    (freshRight : fresh ∉ right.toList) :
    S5_402.SameSimpleSuccessorSignature
      (prependFresh fresh left) (prependFresh fresh right) := by
  refine
    { capped := ?_
      support := ?_
      head := rfl
      globallySimple := ?_
      successor := ?_ }
  · intro letter
    by_cases equal : letter = fresh
    · subst letter
      simp [S5_402.cappedMultiplicity, S5_107.cappedMultiplicity,
        prependFresh_toList,
        List.count_eq_zero.mpr freshLeft,
        List.count_eq_zero.mpr freshRight]
    · simpa [S5_402.cappedMultiplicity, S5_107.cappedMultiplicity,
        prependFresh_toList, equal, Ne.symm equal] using
          same.capped letter
  · intro letter
    simp only [prependFresh, Word.toList_append,
      Word.toList_singleton, List.mem_append, List.mem_singleton]
    exact or_congr Iff.rfl (same.support letter)
  · intro letter
    by_cases equal : letter = fresh
    · subst letter
      exact
        ⟨fun _ => globallySimple_prependFresh right fresh freshRight,
          fun _ => globallySimple_prependFresh left fresh freshLeft⟩
    · exact
        (globallySimple_prependFresh_iff_of_ne left fresh letter equal).trans <|
          (same.globallySimple letter).trans <|
            (globallySimple_prependFresh_iff_of_ne
              right fresh letter equal).symm
  · intro source target
    constructor
    · rintro ⟨different, sourceSimple, edge⟩
      rcases
          (mem_adjacentPairs_prependFresh_iff
            left fresh source target).mp edge with
        ⟨sourceEqual, targetEqual⟩ | oldEdge
      · subst source
        subst target
        exact
          ⟨different,
            globallySimple_prependFresh right fresh freshRight,
            (mem_adjacentPairs_prependFresh_iff
              right fresh fresh left.head).mpr <|
                Or.inl ⟨rfl, same.head⟩⟩
      · have sourceMember :=
          (adjacentPair_letters_mem_toList oldEdge).1
        have sourceNeFresh : source ≠ fresh := by
          intro equal
          subst source
          exact freshLeft sourceMember
        have oldSimple : S5_402.GloballySimple left source :=
          (globallySimple_prependFresh_iff_of_ne
            left fresh source sourceNeFresh).mp sourceSimple
        rcases (same.successor source target).mp
            ⟨different, oldSimple, oldEdge⟩ with
          ⟨rightDifferent, rightSimple, rightEdge⟩
        exact
          ⟨rightDifferent,
            (globallySimple_prependFresh_iff_of_ne
              right fresh source sourceNeFresh).mpr rightSimple,
            (mem_adjacentPairs_prependFresh_iff
              right fresh source target).mpr (Or.inr rightEdge)⟩
    · rintro ⟨different, sourceSimple, edge⟩
      rcases
          (mem_adjacentPairs_prependFresh_iff
            right fresh source target).mp edge with
        ⟨sourceEqual, targetEqual⟩ | oldEdge
      · subst source
        subst target
        exact
          ⟨different,
            globallySimple_prependFresh left fresh freshLeft,
            (mem_adjacentPairs_prependFresh_iff
              left fresh fresh right.head).mpr <|
                Or.inl ⟨rfl, same.head.symm⟩⟩
      · have sourceMember :=
          (adjacentPair_letters_mem_toList oldEdge).1
        have sourceNeFresh : source ≠ fresh := by
          intro equal
          subst source
          exact freshRight sourceMember
        have oldSimple : S5_402.GloballySimple right source :=
          (globallySimple_prependFresh_iff_of_ne
            right fresh source sourceNeFresh).mp sourceSimple
        rcases (same.successor source target).mpr
            ⟨different, oldSimple, oldEdge⟩ with
          ⟨leftDifferent, leftSimple, leftEdge⟩
        exact
          ⟨leftDifferent,
            (globallySimple_prependFresh_iff_of_ne
              left fresh source sourceNeFresh).mpr leftSimple,
            (mem_adjacentPairs_prependFresh_iff
              left fresh source target).mpr (Or.inr leftEdge)⟩

private theorem sameSimpleSuccessorSignature_appendFresh
    {left right : Word Nat} {fresh : Nat}
    (same : S5_402.SameSimpleSuccessorSignature left right)
    (sameFinal : left.final = right.final)
    (freshLeft : fresh ∉ left.toList)
    (freshRight : fresh ∉ right.toList) :
    S5_402.SameSimpleSuccessorSignature
      (appendFresh left fresh) (appendFresh right fresh) := by
  refine
    { capped := ?_
      support := ?_
      head := same.head
      globallySimple := ?_
      successor := ?_ }
  · intro letter
    by_cases equal : letter = fresh
    · subst letter
      simp [S5_402.cappedMultiplicity, S5_107.cappedMultiplicity,
        appendFresh_toList,
        List.count_eq_zero.mpr freshLeft,
        List.count_eq_zero.mpr freshRight]
    · simpa [S5_402.cappedMultiplicity, S5_107.cappedMultiplicity,
        appendFresh_toList, equal, Ne.symm equal] using
          same.capped letter
  · intro letter
    simp only [appendFresh, Word.toList_append,
      Word.toList_singleton, List.mem_append, List.mem_singleton]
    exact or_congr (same.support letter) Iff.rfl
  · intro letter
    by_cases equal : letter = fresh
    · subst letter
      exact
        ⟨fun _ => globallySimple_appendFresh right fresh freshRight,
          fun _ => globallySimple_appendFresh left fresh freshLeft⟩
    · exact
        (globallySimple_appendFresh_iff_of_ne left fresh letter equal).trans <|
          (same.globallySimple letter).trans <|
            (globallySimple_appendFresh_iff_of_ne
              right fresh letter equal).symm
  · intro source target
    constructor
    · rintro ⟨different, sourceSimple, edge⟩
      rcases
          (mem_adjacentPairs_appendFresh_iff
            left fresh source target).mp edge with
        oldEdge | ⟨sourceEqual, targetEqual⟩
      · have sourceMember :=
          (adjacentPair_letters_mem_toList oldEdge).1
        have sourceNeFresh : source ≠ fresh := by
          intro equal
          subst source
          exact freshLeft sourceMember
        have oldSimple : S5_402.GloballySimple left source :=
          (globallySimple_appendFresh_iff_of_ne
            left fresh source sourceNeFresh).mp sourceSimple
        rcases (same.successor source target).mp
            ⟨different, oldSimple, oldEdge⟩ with
          ⟨rightDifferent, rightSimple, rightEdge⟩
        exact
          ⟨rightDifferent,
            (globallySimple_appendFresh_iff_of_ne
              right fresh source sourceNeFresh).mpr rightSimple,
            (mem_adjacentPairs_appendFresh_iff
              right fresh source target).mpr (Or.inl rightEdge)⟩
      · subst source
        subst target
        have finalNeFresh : left.final ≠ fresh := by
          intro equal
          apply freshLeft
          rw [← equal]
          exact word_final_mem_toList left
        have leftFinalSimple :
            S5_402.GloballySimple left left.final :=
          (globallySimple_appendFresh_iff_of_ne
            left fresh left.final finalNeFresh).mp sourceSimple
        have rightFinalSimple :
            S5_402.GloballySimple right left.final :=
          (same.globallySimple left.final).mp leftFinalSimple
        exact
          ⟨different,
            (globallySimple_appendFresh_iff_of_ne
              right fresh left.final finalNeFresh).mpr rightFinalSimple,
            (mem_adjacentPairs_appendFresh_iff
              right fresh left.final fresh).mpr <|
                Or.inr ⟨sameFinal, rfl⟩⟩
    · rintro ⟨different, sourceSimple, edge⟩
      rcases
          (mem_adjacentPairs_appendFresh_iff
            right fresh source target).mp edge with
        oldEdge | ⟨sourceEqual, targetEqual⟩
      · have sourceMember :=
          (adjacentPair_letters_mem_toList oldEdge).1
        have sourceNeFresh : source ≠ fresh := by
          intro equal
          subst source
          exact freshRight sourceMember
        have oldSimple : S5_402.GloballySimple right source :=
          (globallySimple_appendFresh_iff_of_ne
            right fresh source sourceNeFresh).mp sourceSimple
        rcases (same.successor source target).mpr
            ⟨different, oldSimple, oldEdge⟩ with
          ⟨leftDifferent, leftSimple, leftEdge⟩
        exact
          ⟨leftDifferent,
            (globallySimple_appendFresh_iff_of_ne
              left fresh source sourceNeFresh).mpr leftSimple,
            (mem_adjacentPairs_appendFresh_iff
              left fresh source target).mpr (Or.inl leftEdge)⟩
      · subst source
        subst target
        have finalNeFresh : right.final ≠ fresh := by
          intro equal
          apply freshRight
          rw [← equal]
          exact word_final_mem_toList right
        have rightFinalSimple :
            S5_402.GloballySimple right right.final :=
          (globallySimple_appendFresh_iff_of_ne
            right fresh right.final finalNeFresh).mp sourceSimple
        have leftFinalSimple :
            S5_402.GloballySimple left right.final :=
          (same.globallySimple right.final).mpr rightFinalSimple
        exact
          ⟨different,
            (globallySimple_appendFresh_iff_of_ne
              left fresh right.final finalNeFresh).mpr leftFinalSimple,
            (mem_adjacentPairs_appendFresh_iff
              left fresh right.final fresh).mpr <|
                Or.inr ⟨sameFinal.symm, rfl⟩⟩

theorem sameLeeZhang23_9Signature_prependFresh
    {left right : Word Nat} {fresh : Nat}
    (same : SameLeeZhang23_9Signature left right)
    (freshLeft : fresh ∉ left.toList)
    (freshRight : fresh ∉ right.toList) :
    SameLeeZhang23_9Signature
      (prependFresh fresh left) (prependFresh fresh right) := by
  refine ⟨rfl, ?_⟩
  have reversed :=
    sameSimpleSuccessorSignature_appendFresh
      same.reversedS5_402
      (by simpa only [reverse_final_eq_head] using same.head)
      (by simpa only [Word.toList_reverse, List.mem_reverse] using freshLeft)
      (by simpa only [Word.toList_reverse, List.mem_reverse] using freshRight)
  simpa [prependFresh, appendFresh, Word.reverse_append] using reversed

theorem sameLeeZhang23_9Signature_appendFresh
    {left right : Word Nat} {fresh : Nat}
    (same : SameLeeZhang23_9Signature left right)
    (freshLeft : fresh ∉ left.toList)
    (freshRight : fresh ∉ right.toList) :
    SameLeeZhang23_9Signature
      (appendFresh left fresh) (appendFresh right fresh) := by
  refine ⟨same.head, ?_⟩
  have reversed :=
    sameSimpleSuccessorSignature_prependFresh
      same.reversedS5_402
      (by simpa only [Word.toList_reverse, List.mem_reverse] using freshLeft)
      (by simpa only [Word.toList_reverse, List.mem_reverse] using freshRight)
  simpa [prependFresh, appendFresh, Word.reverse_append] using reversed

theorem sameLeeZhang23_9Signature_padBoth
    {left right : Word Nat} {prefixMarker suffix : Nat}
    (same : SameLeeZhang23_9Signature left right)
    (prefixLeft : prefixMarker ∉ left.toList)
    (prefixRight : prefixMarker ∉ right.toList)
    (suffixLeft : suffix ∉ left.toList)
    (suffixRight : suffix ∉ right.toList)
    (different : prefixMarker ≠ suffix) :
    SameLeeZhang23_9Signature
      (padBoth prefixMarker suffix left)
      (padBoth prefixMarker suffix right) := by
  have prefixed :=
    sameLeeZhang23_9Signature_prependFresh
      same prefixLeft prefixRight
  have suffixPrefixedLeft :
      suffix ∉ (prependFresh prefixMarker left).toList := by
    simp [prependFresh_toList, suffixLeft,
      Ne.symm different]
  have suffixPrefixedRight :
      suffix ∉ (prependFresh prefixMarker right).toList := by
    simp [prependFresh_toList, suffixRight,
      Ne.symm different]
  exact sameLeeZhang23_9Signature_appendFresh prefixed
    suffixPrefixedLeft suffixPrefixedRight

/-! ## Non-simplicity and padded endpoints -/

private theorem nonSimple_prependFresh
    (word : Word Nat) (fresh : Nat)
    (freshAbsent : fresh ∉ word.toList)
    (nonSimple : ∃ marker, 2 ≤ word.toList.count marker) :
    ∃ marker, 2 ≤ (prependFresh fresh word).toList.count marker := by
  obtain ⟨marker, multiple⟩ := nonSimple
  have markerMember : marker ∈ word.toList :=
    List.count_pos_iff.mp (by omega)
  have markerNeFresh : marker ≠ fresh := by
    intro equal
    subst marker
    exact freshAbsent markerMember
  exact ⟨marker, by
    simpa [prependFresh_toList, markerNeFresh,
      Ne.symm markerNeFresh] using multiple⟩

private theorem nonSimple_appendFresh
    (word : Word Nat) (fresh : Nat)
    (freshAbsent : fresh ∉ word.toList)
    (nonSimple : ∃ marker, 2 ≤ word.toList.count marker) :
    ∃ marker, 2 ≤ (appendFresh word fresh).toList.count marker := by
  obtain ⟨marker, multiple⟩ := nonSimple
  have markerMember : marker ∈ word.toList :=
    List.count_pos_iff.mp (by omega)
  have markerNeFresh : marker ≠ fresh := by
    intro equal
    subst marker
    exact freshAbsent markerMember
  exact ⟨marker, by
    simpa [appendFresh_toList, markerNeFresh,
      Ne.symm markerNeFresh] using multiple⟩

private theorem multiple_of_mem_of_not_globallySimple
    (word : Word Nat) (letter : Nat)
    (member : letter ∈ word.toList)
    (notSimple : ¬S5_402.GloballySimple word letter) :
    2 ≤ word.toList.count letter := by
  have positive : 0 < word.toList.count letter :=
    List.count_pos_iff.mpr member
  unfold S5_402.GloballySimple S5_107.SimpleIn at notSimple
  omega

/-! ## Substituting the fresh endpoints -/

private def freshSubstitution
    (fresh : Nat) (replacement : Word Nat) : Nat → Word Nat :=
  fun selected =>
    if selected = fresh then replacement else Word.singleton selected

private theorem flatMap_freshSubstitution_of_not_mem
    (fresh : Nat) (replacement : Word Nat) :
    ∀ letters : List Nat, fresh ∉ letters →
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
      rw [List.flatMap_cons,
        flatMap_freshSubstitution_of_not_mem
          fresh replacement rest restAbsent]
      simp [freshSubstitution, selectedNe]

private theorem bind_fresh_prefix
    (word : Word Nat) (fresh : Nat) (replacement : Word Nat)
    (freshAbsent : fresh ∉ word.toList) :
    (prependFresh fresh word).bind
        (freshSubstitution fresh replacement) =
      replacement ++ word := by
  apply Word.toList_injective
  rw [Word.toList_bind, prependFresh, Word.toList_append,
    Word.toList_singleton, List.flatMap_append,
    flatMap_freshSubstitution_of_not_mem
      fresh replacement word.toList freshAbsent,
    Word.toList_append]
  simp [freshSubstitution]

private theorem bind_fresh_suffix
    (word : Word Nat) (fresh : Nat) (replacement : Word Nat)
    (freshAbsent : fresh ∉ word.toList) :
    (appendFresh word fresh).bind
        (freshSubstitution fresh replacement) =
      word ++ replacement := by
  apply Word.toList_injective
  rw [Word.toList_bind, appendFresh, Word.toList_append,
    Word.toList_singleton, List.flatMap_append,
    flatMap_freshSubstitution_of_not_mem
      fresh replacement word.toList freshAbsent,
    Word.toList_append]
  simp [freshSubstitution]

theorem derives_substitute_prependFresh
    {left right : Word Nat} {fresh replacement : Nat}
    (freshLeft : fresh ∉ left.toList)
    (freshRight : fresh ∉ right.toList)
    (derivation : Derives B4Basis
      (prependFresh fresh left) (prependFresh fresh right)) :
    Derives B4Basis
      (Word.singleton replacement ++ left)
      (Word.singleton replacement ++ right) := by
  have substituted :=
    Derives.subst derivation
      (freshSubstitution fresh (Word.singleton replacement))
  rw [bind_fresh_prefix left fresh (Word.singleton replacement) freshLeft,
    bind_fresh_prefix right fresh (Word.singleton replacement) freshRight]
    at substituted
  exact substituted

theorem derives_substitute_appendFresh
    {left right : Word Nat} {fresh replacement : Nat}
    (freshLeft : fresh ∉ left.toList)
    (freshRight : fresh ∉ right.toList)
    (derivation : Derives B4Basis
      (appendFresh left fresh) (appendFresh right fresh)) :
    Derives B4Basis
      (left ++ Word.singleton replacement)
      (right ++ Word.singleton replacement) := by
  have substituted :=
    Derives.subst derivation
      (freshSubstitution fresh (Word.singleton replacement))
  rw [bind_fresh_suffix left fresh (Word.singleton replacement) freshLeft,
    bind_fresh_suffix right fresh (Word.singleton replacement) freshRight]
    at substituted
  exact substituted

theorem derives_substitute_padBoth
    {left right : Word Nat}
    {prefixMarker suffix head final : Nat}
    (prefixLeft : prefixMarker ∉ left.toList)
    (prefixRight : prefixMarker ∉ right.toList)
    (suffixLeft : suffix ∉ left.toList)
    (suffixRight : suffix ∉ right.toList)
    (prefixNeSuffix : prefixMarker ≠ suffix)
    (suffixNeHead : suffix ≠ head)
    (derivation : Derives B4Basis
      (padBoth prefixMarker suffix left)
      (padBoth prefixMarker suffix right)) :
    Derives B4Basis
      ((Word.singleton head ++ left) ++ Word.singleton final)
      ((Word.singleton head ++ right) ++ Word.singleton final) := by
  have prefixAbsentLeftExtended :
      prefixMarker ∉ (appendFresh left suffix).toList := by
    simp [appendFresh_toList, prefixLeft, prefixNeSuffix]
  have prefixAbsentRightExtended :
      prefixMarker ∉ (appendFresh right suffix).toList := by
    simp [appendFresh_toList, prefixRight, prefixNeSuffix]
  have afterPrefixSubstitution :=
    Derives.subst derivation
      (freshSubstitution prefixMarker (Word.singleton head))
  have bindPrefixLeft :
      (padBoth prefixMarker suffix left).bind
          (freshSubstitution prefixMarker (Word.singleton head)) =
        (Word.singleton head ++ left) ++ Word.singleton suffix := by
    simpa [padBoth, prependFresh, appendFresh, Word.append_assoc] using
      bind_fresh_prefix (appendFresh left suffix) prefixMarker
        (Word.singleton head) prefixAbsentLeftExtended
  have bindPrefixRight :
      (padBoth prefixMarker suffix right).bind
          (freshSubstitution prefixMarker (Word.singleton head)) =
        (Word.singleton head ++ right) ++ Word.singleton suffix := by
    simpa [padBoth, prependFresh, appendFresh, Word.append_assoc] using
      bind_fresh_prefix (appendFresh right suffix) prefixMarker
        (Word.singleton head) prefixAbsentRightExtended
  rw [bindPrefixLeft, bindPrefixRight] at afterPrefixSubstitution
  have suffixAbsentLeftPrefixed :
      suffix ∉ (Word.singleton head ++ left).toList := by
    change suffix ∉ head :: left.toList
    intro member
    rcases List.mem_cons.mp member with equal | member
    · exact suffixNeHead equal
    · exact suffixLeft member
  have suffixAbsentRightPrefixed :
      suffix ∉ (Word.singleton head ++ right).toList := by
    change suffix ∉ head :: right.toList
    intro member
    rcases List.mem_cons.mp member with equal | member
    · exact suffixNeHead equal
    · exact suffixRight member
  have afterSuffixSubstitution :=
    Derives.subst afterPrefixSubstitution
      (freshSubstitution suffix (Word.singleton final))
  change
    Derives B4Basis
      ((appendFresh (Word.singleton head ++ left) suffix).bind
        (freshSubstitution suffix (Word.singleton final)))
      ((appendFresh (Word.singleton head ++ right) suffix).bind
        (freshSubstitution suffix (Word.singleton final)))
    at afterSuffixSubstitution
  rw [bind_fresh_suffix (Word.singleton head ++ left) suffix
      (Word.singleton final) suffixAbsentLeftPrefixed,
    bind_fresh_suffix (Word.singleton head ++ right) suffix
      (Word.singleton final) suffixAbsentRightPrefixed]
    at afterSuffixSubstitution
  exact afterSuffixSubstitution

/-! ## B4 duplication and contraction at the original endpoints -/

private theorem derives_of_listDerives_toList
    {left right : Word Nat}
    (derivation : B4ListDerives left.toList right.toList) :
    Derives B4Basis left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simpa [S5_107.listWordOfCons, Word.toList] using
            S5_107.ListDerives.toWord derivation

theorem derivesDuplicateHead
    (word : Word Nat)
    (multiple : 2 ≤ word.toList.count word.head) :
    Derives B4Basis word (Word.singleton word.head ++ word) := by
  cases word with
  | mk head tail =>
      have listed :=
        listDerivesDuplicateSelectedOccurrence head [] tail (by
          simpa [Word.toList] using multiple)
      apply derives_of_listDerives_toList
      simpa [Word.toList, Word.singleton, Word.append] using listed

private theorem dropLast_append_final
    (head : Nat) (tail : List Nat) :
    (head :: tail).dropLast ++ [tail.getLastD head] =
      head :: tail := by
  have reconstruction :=
    List.dropLast_concat_getLast
      (l := head :: tail) (by simp)
  rw [List.getLast_eq_getLastD] at reconstruction
  simpa only [List.getLastD_cons] using reconstruction

theorem derivesDuplicateFinal
    (word : Word Nat)
    (multiple : 2 ≤ word.toList.count word.final) :
    Derives B4Basis word (word ++ Word.singleton word.final) := by
  cases word with
  | mk head tail =>
      have reconstruction := dropLast_append_final head tail
      have selectedMultiple :
          2 ≤
            (((head :: tail).dropLast ++ [tail.getLastD head]) ++ []).count
              (tail.getLastD head) := by
        rw [List.append_nil, reconstruction]
        simpa only [Word.toList, Word.final] using multiple
      have listed :=
        listDerivesDuplicateSelectedOccurrence
          (tail.getLastD head) (head :: tail).dropLast [] selectedMultiple
      apply derives_of_listDerives_toList
      change B4ListDerives
        (head :: tail)
        ((head :: tail) ++ [tail.getLastD head])
      rw [← reconstruction]
      simpa only [List.append_nil, List.append_assoc,
        List.singleton_append] using listed

theorem derivesDuplicateEndpoints
    (word : Word Nat)
    (headMultiple : 2 ≤ word.toList.count word.head)
    (finalMultiple : 2 ≤ word.toList.count word.final) :
    Derives B4Basis word
      ((Word.singleton word.head ++ word) ++
        Word.singleton word.final) := by
  have headStep := derivesDuplicateHead word headMultiple
  have finalStep :=
    Derives.prepend (Word.singleton word.head)
      (derivesDuplicateFinal word finalMultiple)
  have finalStep' :
      Derives B4Basis
        (Word.singleton word.head ++ word)
        ((Word.singleton word.head ++ word) ++
          Word.singleton word.final) := by
    simpa [Word.append_assoc] using finalStep
  exact headStep.trans finalStep'

/-! ## Lemma 23.13: removing the endpoint hypotheses -/

/-- The only input expected from the canonical normalization layer. -/
def SimpleEndpointNormalizer : Prop :=
  ∀ {left right : Word Nat},
    SameLeeZhang23_9Signature left right →
    (∃ marker, 2 ≤ left.toList.count marker) →
    S5_402.GloballySimple left left.head →
    S5_402.GloballySimple left left.final →
    Derives B4Basis left right

theorem derives_of_nonsimpleHead_simpleFinal
    (normalize : SimpleEndpointNormalizer)
    {left right : Word Nat}
    (same : SameLeeZhang23_9Signature left right)
    (nonSimple : ∃ marker, 2 ≤ left.toList.count marker)
    (headNonSimple : ¬S5_402.GloballySimple left left.head)
    (finalSimple : S5_402.GloballySimple left left.final) :
    Derives B4Basis left right := by
  let fresh := paddingPrefix left right
  have freshLeft : fresh ∉ left.toList := by
    simpa [fresh] using paddingPrefix_not_mem_left left right
  have freshRight : fresh ∉ right.toList := by
    simpa [fresh] using paddingPrefix_not_mem_right left right
  have paddedSame :=
    sameLeeZhang23_9Signature_prependFresh
      same freshLeft freshRight
  have paddedNonSimple :=
    nonSimple_prependFresh left fresh freshLeft nonSimple
  have paddedHeadSimple :
      S5_402.GloballySimple
        (prependFresh fresh left) (prependFresh fresh left).head := by
    simpa [prependFresh] using
      globallySimple_prependFresh left fresh freshLeft
  have finalNeFresh : left.final ≠ fresh := by
    intro equal
    apply freshLeft
    rw [← equal]
    exact word_final_mem_toList left
  have paddedFinalSimple :
      S5_402.GloballySimple
        (prependFresh fresh left) (prependFresh fresh left).final := by
    rw [prependFresh_final]
    exact
      (globallySimple_prependFresh_iff_of_ne
        left fresh left.final finalNeFresh).mpr finalSimple
  have padded :=
    normalize paddedSame paddedNonSimple
      paddedHeadSimple paddedFinalSimple
  have substituted :=
    derives_substitute_prependFresh
      (replacement := left.head) freshLeft freshRight padded
  have published :=
    samePublishedLeeZhang23_9Signature_of_compact same
  have leftHeadMultiple : 2 ≤ left.toList.count left.head :=
    multiple_of_mem_of_not_globallySimple left left.head
      (by simp [Word.toList]) headNonSimple
  have rightHeadNonSimple :
      ¬S5_402.GloballySimple right right.head := by
    intro rightSimple
    apply headNonSimple
    exact (published.globallySimple left.head).mpr <| by
      simpa [published.head] using rightSimple
  have rightHeadMultiple : 2 ≤ right.toList.count right.head :=
    multiple_of_mem_of_not_globallySimple right right.head
      (by simp [Word.toList]) rightHeadNonSimple
  have leftExpanded := derivesDuplicateHead left leftHeadMultiple
  have rightExpanded :
      Derives B4Basis right (Word.singleton left.head ++ right) := by
    simpa [published.head] using
      derivesDuplicateHead right rightHeadMultiple
  exact leftExpanded.trans <| substituted.trans rightExpanded.symm

theorem derives_of_simpleHead_nonsimpleFinal
    (normalize : SimpleEndpointNormalizer)
    {left right : Word Nat}
    (same : SameLeeZhang23_9Signature left right)
    (nonSimple : ∃ marker, 2 ≤ left.toList.count marker)
    (headSimple : S5_402.GloballySimple left left.head)
    (finalNonSimple : ¬S5_402.GloballySimple left left.final) :
    Derives B4Basis left right := by
  let fresh := paddingSuffix left right
  have freshLeft : fresh ∉ left.toList := by
    simpa [fresh] using paddingSuffix_not_mem_left left right
  have freshRight : fresh ∉ right.toList := by
    simpa [fresh] using paddingSuffix_not_mem_right left right
  have paddedSame :=
    sameLeeZhang23_9Signature_appendFresh
      same freshLeft freshRight
  have paddedNonSimple :=
    nonSimple_appendFresh left fresh freshLeft nonSimple
  have headNeFresh : left.head ≠ fresh := by
    intro equal
    apply freshLeft
    simp [Word.toList, equal]
  have paddedHeadSimple :
      S5_402.GloballySimple
        (appendFresh left fresh) (appendFresh left fresh).head := by
    simpa [appendFresh] using
      (globallySimple_appendFresh_iff_of_ne
        left fresh left.head headNeFresh).mpr headSimple
  have paddedFinalSimple :
      S5_402.GloballySimple
        (appendFresh left fresh) (appendFresh left fresh).final := by
    simpa [appendFresh] using
      globallySimple_appendFresh left fresh freshLeft
  have padded :=
    normalize paddedSame paddedNonSimple
      paddedHeadSimple paddedFinalSimple
  have substituted :=
    derives_substitute_appendFresh
      (replacement := left.final) freshLeft freshRight padded
  have published :=
    samePublishedLeeZhang23_9Signature_of_compact same
  have leftFinalMultiple : 2 ≤ left.toList.count left.final :=
    multiple_of_mem_of_not_globallySimple left left.final
      (word_final_mem_toList left) finalNonSimple
  have rightFinalNonSimple :
      ¬S5_402.GloballySimple right right.final := by
    intro rightSimple
    apply finalNonSimple
    exact (published.globallySimple left.final).mpr <| by
      simpa [published.final] using rightSimple
  have rightFinalMultiple : 2 ≤ right.toList.count right.final :=
    multiple_of_mem_of_not_globallySimple right right.final
      (word_final_mem_toList right) rightFinalNonSimple
  have leftExpanded := derivesDuplicateFinal left leftFinalMultiple
  have rightExpanded :
      Derives B4Basis right (right ++ Word.singleton left.final) := by
    simpa [published.final] using
      derivesDuplicateFinal right rightFinalMultiple
  exact leftExpanded.trans <| substituted.trans rightExpanded.symm

theorem derives_of_nonsimpleEndpoints
    (normalize : SimpleEndpointNormalizer)
    {left right : Word Nat}
    (same : SameLeeZhang23_9Signature left right)
    (nonSimple : ∃ marker, 2 ≤ left.toList.count marker)
    (headNonSimple : ¬S5_402.GloballySimple left left.head)
    (finalNonSimple : ¬S5_402.GloballySimple left left.final) :
    Derives B4Basis left right := by
  let prefixMarker := paddingPrefix left right
  let suffix := paddingSuffix left right
  have prefixLeft : prefixMarker ∉ left.toList := by
    simpa [prefixMarker] using paddingPrefix_not_mem_left left right
  have prefixRight : prefixMarker ∉ right.toList := by
    simpa [prefixMarker] using paddingPrefix_not_mem_right left right
  have suffixLeft : suffix ∉ left.toList := by
    simpa [suffix] using paddingSuffix_not_mem_left left right
  have suffixRight : suffix ∉ right.toList := by
    simpa [suffix] using paddingSuffix_not_mem_right left right
  have prefixNeSuffix : prefixMarker ≠ suffix := by
    simpa [prefixMarker, suffix] using
      paddingPrefix_ne_paddingSuffix left right
  have paddedSame :=
    sameLeeZhang23_9Signature_padBoth same
      prefixLeft prefixRight suffixLeft suffixRight prefixNeSuffix
  have prefixedNonSimple :=
    nonSimple_prependFresh left prefixMarker prefixLeft nonSimple
  have suffixAbsentPrefixed :
      suffix ∉ (prependFresh prefixMarker left).toList := by
    simp [prependFresh_toList, suffixLeft,
      Ne.symm prefixNeSuffix]
  have paddedNonSimple :=
    nonSimple_appendFresh (prependFresh prefixMarker left) suffix
      suffixAbsentPrefixed prefixedNonSimple
  have prefixSimple :=
    globallySimple_prependFresh left prefixMarker prefixLeft
  have prefixNeSuffix' : prefixMarker ≠ suffix := prefixNeSuffix
  have paddedHeadSimple :
      S5_402.GloballySimple
        (padBoth prefixMarker suffix left)
        (padBoth prefixMarker suffix left).head := by
    have preserved :=
      (globallySimple_appendFresh_iff_of_ne
        (prependFresh prefixMarker left) suffix prefixMarker
          prefixNeSuffix').mpr
        prefixSimple
    simpa [padBoth, appendFresh, prependFresh] using preserved
  have paddedFinalSimple :
      S5_402.GloballySimple
        (padBoth prefixMarker suffix left)
        (padBoth prefixMarker suffix left).final := by
    simpa [padBoth, appendFresh] using
      globallySimple_appendFresh
        (prependFresh prefixMarker left) suffix suffixAbsentPrefixed
  have padded :=
    normalize paddedSame paddedNonSimple
      paddedHeadSimple paddedFinalSimple
  have suffixNeHead : suffix ≠ left.head := by
    intro equal
    apply suffixLeft
    simp [Word.toList, equal]
  have substituted :=
    derives_substitute_padBoth
      (head := left.head) (final := left.final)
      prefixLeft prefixRight suffixLeft suffixRight
      prefixNeSuffix suffixNeHead padded
  have published :=
    samePublishedLeeZhang23_9Signature_of_compact same
  have leftHeadMultiple : 2 ≤ left.toList.count left.head :=
    multiple_of_mem_of_not_globallySimple left left.head
      (by simp [Word.toList]) headNonSimple
  have leftFinalMultiple : 2 ≤ left.toList.count left.final :=
    multiple_of_mem_of_not_globallySimple left left.final
      (word_final_mem_toList left) finalNonSimple
  have rightHeadNonSimple :
      ¬S5_402.GloballySimple right right.head := by
    intro rightSimple
    apply headNonSimple
    exact (published.globallySimple left.head).mpr <| by
      simpa [published.head] using rightSimple
  have rightFinalNonSimple :
      ¬S5_402.GloballySimple right right.final := by
    intro rightSimple
    apply finalNonSimple
    exact (published.globallySimple left.final).mpr <| by
      simpa [published.final] using rightSimple
  have rightHeadMultiple : 2 ≤ right.toList.count right.head :=
    multiple_of_mem_of_not_globallySimple right right.head
      (by simp [Word.toList]) rightHeadNonSimple
  have rightFinalMultiple : 2 ≤ right.toList.count right.final :=
    multiple_of_mem_of_not_globallySimple right right.final
      (word_final_mem_toList right) rightFinalNonSimple
  have leftExpanded :=
    derivesDuplicateEndpoints left leftHeadMultiple leftFinalMultiple
  have rightExpanded :
      Derives B4Basis right
        ((Word.singleton left.head ++ right) ++
          Word.singleton left.final) := by
    simpa [published.head, published.final] using
      derivesDuplicateEndpoints right
        rightHeadMultiple rightFinalMultiple
  exact leftExpanded.trans <| substituted.trans rightExpanded.symm

/-- Lemma 23.13 in callback form: once the non-simple, simple-endpoint case
is normalized, no endpoint-simplicity hypothesis remains. -/
theorem derives_of_sameLeeZhang23_9Signature_of_nonSimple
    (normalize : SimpleEndpointNormalizer)
    {left right : Word Nat}
    (same : SameLeeZhang23_9Signature left right)
    (nonSimple : ∃ marker, 2 ≤ left.toList.count marker) :
    Derives B4Basis left right := by
  by_cases headSimple :
      S5_402.GloballySimple left left.head
  · by_cases finalSimple :
        S5_402.GloballySimple left left.final
    · exact normalize same nonSimple headSimple finalSimple
    · exact derives_of_simpleHead_nonsimpleFinal
        normalize same nonSimple headSimple finalSimple
  · by_cases finalSimple :
        S5_402.GloballySimple left left.final
    · exact derives_of_nonsimpleHead_simpleFinal
        normalize same nonSimple headSimple finalSimple
    · exact derives_of_nonsimpleEndpoints
        normalize same nonSimple headSimple finalSimple

end SemigroupBasis.CoRoots.Order6LeeZhang23_13Padding
