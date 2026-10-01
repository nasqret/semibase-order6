import SemigroupBasis.Nonfinite.B2One.Reconstruction

namespace SemigroupBasis.Nonfinite.B2One

open SemigroupBasis
open SemigroupBasis.Examples.B2One

/-!
The stability part of Sapir's reconstruction of Perkins's proof.

The paper reduces each of the four local source words to stability of
variables and adjacent pairs.  This module makes the reusable semantic
steps explicit:

* isoterms are invariant under bijective renaming;
* a valid identity of the concrete Brandt monoid has the same support on
  both sides;
* an isoterm occurring as a Boolean deletion projection makes that
  projection stable;
* stable singleton and two-letter projections reconstruct the whole word.

The final occurrence-preimage construction remains separate from these
semantic lemmas.
-/

private theorem Word.map_map
    (word : Word α) (first : α → β) (second : β → γ) :
    (word.map first).map second =
      word.map (fun letter => second (first letter)) := by
  cases word
  simp [Word.map, List.map_map]

private theorem Word.map_leftInverse
    (word : Word Nat) (forward backward : Nat → Nat)
    (inverse : ∀ letter, backward (forward letter) = letter) :
    (word.map forward).map backward = word := by
  rw [Word.map_map]
  apply Word.toList_injective
  cases word
  simp [Word.map, Word.toList, inverse]

private theorem Word.map_rightInverse
    (word : Word Nat) (forward backward : Nat → Nat)
    (inverse : ∀ letter, forward (backward letter) = letter) :
    (word.map backward).map forward = word := by
  rw [Word.map_map]
  apply Word.toList_injective
  cases word
  simp [Word.map, Word.toList, inverse]

/-- An isoterm remains an isoterm after any bijective renaming of variables. -/
theorem Isoterm.map_bijection
    {G : Semigroup S} {word : Word Nat}
    (isoterm : Isoterm G word)
    (forward backward : Nat → Nat)
    (leftInverse : ∀ letter, backward (forward letter) = letter)
    (rightInverse : ∀ letter, forward (backward letter) = letter) :
    Isoterm G (word.map forward) := by
  intro other valid
  have pulledBack :
      (Identity.mk word (other.map backward)).SatisfiedBy G := by
    intro valuation
    have equality :=
      valid (fun letter => valuation (backward letter))
    simpa only [Semigroup.eval_map, leftInverse] using equality
  have equality := isoterm (other.map backward) pulledBack
  have mapped := congrArg (fun current => current.map forward) equality
  simpa only [Word.map_rightInverse other forward backward rightInverse]
    using mapped

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  rw [Word.toList_bind]
  induction word.toList with
  | nil =>
      cases word with
      | mk head tail =>
          simp [Word.toList] at *
  | cons head tail ih =>
      simp only [List.flatMap_cons, Word.toList_singleton,
        List.singleton_append]
      change List.flatMap (fun letter => [letter]) tail = tail at ih
      exact congrArg (List.cons head) ih

/-- Every nonempty contiguous factor of an isoterm is an isoterm. -/
theorem Isoterm.of_context
    {G : Semigroup S} {large small : Word Nat}
    (isoterm : Isoterm G large)
    (pre post : List Nat)
    (shape : large = contextWord pre small post) :
    Isoterm G small := by
  intro other valid
  have contextual :=
    contextualInstance_satisfiedBy valid pre post Word.singleton
  have largeValid :
      (Identity.mk large (contextWord pre other post)).SatisfiedBy G := by
    simpa only [bind_singleton, shape] using contextual
  have equality := isoterm (contextWord pre other post) largeValid
  have listEquality := congrArg Word.toList equality
  have largeList :
      large.toList = pre ++ small.toList ++ post := by
    rw [shape, contextWord_toList]
  rw [contextWord_toList, largeList] at listEquality
  have withoutSuffix := List.append_cancel_right listEquality
  have withoutPrefix := List.append_cancel_left withoutSuffix
  exact Word.toList_injective withoutPrefix

/-- The printed Brandt monoid is self-dual, so reversal preserves its
isoterms. -/
theorem Isoterm.reverse
    {word : Word Nat}
    (isoterm : Isoterm table.semigroup word) :
    Isoterm table.semigroup word.reverse := by
  intro other valid
  have oppositeValid :
      (Identity.mk word.reverse other).SatisfiedBy
        table.semigroup.opposite :=
    oppositeIntoDual.pullback_identity
      (Identity.mk word.reverse other) valid
  have reversedValid :
      (Identity.mk word other.reverse).SatisfiedBy table.semigroup := by
    simpa [Identity.reversed] using
      (Identity.satisfiedBy_opposite_iff_reversed
        (Identity.mk word.reverse other) table.semigroup).mp
          oppositeValid
  have equality : other.reverse = word :=
    isoterm other.reverse reversedValid
  have reversedEquality := congrArg Word.reverse equality
  simpa using reversedEquality

private def absenceValuation
    (excluded letter : Nat) : Fin 6 :=
  if letter = excluded then zero else one

private theorem foldl_from_zero
    (valuation : Nat → Fin 6) :
    ∀ letters : List Nat,
      letters.foldl
        (fun current letter => mul current (valuation letter)) zero = zero
  | [] => rfl
  | letter :: letters => by
      simp only [List.foldl_cons, zero_mul]
      exact foldl_from_zero valuation letters

private theorem foldl_absence_of_mem
    (excluded : Nat) :
    ∀ (letters : List Nat) (initial : Fin 6),
      excluded ∈ letters →
      letters.foldl
        (fun current letter =>
          mul current (absenceValuation excluded letter)) initial = zero
  | [], _, member => by simp at member
  | letter :: letters, initial, member => by
      simp only [List.mem_cons] at member
      rcases member with equality | member
      · subst letter
        simp only [List.foldl_cons, absenceValuation, if_pos, mul_zero]
        exact foldl_from_zero (absenceValuation excluded) letters
      · simp only [List.foldl_cons]
        by_cases equality : letter = excluded
        · subst letter
          simp only [absenceValuation, if_pos, mul_zero]
          exact foldl_from_zero (absenceValuation excluded) letters
        · simp only [absenceValuation, if_neg equality]
          exact foldl_absence_of_mem excluded letters
            (mul initial one) member

private theorem foldl_absence_of_not_mem
    (excluded : Nat) :
    ∀ letters : List Nat,
      excluded ∉ letters →
      letters.foldl
        (fun current letter =>
          mul current (absenceValuation excluded letter)) one = one
  | [], _ => rfl
  | letter :: letters, absent => by
      have different : letter ≠ excluded := by
        intro equality
        apply absent
        simp [equality]
      have tailAbsent : excluded ∉ letters := by
        intro member
        exact absent (List.Mem.tail letter member)
      simp only [List.foldl_cons, absenceValuation, if_neg different, one_mul]
      exact foldl_absence_of_not_mem excluded letters tailAbsent

private theorem eval_absence_of_mem
    (excluded : Nat) (word : Word Nat)
    (member : excluded ∈ word.toList) :
    table.semigroup.eval (absenceValuation excluded) word = zero := by
  cases word with
  | mk head tail =>
      simp only [Word.toList, List.mem_cons] at member
      unfold Semigroup.eval
      rcases member with equality | tailMember
      · subst head
        simp only [absenceValuation, if_pos]
        exact foldl_from_zero (absenceValuation excluded) tail
      · by_cases equality : head = excluded
        · subst head
          simp only [absenceValuation, if_pos]
          exact foldl_from_zero (absenceValuation excluded) tail
        · simp only [absenceValuation, if_neg equality]
          exact foldl_absence_of_mem excluded tail one tailMember

private theorem eval_absence_of_not_mem
    (excluded : Nat) (word : Word Nat)
    (absent : excluded ∉ word.toList) :
    table.semigroup.eval (absenceValuation excluded) word = one := by
  cases word with
  | mk head tail =>
      have headDifferent : head ≠ excluded := by
        intro equality
        apply absent
        simp [Word.toList, equality]
      have tailAbsent : excluded ∉ tail := by
        intro member
        exact absent (by simp [Word.toList, member])
      unfold Semigroup.eval
      simp only [absenceValuation, if_neg headDifferent]
      exact foldl_absence_of_not_mem excluded tail tailAbsent

/-- Both sides of a valid identity of the concrete Brandt monoid use
exactly the same variables. -/
theorem valid_identity_support_iff
    {left right : Word Nat}
    (valid : (Identity.mk left right).SatisfiedBy table.semigroup)
    (letter : Nat) :
    letter ∈ left.toList ↔ letter ∈ right.toList := by
  constructor
  · intro leftMember
    by_cases rightMember : letter ∈ right.toList
    · exact rightMember
    · exfalso
      have equality := valid (absenceValuation letter)
      rw [eval_absence_of_mem letter left leftMember,
        eval_absence_of_not_mem letter right rightMember] at equality
      exact (by decide : zero ≠ one) equality
  · intro rightMember
    by_cases leftMember : letter ∈ left.toList
    · exact leftMember
    · exfalso
      have equality := valid (absenceValuation letter)
      rw [eval_absence_of_not_mem letter left leftMember,
        eval_absence_of_mem letter right rightMember] at equality
      exact (by decide : one ≠ zero) equality

private def evalList
    (valuation : Nat → Fin 6) (letters : List Nat) : Fin 6 :=
  letters.foldl
    (fun current letter => mul current (valuation letter)) one

private theorem evalList_toList
    (valuation : Nat → Fin 6) (word : Word Nat) :
    evalList valuation word.toList =
      table.semigroup.eval valuation word := by
  cases word with
  | mk head tail =>
      simp only [evalList, Word.toList, List.foldl_cons, Semigroup.eval]
      rw [one_mul]
      rfl

private def deletionValuation
    (keep : Nat → Bool) (valuation : Nat → Fin 6) (letter : Nat) : Fin 6 :=
  if keep letter then valuation letter else one

private theorem foldl_deletionValuation
    (keep : Nat → Bool) (valuation : Nat → Fin 6)
    (letters : List Nat) (initial : Fin 6) :
    letters.foldl
        (fun current letter =>
          mul current (deletionValuation keep valuation letter))
        initial =
      (letters.filter keep).foldl
        (fun current letter => mul current (valuation letter))
        initial := by
  induction letters generalizing initial with
  | nil => rfl
  | cons letter rest ih =>
      simp only [List.foldl_cons, List.filter_cons]
      by_cases kept : keep letter
      · rw [ih]
        simp [deletionValuation, kept]
      · rw [ih]
        simp [deletionValuation, kept, mul_one]

private theorem filtered_eval_equal
    {left right : Word Nat}
    (valid : (Identity.mk left right).SatisfiedBy table.semigroup)
    (keep : Nat → Bool) (valuation : Nat → Fin 6) :
    evalList valuation (left.toList.filter keep) =
      evalList valuation (right.toList.filter keep) := by
  change
    (left.toList.filter keep).foldl
        (fun current letter => mul current (valuation letter)) one =
      (right.toList.filter keep).foldl
        (fun current letter => mul current (valuation letter)) one
  rw [← foldl_deletionValuation keep valuation left.toList one,
    ← foldl_deletionValuation keep valuation right.toList one]
  change
    evalList (deletionValuation keep valuation) left.toList =
      evalList (deletionValuation keep valuation) right.toList
  rw [evalList_toList, evalList_toList]
  exact valid (deletionValuation keep valuation)

/-- If a Boolean deletion of the left side is an isoterm, the same deletion
of every valid right side is exactly that isoterm. -/
theorem filtered_eq_of_isoterm
    {left right isotermWord : Word Nat}
    (valid : (Identity.mk left right).SatisfiedBy table.semigroup)
    (isoterm : Isoterm table.semigroup isotermWord)
    (keep : Nat → Bool)
    (leftFiltered : left.toList.filter keep = isotermWord.toList) :
    right.toList.filter keep = isotermWord.toList := by
  have headInLeftFiltered :
      isotermWord.head ∈ left.toList.filter keep := by
    rw [leftFiltered]
    simp [Word.toList]
  have headKept : keep isotermWord.head = true :=
    (List.mem_filter.mp headInLeftFiltered).2
  have headInLeft : isotermWord.head ∈ left.toList :=
    (List.mem_filter.mp headInLeftFiltered).1
  have headInRight :=
    (valid_identity_support_iff valid isotermWord.head).mp headInLeft
  have headInRightFiltered :
      isotermWord.head ∈ right.toList.filter keep :=
    List.mem_filter.mpr ⟨headInRight, headKept⟩
  cases filtered : right.toList.filter keep with
  | nil => simp [filtered] at headInRightFiltered
  | cons head tail =>
      let filteredWord : Word Nat := ⟨head, tail⟩
      have filteredWordList :
          filteredWord.toList = right.toList.filter keep := by
        rw [filtered]
        rfl
      have filteredValid :
          (Identity.mk isotermWord filteredWord).SatisfiedBy
            table.semigroup := by
        intro valuation
        rw [← evalList_toList, ← evalList_toList, filteredWordList,
          ← leftFiltered]
        exact filtered_eval_equal valid keep valuation
      have equality := isoterm filteredWord filteredValid
      exact congrArg Word.toList equality

def singletonKeep (selected letter : Nat) : Bool :=
  letter == selected

def keepTriple
    (first second third letter : Nat) : Bool :=
  letter == first || letter == second || letter == third

/-- Stability of all occurrences of one variable under identities with the
given left side. -/
def SingletonStable (source : Word Nat) (selected : Nat) : Prop :=
  ∀ other,
    (Identity.mk source other).SatisfiedBy table.semigroup →
    source.toList.filter (singletonKeep selected) =
      other.toList.filter (singletonKeep selected)

/-- Stability of the complete two-variable deletion projection. -/
def PairStable (source : Word Nat) (first second : Nat) : Prop :=
  ∀ other,
    (Identity.mk source other).SatisfiedBy table.semigroup →
    source.toList.filter (pairKeep first second) =
      other.toList.filter (pairKeep first second)

theorem PairStable.comm
    {source : Word Nat} {first second : Nat}
    (stable : PairStable source first second) :
    PairStable source second first := by
  intro other valid
  have keepEqual :
      pairKeep second first = pairKeep first second := by
    funext letter
    simp [pairKeep, Bool.or_comm]
  rw [keepEqual]
  exact stable other valid

private theorem filter_filter_of_implies
    (letters : List Nat) (small large : Nat → Bool)
    (implies : ∀ letter, small letter = true → large letter = true) :
    (letters.filter large).filter small = letters.filter small := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro letter _
  by_cases smallKept : small letter
  · have largeKept : large letter := implies letter smallKept
    simp [smallKept, largeKept]
  · simp [smallKept]

private theorem filter_filter_singleton_eq_nil_of_dropped
    (letters : List Nat) (keep : Nat → Bool) (selected : Nat)
    (selectedDropped : keep selected = false) :
    (letters.filter keep).filter (singletonKeep selected) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro letter member
  have letterKept := (List.mem_filter.mp member).2
  by_cases letterSelected : letter = selected
  · subst letter
    rw [selectedDropped] at letterKept
    contradiction
  · simp [singletonKeep, letterSelected]

private theorem filter_filter_pair_eq_singleton_left
    (letters : List Nat) (keep : Nat → Bool)
    {first second : Nat}
    (different : first ≠ second)
    (firstKept : keep first = true)
    (secondDropped : keep second = false) :
    (letters.filter keep).filter (pairKeep first second) =
      letters.filter (singletonKeep first) := by
  calc
    (letters.filter keep).filter (pairKeep first second) =
        (letters.filter keep).filter (singletonKeep first) := by
      apply List.filter_congr
      intro letter member
      have letterKept := (List.mem_filter.mp member).2
      by_cases letterFirst : letter = first
      · subst letter
        simp [pairKeep, singletonKeep]
      · by_cases letterSecond : letter = second
        · subst letter
          rw [secondDropped] at letterKept
          contradiction
        · simp [pairKeep, singletonKeep, letterFirst, letterSecond]
    _ = letters.filter (singletonKeep first) := by
      apply filter_filter_of_implies
      intro letter selected
      simp [singletonKeep] at selected
      subst letter
      exact firstKept

private theorem filter_filter_pair_eq_singleton_right
    (letters : List Nat) (keep : Nat → Bool)
    {first second : Nat}
    (different : first ≠ second)
    (firstDropped : keep first = false)
    (secondKept : keep second = true) :
    (letters.filter keep).filter (pairKeep first second) =
      letters.filter (singletonKeep second) := by
  calc
    (letters.filter keep).filter (pairKeep first second) =
        (letters.filter keep).filter (singletonKeep second) := by
      apply List.filter_congr
      intro letter member
      have letterKept := (List.mem_filter.mp member).2
      by_cases letterFirst : letter = first
      · subst letter
        rw [firstDropped] at letterKept
        contradiction
      · by_cases letterSecond : letter = second
        · subst letter
          simp [pairKeep, singletonKeep, different, Ne.symm different]
        · simp [pairKeep, singletonKeep, letterFirst, letterSecond]
    _ = letters.filter (singletonKeep second) := by
      apply filter_filter_of_implies
      intro letter selected
      simp [singletonKeep] at selected
      subst letter
      exact secondKept

private theorem filter_filter_pair_eq_nil_of_dropped
    (letters : List Nat) (keep : Nat → Bool)
    {first second : Nat}
    (firstDropped : keep first = false)
    (secondDropped : keep second = false) :
    (letters.filter keep).filter (pairKeep first second) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro letter member
  have letterKept := (List.mem_filter.mp member).2
  by_cases letterFirst : letter = first
  · subst letter
    rw [firstDropped] at letterKept
    contradiction
  · by_cases letterSecond : letter = second
    · subst letter
      rw [secondDropped] at letterKept
      contradiction
    · simp [pairKeep, letterFirst, letterSecond]

/-- A projected isoterm proves stability of every smaller Boolean
projection contained in it. -/
theorem stable_filter_of_filtered_isoterm
    {source isotermWord : Word Nat}
    (isoterm : Isoterm table.semigroup isotermWord)
    (large small : Nat → Bool)
    (sourceFiltered :
      source.toList.filter large = isotermWord.toList)
    (contained :
      ∀ letter, small letter = true → large letter = true) :
    ∀ other,
      (Identity.mk source other).SatisfiedBy table.semigroup →
      source.toList.filter small = other.toList.filter small := by
  intro other valid
  have otherFiltered :=
    filtered_eq_of_isoterm valid isoterm large sourceFiltered
  calc
    source.toList.filter small =
        (source.toList.filter large).filter small := by
          symm
          exact filter_filter_of_implies source.toList small large contained
    _ = isotermWord.toList.filter small := by rw [sourceFiltered]
    _ = (other.toList.filter large).filter small := by
          rw [otherFiltered]
    _ = other.toList.filter small :=
      filter_filter_of_implies other.toList small large contained

theorem pairStable_of_filtered_isoterm
    {source isotermWord : Word Nat}
    {first second : Nat}
    (isoterm : Isoterm table.semigroup isotermWord)
    (large : Nat → Bool)
    (sourceFiltered :
      source.toList.filter large = isotermWord.toList)
    (contained :
      ∀ letter,
        pairKeep first second letter = true → large letter = true) :
    PairStable source first second :=
  stable_filter_of_filtered_isoterm
    isoterm large (pairKeep first second) sourceFiltered contained

theorem singletonStable_of_filtered_isoterm
    {source isotermWord : Word Nat}
    {selected : Nat}
    (isoterm : Isoterm table.semigroup isotermWord)
    (large : Nat → Bool)
    (sourceFiltered :
      source.toList.filter large = isotermWord.toList)
    (contained :
      ∀ letter,
        singletonKeep selected letter = true → large letter = true) :
    SingletonStable source selected :=
  stable_filter_of_filtered_isoterm
    isoterm large (singletonKeep selected) sourceFiltered contained

/-- A source variable occurring exactly once is stable under every valid
identity of the Brandt monoid. -/
theorem singletonStable_of_count_one
    {source : Word Nat} {selected : Nat}
    (selectedCount : source.toList.count selected = 1) :
    SingletonStable source selected := by
  have zeroIsoterm :
      Isoterm table.semigroup (Word.singleton 0) := by
    apply Isoterm.of_context xytyx_isoterm [] [1, 2, 1, 0]
    decide
  have singletonIsoterm :
      Isoterm table.semigroup (Word.singleton selected) := by
    by_cases selectedZero : selected = 0
    · subst selected
      exact zeroIsoterm
    · let rename : Nat → Nat :=
        fun letter =>
          if letter = 0 then selected
          else if letter = selected then 0
          else letter
      have renameInvolutive :
          ∀ letter, rename (rename letter) = letter := by
        intro letter
        by_cases letterZero : letter = 0
        · subst letter
          simp [rename, selectedZero]
        · by_cases letterSelected : letter = selected
          · subst letter
            simp [rename, selectedZero]
          · simp [rename, selectedZero, letterZero, letterSelected]
      have renamedIsoterm :=
        Isoterm.map_bijection zeroIsoterm
          rename rename renameInvolutive renameInvolutive
      have renamedWord :
          (Word.singleton 0).map rename = Word.singleton selected := by
        apply Word.toList_injective
        rfl
      rw [renamedWord] at renamedIsoterm
      exact renamedIsoterm
  apply singletonStable_of_filtered_isoterm
    singletonIsoterm (singletonKeep selected)
  · have filterCountOne :
        ∀ letters : List Nat,
          letters.count selected = 1 →
            letters.filter (singletonKeep selected) = [selected] := by
      intro letters count
      induction letters with
      | nil =>
          simp at count
      | cons head tail ih =>
          by_cases headSelected : head = selected
          · subst head
            have tailCount : tail.count selected = 0 := by
              simp only [List.count_cons_self] at count
              omega
            have tailAbsent : selected ∉ tail :=
              List.count_eq_zero.mp tailCount
            have tailFiltered :
                tail.filter (singletonKeep selected) = [] := by
              apply List.filter_eq_nil_iff.mpr
              intro letter member
              have different : letter ≠ selected := by
                intro equality
                subst letter
                exact tailAbsent member
              simp [singletonKeep, different]
            simp [singletonKeep, tailFiltered]
          · have tailCount : tail.count selected = 1 := by
              simpa [List.count_cons_of_ne headSelected] using count
            simpa [singletonKeep, headSelected] using ih tailCount
    simpa using filterCountOne source.toList selectedCount
  · intro letter kept
    exact kept

theorem singletonStable_of_pairStable
    {source : Word Nat} {selected partner : Nat}
    (stable : PairStable source selected partner) :
    SingletonStable source selected := by
  intro other valid
  have pairEquality := stable other valid
  have contained :
      ∀ letter,
        singletonKeep selected letter = true →
          pairKeep selected partner letter = true := by
    intro letter kept
    simp [singletonKeep] at kept
    subst letter
    simp [pairKeep]
  calc
    source.toList.filter (singletonKeep selected) =
        (source.toList.filter
          (pairKeep selected partner)).filter
            (singletonKeep selected) := by
      symm
      exact
        filter_filter_of_implies source.toList
          (singletonKeep selected) (pairKeep selected partner) contained
    _ = (other.toList.filter
          (pairKeep selected partner)).filter
            (singletonKeep selected) := by rw [pairEquality]
    _ = other.toList.filter (singletonKeep selected) :=
      filter_filter_of_implies other.toList
        (singletonKeep selected) (pairKeep selected partner) contained

theorem singletonStable_of_pairStable_right
    {source : Word Nat} {partner selected : Nat}
    (stable : PairStable source partner selected) :
    SingletonStable source selected := by
  intro other valid
  have pairEquality := stable other valid
  have contained :
      ∀ letter,
        singletonKeep selected letter = true →
          pairKeep partner selected letter = true := by
    intro letter kept
    simp [singletonKeep] at kept
    subst letter
    simp [pairKeep]
  calc
    source.toList.filter (singletonKeep selected) =
        (source.toList.filter
          (pairKeep partner selected)).filter
            (singletonKeep selected) := by
      symm
      exact
        filter_filter_of_implies source.toList
          (singletonKeep selected) (pairKeep partner selected) contained
    _ = (other.toList.filter
          (pairKeep partner selected)).filter
            (singletonKeep selected) := by rw [pairEquality]
    _ = other.toList.filter (singletonKeep selected) :=
      filter_filter_of_implies other.toList
        (singletonKeep selected) (pairKeep partner selected) contained

private theorem local_count_filter_of_kept
    (letters : List Nat) (keep : Nat → Bool) (letter : Nat)
    (kept : keep letter = true) :
    (letters.filter keep).count letter = letters.count letter := by
  induction letters with
  | nil => simp
  | cons first rest ih =>
      by_cases firstKept : keep first
      · by_cases equality : first = letter
        · subst first
          simp [kept, ih]
        · simp [firstKept, equality, ih]
      · have firstDifferent : first ≠ letter := by
          intro equality
          subst first
          exact firstKept kept
        simp [firstKept, firstDifferent, ih]

private theorem local_length_eq_pair_counts
    {first second : Nat} (different : first ≠ second) :
    ∀ letters : List Nat,
      (∀ letter, letter ∈ letters →
        letter = first ∨ letter = second) →
      letters.length =
        letters.count first + letters.count second
  | [], _ => by simp
  | letter :: rest, onlyPair => by
      have headPair := onlyPair letter (by simp)
      have restPair :
          ∀ value, value ∈ rest →
            value = first ∨ value = second := by
        intro value member
        exact onlyPair value (by simp [member])
      have induction :=
        local_length_eq_pair_counts different rest restPair
      rcases headPair with rfl | rfl
      · simp [different, induction]
        omega
      · simp [Ne.symm different, induction]
        omega

private theorem local_length_eq_triple_counts
    {first second third : Nat}
    (distinct : [first, second, third].Nodup) :
    ∀ letters : List Nat,
      (∀ letter, letter ∈ letters →
        letter = first ∨ letter = second ∨ letter = third) →
      letters.length =
        letters.count first + letters.count second +
          letters.count third
  | [], _ => by simp
  | letter :: rest, onlyTriple => by
      have headTriple := onlyTriple letter (by simp)
      have restTriple :
          ∀ value, value ∈ rest →
            value = first ∨ value = second ∨ value = third := by
        intro value member
        exact onlyTriple value (by simp [member])
      have induction :=
        local_length_eq_triple_counts distinct rest restTriple
      simp only [List.nodup_cons, List.mem_cons,
        List.not_mem_nil, or_false, not_or] at distinct
      rcases distinct with
        ⟨⟨firstSecond, firstThird⟩, ⟨secondThird, _⟩⟩
      rcases headTriple with rfl | rfl | rfl
      · simp [firstSecond, firstThird, induction]
        omega
      · simp [Ne.symm firstSecond, secondThird, induction]
        omega
      · simp [Ne.symm firstThird, Ne.symm secondThird,
          induction]
        omega

private theorem pair_list_shape_counts_one_one
    {letters : List Nat} {first second : Nat}
    (different : first ≠ second)
    (onlyPair :
      ∀ letter, letter ∈ letters →
        letter = first ∨ letter = second)
    (firstCount : letters.count first = 1)
    (secondCount : letters.count second = 1) :
    letters = [first, second] ∨
      letters = [second, first] := by
  have lengthTwo : letters.length = 2 := by
    rw [local_length_eq_pair_counts different letters onlyPair,
      firstCount, secondCount]
  rcases letters with _ | ⟨firstLetter, rest⟩
  · simp at lengthTwo
  rcases rest with _ | ⟨secondLetter, rest⟩
  · simp at lengthTwo
  have restEmpty : rest = [] := by
    apply List.eq_nil_of_length_eq_zero
    simpa using lengthTwo
  subst rest
  have firstPair := onlyPair firstLetter (by simp)
  have secondPair := onlyPair secondLetter (by simp)
  rcases firstPair with rfl | rfl <;>
    rcases secondPair with rfl | rfl <;>
    simp_all [different, Ne.symm different]

/-- Two distinct source variables that each occur once have a stable complete
two-letter projection. -/
theorem pairStable_of_counts_one_one
    {source : Word Nat} {first second : Nat}
    (different : first ≠ second)
    (firstCount : source.toList.count first = 1)
    (secondCount : source.toList.count second = 1) :
    PairStable source first second := by
  intro other valid
  have firstStable : SingletonStable source first :=
    singletonStable_of_count_one firstCount
  have secondStable : SingletonStable source second :=
    singletonStable_of_count_one secondCount
  have sourceOnlyPair :
      ∀ letter,
        letter ∈ source.toList.filter (pairKeep first second) →
          letter = first ∨ letter = second := by
    intro letter member
    have kept := (List.mem_filter.mp member).2
    simpa [pairKeep] using kept
  have sourceFirstCount :
      (source.toList.filter
        (pairKeep first second)).count first = 1 := by
    rw [local_count_filter_of_kept source.toList
      (pairKeep first second) first (by simp [pairKeep])]
    exact firstCount
  have sourceSecondCount :
      (source.toList.filter
        (pairKeep first second)).count second = 1 := by
    rw [local_count_filter_of_kept source.toList
      (pairKeep first second) second (by simp [pairKeep])]
    exact secondCount
  have sourceShape :=
    pair_list_shape_counts_one_one different sourceOnlyPair
      sourceFirstCount sourceSecondCount
  have otherFirstCount : other.toList.count first = 1 := by
    calc
      other.toList.count first =
          (other.toList.filter
            (singletonKeep first)).length :=
        List.count_eq_length_filter
      _ = (source.toList.filter
            (singletonKeep first)).length := by
        rw [firstStable other valid]
      _ = source.toList.count first :=
        List.count_eq_length_filter.symm
      _ = 1 := firstCount
  have otherSecondCount : other.toList.count second = 1 := by
    calc
      other.toList.count second =
          (other.toList.filter
            (singletonKeep second)).length :=
        List.count_eq_length_filter
      _ = (source.toList.filter
            (singletonKeep second)).length := by
        rw [secondStable other valid]
      _ = source.toList.count second :=
        List.count_eq_length_filter.symm
      _ = 1 := secondCount
  have otherOnlyPair :
      ∀ letter,
        letter ∈ other.toList.filter (pairKeep first second) →
          letter = first ∨ letter = second := by
    intro letter member
    have kept := (List.mem_filter.mp member).2
    simpa [pairKeep] using kept
  have otherFirstProjectionCount :
      (other.toList.filter
        (pairKeep first second)).count first = 1 := by
    rw [local_count_filter_of_kept other.toList
      (pairKeep first second) first (by simp [pairKeep])]
    exact otherFirstCount
  have otherSecondProjectionCount :
      (other.toList.filter
        (pairKeep first second)).count second = 1 := by
    rw [local_count_filter_of_kept other.toList
      (pairKeep first second) second (by simp [pairKeep])]
    exact otherSecondCount
  have otherShape :=
    pair_list_shape_counts_one_one different otherOnlyPair
      otherFirstProjectionCount otherSecondProjectionCount
  rcases sourceShape with sourceShape | sourceShape <;>
    rcases otherShape with otherShape | otherShape
  · exact sourceShape.trans otherShape.symm
  · have evaluation :=
      filtered_eval_equal valid (pairKeep first second)
        (fun letter =>
          if letter = first then a
          else if letter = second then b
          else one)
    rw [sourceShape, otherShape] at evaluation
    simp [evalList, different, Ne.symm different,
      a, b, one, mul] at evaluation
  · have evaluation :=
      filtered_eval_equal valid (pairKeep first second)
        (fun letter =>
          if letter = first then a
          else if letter = second then b
          else one)
    rw [sourceShape, otherShape] at evaluation
    simp [evalList, different, Ne.symm different,
      a, b, one, mul] at evaluation
  · exact sourceShape.trans otherShape.symm

private theorem pair_list_shape_counts_two_one
    {letters : List Nat} {repeated linear : Nat}
    (different : repeated ≠ linear)
    (onlyPair :
      ∀ letter, letter ∈ letters →
        letter = repeated ∨ letter = linear)
    (repeatedCount : letters.count repeated = 2)
    (linearCount : letters.count linear = 1) :
    letters = [repeated, repeated, linear] ∨
      letters = [repeated, linear, repeated] ∨
      letters = [linear, repeated, repeated] := by
  have lengthThree : letters.length = 3 := by
    rw [local_length_eq_pair_counts different letters onlyPair,
      repeatedCount, linearCount]
  rcases letters with _ | ⟨first, rest⟩
  · simp at lengthThree
  rcases rest with _ | ⟨second, rest⟩
  · simp at lengthThree
  rcases rest with _ | ⟨third, rest⟩
  · simp at lengthThree
  have restEmpty : rest = [] := by
    apply List.eq_nil_of_length_eq_zero
    simpa using lengthThree
  subst rest
  have firstPair := onlyPair first (by simp)
  have secondPair := onlyPair second (by simp)
  have thirdPair := onlyPair third (by simp)
  rcases firstPair with rfl | rfl <;>
    rcases secondPair with rfl | rfl <;>
    rcases thirdPair with rfl | rfl <;>
    simp_all [different, Ne.symm different]

private def xxtOrderValuation
    (repeated linear letter : Nat) : Fin 6 :=
  if letter = repeated then ab
  else if letter = linear then a
  else one

/-- Even though `xxt` is not an isoterm for `B₂¹`, its order is rigid among
words with exactly two `x` occurrences and one `t` occurrence. -/
theorem pairStable_of_xxt_shape
    {source : Word Nat} {repeated linear : Nat}
    (different : repeated ≠ linear)
    (repeatedStable : SingletonStable source repeated)
    (linearStable : SingletonStable source linear)
    (sourceShape :
      source.toList.filter (pairKeep repeated linear) =
        [repeated, repeated, linear]) :
    PairStable source repeated linear := by
  intro other valid
  have repeatedContained :
      ∀ letter,
        singletonKeep repeated letter = true →
          pairKeep repeated linear letter = true := by
    intro letter kept
    simp [singletonKeep] at kept
    subst letter
    simp [pairKeep]
  have linearContained :
      ∀ letter,
        singletonKeep linear letter = true →
          pairKeep repeated linear letter = true := by
    intro letter kept
    simp [singletonKeep] at kept
    subst letter
    simp [pairKeep]
  have sourceRepeated :
      source.toList.filter (singletonKeep repeated) =
        [repeated, repeated] := by
    calc
      source.toList.filter (singletonKeep repeated) =
          (source.toList.filter
            (pairKeep repeated linear)).filter
              (singletonKeep repeated) := by
        symm
        exact filter_filter_of_implies source.toList
          (singletonKeep repeated) (pairKeep repeated linear)
          repeatedContained
      _ = [repeated, repeated] := by
        rw [sourceShape]
        simp [singletonKeep, different, Ne.symm different]
  have sourceLinear :
      source.toList.filter (singletonKeep linear) = [linear] := by
    calc
      source.toList.filter (singletonKeep linear) =
          (source.toList.filter
            (pairKeep repeated linear)).filter
              (singletonKeep linear) := by
        symm
        exact filter_filter_of_implies source.toList
          (singletonKeep linear) (pairKeep repeated linear)
          linearContained
      _ = [linear] := by
        rw [sourceShape]
        simp [singletonKeep, different, Ne.symm different]
  have otherRepeated :
      other.toList.filter (singletonKeep repeated) =
        [repeated, repeated] := by
    rw [← repeatedStable other valid]
    exact sourceRepeated
  have otherLinear :
      other.toList.filter (singletonKeep linear) = [linear] := by
    rw [← linearStable other valid]
    exact sourceLinear
  let pairProjection :=
    other.toList.filter (pairKeep repeated linear)
  have projectionOnlyPair :
      ∀ letter, letter ∈ pairProjection →
        letter = repeated ∨ letter = linear := by
    intro letter member
    have kept := (List.mem_filter.mp member).2
    simpa [pairKeep] using kept
  have otherRepeatedCount :
      other.toList.count repeated = 2 := by
    rw [List.count_eq_length_filter]
    simpa [singletonKeep] using congrArg List.length otherRepeated
  have otherLinearCount :
      other.toList.count linear = 1 := by
    rw [List.count_eq_length_filter]
    simpa [singletonKeep] using congrArg List.length otherLinear
  have projectionRepeatedCount :
      pairProjection.count repeated = 2 := by
    rw [local_count_filter_of_kept other.toList
      (pairKeep repeated linear) repeated (by simp [pairKeep])]
    exact otherRepeatedCount
  have projectionLinearCount :
      pairProjection.count linear = 1 := by
    rw [local_count_filter_of_kept other.toList
      (pairKeep repeated linear) linear (by simp [pairKeep])]
    exact otherLinearCount
  rcases
      pair_list_shape_counts_two_one different projectionOnlyPair
        projectionRepeatedCount projectionLinearCount with
    projectionShape | projectionShape | projectionShape
  · exact sourceShape.trans projectionShape.symm
  · have evaluation :=
      filtered_eval_equal valid (pairKeep repeated linear)
        (xxtOrderValuation repeated linear)
    change
      other.toList.filter (pairKeep repeated linear) =
        [repeated, linear, repeated] at projectionShape
    rw [sourceShape, projectionShape] at evaluation
    simp [evalList, xxtOrderValuation, different, Ne.symm different,
      ab, a, one, zero, mul] at evaluation
  · have evaluation :=
      filtered_eval_equal valid (pairKeep repeated linear)
        (xxtOrderValuation repeated linear)
    change
      other.toList.filter (pairKeep repeated linear) =
        [linear, repeated, repeated] at projectionShape
    rw [sourceShape, projectionShape] at evaluation
    simp [evalList, xxtOrderValuation, different, Ne.symm different,
      ab, a, one, zero, mul] at evaluation

/-- The reverse order `txx` is rigid under the same singleton-stability
hypotheses as `pairStable_of_xxt_shape`. -/
theorem pairStable_of_txx_shape
    {source : Word Nat} {repeated linear : Nat}
    (different : repeated ≠ linear)
    (repeatedStable : SingletonStable source repeated)
    (linearStable : SingletonStable source linear)
    (sourceShape :
      source.toList.filter (pairKeep repeated linear) =
        [linear, repeated, repeated]) :
    PairStable source repeated linear := by
  intro other valid
  have repeatedContained :
      ∀ letter,
        singletonKeep repeated letter = true →
          pairKeep repeated linear letter = true := by
    intro letter kept
    simp [singletonKeep] at kept
    subst letter
    simp [pairKeep]
  have linearContained :
      ∀ letter,
        singletonKeep linear letter = true →
          pairKeep repeated linear letter = true := by
    intro letter kept
    simp [singletonKeep] at kept
    subst letter
    simp [pairKeep]
  have sourceRepeated :
      source.toList.filter (singletonKeep repeated) =
        [repeated, repeated] := by
    calc
      source.toList.filter (singletonKeep repeated) =
          (source.toList.filter
            (pairKeep repeated linear)).filter
              (singletonKeep repeated) := by
        symm
        exact filter_filter_of_implies source.toList
          (singletonKeep repeated) (pairKeep repeated linear)
          repeatedContained
      _ = [repeated, repeated] := by
        rw [sourceShape]
        simp [singletonKeep, different, Ne.symm different]
  have sourceLinear :
      source.toList.filter (singletonKeep linear) = [linear] := by
    calc
      source.toList.filter (singletonKeep linear) =
          (source.toList.filter
            (pairKeep repeated linear)).filter
              (singletonKeep linear) := by
        symm
        exact filter_filter_of_implies source.toList
          (singletonKeep linear) (pairKeep repeated linear)
          linearContained
      _ = [linear] := by
        rw [sourceShape]
        simp [singletonKeep, different, Ne.symm different]
  have otherRepeated :
      other.toList.filter (singletonKeep repeated) =
        [repeated, repeated] := by
    rw [← repeatedStable other valid]
    exact sourceRepeated
  have otherLinear :
      other.toList.filter (singletonKeep linear) = [linear] := by
    rw [← linearStable other valid]
    exact sourceLinear
  let pairProjection :=
    other.toList.filter (pairKeep repeated linear)
  have projectionOnlyPair :
      ∀ letter, letter ∈ pairProjection →
        letter = repeated ∨ letter = linear := by
    intro letter member
    have kept := (List.mem_filter.mp member).2
    simpa [pairKeep] using kept
  have otherRepeatedCount :
      other.toList.count repeated = 2 := by
    rw [List.count_eq_length_filter]
    simpa [singletonKeep] using congrArg List.length otherRepeated
  have otherLinearCount :
      other.toList.count linear = 1 := by
    rw [List.count_eq_length_filter]
    simpa [singletonKeep] using congrArg List.length otherLinear
  have projectionRepeatedCount :
      pairProjection.count repeated = 2 := by
    rw [local_count_filter_of_kept other.toList
      (pairKeep repeated linear) repeated (by simp [pairKeep])]
    exact otherRepeatedCount
  have projectionLinearCount :
      pairProjection.count linear = 1 := by
    rw [local_count_filter_of_kept other.toList
      (pairKeep repeated linear) linear (by simp [pairKeep])]
    exact otherLinearCount
  rcases
      pair_list_shape_counts_two_one different projectionOnlyPair
        projectionRepeatedCount projectionLinearCount with
    projectionShape | projectionShape | projectionShape
  · have evaluation :=
      filtered_eval_equal valid (pairKeep repeated linear)
        (fun letter =>
          if letter = repeated then ba
          else if letter = linear then a
          else one)
    change
      other.toList.filter (pairKeep repeated linear) =
        [repeated, repeated, linear] at projectionShape
    rw [sourceShape, projectionShape] at evaluation
    simp [evalList, different, Ne.symm different,
      ba, a, one, zero, mul] at evaluation
  · have evaluation :=
      filtered_eval_equal valid (pairKeep repeated linear)
        (fun letter =>
          if letter = repeated then ba
          else if letter = linear then a
          else one)
    change
      other.toList.filter (pairKeep repeated linear) =
        [repeated, linear, repeated] at projectionShape
    rw [sourceShape, projectionShape] at evaluation
    simp [evalList, different, Ne.symm different,
      ba, a, one, zero, mul] at evaluation
  · exact sourceShape.trans projectionShape.symm

/-- The middle order `xtx` is rigid among projections with two occurrences
of `x` and one occurrence of `t`. -/
theorem pairStable_of_xtx_shape
    {source : Word Nat} {repeated linear : Nat}
    (different : repeated ≠ linear)
    (repeatedStable : SingletonStable source repeated)
    (linearStable : SingletonStable source linear)
    (sourceShape :
      source.toList.filter (pairKeep repeated linear) =
        [repeated, linear, repeated]) :
    PairStable source repeated linear := by
  intro other valid
  have repeatedContained :
      ∀ letter,
        singletonKeep repeated letter = true →
          pairKeep repeated linear letter = true := by
    intro letter kept
    simp [singletonKeep] at kept
    subst letter
    simp [pairKeep]
  have linearContained :
      ∀ letter,
        singletonKeep linear letter = true →
          pairKeep repeated linear letter = true := by
    intro letter kept
    simp [singletonKeep] at kept
    subst letter
    simp [pairKeep]
  have sourceRepeated :
      source.toList.filter (singletonKeep repeated) =
        [repeated, repeated] := by
    calc
      source.toList.filter (singletonKeep repeated) =
          (source.toList.filter
            (pairKeep repeated linear)).filter
              (singletonKeep repeated) := by
        symm
        exact filter_filter_of_implies source.toList
          (singletonKeep repeated) (pairKeep repeated linear)
          repeatedContained
      _ = [repeated, repeated] := by
        rw [sourceShape]
        simp [singletonKeep, different, Ne.symm different]
  have sourceLinear :
      source.toList.filter (singletonKeep linear) = [linear] := by
    calc
      source.toList.filter (singletonKeep linear) =
          (source.toList.filter
            (pairKeep repeated linear)).filter
              (singletonKeep linear) := by
        symm
        exact filter_filter_of_implies source.toList
          (singletonKeep linear) (pairKeep repeated linear)
          linearContained
      _ = [linear] := by
        rw [sourceShape]
        simp [singletonKeep, different, Ne.symm different]
  have otherRepeated :
      other.toList.filter (singletonKeep repeated) =
        [repeated, repeated] := by
    rw [← repeatedStable other valid]
    exact sourceRepeated
  have otherLinear :
      other.toList.filter (singletonKeep linear) = [linear] := by
    rw [← linearStable other valid]
    exact sourceLinear
  let pairProjection :=
    other.toList.filter (pairKeep repeated linear)
  have projectionOnlyPair :
      ∀ letter, letter ∈ pairProjection →
        letter = repeated ∨ letter = linear := by
    intro letter member
    have kept := (List.mem_filter.mp member).2
    simpa [pairKeep] using kept
  have otherRepeatedCount :
      other.toList.count repeated = 2 := by
    rw [List.count_eq_length_filter]
    simpa [singletonKeep] using congrArg List.length otherRepeated
  have otherLinearCount :
      other.toList.count linear = 1 := by
    rw [List.count_eq_length_filter]
    simpa [singletonKeep] using congrArg List.length otherLinear
  have projectionRepeatedCount :
      pairProjection.count repeated = 2 := by
    rw [local_count_filter_of_kept other.toList
      (pairKeep repeated linear) repeated (by simp [pairKeep])]
    exact otherRepeatedCount
  have projectionLinearCount :
      pairProjection.count linear = 1 := by
    rw [local_count_filter_of_kept other.toList
      (pairKeep repeated linear) linear (by simp [pairKeep])]
    exact otherLinearCount
  rcases
      pair_list_shape_counts_two_one different projectionOnlyPair
        projectionRepeatedCount projectionLinearCount with
    projectionShape | projectionShape | projectionShape
  · have evaluation :=
      filtered_eval_equal valid (pairKeep repeated linear)
        (fun letter =>
          if letter = repeated then a
          else if letter = linear then b
          else one)
    change
      other.toList.filter (pairKeep repeated linear) =
        [repeated, repeated, linear] at projectionShape
    rw [sourceShape, projectionShape] at evaluation
    simp [evalList, different, Ne.symm different,
      a, b, one, zero, mul] at evaluation
  · exact sourceShape.trans projectionShape.symm
  · have evaluation :=
      filtered_eval_equal valid (pairKeep repeated linear)
        (fun letter =>
          if letter = repeated then a
          else if letter = linear then b
          else one)
    change
      other.toList.filter (pairKeep repeated linear) =
        [linear, repeated, repeated] at projectionShape
    rw [sourceShape, projectionShape] at evaluation
    simp [evalList, different, Ne.symm different,
      a, b, one, zero, mul] at evaluation

/-- A stable twice-occurring source variable and a linear source variable
have a stable complete two-letter projection.  The source order is derived
from the exact multiplicities and dispatched to the three rigid shapes. -/
theorem pairStable_of_counts_two_one
    {source : Word Nat} {repeated linear : Nat}
    (different : repeated ≠ linear)
    (repeatedStable : SingletonStable source repeated)
    (repeatedCount : source.toList.count repeated = 2)
    (linearCount : source.toList.count linear = 1) :
    PairStable source repeated linear := by
  let pairProjection :=
    source.toList.filter (pairKeep repeated linear)
  have projectionOnlyPair :
      ∀ letter, letter ∈ pairProjection →
        letter = repeated ∨ letter = linear := by
    intro letter member
    have kept := (List.mem_filter.mp member).2
    simpa [pairKeep] using kept
  have projectionRepeatedCount :
      pairProjection.count repeated = 2 := by
    rw [local_count_filter_of_kept source.toList
      (pairKeep repeated linear) repeated (by simp [pairKeep])]
    exact repeatedCount
  have projectionLinearCount :
      pairProjection.count linear = 1 := by
    rw [local_count_filter_of_kept source.toList
      (pairKeep repeated linear) linear (by simp [pairKeep])]
    exact linearCount
  have linearStable : SingletonStable source linear :=
    singletonStable_of_count_one linearCount
  rcases
      pair_list_shape_counts_two_one different projectionOnlyPair
        projectionRepeatedCount projectionLinearCount with
    sourceShape | sourceShape | sourceShape
  · exact
      pairStable_of_xxt_shape different repeatedStable linearStable
        sourceShape
  · exact
      pairStable_of_xtx_shape different repeatedStable linearStable
        sourceShape
  · exact
      pairStable_of_txx_shape different repeatedStable linearStable
        sourceShape

private theorem pair_list_shape_counts_two_two
    {letters : List Nat} {first second : Nat}
    (different : first ≠ second)
    (onlyPair :
      ∀ letter, letter ∈ letters →
        letter = first ∨ letter = second)
    (firstCount : letters.count first = 2)
    (secondCount : letters.count second = 2) :
    letters = [first, second, first, second] ∨
      letters = [second, first, second, first] ∨
      letters = [first, first, second, second] ∨
      letters = [first, second, second, first] ∨
      letters = [second, first, first, second] ∨
      letters = [second, second, first, first] := by
  have lengthFour : letters.length = 4 := by
    rw [local_length_eq_pair_counts different letters onlyPair,
      firstCount, secondCount]
  rcases letters with _ | ⟨firstLetter, rest⟩
  · simp at lengthFour
  rcases rest with _ | ⟨secondLetter, rest⟩
  · simp at lengthFour
  rcases rest with _ | ⟨thirdLetter, rest⟩
  · simp at lengthFour
  rcases rest with _ | ⟨fourthLetter, rest⟩
  · simp at lengthFour
  have restEmpty : rest = [] := by
    apply List.eq_nil_of_length_eq_zero
    simpa using lengthFour
  subst rest
  have firstPair := onlyPair firstLetter (by simp)
  have secondPair := onlyPair secondLetter (by simp)
  have thirdPair := onlyPair thirdLetter (by simp)
  have fourthPair := onlyPair fourthLetter (by simp)
  rcases firstPair with rfl | rfl <;>
    rcases secondPair with rfl | rfl <;>
    rcases thirdPair with rfl | rfl <;>
    rcases fourthPair with rfl | rfl <;>
    simp_all [different, Ne.symm different]

private def alternatingOrderValuation
    (first second letter : Nat) : Fin 6 :=
  if letter = first then a
  else if letter = second then b
  else one

/-- The alternating order `xyxy` is rigid among two-two projections for the
printed Brandt table. -/
theorem pairStable_of_xyxy_shape
    {source : Word Nat} {first second : Nat}
    (different : first ≠ second)
    (firstStable : SingletonStable source first)
    (secondStable : SingletonStable source second)
    (sourceShape :
      source.toList.filter (pairKeep first second) =
        [first, second, first, second]) :
    PairStable source first second := by
  intro other valid
  have firstContained :
      ∀ letter,
        singletonKeep first letter = true →
          pairKeep first second letter = true := by
    intro letter kept
    simp [singletonKeep] at kept
    subst letter
    simp [pairKeep]
  have secondContained :
      ∀ letter,
        singletonKeep second letter = true →
          pairKeep first second letter = true := by
    intro letter kept
    simp [singletonKeep] at kept
    subst letter
    simp [pairKeep]
  have sourceFirst :
      source.toList.filter (singletonKeep first) = [first, first] := by
    calc
      source.toList.filter (singletonKeep first) =
          (source.toList.filter
            (pairKeep first second)).filter
              (singletonKeep first) := by
        symm
        exact filter_filter_of_implies source.toList
          (singletonKeep first) (pairKeep first second)
          firstContained
      _ = [first, first] := by
        rw [sourceShape]
        simp [singletonKeep, different, Ne.symm different]
  have sourceSecond :
      source.toList.filter (singletonKeep second) = [second, second] := by
    calc
      source.toList.filter (singletonKeep second) =
          (source.toList.filter
            (pairKeep first second)).filter
              (singletonKeep second) := by
        symm
        exact filter_filter_of_implies source.toList
          (singletonKeep second) (pairKeep first second)
          secondContained
      _ = [second, second] := by
        rw [sourceShape]
        simp [singletonKeep, different, Ne.symm different]
  have otherFirst :
      other.toList.filter (singletonKeep first) = [first, first] := by
    rw [← firstStable other valid]
    exact sourceFirst
  have otherSecond :
      other.toList.filter (singletonKeep second) =
        [second, second] := by
    rw [← secondStable other valid]
    exact sourceSecond
  let pairProjection :=
    other.toList.filter (pairKeep first second)
  have projectionOnlyPair :
      ∀ letter, letter ∈ pairProjection →
        letter = first ∨ letter = second := by
    intro letter member
    have kept := (List.mem_filter.mp member).2
    simpa [pairKeep] using kept
  have otherFirstCount : other.toList.count first = 2 := by
    rw [List.count_eq_length_filter]
    simpa [singletonKeep] using congrArg List.length otherFirst
  have otherSecondCount : other.toList.count second = 2 := by
    rw [List.count_eq_length_filter]
    simpa [singletonKeep] using congrArg List.length otherSecond
  have projectionFirstCount : pairProjection.count first = 2 := by
    rw [local_count_filter_of_kept other.toList
      (pairKeep first second) first (by simp [pairKeep])]
    exact otherFirstCount
  have projectionSecondCount : pairProjection.count second = 2 := by
    rw [local_count_filter_of_kept other.toList
      (pairKeep first second) second (by simp [pairKeep])]
    exact otherSecondCount
  rcases
      pair_list_shape_counts_two_two different projectionOnlyPair
        projectionFirstCount projectionSecondCount with
    projectionShape | projectionShape | projectionShape |
      projectionShape | projectionShape | projectionShape
  · exact sourceShape.trans projectionShape.symm
  all_goals
    have evaluation :=
      filtered_eval_equal valid (pairKeep first second)
        (alternatingOrderValuation first second)
    change
      other.toList.filter (pairKeep first second) = _ at projectionShape
    rw [sourceShape, projectionShape] at evaluation
    simp [evalList, alternatingOrderValuation, different,
      Ne.symm different, a, b, one, mul] at evaluation

/-- Singleton and all distinct two-letter deletion projections determine a
finite word.  This is the list-level kernel behind Sapir's adjacent-pair
stability criterion. -/
theorem list_eq_of_singleton_and_pair_filters :
    ∀ left right : List Nat,
      (∀ selected,
        left.filter (singletonKeep selected) =
          right.filter (singletonKeep selected)) →
      (∀ first second, first ≠ second →
        left.filter (pairKeep first second) =
          right.filter (pairKeep first second)) →
      left = right
  | [], [], _, _ => rfl
  | [], rightHead :: rightTail, single, _ => by
      have equality := single rightHead
      simp [singletonKeep] at equality
  | leftHead :: leftTail, [], single, _ => by
      have equality := single leftHead
      simp [singletonKeep] at equality
  | leftHead :: leftTail, rightHead :: rightTail, single, pairs => by
      by_cases headsEqual : leftHead = rightHead
      · subst rightHead
        congr 1
        apply list_eq_of_singleton_and_pair_filters leftTail rightTail
        · intro selected
          have equality := single selected
          by_cases selectedHead : selected = leftHead
          · subst selected
            simpa [singletonKeep] using equality
          · have headSelected : (leftHead == selected) = false := by
              simp [Ne.symm selectedHead]
            simpa [singletonKeep, headSelected] using equality
        · intro first second different
          have equality := pairs first second different
          by_cases headFirst : leftHead = first
          · subst first
            simpa [pairKeep] using equality
          · by_cases headSecond : leftHead = second
            · subst second
              simpa [pairKeep, headFirst] using equality
            · have firstFalse : (leftHead == first) = false := by
                simp [headFirst]
              have secondFalse : (leftHead == second) = false := by
                simp [headSecond]
              simpa [pairKeep, firstFalse, secondFalse] using equality
      · have equality := pairs leftHead rightHead headsEqual
        simp [pairKeep, headsEqual] at equality

/-- Singleton stability and distinct-pair stability for exactly the selected
letters determine the complete selected projection. -/
theorem stable_filter_of_singleton_and_pair_stability
    {source : Word Nat} (keep : Nat → Bool)
    (single :
      ∀ selected, keep selected = true →
        SingletonStable source selected)
    (pairs :
      ∀ first second,
        keep first = true → keep second = true →
        first ≠ second → PairStable source first second) :
    ∀ other,
      (Identity.mk source other).SatisfiedBy table.semigroup →
      source.toList.filter keep = other.toList.filter keep := by
  intro other valid
  apply list_eq_of_singleton_and_pair_filters
  · intro selected
    cases selectedKept : keep selected with
    | false =>
        rw [
          filter_filter_singleton_eq_nil_of_dropped
            source.toList keep selected selectedKept,
          filter_filter_singleton_eq_nil_of_dropped
            other.toList keep selected selectedKept]
    | true =>
        have equality := single selected selectedKept other valid
        have contained :
            ∀ letter,
              singletonKeep selected letter = true →
                keep letter = true := by
          intro letter selectedLetter
          simp [singletonKeep] at selectedLetter
          subst letter
          exact selectedKept
        calc
          (source.toList.filter keep).filter
                (singletonKeep selected) =
              source.toList.filter (singletonKeep selected) :=
            filter_filter_of_implies source.toList
              (singletonKeep selected) keep contained
          _ = other.toList.filter (singletonKeep selected) :=
            equality
          _ = (other.toList.filter keep).filter
                (singletonKeep selected) := by
            symm
            exact
              filter_filter_of_implies other.toList
                (singletonKeep selected) keep contained
  · intro first second different
    cases firstKept : keep first <;>
      cases secondKept : keep second
    · rw [
        filter_filter_pair_eq_nil_of_dropped
          source.toList keep firstKept secondKept,
        filter_filter_pair_eq_nil_of_dropped
          other.toList keep firstKept secondKept]
    · have equality := single second secondKept other valid
      calc
        (source.toList.filter keep).filter
              (pairKeep first second) =
            source.toList.filter (singletonKeep second) :=
          filter_filter_pair_eq_singleton_right
            source.toList keep different firstKept secondKept
        _ = other.toList.filter (singletonKeep second) := equality
        _ = (other.toList.filter keep).filter
              (pairKeep first second) := by
          symm
          exact
            filter_filter_pair_eq_singleton_right
              other.toList keep different firstKept secondKept
    · have equality := single first firstKept other valid
      calc
        (source.toList.filter keep).filter
              (pairKeep first second) =
            source.toList.filter (singletonKeep first) :=
          filter_filter_pair_eq_singleton_left
            source.toList keep different firstKept secondKept
        _ = other.toList.filter (singletonKeep first) := equality
        _ = (other.toList.filter keep).filter
              (pairKeep first second) := by
          symm
          exact
            filter_filter_pair_eq_singleton_left
              other.toList keep different firstKept secondKept
    · have equality :=
        pairs first second firstKept secondKept different other valid
      have contained :
          ∀ letter,
            pairKeep first second letter = true →
              keep letter = true := by
        intro letter selectedLetter
        simp [pairKeep] at selectedLetter
        rcases selectedLetter with rfl | rfl
        · exact firstKept
        · exact secondKept
      calc
        (source.toList.filter keep).filter
              (pairKeep first second) =
            source.toList.filter (pairKeep first second) :=
          filter_filter_of_implies source.toList
            (pairKeep first second) keep contained
        _ = other.toList.filter (pairKeep first second) := equality
        _ = (other.toList.filter keep).filter
              (pairKeep first second) := by
          symm
          exact
            filter_filter_of_implies other.toList
              (pairKeep first second) keep contained

/-- A selected projection is stable once every selected variable is either
linear or a stable twice-occurring variable, and every pair of distinct
twice-occurring selected variables is stable. -/
theorem stable_filter_of_count_one_or_stable_two
    {source : Word Nat} (keep : Nat → Bool)
    (classification :
      ∀ selected, keep selected = true →
        source.toList.count selected = 1 ∨
          (source.toList.count selected = 2 ∧
            SingletonStable source selected))
    (repeatedPairs :
      ∀ first second,
        keep first = true → keep second = true →
        first ≠ second →
        source.toList.count first = 2 →
        source.toList.count second = 2 →
        PairStable source first second) :
    ∀ other,
      (Identity.mk source other).SatisfiedBy table.semigroup →
      source.toList.filter keep = other.toList.filter keep := by
  apply stable_filter_of_singleton_and_pair_stability keep
  · intro selected selectedKept
    rcases classification selected selectedKept with
      selectedLinear | selectedRepeated
    · exact singletonStable_of_count_one selectedLinear
    · exact selectedRepeated.2
  · intro first second firstKept secondKept different
    rcases classification first firstKept with
      firstLinear | firstRepeated
    · rcases classification second secondKept with
        secondLinear | secondRepeated
      · exact
          pairStable_of_counts_one_one different
            firstLinear secondLinear
      · exact
          (pairStable_of_counts_two_one
            (Ne.symm different) secondRepeated.2
            secondRepeated.1 firstLinear).comm
    · rcases classification second secondKept with
        secondLinear | secondRepeated
      · exact
          pairStable_of_counts_two_one different
            firstRepeated.2 firstRepeated.1 secondLinear
      · exact
          repeatedPairs first second firstKept secondKept
            different firstRepeated.1 secondRepeated.1

theorem word_eq_of_singleton_and_pair_stability
    {source other : Word Nat}
    (single :
      ∀ selected,
        source.toList.filter (singletonKeep selected) =
          other.toList.filter (singletonKeep selected))
    (pairs :
      ∀ first second, first ≠ second →
        source.toList.filter (pairKeep first second) =
          other.toList.filter (pairKeep first second)) :
    source = other := by
  apply Word.toList_injective
  exact list_eq_of_singleton_and_pair_filters
    source.toList other.toList single pairs

/-- Sapir's stability criterion in a projection-heavy form: stability of
every variable and every distinct two-variable deletion forces the source
word to be an isoterm. -/
theorem isoterm_of_singleton_and_pair_stability
    {source : Word Nat}
    (single : ∀ selected, SingletonStable source selected)
    (pairs :
      ∀ first second, first ≠ second →
        PairStable source first second) :
    Isoterm table.semigroup source := by
  intro other valid
  symm
  apply word_eq_of_singleton_and_pair_stability
  · intro selected
    exact single selected other valid
  · intro first second different
    exact pairs first second different other valid

/-! ## Block-local occurrence containers

The same middle variable occurs once in each Perkins block, so filtering by
variable name cannot distinguish the two occurrences.  We instead annotate
every letter of a substitution expansion by the index of the source
occurrence whose image contains it.
-/

def sourceAt : List Nat → Nat → Option Nat
  | [], _ => none
  | letter :: _, 0 => some letter
  | _ :: rest, index + 1 => sourceAt rest index

def annotateExpansion
    (source : List Nat) (images : Nat → List Nat) :
    List (Nat × Nat) :=
  match source with
  | [] => []
  | letter :: rest =>
      (images letter).map (fun marker => (0, marker)) ++
        (annotateExpansion rest images).map
          (fun entry => (entry.1 + 1, entry.2))

theorem annotateExpansion_map_snd
    (source : List Nat) (images : Nat → List Nat) :
    (annotateExpansion source images).map Prod.snd =
      source.flatMap images := by
  induction source with
  | nil => rfl
  | cons letter rest ih =>
      simp only [annotateExpansion, List.map_append, List.map_map,
        List.flatMap_cons]
      congr 1
      induction images letter with
      | nil => rfl
      | cons marker markers ihMarkers =>
          simp [ihMarkers]

private theorem pairwise_constant_owner
    (owner : Nat) (markers : List Nat) :
    (markers.map fun marker => (owner, marker)).Pairwise
      (fun first second => first.1 ≤ second.1) := by
  induction markers with
  | nil => simp
  | cons marker markers ih =>
      simp only [List.map_cons, List.pairwise_cons]
      refine ⟨?_, ih⟩
      intro entry member
      rcases List.mem_map.mp member with
        ⟨nextMarker, _, rfl⟩
      simp

private theorem pairwise_succ_owner
    {annotations : List (Nat × Nat)}
    (ordered :
      annotations.Pairwise
        (fun first second => first.1 ≤ second.1)) :
    (annotations.map
        fun entry => (entry.1 + 1, entry.2)).Pairwise
      (fun first second => first.1 ≤ second.1) := by
  apply ordered.map
  intro first second ownerLe
  simpa using Nat.add_le_add_right ownerLe 1

/-- Source-occurrence owners in an annotated expansion are nondecreasing.
This is the order-theoretic kernel for transporting target occurrence
positions back to source positions. -/
theorem annotateExpansion_pairwise_owner
    (source : List Nat) (images : Nat → List Nat) :
    (annotateExpansion source images).Pairwise
      (fun first second => first.1 ≤ second.1) := by
  induction source with
  | nil => simp [annotateExpansion]
  | cons sourceLetter rest ih =>
      simp only [annotateExpansion, List.pairwise_append]
      refine
        ⟨pairwise_constant_owner 0 (images sourceLetter),
          pairwise_succ_owner ih, ?_⟩
      intro first firstMember second secondMember
      rcases List.mem_map.mp firstMember with
        ⟨firstMarker, _, rfl⟩
      rcases List.mem_map.mp secondMember with
        ⟨secondEntry, _, rfl⟩
      simp

theorem mem_annotateExpansion_iff
    {source : List Nat} {images : Nat → List Nat}
    {owner marker : Nat} :
    (owner, marker) ∈ annotateExpansion source images ↔
      ∃ sourceLetter,
        sourceAt source owner = some sourceLetter ∧
        marker ∈ images sourceLetter := by
  induction source generalizing owner with
  | nil => simp [annotateExpansion, sourceAt]
  | cons letter rest ih =>
      cases owner with
      | zero => simp [annotateExpansion, sourceAt]
      | succ owner => simp [annotateExpansion, sourceAt, ih]

theorem sourceAt_some_index_lt
    {source : List Nat} {index sourceLetter : Nat}
    (atIndex : sourceAt source index = some sourceLetter) :
    index < source.length := by
  induction source generalizing index with
  | nil => simp [sourceAt] at atIndex
  | cons letter rest ih =>
      cases index with
      | zero => simp
      | succ index =>
          simp only [sourceAt] at atIndex
          have small := ih atIndex
          simp
          omega

theorem sourceAt_some_mem
    {source : List Nat} {index sourceLetter : Nat}
    (atIndex : sourceAt source index = some sourceLetter) :
    sourceLetter ∈ source := by
  induction source generalizing index with
  | nil => simp [sourceAt] at atIndex
  | cons letter rest ih =>
      cases index with
      | zero =>
          simp only [sourceAt, Option.some.injEq] at atIndex
          subst sourceLetter
          simp
      | succ index =>
          simp only [sourceAt] at atIndex
          exact List.Mem.tail letter (ih atIndex)

theorem getElem_eq_of_sourceAt
    {source : List Nat} {index sourceLetter : Nat}
    (atIndex : sourceAt source index = some sourceLetter)
    (small : index < source.length := sourceAt_some_index_lt atIndex) :
    source[index] = sourceLetter := by
  induction source generalizing index with
  | nil => simp at small
  | cons letter rest ih =>
      cases index with
      | zero =>
          simp only [sourceAt, Option.some.injEq] at atIndex
          simpa using atIndex
      | succ index =>
          simp only [sourceAt] at atIndex
          exact ih atIndex (by simpa using small)

theorem sourceAt_some_injective
    {source : List Nat} {owner firstSource secondSource : Nat}
    (firstAt : sourceAt source owner = some firstSource)
    (secondAt : sourceAt source owner = some secondSource) :
    firstSource = secondSource := by
  rw [firstAt] at secondAt
  exact Option.some.inj secondAt

private theorem count_map_constant_owner
    (markers : List Nat) (owner marker : Nat) :
    (markers.map fun value => (owner, value)).count (owner, marker) =
      markers.count marker := by
  induction markers with
  | nil => rfl
  | cons value rest ih =>
      by_cases equality : value = marker
      · subst value
        simp only [List.map_cons, List.count_cons_self]
        exact congrArg Nat.succ ih
      · have pairDifferent :
          (owner, value) ≠ (owner, marker) := by
          simp [equality]
        rw [List.map_cons, List.count_cons_of_ne pairDifferent,
          List.count_cons_of_ne equality, ih]

private theorem count_zero_owner_map_succ
    (annotations : List (Nat × Nat)) (marker : Nat) :
    (annotations.map
        fun entry => (entry.1 + 1, entry.2)).count (0, marker) = 0 := by
  induction annotations with
  | nil => rfl
  | cons entry rest ih =>
      have different :
          (entry.1 + 1, entry.2) ≠ (0, marker) := by
        intro equality
        have ownerEquality := congrArg Prod.fst equality
        simp at ownerEquality
      rw [List.map_cons, List.count_cons_of_ne different, ih]

private theorem count_succ_owner_map_constant
    (markers : List Nat) (owner marker : Nat) :
    (markers.map fun value => (0, value)).count (owner + 1, marker) = 0 := by
  induction markers with
  | nil => rfl
  | cons value rest ih =>
      have different :
          (0, value) ≠ (owner + 1, marker) := by
        intro equality
        have ownerEquality := congrArg Prod.fst equality
        simp at ownerEquality
      rw [List.map_cons, List.count_cons_of_ne different, ih]

private theorem count_succ_owner_map_succ
    (annotations : List (Nat × Nat)) (owner marker : Nat) :
    (annotations.map
        fun entry => (entry.1 + 1, entry.2)).count
          (owner + 1, marker) =
      annotations.count (owner, marker) := by
  induction annotations with
  | nil => rfl
  | cons entry rest ih =>
      by_cases equality : entry = (owner, marker)
      · subst entry
        simp only [List.map_cons, List.count_cons_self]
        exact congrArg Nat.succ ih
      · have mappedDifferent :
          (entry.1 + 1, entry.2) ≠ (owner + 1, marker) := by
          intro mappedEquality
          apply equality
          have ownerEquality :
              entry.1 = owner :=
            Nat.add_right_cancel (congrArg Prod.fst mappedEquality)
          have markerEquality :
              entry.2 = marker :=
            congrArg Prod.snd mappedEquality
          exact Prod.ext ownerEquality markerEquality
        rw [List.map_cons, List.count_cons_of_ne mappedDifferent,
          List.count_cons_of_ne equality, ih]

/-- Counting an annotated owner-marker pair recovers the count of the marker
inside the image of that exact source occurrence. -/
theorem annotateExpansion_count_owner_marker
    {source : List Nat} {images : Nat → List Nat}
    {owner sourceLetter marker : Nat}
    (atIndex : sourceAt source owner = some sourceLetter) :
    (annotateExpansion source images).count (owner, marker) =
      (images sourceLetter).count marker := by
  induction source generalizing owner with
  | nil => simp [sourceAt] at atIndex
  | cons letter rest ih =>
      cases owner with
      | zero =>
          simp only [sourceAt, Option.some.injEq] at atIndex
          subst sourceLetter
          simp only [annotateExpansion, List.count_append,
            count_map_constant_owner, count_zero_owner_map_succ,
            Nat.add_zero]
      | succ owner =>
          simp only [sourceAt] at atIndex
          simp only [annotateExpansion, List.count_append,
            count_succ_owner_map_constant,
            count_succ_owner_map_succ, Nat.zero_add]
          exact ih atIndex

private def annotationSlice
    (annotations : List (Nat × Nat))
    (preBlock block : List Nat) :
    List (Nat × Nat) :=
  (annotations.drop preBlock.length).take block.length

private theorem annotationSlice_map_snd
    {annotations : List (Nat × Nat)}
    {preBlock block suffix : List Nat}
    (shape :
      annotations.map Prod.snd = preBlock ++ block ++ suffix) :
    (annotationSlice annotations preBlock block).map Prod.snd = block := by
  simp only [annotationSlice, List.map_take, List.map_drop, shape]
  simp

private theorem annotationSlice_eq_of_decomposition
    {annotations : List (Nat × Nat)}
    {preBlock block : List Nat}
    {preAnnotations blockAnnotations suffixAnnotations :
      List (Nat × Nat)}
    (decomposition :
      annotations =
        preAnnotations ++ blockAnnotations ++ suffixAnnotations)
    (preMap : preAnnotations.map Prod.snd = preBlock)
    (blockMap : blockAnnotations.map Prod.snd = block) :
    annotationSlice annotations preBlock block = blockAnnotations := by
  have preLength :
      preAnnotations.length = preBlock.length := by
    simpa using congrArg List.length preMap
  have blockLength :
      blockAnnotations.length = block.length := by
    simpa using congrArg List.length blockMap
  simp [annotationSlice, decomposition, ← preLength, ← blockLength]

private theorem annotation_decompose_five_sections
    {annotations : List (Nat × Nat)}
    {first second third fourth fifth : List Nat}
    (shape :
      annotations.map Prod.snd =
        first ++ second ++ third ++ fourth ++ fifth) :
    ∃ firstAnnotations secondAnnotations thirdAnnotations
        fourthAnnotations fifthAnnotations,
      annotations =
        firstAnnotations ++ secondAnnotations ++ thirdAnnotations ++
          fourthAnnotations ++ fifthAnnotations ∧
      firstAnnotations.map Prod.snd = first ∧
      secondAnnotations.map Prod.snd = second ∧
      thirdAnnotations.map Prod.snd = third ∧
      fourthAnnotations.map Prod.snd = fourth ∧
      fifthAnnotations.map Prod.snd = fifth := by
  have firstSplit :
      annotations.map Prod.snd =
        first ++ (second ++ third ++ fourth ++ fifth) := by
    simpa only [List.append_assoc] using shape
  rcases List.map_eq_append_iff.mp firstSplit with
    ⟨firstAnnotations, restAnnotations, annotationsEq,
      firstMap, restMap⟩
  have secondSplit :
      restAnnotations.map Prod.snd =
        second ++ (third ++ fourth ++ fifth) := by
    simpa only [List.append_assoc] using restMap
  rcases List.map_eq_append_iff.mp secondSplit with
    ⟨secondAnnotations, restAnnotations,
      restEq, secondMap, restMap⟩
  have thirdSplit :
      restAnnotations.map Prod.snd =
        third ++ (fourth ++ fifth) := by
    simpa only [List.append_assoc] using restMap
  rcases List.map_eq_append_iff.mp thirdSplit with
    ⟨thirdAnnotations, restAnnotations,
      restEq', thirdMap, restMap⟩
  rcases List.map_eq_append_iff.mp restMap with
    ⟨fourthAnnotations, fifthAnnotations,
      restEq'', fourthMap, fifthMap⟩
  subst restAnnotations
  subst restAnnotations
  subst restAnnotations
  refine
    ⟨firstAnnotations, secondAnnotations, thirdAnnotations,
      fourthAnnotations, fifthAnnotations, ?_, firstMap,
      secondMap, thirdMap, fourthMap, fifthMap⟩
  simpa only [List.append_assoc] using annotationsEq

private theorem annotationSlice_sublist
    (annotations : List (Nat × Nat))
    (preBlock block : List Nat) :
    (annotationSlice annotations preBlock block).Sublist annotations := by
  exact
    (List.take_sublist _ _).trans
      (List.drop_sublist _ _)

private theorem annotationSlice_owner_lt
    {source : List Nat} {images : Nat → List Nat}
    {preBlock block : List Nat} {owner marker : Nat}
    (member :
      (owner, marker) ∈
        annotationSlice (annotateExpansion source images)
          preBlock block) :
    owner < source.length := by
  have fullMember :=
    (annotationSlice_sublist
      (annotateExpansion source images) preBlock block).mem member
  rcases
      (mem_annotateExpansion_iff.mp fullMember) with
    ⟨sourceLetter, atIndex, _⟩
  exact sourceAt_some_index_lt atIndex

private theorem map_fst_annotationSlice_covered
    (source : List Nat) (images : Nat → List Nat)
    (preBlock block : List Nat) :
    ∀ owner,
      owner ∈
          (annotationSlice (annotateExpansion source images)
            preBlock block).map Prod.fst →
        owner ∈ List.range source.length := by
  intro owner member
  rcases List.mem_map.mp member with
    ⟨entry, entryMember, equality⟩
  have ownerEquality : entry.1 = owner := by simpa using equality
  subst owner
  exact List.mem_range.mpr
    (annotationSlice_owner_lt entryMember)

private theorem local_length_eq_count_add_filter_ne
    (letters : List Nat) (letter : Nat) :
    letters.length =
      letters.count letter +
        (letters.filter fun value => value != letter).length := by
  induction letters with
  | nil => simp
  | cons first rest ih =>
      by_cases equality : first = letter
      · subst first
        simp [ih]
        omega
      · simp [equality, ih]
        omega

private theorem local_count_filter_ne_eq
    (letters : List Nat) {removed retained : Nat}
    (different : retained ≠ removed) :
    (letters.filter fun value => value != removed).count retained =
      letters.count retained := by
  induction letters with
  | nil => simp
  | cons first rest ih =>
      by_cases firstRemoved : first = removed
      · subst first
        have reverseDifferent : removed ≠ retained :=
          Ne.symm different
        simp [reverseDifferent, ih]
      · by_cases firstRetained : first = retained
        · subst first
          simp [firstRemoved, ih]
        · simp [firstRemoved, firstRetained, ih]

private theorem length_le_of_cover_and_count_le_one :
    ∀ (letters variables : List Nat),
      (∀ letter, letter ∈ letters → letter ∈ variables) →
      (∀ letter, letter ∈ letters → letters.count letter ≤ 1) →
      letters.length ≤ variables.length
  | [], _, _, _ => by simp
  | first :: rest, [], covered, _ => by
      have impossible := covered first (by simp)
      simp at impossible
  | letters, pivot :: variables, covered, bounded => by
      let remainder :=
        letters.filter fun letter => letter != pivot
      have remainderCovered :
          ∀ letter, letter ∈ remainder → letter ∈ variables := by
        intro letter member
        have filtered := List.mem_filter.mp member
        have different : letter ≠ pivot := by simpa using filtered.2
        have inCover := covered letter filtered.1
        simp only [List.mem_cons] at inCover
        rcases inCover with equality | inVariables
        · exact False.elim (different equality)
        · exact inVariables
      have remainderBounded :
          ∀ letter, letter ∈ remainder →
            remainder.count letter ≤ 1 := by
        intro letter member
        have filtered := List.mem_filter.mp member
        have different : letter ≠ pivot := by
          simpa using filtered.2
        rw [local_count_filter_ne_eq letters different]
        exact bounded letter filtered.1
      have inductionBound :=
        length_le_of_cover_and_count_le_one
          remainder variables remainderCovered remainderBounded
      have pivotBound : letters.count pivot ≤ 1 := by
        by_cases member : pivot ∈ letters
        · exact bounded pivot member
        · simp [List.count_eq_zero.mpr member]
      have decomposition :=
        local_length_eq_count_add_filter_ne letters pivot
      change letters.length ≤ (pivot :: variables).length
      change remainder.length ≤ variables.length at inductionBound
      change
        letters.length =
          letters.count pivot + remainder.length at decomposition
      simp only [List.length_cons]
      omega

private theorem exists_owner_count_two
    {owners cover : List Nat}
    (covered :
      ∀ owner, owner ∈ owners → owner ∈ cover)
    (large : cover.length < owners.length) :
    ∃ owner, owner ∈ owners ∧ 2 ≤ owners.count owner := by
  by_cases existsLarge :
      ∃ owner, owner ∈ owners ∧ 2 ≤ owners.count owner
  · exact existsLarge
  · exfalso
    have everySmall :
        ∀ owner, owner ∈ owners → owners.count owner ≤ 1 := by
      intro owner member
      have notTwo : ¬ 2 ≤ owners.count owner := by
        intro two
        exact existsLarge ⟨owner, member, two⟩
      omega
    have bound :=
      length_le_of_cover_and_count_le_one
        owners cover covered everySmall
    omega

private theorem filtered_owner_markers_length
    (annotations : List (Nat × Nat)) (owner : Nat) :
    ((annotations.filter
        (fun entry => entry.1 == owner)).map Prod.snd).length =
      (annotations.map Prod.fst).count owner := by
  induction annotations with
  | nil => rfl
  | cons entry rest ih =>
      by_cases equality : entry.1 = owner
      · simp [equality, ih]
      · simp [equality, ih]

private theorem filtered_owner_markers_sublist
    (annotations : List (Nat × Nat)) (owner : Nat) :
    ((annotations.filter
        (fun entry => entry.1 == owner)).map Prod.snd).Sublist
      (annotations.map Prod.snd) :=
  (List.filter_sublist.map Prod.snd)

private theorem exists_two_distinct_of_nodup_length_two
    {letters : List Nat}
    (nodup : letters.Nodup)
    (large : 2 ≤ letters.length) :
    ∃ first second,
      first ≠ second ∧ first ∈ letters ∧ second ∈ letters := by
  rcases letters with _ | ⟨first, rest⟩
  · simp at large
  rcases rest with _ | ⟨second, rest⟩
  · simp at large
  have different : first ≠ second := by
    intro equality
    subst second
    simp at nodup
  exact ⟨first, second, different, by simp, by simp⟩

def BlockOccurrencePreimage
    (source : Word Nat) (substitution : Nat → Word Nat)
    (preBlock block : List Nat) (owner marker : Nat) : Prop :=
  (owner, marker) ∈
    annotationSlice
      (annotateExpansion source.toList
      (fun letter => (substitution letter).toList))
      preBlock block

private theorem eq_of_mem_of_mem_of_map_nodup
    {entries : List α} {project : α → β} {first second : α}
    (mappedNodup : (entries.map project).Nodup)
    (firstMember : first ∈ entries)
    (secondMember : second ∈ entries)
    (projectedEqual : project first = project second) :
    first = second := by
  induction entries with
  | nil =>
      simp at firstMember
  | cons head tail ih =>
      simp only [List.map_cons, List.nodup_cons] at mappedNodup
      rcases mappedNodup with ⟨headNotMapped, tailMappedNodup⟩
      simp only [List.mem_cons] at firstMember secondMember
      rcases firstMember with rfl | firstTail
      · rcases secondMember with rfl | secondTail
        · rfl
        · exfalso
          apply headNotMapped
          exact List.mem_map.mpr
            ⟨second, secondTail, projectedEqual.symm⟩
      · rcases secondMember with rfl | secondTail
        · exfalso
          apply headNotMapped
          exact List.mem_map.mpr
            ⟨first, firstTail, projectedEqual⟩
        · exact ih tailMappedNodup firstTail secondTail

/-- A marker occurring once in a block has a unique source-occurrence owner
inside that block. -/
theorem blockOccurrencePreimage_owner_eq_of_nodup
    {source target : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : source.bind substitution = target)
    {preBlock block suffix : List Nat}
    (targetShape : target.toList = preBlock ++ block ++ suffix)
    (blockNodup : block.Nodup)
    {firstOwner secondOwner marker : Nat}
    (firstPreimage :
      BlockOccurrencePreimage source substitution
        preBlock block firstOwner marker)
    (secondPreimage :
      BlockOccurrencePreimage source substitution
        preBlock block secondOwner marker) :
    firstOwner = secondOwner := by
  let annotations :=
    annotateExpansion source.toList
      (fun letter => (substitution letter).toList)
  have annotationShape :
      annotations.map Prod.snd =
        preBlock ++ block ++ suffix := by
    rw [annotateExpansion_map_snd]
    simpa only [← Word.toList_bind, mapped] using targetShape
  have blockMap :
      (annotationSlice annotations preBlock block).map Prod.snd =
        block :=
    annotationSlice_map_snd annotationShape
  have mappedNodup :
      ((annotationSlice annotations preBlock block).map Prod.snd).Nodup := by
    rw [blockMap]
    exact blockNodup
  have entriesEqual :
      (firstOwner, marker) = (secondOwner, marker) :=
    eq_of_mem_of_mem_of_map_nodup mappedNodup
      firstPreimage secondPreimage rfl
  exact congrArg Prod.fst entriesEqual

private theorem two_le_count_of_mem_separated
    {entry : Nat × Nat}
    {first second third fourth fifth : List (Nat × Nat)}
    (firstMember : entry ∈ second)
    (secondMember : entry ∈ fourth) :
    2 ≤
      (first ++ second ++ third ++ fourth ++ fifth).count entry := by
  have firstPositive : 1 ≤ second.count entry :=
    List.count_pos_iff.mpr firstMember
  have secondPositive : 1 ≤ fourth.count entry :=
    List.count_pos_iff.mpr secondMember
  simp only [List.count_append]
  omega

private theorem blockOccurrencePair_count_two_of_sections
    {source : Word Nat} {substitution : Nat → Word Nat}
    {first second third fourth fifth : List Nat}
    (mappedShape :
      (source.bind substitution).toList =
        first ++ second ++ third ++ fourth ++ fifth)
    {owner marker : Nat}
    (firstPreimage :
      BlockOccurrencePreimage source substitution
        first second owner marker)
    (secondPreimage :
      BlockOccurrencePreimage source substitution
        (first ++ second ++ third) fourth owner marker) :
    2 ≤
      (annotateExpansion source.toList
        (fun letter => (substitution letter).toList)).count
          (owner, marker) := by
  let annotations :=
    annotateExpansion source.toList
      (fun letter => (substitution letter).toList)
  have annotationShape :
      annotations.map Prod.snd =
        first ++ second ++ third ++ fourth ++ fifth := by
    rw [annotateExpansion_map_snd]
    simpa only [← Word.toList_bind] using mappedShape
  rcases annotation_decompose_five_sections annotationShape with
    ⟨firstAnnotations, secondAnnotations, thirdAnnotations,
      fourthAnnotations, fifthAnnotations, annotationsEq,
      firstMap, secondMap, thirdMap, fourthMap, fifthMap⟩
  have firstSlice :
      annotationSlice annotations first second =
        secondAnnotations := by
    apply annotationSlice_eq_of_decomposition
      (preAnnotations := firstAnnotations)
      (suffixAnnotations :=
        thirdAnnotations ++ fourthAnnotations ++ fifthAnnotations)
    · simpa only [List.append_assoc] using annotationsEq
    · exact firstMap
    · exact secondMap
  have secondSlice :
      annotationSlice annotations
          (first ++ second ++ third) fourth =
        fourthAnnotations := by
    apply annotationSlice_eq_of_decomposition
      (preAnnotations :=
        firstAnnotations ++ secondAnnotations ++ thirdAnnotations)
      (suffixAnnotations := fifthAnnotations)
    · simpa only [List.append_assoc] using annotationsEq
    · simpa only [List.map_append, firstMap, secondMap, thirdMap,
        List.append_assoc]
    · exact fourthMap
  have firstMember :
      (owner, marker) ∈ secondAnnotations := by
    rw [← firstSlice]
    exact firstPreimage
  have secondMember :
      (owner, marker) ∈ fourthAnnotations := by
    rw [← secondSlice]
    exact secondPreimage
  change 2 ≤ annotations.count (owner, marker)
  rw [annotationsEq]
  exact two_le_count_of_mem_separated firstMember secondMember

private theorem local_count_mul_le_flatMap_count
    (source : List Nat) (images : Nat → List Nat)
    (sourceLetter marker : Nat) :
    source.count sourceLetter * (images sourceLetter).count marker ≤
      (source.flatMap images).count marker := by
  induction source with
  | nil => simp
  | cons first rest ih =>
      simp only [List.flatMap_cons, List.count_append]
      by_cases equality : first = sourceLetter
      · subst first
        have combined :=
          Nat.add_le_add ih
            (Nat.le_refl ((images sourceLetter).count marker))
        simpa [Nat.add_mul, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using combined
      · rw [List.count_cons_of_ne equality]
        exact Nat.le_trans ih (Nat.le_add_left _ _)

/-- In the repeated branch of Sapir's `2occ` dichotomy, separated target
occurrences are owned by the first and second source occurrences, never by
one source occurrence twice. -/
theorem repeatedPreimageOwners_ne_of_sections
    {source target : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : source.bind substitution = target)
    (pattern : OccurrencePattern extra target.toList)
    {first second third fourth fifth : List Nat}
    (targetShape :
      target.toList =
        first ++ second ++ third ++ fourth ++ fifth)
    {firstOwner secondOwner marker sourceLetter : Nat}
    (firstPreimage :
      BlockOccurrencePreimage source substitution
        first second firstOwner marker)
    (secondPreimage :
      BlockOccurrencePreimage source substitution
        (first ++ second ++ third) fourth secondOwner marker)
    (firstAt :
      sourceAt source.toList firstOwner = some sourceLetter)
    (sourceCount : source.toList.count sourceLetter = 2) :
    firstOwner ≠ secondOwner := by
  intro ownersEqual
  subst secondOwner
  have mappedShape :
      (source.bind substitution).toList =
        first ++ second ++ third ++ fourth ++ fifth := by
    rw [mapped]
    exact targetShape
  have annotationCount :
      2 ≤
        (annotateExpansion source.toList
          (fun letter => (substitution letter).toList)).count
            (firstOwner, marker) :=
    blockOccurrencePair_count_two_of_sections
      mappedShape firstPreimage secondPreimage
  have imageCount :
      2 ≤ (substitution sourceLetter).toList.count marker := by
    rw [annotateExpansion_count_owner_marker firstAt] at annotationCount
    exact annotationCount
  have targetLower :
      4 ≤ target.toList.count marker := by
    have contribution :=
      local_count_mul_le_flatMap_count source.toList
        (fun letter => (substitution letter).toList)
        sourceLetter marker
    rw [sourceCount, ← Word.toList_bind, mapped] at contribution
    omega
  have targetUpper := pattern.count_le_two marker
  omega

/-- Every owner selected from an earlier target section is at most every
owner selected from a later target section. -/
theorem blockOccurrenceOwner_le_of_sections
    {source : Word Nat} {substitution : Nat → Word Nat}
    {first second third fourth fifth : List Nat}
    (mappedShape :
      (source.bind substitution).toList =
        first ++ second ++ third ++ fourth ++ fifth)
    {firstOwner firstMarker secondOwner secondMarker : Nat}
    (firstPreimage :
      BlockOccurrencePreimage source substitution
        first second firstOwner firstMarker)
    (secondPreimage :
      BlockOccurrencePreimage source substitution
        (first ++ second ++ third) fourth secondOwner secondMarker) :
    firstOwner ≤ secondOwner := by
  let annotations :=
    annotateExpansion source.toList
      (fun letter => (substitution letter).toList)
  have annotationShape :
      annotations.map Prod.snd =
        first ++ second ++ third ++ fourth ++ fifth := by
    rw [annotateExpansion_map_snd]
    simpa only [← Word.toList_bind] using mappedShape
  rcases annotation_decompose_five_sections annotationShape with
    ⟨firstAnnotations, secondAnnotations, thirdAnnotations,
      fourthAnnotations, fifthAnnotations, annotationsEq,
      firstMap, secondMap, thirdMap, fourthMap, fifthMap⟩
  have firstSlice :
      annotationSlice annotations first second =
        secondAnnotations := by
    apply annotationSlice_eq_of_decomposition
      (preAnnotations := firstAnnotations)
      (suffixAnnotations :=
        thirdAnnotations ++ fourthAnnotations ++ fifthAnnotations)
    · simpa only [List.append_assoc] using annotationsEq
    · exact firstMap
    · exact secondMap
  have secondSlice :
      annotationSlice annotations
          (first ++ second ++ third) fourth =
        fourthAnnotations := by
    apply annotationSlice_eq_of_decomposition
      (preAnnotations :=
        firstAnnotations ++ secondAnnotations ++ thirdAnnotations)
      (suffixAnnotations := fifthAnnotations)
    · simpa only [List.append_assoc] using annotationsEq
    · simpa only [List.map_append, firstMap, secondMap, thirdMap,
        List.append_assoc]
    · exact fourthMap
  have firstMember :
      (firstOwner, firstMarker) ∈ secondAnnotations := by
    rw [← firstSlice]
    exact firstPreimage
  have secondMember :
      (secondOwner, secondMarker) ∈ fourthAnnotations := by
    rw [← secondSlice]
    exact secondPreimage
  have ordered :
      annotations.Pairwise
        (fun first second => first.1 ≤ second.1) :=
    annotateExpansion_pairwise_owner source.toList
      (fun letter => (substitution letter).toList)
  have leftMember :
      (firstOwner, firstMarker) ∈
        firstAnnotations ++ secondAnnotations := by
    simp [firstMember]
  have rightMember :
      (secondOwner, secondMarker) ∈
        thirdAnnotations ++ fourthAnnotations ++ fifthAnnotations := by
    simp [secondMember]
  have orderedSplit :
      ((firstAnnotations ++ secondAnnotations) ++
          (thirdAnnotations ++ fourthAnnotations ++ fifthAnnotations)).Pairwise
        (fun first second => first.1 ≤ second.1) := by
    rw [annotationsEq] at ordered
    simpa only [List.append_assoc] using ordered
  have relation :=
    orderedSplit.rel_of_mem_append leftMember rightMember
  exact relation

private theorem two_le_count_of_ordered_sourceAt
    {source : List Nat} {first second sourceLetter : Nat}
    (firstAt : sourceAt source first = some sourceLetter)
    (secondAt : sourceAt source second = some sourceLetter)
    (ordered : first < second) :
    2 ≤ source.count sourceLetter := by
  let indices : List (Fin source.length) :=
    [⟨first, sourceAt_some_index_lt firstAt⟩,
      ⟨second, sourceAt_some_index_lt secondAt⟩]
  have indicesOrdered : indices.Pairwise (· < ·) := by
    simp [indices, Fin.mk_lt_mk, ordered]
  have selectedSublist :=
    List.map_getElem_sublist indicesOrdered
  have selectedValues :
      indices.map (fun index => source[index]) =
        [sourceLetter, sourceLetter] := by
    simp only [indices, List.map_cons, List.map_nil]
    congr 1
    · exact getElem_eq_of_sourceAt firstAt
    congr 1
    exact getElem_eq_of_sourceAt secondAt
  rw [selectedValues] at selectedSublist
  have countBound := selectedSublist.count_le sourceLetter
  simpa using countBound

/-- A source letter occurring exactly once has a unique source-occurrence
index. -/
theorem sourceAt_eq_of_count_one
    {source : List Nat} {first second sourceLetter : Nat}
    (firstAt : sourceAt source first = some sourceLetter)
    (secondAt : sourceAt source second = some sourceLetter)
    (sourceCount : source.count sourceLetter = 1) :
    first = second := by
  apply Decidable.byContradiction
  intro different
  rcases Nat.lt_or_gt_of_ne different with ordered | ordered
  · have countLower :=
      two_le_count_of_ordered_sourceAt firstAt secondAt ordered
    omega
  · have countLower :=
      two_le_count_of_ordered_sourceAt secondAt firstAt ordered
    omega

/-- Ordered source occurrences carrying different source letters are
strictly ordered. -/
theorem sourceAt_lt_of_le_of_ne
    {source : List Nat}
    {first second firstSource secondSource : Nat}
    (firstAt : sourceAt source first = some firstSource)
    (secondAt : sourceAt source second = some secondSource)
    (sourcesDifferent : firstSource ≠ secondSource)
    (ordered : first ≤ second) :
    first < second := by
  apply Nat.lt_of_le_of_ne ordered
  intro ownersEqual
  subst second
  exact sourcesDifferent (sourceAt_some_injective firstAt secondAt)

/-- Two occurrences of `repeated` surrounding the unique occurrence of
`linear` determine the complete `repeated linear repeated` deletion
projection. -/
theorem sandwichProjection_of_orderedOwners
    {source : Word Nat}
    {repeated linear firstOwner linearOwner secondOwner : Nat}
    (repeatedCount : source.toList.count repeated = 2)
    (linearCount : source.toList.count linear = 1)
    (firstAt :
      sourceAt source.toList firstOwner = some repeated)
    (linearAt :
      sourceAt source.toList linearOwner = some linear)
    (secondAt :
      sourceAt source.toList secondOwner = some repeated)
    (firstBeforeLinear : firstOwner ≤ linearOwner)
    (linearBeforeSecond : linearOwner ≤ secondOwner) :
    repeated ≠ linear ∧
      source.toList.filter (pairKeep repeated linear) =
        [repeated, linear, repeated] := by
  have different : repeated ≠ linear := by
    intro equality
    subst linear
    rw [repeatedCount] at linearCount
    omega
  have firstStrict : firstOwner < linearOwner :=
    sourceAt_lt_of_le_of_ne firstAt linearAt
      different firstBeforeLinear
  have secondStrict : linearOwner < secondOwner :=
    sourceAt_lt_of_le_of_ne linearAt secondAt
      (Ne.symm different) linearBeforeSecond
  let indices : List (Fin source.toList.length) :=
    [⟨firstOwner, sourceAt_some_index_lt firstAt⟩,
      ⟨linearOwner, sourceAt_some_index_lt linearAt⟩,
      ⟨secondOwner, sourceAt_some_index_lt secondAt⟩]
  have indicesOrdered : indices.Pairwise (· < ·) := by
    simp [indices, Fin.mk_lt_mk, firstStrict, secondStrict]
    exact Nat.lt_trans firstStrict secondStrict
  have selectedSublist :=
    List.map_getElem_sublist indicesOrdered
  have selectedValues :
      indices.map (fun index => source.toList[index]) =
        [repeated, linear, repeated] := by
    simp only [indices, List.map_cons, List.map_nil]
    congr 1
    · exact getElem_eq_of_sourceAt firstAt
    congr 1
    · exact getElem_eq_of_sourceAt linearAt
    congr 1
    exact getElem_eq_of_sourceAt secondAt
  rw [selectedValues] at selectedSublist
  have filteredSublist :=
    selectedSublist.filter (pairKeep repeated linear)
  have selectedKept :
      [repeated, linear, repeated].filter
          (pairKeep repeated linear) =
        [repeated, linear, repeated] := by
    simp [pairKeep]
  rw [selectedKept] at filteredSublist
  have projectionOnlyPair :
      ∀ letter,
        letter ∈
            source.toList.filter (pairKeep repeated linear) →
          letter = repeated ∨ letter = linear := by
    intro letter member
    have kept := (List.mem_filter.mp member).2
    simpa [pairKeep] using kept
  have projectionRepeatedCount :
      (source.toList.filter
          (pairKeep repeated linear)).count repeated = 2 := by
    rw [local_count_filter_of_kept source.toList
      (pairKeep repeated linear) repeated (by simp [pairKeep])]
    exact repeatedCount
  have projectionLinearCount :
      (source.toList.filter
          (pairKeep repeated linear)).count linear = 1 := by
    rw [local_count_filter_of_kept source.toList
      (pairKeep repeated linear) linear (by simp [pairKeep])]
    exact linearCount
  have filteredLength :
      (source.toList.filter
          (pairKeep repeated linear)).length = 3 := by
    rw [local_length_eq_pair_counts different
      (source.toList.filter (pairKeep repeated linear))
      projectionOnlyPair, projectionRepeatedCount,
      projectionLinearCount]
  have equality :=
    filteredSublist.eq_of_length
      (by simpa using filteredLength.symm)
  exact ⟨different, equality.symm⟩

private theorem exact_five_owner_keepTriple_projection
    {source : Word Nat}
    {first second third : Nat}
    {firstOwner secondOwner thirdOwner fourthOwner fifthOwner : Nat}
    {firstLetter secondLetter thirdLetter fourthLetter
      fifthLetter : Nat}
    (distinct : [first, second, third].Nodup)
    (firstCount : source.toList.count first = 2)
    (secondCount : source.toList.count second = 2)
    (thirdCount : source.toList.count third = 1)
    (firstAt :
      sourceAt source.toList firstOwner = some firstLetter)
    (secondAt :
      sourceAt source.toList secondOwner = some secondLetter)
    (thirdAt :
      sourceAt source.toList thirdOwner = some thirdLetter)
    (fourthAt :
      sourceAt source.toList fourthOwner = some fourthLetter)
    (fifthAt :
      sourceAt source.toList fifthOwner = some fifthLetter)
    (ownersOrdered :
      firstOwner < secondOwner ∧ secondOwner < thirdOwner ∧
        thirdOwner < fourthOwner ∧ fourthOwner < fifthOwner)
    (selectedKept :
      [firstLetter, secondLetter, thirdLetter,
          fourthLetter, fifthLetter].filter
          (keepTriple first second third) =
        [firstLetter, secondLetter, thirdLetter,
          fourthLetter, fifthLetter]) :
    source.toList.filter (keepTriple first second third) =
      [firstLetter, secondLetter, thirdLetter,
        fourthLetter, fifthLetter] := by
  let indices : List (Fin source.toList.length) :=
    [⟨firstOwner, sourceAt_some_index_lt firstAt⟩,
      ⟨secondOwner, sourceAt_some_index_lt secondAt⟩,
      ⟨thirdOwner, sourceAt_some_index_lt thirdAt⟩,
      ⟨fourthOwner, sourceAt_some_index_lt fourthAt⟩,
      ⟨fifthOwner, sourceAt_some_index_lt fifthAt⟩]
  have indicesOrdered : indices.Pairwise (· < ·) := by
    simp [indices, Fin.mk_lt_mk] <;> omega
  have selectedSublist :=
    List.map_getElem_sublist indicesOrdered
  have selectedValues :
      indices.map (fun index => source.toList[index]) =
        [firstLetter, secondLetter, thirdLetter,
          fourthLetter, fifthLetter] := by
    simp only [indices, List.map_cons, List.map_nil]
    congr 1
    · exact getElem_eq_of_sourceAt firstAt
    congr 1
    · exact getElem_eq_of_sourceAt secondAt
    congr 1
    · exact getElem_eq_of_sourceAt thirdAt
    congr 1
    · exact getElem_eq_of_sourceAt fourthAt
    congr 1
    exact getElem_eq_of_sourceAt fifthAt
  rw [selectedValues] at selectedSublist
  have filteredSublist :=
    selectedSublist.filter (keepTriple first second third)
  rw [selectedKept] at filteredSublist
  have projectionOnlyTriple :
      ∀ letter,
        letter ∈
            source.toList.filter
              (keepTriple first second third) →
          letter = first ∨ letter = second ∨ letter = third := by
    intro letter member
    have kept := (List.mem_filter.mp member).2
    simpa [keepTriple, or_assoc] using kept
  have projectionFirstCount :
      (source.toList.filter
          (keepTriple first second third)).count first = 2 := by
    rw [local_count_filter_of_kept source.toList
      (keepTriple first second third) first
      (by simp [keepTriple])]
    exact firstCount
  have projectionSecondCount :
      (source.toList.filter
          (keepTriple first second third)).count second = 2 := by
    rw [local_count_filter_of_kept source.toList
      (keepTriple first second third) second
      (by simp [keepTriple])]
    exact secondCount
  have projectionThirdCount :
      (source.toList.filter
          (keepTriple first second third)).count third = 1 := by
    rw [local_count_filter_of_kept source.toList
      (keepTriple first second third) third
      (by simp [keepTriple])]
    exact thirdCount
  have filteredLength :
      (source.toList.filter
          (keepTriple first second third)).length = 5 := by
    rw [local_length_eq_triple_counts distinct
      (source.toList.filter (keepTriple first second third))
      projectionOnlyTriple, projectionFirstCount,
      projectionSecondCount, projectionThirdCount]
  have equality :=
    filteredSublist.eq_of_length
      (by simpa using filteredLength.symm)
  exact equality.symm

/-- A weak owner chain with multiplicities `2,2,1` determines the exact
renamed `x y t y x` projection. -/
theorem palindromicTripleProjection_of_orderedOwners
    {source : Word Nat}
    {outer inner separator
      outerFirst innerFirst separatorOwner
      innerSecond outerSecond : Nat}
    (distinct : [outer, inner, separator].Nodup)
    (outerCount : source.toList.count outer = 2)
    (innerCount : source.toList.count inner = 2)
    (separatorCount : source.toList.count separator = 1)
    (outerFirstAt :
      sourceAt source.toList outerFirst = some outer)
    (innerFirstAt :
      sourceAt source.toList innerFirst = some inner)
    (separatorAt :
      sourceAt source.toList separatorOwner = some separator)
    (innerSecondAt :
      sourceAt source.toList innerSecond = some inner)
    (outerSecondAt :
      sourceAt source.toList outerSecond = some outer)
    (ownersOrdered :
      outerFirst ≤ innerFirst ∧ innerFirst ≤ separatorOwner ∧
        separatorOwner ≤ innerSecond ∧ innerSecond ≤ outerSecond) :
    source.toList.filter (keepTriple outer inner separator) =
      [outer, inner, separator, inner, outer] := by
  have inequalities := distinct
  simp only [List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at inequalities
  rcases inequalities with
    ⟨⟨outerInner, outerSeparator⟩, ⟨innerSeparator, _⟩⟩
  have firstStrict : outerFirst < innerFirst :=
    sourceAt_lt_of_le_of_ne outerFirstAt innerFirstAt
      outerInner ownersOrdered.1
  have secondStrict : innerFirst < separatorOwner :=
    sourceAt_lt_of_le_of_ne innerFirstAt separatorAt
      innerSeparator ownersOrdered.2.1
  have thirdStrict : separatorOwner < innerSecond :=
    sourceAt_lt_of_le_of_ne separatorAt innerSecondAt
      (Ne.symm innerSeparator) ownersOrdered.2.2.1
  have fourthStrict : innerSecond < outerSecond :=
    sourceAt_lt_of_le_of_ne innerSecondAt outerSecondAt
      (Ne.symm outerInner) ownersOrdered.2.2.2
  exact
    exact_five_owner_keepTriple_projection distinct
      outerCount innerCount separatorCount
      outerFirstAt innerFirstAt separatorAt
      innerSecondAt outerSecondAt
      ⟨firstStrict, secondStrict, thirdStrict, fourthStrict⟩
      (by simp [keepTriple])

/-- A weak owner chain with multiplicities `2,2,1` determines the exact
renamed `x t y x y` projection. -/
theorem alternatingTripleProjection_of_orderedOwners
    {source : Word Nat}
    {first second separator
      firstOwner separatorOwner secondOwner
      firstSecondOwner secondSecondOwner : Nat}
    (distinct : [first, second, separator].Nodup)
    (firstCount : source.toList.count first = 2)
    (secondCount : source.toList.count second = 2)
    (separatorCount : source.toList.count separator = 1)
    (firstAt :
      sourceAt source.toList firstOwner = some first)
    (separatorAt :
      sourceAt source.toList separatorOwner = some separator)
    (secondAt :
      sourceAt source.toList secondOwner = some second)
    (firstSecondAt :
      sourceAt source.toList firstSecondOwner = some first)
    (secondSecondAt :
      sourceAt source.toList secondSecondOwner = some second)
    (ownersOrdered :
      firstOwner ≤ separatorOwner ∧ separatorOwner ≤ secondOwner ∧
        secondOwner ≤ firstSecondOwner ∧
        firstSecondOwner ≤ secondSecondOwner) :
    source.toList.filter (keepTriple first second separator) =
      [first, separator, second, first, second] := by
  have inequalities := distinct
  simp only [List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at inequalities
  rcases inequalities with
    ⟨⟨firstSecond, firstSeparator⟩,
      ⟨secondSeparator, _⟩⟩
  have firstStrict : firstOwner < separatorOwner :=
    sourceAt_lt_of_le_of_ne firstAt separatorAt
      firstSeparator ownersOrdered.1
  have secondStrict : separatorOwner < secondOwner :=
    sourceAt_lt_of_le_of_ne separatorAt secondAt
      (Ne.symm secondSeparator) ownersOrdered.2.1
  have thirdStrict : secondOwner < firstSecondOwner :=
    sourceAt_lt_of_le_of_ne secondAt firstSecondAt
      (Ne.symm firstSecond) ownersOrdered.2.2.1
  have fourthStrict : firstSecondOwner < secondSecondOwner :=
    sourceAt_lt_of_le_of_ne firstSecondAt secondSecondAt
      firstSecond ownersOrdered.2.2.2
  exact
    exact_five_owner_keepTriple_projection distinct
      firstCount secondCount separatorCount
      firstAt separatorAt secondAt firstSecondAt secondSecondAt
      ⟨firstStrict, secondStrict, thirdStrict, fourthStrict⟩
      (by simp [keepTriple])

private theorem three_le_count_of_ordered_sourceAt
    {source : List Nat} {first second third sourceLetter : Nat}
    (firstAt : sourceAt source first = some sourceLetter)
    (secondAt : sourceAt source second = some sourceLetter)
    (thirdAt : sourceAt source third = some sourceLetter)
    (ordered : first < second ∧ second < third) :
    3 ≤ source.count sourceLetter := by
  let indices : List (Fin source.length) :=
    [⟨first, sourceAt_some_index_lt firstAt⟩,
      ⟨second, sourceAt_some_index_lt secondAt⟩,
      ⟨third, sourceAt_some_index_lt thirdAt⟩]
  have firstThird : first < third :=
    Nat.lt_trans ordered.1 ordered.2
  have indicesOrdered : indices.Pairwise (· < ·) := by
    simp [indices, Fin.mk_lt_mk, ordered.1, ordered.2, firstThird]
  have selectedSublist :=
    List.map_getElem_sublist indicesOrdered
  have selectedValues :
      indices.map (fun index => source[index]) =
        [sourceLetter, sourceLetter, sourceLetter] := by
    simp only [indices, List.map_cons, List.map_nil]
    congr 1
    · exact getElem_eq_of_sourceAt firstAt
    congr 1
    · exact getElem_eq_of_sourceAt secondAt
    congr 1
    exact getElem_eq_of_sourceAt thirdAt
  rw [selectedValues] at selectedSublist
  have countBound := selectedSublist.count_le sourceLetter
  simpa using countBound

private theorem repeatedSourceOrderedPairs_align
    {source : List Nat}
    {firstA firstB secondA secondB sourceLetter : Nat}
    (firstAAt : sourceAt source firstA = some sourceLetter)
    (firstBAt : sourceAt source firstB = some sourceLetter)
    (secondAAt : sourceAt source secondA = some sourceLetter)
    (secondBAt : sourceAt source secondB = some sourceLetter)
    (sourceCount : source.count sourceLetter = 2)
    (aOwnersDifferent : firstA ≠ secondA)
    (bOwnersDifferent : firstB ≠ secondB)
    (ownersOrdered :
      firstA ≤ firstB ∧ firstB ≤ secondA ∧ secondA ≤ secondB) :
    firstA = firstB ∧ secondA = secondB := by
  constructor
  · apply Decidable.byContradiction
    intro firstDifferent
    have firstLt : firstA < firstB := by omega
    have secondLt : firstB < secondB := by omega
    have countLower :=
      three_le_count_of_ordered_sourceAt
        firstAAt firstBAt secondBAt ⟨firstLt, secondLt⟩
    omega
  · apply Decidable.byContradiction
    intro secondDifferent
    have firstLt : firstA < secondA := by omega
    have secondLt : secondA < secondB := by omega
    have countLower :=
      three_le_count_of_ordered_sourceAt
        firstAAt secondAAt secondBAt ⟨firstLt, secondLt⟩
    omega

/-- Repeated source variables selected for target `x`, `y`, and a middle
marker `z` are pairwise distinct.  The owner hypotheses are the ordered
occurrences supplied by the six corresponding `BlockOccurrencePreimage`
records.  Only the nested `y,z` target projection is needed to distinguish
the repeated `y` and `z` sources; the other two aliases are then excluded by
the interleaving owner order and the two-occurrence source counts. -/
theorem repeatedPerkinsSources_nodup
    {source target : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : source.bind substitution = target)
    (pattern : OccurrencePattern extra target.toList)
    {z : Nat}
    (zMiddle : z ∈ middleVariables extra)
    {xFirst yFirst zFirst xSecond zSecond ySecond
      sourceX sourceY sourceZ : Nat}
    (xFirstAt : sourceAt source.toList xFirst = some sourceX)
    (yFirstAt : sourceAt source.toList yFirst = some sourceY)
    (zFirstAt : sourceAt source.toList zFirst = some sourceZ)
    (xSecondAt : sourceAt source.toList xSecond = some sourceX)
    (zSecondAt : sourceAt source.toList zSecond = some sourceZ)
    (ySecondAt : sourceAt source.toList ySecond = some sourceY)
    (xCount : source.toList.count sourceX = 2)
    (yCount : source.toList.count sourceY = 2)
    (yImage : 1 ∈ (substitution sourceY).toList)
    (zImage : z ∈ (substitution sourceZ).toList)
    (xOwnersDifferent : xFirst ≠ xSecond)
    (yOwnersDifferent : yFirst ≠ ySecond)
    (zOwnersDifferent : zFirst ≠ zSecond)
    (ownersOrdered :
      xFirst ≤ yFirst ∧ yFirst ≤ zFirst ∧
      zFirst ≤ xSecond ∧ xSecond ≤ zSecond ∧
      zSecond ≤ ySecond) :
    [sourceX, sourceY, sourceZ].Nodup := by
  have zLower : 2 ≤ z := by
    rcases List.mem_map.mp zMiddle with
      ⟨index, _indexMember, rfl⟩
    omega
  have oneNeZ : 1 ≠ z := by omega
  have zNeOne : z ≠ 1 := Ne.symm oneNeZ
  have zeroNeZ : 0 ≠ z := by omega
  have zNeZero : z ≠ 0 := Ne.symm zeroNeZ
  have targetXYZ :
      target.toList.filter (keepTriple 0 1 z) =
        [0, 1, z, 0, z, 1] := by
    simpa [occurrenceProjection, keepTriple] using
      pattern.occurrenceProjection_eq zMiddle
  have targetYZ :
      target.toList.filter (pairKeep 1 z) =
        [1, z, z, 1] := by
    calc
      target.toList.filter (pairKeep 1 z) =
          (target.toList.filter
            (keepTriple 0 1 z)).filter (pairKeep 1 z) := by
        symm
        apply filter_filter_of_implies
        intro letter kept
        simp [pairKeep] at kept
        rcases kept with rfl | rfl <;> simp [keepTriple]
      _ = [1, z, z, 1] := by
        rw [targetXYZ]
        simp [pairKeep, zeroNeZ, zNeZero, oneNeZ, zNeOne]
  have yzDifferent : sourceY ≠ sourceZ := by
    intro sourcesEqual
    have zImageY :
        z ∈ (substitution sourceY).toList := by
      simpa [sourcesEqual] using zImage
    have alternating :=
      repeated_source_forces_alternating_projection
        mapped pattern yCount oneNeZ yImage zImageY
    rw [targetYZ] at alternating
    rcases alternating with alternating | alternating <;>
      simp [oneNeZ, zNeOne] at alternating
  have xyDifferent : sourceX ≠ sourceY := by
    intro sourcesEqual
    have yFirstAtX := yFirstAt
    have ySecondAtX := ySecondAt
    rw [← sourcesEqual] at yFirstAtX ySecondAtX
    have aligned :=
      repeatedSourceOrderedPairs_align
        xFirstAt yFirstAtX xSecondAt ySecondAtX xCount
        xOwnersDifferent yOwnersDifferent
        ⟨ownersOrdered.1,
          Nat.le_trans ownersOrdered.2.1 ownersOrdered.2.2.1,
          Nat.le_trans ownersOrdered.2.2.2.1 ownersOrdered.2.2.2.2⟩
    have zSecondEq : zSecond = xSecond := by omega
    have zSecondAtX := zSecondAt
    rw [zSecondEq] at zSecondAtX
    have xzEqual :
        sourceX = sourceZ :=
      sourceAt_some_injective xSecondAt zSecondAtX
    apply yzDifferent
    exact sourcesEqual.symm.trans xzEqual
  have xzDifferent : sourceX ≠ sourceZ := by
    intro sourcesEqual
    have zFirstAtX := zFirstAt
    have zSecondAtX := zSecondAt
    rw [← sourcesEqual] at zFirstAtX zSecondAtX
    have aligned :=
      repeatedSourceOrderedPairs_align
        xFirstAt zFirstAtX xSecondAt zSecondAtX xCount
        xOwnersDifferent zOwnersDifferent
        ⟨Nat.le_trans ownersOrdered.1 ownersOrdered.2.1,
          ownersOrdered.2.2.1, ownersOrdered.2.2.2.1⟩
    have yFirstEq : yFirst = xFirst := by omega
    have yFirstAtX := yFirstAt
    rw [yFirstEq] at yFirstAtX
    have xyEqual :
        sourceX = sourceY :=
      sourceAt_some_injective xFirstAt yFirstAtX
    apply yzDifferent
    exact xyEqual.symm.trans sourcesEqual
  simp [xyDifferent, xzDifferent, yzDifferent]

def BlockLocalLinearContainer
    (source : Word Nat) (substitution : Nat → Word Nat)
    (preBlock block : List Nat) : Prop :=
  ∃ owner sourceLetter firstMarker secondMarker,
    sourceAt source.toList owner = some sourceLetter ∧
    source.toList.count sourceLetter = 1 ∧
    firstMarker ≠ secondMarker ∧
    BlockOccurrencePreimage source substitution preBlock block
      owner firstMarker ∧
    BlockOccurrencePreimage source substitution preBlock block
      owner secondMarker ∧
    firstMarker ∈ block ∧
    secondMarker ∈ block ∧
    firstMarker ∈ (substitution sourceLetter).toList ∧
    secondMarker ∈ (substitution sourceLetter).toList

private theorem select_block_local_linear_container
    {source target : Word Nat}
    (uses : WordUsesAtMost source (bound + 2))
    {substitution : Nat → Word Nat}
    (mapped : source.bind substitution = target)
    (pattern :
      OccurrencePattern (4 * bound + 7) target.toList)
    (semantic :
      (Identity.mk (obstruction bound).lhs target).SatisfiedBy
        table.semigroup)
    {preBlock block suffix : List Nat}
    (targetShape : target.toList = preBlock ++ block ++ suffix)
    (blockPerm :
      block.Perm (middleVariables (4 * bound + 7))) :
    BlockLocalLinearContainer source substitution preBlock block := by
  let images : Nat → List Nat :=
    fun letter => (substitution letter).toList
  let annotations :=
    annotateExpansion source.toList images
  let blockAnnotations :=
    annotationSlice annotations preBlock block
  let owners := blockAnnotations.map Prod.fst
  have annotationShape :
      annotations.map Prod.snd =
        preBlock ++ block ++ suffix := by
    rw [annotateExpansion_map_snd]
    simpa only [images, ← Word.toList_bind, mapped] using targetShape
  have blockMap :
      blockAnnotations.map Prod.snd = block := by
    exact annotationSlice_map_snd annotationShape
  have ownerLength : owners.length = block.length := by
    simpa only [owners, List.length_map] using
      congrArg List.length blockMap
  have ownerCover :
      ∀ owner, owner ∈ owners →
        owner ∈ List.range source.toList.length := by
    exact
      map_fst_annotationSlice_covered
        source.toList images preBlock block
  have sourceLength :=
    preimage_word_length_le_two_mul uses mapped pattern
  have blockLength : block.length = 4 * bound + 7 := by
    rw [blockPerm.length_eq]
    simp [middleVariables]
  have sourceSmaller : source.toList.length < owners.length := by
    rw [ownerLength, blockLength]
    omega
  rcases
      exists_owner_count_two ownerCover
        (by simpa using sourceSmaller) with
    ⟨owner, ownerMember, ownerCount⟩
  let selectedMarkers :=
    (blockAnnotations.filter
      (fun entry => entry.1 == owner)).map Prod.snd
  have selectedLength : 2 ≤ selectedMarkers.length := by
    rw [filtered_owner_markers_length]
    exact ownerCount
  have selectedSublist : selectedMarkers.Sublist block := by
    have sublist :=
      filtered_owner_markers_sublist blockAnnotations owner
    rw [blockMap] at sublist
    exact sublist
  have middleNodup :
      (middleVariables (4 * bound + 7)).Nodup := by
    simp only [middleVariables]
    exact
      (List.nodup_range :
        (List.range (4 * bound + 7)).Nodup).map
        (fun index => index + 2)
        (by
          intro first second different equality
          apply different
          exact Nat.add_right_cancel equality)
  have blockNodup : block.Nodup :=
    blockPerm.nodup_iff.mpr middleNodup
  have selectedNodup : selectedMarkers.Nodup :=
    blockNodup.sublist selectedSublist
  rcases
      exists_two_distinct_of_nodup_length_two
        selectedNodup selectedLength with
    ⟨firstMarker, secondMarker, different,
      firstSelected, secondSelected⟩
  have selectedOwnerMember :
      ∀ marker, marker ∈ selectedMarkers →
        (owner, marker) ∈ blockAnnotations := by
    intro marker member
    rcases List.mem_map.mp member with
      ⟨entry, entryFiltered, equality⟩
    have ownerEquality : entry.1 = owner := by
      have kept := (List.mem_filter.mp entryFiltered).2
      simpa using kept
    have markerEquality : entry.2 = marker := by simpa using equality
    cases entry
    simp_all
  have firstAnnotation :=
    selectedOwnerMember firstMarker firstSelected
  have firstFull :=
    (annotationSlice_sublist annotations preBlock block).mem firstAnnotation
  rcases
      (mem_annotateExpansion_iff.mp firstFull) with
    ⟨sourceLetter, atOwner, firstInImage⟩
  have secondAnnotation :=
    selectedOwnerMember secondMarker secondSelected
  have secondFull :=
    (annotationSlice_sublist annotations preBlock block).mem secondAnnotation
  rcases
      (mem_annotateExpansion_iff.mp secondFull) with
    ⟨secondSourceLetter, secondAtOwner, secondInImage⟩
  have sourceEquality : secondSourceLetter = sourceLetter := by
    rw [atOwner] at secondAtOwner
    exact (Option.some.inj secondAtOwner).symm
  subst secondSourceLetter
  have sourceMember : sourceLetter ∈ source.toList :=
    sourceAt_some_mem atOwner
  have firstInBlock := selectedSublist.mem firstSelected
  have secondInBlock := selectedSublist.mem secondSelected
  have firstMiddle := blockPerm.mem_iff.mp firstInBlock
  have secondMiddle := blockPerm.mem_iff.mp secondInBlock
  have anchorProjection :
      (obstruction bound).lhs.toList.filter
            (pairKeep firstMarker secondMarker) =
          [firstMarker, secondMarker, secondMarker, firstMarker] ∨
        (obstruction bound).lhs.toList.filter
            (pairKeep firstMarker secondMarker) =
          [secondMarker, firstMarker, firstMarker, secondMarker] := by
    simpa [obstruction, perkinsIdentity] using
      perkinsLeft_pair_projection
        different firstMiddle secondMiddle
  have linear :=
    selected_source_variable_is_linear mapped pattern semantic
      sourceMember different firstInImage secondInImage anchorProjection
  exact
    ⟨owner, sourceLetter, firstMarker, secondMarker,
      atOwner, linear, different, firstAnnotation, secondAnnotation,
      firstInBlock, secondInBlock, firstInImage, secondInImage⟩

/-- Independent source-occurrence containers for the forward and reverse
middle blocks of a Perkins-pattern target.  The source variables are linear;
they are not required to have different names, matching Sapir's explicit
allowance that the two selected occurrences can come from one linear
variable image. -/
theorem select_two_block_local_linear_containers
    {source target : Word Nat}
    (uses : WordUsesAtMost source (bound + 2))
    {substitution : Nat → Word Nat}
    (mapped : source.bind substitution = target)
    (pattern :
      OccurrencePattern (4 * bound + 7) target.toList)
    (semantic :
      (Identity.mk (obstruction bound).lhs target).SatisfiedBy
        table.semigroup) :
    ∃ firstBlock secondBlock,
      firstBlock.Perm (middleVariables (4 * bound + 7)) ∧
      secondBlock.Perm (middleVariables (4 * bound + 7)) ∧
      target.toList =
        [0, 1] ++ firstBlock ++ [0] ++ secondBlock ++ [1] ∧
      BlockLocalLinearContainer source substitution [0, 1] firstBlock ∧
      BlockLocalLinearContainer source substitution
        ([0, 1] ++ firstBlock ++ [0]) secondBlock := by
  rcases pattern with
    ⟨firstBlock, secondBlock, firstPerm, secondPerm, targetShape⟩
  have firstContainer :
      BlockLocalLinearContainer source substitution
        [0, 1] firstBlock := by
    apply select_block_local_linear_container
      uses mapped
      ⟨firstBlock, secondBlock, firstPerm, secondPerm, targetShape⟩
      semantic
      (preBlock := [0, 1])
      (suffix := [0] ++ secondBlock ++ [1])
    simpa only [List.append_assoc] using targetShape
    exact firstPerm
  have secondContainer :
      BlockLocalLinearContainer source substitution
        ([0, 1] ++ firstBlock ++ [0]) secondBlock := by
    apply select_block_local_linear_container
      uses mapped
      ⟨firstBlock, secondBlock, firstPerm, secondPerm, targetShape⟩
      semantic
      (preBlock := [0, 1] ++ firstBlock ++ [0])
      (suffix := [1])
    simpa only [List.append_assoc] using targetShape
    exact secondPerm
  exact
    ⟨firstBlock, secondBlock, firstPerm, secondPerm,
      targetShape, firstContainer, secondContainer⟩

theorem blockOccurrencePreimage_exists
    {source target : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : source.bind substitution = target)
    {preBlock block suffix : List Nat}
    (targetShape : target.toList = preBlock ++ block ++ suffix)
    {marker : Nat} (markerMember : marker ∈ block) :
    ∃ owner,
      BlockOccurrencePreimage source substitution
        preBlock block owner marker := by
  let annotations :=
    annotateExpansion source.toList
      (fun letter => (substitution letter).toList)
  have annotationShape :
      annotations.map Prod.snd =
        preBlock ++ block ++ suffix := by
    rw [annotateExpansion_map_snd]
    simpa only [← Word.toList_bind, mapped] using targetShape
  have blockMap :
      (annotationSlice annotations preBlock block).map Prod.snd =
        block :=
    annotationSlice_map_snd annotationShape
  have markerMapped :
      marker ∈
        (annotationSlice annotations preBlock block).map Prod.snd := by
    rw [blockMap]
    exact markerMember
  rcases List.mem_map.mp markerMapped with
    ⟨⟨owner, actualMarker⟩, occurrenceMember, markerEquality⟩
  simp only at markerEquality
  subst actualMarker
  exact ⟨owner, occurrenceMember⟩

theorem BlockOccurrencePreimage.sourceData
    {source : Word Nat} {substitution : Nat → Word Nat}
    {preBlock block : List Nat} {owner marker : Nat}
    (preimage :
      BlockOccurrencePreimage source substitution
        preBlock block owner marker) :
    ∃ sourceLetter,
      sourceAt source.toList owner = some sourceLetter ∧
      marker ∈ (substitution sourceLetter).toList := by
  have fullMember :=
    (annotationSlice_sublist
      (annotateExpansion source.toList
        (fun letter => (substitution letter).toList))
      preBlock block).mem preimage
  exact mem_annotateExpansion_iff.mp fullMember

private theorem two_source_contributions_le
    (source : List Nat) (images : Nat → List Nat)
    (firstSource secondSource marker : Nat)
    (different : firstSource ≠ secondSource) :
    source.count firstSource * (images firstSource).count marker +
        source.count secondSource * (images secondSource).count marker ≤
      (source.flatMap images).count marker := by
  induction source with
  | nil => simp
  | cons head rest ih =>
      simp only [List.flatMap_cons, List.count_append]
      by_cases headFirst : head = firstSource
      · subst head
        have headSecond : firstSource ≠ secondSource := different
        simp only [List.count_cons_self,
          List.count_cons_of_ne headSecond]
        rw [Nat.add_mul]
        omega
      · by_cases headSecond : head = secondSource
        · subst head
          have secondFirst : secondSource ≠ firstSource :=
            Ne.symm different
          simp only [List.count_cons_self,
            List.count_cons_of_ne secondFirst]
          rw [Nat.add_mul]
          omega
        · rw [List.count_cons_of_ne headFirst,
            List.count_cons_of_ne headSecond]
          exact Nat.le_trans ih (Nat.le_add_left _ _)

private theorem three_source_contributions_le
    (source : List Nat) (images : Nat → List Nat)
    (firstSource secondSource thirdSource marker : Nat)
    (firstSecond : firstSource ≠ secondSource)
    (firstThird : firstSource ≠ thirdSource)
    (secondThird : secondSource ≠ thirdSource) :
    source.count firstSource * (images firstSource).count marker +
        source.count secondSource * (images secondSource).count marker +
        source.count thirdSource * (images thirdSource).count marker ≤
      (source.flatMap images).count marker := by
  induction source with
  | nil => simp
  | cons head rest ih =>
      simp only [List.flatMap_cons, List.count_append]
      by_cases headFirst : head = firstSource
      · subst head
        simp only [List.count_cons_self,
          List.count_cons_of_ne firstSecond,
          List.count_cons_of_ne firstThird]
        rw [Nat.add_mul]
        omega
      · by_cases headSecond : head = secondSource
        · subst head
          simp only [List.count_cons_self,
            List.count_cons_of_ne (Ne.symm firstSecond),
            List.count_cons_of_ne secondThird]
          rw [Nat.add_mul]
          omega
        · by_cases headThird : head = thirdSource
          · subst head
            simp only [List.count_cons_self,
              List.count_cons_of_ne (Ne.symm firstThird),
              List.count_cons_of_ne (Ne.symm secondThird)]
            rw [Nat.add_mul]
            omega
          · rw [List.count_cons_of_ne headFirst,
              List.count_cons_of_ne headSecond,
              List.count_cons_of_ne headThird]
            exact Nat.le_trans ih (Nat.le_add_left _ _)

/-- A repeated source variable that contributes a target marker exhausts both
target occurrences, so no distinct source variable can contribute that
marker. -/
theorem repeatedSource_uniqueMarkerContributor
    {source target : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : source.bind substitution = target)
    (pattern : OccurrencePattern extra target.toList)
    {selected marker sourceLetter : Nat}
    (selectedCount : source.toList.count selected = 2)
    (selectedImage : marker ∈ (substitution selected).toList)
    (sourceMember : sourceLetter ∈ source.toList)
    (sourceImage : marker ∈ (substitution sourceLetter).toList) :
    sourceLetter = selected := by
  apply Decidable.byContradiction
  intro different
  let images : Nat → List Nat :=
    fun letter => (substitution letter).toList
  have contributions :=
    two_source_contributions_le source.toList images
      selected sourceLetter marker (Ne.symm different)
  rw [← Word.toList_bind, mapped] at contributions
  have selectedImagePositive :
      1 ≤ (images selected).count marker :=
    List.count_pos_iff.mpr selectedImage
  have sourceCountPositive :
      1 ≤ source.toList.count sourceLetter :=
    List.count_pos_iff.mpr sourceMember
  have sourceImagePositive :
      1 ≤ (images sourceLetter).count marker :=
    List.count_pos_iff.mpr sourceImage
  have sourceCountsLe :
      source.toList.count selected +
          source.toList.count sourceLetter ≤
        target.toList.count marker := by
    exact Nat.le_trans
      (Nat.add_le_add
        (Nat.le_mul_of_pos_right _ selectedImagePositive)
        (Nat.le_mul_of_pos_right _ sourceImagePositive))
      contributions
  have targetBound := pattern.count_le_two marker
  rw [selectedCount] at sourceCountsLe
  omega

/-- In the linear branch of Sapir's `2occ` dichotomy, the two selected
linear source labels are all source variables that can contribute the target
marker.  The proof also covers the case where one linear source occurrence
contains both target occurrences. -/
theorem linearSources_completeMarkerContributors_of_sections
    {source target : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : source.bind substitution = target)
    (pattern : OccurrencePattern extra target.toList)
    {first second third fourth fifth : List Nat}
    (targetShape :
      target.toList =
        first ++ second ++ third ++ fourth ++ fifth)
    {firstOwner secondOwner marker firstSource secondSource
      sourceLetter : Nat}
    (firstPreimage :
      BlockOccurrencePreimage source substitution
        first second firstOwner marker)
    (secondPreimage :
      BlockOccurrencePreimage source substitution
        (first ++ second ++ third) fourth secondOwner marker)
    (firstAt :
      sourceAt source.toList firstOwner = some firstSource)
    (secondAt :
      sourceAt source.toList secondOwner = some secondSource)
    (firstCount : source.toList.count firstSource = 1)
    (secondCount : source.toList.count secondSource = 1)
    (firstImage : marker ∈ (substitution firstSource).toList)
    (secondImage : marker ∈ (substitution secondSource).toList)
    (sourceMember : sourceLetter ∈ source.toList)
    (sourceImage : marker ∈ (substitution sourceLetter).toList) :
    sourceLetter = firstSource ∨ sourceLetter = secondSource := by
  let images : Nat → List Nat :=
    fun letter => (substitution letter).toList
  have sourceCountPositive :
      1 ≤ source.toList.count sourceLetter :=
    List.count_pos_iff.mpr sourceMember
  have sourceImagePositive :
      1 ≤ (images sourceLetter).count marker :=
    List.count_pos_iff.mpr sourceImage
  by_cases selectedEqual : firstSource = secondSource
  · subst secondSource
    have ownersEqual :
        firstOwner = secondOwner :=
      sourceAt_eq_of_count_one firstAt secondAt firstCount
    subst secondOwner
    by_cases sourceEqual : sourceLetter = firstSource
    · exact Or.inl sourceEqual
    · exfalso
      have mappedShape :
          (source.bind substitution).toList =
            first ++ second ++ third ++ fourth ++ fifth := by
        rw [mapped]
        exact targetShape
      have annotationCount :
          2 ≤
            (annotateExpansion source.toList images).count
              (firstOwner, marker) :=
        blockOccurrencePair_count_two_of_sections
          mappedShape firstPreimage secondPreimage
      have selectedImageCount :
          2 ≤ (images firstSource).count marker := by
        rw [annotateExpansion_count_owner_marker firstAt] at annotationCount
        exact annotationCount
      have contributions :=
        two_source_contributions_le source.toList images
          firstSource sourceLetter marker (Ne.symm sourceEqual)
      rw [← Word.toList_bind, mapped] at contributions
      have selectedContribution :
          2 ≤
            source.toList.count firstSource *
              (images firstSource).count marker := by
        simpa [firstCount] using selectedImageCount
      have sourceContribution :
          1 ≤
            source.toList.count sourceLetter *
              (images sourceLetter).count marker :=
        Nat.mul_pos sourceCountPositive sourceImagePositive
      have targetBound := pattern.count_le_two marker
      omega
  · by_cases sourceFirst : sourceLetter = firstSource
    · exact Or.inl sourceFirst
    · by_cases sourceSecond : sourceLetter = secondSource
      · exact Or.inr sourceSecond
      · exfalso
        have contributions :=
          three_source_contributions_le source.toList images
            firstSource secondSource sourceLetter marker
            selectedEqual (Ne.symm sourceFirst) (Ne.symm sourceSecond)
        rw [← Word.toList_bind, mapped] at contributions
        have firstImagePositive :
            1 ≤ (images firstSource).count marker :=
          List.count_pos_iff.mpr firstImage
        have secondImagePositive :
            1 ≤ (images secondSource).count marker :=
          List.count_pos_iff.mpr secondImage
        have firstContribution :
            1 ≤
              source.toList.count firstSource *
                (images firstSource).count marker := by
          simpa [firstCount] using firstImagePositive
        have secondContribution :
            1 ≤
              source.toList.count secondSource *
                (images secondSource).count marker := by
          simpa [secondCount] using secondImagePositive
        have sourceContribution :
            1 ≤
              source.toList.count sourceLetter *
                (images sourceLetter).count marker :=
          Nat.mul_pos sourceCountPositive sourceImagePositive
        have targetBound := pattern.count_le_two marker
        omega

def TwoOccurrencePreimageAlternative
    (source : Word Nat) (firstSource secondSource : Nat) : Prop :=
  (source.toList.count firstSource = 1 ∧
      source.toList.count secondSource = 1) ∨
    (firstSource = secondSource ∧
      source.toList.count firstSource = 2)

/-- Sapir's `2occ` source-variable dichotomy. Two annotated preimages of a
target marker occurring at most twice are either carried by linear source
variables, or by the two occurrences of one repeated source variable. The
linear branch includes one source occurrence whose image contains both target
occurrences. -/
theorem twoOccurrencePreimageAlternative
    {source target : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : source.bind substitution = target)
    (pattern : OccurrencePattern extra target.toList)
    {firstOwner secondOwner marker firstSource secondSource : Nat}
    (firstAt :
      sourceAt source.toList firstOwner = some firstSource)
    (secondAt :
      sourceAt source.toList secondOwner = some secondSource)
    (firstImage : marker ∈ (substitution firstSource).toList)
    (secondImage : marker ∈ (substitution secondSource).toList) :
    TwoOccurrencePreimageAlternative source firstSource secondSource := by
  let images : Nat → List Nat :=
    fun letter => (substitution letter).toList
  have firstMember : firstSource ∈ source.toList :=
    sourceAt_some_mem firstAt
  have secondMember : secondSource ∈ source.toList :=
    sourceAt_some_mem secondAt
  have firstPositive :
      1 ≤ source.toList.count firstSource :=
    List.count_pos_iff.mpr firstMember
  have secondPositive :
      1 ≤ source.toList.count secondSource :=
    List.count_pos_iff.mpr secondMember
  have firstBound :=
    preimage_variable_count_le_two mapped pattern firstMember
  have secondBound :=
    preimage_variable_count_le_two mapped pattern secondMember
  by_cases firstLinear : source.toList.count firstSource = 1
  · left
    refine ⟨firstLinear, ?_⟩
    by_cases same : firstSource = secondSource
    · simpa [same] using firstLinear
    · have contributions :=
        two_source_contributions_le source.toList images
          firstSource secondSource marker same
      rw [← Word.toList_bind, mapped] at contributions
      have firstImagePositive :
          1 ≤ (images firstSource).count marker :=
        List.count_pos_iff.mpr firstImage
      have secondImagePositive :
          1 ≤ (images secondSource).count marker :=
        List.count_pos_iff.mpr secondImage
      have sourceCountsLe :
          source.toList.count firstSource +
              source.toList.count secondSource ≤
            target.toList.count marker := by
        exact Nat.le_trans
          (Nat.add_le_add
            (Nat.le_mul_of_pos_right _ firstImagePositive)
            (Nat.le_mul_of_pos_right _ secondImagePositive))
          contributions
      have targetBound := pattern.count_le_two marker
      omega
  · have firstRepeated :
        source.toList.count firstSource = 2 := by
      omega
    right
    refine ⟨?_, firstRepeated⟩
    apply Decidable.byContradiction
    intro different
    have contributions :=
      two_source_contributions_le source.toList images
        firstSource secondSource marker different
    rw [← Word.toList_bind, mapped] at contributions
    have firstImagePositive :
        1 ≤ (images firstSource).count marker :=
      List.count_pos_iff.mpr firstImage
    have secondImagePositive :
        1 ≤ (images secondSource).count marker :=
      List.count_pos_iff.mpr secondImage
    have sourceCountsLe :
        source.toList.count firstSource +
            source.toList.count secondSource ≤
          target.toList.count marker := by
      exact Nat.le_trans
        (Nat.add_le_add
          (Nat.le_mul_of_pos_right _ firstImagePositive)
          (Nat.le_mul_of_pos_right _ secondImagePositive))
        contributions
    have targetBound := pattern.count_le_two marker
    omega

def TwoBlockMarkerPreimages
    (source : Word Nat) (substitution : Nat → Word Nat)
    (firstPre firstBlock secondPre secondBlock : List Nat)
    (marker : Nat) : Prop :=
  ∃ firstOwner secondOwner firstSource secondSource,
    BlockOccurrencePreimage source substitution
      firstPre firstBlock firstOwner marker ∧
    BlockOccurrencePreimage source substitution
      secondPre secondBlock secondOwner marker ∧
    sourceAt source.toList firstOwner = some firstSource ∧
    sourceAt source.toList secondOwner = some secondSource ∧
    marker ∈ (substitution firstSource).toList ∧
    marker ∈ (substitution secondSource).toList ∧
    TwoOccurrencePreimageAlternative source firstSource secondSource

def LinearTwoBlockMarkerPreimages
    (source : Word Nat) (substitution : Nat → Word Nat)
    (firstPre firstBlock secondPre secondBlock : List Nat)
    (marker : Nat) : Prop :=
  ∃ firstOwner secondOwner firstSource secondSource,
    BlockOccurrencePreimage source substitution
      firstPre firstBlock firstOwner marker ∧
    BlockOccurrencePreimage source substitution
      secondPre secondBlock secondOwner marker ∧
    sourceAt source.toList firstOwner = some firstSource ∧
    sourceAt source.toList secondOwner = some secondSource ∧
    marker ∈ (substitution firstSource).toList ∧
    marker ∈ (substitution secondSource).toList ∧
    source.toList.count firstSource = 1 ∧
    source.toList.count secondSource = 1

def RepeatedTwoBlockMarkerPreimages
    (source : Word Nat) (substitution : Nat → Word Nat)
    (firstPre firstBlock secondPre secondBlock : List Nat)
    (marker : Nat) : Prop :=
  ∃ firstOwner secondOwner sourceLetter,
    BlockOccurrencePreimage source substitution
      firstPre firstBlock firstOwner marker ∧
    BlockOccurrencePreimage source substitution
      secondPre secondBlock secondOwner marker ∧
    sourceAt source.toList firstOwner = some sourceLetter ∧
    sourceAt source.toList secondOwner = some sourceLetter ∧
    marker ∈ (substitution sourceLetter).toList ∧
    source.toList.count sourceLetter = 2

/-- Package Sapir's `2occ` alternative into complete linear and repeated
preimage records. -/
theorem TwoBlockMarkerPreimages.linear_or_repeated
    {source : Word Nat} {substitution : Nat → Word Nat}
    {firstPre firstBlock secondPre secondBlock : List Nat}
    {marker : Nat}
    (preimages :
      TwoBlockMarkerPreimages source substitution
        firstPre firstBlock secondPre secondBlock marker) :
    LinearTwoBlockMarkerPreimages source substitution
        firstPre firstBlock secondPre secondBlock marker ∨
      RepeatedTwoBlockMarkerPreimages source substitution
        firstPre firstBlock secondPre secondBlock marker := by
  rcases preimages with
    ⟨firstOwner, secondOwner, firstSource, secondSource,
      firstPreimage, secondPreimage, firstAt, secondAt,
      firstImage, secondImage, alternative⟩
  rcases alternative with linear | repeated
  · exact Or.inl
      ⟨firstOwner, secondOwner, firstSource, secondSource,
        firstPreimage, secondPreimage, firstAt, secondAt,
        firstImage, secondImage, linear⟩
  · rcases repeated with ⟨sourcesEqual, firstCount⟩
    subst secondSource
    exact Or.inr
      ⟨firstOwner, secondOwner, firstSource,
        firstPreimage, secondPreimage, firstAt, secondAt,
        firstImage, firstCount⟩

/-- The two selected source labels are the complete inverse contributor set
of their target marker, independently of the linear/repeated alternative. -/
theorem twoOccurrenceAlternative_completeContributors_of_sections
    {source target : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : source.bind substitution = target)
    (pattern : OccurrencePattern extra target.toList)
    {first second third fourth fifth : List Nat}
    (targetShape :
      target.toList =
        first ++ second ++ third ++ fourth ++ fifth)
    {firstOwner secondOwner marker firstSource secondSource
      sourceLetter : Nat}
    (firstPreimage :
      BlockOccurrencePreimage source substitution
        first second firstOwner marker)
    (secondPreimage :
      BlockOccurrencePreimage source substitution
        (first ++ second ++ third) fourth secondOwner marker)
    (firstAt :
      sourceAt source.toList firstOwner = some firstSource)
    (secondAt :
      sourceAt source.toList secondOwner = some secondSource)
    (firstImage : marker ∈ (substitution firstSource).toList)
    (secondImage : marker ∈ (substitution secondSource).toList)
    (alternative :
      TwoOccurrencePreimageAlternative source firstSource secondSource)
    (sourceMember : sourceLetter ∈ source.toList)
    (sourceImage : marker ∈ (substitution sourceLetter).toList) :
    sourceLetter = firstSource ∨ sourceLetter = secondSource := by
  rcases alternative with linear | repeated
  · exact
      linearSources_completeMarkerContributors_of_sections
        mapped pattern targetShape firstPreimage secondPreimage
        firstAt secondAt linear.1 linear.2
        firstImage secondImage sourceMember sourceImage
  · rcases repeated with ⟨sourcesEqual, sourceCount⟩
    subst secondSource
    exact Or.inl
      (repeatedSource_uniqueMarkerContributor
        mapped pattern sourceCount firstImage
        sourceMember sourceImage)

theorem selectTwoBlockMarkerPreimages
    {source target : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : source.bind substitution = target)
    (pattern : OccurrencePattern extra target.toList)
    {firstPre firstBlock firstSuffix
      secondPre secondBlock secondSuffix : List Nat}
    (firstShape :
      target.toList = firstPre ++ firstBlock ++ firstSuffix)
    (secondShape :
      target.toList = secondPre ++ secondBlock ++ secondSuffix)
    {marker : Nat}
    (firstMember : marker ∈ firstBlock)
    (secondMember : marker ∈ secondBlock) :
    TwoBlockMarkerPreimages source substitution
      firstPre firstBlock secondPre secondBlock marker := by
  rcases
      blockOccurrencePreimage_exists mapped firstShape firstMember with
    ⟨firstOwner, firstPreimage⟩
  rcases
      blockOccurrencePreimage_exists mapped secondShape secondMember with
    ⟨secondOwner, secondPreimage⟩
  rcases firstPreimage.sourceData with
    ⟨firstSource, firstAt, firstImage⟩
  rcases secondPreimage.sourceData with
    ⟨secondSource, secondAt, secondImage⟩
  exact
    ⟨firstOwner, secondOwner, firstSource, secondSource,
      firstPreimage, secondPreimage, firstAt, secondAt,
      firstImage, secondImage,
      twoOccurrencePreimageAlternative mapped pattern
        firstAt secondAt firstImage secondImage⟩

def PerkinsDistinguishedPreimages
    (source : Word Nat) (substitution : Nat → Word Nat)
    (blockSize : Nat) (firstBlock secondBlock : List Nat) : Prop :=
  TwoBlockMarkerPreimages source substitution
      [] [0] ([0, 1] ++ firstBlock) [0] 0 ∧
    TwoBlockMarkerPreimages source substitution
      [0] [1]
      ([0, 1] ++ firstBlock ++ [0] ++ secondBlock) [1] 1 ∧
    ∀ z, z ∈ middleVariables blockSize →
      TwoBlockMarkerPreimages source substitution
        [0, 1] firstBlock
        ([0, 1] ++ firstBlock ++ [0]) secondBlock z

/-- The three independent `2occ` alternatives for target `x`, target `y`,
and one selected middle marker.  Splitting these disjunctions gives the
eight branches of the final semantic-projection proof. -/
theorem PerkinsDistinguishedPreimages.markerAlternatives
    {source : Word Nat} {substitution : Nat → Word Nat}
    {blockSize : Nat} {firstBlock secondBlock : List Nat}
    (preimages :
      PerkinsDistinguishedPreimages source substitution
        blockSize firstBlock secondBlock)
    {z : Nat} (zMiddle : z ∈ middleVariables blockSize) :
    (LinearTwoBlockMarkerPreimages source substitution
          [] [0] ([0, 1] ++ firstBlock) [0] 0 ∨
        RepeatedTwoBlockMarkerPreimages source substitution
          [] [0] ([0, 1] ++ firstBlock) [0] 0) ∧
      (LinearTwoBlockMarkerPreimages source substitution
          [0] [1]
          ([0, 1] ++ firstBlock ++ [0] ++ secondBlock) [1] 1 ∨
        RepeatedTwoBlockMarkerPreimages source substitution
          [0] [1]
          ([0, 1] ++ firstBlock ++ [0] ++ secondBlock) [1] 1) ∧
      (LinearTwoBlockMarkerPreimages source substitution
          [0, 1] firstBlock
          ([0, 1] ++ firstBlock ++ [0]) secondBlock z ∨
        RepeatedTwoBlockMarkerPreimages source substitution
          [0, 1] firstBlock
          ([0, 1] ++ firstBlock ++ [0]) secondBlock z) := by
  exact
    ⟨preimages.1.linear_or_repeated,
      preimages.2.1.linear_or_repeated,
      (preimages.2.2 z zMiddle).linear_or_repeated⟩

/-- The distinguished target blocks impose one common weak order on their
six selected source owners, independently of whether their source labels are
linear or repeated. -/
theorem perkinsDistinguishedOwnerChain
    {source target : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : source.bind substitution = target)
    {firstBlock secondBlock : List Nat}
    (targetShape :
      target.toList =
        [0, 1] ++ firstBlock ++ [0] ++ secondBlock ++ [1])
    {z xFirst yFirst zFirst xSecond zSecond ySecond : Nat}
    (xFirstPreimage :
      BlockOccurrencePreimage source substitution
        [] [0] xFirst 0)
    (yFirstPreimage :
      BlockOccurrencePreimage source substitution
        [0] [1] yFirst 1)
    (zFirstPreimage :
      BlockOccurrencePreimage source substitution
        [0, 1] firstBlock zFirst z)
    (xSecondPreimage :
      BlockOccurrencePreimage source substitution
        ([0, 1] ++ firstBlock) [0] xSecond 0)
    (zSecondPreimage :
      BlockOccurrencePreimage source substitution
        ([0, 1] ++ firstBlock ++ [0]) secondBlock zSecond z)
    (ySecondPreimage :
      BlockOccurrencePreimage source substitution
        ([0, 1] ++ firstBlock ++ [0] ++ secondBlock)
        [1] ySecond 1) :
    xFirst ≤ yFirst ∧ yFirst ≤ zFirst ∧
      zFirst ≤ xSecond ∧ xSecond ≤ zSecond ∧
      zSecond ≤ ySecond := by
  have mappedShape :
      (source.bind substitution).toList =
        [0, 1] ++ firstBlock ++ [0] ++ secondBlock ++ [1] := by
    rw [mapped]
    exact targetShape
  have xBeforeY : xFirst ≤ yFirst := by
    apply blockOccurrenceOwner_le_of_sections
      (first := []) (second := [0]) (third := [])
      (fourth := [1])
      (fifth := firstBlock ++ [0] ++ secondBlock ++ [1])
      mappedShape xFirstPreimage yFirstPreimage
  have yBeforeZ : yFirst ≤ zFirst := by
    have sectionShape :
        (source.bind substitution).toList =
          [0] ++ [1] ++ [] ++ firstBlock ++
            ([0] ++ secondBlock ++ [1]) := by
      simpa only [List.append_assoc, List.append_nil] using mappedShape
    have laterPreimage :
        BlockOccurrencePreimage source substitution
          ([0] ++ [1] ++ []) firstBlock zFirst z := by
      simpa only [List.append_nil] using zFirstPreimage
    exact
      blockOccurrenceOwner_le_of_sections
        sectionShape yFirstPreimage laterPreimage
  have zBeforeX : zFirst ≤ xSecond := by
    have sectionShape :
        (source.bind substitution).toList =
          [0, 1] ++ firstBlock ++ [] ++ [0] ++
            (secondBlock ++ [1]) := by
      simpa only [List.append_assoc, List.append_nil] using mappedShape
    have laterPreimage :
        BlockOccurrencePreimage source substitution
          ([0, 1] ++ firstBlock ++ []) [0] xSecond 0 := by
      simpa only [List.append_nil] using xSecondPreimage
    exact
      blockOccurrenceOwner_le_of_sections
        sectionShape zFirstPreimage laterPreimage
  have xBeforeZ : xSecond ≤ zSecond := by
    have sectionShape :
        (source.bind substitution).toList =
          ([0, 1] ++ firstBlock) ++ [0] ++ [] ++
            secondBlock ++ [1] := by
      simpa only [List.append_assoc, List.append_nil] using mappedShape
    have laterPreimage :
        BlockOccurrencePreimage source substitution
          (([0, 1] ++ firstBlock) ++ [0] ++ [])
          secondBlock zSecond z := by
      simpa only [List.append_nil] using zSecondPreimage
    exact
      blockOccurrenceOwner_le_of_sections
        sectionShape xSecondPreimage laterPreimage
  have zBeforeY : zSecond ≤ ySecond := by
    have sectionShape :
        (source.bind substitution).toList =
          ([0, 1] ++ firstBlock ++ [0]) ++ secondBlock ++
            [] ++ [1] ++ [] := by
      simpa only [List.append_assoc, List.append_nil] using mappedShape
    have laterPreimage :
        BlockOccurrencePreimage source substitution
          (([0, 1] ++ firstBlock ++ [0]) ++
            secondBlock ++ [])
          [1] ySecond 1 := by
      simpa only [List.append_nil] using ySecondPreimage
    exact
      blockOccurrenceOwner_le_of_sections
        sectionShape zSecondPreimage laterPreimage
  exact
    ⟨xBeforeY, yBeforeZ, zBeforeX, xBeforeZ, zBeforeY⟩

/-- The three repeated marker records determine the ordered six source
occurrences used by Sapir's four projection cases. -/
theorem repeatedPerkinsOwnerFacts
    {source target : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : source.bind substitution = target)
    (pattern : OccurrencePattern extra target.toList)
    {firstBlock secondBlock : List Nat}
    (targetShape :
      target.toList =
        [0, 1] ++ firstBlock ++ [0] ++ secondBlock ++ [1])
    {z : Nat} (zMiddle : z ∈ middleVariables extra)
    {xFirst xSecond sourceX
      yFirst ySecond sourceY
      zFirst zSecond sourceZ : Nat}
    (xFirstPreimage :
      BlockOccurrencePreimage source substitution
        [] [0] xFirst 0)
    (xSecondPreimage :
      BlockOccurrencePreimage source substitution
        ([0, 1] ++ firstBlock) [0] xSecond 0)
    (yFirstPreimage :
      BlockOccurrencePreimage source substitution
        [0] [1] yFirst 1)
    (ySecondPreimage :
      BlockOccurrencePreimage source substitution
        ([0, 1] ++ firstBlock ++ [0] ++ secondBlock)
        [1] ySecond 1)
    (zFirstPreimage :
      BlockOccurrencePreimage source substitution
        [0, 1] firstBlock zFirst z)
    (zSecondPreimage :
      BlockOccurrencePreimage source substitution
        ([0, 1] ++ firstBlock ++ [0]) secondBlock zSecond z)
    (xFirstAt : sourceAt source.toList xFirst = some sourceX)
    (xSecondAt : sourceAt source.toList xSecond = some sourceX)
    (yFirstAt : sourceAt source.toList yFirst = some sourceY)
    (ySecondAt : sourceAt source.toList ySecond = some sourceY)
    (zFirstAt : sourceAt source.toList zFirst = some sourceZ)
    (zSecondAt : sourceAt source.toList zSecond = some sourceZ)
    (xCount : source.toList.count sourceX = 2)
    (yCount : source.toList.count sourceY = 2)
    (zCount : source.toList.count sourceZ = 2)
    (yImage : 1 ∈ (substitution sourceY).toList)
    (zImage : z ∈ (substitution sourceZ).toList) :
    (xFirst ≤ yFirst ∧ yFirst ≤ zFirst ∧
        zFirst ≤ xSecond ∧ xSecond ≤ zSecond ∧
        zSecond ≤ ySecond) ∧
      xFirst ≠ xSecond ∧
      yFirst ≠ ySecond ∧
      zFirst ≠ zSecond ∧
      [sourceX, sourceY, sourceZ].Nodup := by
  have mappedShape :
      (source.bind substitution).toList =
        [0, 1] ++ firstBlock ++ [0] ++ secondBlock ++ [1] := by
    rw [mapped]
    exact targetShape
  have xBeforeY : xFirst ≤ yFirst := by
    apply blockOccurrenceOwner_le_of_sections
      (first := []) (second := [0]) (third := [])
      (fourth := [1])
      (fifth := firstBlock ++ [0] ++ secondBlock ++ [1])
      mappedShape xFirstPreimage yFirstPreimage
  have yBeforeZ : yFirst ≤ zFirst := by
    have sectionShape :
        (source.bind substitution).toList =
          [0] ++ [1] ++ [] ++ firstBlock ++
            ([0] ++ secondBlock ++ [1]) := by
      simpa only [List.append_assoc, List.append_nil] using mappedShape
    have laterPreimage :
        BlockOccurrencePreimage source substitution
          ([0] ++ [1] ++ []) firstBlock zFirst z := by
      simpa only [List.append_nil] using zFirstPreimage
    exact
      blockOccurrenceOwner_le_of_sections
        sectionShape yFirstPreimage laterPreimage
  have zBeforeX : zFirst ≤ xSecond := by
    have sectionShape :
        (source.bind substitution).toList =
          [0, 1] ++ firstBlock ++ [] ++ [0] ++
            (secondBlock ++ [1]) := by
      simpa only [List.append_assoc, List.append_nil] using mappedShape
    have laterPreimage :
        BlockOccurrencePreimage source substitution
          ([0, 1] ++ firstBlock ++ []) [0] xSecond 0 := by
      simpa only [List.append_nil] using xSecondPreimage
    exact
      blockOccurrenceOwner_le_of_sections
        sectionShape zFirstPreimage laterPreimage
  have xBeforeZ : xSecond ≤ zSecond := by
    have sectionShape :
        (source.bind substitution).toList =
          ([0, 1] ++ firstBlock) ++ [0] ++ [] ++
            secondBlock ++ [1] := by
      simpa only [List.append_assoc, List.append_nil] using mappedShape
    have laterPreimage :
        BlockOccurrencePreimage source substitution
          (([0, 1] ++ firstBlock) ++ [0] ++ [])
          secondBlock zSecond z := by
      simpa only [List.append_nil] using zSecondPreimage
    exact
      blockOccurrenceOwner_le_of_sections
        sectionShape xSecondPreimage laterPreimage
  have zBeforeY : zSecond ≤ ySecond := by
    have sectionShape :
        (source.bind substitution).toList =
          ([0, 1] ++ firstBlock ++ [0]) ++ secondBlock ++
            [] ++ [1] ++ [] := by
      simpa only [List.append_assoc, List.append_nil] using mappedShape
    have laterPreimage :
        BlockOccurrencePreimage source substitution
          (([0, 1] ++ firstBlock ++ [0]) ++
            secondBlock ++ [])
          [1] ySecond 1 := by
      simpa only [List.append_nil] using ySecondPreimage
    exact
      blockOccurrenceOwner_le_of_sections
        sectionShape zSecondPreimage laterPreimage
  have xOwnersDifferent : xFirst ≠ xSecond := by
    have sectionShape :
        target.toList =
          [] ++ [0] ++ ([1] ++ firstBlock) ++ [0] ++
            (secondBlock ++ [1]) := by
      simpa only [List.nil_append, List.append_assoc] using targetShape
    have laterPreimage :
        BlockOccurrencePreimage source substitution
          ([] ++ [0] ++ ([1] ++ firstBlock))
          [0] xSecond 0 := by
      simpa only [List.nil_append, List.append_assoc] using
        xSecondPreimage
    exact
      repeatedPreimageOwners_ne_of_sections
        mapped pattern sectionShape xFirstPreimage laterPreimage
        xFirstAt xCount
  have yOwnersDifferent : yFirst ≠ ySecond := by
    have sectionShape :
        target.toList =
          [0] ++ [1] ++
            (firstBlock ++ [0] ++ secondBlock) ++ [1] ++ [] := by
      simpa only [List.append_assoc, List.append_nil] using targetShape
    have laterPreimage :
        BlockOccurrencePreimage source substitution
          ([0] ++ [1] ++
            (firstBlock ++ [0] ++ secondBlock))
          [1] ySecond 1 := by
      simpa only [List.append_assoc] using ySecondPreimage
    exact
      repeatedPreimageOwners_ne_of_sections
        mapped pattern sectionShape yFirstPreimage laterPreimage
        yFirstAt yCount
  have zOwnersDifferent : zFirst ≠ zSecond := by
    apply repeatedPreimageOwners_ne_of_sections
      mapped pattern targetShape zFirstPreimage zSecondPreimage
      zFirstAt zCount
  have sourcesNodup :
      [sourceX, sourceY, sourceZ].Nodup :=
    repeatedPerkinsSources_nodup mapped pattern zMiddle
      xFirstAt yFirstAt zFirstAt xSecondAt zSecondAt ySecondAt
      xCount yCount yImage zImage
      xOwnersDifferent yOwnersDifferent zOwnersDifferent
      ⟨xBeforeY, yBeforeZ, zBeforeX, xBeforeZ, zBeforeY⟩
  exact
    ⟨⟨xBeforeY, yBeforeZ, zBeforeX, xBeforeZ, zBeforeY⟩,
      xOwnersDifferent, yOwnersDifferent, zOwnersDifferent,
      sourcesNodup⟩

/-- The two block-local linear separators lie between the fixed outside
owners independently of the selected middle marker. -/
theorem perkinsSeparatorOwnerOrder
    {source target : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : source.bind substitution = target)
    {firstBlock secondBlock : List Nat}
    (targetShape :
      target.toList =
        [0, 1] ++ firstBlock ++ [0] ++ secondBlock ++ [1])
    {yFirst t1Owner xSecond t2Owner ySecond
      t1Marker t2Marker : Nat}
    (yFirstPreimage :
      BlockOccurrencePreimage source substitution
        [0] [1] yFirst 1)
    (t1Preimage :
      BlockOccurrencePreimage source substitution
        [0, 1] firstBlock t1Owner t1Marker)
    (xSecondPreimage :
      BlockOccurrencePreimage source substitution
        ([0, 1] ++ firstBlock) [0] xSecond 0)
    (t2Preimage :
      BlockOccurrencePreimage source substitution
        ([0, 1] ++ firstBlock ++ [0]) secondBlock
        t2Owner t2Marker)
    (ySecondPreimage :
      BlockOccurrencePreimage source substitution
        ([0, 1] ++ firstBlock ++ [0] ++ secondBlock)
        [1] ySecond 1) :
    yFirst ≤ t1Owner ∧ t1Owner ≤ xSecond ∧
      xSecond ≤ t2Owner ∧ t2Owner ≤ ySecond := by
  have mappedShape :
      (source.bind substitution).toList =
        [0, 1] ++ firstBlock ++ [0] ++ secondBlock ++ [1] := by
    rw [mapped]
    exact targetShape
  have yBeforeT1 : yFirst ≤ t1Owner := by
    have sectionShape :
        (source.bind substitution).toList =
          [0] ++ [1] ++ [] ++ firstBlock ++
            ([0] ++ secondBlock ++ [1]) := by
      simpa only [List.append_assoc, List.append_nil] using mappedShape
    have laterPreimage :
        BlockOccurrencePreimage source substitution
          ([0] ++ [1] ++ []) firstBlock t1Owner t1Marker := by
      simpa only [List.append_nil] using t1Preimage
    exact
      blockOccurrenceOwner_le_of_sections
        sectionShape yFirstPreimage laterPreimage
  have t1BeforeX : t1Owner ≤ xSecond := by
    have sectionShape :
        (source.bind substitution).toList =
          [0, 1] ++ firstBlock ++ [] ++ [0] ++
            (secondBlock ++ [1]) := by
      simpa only [List.append_assoc, List.append_nil] using mappedShape
    have laterPreimage :
        BlockOccurrencePreimage source substitution
          ([0, 1] ++ firstBlock ++ []) [0] xSecond 0 := by
      simpa only [List.append_nil] using xSecondPreimage
    exact
      blockOccurrenceOwner_le_of_sections
        sectionShape t1Preimage laterPreimage
  have xBeforeT2 : xSecond ≤ t2Owner := by
    have sectionShape :
        (source.bind substitution).toList =
          ([0, 1] ++ firstBlock) ++ [0] ++ [] ++
            secondBlock ++ [1] := by
      simpa only [List.append_assoc, List.append_nil] using mappedShape
    have laterPreimage :
        BlockOccurrencePreimage source substitution
          (([0, 1] ++ firstBlock) ++ [0] ++ [])
          secondBlock t2Owner t2Marker := by
      simpa only [List.append_nil] using t2Preimage
    exact
      blockOccurrenceOwner_le_of_sections
        sectionShape xSecondPreimage laterPreimage
  have t2BeforeY : t2Owner ≤ ySecond := by
    have sectionShape :
        (source.bind substitution).toList =
          ([0, 1] ++ firstBlock ++ [0]) ++ secondBlock ++
            [] ++ [1] ++ [] := by
      simpa only [List.append_assoc, List.append_nil] using mappedShape
    have laterPreimage :
        BlockOccurrencePreimage source substitution
          (([0, 1] ++ firstBlock ++ [0]) ++
            secondBlock ++ [])
          [1] ySecond 1 := by
      simpa only [List.append_nil] using ySecondPreimage
    exact
      blockOccurrenceOwner_le_of_sections
        sectionShape t2Preimage laterPreimage
  exact ⟨yBeforeT1, t1BeforeX, xBeforeT2, t2BeforeY⟩

/-- Three repeated source labels and the two linear separator labels are
pairwise distinct.  The two separator occurrences are also strictly placed
on opposite sides of the selected second `x` occurrence. -/
theorem repeatedAndLinearSources_nodup
    {source : Word Nat}
    {sourceX sourceY sourceZ t1Source t2Source : Nat}
    {t1Owner xSecond t2Owner : Nat}
    (repeatedNodup : [sourceX, sourceY, sourceZ].Nodup)
    (xCount : source.toList.count sourceX = 2)
    (yCount : source.toList.count sourceY = 2)
    (zCount : source.toList.count sourceZ = 2)
    (t1Count : source.toList.count t1Source = 1)
    (t2Count : source.toList.count t2Source = 1)
    (t1At : sourceAt source.toList t1Owner = some t1Source)
    (xSecondAt : sourceAt source.toList xSecond = some sourceX)
    (t2At : sourceAt source.toList t2Owner = some t2Source)
    (t1BeforeX : t1Owner ≤ xSecond)
    (xBeforeT2 : xSecond ≤ t2Owner) :
    [sourceX, sourceY, sourceZ, t1Source, t2Source].Nodup ∧
      t1Owner < xSecond ∧ xSecond < t2Owner := by
  have xNeT1 : sourceX ≠ t1Source := by
    intro equality
    rw [← equality, xCount] at t1Count
    omega
  have yNeT1 : sourceY ≠ t1Source := by
    intro equality
    rw [← equality, yCount] at t1Count
    omega
  have zNeT1 : sourceZ ≠ t1Source := by
    intro equality
    rw [← equality, zCount] at t1Count
    omega
  have xNeT2 : sourceX ≠ t2Source := by
    intro equality
    rw [← equality, xCount] at t2Count
    omega
  have yNeT2 : sourceY ≠ t2Source := by
    intro equality
    rw [← equality, yCount] at t2Count
    omega
  have zNeT2 : sourceZ ≠ t2Source := by
    intro equality
    rw [← equality, zCount] at t2Count
    omega
  have t1Strict :
      t1Owner < xSecond :=
    sourceAt_lt_of_le_of_ne t1At xSecondAt
      (Ne.symm xNeT1) t1BeforeX
  have t2Strict :
      xSecond < t2Owner :=
    sourceAt_lt_of_le_of_ne xSecondAt t2At
      xNeT2 xBeforeT2
  have t1NeT2 : t1Source ≠ t2Source := by
    intro equality
    have t2AtT1 := t2At
    rw [← equality] at t2AtT1
    have ownersEqual :=
      sourceAt_eq_of_count_one t1At t2AtT1 t1Count
    omega
  have allNodup :
      [sourceX, sourceY, sourceZ, t1Source, t2Source].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or] at repeatedNodup ⊢
    rcases repeatedNodup with
      ⟨⟨xy, xz⟩, ⟨yz, _⟩⟩
    exact
      ⟨⟨xy, xz, xNeT1, xNeT2⟩,
        ⟨⟨yz, yNeT1, yNeT2⟩,
          ⟨⟨zNeT1, zNeT2⟩,
            ⟨t1NeT2, ⟨by simp, by simp⟩⟩⟩⟩⟩
  exact ⟨allNodup, t1Strict, t2Strict⟩

/-- Construct the distinguished `x`, `y`, and `z` preimages for a specified
Perkins block decomposition.  Keeping the block pair explicit lets this
layer share its occurrence owners with the independent-container layer. -/
theorem perkinsDistinguishedPreimages_of_shape
    {source target : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : source.bind substitution = target)
    (pattern : OccurrencePattern extra target.toList)
    {firstBlock secondBlock : List Nat}
    (firstPerm : firstBlock.Perm (middleVariables extra))
    (secondPerm : secondBlock.Perm (middleVariables extra))
    (targetShape :
      target.toList =
        [0, 1] ++ firstBlock ++ [0] ++ secondBlock ++ [1]) :
    PerkinsDistinguishedPreimages source substitution
      extra firstBlock secondBlock := by
  have xFirstShape :
      target.toList =
        [] ++ [0] ++ ([1] ++ firstBlock ++ [0] ++ secondBlock ++ [1]) := by
    simpa only [List.nil_append, List.append_assoc] using targetShape
  have xSecondShape :
      target.toList =
        ([0, 1] ++ firstBlock) ++ [0] ++ (secondBlock ++ [1]) := by
    simpa only [List.append_assoc] using targetShape
  have xPreimages :
      TwoBlockMarkerPreimages source substitution
        [] [0] ([0, 1] ++ firstBlock) [0] 0 :=
    selectTwoBlockMarkerPreimages mapped pattern
      xFirstShape xSecondShape (by simp) (by simp)
  have yFirstShape :
      target.toList =
        [0] ++ [1] ++ (firstBlock ++ [0] ++ secondBlock ++ [1]) := by
    simpa only [List.append_assoc] using targetShape
  have ySecondShape :
      target.toList =
        ([0, 1] ++ firstBlock ++ [0] ++ secondBlock) ++ [1] ++ [] := by
    simpa only [List.append_assoc, List.append_nil] using targetShape
  have yPreimages :
      TwoBlockMarkerPreimages source substitution
        [0] [1]
        ([0, 1] ++ firstBlock ++ [0] ++ secondBlock) [1] 1 :=
    selectTwoBlockMarkerPreimages mapped pattern
      yFirstShape ySecondShape (by simp) (by simp)
  refine ⟨xPreimages, yPreimages, ?_⟩
  intro z middleMember
  have firstMember : z ∈ firstBlock :=
    firstPerm.mem_iff.mpr middleMember
  have secondMember : z ∈ secondBlock :=
    secondPerm.mem_iff.mpr middleMember
  have firstShape :
      target.toList =
        [0, 1] ++ firstBlock ++ ([0] ++ secondBlock ++ [1]) := by
    simpa only [List.append_assoc] using targetShape
  have secondShape :
      target.toList =
        ([0, 1] ++ firstBlock ++ [0]) ++ secondBlock ++ [1] := by
    simpa only [List.append_assoc] using targetShape
  exact
    selectTwoBlockMarkerPreimages mapped pattern
      firstShape secondShape firstMember secondMember

/-- Source-variable preimages of both occurrences of target `x`, target `y`,
and every distinguished middle marker `z`, together with the exact `2occ`
linear/repeated alternative for each marker. -/
theorem selectPerkinsDistinguishedPreimages
    {source target : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : source.bind substitution = target)
    (pattern : OccurrencePattern extra target.toList) :
    ∃ firstBlock secondBlock,
      firstBlock.Perm (middleVariables extra) ∧
      secondBlock.Perm (middleVariables extra) ∧
      target.toList =
        [0, 1] ++ firstBlock ++ [0] ++ secondBlock ++ [1] ∧
      PerkinsDistinguishedPreimages source substitution
        extra firstBlock secondBlock := by
  rcases pattern with
    ⟨firstBlock, secondBlock, firstPerm, secondPerm, targetShape⟩
  have distinguished :=
    perkinsDistinguishedPreimages_of_shape mapped
      ⟨firstBlock, secondBlock, firstPerm, secondPerm, targetShape⟩
      firstPerm secondPerm targetShape
  exact
    ⟨firstBlock, secondBlock, firstPerm, secondPerm,
      targetShape, distinguished⟩

def SourceProjectionPreimageCase1
    (t1Owner zFirstOwner t2Owner zSecondOwner : Nat) : Prop :=
  t1Owner ≤ zFirstOwner ∧ t2Owner ≤ zSecondOwner

def SourceProjectionPreimageCase2
    (t1Owner zFirstOwner t2Owner zSecondOwner : Nat) : Prop :=
  zFirstOwner ≤ t1Owner ∧ t2Owner ≤ zSecondOwner

def SourceProjectionPreimageCase3
    (t1Owner zFirstOwner t2Owner zSecondOwner : Nat) : Prop :=
  t1Owner ≤ zFirstOwner ∧ zSecondOwner ≤ t2Owner

def SourceProjectionPreimageCase4
    (t1Owner zFirstOwner t2Owner zSecondOwner : Nat) : Prop :=
  zFirstOwner ≤ t1Owner ∧ zSecondOwner ≤ t2Owner

def keepFive
    (x y z t1 t2 letter : Nat) : Bool :=
  letter == x || letter == y || letter == z ||
    letter == t1 || letter == t2

private theorem keepFive_filter_length
    (source : List Nat) {x y z t1 t2 : Nat}
    (distinct : [x, y, z, t1, t2].Nodup) :
    (source.filter (keepFive x y z t1 t2)).length =
      source.count x + source.count y + source.count z +
        source.count t1 + source.count t2 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at distinct
  rcases distinct with
    ⟨⟨xy, xz, xt1, xt2⟩,
      ⟨⟨yz, yt1, yt2⟩, ⟨⟨zt1, zt2⟩, ⟨t1t2, _⟩⟩⟩⟩
  induction source with
  | nil => simp
  | cons head rest ih =>
      by_cases hx : head = x
      · subst head
        simp [keepFive, ih, xy, xz, xt1, xt2]
        omega
      · by_cases hy : head = y
        · subst head
          simp [keepFive, ih, Ne.symm xy, yz, yt1, yt2]
          omega
        · by_cases hz : head = z
          · subst head
            simp [keepFive, ih, Ne.symm xz, Ne.symm yz, zt1, zt2]
            omega
          · by_cases ht1 : head = t1
            · subst head
              simp [keepFive, ih, Ne.symm xt1, Ne.symm yt1,
                Ne.symm zt1, t1t2]
              omega
            · by_cases ht2 : head = t2
              · subst head
                simp [keepFive, ih, Ne.symm xt2, Ne.symm yt2,
                  Ne.symm zt2, Ne.symm t1t2]
                omega
              · simp [keepFive, hx, hy, hz, ht1, ht2, ih]

private theorem exactFiveVariableProjection_of_ownerSequence
    {source : Word Nat}
    {x y z t1 t2 : Nat}
    {firstOwner secondOwner thirdOwner fourthOwner
      fifthOwner sixthOwner seventhOwner eighthOwner : Nat}
    {firstLetter secondLetter thirdLetter fourthLetter
      fifthLetter sixthLetter seventhLetter eighthLetter : Nat}
    (variablesDistinct : [x, y, z, t1, t2].Nodup)
    (xCount : source.toList.count x = 2)
    (yCount : source.toList.count y = 2)
    (zCount : source.toList.count z = 2)
    (t1Count : source.toList.count t1 = 1)
    (t2Count : source.toList.count t2 = 1)
    (firstAt :
      sourceAt source.toList firstOwner = some firstLetter)
    (secondAt :
      sourceAt source.toList secondOwner = some secondLetter)
    (thirdAt :
      sourceAt source.toList thirdOwner = some thirdLetter)
    (fourthAt :
      sourceAt source.toList fourthOwner = some fourthLetter)
    (fifthAt :
      sourceAt source.toList fifthOwner = some fifthLetter)
    (sixthAt :
      sourceAt source.toList sixthOwner = some sixthLetter)
    (seventhAt :
      sourceAt source.toList seventhOwner = some seventhLetter)
    (eighthAt :
      sourceAt source.toList eighthOwner = some eighthLetter)
    (ownersOrdered :
      firstOwner < secondOwner ∧ secondOwner < thirdOwner ∧
      thirdOwner < fourthOwner ∧ fourthOwner < fifthOwner ∧
      fifthOwner < sixthOwner ∧ sixthOwner < seventhOwner ∧
      seventhOwner < eighthOwner)
    (selectedKept :
      [firstLetter, secondLetter, thirdLetter, fourthLetter,
          fifthLetter, sixthLetter, seventhLetter, eighthLetter].filter
          (keepFive x y z t1 t2) =
        [firstLetter, secondLetter, thirdLetter, fourthLetter,
          fifthLetter, sixthLetter, seventhLetter, eighthLetter]) :
    source.toList.filter (keepFive x y z t1 t2) =
      [firstLetter, secondLetter, thirdLetter, fourthLetter,
        fifthLetter, sixthLetter, seventhLetter, eighthLetter] := by
  let indices : List (Fin source.toList.length) :=
    [⟨firstOwner, sourceAt_some_index_lt firstAt⟩,
      ⟨secondOwner, sourceAt_some_index_lt secondAt⟩,
      ⟨thirdOwner, sourceAt_some_index_lt thirdAt⟩,
      ⟨fourthOwner, sourceAt_some_index_lt fourthAt⟩,
      ⟨fifthOwner, sourceAt_some_index_lt fifthAt⟩,
      ⟨sixthOwner, sourceAt_some_index_lt sixthAt⟩,
      ⟨seventhOwner, sourceAt_some_index_lt seventhAt⟩,
      ⟨eighthOwner, sourceAt_some_index_lt eighthAt⟩]
  have indicesOrdered : indices.Pairwise (· < ·) := by
    simp [indices, Fin.mk_lt_mk] <;> omega
  have selectedSublist :=
    List.map_getElem_sublist indicesOrdered
  have selectedValues :
      indices.map (fun index => source.toList[index]) =
        [firstLetter, secondLetter, thirdLetter, fourthLetter,
          fifthLetter, sixthLetter, seventhLetter, eighthLetter] := by
    simp only [indices, List.map_cons, List.map_nil]
    congr 1
    · exact getElem_eq_of_sourceAt firstAt
    congr 1
    · exact getElem_eq_of_sourceAt secondAt
    congr 1
    · exact getElem_eq_of_sourceAt thirdAt
    congr 1
    · exact getElem_eq_of_sourceAt fourthAt
    congr 1
    · exact getElem_eq_of_sourceAt fifthAt
    congr 1
    · exact getElem_eq_of_sourceAt sixthAt
    congr 1
    · exact getElem_eq_of_sourceAt seventhAt
    congr 1
    exact getElem_eq_of_sourceAt eighthAt
  rw [selectedValues] at selectedSublist
  have filteredSublist :=
    selectedSublist.filter (keepFive x y z t1 t2)
  rw [selectedKept] at filteredSublist
  have filteredLength :
      (source.toList.filter (keepFive x y z t1 t2)).length = 8 := by
    rw [keepFive_filter_length source.toList variablesDistinct,
      xCount, yCount, zCount, t1Count, t2Count]
  have equality :=
    filteredSublist.eq_of_length (by simpa using filteredLength.symm)
  exact equality.symm

/-- Exact source deletion in Sapir case 1. -/
theorem exactFiveVariableProjection_case1
    {source : Word Nat}
    {x y z t1 t2 : Nat}
    {xFirst yFirst zFirst xSecond zSecond ySecond
      t1Owner t2Owner : Nat}
    (variablesDistinct : [x, y, z, t1, t2].Nodup)
    (xCount : source.toList.count x = 2)
    (yCount : source.toList.count y = 2)
    (zCount : source.toList.count z = 2)
    (t1Count : source.toList.count t1 = 1)
    (t2Count : source.toList.count t2 = 1)
    (xFirstAt : sourceAt source.toList xFirst = some x)
    (yFirstAt : sourceAt source.toList yFirst = some y)
    (zFirstAt : sourceAt source.toList zFirst = some z)
    (xSecondAt : sourceAt source.toList xSecond = some x)
    (zSecondAt : sourceAt source.toList zSecond = some z)
    (ySecondAt : sourceAt source.toList ySecond = some y)
    (t1At : sourceAt source.toList t1Owner = some t1)
    (t2At : sourceAt source.toList t2Owner = some t2)
    (ownersOrdered :
      xFirst < yFirst ∧ yFirst < t1Owner ∧
      t1Owner < zFirst ∧ zFirst < xSecond ∧
      xSecond < t2Owner ∧ t2Owner < zSecond ∧
      zSecond < ySecond) :
    source.toList.filter (keepFive x y z t1 t2) =
      [x, y, t1, z, x, t2, z, y] := by
  apply exactFiveVariableProjection_of_ownerSequence
    variablesDistinct xCount yCount zCount t1Count t2Count
    xFirstAt yFirstAt t1At zFirstAt xSecondAt t2At zSecondAt ySecondAt
    ownersOrdered
  simp [keepFive]

/-- Exact source deletion in Sapir case 2. -/
theorem exactFiveVariableProjection_case2
    {source : Word Nat}
    {x y z t1 t2 : Nat}
    {xFirst yFirst zFirst xSecond zSecond ySecond
      t1Owner t2Owner : Nat}
    (variablesDistinct : [x, y, z, t1, t2].Nodup)
    (xCount : source.toList.count x = 2)
    (yCount : source.toList.count y = 2)
    (zCount : source.toList.count z = 2)
    (t1Count : source.toList.count t1 = 1)
    (t2Count : source.toList.count t2 = 1)
    (xFirstAt : sourceAt source.toList xFirst = some x)
    (yFirstAt : sourceAt source.toList yFirst = some y)
    (zFirstAt : sourceAt source.toList zFirst = some z)
    (xSecondAt : sourceAt source.toList xSecond = some x)
    (zSecondAt : sourceAt source.toList zSecond = some z)
    (ySecondAt : sourceAt source.toList ySecond = some y)
    (t1At : sourceAt source.toList t1Owner = some t1)
    (t2At : sourceAt source.toList t2Owner = some t2)
    (ownersOrdered :
      xFirst < yFirst ∧ yFirst < zFirst ∧
      zFirst < t1Owner ∧ t1Owner < xSecond ∧
      xSecond < t2Owner ∧ t2Owner < zSecond ∧
      zSecond < ySecond) :
    source.toList.filter (keepFive x y z t1 t2) =
      [x, y, z, t1, x, t2, z, y] := by
  apply exactFiveVariableProjection_of_ownerSequence
    variablesDistinct xCount yCount zCount t1Count t2Count
    xFirstAt yFirstAt zFirstAt t1At xSecondAt t2At zSecondAt ySecondAt
    ownersOrdered
  simp [keepFive]

/-- Exact source deletion in Sapir case 3. -/
theorem exactFiveVariableProjection_case3
    {source : Word Nat}
    {x y z t1 t2 : Nat}
    {xFirst yFirst zFirst xSecond zSecond ySecond
      t1Owner t2Owner : Nat}
    (variablesDistinct : [x, y, z, t1, t2].Nodup)
    (xCount : source.toList.count x = 2)
    (yCount : source.toList.count y = 2)
    (zCount : source.toList.count z = 2)
    (t1Count : source.toList.count t1 = 1)
    (t2Count : source.toList.count t2 = 1)
    (xFirstAt : sourceAt source.toList xFirst = some x)
    (yFirstAt : sourceAt source.toList yFirst = some y)
    (zFirstAt : sourceAt source.toList zFirst = some z)
    (xSecondAt : sourceAt source.toList xSecond = some x)
    (zSecondAt : sourceAt source.toList zSecond = some z)
    (ySecondAt : sourceAt source.toList ySecond = some y)
    (t1At : sourceAt source.toList t1Owner = some t1)
    (t2At : sourceAt source.toList t2Owner = some t2)
    (ownersOrdered :
      xFirst < yFirst ∧ yFirst < t1Owner ∧
      t1Owner < zFirst ∧ zFirst < xSecond ∧
      xSecond < zSecond ∧ zSecond < t2Owner ∧
      t2Owner < ySecond) :
    source.toList.filter (keepFive x y z t1 t2) =
      [x, y, t1, z, x, z, t2, y] := by
  apply exactFiveVariableProjection_of_ownerSequence
    variablesDistinct xCount yCount zCount t1Count t2Count
    xFirstAt yFirstAt t1At zFirstAt xSecondAt zSecondAt t2At ySecondAt
    ownersOrdered
  simp [keepFive]

/-- Exact source deletion in Sapir case 4. -/
theorem exactFiveVariableProjection_case4
    {source : Word Nat}
    {x y z t1 t2 : Nat}
    {xFirst yFirst zFirst xSecond zSecond ySecond
      t1Owner t2Owner : Nat}
    (variablesDistinct : [x, y, z, t1, t2].Nodup)
    (xCount : source.toList.count x = 2)
    (yCount : source.toList.count y = 2)
    (zCount : source.toList.count z = 2)
    (t1Count : source.toList.count t1 = 1)
    (t2Count : source.toList.count t2 = 1)
    (xFirstAt : sourceAt source.toList xFirst = some x)
    (yFirstAt : sourceAt source.toList yFirst = some y)
    (zFirstAt : sourceAt source.toList zFirst = some z)
    (xSecondAt : sourceAt source.toList xSecond = some x)
    (zSecondAt : sourceAt source.toList zSecond = some z)
    (ySecondAt : sourceAt source.toList ySecond = some y)
    (t1At : sourceAt source.toList t1Owner = some t1)
    (t2At : sourceAt source.toList t2Owner = some t2)
    (ownersOrdered :
      xFirst < yFirst ∧ yFirst < zFirst ∧
      zFirst < t1Owner ∧ t1Owner < xSecond ∧
      xSecond < zSecond ∧ zSecond < t2Owner ∧
      t2Owner < ySecond) :
    source.toList.filter (keepFive x y z t1 t2) =
      [x, y, z, t1, x, z, t2, y] := by
  apply exactFiveVariableProjection_of_ownerSequence
    variablesDistinct xCount yCount zCount t1Count t2Count
    xFirstAt yFirstAt zFirstAt t1At xSecondAt zSecondAt t2At ySecondAt
    ownersOrdered
  simp [keepFive]

theorem exactSourceProjectionCase1_of_orderedOwners
    {source : Word Nat}
    {xFirst yFirst zFirst xSecond zSecond ySecond
      t1Owner t2Owner : Nat}
    (xCount : source.toList.count 0 = 2)
    (yCount : source.toList.count 1 = 2)
    (zCount : source.toList.count 2 = 2)
    (t1Count : source.toList.count 3 = 1)
    (t2Count : source.toList.count 4 = 1)
    (xFirstAt : sourceAt source.toList xFirst = some 0)
    (yFirstAt : sourceAt source.toList yFirst = some 1)
    (zFirstAt : sourceAt source.toList zFirst = some 2)
    (xSecondAt : sourceAt source.toList xSecond = some 0)
    (zSecondAt : sourceAt source.toList zSecond = some 2)
    (ySecondAt : sourceAt source.toList ySecond = some 1)
    (t1At : sourceAt source.toList t1Owner = some 3)
    (t2At : sourceAt source.toList t2Owner = some 4)
    (ownersOrdered :
      xFirst < yFirst ∧ yFirst < t1Owner ∧
      t1Owner < zFirst ∧ zFirst < xSecond ∧
      xSecond < t2Owner ∧ t2Owner < zSecond ∧
      zSecond < ySecond) :
    source.toList.filter (keepFive 0 1 2 3 4) =
      sourceProjectionCase1.toList := by
  rw [sourceProjectionCase1_toList]
  exact
    exactFiveVariableProjection_case1 (by decide)
      xCount yCount zCount t1Count t2Count
      xFirstAt yFirstAt zFirstAt xSecondAt zSecondAt ySecondAt
      t1At t2At ownersOrdered

theorem exactSourceProjectionCase2_of_orderedOwners
    {source : Word Nat}
    {xFirst yFirst zFirst xSecond zSecond ySecond
      t1Owner t2Owner : Nat}
    (xCount : source.toList.count 0 = 2)
    (yCount : source.toList.count 1 = 2)
    (zCount : source.toList.count 2 = 2)
    (t1Count : source.toList.count 3 = 1)
    (t2Count : source.toList.count 4 = 1)
    (xFirstAt : sourceAt source.toList xFirst = some 0)
    (yFirstAt : sourceAt source.toList yFirst = some 1)
    (zFirstAt : sourceAt source.toList zFirst = some 2)
    (xSecondAt : sourceAt source.toList xSecond = some 0)
    (zSecondAt : sourceAt source.toList zSecond = some 2)
    (ySecondAt : sourceAt source.toList ySecond = some 1)
    (t1At : sourceAt source.toList t1Owner = some 3)
    (t2At : sourceAt source.toList t2Owner = some 4)
    (ownersOrdered :
      xFirst < yFirst ∧ yFirst < zFirst ∧
      zFirst < t1Owner ∧ t1Owner < xSecond ∧
      xSecond < t2Owner ∧ t2Owner < zSecond ∧
      zSecond < ySecond) :
    source.toList.filter (keepFive 0 1 2 3 4) =
      sourceProjectionCase2.toList := by
  rw [sourceProjectionCase2_toList]
  exact
    exactFiveVariableProjection_case2 (by decide)
      xCount yCount zCount t1Count t2Count
      xFirstAt yFirstAt zFirstAt xSecondAt zSecondAt ySecondAt
      t1At t2At ownersOrdered

theorem exactSourceProjectionCase3_of_orderedOwners
    {source : Word Nat}
    {xFirst yFirst zFirst xSecond zSecond ySecond
      t1Owner t2Owner : Nat}
    (xCount : source.toList.count 0 = 2)
    (yCount : source.toList.count 1 = 2)
    (zCount : source.toList.count 2 = 2)
    (t1Count : source.toList.count 3 = 1)
    (t2Count : source.toList.count 4 = 1)
    (xFirstAt : sourceAt source.toList xFirst = some 0)
    (yFirstAt : sourceAt source.toList yFirst = some 1)
    (zFirstAt : sourceAt source.toList zFirst = some 2)
    (xSecondAt : sourceAt source.toList xSecond = some 0)
    (zSecondAt : sourceAt source.toList zSecond = some 2)
    (ySecondAt : sourceAt source.toList ySecond = some 1)
    (t1At : sourceAt source.toList t1Owner = some 3)
    (t2At : sourceAt source.toList t2Owner = some 4)
    (ownersOrdered :
      xFirst < yFirst ∧ yFirst < t1Owner ∧
      t1Owner < zFirst ∧ zFirst < xSecond ∧
      xSecond < zSecond ∧ zSecond < t2Owner ∧
      t2Owner < ySecond) :
    source.toList.filter (keepFive 0 1 2 3 4) =
      sourceProjectionCase3.toList := by
  rw [sourceProjectionCase3_toList]
  exact
    exactFiveVariableProjection_case3 (by decide)
      xCount yCount zCount t1Count t2Count
      xFirstAt yFirstAt zFirstAt xSecondAt zSecondAt ySecondAt
      t1At t2At ownersOrdered

theorem exactSourceProjectionCase4_of_orderedOwners
    {source : Word Nat}
    {xFirst yFirst zFirst xSecond zSecond ySecond
      t1Owner t2Owner : Nat}
    (xCount : source.toList.count 0 = 2)
    (yCount : source.toList.count 1 = 2)
    (zCount : source.toList.count 2 = 2)
    (t1Count : source.toList.count 3 = 1)
    (t2Count : source.toList.count 4 = 1)
    (xFirstAt : sourceAt source.toList xFirst = some 0)
    (yFirstAt : sourceAt source.toList yFirst = some 1)
    (zFirstAt : sourceAt source.toList zFirst = some 2)
    (xSecondAt : sourceAt source.toList xSecond = some 0)
    (zSecondAt : sourceAt source.toList zSecond = some 2)
    (ySecondAt : sourceAt source.toList ySecond = some 1)
    (t1At : sourceAt source.toList t1Owner = some 3)
    (t2At : sourceAt source.toList t2Owner = some 4)
    (ownersOrdered :
      xFirst < yFirst ∧ yFirst < zFirst ∧
      zFirst < t1Owner ∧ t1Owner < xSecond ∧
      xSecond < zSecond ∧ zSecond < t2Owner ∧
      t2Owner < ySecond) :
    source.toList.filter (keepFive 0 1 2 3 4) =
      sourceProjectionCase4.toList := by
  rw [sourceProjectionCase4_toList]
  exact
    exactFiveVariableProjection_case4 (by decide)
      xCount yCount zCount t1Count t2Count
      xFirstAt yFirstAt zFirstAt xSecondAt zSecondAt ySecondAt
      t1At t2At ownersOrdered

/-- The four Sapir cases are the two independent order comparisons between
the block-local linear container and the occurrence preimage of `z`. -/
theorem sourceProjectionPreimage_four_cases
    (t1Owner zFirstOwner t2Owner zSecondOwner : Nat) :
    SourceProjectionPreimageCase1
        t1Owner zFirstOwner t2Owner zSecondOwner ∨
      SourceProjectionPreimageCase2
        t1Owner zFirstOwner t2Owner zSecondOwner ∨
      SourceProjectionPreimageCase3
        t1Owner zFirstOwner t2Owner zSecondOwner ∨
      SourceProjectionPreimageCase4
        t1Owner zFirstOwner t2Owner zSecondOwner := by
  rcases Nat.le_total t1Owner zFirstOwner with firstBefore | firstAfter
  · rcases Nat.le_total t2Owner zSecondOwner with
      secondBefore | secondAfter
    · exact Or.inl ⟨firstBefore, secondBefore⟩
    · exact Or.inr (Or.inr (Or.inl ⟨firstBefore, secondAfter⟩))
  · rcases Nat.le_total t2Owner zSecondOwner with
      secondBefore | secondAfter
    · exact Or.inr (Or.inl ⟨firstAfter, secondBefore⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨firstAfter, secondAfter⟩))

def IndependentBlockPreimageSelection
    (source : Word Nat) (substitution : Nat → Word Nat)
    (blockSize : Nat) (firstBlock secondBlock : List Nat) : Prop :=
  ∃ t1Owner t1Source t1First t1Second
      t2Owner t2Source t2First t2Second,
    sourceAt source.toList t1Owner = some t1Source ∧
    source.toList.count t1Source = 1 ∧
    t1First ≠ t1Second ∧
    BlockOccurrencePreimage source substitution
      [0, 1] firstBlock t1Owner t1First ∧
    BlockOccurrencePreimage source substitution
      [0, 1] firstBlock t1Owner t1Second ∧
    sourceAt source.toList t2Owner = some t2Source ∧
    source.toList.count t2Source = 1 ∧
    t2First ≠ t2Second ∧
    BlockOccurrencePreimage source substitution
      ([0, 1] ++ firstBlock ++ [0]) secondBlock
      t2Owner t2First ∧
    BlockOccurrencePreimage source substitution
      ([0, 1] ++ firstBlock ++ [0]) secondBlock
      t2Owner t2Second ∧
    ∀ z, z ∈ middleVariables blockSize →
      ∃ zFirstOwner zSecondOwner,
        BlockOccurrencePreimage source substitution
          [0, 1] firstBlock zFirstOwner z ∧
        BlockOccurrencePreimage source substitution
          ([0, 1] ++ firstBlock ++ [0]) secondBlock
          zSecondOwner z ∧
        (SourceProjectionPreimageCase1
              t1Owner zFirstOwner t2Owner zSecondOwner ∨
          SourceProjectionPreimageCase2
              t1Owner zFirstOwner t2Owner zSecondOwner ∨
          SourceProjectionPreimageCase3
              t1Owner zFirstOwner t2Owner zSecondOwner ∨
          SourceProjectionPreimageCase4
              t1Owner zFirstOwner t2Owner zSecondOwner)

/-- Select the two block-local linear containers once, then for every middle
marker `z` select its first- and reverse-block occurrence preimages and place
them in one of the four Sapir order cases. -/
theorem select_independent_block_preimage_cases
    {source target : Word Nat}
    (uses : WordUsesAtMost source (bound + 2))
    {substitution : Nat → Word Nat}
    (mapped : source.bind substitution = target)
    (pattern :
      OccurrencePattern (4 * bound + 7) target.toList)
    (semantic :
      (Identity.mk (obstruction bound).lhs target).SatisfiedBy
        table.semigroup) :
    ∃ firstBlock secondBlock,
      firstBlock.Perm (middleVariables (4 * bound + 7)) ∧
      secondBlock.Perm (middleVariables (4 * bound + 7)) ∧
      target.toList =
        [0, 1] ++ firstBlock ++ [0] ++ secondBlock ++ [1] ∧
      IndependentBlockPreimageSelection source substitution
        (4 * bound + 7) firstBlock secondBlock := by
  rcases
      select_two_block_local_linear_containers
        uses mapped pattern semantic with
    ⟨firstBlock, secondBlock, firstPerm, secondPerm, targetShape,
      firstContainer, secondContainer⟩
  rcases firstContainer with
    ⟨t1Owner, t1Source, t1First, t1Second,
      t1At, t1Linear, t1Different, t1FirstPreimage, t1SecondPreimage,
      _, _, _, _⟩
  rcases secondContainer with
    ⟨t2Owner, t2Source, t2First, t2Second,
      t2At, t2Linear, t2Different, t2FirstPreimage, t2SecondPreimage,
      _, _, _, _⟩
  refine
    ⟨firstBlock, secondBlock, firstPerm, secondPerm, targetShape, ?_⟩
  refine
    ⟨t1Owner, t1Source, t1First, t1Second,
      t2Owner, t2Source, t2First, t2Second,
      t1At, t1Linear, t1Different, t1FirstPreimage, t1SecondPreimage,
      t2At, t2Linear, t2Different, t2FirstPreimage, t2SecondPreimage,
      ?_⟩
  intro z middleMember
  have firstMember : z ∈ firstBlock :=
    firstPerm.mem_iff.mpr middleMember
  have secondMember : z ∈ secondBlock :=
    secondPerm.mem_iff.mpr middleMember
  have firstShape :
      target.toList =
        [0, 1] ++ firstBlock ++ ([0] ++ secondBlock ++ [1]) := by
    simpa only [List.append_assoc] using targetShape
  have secondShape :
      target.toList =
        ([0, 1] ++ firstBlock ++ [0]) ++ secondBlock ++ [1] := by
    simpa only [List.append_assoc] using targetShape
  rcases
      blockOccurrencePreimage_exists mapped firstShape firstMember with
    ⟨zFirstOwner, zFirstPreimage⟩
  rcases
      blockOccurrencePreimage_exists mapped secondShape secondMember with
    ⟨zSecondOwner, zSecondPreimage⟩
  exact
    ⟨zFirstOwner, zSecondOwner, zFirstPreimage, zSecondPreimage,
      sourceProjectionPreimage_four_cases
        t1Owner zFirstOwner t2Owner zSecondOwner⟩

def ContextPackedPreimageLayers
    (bound : Nat) (identity : Identity Nat)
    (pre post : List Nat) (substitution : Nat → Word Nat) : Prop :=
  ∃ packed : Identity Nat, ∃ augmented : Nat → Word Nat,
    packed.SatisfiedBy table.semigroup ∧
    packed.UsesAtMost (bound + 2) ∧
    packed.lhs.bind augmented =
      contextWord pre (identity.lhs.bind substitution) post ∧
    packed.rhs.bind augmented =
      contextWord pre (identity.rhs.bind substitution) post ∧
    ∃ firstBlock secondBlock,
      firstBlock.Perm (middleVariables (4 * bound + 7)) ∧
      secondBlock.Perm (middleVariables (4 * bound + 7)) ∧
      (contextWord pre
          (identity.lhs.bind substitution) post).toList =
        [0, 1] ++ firstBlock ++ [0] ++ secondBlock ++ [1] ∧
      IndependentBlockPreimageSelection packed.lhs augmented
        (4 * bound + 7) firstBlock secondBlock ∧
      PerkinsDistinguishedPreimages packed.lhs augmented
        (4 * bound + 7) firstBlock secondBlock

/-- Context packing followed by both occurrence-preimage layers. This is the
direct setup required by `PerkinsSemanticProjectionLemma`: `packed.lhs` maps
to the current Perkins-pattern word and `packed.rhs` maps to the next
contextual word. -/
theorem selectContextPackedPreimageLayers
    {identity : Identity Nat}
    (valid : identity.SatisfiedBy table.semigroup)
    (uses : identity.UsesAtMost bound)
    (pre post : List Nat) (substitution : Nat → Word Nat)
    (semantic :
      (Identity.mk (obstruction bound).lhs
        (contextWord pre (identity.lhs.bind substitution) post)).SatisfiedBy
          table.semigroup)
    (pattern :
      OccurrencePattern (4 * bound + 7)
        (contextWord pre
          (identity.lhs.bind substitution) post).toList) :
    ContextPackedPreimageLayers bound identity pre post substitution := by
  rcases
      exists_context_packing valid uses pre post substitution with
    ⟨packed, augmented, packedValid, packedUses,
      leftMapped, rightMapped⟩
  rcases packedUses with
    ⟨variables, variableBound, leftUses, rightUses⟩
  have packedUses' :
      packed.UsesAtMost (bound + 2) :=
    ⟨variables, variableBound, leftUses, rightUses⟩
  have sourceUses :
      WordUsesAtMost packed.lhs (bound + 2) :=
    ⟨variables, variableBound, leftUses⟩
  rcases
      select_independent_block_preimage_cases
        sourceUses leftMapped pattern semantic with
    ⟨firstBlock, secondBlock, firstPerm, secondPerm,
      targetShape, independent⟩
  have distinguished :
      PerkinsDistinguishedPreimages packed.lhs augmented
        (4 * bound + 7) firstBlock secondBlock :=
    perkinsDistinguishedPreimages_of_shape leftMapped pattern
      firstPerm secondPerm targetShape
  exact
    ⟨packed, augmented, packedValid, packedUses',
      leftMapped, rightMapped, firstBlock, secondBlock,
      firstPerm, secondPerm, targetShape, independent, distinguished⟩

private def swapNat (first second letter : Nat) : Nat :=
  if letter = first then second
  else if letter = second then first
  else letter

private theorem swapNat_involutive
    (first second letter : Nat) :
    swapNat first second (swapNat first second letter) = letter := by
  by_cases same : first = second
  · subst second
    by_cases selected : letter = first
    · subst letter
      simp [swapNat]
    · simp [swapNat, selected]
  · by_cases firstCase : letter = first
    · subst letter
      simp [swapNat, Ne.symm same]
    · by_cases secondCase : letter = second
      · subst letter
        simp [swapNat, Ne.symm same]
      · simp [swapNat, firstCase, secondCase]

private def yzt2Forward (letter : Nat) : Nat :=
  swapNat 0 4 (swapNat 0 2 (swapNat 0 1 letter))

private def yzt2Backward (letter : Nat) : Nat :=
  swapNat 0 1 (swapNat 0 2 (swapNat 0 4 letter))

private theorem yzt2_leftInverse (letter : Nat) :
    yzt2Backward (yzt2Forward letter) = letter := by
  simp only [yzt2Backward, yzt2Forward]
  rw [swapNat_involutive, swapNat_involutive, swapNat_involutive]

private theorem yzt2_rightInverse (letter : Nat) :
    yzt2Forward (yzt2Backward letter) = letter := by
  simp only [yzt2Backward, yzt2Forward]
  rw [swapNat_involutive, swapNat_involutive, swapNat_involutive]

private def yzt1Forward (letter : Nat) : Nat :=
  swapNat 0 3 (swapNat 0 2 (swapNat 0 1 letter))

private def yzt1Backward (letter : Nat) : Nat :=
  swapNat 0 1 (swapNat 0 2 (swapNat 0 3 letter))

private theorem yzt1_leftInverse (letter : Nat) :
    yzt1Backward (yzt1Forward letter) = letter := by
  simp only [yzt1Backward, yzt1Forward]
  rw [swapNat_involutive, swapNat_involutive, swapNat_involutive]

private theorem yzt1_rightInverse (letter : Nat) :
    yzt1Forward (yzt1Backward letter) = letter := by
  simp only [yzt1Backward, yzt1Forward]
  rw [swapNat_involutive, swapNat_involutive, swapNat_involutive]

private def xzt1Forward (letter : Nat) : Nat :=
  swapNat 1 3 (swapNat 1 2 letter)

private def xzt1Backward (letter : Nat) : Nat :=
  swapNat 1 2 (swapNat 1 3 letter)

private theorem xzt1_leftInverse (letter : Nat) :
    xzt1Backward (xzt1Forward letter) = letter := by
  simp only [xzt1Backward, xzt1Forward]
  rw [swapNat_involutive, swapNat_involutive]

private theorem xzt1_rightInverse (letter : Nat) :
    xzt1Forward (xzt1Backward letter) = letter := by
  simp only [xzt1Backward, xzt1Forward]
  rw [swapNat_involutive, swapNat_involutive]

private def twoSwapForward
    (first second third fourth letter : Nat) : Nat :=
  swapNat third fourth (swapNat first second letter)

private def twoSwapBackward
    (first second third fourth letter : Nat) : Nat :=
  swapNat first second (swapNat third fourth letter)

private theorem twoSwap_leftInverse
    (first second third fourth letter : Nat) :
    twoSwapBackward first second third fourth
        (twoSwapForward first second third fourth letter) =
      letter := by
  simp only [twoSwapBackward, twoSwapForward]
  rw [swapNat_involutive, swapNat_involutive]

private theorem twoSwap_rightInverse
    (first second third fourth letter : Nat) :
    twoSwapForward first second third fourth
        (twoSwapBackward first second third fourth letter) =
      letter := by
  simp only [twoSwapBackward, twoSwapForward]
  rw [swapNat_involutive, swapNat_involutive]

def yzt2IsotermWord : Word Nat :=
  ⟨1, [2, 4, 2, 1]⟩

def yzt1IsotermWord : Word Nat :=
  ⟨1, [2, 3, 2, 1]⟩

def xzt1IsotermWord : Word Nat :=
  ⟨0, [3, 2, 0, 2]⟩

def ytyIsotermWord : Word Nat :=
  ⟨1, [2, 1]⟩

def sandwichIsotermWord (repeated linear : Nat) : Word Nat :=
  ⟨repeated, [linear, repeated]⟩

def yt1yIsotermWord : Word Nat :=
  ⟨1, [3, 1]⟩

def yt2yIsotermWord : Word Nat :=
  ⟨1, [4, 1]⟩

def zt1zIsotermWord : Word Nat :=
  ⟨2, [3, 2]⟩

def zt2zIsotermWord : Word Nat :=
  ⟨2, [4, 2]⟩

def xt1xIsotermWord : Word Nat :=
  ⟨0, [3, 0]⟩

def xyIsotermWord : Word Nat :=
  ⟨0, [1]⟩

def xyxt2yIsotermWord : Word Nat :=
  ⟨0, [1, 0, 4, 1]⟩

theorem yzt2_isoterm :
    Isoterm table.semigroup yzt2IsotermWord := by
  have renamed :=
    Isoterm.map_bijection xytyx_isoterm
      yzt2Forward yzt2Backward yzt2_leftInverse yzt2_rightInverse
  have equality :
      xytyx.map yzt2Forward = yzt2IsotermWord := by
    decide
  rwa [equality] at renamed

theorem yzt1_isoterm :
    Isoterm table.semigroup yzt1IsotermWord := by
  have renamed :=
    Isoterm.map_bijection xytyx_isoterm
      yzt1Forward yzt1Backward yzt1_leftInverse yzt1_rightInverse
  have equality :
      xytyx.map yzt1Forward = yzt1IsotermWord := by
    decide
  rwa [equality] at renamed

theorem xzt1_isoterm :
    Isoterm table.semigroup xzt1IsotermWord := by
  have renamed :=
    Isoterm.map_bijection xtyxy_isoterm
      xzt1Forward xzt1Backward xzt1_leftInverse xzt1_rightInverse
  have equality :
      xtyxy.map xzt1Forward = xzt1IsotermWord := by
    decide
  rwa [equality] at renamed

theorem yty_isoterm :
    Isoterm table.semigroup ytyIsotermWord := by
  apply Isoterm.of_context xytyx_isoterm [0] [0]
  decide

private def sandwichMiddle (repeated : Nat) : Nat :=
  swapNat 1 repeated 2

private def sandwichForward
    (repeated linear letter : Nat) : Nat :=
  swapNat (sandwichMiddle repeated) linear
    (swapNat 1 repeated letter)

private def sandwichBackward
    (repeated linear letter : Nat) : Nat :=
  swapNat 1 repeated
    (swapNat (sandwichMiddle repeated) linear letter)

private theorem sandwich_leftInverse
    (repeated linear letter : Nat) :
    sandwichBackward repeated linear
        (sandwichForward repeated linear letter) =
      letter := by
  simp only [sandwichBackward, sandwichForward]
  rw [swapNat_involutive, swapNat_involutive]

private theorem sandwich_rightInverse
    (repeated linear letter : Nat) :
    sandwichForward repeated linear
        (sandwichBackward repeated linear letter) =
      letter := by
  simp only [sandwichBackward, sandwichForward]
  rw [swapNat_involutive, swapNat_involutive]

private theorem sandwichMiddle_ne_repeated (repeated : Nat) :
    sandwichMiddle repeated ≠ repeated := by
  by_cases repeatedOne : repeated = 1
  · subst repeated
    simp [sandwichMiddle, swapNat]
  · by_cases repeatedTwo : repeated = 2
    · subst repeated
      simp [sandwichMiddle, swapNat]
    · simp [sandwichMiddle, swapNat, repeatedOne, repeatedTwo,
        Ne.symm repeatedTwo]

private theorem sandwichForward_repeated
    {repeated linear : Nat} (different : repeated ≠ linear) :
    sandwichForward repeated linear 1 = repeated := by
  have middleDifferent := sandwichMiddle_ne_repeated repeated
  simp [sandwichForward, swapNat, different,
    Ne.symm middleDifferent]

private theorem sandwichForward_linear
    (repeated linear : Nat) :
    sandwichForward repeated linear 2 = linear := by
  simp [sandwichForward, sandwichMiddle, swapNat]

/-- Every two-variable sandwich `r l r` with `r ≠ l` is an isoterm for
`B₂¹`. -/
theorem sandwich_isoterm
    {repeated linear : Nat} (different : repeated ≠ linear) :
    Isoterm table.semigroup
      (sandwichIsotermWord repeated linear) := by
  have renamed :=
    Isoterm.map_bijection yty_isoterm
      (sandwichForward repeated linear)
      (sandwichBackward repeated linear)
      (sandwich_leftInverse repeated linear)
      (sandwich_rightInverse repeated linear)
  have equality :
      ytyIsotermWord.map (sandwichForward repeated linear) =
        sandwichIsotermWord repeated linear := by
    apply Word.toList_injective
    change
      [sandwichForward repeated linear 1,
        sandwichForward repeated linear 2,
        sandwichForward repeated linear 1] =
      [repeated, linear, repeated]
    simp [sandwichForward_repeated different,
      sandwichForward_linear]
  rwa [equality] at renamed

/-- An exact `r l r` source projection is stable without first assuming
singleton stability of the repeated variable. -/
theorem pairStable_of_sandwich_shape
    {source : Word Nat} {repeated linear : Nat}
    (different : repeated ≠ linear)
    (sourceShape :
      source.toList.filter (pairKeep repeated linear) =
        [repeated, linear, repeated]) :
    PairStable source repeated linear := by
  apply pairStable_of_filtered_isoterm
    (sandwich_isoterm different)
    (pairKeep repeated linear)
  · simpa [sandwichIsotermWord] using sourceShape
  · intro letter kept
    exact kept

/-- An exact `r l r` source projection bootstraps stability of the repeated
source variable. -/
theorem singletonStable_of_sandwich_shape
    {source : Word Nat} {repeated linear : Nat}
    (different : repeated ≠ linear)
    (sourceShape :
      source.toList.filter (pairKeep repeated linear) =
        [repeated, linear, repeated]) :
    SingletonStable source repeated :=
  singletonStable_of_pairStable
    (pairStable_of_sandwich_shape different sourceShape)

theorem yt1y_isoterm :
    Isoterm table.semigroup yt1yIsotermWord := by
  have renamed :=
    Isoterm.map_bijection yty_isoterm
      (swapNat 2 3) (swapNat 2 3)
      (swapNat_involutive 2 3) (swapNat_involutive 2 3)
  have equality :
      ytyIsotermWord.map (swapNat 2 3) = yt1yIsotermWord := by
    decide
  rwa [equality] at renamed

theorem yt2y_isoterm :
    Isoterm table.semigroup yt2yIsotermWord := by
  have renamed :=
    Isoterm.map_bijection yty_isoterm
      (swapNat 2 4) (swapNat 2 4)
      (swapNat_involutive 2 4) (swapNat_involutive 2 4)
  have equality :
      ytyIsotermWord.map (swapNat 2 4) = yt2yIsotermWord := by
    decide
  rwa [equality] at renamed

theorem zt1z_isoterm :
    Isoterm table.semigroup zt1zIsotermWord := by
  have renamed :=
    Isoterm.map_bijection yty_isoterm
      (twoSwapForward 1 2 1 3) (twoSwapBackward 1 2 1 3)
      (twoSwap_leftInverse 1 2 1 3)
      (twoSwap_rightInverse 1 2 1 3)
  have equality :
      ytyIsotermWord.map (twoSwapForward 1 2 1 3) =
        zt1zIsotermWord := by
    decide
  rwa [equality] at renamed

theorem zt2z_isoterm :
    Isoterm table.semigroup zt2zIsotermWord := by
  have renamed :=
    Isoterm.map_bijection yty_isoterm
      (twoSwapForward 1 2 1 4) (twoSwapBackward 1 2 1 4)
      (twoSwap_leftInverse 1 2 1 4)
      (twoSwap_rightInverse 1 2 1 4)
  have equality :
      ytyIsotermWord.map (twoSwapForward 1 2 1 4) =
        zt2zIsotermWord := by
    decide
  rwa [equality] at renamed

theorem xt1x_isoterm :
    Isoterm table.semigroup xt1xIsotermWord := by
  have renamed :=
    Isoterm.map_bijection yty_isoterm
      (twoSwapForward 0 1 2 3) (twoSwapBackward 0 1 2 3)
      (twoSwap_leftInverse 0 1 2 3)
      (twoSwap_rightInverse 0 1 2 3)
  have equality :
      ytyIsotermWord.map (twoSwapForward 0 1 2 3) =
        xt1xIsotermWord := by
    decide
  rwa [equality] at renamed

theorem xy_isoterm :
    Isoterm table.semigroup xyIsotermWord := by
  apply Isoterm.of_context xytyx_isoterm [] [2, 1, 0]
  decide

theorem xyxt2y_isoterm :
    Isoterm table.semigroup xyxt2yIsotermWord := by
  have reversed := Isoterm.reverse xtyxy_isoterm
  have renamed :=
    Isoterm.map_bijection reversed
      (twoSwapForward 0 1 2 4) (twoSwapBackward 0 1 2 4)
      (twoSwap_leftInverse 0 1 2 4)
      (twoSwap_rightInverse 0 1 2 4)
  have equality :
      xtyxy.reverse.map (twoSwapForward 0 1 2 4) =
        xyxt2yIsotermWord := by
    decide
  rwa [equality] at renamed

private theorem sourceProjectionCase1_xy_t2_isoterm :
    sourceProjectionCase1.toList.filter (keepTriple 0 1 4) =
      xyxt2yIsotermWord.toList := by
  decide

private theorem sourceProjectionCase2_xy_t2_isoterm :
    sourceProjectionCase2.toList.filter (keepTriple 0 1 4) =
      xyxt2yIsotermWord.toList := by
  decide

private theorem sourceProjectionCase3_xy_t2_isoterm :
    sourceProjectionCase3.toList.filter (keepTriple 0 1 4) =
      xyxt2yIsotermWord.toList := by
  decide

private theorem sourceProjectionCase4_xy_t2_isoterm :
    sourceProjectionCase4.toList.filter (keepTriple 0 1 4) =
      xyxt2yIsotermWord.toList := by
  decide

theorem sourceProjectionCase1_xy_stable :
    PairStable sourceProjectionCase1 0 1 := by
  apply pairStable_of_filtered_isoterm
    xyxt2y_isoterm (keepTriple 0 1 4)
  · exact sourceProjectionCase1_xy_t2_isoterm
  · intro letter kept
    simp [pairKeep] at kept
    rcases kept with rfl | rfl <;> simp [keepTriple]

theorem sourceProjectionCase2_xy_stable :
    PairStable sourceProjectionCase2 0 1 := by
  apply pairStable_of_filtered_isoterm
    xyxt2y_isoterm (keepTriple 0 1 4)
  · exact sourceProjectionCase2_xy_t2_isoterm
  · intro letter kept
    simp [pairKeep] at kept
    rcases kept with rfl | rfl <;> simp [keepTriple]

theorem sourceProjectionCase3_xy_stable :
    PairStable sourceProjectionCase3 0 1 := by
  apply pairStable_of_filtered_isoterm
    xyxt2y_isoterm (keepTriple 0 1 4)
  · exact sourceProjectionCase3_xy_t2_isoterm
  · intro letter kept
    simp [pairKeep] at kept
    rcases kept with rfl | rfl <;> simp [keepTriple]

theorem sourceProjectionCase4_xy_stable :
    PairStable sourceProjectionCase4 0 1 := by
  apply pairStable_of_filtered_isoterm
    xyxt2y_isoterm (keepTriple 0 1 4)
  · exact sourceProjectionCase4_xy_t2_isoterm
  · intro letter kept
    simp [pairKeep] at kept
    rcases kept with rfl | rfl <;> simp [keepTriple]

theorem sourceProjectionCase3_xt2_stable :
    PairStable sourceProjectionCase3 0 4 := by
  apply pairStable_of_filtered_isoterm
    xyxt2y_isoterm (keepTriple 0 1 4)
  · exact sourceProjectionCase3_xy_t2_isoterm
  · intro letter kept
    simp [pairKeep] at kept
    rcases kept with rfl | rfl <;> simp [keepTriple]

theorem sourceProjectionCase4_xt2_stable :
    PairStable sourceProjectionCase4 0 4 := by
  apply pairStable_of_filtered_isoterm
    xyxt2y_isoterm (keepTriple 0 1 4)
  · exact sourceProjectionCase4_xy_t2_isoterm
  · intro letter kept
    simp [pairKeep] at kept
    rcases kept with rfl | rfl <;> simp [keepTriple]

theorem sourceProjectionCase3_t2_stable :
    SingletonStable sourceProjectionCase3 4 :=
  singletonStable_of_pairStable_right sourceProjectionCase3_xt2_stable

theorem sourceProjectionCase4_t2_stable :
    SingletonStable sourceProjectionCase4 4 :=
  singletonStable_of_pairStable_right sourceProjectionCase4_xt2_stable

theorem sourceProjectionCase1_yz_stable :
    PairStable sourceProjectionCase1 1 2 := by
  apply pairStable_of_filtered_isoterm
    yzt2_isoterm (keepTriple 1 2 4)
  · decide
  · intro letter kept
    simp [pairKeep] at kept
    rcases kept with rfl | rfl <;> simp [keepTriple]

theorem sourceProjectionCase1_xz_stable :
    PairStable sourceProjectionCase1 0 2 := by
  apply pairStable_of_filtered_isoterm
    xzt1_isoterm (keepTriple 0 2 3)
  · decide
  · intro letter kept
    simp [pairKeep] at kept
    rcases kept with rfl | rfl <;> simp [keepTriple]

theorem sourceProjectionCase1_xt1_stable :
    PairStable sourceProjectionCase1 0 3 := by
  apply pairStable_of_filtered_isoterm
    xzt1_isoterm (keepTriple 0 2 3)
  · decide
  · intro letter kept
    simp [pairKeep] at kept
    rcases kept with rfl | rfl <;> simp [keepTriple]

theorem sourceProjectionCase1_zt1_stable :
    PairStable sourceProjectionCase1 2 3 := by
  apply pairStable_of_filtered_isoterm
    xzt1_isoterm (keepTriple 0 2 3)
  · decide
  · intro letter kept
    simp [pairKeep] at kept
    rcases kept with rfl | rfl <;> simp [keepTriple]

theorem sourceProjectionCase1_yt2_stable :
    PairStable sourceProjectionCase1 1 4 := by
  apply pairStable_of_filtered_isoterm
    yzt2_isoterm (keepTriple 1 2 4)
  · decide
  · intro letter kept
    simp [pairKeep] at kept
    rcases kept with rfl | rfl <;> simp [keepTriple]

theorem sourceProjectionCase1_zt2_stable :
    PairStable sourceProjectionCase1 2 4 := by
  apply pairStable_of_filtered_isoterm
    yzt2_isoterm (keepTriple 1 2 4)
  · decide
  · intro letter kept
    simp [pairKeep] at kept
    rcases kept with rfl | rfl <;> simp [keepTriple]

theorem sourceProjectionCase1_yt1_stable :
    PairStable sourceProjectionCase1 1 3 := by
  apply pairStable_of_filtered_isoterm
    yt1y_isoterm (pairKeep 1 3)
  · decide
  · exact fun _ kept => kept

theorem sourceProjectionCase1_x_stable :
    SingletonStable sourceProjectionCase1 0 :=
  singletonStable_of_pairStable sourceProjectionCase1_xz_stable

theorem sourceProjectionCase1_y_stable :
    SingletonStable sourceProjectionCase1 1 :=
  singletonStable_of_pairStable sourceProjectionCase1_yz_stable

theorem sourceProjectionCase1_z_stable :
    SingletonStable sourceProjectionCase1 2 :=
  singletonStable_of_pairStable_right sourceProjectionCase1_xz_stable

theorem sourceProjectionCase1_t1_stable :
    SingletonStable sourceProjectionCase1 3 :=
  singletonStable_of_pairStable_right sourceProjectionCase1_xt1_stable

theorem sourceProjectionCase1_t2_stable :
    SingletonStable sourceProjectionCase1 4 :=
  singletonStable_of_pairStable_right sourceProjectionCase1_yt2_stable

theorem sourceProjectionCase2_yz_stable :
    PairStable sourceProjectionCase2 1 2 := by
  apply pairStable_of_filtered_isoterm
    yzt2_isoterm (keepTriple 1 2 4)
  · decide
  · intro letter kept
    simp [pairKeep] at kept
    rcases kept with rfl | rfl <;> simp [keepTriple]

theorem sourceProjectionCase2_x_stable :
    SingletonStable sourceProjectionCase2 0 :=
  singletonStable_of_pairStable sourceProjectionCase2_xy_stable

theorem sourceProjectionCase2_z_stable :
    SingletonStable sourceProjectionCase2 2 :=
  singletonStable_of_pairStable_right sourceProjectionCase2_yz_stable

theorem sourceProjectionCase2_xz_stable :
    PairStable sourceProjectionCase2 0 2 := by
  apply pairStable_of_xyxy_shape
    (source := sourceProjectionCase2)
    (first := 0) (second := 2)
  · decide
  · exact sourceProjectionCase2_x_stable
  · exact sourceProjectionCase2_z_stable
  · decide

theorem sourceProjectionCase2_yt2_stable :
    PairStable sourceProjectionCase2 1 4 := by
  apply pairStable_of_filtered_isoterm
    yzt2_isoterm (keepTriple 1 2 4)
  · decide
  · intro letter kept
    simp [pairKeep] at kept
    rcases kept with rfl | rfl <;> simp [keepTriple]

theorem sourceProjectionCase2_zt2_stable :
    PairStable sourceProjectionCase2 2 4 := by
  apply pairStable_of_filtered_isoterm
    yzt2_isoterm (keepTriple 1 2 4)
  · decide
  · intro letter kept
    simp [pairKeep] at kept
    rcases kept with rfl | rfl <;> simp [keepTriple]

theorem sourceProjectionCase2_zt1_stable :
    PairStable sourceProjectionCase2 2 3 := by
  apply pairStable_of_filtered_isoterm
    zt1z_isoterm (pairKeep 2 3)
  · decide
  · exact fun _ kept => kept

theorem sourceProjectionCase2_xt1_stable :
    PairStable sourceProjectionCase2 0 3 := by
  apply pairStable_of_filtered_isoterm
    xt1x_isoterm (pairKeep 0 3)
  · decide
  · exact fun _ kept => kept

theorem sourceProjectionCase3_xz_stable :
    PairStable sourceProjectionCase3 0 2 := by
  apply pairStable_of_filtered_isoterm
    xzt1_isoterm (keepTriple 0 2 3)
  · decide
  · intro letter kept
    simp [pairKeep] at kept
    rcases kept with rfl | rfl <;> simp [keepTriple]

theorem sourceProjectionCase3_xt1_stable :
    PairStable sourceProjectionCase3 0 3 := by
  apply pairStable_of_filtered_isoterm
    xzt1_isoterm (keepTriple 0 2 3)
  · decide
  · intro letter kept
    simp [pairKeep] at kept
    rcases kept with rfl | rfl <;> simp [keepTriple]

theorem sourceProjectionCase3_zt1_stable :
    PairStable sourceProjectionCase3 2 3 := by
  apply pairStable_of_filtered_isoterm
    xzt1_isoterm (keepTriple 0 2 3)
  · decide
  · intro letter kept
    simp [pairKeep] at kept
    rcases kept with rfl | rfl <;> simp [keepTriple]

theorem sourceProjectionCase3_yt1_stable :
    PairStable sourceProjectionCase3 1 3 := by
  apply pairStable_of_filtered_isoterm
    yt1y_isoterm (pairKeep 1 3)
  · decide
  · exact fun _ kept => kept

theorem sourceProjectionCase3_yt2_stable :
    PairStable sourceProjectionCase3 1 4 := by
  apply pairStable_of_filtered_isoterm
    yt2y_isoterm (pairKeep 1 4)
  · decide
  · exact fun _ kept => kept

theorem sourceProjectionCase3_z_stable :
    SingletonStable sourceProjectionCase3 2 :=
  singletonStable_of_pairStable_right sourceProjectionCase3_xz_stable

theorem sourceProjectionCase3_zt2_stable :
    PairStable sourceProjectionCase3 2 4 := by
  apply pairStable_of_xxt_shape
    (source := sourceProjectionCase3)
    (repeated := 2) (linear := 4)
  · decide
  · exact sourceProjectionCase3_z_stable
  · exact sourceProjectionCase3_t2_stable
  · decide

private def keepFour
    (first second third fourth letter : Nat) : Bool :=
  letter == first || letter == second ||
    letter == third || letter == fourth

private theorem filter_keepFour_pair
    (letters : List Nat)
    (first second third fourth pairFirst pairSecond : Nat)
    (pairFirstMember :
      pairFirst = first ∨ pairFirst = second ∨
        pairFirst = third ∨ pairFirst = fourth)
    (pairSecondMember :
      pairSecond = first ∨ pairSecond = second ∨
        pairSecond = third ∨ pairSecond = fourth) :
    (letters.filter
        (keepFour first second third fourth)).filter
          (pairKeep pairFirst pairSecond) =
      letters.filter (pairKeep pairFirst pairSecond) := by
  apply filter_filter_of_implies
  intro letter kept
  simp [pairKeep] at kept
  rcases kept with rfl | rfl
  · simpa [keepFour, or_assoc] using pairFirstMember
  · simpa [keepFour, or_assoc] using pairSecondMember

private theorem canonical_case3_separator_merge
    (letters : List Nat)
    (domain :
      ∀ letter, letter ∈ letters →
        letter = 1 ∨ letter = 2 ∨ letter = 3 ∨ letter = 4)
    (yT1 :
      letters.filter (pairKeep 1 3) = [1, 3, 1])
    (zT1 :
      letters.filter (pairKeep 2 3) = [3, 2, 2])
    (zT2 :
      letters.filter (pairKeep 2 4) = [2, 2, 4])
    (yT2 :
      letters.filter (pairKeep 1 4) = [1, 4, 1]) :
    letters = [1, 3, 2, 2, 4, 1] := by
  rcases letters with _ | ⟨first, letters⟩
  · simp at yT1
  have firstDomain := domain first (by simp)
  rcases firstDomain with rfl | rfl | rfl | rfl <;>
    simp [pairKeep] at yT1 zT1 zT2 yT2 ⊢
  rcases letters with _ | ⟨second, letters⟩
  · simp at yT1
  have secondDomain := domain second (by simp)
  rcases secondDomain with rfl | rfl | rfl | rfl <;>
    simp [pairKeep] at yT1 zT1 zT2 yT2 ⊢
  rcases letters with _ | ⟨third, letters⟩
  · simp at zT1
  have thirdDomain := domain third (by simp)
  rcases thirdDomain with rfl | rfl | rfl | rfl <;>
    simp [pairKeep] at yT1 zT1 zT2 yT2 ⊢
  rcases letters with _ | ⟨fourth, letters⟩
  · simp at zT1
  have fourthDomain := domain fourth (by simp)
  rcases fourthDomain with rfl | rfl | rfl | rfl <;>
    simp [pairKeep] at yT1 zT1 zT2 yT2 ⊢
  rcases letters with _ | ⟨fifth, letters⟩
  · simp at zT2
  have fifthDomain := domain fifth (by simp)
  rcases fifthDomain with rfl | rfl | rfl | rfl <;>
    simp [pairKeep] at yT1 zT1 zT2 yT2 ⊢
  rcases letters with _ | ⟨sixth, letters⟩
  · simp at yT1
  have sixthDomain := domain sixth (by simp)
  rcases sixthDomain with rfl | rfl | rfl | rfl <;>
    simp [pairKeep] at yT1 zT1 zT2 yT2 ⊢
  cases letters with
  | nil => rfl
  | cons seventh letters =>
      have seventhDomain := domain seventh (by simp)
      rcases seventhDomain with rfl | rfl | rfl | rfl <;>
        simp [pairKeep] at yT1 zT1 zT2 yT2

theorem sourceProjectionCase3_yz_stable :
    PairStable sourceProjectionCase3 1 2 := by
  intro other valid
  let selected :=
    other.toList.filter (keepFour 1 2 3 4)
  have selectedDomain :
      ∀ letter, letter ∈ selected →
        letter = 1 ∨ letter = 2 ∨ letter = 3 ∨ letter = 4 := by
    intro letter member
    have kept := (List.mem_filter.mp member).2
    simpa [keepFour, or_assoc] using kept
  have yT1 :
      selected.filter (pairKeep 1 3) = [1, 3, 1] := by
    rw [filter_keepFour_pair other.toList 1 2 3 4 1 3
      (by simp) (by simp)]
    rw [← sourceProjectionCase3_yt1_stable other valid]
    decide
  have zT1 :
      selected.filter (pairKeep 2 3) = [3, 2, 2] := by
    rw [filter_keepFour_pair other.toList 1 2 3 4 2 3
      (by simp) (by simp)]
    rw [← sourceProjectionCase3_zt1_stable other valid]
    decide
  have zT2 :
      selected.filter (pairKeep 2 4) = [2, 2, 4] := by
    rw [filter_keepFour_pair other.toList 1 2 3 4 2 4
      (by simp) (by simp)]
    rw [← sourceProjectionCase3_zt2_stable other valid]
    decide
  have yT2 :
      selected.filter (pairKeep 1 4) = [1, 4, 1] := by
    rw [filter_keepFour_pair other.toList 1 2 3 4 1 4
      (by simp) (by simp)]
    rw [← sourceProjectionCase3_yt2_stable other valid]
    decide
  have selectedShape :
      selected = [1, 3, 2, 2, 4, 1] :=
    canonical_case3_separator_merge selected selectedDomain
      yT1 zT1 zT2 yT2
  calc
    sourceProjectionCase3.toList.filter (pairKeep 1 2) =
        [1, 2, 2, 1] := by decide
    _ =
        selected.filter (pairKeep 1 2) := by
          rw [selectedShape]
          decide
    _ = other.toList.filter (pairKeep 1 2) :=
      filter_keepFour_pair other.toList 1 2 3 4 1 2
        (by simp) (by simp)

theorem sourceProjectionCase4_yz_stable :
    PairStable sourceProjectionCase4 1 2 := by
  apply pairStable_of_filtered_isoterm
    yzt1_isoterm (keepTriple 1 2 3)
  · decide
  · intro letter kept
    simp [pairKeep] at kept
    rcases kept with rfl | rfl <;> simp [keepTriple]

theorem sourceProjectionCase4_x_stable :
    SingletonStable sourceProjectionCase4 0 :=
  singletonStable_of_pairStable sourceProjectionCase4_xy_stable

theorem sourceProjectionCase4_z_stable :
    SingletonStable sourceProjectionCase4 2 :=
  singletonStable_of_pairStable_right sourceProjectionCase4_yz_stable

theorem sourceProjectionCase4_xz_stable :
    PairStable sourceProjectionCase4 0 2 := by
  apply pairStable_of_xyxy_shape
    (source := sourceProjectionCase4)
    (first := 0) (second := 2)
  · decide
  · exact sourceProjectionCase4_x_stable
  · exact sourceProjectionCase4_z_stable
  · decide

theorem sourceProjectionCase4_yt1_stable :
    PairStable sourceProjectionCase4 1 3 := by
  apply pairStable_of_filtered_isoterm
    yzt1_isoterm (keepTriple 1 2 3)
  · decide
  · intro letter kept
    simp [pairKeep] at kept
    rcases kept with rfl | rfl <;> simp [keepTriple]

theorem sourceProjectionCase4_zt1_stable :
    PairStable sourceProjectionCase4 2 3 := by
  apply pairStable_of_filtered_isoterm
    yzt1_isoterm (keepTriple 1 2 3)
  · decide
  · intro letter kept
    simp [pairKeep] at kept
    rcases kept with rfl | rfl <;> simp [keepTriple]

theorem sourceProjectionCase4_xt1_stable :
    PairStable sourceProjectionCase4 0 3 := by
  apply pairStable_of_filtered_isoterm
    xt1x_isoterm (pairKeep 0 3)
  · decide
  · exact fun _ kept => kept

theorem sourceProjectionCase4_yt2_stable :
    PairStable sourceProjectionCase4 1 4 := by
  apply pairStable_of_filtered_isoterm
    yt2y_isoterm (pairKeep 1 4)
  · decide
  · exact fun _ kept => kept

def TripleStable
    (source : Word Nat) (first second third : Nat) : Prop :=
  ∀ other,
    (Identity.mk source other).SatisfiedBy table.semigroup →
    source.toList.filter (keepTriple first second third) =
      other.toList.filter (keepTriple first second third)

private theorem filter_keepTriple_pair
    (letters : List Nat)
    (first second third pairFirst pairSecond : Nat)
    (pairFirstMember :
      pairFirst = first ∨ pairFirst = second ∨ pairFirst = third)
    (pairSecondMember :
      pairSecond = first ∨ pairSecond = second ∨ pairSecond = third) :
    (letters.filter
        (keepTriple first second third)).filter
          (pairKeep pairFirst pairSecond) =
      letters.filter (pairKeep pairFirst pairSecond) := by
  apply filter_filter_of_implies
  intro letter kept
  simp [pairKeep] at kept
  rcases kept with rfl | rfl
  · simpa [keepTriple, or_assoc] using pairFirstMember
  · simpa [keepTriple, or_assoc] using pairSecondMember

private theorem canonical_xyz_merge
    (letters : List Nat)
    (domain :
      ∀ letter, letter ∈ letters →
        letter = 0 ∨ letter = 1 ∨ letter = 2)
    (xy : letters.filter (pairKeep 0 1) = [0, 1, 0, 1])
    (xz : letters.filter (pairKeep 0 2) = [0, 2, 0, 2])
    (yz : letters.filter (pairKeep 1 2) = [1, 2, 2, 1]) :
    letters = [0, 1, 2, 0, 2, 1] := by
  rcases letters with _ | ⟨first, letters⟩
  · simp at xy
  have firstDomain := domain first (by simp)
  rcases firstDomain with rfl | rfl | rfl <;>
    simp [pairKeep] at xy xz yz ⊢
  rcases letters with _ | ⟨second, letters⟩
  · simp at xy
  have secondDomain := domain second (by simp)
  rcases secondDomain with rfl | rfl | rfl <;>
    simp [pairKeep] at xy xz yz ⊢
  rcases letters with _ | ⟨third, letters⟩
  · simp at yz
  have thirdDomain := domain third (by simp)
  rcases thirdDomain with rfl | rfl | rfl <;>
    simp [pairKeep] at xy xz yz ⊢
  rcases letters with _ | ⟨fourth, letters⟩
  · simp at xy
  have fourthDomain := domain fourth (by simp)
  rcases fourthDomain with rfl | rfl | rfl <;>
    simp [pairKeep] at xy xz yz ⊢
  rcases letters with _ | ⟨fifth, letters⟩
  · simp at xz
  have fifthDomain := domain fifth (by simp)
  rcases fifthDomain with rfl | rfl | rfl <;>
    simp [pairKeep] at xy xz yz ⊢
  rcases letters with _ | ⟨sixth, letters⟩
  · simp at xy
  have sixthDomain := domain sixth (by simp)
  rcases sixthDomain with rfl | rfl | rfl <;>
    simp [pairKeep] at xy xz yz ⊢
  cases letters with
  | nil => rfl
  | cons seventh letters =>
      have seventhDomain := domain seventh (by simp)
      rcases seventhDomain with rfl | rfl | rfl <;>
        simp [pairKeep] at xy xz yz

theorem tripleStable_of_perkins_pair_stability
    {source : Word Nat}
    (xyStable : PairStable source 0 1)
    (xzStable : PairStable source 0 2)
    (yzStable : PairStable source 1 2)
    (sourceShape :
      source.toList.filter (keepTriple 0 1 2) =
        [0, 1, 2, 0, 2, 1]) :
    TripleStable source 0 1 2 := by
  intro other valid
  let selected :=
    other.toList.filter (keepTriple 0 1 2)
  have selectedDomain :
      ∀ letter, letter ∈ selected →
        letter = 0 ∨ letter = 1 ∨ letter = 2 := by
    intro letter member
    have kept := (List.mem_filter.mp member).2
    simpa [keepTriple, or_assoc] using kept
  have sourceXY :
      source.toList.filter (pairKeep 0 1) = [0, 1, 0, 1] := by
    calc
      source.toList.filter (pairKeep 0 1) =
          (source.toList.filter
            (keepTriple 0 1 2)).filter (pairKeep 0 1) := by
        symm
        exact filter_keepTriple_pair source.toList 0 1 2 0 1
          (by simp) (by simp)
      _ = [0, 1, 0, 1] := by rw [sourceShape]; decide
  have sourceXZ :
      source.toList.filter (pairKeep 0 2) = [0, 2, 0, 2] := by
    calc
      source.toList.filter (pairKeep 0 2) =
          (source.toList.filter
            (keepTriple 0 1 2)).filter (pairKeep 0 2) := by
        symm
        exact filter_keepTriple_pair source.toList 0 1 2 0 2
          (by simp) (by simp)
      _ = [0, 2, 0, 2] := by rw [sourceShape]; decide
  have sourceYZ :
      source.toList.filter (pairKeep 1 2) = [1, 2, 2, 1] := by
    calc
      source.toList.filter (pairKeep 1 2) =
          (source.toList.filter
            (keepTriple 0 1 2)).filter (pairKeep 1 2) := by
        symm
        exact filter_keepTriple_pair source.toList 0 1 2 1 2
          (by simp) (by simp)
      _ = [1, 2, 2, 1] := by rw [sourceShape]; decide
  have selectedXY :
      selected.filter (pairKeep 0 1) = [0, 1, 0, 1] := by
    rw [filter_keepTriple_pair other.toList 0 1 2 0 1
      (by simp) (by simp)]
    rw [← xyStable other valid]
    exact sourceXY
  have selectedXZ :
      selected.filter (pairKeep 0 2) = [0, 2, 0, 2] := by
    rw [filter_keepTriple_pair other.toList 0 1 2 0 2
      (by simp) (by simp)]
    rw [← xzStable other valid]
    exact sourceXZ
  have selectedYZ :
      selected.filter (pairKeep 1 2) = [1, 2, 2, 1] := by
    rw [filter_keepTriple_pair other.toList 0 1 2 1 2
      (by simp) (by simp)]
    rw [← yzStable other valid]
    exact sourceYZ
  have selectedShape :
      selected = [0, 1, 2, 0, 2, 1] :=
    canonical_xyz_merge selected selectedDomain
      selectedXY selectedXZ selectedYZ
  exact sourceShape.trans selectedShape.symm

theorem sourceProjectionCase1_xyz_stable :
    TripleStable sourceProjectionCase1 0 1 2 :=
  tripleStable_of_perkins_pair_stability
    sourceProjectionCase1_xy_stable
    sourceProjectionCase1_xz_stable
    sourceProjectionCase1_yz_stable
    (by decide)

theorem sourceProjectionCase2_xyz_stable :
    TripleStable sourceProjectionCase2 0 1 2 :=
  tripleStable_of_perkins_pair_stability
    sourceProjectionCase2_xy_stable
    sourceProjectionCase2_xz_stable
    sourceProjectionCase2_yz_stable
    (by decide)

theorem sourceProjectionCase3_xyz_stable :
    TripleStable sourceProjectionCase3 0 1 2 :=
  tripleStable_of_perkins_pair_stability
    sourceProjectionCase3_xy_stable
    sourceProjectionCase3_xz_stable
    sourceProjectionCase3_yz_stable
    (by decide)

theorem sourceProjectionCase4_xyz_stable :
    TripleStable sourceProjectionCase4 0 1 2 :=
  tripleStable_of_perkins_pair_stability
    sourceProjectionCase4_xy_stable
    sourceProjectionCase4_xz_stable
    sourceProjectionCase4_yz_stable
    (by decide)

private theorem Word.toList_map
    (word : Word Nat) (rename : Nat → Nat) :
    (word.map rename).toList = word.toList.map rename := by
  cases word
  rfl

private theorem Word.map_leftInverse_on_support
    (word : Word Nat) (forward backward : Nat → Nat)
    (leftInverse :
      ∀ letter, letter ∈ word.toList →
        backward (forward letter) = letter) :
    (word.map forward).map backward = word := by
  apply Word.toList_injective
  rw [Word.toList_map, Word.toList_map, List.map_map]
  calc
    word.toList.map (backward ∘ forward) =
        word.toList.map id := by
      apply List.map_congr_left
      intro letter member
      exact leftInverse letter member
    _ = word.toList := List.map_id word.toList

/-- An isoterm may be renamed by any map admitting a left inverse on the
finite support of the word.  A right inverse on an arbitrary valid right
side follows from support preservation. -/
theorem Isoterm.map_leftInverse_on_support
    {word : Word Nat}
    (isoterm : Isoterm table.semigroup word)
    (forward backward : Nat → Nat)
    (leftInverse :
      ∀ letter, letter ∈ word.toList →
        backward (forward letter) = letter) :
    Isoterm table.semigroup (word.map forward) := by
  intro other valid
  have sourceBack :
      (word.map forward).map backward = word :=
    Word.map_leftInverse_on_support word forward backward leftInverse
  have pulledValid :
      (Identity.mk word (other.map backward)).SatisfiedBy
        table.semigroup := by
    intro valuation
    have equality :=
      valid (fun letter => valuation (backward letter))
    calc
      table.semigroup.eval valuation word =
          table.semigroup.eval
            (fun letter => valuation (backward letter))
            (word.map forward) := by
        have sourceBackEval :=
          congrArg (table.semigroup.eval valuation) sourceBack
        exact sourceBackEval.symm.trans
          (Semigroup.eval_map table.semigroup valuation backward
            (word.map forward))
      _ =
          table.semigroup.eval
            (fun letter => valuation (backward letter))
            other :=
        equality
      _ = table.semigroup.eval valuation
          (other.map backward) := by
        rw [Semigroup.eval_map]
  have pulledEquality :=
    isoterm (other.map backward) pulledValid
  have otherRightInverse :
      ∀ letter, letter ∈ other.toList →
        forward (backward letter) = letter := by
    intro letter member
    have sourceMember :
        letter ∈ (word.map forward).toList :=
      (valid_identity_support_iff valid letter).mpr member
    rw [Word.toList_map] at sourceMember
    rcases List.mem_map.mp sourceMember with
      ⟨sourceLetter, sourceLetterMember, sourceEquality⟩
    subst letter
    rw [leftInverse sourceLetter sourceLetterMember]
  have otherBackForward :
      (other.map backward).map forward = other := by
    apply Word.toList_injective
    rw [Word.toList_map, Word.toList_map, List.map_map]
    calc
      other.toList.map (forward ∘ backward) =
          other.toList.map id := by
        apply List.map_congr_left
        intro letter member
        exact otherRightInverse letter member
      _ = other.toList := List.map_id other.toList
  have mapped :=
    congrArg (fun current => current.map forward) pulledEquality
  change
    (other.map backward).map forward =
      word.map forward at mapped
  exact otherBackForward.symm.trans mapped

private def threeLabelForward
    (first second third letter : Nat) : Nat :=
  if letter = 0 then first
  else if letter = 1 then second
  else if letter = 2 then third
  else letter

private def threeLabelBackward
    (first second third letter : Nat) : Nat :=
  if letter = first then 0
  else if letter = second then 1
  else if letter = third then 2
  else letter

private theorem threeLabel_leftInverse_on_canonical
    {first second third letter : Nat}
    (distinct : [first, second, third].Nodup)
    (canonical :
      letter = 0 ∨ letter = 1 ∨ letter = 2) :
    threeLabelBackward first second third
        (threeLabelForward first second third letter) =
      letter := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at distinct
  rcases distinct with
    ⟨⟨firstSecond, firstThird⟩, ⟨secondThird, _⟩⟩
  rcases canonical with rfl | rfl | rfl <;>
    simp [threeLabelForward, threeLabelBackward,
      firstSecond, firstThird, secondThird,
      Ne.symm firstSecond, Ne.symm firstThird,
      Ne.symm secondThird]

private theorem xytyx_member_canonical
    {letter : Nat} (member : letter ∈ xytyx.toList) :
    letter = 0 ∨ letter = 1 ∨ letter = 2 := by
  simp only [xytyx, Word.toList, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> simp

private theorem xtyxy_member_canonical
    {letter : Nat} (member : letter ∈ xtyxy.toList) :
    letter = 0 ∨ letter = 1 ∨ letter = 2 := by
  simp only [xtyxy, Word.toList, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> simp

def palindromicTripleIsotermWord
    (outer inner separator : Nat) : Word Nat :=
  ⟨outer, [inner, separator, inner, outer]⟩

def alternatingTripleIsotermWord
    (first second separator : Nat) : Word Nat :=
  ⟨first, [separator, second, first, second]⟩

/-- Every injective renaming of Perkins's isoterm `x y t y x` is an
isoterm. -/
theorem palindromicTriple_isoterm
    {outer inner separator : Nat}
    (distinct : [outer, inner, separator].Nodup) :
    Isoterm table.semigroup
      (palindromicTripleIsotermWord outer inner separator) := by
  let forward :=
    threeLabelForward outer inner separator
  let backward :=
    threeLabelBackward outer inner separator
  have renamed :=
    Isoterm.map_leftInverse_on_support xytyx_isoterm
      forward backward
      (fun letter member =>
        threeLabel_leftInverse_on_canonical distinct
          (xytyx_member_canonical member))
  have mappedWord :
      xytyx.map forward =
        palindromicTripleIsotermWord
          outer inner separator := by
    apply Word.toList_injective
    rw [Word.toList_map]
    change
      [forward 0, forward 1, forward 2, forward 1, forward 0] =
        [outer, inner, separator, inner, outer]
    simp [forward, threeLabelForward]
  rwa [mappedWord] at renamed

/-- Every injective renaming of Perkins's isoterm `x t y x y` is an
isoterm. -/
theorem alternatingTriple_isoterm
    {first second separator : Nat}
    (distinct : [first, second, separator].Nodup) :
    Isoterm table.semigroup
      (alternatingTripleIsotermWord first second separator) := by
  let forward :=
    threeLabelForward first second separator
  let backward :=
    threeLabelBackward first second separator
  have renamed :=
    Isoterm.map_leftInverse_on_support xtyxy_isoterm
      forward backward
      (fun letter member =>
        threeLabel_leftInverse_on_canonical distinct
          (xtyxy_member_canonical member))
  have mappedWord :
      xtyxy.map forward =
        alternatingTripleIsotermWord
          first second separator := by
    apply Word.toList_injective
    rw [Word.toList_map]
    change
      [forward 0, forward 2, forward 1, forward 0, forward 1] =
        [first, separator, second, first, second]
    simp [forward, threeLabelForward]
  rwa [mappedWord] at renamed

private theorem filter_map_transport
    (letters : List Nat) (rename : Nat → Nat)
    (sourceKeep targetKeep : Nat → Bool)
    (commutes :
      ∀ letter, letter ∈ letters →
        targetKeep (rename letter) = sourceKeep letter) :
    (letters.map rename).filter targetKeep =
      (letters.filter sourceKeep).map rename := by
  induction letters with
  | nil => rfl
  | cons letter rest ih =>
      have headCommutes := commutes letter (by simp)
      have tailCommutes :
          ∀ value, value ∈ rest →
            targetKeep (rename value) = sourceKeep value := by
        intro value member
        exact commutes value (by simp [member])
      simp only [List.map_cons, List.filter_cons]
      rw [headCommutes, ih tailCommutes]
      cases kept : sourceKeep letter <;> simp [kept]

private theorem map_filter_inverse_transport
    (letters : List Nat) (forward backward : Nat → Nat)
    (sourceKeep targetKeep : Nat → Bool)
    (rightInverse :
      ∀ letter, letter ∈ letters →
        forward (backward letter) = letter)
    (commutes :
      ∀ letter, letter ∈ letters →
        sourceKeep (backward letter) = targetKeep letter) :
    ((letters.map backward).filter sourceKeep).map forward =
      letters.filter targetKeep := by
  induction letters with
  | nil => rfl
  | cons letter rest ih =>
      have headInverse := rightInverse letter (by simp)
      have headCommutes := commutes letter (by simp)
      have tailInverse :
          ∀ value, value ∈ rest →
            forward (backward value) = value := by
        intro value member
        exact rightInverse value (by simp [member])
      have tailCommutes :
          ∀ value, value ∈ rest →
            sourceKeep (backward value) = targetKeep value := by
        intro value member
        exact commutes value (by simp [member])
      simp only [List.map_cons, List.filter_cons]
      rw [headCommutes]
      cases kept : targetKeep letter
      · simpa [kept] using ih tailInverse tailCommutes
      · simp [kept, headInverse, ih tailInverse tailCommutes]

private theorem keepTriple_map_eq_of_injective_on_support
    {source : Word Nat} {first second third : Nat}
    (firstMember : first ∈ source.toList)
    (secondMember : second ∈ source.toList)
    (thirdMember : third ∈ source.toList)
    (forward : Nat → Nat)
    (injective :
      ∀ left, left ∈ source.toList →
        ∀ right, right ∈ source.toList →
          forward left = forward right → left = right) :
    ∀ letter, letter ∈ source.toList →
      keepTriple (forward first) (forward second) (forward third)
          (forward letter) =
        keepTriple first second third letter := by
  intro letter member
  by_cases firstCase : letter = first
  · subst letter
    simp [keepTriple]
  by_cases secondCase : letter = second
  · subst letter
    simp [keepTriple]
  by_cases thirdCase : letter = third
  · subst letter
    simp [keepTriple]
  have forwardFirst : forward letter ≠ forward first := by
    intro equality
    exact firstCase
      (injective letter member first firstMember equality)
  have forwardSecond : forward letter ≠ forward second := by
    intro equality
    exact secondCase
      (injective letter member second secondMember equality)
  have forwardThird : forward letter ≠ forward third := by
    intro equality
    exact thirdCase
      (injective letter member third thirdMember equality)
  have sourceFirst : (letter == first) = false := by
    simp [firstCase]
  have sourceSecond : (letter == second) = false := by
    simp [secondCase]
  have sourceThird : (letter == third) = false := by
    simp [thirdCase]
  have targetFirst :
      (forward letter == forward first) = false := by
    simp [forwardFirst]
  have targetSecond :
      (forward letter == forward second) = false := by
    simp [forwardSecond]
  have targetThird :
      (forward letter == forward third) = false := by
    simp [forwardThird]
  simp [keepTriple, sourceFirst, sourceSecond, sourceThird,
    targetFirst, targetSecond, targetThird]

/-- Triple stability is invariant under a renaming that is injective on the
finite support of the source word.  A total inverse is only required to be a
left inverse there; support preservation of valid identities supplies the
right-inverse facts needed on an arbitrary right side. -/
theorem TripleStable.map_injective_on_support
    {source : Word Nat} {first second third : Nat}
    (stable : TripleStable source first second third)
    (firstMember : first ∈ source.toList)
    (secondMember : second ∈ source.toList)
    (thirdMember : third ∈ source.toList)
    (forward backward : Nat → Nat)
    (leftInverse :
      ∀ letter, letter ∈ source.toList →
        backward (forward letter) = letter)
    (injective :
      ∀ left, left ∈ source.toList →
        ∀ right, right ∈ source.toList →
          forward left = forward right → left = right) :
    TripleStable (source.map forward)
      (forward first) (forward second) (forward third) := by
  intro other valid
  have sourceBack :
      (source.map forward).map backward = source :=
    Word.map_leftInverse_on_support source forward backward leftInverse
  have pulledValid :
      (Identity.mk source (other.map backward)).SatisfiedBy
        table.semigroup := by
    intro valuation
    have equality :=
      valid (fun letter => valuation (backward letter))
    calc
      table.semigroup.eval valuation source =
          table.semigroup.eval
            (fun letter => valuation (backward letter))
            (source.map forward) := by
        have sourceBackEval :=
          congrArg (table.semigroup.eval valuation) sourceBack
        exact sourceBackEval.symm.trans
          (Semigroup.eval_map table.semigroup valuation backward
            (source.map forward))
      _ =
          table.semigroup.eval
            (fun letter => valuation (backward letter)) other :=
        equality
      _ = table.semigroup.eval valuation (other.map backward) := by
        rw [Semigroup.eval_map]
  have pulledStable := stable (other.map backward) pulledValid
  let sourceKeep := keepTriple first second third
  let targetKeep :=
    keepTriple (forward first) (forward second) (forward third)
  have sourceCommutes :
      ∀ letter, letter ∈ source.toList →
        targetKeep (forward letter) = sourceKeep letter := by
    exact
      keepTriple_map_eq_of_injective_on_support
        firstMember secondMember thirdMember forward injective
  have sourceFilter :
      (source.map forward).toList.filter targetKeep =
        (source.toList.filter sourceKeep).map forward := by
    rw [Word.toList_map]
    exact
      filter_map_transport source.toList forward
        sourceKeep targetKeep sourceCommutes
  have otherRightInverse :
      ∀ letter, letter ∈ other.toList →
        forward (backward letter) = letter := by
    intro letter member
    have leftMember :
        letter ∈ (source.map forward).toList :=
      (valid_identity_support_iff valid letter).mpr member
    rw [Word.toList_map] at leftMember
    rcases List.mem_map.mp leftMember with
      ⟨sourceLetter, sourceMember, sourceEquality⟩
    subst letter
    rw [leftInverse sourceLetter sourceMember]
  have otherCommutes :
      ∀ letter, letter ∈ other.toList →
        sourceKeep (backward letter) = targetKeep letter := by
    intro letter member
    have leftMember :
        letter ∈ (source.map forward).toList :=
      (valid_identity_support_iff valid letter).mpr member
    rw [Word.toList_map] at leftMember
    rcases List.mem_map.mp leftMember with
      ⟨sourceLetter, sourceMember, sourceEquality⟩
    subst letter
    rw [leftInverse sourceLetter sourceMember]
    exact (sourceCommutes sourceLetter sourceMember).symm
  have otherFilter :
      (((other.map backward).toList.filter sourceKeep).map forward) =
        other.toList.filter targetKeep := by
    rw [Word.toList_map]
    exact
      map_filter_inverse_transport other.toList forward backward
        sourceKeep targetKeep otherRightInverse otherCommutes
  rw [sourceFilter, pulledStable, otherFilter]

private def fiveLabelForward
    (x y z t1 t2 letter : Nat) : Nat :=
  if letter = 0 then x
  else if letter = 1 then y
  else if letter = 2 then z
  else if letter = 3 then t1
  else if letter = 4 then t2
  else letter

private def fiveLabelBackward
    (x y z t1 t2 letter : Nat) : Nat :=
  if letter = x then 0
  else if letter = y then 1
  else if letter = z then 2
  else if letter = t1 then 3
  else if letter = t2 then 4
  else letter

private theorem fiveLabel_leftInverse_on_canonical
    {x y z t1 t2 letter : Nat}
    (distinct : [x, y, z, t1, t2].Nodup)
    (canonical : letter = 0 ∨ letter = 1 ∨ letter = 2 ∨
      letter = 3 ∨ letter = 4) :
    fiveLabelBackward x y z t1 t2
        (fiveLabelForward x y z t1 t2 letter) =
      letter := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at distinct
  rcases distinct with
    ⟨⟨xy, xz, xt1, xt2⟩,
      ⟨⟨yz, yt1, yt2⟩, ⟨⟨zt1, zt2⟩, ⟨t1t2, _⟩⟩⟩⟩
  rcases canonical with rfl | rfl | rfl | rfl | rfl <;>
    simp [fiveLabelForward, fiveLabelBackward, xy, xz, xt1, xt2,
      yz, yt1, yt2, zt1, zt2, t1t2,
      Ne.symm xy, Ne.symm xz, Ne.symm xt1, Ne.symm xt2,
      Ne.symm yz, Ne.symm yt1, Ne.symm yt2,
      Ne.symm zt1, Ne.symm zt2, Ne.symm t1t2]

private theorem fiveLabelForward_injective_on_canonical
    {x y z t1 t2 left right : Nat}
    (distinct : [x, y, z, t1, t2].Nodup)
    (leftCanonical : left = 0 ∨ left = 1 ∨ left = 2 ∨
      left = 3 ∨ left = 4)
    (rightCanonical : right = 0 ∨ right = 1 ∨ right = 2 ∨
      right = 3 ∨ right = 4)
    (equality :
      fiveLabelForward x y z t1 t2 left =
        fiveLabelForward x y z t1 t2 right) :
    left = right := by
  have leftInverse :=
    fiveLabel_leftInverse_on_canonical distinct leftCanonical
  have rightInverse :=
    fiveLabel_leftInverse_on_canonical distinct rightCanonical
  rw [← leftInverse, equality, rightInverse]

private theorem canonical_member_of_case1
    {letter : Nat} (member : letter ∈ sourceProjectionCase1.toList) :
    letter = 0 ∨ letter = 1 ∨ letter = 2 ∨
      letter = 3 ∨ letter = 4 := by
  simp [sourceProjectionCase1_toList] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp

private theorem canonical_member_of_case2
    {letter : Nat} (member : letter ∈ sourceProjectionCase2.toList) :
    letter = 0 ∨ letter = 1 ∨ letter = 2 ∨
      letter = 3 ∨ letter = 4 := by
  simp [sourceProjectionCase2_toList] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp

private theorem canonical_member_of_case3
    {letter : Nat} (member : letter ∈ sourceProjectionCase3.toList) :
    letter = 0 ∨ letter = 1 ∨ letter = 2 ∨
      letter = 3 ∨ letter = 4 := by
  simp [sourceProjectionCase3_toList] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp

private theorem canonical_member_of_case4
    {letter : Nat} (member : letter ∈ sourceProjectionCase4.toList) :
    letter = 0 ∨ letter = 1 ∨ letter = 2 ∨
      letter = 3 ∨ letter = 4 := by
  simp [sourceProjectionCase4_toList] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp

theorem sourceProjectionCase1_renamed_xyz_stable
    {x y z t1 t2 : Nat}
    (distinct : [x, y, z, t1, t2].Nodup) :
    TripleStable
      (sourceProjectionCase1.map
        (fiveLabelForward x y z t1 t2)) x y z := by
  have renamed :=
    sourceProjectionCase1_xyz_stable.map_injective_on_support
      (by decide) (by decide) (by decide)
      (fiveLabelForward x y z t1 t2)
      (fiveLabelBackward x y z t1 t2)
      (fun letter member =>
        fiveLabel_leftInverse_on_canonical distinct
          (canonical_member_of_case1 member))
      (fun left leftMember right rightMember equality =>
        fiveLabelForward_injective_on_canonical distinct
          (canonical_member_of_case1 leftMember)
          (canonical_member_of_case1 rightMember) equality)
  simpa [fiveLabelForward] using renamed

theorem sourceProjectionCase2_renamed_xyz_stable
    {x y z t1 t2 : Nat}
    (distinct : [x, y, z, t1, t2].Nodup) :
    TripleStable
      (sourceProjectionCase2.map
        (fiveLabelForward x y z t1 t2)) x y z := by
  have renamed :=
    sourceProjectionCase2_xyz_stable.map_injective_on_support
      (by decide) (by decide) (by decide)
      (fiveLabelForward x y z t1 t2)
      (fiveLabelBackward x y z t1 t2)
      (fun letter member =>
        fiveLabel_leftInverse_on_canonical distinct
          (canonical_member_of_case2 member))
      (fun left leftMember right rightMember equality =>
        fiveLabelForward_injective_on_canonical distinct
          (canonical_member_of_case2 leftMember)
          (canonical_member_of_case2 rightMember) equality)
  simpa [fiveLabelForward] using renamed

theorem sourceProjectionCase3_renamed_xyz_stable
    {x y z t1 t2 : Nat}
    (distinct : [x, y, z, t1, t2].Nodup) :
    TripleStable
      (sourceProjectionCase3.map
        (fiveLabelForward x y z t1 t2)) x y z := by
  have renamed :=
    sourceProjectionCase3_xyz_stable.map_injective_on_support
      (by decide) (by decide) (by decide)
      (fiveLabelForward x y z t1 t2)
      (fiveLabelBackward x y z t1 t2)
      (fun letter member =>
        fiveLabel_leftInverse_on_canonical distinct
          (canonical_member_of_case3 member))
      (fun left leftMember right rightMember equality =>
        fiveLabelForward_injective_on_canonical distinct
          (canonical_member_of_case3 leftMember)
          (canonical_member_of_case3 rightMember) equality)
  simpa [fiveLabelForward] using renamed

theorem sourceProjectionCase4_renamed_xyz_stable
    {x y z t1 t2 : Nat}
    (distinct : [x, y, z, t1, t2].Nodup) :
    TripleStable
      (sourceProjectionCase4.map
        (fiveLabelForward x y z t1 t2)) x y z := by
  have renamed :=
    sourceProjectionCase4_xyz_stable.map_injective_on_support
      (by decide) (by decide) (by decide)
      (fiveLabelForward x y z t1 t2)
      (fiveLabelBackward x y z t1 t2)
      (fun letter member =>
        fiveLabel_leftInverse_on_canonical distinct
          (canonical_member_of_case4 member))
      (fun left leftMember right rightMember equality =>
        fiveLabelForward_injective_on_canonical distinct
          (canonical_member_of_case4 leftMember)
          (canonical_member_of_case4 rightMember) equality)
  simpa [fiveLabelForward] using renamed

/-- A stable selected projection can be lifted through a larger exact
deletion of the source word.  This is the stability analogue of
`stable_filter_of_filtered_isoterm`; the larger projected word need not be
an isoterm. -/
theorem stable_filter_of_filtered_stability
    {source projected : Word Nat}
    (large small : Nat → Bool)
    (projectedStable :
      ∀ other,
        (Identity.mk projected other).SatisfiedBy table.semigroup →
        projected.toList.filter small =
          other.toList.filter small)
    (sourceFiltered :
      source.toList.filter large = projected.toList)
    (contained :
      ∀ letter, small letter = true → large letter = true) :
    ∀ other,
      (Identity.mk source other).SatisfiedBy table.semigroup →
      source.toList.filter small =
        other.toList.filter small := by
  intro other valid
  have headInSourceFiltered :
      projected.head ∈ source.toList.filter large := by
    rw [sourceFiltered]
    simp [Word.toList]
  have headKept : large projected.head = true :=
    (List.mem_filter.mp headInSourceFiltered).2
  have headInSource : projected.head ∈ source.toList :=
    (List.mem_filter.mp headInSourceFiltered).1
  have headInOther :=
    (valid_identity_support_iff valid projected.head).mp headInSource
  have headInOtherFiltered :
      projected.head ∈ other.toList.filter large :=
    List.mem_filter.mpr ⟨headInOther, headKept⟩
  cases filtered : other.toList.filter large with
  | nil => simp [filtered] at headInOtherFiltered
  | cons head tail =>
      let filteredWord : Word Nat := ⟨head, tail⟩
      have filteredWordList :
          filteredWord.toList = other.toList.filter large := by
        rw [filtered]
        rfl
      have filteredValid :
          (Identity.mk projected filteredWord).SatisfiedBy
            table.semigroup := by
        intro valuation
        rw [← evalList_toList, ← evalList_toList, filteredWordList,
          ← sourceFiltered]
        exact filtered_eval_equal valid large valuation
      have projectedEquality :=
        projectedStable filteredWord filteredValid
      calc
        source.toList.filter small =
            (source.toList.filter large).filter small := by
          symm
          exact
            filter_filter_of_implies source.toList
              small large contained
        _ = projected.toList.filter small := by rw [sourceFiltered]
        _ = filteredWord.toList.filter small := projectedEquality
        _ = (other.toList.filter large).filter small := by
          rw [filteredWordList]
        _ = other.toList.filter small :=
          filter_filter_of_implies other.toList small large contained

private theorem keepTriple_contained_keepFive
    (x y z t1 t2 letter : Nat)
    (kept : keepTriple x y z letter = true) :
    keepFive x y z t1 t2 letter = true := by
  simp [keepTriple, or_assoc] at kept
  simp [keepFive, or_assoc]
  rcases kept with hx | hy | hz
  · exact Or.inl hx
  · exact Or.inr (Or.inl hy)
  · exact Or.inr (Or.inr (Or.inl hz))

private theorem sourceProjectionCase1_renamed_toList
    (x y z t1 t2 : Nat) :
    (sourceProjectionCase1.map
        (fiveLabelForward x y z t1 t2)).toList =
      [x, y, t1, z, x, t2, z, y] := by
  simp [Word.toList_map, sourceProjectionCase1_toList,
    fiveLabelForward]

private theorem sourceProjectionCase2_renamed_toList
    (x y z t1 t2 : Nat) :
    (sourceProjectionCase2.map
        (fiveLabelForward x y z t1 t2)).toList =
      [x, y, z, t1, x, t2, z, y] := by
  simp [Word.toList_map, sourceProjectionCase2_toList,
    fiveLabelForward]

private theorem sourceProjectionCase3_renamed_toList
    (x y z t1 t2 : Nat) :
    (sourceProjectionCase3.map
        (fiveLabelForward x y z t1 t2)).toList =
      [x, y, t1, z, x, z, t2, y] := by
  simp [Word.toList_map, sourceProjectionCase3_toList,
    fiveLabelForward]

private theorem sourceProjectionCase4_renamed_toList
    (x y z t1 t2 : Nat) :
    (sourceProjectionCase4.map
        (fiveLabelForward x y z t1 t2)).toList =
      [x, y, z, t1, x, z, t2, y] := by
  simp [Word.toList_map, sourceProjectionCase4_toList,
    fiveLabelForward]

theorem tripleStable_of_sourceProjectionCase1
    {source : Word Nat} {x y z t1 t2 : Nat}
    (distinct : [x, y, z, t1, t2].Nodup)
    (sourceFiltered :
      source.toList.filter (keepFive x y z t1 t2) =
        [x, y, t1, z, x, t2, z, y]) :
    TripleStable source x y z := by
  apply stable_filter_of_filtered_stability
    (projected :=
      sourceProjectionCase1.map
        (fiveLabelForward x y z t1 t2))
    (keepFive x y z t1 t2) (keepTriple x y z)
  · exact sourceProjectionCase1_renamed_xyz_stable distinct
  · rw [sourceProjectionCase1_renamed_toList]
    exact sourceFiltered
  · exact keepTriple_contained_keepFive x y z t1 t2

theorem tripleStable_of_sourceProjectionCase2
    {source : Word Nat} {x y z t1 t2 : Nat}
    (distinct : [x, y, z, t1, t2].Nodup)
    (sourceFiltered :
      source.toList.filter (keepFive x y z t1 t2) =
        [x, y, z, t1, x, t2, z, y]) :
    TripleStable source x y z := by
  apply stable_filter_of_filtered_stability
    (projected :=
      sourceProjectionCase2.map
        (fiveLabelForward x y z t1 t2))
    (keepFive x y z t1 t2) (keepTriple x y z)
  · exact sourceProjectionCase2_renamed_xyz_stable distinct
  · rw [sourceProjectionCase2_renamed_toList]
    exact sourceFiltered
  · exact keepTriple_contained_keepFive x y z t1 t2

theorem tripleStable_of_sourceProjectionCase3
    {source : Word Nat} {x y z t1 t2 : Nat}
    (distinct : [x, y, z, t1, t2].Nodup)
    (sourceFiltered :
      source.toList.filter (keepFive x y z t1 t2) =
        [x, y, t1, z, x, z, t2, y]) :
    TripleStable source x y z := by
  apply stable_filter_of_filtered_stability
    (projected :=
      sourceProjectionCase3.map
        (fiveLabelForward x y z t1 t2))
    (keepFive x y z t1 t2) (keepTriple x y z)
  · exact sourceProjectionCase3_renamed_xyz_stable distinct
  · rw [sourceProjectionCase3_renamed_toList]
    exact sourceFiltered
  · exact keepTriple_contained_keepFive x y z t1 t2

theorem tripleStable_of_sourceProjectionCase4
    {source : Word Nat} {x y z t1 t2 : Nat}
    (distinct : [x, y, z, t1, t2].Nodup)
    (sourceFiltered :
      source.toList.filter (keepFive x y z t1 t2) =
        [x, y, z, t1, x, z, t2, y]) :
    TripleStable source x y z := by
  apply stable_filter_of_filtered_stability
    (projected :=
      sourceProjectionCase4.map
        (fiveLabelForward x y z t1 t2))
    (keepFive x y z t1 t2) (keepTriple x y z)
  · exact sourceProjectionCase4_renamed_xyz_stable distinct
  · rw [sourceProjectionCase4_renamed_toList]
    exact sourceFiltered
  · exact keepTriple_contained_keepFive x y z t1 t2

/-- The all-repeated branch of Sapir's `2occ` split.  The shared block
decomposition aligns the independently selected `z` owners, the four owner
comparisons select one exact five-variable source projection, and that
projection yields triple stability. -/
theorem tripleStable_of_repeatedPerkinsPreimages
    {source target : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : source.bind substitution = target)
    (pattern : OccurrencePattern extra target.toList)
    {firstBlock secondBlock : List Nat}
    (firstPerm : firstBlock.Perm (middleVariables extra))
    (secondPerm : secondBlock.Perm (middleVariables extra))
    (targetShape :
      target.toList =
        [0, 1] ++ firstBlock ++ [0] ++ secondBlock ++ [1])
    (independent :
      IndependentBlockPreimageSelection source substitution
        extra firstBlock secondBlock)
    {z : Nat} (zMiddle : z ∈ middleVariables extra)
    (xRepeated :
      RepeatedTwoBlockMarkerPreimages source substitution
        [] [0] ([0, 1] ++ firstBlock) [0] 0)
    (yRepeated :
      RepeatedTwoBlockMarkerPreimages source substitution
        [0] [1]
        ([0, 1] ++ firstBlock ++ [0] ++ secondBlock) [1] 1)
    (zRepeated :
      RepeatedTwoBlockMarkerPreimages source substitution
        [0, 1] firstBlock
        ([0, 1] ++ firstBlock ++ [0]) secondBlock z) :
    ∃ sourceX sourceY sourceZ,
      TripleStable source sourceX sourceY sourceZ ∧
      source.toList.count sourceX = 2 ∧
      source.toList.count sourceY = 2 ∧
      source.toList.count sourceZ = 2 ∧
      0 ∈ (substitution sourceX).toList ∧
      1 ∈ (substitution sourceY).toList ∧
      z ∈ (substitution sourceZ).toList := by
  rcases xRepeated with
    ⟨xFirst, xSecond, sourceX,
      xFirstPreimage, xSecondPreimage,
      xFirstAt, xSecondAt, xImage, xCount⟩
  rcases yRepeated with
    ⟨yFirst, ySecond, sourceY,
      yFirstPreimage, ySecondPreimage,
      yFirstAt, ySecondAt, yImage, yCount⟩
  rcases zRepeated with
    ⟨zFirst, zSecond, sourceZ,
      zFirstPreimage, zSecondPreimage,
      zFirstAt, zSecondAt, zImage, zCount⟩
  rcases independent with
    ⟨t1Owner, t1Source, t1First, t1Second,
      t2Owner, t2Source, t2First, t2Second,
      t1At, t1Count, _t1Different,
      t1FirstPreimage, _t1SecondPreimage,
      t2At, t2Count, _t2Different,
      t2FirstPreimage, _t2SecondPreimage,
      zIndependent⟩
  rcases zIndependent z zMiddle with
    ⟨independentZFirst, independentZSecond,
      independentZFirstPreimage, independentZSecondPreimage,
      sourceCase⟩
  have middleNodup : (middleVariables extra).Nodup := by
    simp only [middleVariables]
    exact
      (List.nodup_range : (List.range extra).Nodup).map
        (fun index => index + 2)
        (by
          intro first second different equality
          apply different
          exact Nat.add_right_cancel equality)
  have firstNodup : firstBlock.Nodup :=
    firstPerm.nodup_iff.mpr middleNodup
  have secondNodup : secondBlock.Nodup :=
    secondPerm.nodup_iff.mpr middleNodup
  have firstShape :
      target.toList =
        [0, 1] ++ firstBlock ++ ([0] ++ secondBlock ++ [1]) := by
    simpa only [List.append_assoc] using targetShape
  have secondShape :
      target.toList =
        ([0, 1] ++ firstBlock ++ [0]) ++ secondBlock ++ [1] := by
    simpa only [List.append_assoc] using targetShape
  have independentZFirstEq : independentZFirst = zFirst := by
    exact
      blockOccurrencePreimage_owner_eq_of_nodup
        mapped firstShape firstNodup
        independentZFirstPreimage zFirstPreimage
  have independentZSecondEq : independentZSecond = zSecond := by
    exact
      blockOccurrencePreimage_owner_eq_of_nodup
        mapped secondShape secondNodup
        independentZSecondPreimage zSecondPreimage
  subst independentZFirst
  subst independentZSecond
  rcases
      repeatedPerkinsOwnerFacts mapped pattern targetShape zMiddle
        xFirstPreimage xSecondPreimage
        yFirstPreimage ySecondPreimage
        zFirstPreimage zSecondPreimage
        xFirstAt xSecondAt yFirstAt ySecondAt zFirstAt zSecondAt
        xCount yCount zCount yImage zImage with
    ⟨ownerChain, _xOwnersDifferent, _yOwnersDifferent,
      _zOwnersDifferent, repeatedNodup⟩
  have separatorOrder :=
    perkinsSeparatorOwnerOrder mapped targetShape
      yFirstPreimage t1FirstPreimage xSecondPreimage
      t2FirstPreimage ySecondPreimage
  rcases
      repeatedAndLinearSources_nodup repeatedNodup
        xCount yCount zCount t1Count t2Count
        t1At xSecondAt t2At separatorOrder.2.1 separatorOrder.2.2.1 with
    ⟨allNodup, t1BeforeX, xBeforeT2⟩
  have repeatedDistinct := repeatedNodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at repeatedDistinct
  rcases repeatedDistinct with
    ⟨⟨xy, xz⟩, ⟨yz, _⟩⟩
  have xBeforeY :
      xFirst < yFirst :=
    sourceAt_lt_of_le_of_ne xFirstAt yFirstAt xy ownerChain.1
  have yBeforeZ :
      yFirst < zFirst :=
    sourceAt_lt_of_le_of_ne yFirstAt zFirstAt yz ownerChain.2.1
  have zBeforeX :
      zFirst < xSecond :=
    sourceAt_lt_of_le_of_ne zFirstAt xSecondAt
      (Ne.symm xz) ownerChain.2.2.1
  have xBeforeZ :
      xSecond < zSecond :=
    sourceAt_lt_of_le_of_ne xSecondAt zSecondAt
      xz ownerChain.2.2.2.1
  have zBeforeY :
      zSecond < ySecond :=
    sourceAt_lt_of_le_of_ne zSecondAt ySecondAt
      (Ne.symm yz) ownerChain.2.2.2.2
  have yNeT1 : sourceY ≠ t1Source := by
    intro equality
    rw [← equality, yCount] at t1Count
    omega
  have zNeT1 : sourceZ ≠ t1Source := by
    intro equality
    rw [← equality, zCount] at t1Count
    omega
  have zNeT2 : sourceZ ≠ t2Source := by
    intro equality
    rw [← equality, zCount] at t2Count
    omega
  have yNeT2 : sourceY ≠ t2Source := by
    intro equality
    rw [← equality, yCount] at t2Count
    omega
  have yBeforeT1 :
      yFirst < t1Owner :=
    sourceAt_lt_of_le_of_ne yFirstAt t1At
      yNeT1 separatorOrder.1
  have t2BeforeY :
      t2Owner < ySecond :=
    sourceAt_lt_of_le_of_ne t2At ySecondAt
      (Ne.symm yNeT2) separatorOrder.2.2.2
  have stable :
      TripleStable source sourceX sourceY sourceZ := by
    rcases sourceCase with case1 | case2 | case3 | case4
    · have t1BeforeZ :
          t1Owner < zFirst :=
        sourceAt_lt_of_le_of_ne t1At zFirstAt
          (Ne.symm zNeT1) case1.1
      have t2BeforeZ :
          t2Owner < zSecond :=
        sourceAt_lt_of_le_of_ne t2At zSecondAt
          (Ne.symm zNeT2) case1.2
      apply tripleStable_of_sourceProjectionCase1 allNodup
      exact
        exactFiveVariableProjection_case1 allNodup
          xCount yCount zCount t1Count t2Count
          xFirstAt yFirstAt zFirstAt xSecondAt zSecondAt ySecondAt
          t1At t2At
          ⟨xBeforeY, yBeforeT1, t1BeforeZ, zBeforeX,
            xBeforeT2, t2BeforeZ, zBeforeY⟩
    · have zBeforeT1 :
          zFirst < t1Owner :=
        sourceAt_lt_of_le_of_ne zFirstAt t1At
          zNeT1 case2.1
      have t2BeforeZ :
          t2Owner < zSecond :=
        sourceAt_lt_of_le_of_ne t2At zSecondAt
          (Ne.symm zNeT2) case2.2
      apply tripleStable_of_sourceProjectionCase2 allNodup
      exact
        exactFiveVariableProjection_case2 allNodup
          xCount yCount zCount t1Count t2Count
          xFirstAt yFirstAt zFirstAt xSecondAt zSecondAt ySecondAt
          t1At t2At
          ⟨xBeforeY, yBeforeZ, zBeforeT1, t1BeforeX,
            xBeforeT2, t2BeforeZ, zBeforeY⟩
    · have t1BeforeZ :
          t1Owner < zFirst :=
        sourceAt_lt_of_le_of_ne t1At zFirstAt
          (Ne.symm zNeT1) case3.1
      have zBeforeT2 :
          zSecond < t2Owner :=
        sourceAt_lt_of_le_of_ne zSecondAt t2At
          zNeT2 case3.2
      apply tripleStable_of_sourceProjectionCase3 allNodup
      exact
        exactFiveVariableProjection_case3 allNodup
          xCount yCount zCount t1Count t2Count
          xFirstAt yFirstAt zFirstAt xSecondAt zSecondAt ySecondAt
          t1At t2At
          ⟨xBeforeY, yBeforeT1, t1BeforeZ, zBeforeX,
            xBeforeZ, zBeforeT2, t2BeforeY⟩
    · have zBeforeT1 :
          zFirst < t1Owner :=
        sourceAt_lt_of_le_of_ne zFirstAt t1At
          zNeT1 case4.1
      have zBeforeT2 :
          zSecond < t2Owner :=
        sourceAt_lt_of_le_of_ne zSecondAt t2At
          zNeT2 case4.2
      apply tripleStable_of_sourceProjectionCase4 allNodup
      exact
        exactFiveVariableProjection_case4 allNodup
          xCount yCount zCount t1Count t2Count
          xFirstAt yFirstAt zFirstAt xSecondAt zSecondAt ySecondAt
          t1At t2At
          ⟨xBeforeY, yBeforeZ, zBeforeT1, t1BeforeX,
            xBeforeZ, zBeforeT2, t2BeforeY⟩
  exact
    ⟨sourceX, sourceY, sourceZ, stable,
      xCount, yCount, zCount, xImage, yImage, zImage⟩

private def contributesTo
    (substitution : Nat → Word Nat)
    (targetKeep : Nat → Bool) (sourceLetter : Nat) : Bool :=
  !((substitution sourceLetter).toList.filter targetKeep).isEmpty

private def keepSixSources
    (xFirst xSecond yFirst ySecond zFirst zSecond letter : Nat) : Bool :=
  pairKeep xFirst xSecond letter ||
    pairKeep yFirst ySecond letter ||
    pairKeep zFirst zSecond letter

def KeepSixStable
    (source : Word Nat)
    (xFirst xSecond yFirst ySecond zFirst zSecond : Nat) : Prop :=
  ∀ other,
    (Identity.mk source other).SatisfiedBy table.semigroup →
    source.toList.filter
        (keepSixSources
          xFirst xSecond yFirst ySecond zFirst zSecond) =
      other.toList.filter
        (keepSixSources
          xFirst xSecond yFirst ySecond zFirst zSecond)

private theorem keepSixSources_cases
    {xFirst xSecond yFirst ySecond zFirst zSecond letter : Nat}
    (kept :
      keepSixSources
          xFirst xSecond yFirst ySecond zFirst zSecond letter =
        true) :
    letter = xFirst ∨ letter = xSecond ∨
      letter = yFirst ∨ letter = ySecond ∨
      letter = zFirst ∨ letter = zSecond := by
  by_cases xKept : pairKeep xFirst xSecond letter
  · have xCases : letter = xFirst ∨ letter = xSecond := by
      simpa [pairKeep] using xKept
    rcases xCases with xCase | xCase
    · exact Or.inl xCase
    · exact Or.inr (Or.inl xCase)
  · by_cases yKept : pairKeep yFirst ySecond letter
    · have yCases : letter = yFirst ∨ letter = ySecond := by
        simpa [pairKeep] using yKept
      rcases yCases with yCase | yCase
      · exact Or.inr (Or.inr (Or.inl yCase))
      · exact Or.inr (Or.inr (Or.inr (Or.inl yCase)))
    · have zKept : pairKeep zFirst zSecond letter = true := by
        cases zValue : pairKeep zFirst zSecond letter
        · simp [keepSixSources, xKept, yKept, zValue] at kept
        · rfl
      have zCases : letter = zFirst ∨ letter = zSecond := by
        simpa [pairKeep] using zKept
      rcases zCases with zCase | zCase
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl zCase))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr zCase))))

theorem keepSixStable_LLL
    {source : Word Nat}
    {xFirst xSecond yFirst ySecond zFirst zSecond : Nat}
    (xFirstCount : source.toList.count xFirst = 1)
    (xSecondCount : source.toList.count xSecond = 1)
    (yFirstCount : source.toList.count yFirst = 1)
    (ySecondCount : source.toList.count ySecond = 1)
    (zFirstCount : source.toList.count zFirst = 1)
    (zSecondCount : source.toList.count zSecond = 1) :
    KeepSixStable source
      xFirst xSecond yFirst ySecond zFirst zSecond := by
  apply stable_filter_of_count_one_or_stable_two
  · intro selected selectedKept
    rcases keepSixSources_cases selectedKept with
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl xFirstCount
    · exact Or.inl xSecondCount
    · exact Or.inl yFirstCount
    · exact Or.inl ySecondCount
    · exact Or.inl zFirstCount
    · exact Or.inl zSecondCount
  · intro first second firstKept _ _ firstTwo _
    rcases keepSixSources_cases firstKept with
      rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem keepSixStable_LLR
    {source : Word Nat}
    {xFirst xSecond yFirst ySecond sourceZ : Nat}
    (xFirstCount : source.toList.count xFirst = 1)
    (xSecondCount : source.toList.count xSecond = 1)
    (yFirstCount : source.toList.count yFirst = 1)
    (ySecondCount : source.toList.count ySecond = 1)
    (zCount : source.toList.count sourceZ = 2)
    (zStable : SingletonStable source sourceZ) :
    KeepSixStable source
      xFirst xSecond yFirst ySecond sourceZ sourceZ := by
  apply stable_filter_of_count_one_or_stable_two
  · intro selected selectedKept
    rcases keepSixSources_cases selectedKept with
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl xFirstCount
    · exact Or.inl xSecondCount
    · exact Or.inl yFirstCount
    · exact Or.inl ySecondCount
    · exact Or.inr ⟨zCount, zStable⟩
    · exact Or.inr ⟨zCount, zStable⟩
  · intro first second firstKept secondKept different
      firstTwo secondTwo
    have firstEq : first = sourceZ := by
      rcases keepSixSources_cases firstKept with
        rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    have secondEq : second = sourceZ := by
      rcases keepSixSources_cases secondKept with
        rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    exact (different (firstEq.trans secondEq.symm)).elim

theorem keepSixStable_LRL
    {source : Word Nat}
    {xFirst xSecond sourceY zFirst zSecond : Nat}
    (xFirstCount : source.toList.count xFirst = 1)
    (xSecondCount : source.toList.count xSecond = 1)
    (yCount : source.toList.count sourceY = 2)
    (yStable : SingletonStable source sourceY)
    (zFirstCount : source.toList.count zFirst = 1)
    (zSecondCount : source.toList.count zSecond = 1) :
    KeepSixStable source
      xFirst xSecond sourceY sourceY zFirst zSecond := by
  apply stable_filter_of_count_one_or_stable_two
  · intro selected selectedKept
    rcases keepSixSources_cases selectedKept with
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl xFirstCount
    · exact Or.inl xSecondCount
    · exact Or.inr ⟨yCount, yStable⟩
    · exact Or.inr ⟨yCount, yStable⟩
    · exact Or.inl zFirstCount
    · exact Or.inl zSecondCount
  · intro first second firstKept secondKept different
      firstTwo secondTwo
    have firstEq : first = sourceY := by
      rcases keepSixSources_cases firstKept with
        rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    have secondEq : second = sourceY := by
      rcases keepSixSources_cases secondKept with
        rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    exact (different (firstEq.trans secondEq.symm)).elim

theorem keepSixStable_RLL
    {source : Word Nat}
    {sourceX yFirst ySecond zFirst zSecond : Nat}
    (xCount : source.toList.count sourceX = 2)
    (xStable : SingletonStable source sourceX)
    (yFirstCount : source.toList.count yFirst = 1)
    (ySecondCount : source.toList.count ySecond = 1)
    (zFirstCount : source.toList.count zFirst = 1)
    (zSecondCount : source.toList.count zSecond = 1) :
    KeepSixStable source
      sourceX sourceX yFirst ySecond zFirst zSecond := by
  apply stable_filter_of_count_one_or_stable_two
  · intro selected selectedKept
    rcases keepSixSources_cases selectedKept with
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr ⟨xCount, xStable⟩
    · exact Or.inr ⟨xCount, xStable⟩
    · exact Or.inl yFirstCount
    · exact Or.inl ySecondCount
    · exact Or.inl zFirstCount
    · exact Or.inl zSecondCount
  · intro first second firstKept secondKept different
      firstTwo secondTwo
    have firstEq : first = sourceX := by
      rcases keepSixSources_cases firstKept with
        rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    have secondEq : second = sourceX := by
      rcases keepSixSources_cases secondKept with
        rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    exact (different (firstEq.trans secondEq.symm)).elim

theorem keepSixStable_LRR
    {source : Word Nat}
    {xFirst xSecond sourceY sourceZ : Nat}
    (xFirstCount : source.toList.count xFirst = 1)
    (xSecondCount : source.toList.count xSecond = 1)
    (yCount : source.toList.count sourceY = 2)
    (yStable : SingletonStable source sourceY)
    (zCount : source.toList.count sourceZ = 2)
    (zStable : SingletonStable source sourceZ)
    (yzStable :
      sourceY ≠ sourceZ →
        PairStable source sourceY sourceZ) :
    KeepSixStable source
      xFirst xSecond sourceY sourceY sourceZ sourceZ := by
  apply stable_filter_of_count_one_or_stable_two
  · intro selected selectedKept
    rcases keepSixSources_cases selectedKept with
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl xFirstCount
    · exact Or.inl xSecondCount
    · exact Or.inr ⟨yCount, yStable⟩
    · exact Or.inr ⟨yCount, yStable⟩
    · exact Or.inr ⟨zCount, zStable⟩
    · exact Or.inr ⟨zCount, zStable⟩
  · intro first second firstKept secondKept different
      firstTwo secondTwo
    have firstCases : first = sourceY ∨ first = sourceZ := by
      rcases keepSixSources_cases firstKept with
        rfl | rfl | rfl | rfl | rfl | rfl
      · omega
      · omega
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact Or.inr rfl
    have secondCases : second = sourceY ∨ second = sourceZ := by
      rcases keepSixSources_cases secondKept with
        rfl | rfl | rfl | rfl | rfl | rfl
      · omega
      · omega
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact Or.inr rfl
    rcases firstCases with rfl | rfl <;>
      rcases secondCases with rfl | rfl
    · exact (different rfl).elim
    · exact yzStable different
    · exact (yzStable (Ne.symm different)).comm
    · exact (different rfl).elim

theorem keepSixStable_RLR
    {source : Word Nat}
    {sourceX yFirst ySecond sourceZ : Nat}
    (xCount : source.toList.count sourceX = 2)
    (xStable : SingletonStable source sourceX)
    (yFirstCount : source.toList.count yFirst = 1)
    (ySecondCount : source.toList.count ySecond = 1)
    (zCount : source.toList.count sourceZ = 2)
    (zStable : SingletonStable source sourceZ)
    (xzStable :
      sourceX ≠ sourceZ →
        PairStable source sourceX sourceZ) :
    KeepSixStable source
      sourceX sourceX yFirst ySecond sourceZ sourceZ := by
  apply stable_filter_of_count_one_or_stable_two
  · intro selected selectedKept
    rcases keepSixSources_cases selectedKept with
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr ⟨xCount, xStable⟩
    · exact Or.inr ⟨xCount, xStable⟩
    · exact Or.inl yFirstCount
    · exact Or.inl ySecondCount
    · exact Or.inr ⟨zCount, zStable⟩
    · exact Or.inr ⟨zCount, zStable⟩
  · intro first second firstKept secondKept different
      firstTwo secondTwo
    have firstCases : first = sourceX ∨ first = sourceZ := by
      rcases keepSixSources_cases firstKept with
        rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inl rfl
      · omega
      · omega
      · exact Or.inr rfl
      · exact Or.inr rfl
    have secondCases : second = sourceX ∨ second = sourceZ := by
      rcases keepSixSources_cases secondKept with
        rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inl rfl
      · omega
      · omega
      · exact Or.inr rfl
      · exact Or.inr rfl
    rcases firstCases with rfl | rfl <;>
      rcases secondCases with rfl | rfl
    · exact (different rfl).elim
    · exact xzStable different
    · exact (xzStable (Ne.symm different)).comm
    · exact (different rfl).elim

theorem keepSixStable_RRL
    {source : Word Nat}
    {sourceX sourceY zFirst zSecond : Nat}
    (xCount : source.toList.count sourceX = 2)
    (xStable : SingletonStable source sourceX)
    (yCount : source.toList.count sourceY = 2)
    (yStable : SingletonStable source sourceY)
    (zFirstCount : source.toList.count zFirst = 1)
    (zSecondCount : source.toList.count zSecond = 1)
    (xyStable :
      sourceX ≠ sourceY →
        PairStable source sourceX sourceY) :
    KeepSixStable source
      sourceX sourceX sourceY sourceY zFirst zSecond := by
  apply stable_filter_of_count_one_or_stable_two
  · intro selected selectedKept
    rcases keepSixSources_cases selectedKept with
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr ⟨xCount, xStable⟩
    · exact Or.inr ⟨xCount, xStable⟩
    · exact Or.inr ⟨yCount, yStable⟩
    · exact Or.inr ⟨yCount, yStable⟩
    · exact Or.inl zFirstCount
    · exact Or.inl zSecondCount
  · intro first second firstKept secondKept different
      firstTwo secondTwo
    have firstCases : first = sourceX ∨ first = sourceY := by
      rcases keepSixSources_cases firstKept with
        rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact Or.inr rfl
      · omega
      · omega
    have secondCases : second = sourceX ∨ second = sourceY := by
      rcases keepSixSources_cases secondKept with
        rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact Or.inr rfl
      · omega
      · omega
    rcases firstCases with rfl | rfl <;>
      rcases secondCases with rfl | rfl
    · exact (different rfl).elim
    · exact xyStable different
    · exact (xyStable (Ne.symm different)).comm
    · exact (different rfl).elim

private theorem contributesTo_eq_true_of_image
    (substitution : Nat → Word Nat)
    (targetKeep : Nat → Bool)
    {sourceLetter targetLetter : Nat}
    (targetKept : targetKeep targetLetter = true)
    (imageMember :
      targetLetter ∈ (substitution sourceLetter).toList) :
    contributesTo substitution targetKeep sourceLetter = true := by
  unfold contributesTo
  have retained :
      targetLetter ∈
        (substitution sourceLetter).toList.filter targetKeep :=
    List.mem_filter.mpr ⟨imageMember, targetKept⟩
  cases filteredShape :
      (substitution sourceLetter).toList.filter targetKeep with
  | nil =>
      rw [filteredShape] at retained
      simp at retained
  | cons head tail =>
      simp [filteredShape]

/-- The complete inverse contributor set of target `0,1,z` is the union of
the two selected source labels for each marker.  Equal label pairs encode a
repeated source variable, so this one statement covers all eight
linear/repeated branches. -/
theorem contributors_eq_keepSixSources_of_markerPreimages
    {source target : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : source.bind substitution = target)
    (pattern : OccurrencePattern extra target.toList)
    {firstBlock secondBlock : List Nat}
    (targetShape :
      target.toList =
        [0, 1] ++ firstBlock ++ [0] ++ secondBlock ++ [1])
    {z : Nat}
    {xFirstOwner xSecondOwner xFirstSource xSecondSource
      yFirstOwner ySecondOwner yFirstSource ySecondSource
      zFirstOwner zSecondOwner zFirstSource zSecondSource : Nat}
    (xFirstPreimage :
      BlockOccurrencePreimage source substitution
        [] [0] xFirstOwner 0)
    (xSecondPreimage :
      BlockOccurrencePreimage source substitution
        ([0, 1] ++ firstBlock) [0] xSecondOwner 0)
    (xFirstAt :
      sourceAt source.toList xFirstOwner = some xFirstSource)
    (xSecondAt :
      sourceAt source.toList xSecondOwner = some xSecondSource)
    (xFirstImage : 0 ∈ (substitution xFirstSource).toList)
    (xSecondImage : 0 ∈ (substitution xSecondSource).toList)
    (xAlternative :
      TwoOccurrencePreimageAlternative source
        xFirstSource xSecondSource)
    (yFirstPreimage :
      BlockOccurrencePreimage source substitution
        [0] [1] yFirstOwner 1)
    (ySecondPreimage :
      BlockOccurrencePreimage source substitution
        ([0, 1] ++ firstBlock ++ [0] ++ secondBlock)
        [1] ySecondOwner 1)
    (yFirstAt :
      sourceAt source.toList yFirstOwner = some yFirstSource)
    (ySecondAt :
      sourceAt source.toList ySecondOwner = some ySecondSource)
    (yFirstImage : 1 ∈ (substitution yFirstSource).toList)
    (ySecondImage : 1 ∈ (substitution ySecondSource).toList)
    (yAlternative :
      TwoOccurrencePreimageAlternative source
        yFirstSource ySecondSource)
    (zFirstPreimage :
      BlockOccurrencePreimage source substitution
        [0, 1] firstBlock zFirstOwner z)
    (zSecondPreimage :
      BlockOccurrencePreimage source substitution
        ([0, 1] ++ firstBlock ++ [0]) secondBlock zSecondOwner z)
    (zFirstAt :
      sourceAt source.toList zFirstOwner = some zFirstSource)
    (zSecondAt :
      sourceAt source.toList zSecondOwner = some zSecondSource)
    (zFirstImage : z ∈ (substitution zFirstSource).toList)
    (zSecondImage : z ∈ (substitution zSecondSource).toList)
    (zAlternative :
      TwoOccurrencePreimageAlternative source
        zFirstSource zSecondSource) :
    ∀ sourceLetter, sourceLetter ∈ source.toList →
      contributesTo substitution (keepTriple 0 1 z) sourceLetter =
        keepSixSources
          xFirstSource xSecondSource
          yFirstSource ySecondSource
          zFirstSource zSecondSource sourceLetter := by
  have xShape :
      target.toList =
        [] ++ [0] ++ ([1] ++ firstBlock) ++ [0] ++
          (secondBlock ++ [1]) := by
    simpa only [List.nil_append, List.append_assoc] using targetShape
  have yShape :
      target.toList =
        [0] ++ [1] ++ (firstBlock ++ [0] ++ secondBlock) ++
          [1] ++ [] := by
    simpa only [List.append_assoc, List.append_nil] using targetShape
  have zShape :
      target.toList =
        [0, 1] ++ firstBlock ++ [0] ++ secondBlock ++ [1] :=
    targetShape
  intro sourceLetter sourceMember
  cases contributes :
      contributesTo substitution (keepTriple 0 1 z) sourceLetter with
  | false =>
      have sourceNeXFirst : sourceLetter ≠ xFirstSource := by
        intro equality
        subst sourceLetter
        have retained :=
          contributesTo_eq_true_of_image substitution
            (keepTriple 0 1 z) (by simp [keepTriple]) xFirstImage
        rw [contributes] at retained
        contradiction
      have sourceNeXSecond : sourceLetter ≠ xSecondSource := by
        intro equality
        subst sourceLetter
        have retained :=
          contributesTo_eq_true_of_image substitution
            (keepTriple 0 1 z) (by simp [keepTriple]) xSecondImage
        rw [contributes] at retained
        contradiction
      have sourceNeYFirst : sourceLetter ≠ yFirstSource := by
        intro equality
        subst sourceLetter
        have retained :=
          contributesTo_eq_true_of_image substitution
            (keepTriple 0 1 z) (by simp [keepTriple]) yFirstImage
        rw [contributes] at retained
        contradiction
      have sourceNeYSecond : sourceLetter ≠ ySecondSource := by
        intro equality
        subst sourceLetter
        have retained :=
          contributesTo_eq_true_of_image substitution
            (keepTriple 0 1 z) (by simp [keepTriple]) ySecondImage
        rw [contributes] at retained
        contradiction
      have sourceNeZFirst : sourceLetter ≠ zFirstSource := by
        intro equality
        subst sourceLetter
        have retained :=
          contributesTo_eq_true_of_image substitution
            (keepTriple 0 1 z) (by simp [keepTriple]) zFirstImage
        rw [contributes] at retained
        contradiction
      have sourceNeZSecond : sourceLetter ≠ zSecondSource := by
        intro equality
        subst sourceLetter
        have retained :=
          contributesTo_eq_true_of_image substitution
            (keepTriple 0 1 z) (by simp [keepTriple]) zSecondImage
        rw [contributes] at retained
        contradiction
      simp [keepSixSources, pairKeep, sourceNeXFirst,
        sourceNeXSecond, sourceNeYFirst, sourceNeYSecond,
        sourceNeZFirst, sourceNeZSecond]
  | true =>
      have retainedExists :
          ∃ retained,
            retained ∈ (substitution sourceLetter).toList ∧
            keepTriple 0 1 z retained = true := by
        unfold contributesTo at contributes
        cases filteredShape :
            (substitution sourceLetter).toList.filter
              (keepTriple 0 1 z) with
        | nil =>
            simp [filteredShape] at contributes
        | cons retained rest =>
            refine ⟨retained, ?_, ?_⟩
            · exact
                (List.mem_filter.mp
                  (show retained ∈
                      (substitution sourceLetter).toList.filter
                        (keepTriple 0 1 z) by
                    rw [filteredShape]
                    simp)).1
            · exact
                (List.mem_filter.mp
                  (show retained ∈
                      (substitution sourceLetter).toList.filter
                        (keepTriple 0 1 z) by
                    rw [filteredShape]
                    simp)).2
      rcases retainedExists with
        ⟨retained, retainedImage, retainedKept⟩
      have retainedCases :
          retained = 0 ∨ retained = 1 ∨ retained = z := by
        simpa [keepTriple, or_assoc] using retainedKept
      rcases retainedCases with retainedX | retainedY | retainedZ
      · subst retained
        have contributor :=
          twoOccurrenceAlternative_completeContributors_of_sections
            mapped pattern xShape xFirstPreimage xSecondPreimage
            xFirstAt xSecondAt xFirstImage xSecondImage xAlternative
            sourceMember retainedImage
        rcases contributor with sourceX | sourceX
        · subst sourceLetter
          simp [keepSixSources, pairKeep]
        · subst sourceLetter
          simp [keepSixSources, pairKeep]
      · subst retained
        have contributor :=
          twoOccurrenceAlternative_completeContributors_of_sections
            mapped pattern yShape yFirstPreimage ySecondPreimage
            yFirstAt ySecondAt yFirstImage ySecondImage yAlternative
            sourceMember retainedImage
        rcases contributor with sourceY | sourceY
        · subst sourceLetter
          simp [keepSixSources, pairKeep]
        · subst sourceLetter
          simp [keepSixSources, pairKeep]
      · subst retained
        have contributor :=
          twoOccurrenceAlternative_completeContributors_of_sections
            mapped pattern zShape zFirstPreimage zSecondPreimage
            zFirstAt zSecondAt zFirstImage zSecondImage zAlternative
            sourceMember retainedImage
        rcases contributor with sourceZ | sourceZ
        · subst sourceLetter
          simp [keepSixSources, pairKeep]
        · subst sourceLetter
          simp [keepSixSources, pairKeep]

/-- Three repeated source variables are exactly the inverse contributors to
their selected three-marker target projection. -/
theorem contributors_eq_keepTriple_of_repeatedSources
    {source target : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : source.bind substitution = target)
    (pattern : OccurrencePattern extra target.toList)
    {sourceX sourceY sourceZ targetX targetY targetZ : Nat}
    (xCount : source.toList.count sourceX = 2)
    (yCount : source.toList.count sourceY = 2)
    (zCount : source.toList.count sourceZ = 2)
    (xImage : targetX ∈ (substitution sourceX).toList)
    (yImage : targetY ∈ (substitution sourceY).toList)
    (zImage : targetZ ∈ (substitution sourceZ).toList) :
    ∀ sourceLetter, sourceLetter ∈ source.toList →
      contributesTo substitution
          (keepTriple targetX targetY targetZ) sourceLetter =
        keepTriple sourceX sourceY sourceZ sourceLetter := by
  have contributesOfMem :
      ∀ (sourceLabel targetLabel : Nat),
        keepTriple targetX targetY targetZ targetLabel = true →
        targetLabel ∈ (substitution sourceLabel).toList →
        contributesTo substitution
            (keepTriple targetX targetY targetZ) sourceLabel = true := by
    intro sourceLabel targetLabel targetKept imageMember
    unfold contributesTo
    have retained :
        targetLabel ∈
          (substitution sourceLabel).toList.filter
            (keepTriple targetX targetY targetZ) :=
      List.mem_filter.mpr ⟨imageMember, targetKept⟩
    cases filteredShape :
        (substitution sourceLabel).toList.filter
          (keepTriple targetX targetY targetZ) with
    | nil =>
        rw [filteredShape] at retained
        simp at retained
    | cons head tail =>
        simp [filteredShape]
  intro sourceLetter sourceMember
  by_cases hx : sourceLetter = sourceX
  · subst sourceLetter
    rw [contributesOfMem sourceX targetX
      (by simp [keepTriple]) xImage]
    simp [keepTriple]
  · by_cases hy : sourceLetter = sourceY
    · subst sourceLetter
      rw [contributesOfMem sourceY targetY
        (by simp [keepTriple]) yImage]
      simp [keepTriple]
    · by_cases hz : sourceLetter = sourceZ
      · subst sourceLetter
        rw [contributesOfMem sourceZ targetZ
          (by simp [keepTriple]) zImage]
        simp [keepTriple]
      · have sourceNotKept :
            keepTriple sourceX sourceY sourceZ sourceLetter = false := by
          simp [keepTriple, hx, hy, hz]
        rw [sourceNotKept]
        unfold contributesTo
        cases filteredShape :
            (substitution sourceLetter).toList.filter
              (keepTriple targetX targetY targetZ) with
        | nil =>
            simp [filteredShape]
        | cons retained rest =>
            have retainedMember :
                retained ∈
                  (substitution sourceLetter).toList.filter
                    (keepTriple targetX targetY targetZ) := by
              rw [filteredShape]
              simp
            rcases List.mem_filter.mp retainedMember with
              ⟨retainedImage, retainedKept⟩
            have retainedCases :
                (retained = targetX ∨ retained = targetY) ∨
                  retained = targetZ := by
              simpa [keepTriple] using retainedKept
            rcases retainedCases with
              (retainedX | retainedY) | retainedZ
            · subst retained
              exact
                (hx
                  (repeatedSource_uniqueMarkerContributor
                    mapped pattern xCount xImage
                    sourceMember retainedImage)).elim
            · subst retained
              exact
                (hy
                  (repeatedSource_uniqueMarkerContributor
                    mapped pattern yCount yImage
                    sourceMember retainedImage)).elim
            · subst retained
              exact
                (hz
                  (repeatedSource_uniqueMarkerContributor
                    mapped pattern zCount zImage
                    sourceMember retainedImage)).elim

private theorem flatMap_filter_contributors
    (letters : List Nat) (images : Nat → List Nat) :
    (letters.filter fun letter => !(images letter).isEmpty).flatMap images =
      letters.flatMap images := by
  induction letters with
  | nil => rfl
  | cons letter rest ih =>
      simp only [List.filter_cons, List.flatMap_cons]
      cases imageShape : images letter with
      | nil =>
          simp [imageShape, ih]
      | cons head tail =>
          simp [imageShape, ih]

private theorem bind_filtered_projection
    (source : Word Nat) (substitution : Nat → Word Nat)
    (targetKeep : Nat → Bool) :
    (source.bind substitution).toList.filter targetKeep =
      (source.toList.filter
          (contributesTo substitution targetKeep)).flatMap
        (fun sourceLetter =>
          (substitution sourceLetter).toList.filter targetKeep) := by
  rw [Word.toList_bind, List.filter_flatMap]
  symm
  exact
    flatMap_filter_contributors source.toList
      (fun sourceLetter =>
        (substitution sourceLetter).toList.filter targetKeep)

private theorem filter_eq_of_predicate_eq_on_members
    (letters : List Nat) (first second : Nat → Bool)
    (agree :
      ∀ letter, letter ∈ letters →
        first letter = second letter) :
    letters.filter first = letters.filter second := by
  apply List.filter_congr
  intro letter member
  exact agree letter member

/-- If the complete inverse-contributor projection is stable in the source
identity, its target projection is stable after applying the substitution.
This is the transport interface used by the mixed linear/repeated branch. -/
theorem bind_projection_stable_of_contributor_filter
    {source other : Word Nat}
    (substitution : Nat → Word Nat)
    (targetKeep : Nat → Bool)
    (contributorStable :
      source.toList.filter
          (contributesTo substitution targetKeep) =
        other.toList.filter
          (contributesTo substitution targetKeep)) :
    (source.bind substitution).toList.filter targetKeep =
      (other.bind substitution).toList.filter targetKeep := by
  rw [bind_filtered_projection source substitution targetKeep,
    bind_filtered_projection other substitution targetKeep,
    contributorStable]

/-- It is enough for the complete inverse-contributor projection of the
source to be an isoterm.  This is the direct formal counterpart of Sapir's
"similar but more simple arguments" for a mixed linear/repeated preimage
case. -/
theorem bind_projection_stable_of_contributor_isoterm
    {source other projected : Word Nat}
    (substitution : Nat → Word Nat)
    (targetKeep : Nat → Bool)
    (valid :
      (Identity.mk source other).SatisfiedBy table.semigroup)
    (isoterm : Isoterm table.semigroup projected)
    (sourceFiltered :
      source.toList.filter
          (contributesTo substitution targetKeep) =
        projected.toList) :
    (source.bind substitution).toList.filter targetKeep =
      (other.bind substitution).toList.filter targetKeep := by
  apply bind_projection_stable_of_contributor_filter
  have otherFiltered :=
    filtered_eq_of_isoterm valid isoterm
      (contributesTo substitution targetKeep) sourceFiltered
  exact sourceFiltered.trans otherFiltered.symm

/-- Stability of the six-label inverse-contributor projection transports
through a nonempty-word substitution. -/
theorem bind_projection_stable_of_keepSixStable
    {source other : Word Nat}
    (substitution : Nat → Word Nat)
    (targetKeep : Nat → Bool)
    (valid :
      (Identity.mk source other).SatisfiedBy table.semigroup)
    {xFirst xSecond yFirst ySecond zFirst zSecond : Nat}
    (stable :
      KeepSixStable source
        xFirst xSecond yFirst ySecond zFirst zSecond)
    (contributors :
      ∀ sourceLetter, sourceLetter ∈ source.toList →
        contributesTo substitution targetKeep sourceLetter =
          keepSixSources
            xFirst xSecond yFirst ySecond zFirst zSecond
            sourceLetter) :
    (source.bind substitution).toList.filter targetKeep =
      (other.bind substitution).toList.filter targetKeep := by
  let sourceKeep :=
    keepSixSources
      xFirst xSecond yFirst ySecond zFirst zSecond
  have sourceContributors :
      source.toList.filter
          (contributesTo substitution targetKeep) =
        source.toList.filter sourceKeep :=
    filter_eq_of_predicate_eq_on_members
      source.toList
      (contributesTo substitution targetKeep) sourceKeep
      contributors
  have otherContributors :
      other.toList.filter
          (contributesTo substitution targetKeep) =
        other.toList.filter sourceKeep := by
    apply filter_eq_of_predicate_eq_on_members
    intro sourceLetter member
    have sourceMember :=
      (valid_identity_support_iff valid sourceLetter).mpr member
    exact contributors sourceLetter sourceMember
  have sourceStable := stable other valid
  apply bind_projection_stable_of_contributor_filter
  rw [sourceContributors, otherContributors, sourceStable]

/-- Complete target-projection transport when all three distinguished
markers have two distinct linear source preimages. -/
theorem bind_projection_stable_of_LLLPerkinsPreimages
    {source other target : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : source.bind substitution = target)
    (pattern : OccurrencePattern extra target.toList)
    (valid :
      (Identity.mk source other).SatisfiedBy table.semigroup)
    {firstBlock secondBlock : List Nat}
    (targetShape :
      target.toList =
        [0, 1] ++ firstBlock ++ [0] ++ secondBlock ++ [1])
    {z : Nat}
    (xLinear :
      LinearTwoBlockMarkerPreimages source substitution
        [] [0] ([0, 1] ++ firstBlock) [0] 0)
    (yLinear :
      LinearTwoBlockMarkerPreimages source substitution
        [0] [1]
        ([0, 1] ++ firstBlock ++ [0] ++ secondBlock) [1] 1)
    (zLinear :
      LinearTwoBlockMarkerPreimages source substitution
        [0, 1] firstBlock
        ([0, 1] ++ firstBlock ++ [0]) secondBlock z) :
    (source.bind substitution).toList.filter (keepTriple 0 1 z) =
      (other.bind substitution).toList.filter
        (keepTriple 0 1 z) := by
  rcases xLinear with
    ⟨xFirstOwner, xSecondOwner, xFirstSource, xSecondSource,
      xFirstPreimage, xSecondPreimage, xFirstAt, xSecondAt,
      xFirstImage, xSecondImage, xFirstCount, xSecondCount⟩
  rcases yLinear with
    ⟨yFirstOwner, ySecondOwner, yFirstSource, ySecondSource,
      yFirstPreimage, ySecondPreimage, yFirstAt, ySecondAt,
      yFirstImage, ySecondImage, yFirstCount, ySecondCount⟩
  rcases zLinear with
    ⟨zFirstOwner, zSecondOwner, zFirstSource, zSecondSource,
      zFirstPreimage, zSecondPreimage, zFirstAt, zSecondAt,
      zFirstImage, zSecondImage, zFirstCount, zSecondCount⟩
  have stable :
      KeepSixStable source
        xFirstSource xSecondSource
        yFirstSource ySecondSource
        zFirstSource zSecondSource :=
    keepSixStable_LLL
      xFirstCount xSecondCount yFirstCount ySecondCount
      zFirstCount zSecondCount
  have contributors :=
    contributors_eq_keepSixSources_of_markerPreimages
      mapped pattern targetShape
      xFirstPreimage xSecondPreimage
      xFirstAt xSecondAt xFirstImage xSecondImage
      (Or.inl ⟨xFirstCount, xSecondCount⟩)
      yFirstPreimage ySecondPreimage
      yFirstAt ySecondAt yFirstImage ySecondImage
      (Or.inl ⟨yFirstCount, ySecondCount⟩)
      zFirstPreimage zSecondPreimage
      zFirstAt zSecondAt zFirstImage zSecondImage
      (Or.inl ⟨zFirstCount, zSecondCount⟩)
  exact
    bind_projection_stable_of_keepSixStable substitution
      (keepTriple 0 1 z) valid stable contributors

/-- Complete target-projection transport when `x` and `y` have linear
preimages and `z` has one repeated source preimage. -/
theorem bind_projection_stable_of_LLRPerkinsPreimages
    {source other target : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : source.bind substitution = target)
    (pattern : OccurrencePattern extra target.toList)
    (valid :
      (Identity.mk source other).SatisfiedBy table.semigroup)
    {firstBlock secondBlock : List Nat}
    (targetShape :
      target.toList =
        [0, 1] ++ firstBlock ++ [0] ++ secondBlock ++ [1])
    {z : Nat}
    (xLinear :
      LinearTwoBlockMarkerPreimages source substitution
        [] [0] ([0, 1] ++ firstBlock) [0] 0)
    (yLinear :
      LinearTwoBlockMarkerPreimages source substitution
        [0] [1]
        ([0, 1] ++ firstBlock ++ [0] ++ secondBlock) [1] 1)
    (zRepeated :
      RepeatedTwoBlockMarkerPreimages source substitution
        [0, 1] firstBlock
        ([0, 1] ++ firstBlock ++ [0]) secondBlock z) :
    (source.bind substitution).toList.filter (keepTriple 0 1 z) =
      (other.bind substitution).toList.filter
        (keepTriple 0 1 z) := by
  rcases xLinear with
    ⟨xFirstOwner, xSecondOwner, xFirstSource, xSecondSource,
      xFirstPreimage, xSecondPreimage, xFirstAt, xSecondAt,
      xFirstImage, xSecondImage, xFirstCount, xSecondCount⟩
  rcases yLinear with
    ⟨yFirstOwner, ySecondOwner, yFirstSource, ySecondSource,
      yFirstPreimage, ySecondPreimage, yFirstAt, ySecondAt,
      yFirstImage, ySecondImage, yFirstCount, ySecondCount⟩
  rcases zRepeated with
    ⟨zFirstOwner, zSecondOwner, sourceZ,
      zFirstPreimage, zSecondPreimage, zFirstAt, zSecondAt,
      zImage, zCount⟩
  have ownerChain :=
    perkinsDistinguishedOwnerChain mapped targetShape
      xFirstPreimage yFirstPreimage zFirstPreimage
      xSecondPreimage zSecondPreimage ySecondPreimage
  have zProjection :=
    sandwichProjection_of_orderedOwners
      zCount xSecondCount zFirstAt xSecondAt zSecondAt
      ownerChain.2.2.1 ownerChain.2.2.2.1
  have zStable : SingletonStable source sourceZ :=
    singletonStable_of_sandwich_shape
      zProjection.1 zProjection.2
  have stable :
      KeepSixStable source
        xFirstSource xSecondSource
        yFirstSource ySecondSource sourceZ sourceZ :=
    keepSixStable_LLR
      xFirstCount xSecondCount yFirstCount ySecondCount
      zCount zStable
  have contributors :=
    contributors_eq_keepSixSources_of_markerPreimages
      mapped pattern targetShape
      xFirstPreimage xSecondPreimage
      xFirstAt xSecondAt xFirstImage xSecondImage
      (Or.inl ⟨xFirstCount, xSecondCount⟩)
      yFirstPreimage ySecondPreimage
      yFirstAt ySecondAt yFirstImage ySecondImage
      (Or.inl ⟨yFirstCount, ySecondCount⟩)
      zFirstPreimage zSecondPreimage
      zFirstAt zSecondAt zImage zImage
      (Or.inr ⟨rfl, zCount⟩)
  exact
    bind_projection_stable_of_keepSixStable substitution
      (keepTriple 0 1 z) valid stable contributors

/-- Complete target-projection transport when `x` and `z` have linear
preimages and `y` has one repeated source preimage. -/
theorem bind_projection_stable_of_LRLPerkinsPreimages
    {source other target : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : source.bind substitution = target)
    (pattern : OccurrencePattern extra target.toList)
    (valid :
      (Identity.mk source other).SatisfiedBy table.semigroup)
    {firstBlock secondBlock : List Nat}
    (targetShape :
      target.toList =
        [0, 1] ++ firstBlock ++ [0] ++ secondBlock ++ [1])
    {z : Nat}
    (xLinear :
      LinearTwoBlockMarkerPreimages source substitution
        [] [0] ([0, 1] ++ firstBlock) [0] 0)
    (yRepeated :
      RepeatedTwoBlockMarkerPreimages source substitution
        [0] [1]
        ([0, 1] ++ firstBlock ++ [0] ++ secondBlock) [1] 1)
    (zLinear :
      LinearTwoBlockMarkerPreimages source substitution
        [0, 1] firstBlock
        ([0, 1] ++ firstBlock ++ [0]) secondBlock z) :
    (source.bind substitution).toList.filter (keepTriple 0 1 z) =
      (other.bind substitution).toList.filter
        (keepTriple 0 1 z) := by
  rcases xLinear with
    ⟨xFirstOwner, xSecondOwner, xFirstSource, xSecondSource,
      xFirstPreimage, xSecondPreimage, xFirstAt, xSecondAt,
      xFirstImage, xSecondImage, xFirstCount, xSecondCount⟩
  rcases yRepeated with
    ⟨yFirstOwner, ySecondOwner, sourceY,
      yFirstPreimage, ySecondPreimage, yFirstAt, ySecondAt,
      yImage, yCount⟩
  rcases zLinear with
    ⟨zFirstOwner, zSecondOwner, zFirstSource, zSecondSource,
      zFirstPreimage, zSecondPreimage, zFirstAt, zSecondAt,
      zFirstImage, zSecondImage, zFirstCount, zSecondCount⟩
  have ownerChain :=
    perkinsDistinguishedOwnerChain mapped targetShape
      xFirstPreimage yFirstPreimage zFirstPreimage
      xSecondPreimage zSecondPreimage ySecondPreimage
  have zFirstBeforeYSecond : zFirstOwner ≤ ySecondOwner :=
    Nat.le_trans ownerChain.2.2.1
      (Nat.le_trans ownerChain.2.2.2.1
        ownerChain.2.2.2.2)
  have yProjection :=
    sandwichProjection_of_orderedOwners
      yCount zFirstCount yFirstAt zFirstAt ySecondAt
      ownerChain.2.1 zFirstBeforeYSecond
  have yStable : SingletonStable source sourceY :=
    singletonStable_of_sandwich_shape
      yProjection.1 yProjection.2
  have stable :
      KeepSixStable source
        xFirstSource xSecondSource sourceY sourceY
        zFirstSource zSecondSource :=
    keepSixStable_LRL
      xFirstCount xSecondCount yCount yStable
      zFirstCount zSecondCount
  have contributors :=
    contributors_eq_keepSixSources_of_markerPreimages
      mapped pattern targetShape
      xFirstPreimage xSecondPreimage
      xFirstAt xSecondAt xFirstImage xSecondImage
      (Or.inl ⟨xFirstCount, xSecondCount⟩)
      yFirstPreimage ySecondPreimage
      yFirstAt ySecondAt yImage yImage
      (Or.inr ⟨rfl, yCount⟩)
      zFirstPreimage zSecondPreimage
      zFirstAt zSecondAt zFirstImage zSecondImage
      (Or.inl ⟨zFirstCount, zSecondCount⟩)
  exact
    bind_projection_stable_of_keepSixStable substitution
      (keepTriple 0 1 z) valid stable contributors

/-- Complete target-projection transport when `y` and `z` have linear
preimages and `x` has one repeated source preimage. -/
theorem bind_projection_stable_of_RLLPerkinsPreimages
    {source other target : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : source.bind substitution = target)
    (pattern : OccurrencePattern extra target.toList)
    (valid :
      (Identity.mk source other).SatisfiedBy table.semigroup)
    {firstBlock secondBlock : List Nat}
    (targetShape :
      target.toList =
        [0, 1] ++ firstBlock ++ [0] ++ secondBlock ++ [1])
    {z : Nat}
    (xRepeated :
      RepeatedTwoBlockMarkerPreimages source substitution
        [] [0] ([0, 1] ++ firstBlock) [0] 0)
    (yLinear :
      LinearTwoBlockMarkerPreimages source substitution
        [0] [1]
        ([0, 1] ++ firstBlock ++ [0] ++ secondBlock) [1] 1)
    (zLinear :
      LinearTwoBlockMarkerPreimages source substitution
        [0, 1] firstBlock
        ([0, 1] ++ firstBlock ++ [0]) secondBlock z) :
    (source.bind substitution).toList.filter (keepTriple 0 1 z) =
      (other.bind substitution).toList.filter
        (keepTriple 0 1 z) := by
  rcases xRepeated with
    ⟨xFirstOwner, xSecondOwner, sourceX,
      xFirstPreimage, xSecondPreimage, xFirstAt, xSecondAt,
      xImage, xCount⟩
  rcases yLinear with
    ⟨yFirstOwner, ySecondOwner, yFirstSource, ySecondSource,
      yFirstPreimage, ySecondPreimage, yFirstAt, ySecondAt,
      yFirstImage, ySecondImage, yFirstCount, ySecondCount⟩
  rcases zLinear with
    ⟨zFirstOwner, zSecondOwner, zFirstSource, zSecondSource,
      zFirstPreimage, zSecondPreimage, zFirstAt, zSecondAt,
      zFirstImage, zSecondImage, zFirstCount, zSecondCount⟩
  have ownerChain :=
    perkinsDistinguishedOwnerChain mapped targetShape
      xFirstPreimage yFirstPreimage zFirstPreimage
      xSecondPreimage zSecondPreimage ySecondPreimage
  have yFirstBeforeXSecond : yFirstOwner ≤ xSecondOwner :=
    Nat.le_trans ownerChain.2.1 ownerChain.2.2.1
  have xProjection :=
    sandwichProjection_of_orderedOwners
      xCount yFirstCount xFirstAt yFirstAt xSecondAt
      ownerChain.1 yFirstBeforeXSecond
  have xStable : SingletonStable source sourceX :=
    singletonStable_of_sandwich_shape
      xProjection.1 xProjection.2
  have stable :
      KeepSixStable source
        sourceX sourceX yFirstSource ySecondSource
        zFirstSource zSecondSource :=
    keepSixStable_RLL
      xCount xStable yFirstCount ySecondCount
      zFirstCount zSecondCount
  have contributors :=
    contributors_eq_keepSixSources_of_markerPreimages
      mapped pattern targetShape
      xFirstPreimage xSecondPreimage
      xFirstAt xSecondAt xImage xImage
      (Or.inr ⟨rfl, xCount⟩)
      yFirstPreimage ySecondPreimage
      yFirstAt ySecondAt yFirstImage ySecondImage
      (Or.inl ⟨yFirstCount, ySecondCount⟩)
      zFirstPreimage zSecondPreimage
      zFirstAt zSecondAt zFirstImage zSecondImage
      (Or.inl ⟨zFirstCount, zSecondCount⟩)
  exact
    bind_projection_stable_of_keepSixStable substitution
      (keepTriple 0 1 z) valid stable contributors

/-- Complete target-projection transport when `x` has linear preimages and
`y,z` have repeated source preimages. -/
theorem bind_projection_stable_of_LRRPerkinsPreimages
    {source other target : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : source.bind substitution = target)
    (pattern : OccurrencePattern extra target.toList)
    (valid :
      (Identity.mk source other).SatisfiedBy table.semigroup)
    {firstBlock secondBlock : List Nat}
    (targetShape :
      target.toList =
        [0, 1] ++ firstBlock ++ [0] ++ secondBlock ++ [1])
    {z : Nat}
    (xLinear :
      LinearTwoBlockMarkerPreimages source substitution
        [] [0] ([0, 1] ++ firstBlock) [0] 0)
    (yRepeated :
      RepeatedTwoBlockMarkerPreimages source substitution
        [0] [1]
        ([0, 1] ++ firstBlock ++ [0] ++ secondBlock) [1] 1)
    (zRepeated :
      RepeatedTwoBlockMarkerPreimages source substitution
        [0, 1] firstBlock
        ([0, 1] ++ firstBlock ++ [0]) secondBlock z) :
    (source.bind substitution).toList.filter (keepTriple 0 1 z) =
      (other.bind substitution).toList.filter
        (keepTriple 0 1 z) := by
  rcases xLinear with
    ⟨xFirstOwner, xSecondOwner, xFirstSource, xSecondSource,
      xFirstPreimage, xSecondPreimage, xFirstAt, xSecondAt,
      xFirstImage, xSecondImage, xFirstCount, xSecondCount⟩
  rcases yRepeated with
    ⟨yFirstOwner, ySecondOwner, sourceY,
      yFirstPreimage, ySecondPreimage, yFirstAt, ySecondAt,
      yImage, yCount⟩
  rcases zRepeated with
    ⟨zFirstOwner, zSecondOwner, sourceZ,
      zFirstPreimage, zSecondPreimage, zFirstAt, zSecondAt,
      zImage, zCount⟩
  have ownerChain :=
    perkinsDistinguishedOwnerChain mapped targetShape
      xFirstPreimage yFirstPreimage zFirstPreimage
      xSecondPreimage zSecondPreimage ySecondPreimage
  have stable :
      KeepSixStable source
        xFirstSource xSecondSource
        sourceY sourceY sourceZ sourceZ := by
    by_cases yzDifferent : sourceY = sourceZ
    · subst sourceZ
      have yFirstBeforeXSecond : yFirstOwner ≤ xSecondOwner :=
        Nat.le_trans ownerChain.2.1 ownerChain.2.2.1
      have xSecondBeforeYSecond : xSecondOwner ≤ ySecondOwner :=
        Nat.le_trans ownerChain.2.2.2.1
          ownerChain.2.2.2.2
      have yProjection :=
        sandwichProjection_of_orderedOwners
          yCount xSecondCount yFirstAt xSecondAt ySecondAt
          yFirstBeforeXSecond xSecondBeforeYSecond
      have yStable : SingletonStable source sourceY :=
        singletonStable_of_sandwich_shape
          yProjection.1 yProjection.2
      exact
        keepSixStable_LRR
          xFirstCount xSecondCount
          yCount yStable zCount yStable
          (fun different => (different rfl).elim)
    · have yNeXSecond : sourceY ≠ xSecondSource := by
        intro equality
        rw [← equality, yCount] at xSecondCount
        omega
      have zNeXSecond : sourceZ ≠ xSecondSource := by
        intro equality
        rw [← equality, zCount] at xSecondCount
        omega
      have distinct :
          [sourceY, sourceZ, xSecondSource].Nodup := by
        simp [yzDifferent, yNeXSecond, zNeXSecond]
      have projection :=
        palindromicTripleProjection_of_orderedOwners
          distinct yCount zCount xSecondCount
          yFirstAt zFirstAt xSecondAt zSecondAt ySecondAt
          ⟨ownerChain.2.1, ownerChain.2.2.1,
            ownerChain.2.2.2.1, ownerChain.2.2.2.2⟩
      have isoterm :=
        palindromicTriple_isoterm distinct
      have sourceFiltered :
          source.toList.filter
              (keepTriple sourceY sourceZ xSecondSource) =
            (palindromicTripleIsotermWord
              sourceY sourceZ xSecondSource).toList := by
        simpa [palindromicTripleIsotermWord] using projection
      have yStable : SingletonStable source sourceY := by
        apply singletonStable_of_filtered_isoterm isoterm
          (keepTriple sourceY sourceZ xSecondSource)
          sourceFiltered
        intro letter kept
        simp [singletonKeep] at kept
        subst letter
        simp [keepTriple]
      have zStable : SingletonStable source sourceZ := by
        apply singletonStable_of_filtered_isoterm isoterm
          (keepTriple sourceY sourceZ xSecondSource)
          sourceFiltered
        intro letter kept
        simp [singletonKeep] at kept
        subst letter
        simp [keepTriple]
      have yzStable :
          PairStable source sourceY sourceZ := by
        apply pairStable_of_filtered_isoterm isoterm
          (keepTriple sourceY sourceZ xSecondSource)
          sourceFiltered
        intro letter kept
        simp [pairKeep] at kept
        rcases kept with rfl | rfl <;> simp [keepTriple]
      exact
        keepSixStable_LRR
          xFirstCount xSecondCount
          yCount yStable zCount zStable
          (fun _ => yzStable)
  have contributors :=
    contributors_eq_keepSixSources_of_markerPreimages
      mapped pattern targetShape
      xFirstPreimage xSecondPreimage
      xFirstAt xSecondAt xFirstImage xSecondImage
      (Or.inl ⟨xFirstCount, xSecondCount⟩)
      yFirstPreimage ySecondPreimage
      yFirstAt ySecondAt yImage yImage
      (Or.inr ⟨rfl, yCount⟩)
      zFirstPreimage zSecondPreimage
      zFirstAt zSecondAt zImage zImage
      (Or.inr ⟨rfl, zCount⟩)
  exact
    bind_projection_stable_of_keepSixStable substitution
      (keepTriple 0 1 z) valid stable contributors

/-- Complete target-projection transport when `y` has linear preimages and
`x,z` have repeated source preimages. -/
theorem bind_projection_stable_of_RLRPerkinsPreimages
    {source other target : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : source.bind substitution = target)
    (pattern : OccurrencePattern extra target.toList)
    (valid :
      (Identity.mk source other).SatisfiedBy table.semigroup)
    {firstBlock secondBlock : List Nat}
    (targetShape :
      target.toList =
        [0, 1] ++ firstBlock ++ [0] ++ secondBlock ++ [1])
    {z : Nat}
    (xRepeated :
      RepeatedTwoBlockMarkerPreimages source substitution
        [] [0] ([0, 1] ++ firstBlock) [0] 0)
    (yLinear :
      LinearTwoBlockMarkerPreimages source substitution
        [0] [1]
        ([0, 1] ++ firstBlock ++ [0] ++ secondBlock) [1] 1)
    (zRepeated :
      RepeatedTwoBlockMarkerPreimages source substitution
        [0, 1] firstBlock
        ([0, 1] ++ firstBlock ++ [0]) secondBlock z) :
    (source.bind substitution).toList.filter (keepTriple 0 1 z) =
      (other.bind substitution).toList.filter
        (keepTriple 0 1 z) := by
  rcases xRepeated with
    ⟨xFirstOwner, xSecondOwner, sourceX,
      xFirstPreimage, xSecondPreimage, xFirstAt, xSecondAt,
      xImage, xCount⟩
  rcases yLinear with
    ⟨yFirstOwner, ySecondOwner, yFirstSource, ySecondSource,
      yFirstPreimage, ySecondPreimage, yFirstAt, ySecondAt,
      yFirstImage, ySecondImage, yFirstCount, ySecondCount⟩
  rcases zRepeated with
    ⟨zFirstOwner, zSecondOwner, sourceZ,
      zFirstPreimage, zSecondPreimage, zFirstAt, zSecondAt,
      zImage, zCount⟩
  have ownerChain :=
    perkinsDistinguishedOwnerChain mapped targetShape
      xFirstPreimage yFirstPreimage zFirstPreimage
      xSecondPreimage zSecondPreimage ySecondPreimage
  have stable :
      KeepSixStable source
        sourceX sourceX yFirstSource ySecondSource
        sourceZ sourceZ := by
    by_cases xzDifferent : sourceX = sourceZ
    · subst sourceZ
      have xProjection :=
        sandwichProjection_of_orderedOwners
          xCount yFirstCount xFirstAt yFirstAt zFirstAt
          ownerChain.1 ownerChain.2.1
      have xStable : SingletonStable source sourceX :=
        singletonStable_of_sandwich_shape
          xProjection.1 xProjection.2
      exact
        keepSixStable_RLR
          xCount xStable yFirstCount ySecondCount
          zCount xStable
          (fun different => (different rfl).elim)
    · have xNeYFirst : sourceX ≠ yFirstSource := by
        intro equality
        rw [← equality, xCount] at yFirstCount
        omega
      have zNeYFirst : sourceZ ≠ yFirstSource := by
        intro equality
        rw [← equality, zCount] at yFirstCount
        omega
      have distinct :
          [sourceX, sourceZ, yFirstSource].Nodup := by
        simp [xzDifferent, xNeYFirst, zNeYFirst]
      have projection :=
        alternatingTripleProjection_of_orderedOwners
          distinct xCount zCount yFirstCount
          xFirstAt yFirstAt zFirstAt xSecondAt zSecondAt
          ⟨ownerChain.1, ownerChain.2.1,
            ownerChain.2.2.1, ownerChain.2.2.2.1⟩
      have isoterm :=
        alternatingTriple_isoterm distinct
      have sourceFiltered :
          source.toList.filter
              (keepTriple sourceX sourceZ yFirstSource) =
            (alternatingTripleIsotermWord
              sourceX sourceZ yFirstSource).toList := by
        simpa [alternatingTripleIsotermWord] using projection
      have xStable : SingletonStable source sourceX := by
        apply singletonStable_of_filtered_isoterm isoterm
          (keepTriple sourceX sourceZ yFirstSource)
          sourceFiltered
        intro letter kept
        simp [singletonKeep] at kept
        subst letter
        simp [keepTriple]
      have zStable : SingletonStable source sourceZ := by
        apply singletonStable_of_filtered_isoterm isoterm
          (keepTriple sourceX sourceZ yFirstSource)
          sourceFiltered
        intro letter kept
        simp [singletonKeep] at kept
        subst letter
        simp [keepTriple]
      have xzStable :
          PairStable source sourceX sourceZ := by
        apply pairStable_of_filtered_isoterm isoterm
          (keepTriple sourceX sourceZ yFirstSource)
          sourceFiltered
        intro letter kept
        simp [pairKeep] at kept
        rcases kept with rfl | rfl <;> simp [keepTriple]
      exact
        keepSixStable_RLR
          xCount xStable yFirstCount ySecondCount
          zCount zStable
          (fun _ => xzStable)
  have contributors :=
    contributors_eq_keepSixSources_of_markerPreimages
      mapped pattern targetShape
      xFirstPreimage xSecondPreimage
      xFirstAt xSecondAt xImage xImage
      (Or.inr ⟨rfl, xCount⟩)
      yFirstPreimage ySecondPreimage
      yFirstAt ySecondAt yFirstImage ySecondImage
      (Or.inl ⟨yFirstCount, ySecondCount⟩)
      zFirstPreimage zSecondPreimage
      zFirstAt zSecondAt zImage zImage
      (Or.inr ⟨rfl, zCount⟩)
  exact
    bind_projection_stable_of_keepSixStable substitution
      (keepTriple 0 1 z) valid stable contributors

/-- Complete target-projection transport when `z` has linear preimages and
`x,y` have repeated source preimages. -/
theorem bind_projection_stable_of_RRLPerkinsPreimages
    {source other target : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : source.bind substitution = target)
    (pattern : OccurrencePattern extra target.toList)
    (valid :
      (Identity.mk source other).SatisfiedBy table.semigroup)
    {firstBlock secondBlock : List Nat}
    (targetShape :
      target.toList =
        [0, 1] ++ firstBlock ++ [0] ++ secondBlock ++ [1])
    {z : Nat}
    (xRepeated :
      RepeatedTwoBlockMarkerPreimages source substitution
        [] [0] ([0, 1] ++ firstBlock) [0] 0)
    (yRepeated :
      RepeatedTwoBlockMarkerPreimages source substitution
        [0] [1]
        ([0, 1] ++ firstBlock ++ [0] ++ secondBlock) [1] 1)
    (zLinear :
      LinearTwoBlockMarkerPreimages source substitution
        [0, 1] firstBlock
        ([0, 1] ++ firstBlock ++ [0]) secondBlock z) :
    (source.bind substitution).toList.filter (keepTriple 0 1 z) =
      (other.bind substitution).toList.filter
        (keepTriple 0 1 z) := by
  rcases xRepeated with
    ⟨xFirstOwner, xSecondOwner, sourceX,
      xFirstPreimage, xSecondPreimage, xFirstAt, xSecondAt,
      xImage, xCount⟩
  rcases yRepeated with
    ⟨yFirstOwner, ySecondOwner, sourceY,
      yFirstPreimage, ySecondPreimage, yFirstAt, ySecondAt,
      yImage, yCount⟩
  rcases zLinear with
    ⟨zFirstOwner, zSecondOwner, zFirstSource, zSecondSource,
      zFirstPreimage, zSecondPreimage, zFirstAt, zSecondAt,
      zFirstImage, zSecondImage, zFirstCount, zSecondCount⟩
  have ownerChain :=
    perkinsDistinguishedOwnerChain mapped targetShape
      xFirstPreimage yFirstPreimage zFirstPreimage
      xSecondPreimage zSecondPreimage ySecondPreimage
  have stable :
      KeepSixStable source
        sourceX sourceX sourceY sourceY
        zFirstSource zSecondSource := by
    by_cases xyDifferent : sourceX = sourceY
    · subst sourceY
      have xFirstBeforeZFirst : xFirstOwner ≤ zFirstOwner :=
        Nat.le_trans ownerChain.1 ownerChain.2.1
      have xProjection :=
        sandwichProjection_of_orderedOwners
          xCount zFirstCount xFirstAt zFirstAt xSecondAt
          xFirstBeforeZFirst ownerChain.2.2.1
      have xStable : SingletonStable source sourceX :=
        singletonStable_of_sandwich_shape
          xProjection.1 xProjection.2
      exact
        keepSixStable_RRL
          xCount xStable yCount xStable
          zFirstCount zSecondCount
          (fun different => (different rfl).elim)
    · have xNeZSecond : sourceX ≠ zSecondSource := by
        intro equality
        rw [← equality, xCount] at zSecondCount
        omega
      have yNeZSecond : sourceY ≠ zSecondSource := by
        intro equality
        rw [← equality, yCount] at zSecondCount
        omega
      have distinct :
          [sourceX, sourceY, zSecondSource].Nodup := by
        simp [xyDifferent, xNeZSecond, yNeZSecond]
      have yFirstBeforeXSecond : yFirstOwner ≤ xSecondOwner :=
        Nat.le_trans ownerChain.2.1 ownerChain.2.2.1
      have xBeforeY : xFirstOwner < yFirstOwner :=
        sourceAt_lt_of_le_of_ne xFirstAt yFirstAt
          xyDifferent ownerChain.1
      have yBeforeX : yFirstOwner < xSecondOwner :=
        sourceAt_lt_of_le_of_ne yFirstAt xSecondAt
          (Ne.symm xyDifferent) yFirstBeforeXSecond
      have xBeforeZ : xSecondOwner < zSecondOwner :=
        sourceAt_lt_of_le_of_ne xSecondAt zSecondAt
          xNeZSecond ownerChain.2.2.2.1
      have zBeforeY : zSecondOwner < ySecondOwner :=
        sourceAt_lt_of_le_of_ne zSecondAt ySecondAt
          (Ne.symm yNeZSecond) ownerChain.2.2.2.2
      have projection :=
        exact_five_owner_keepTriple_projection
          distinct xCount yCount zSecondCount
          xFirstAt yFirstAt xSecondAt zSecondAt ySecondAt
          ⟨xBeforeY, yBeforeX, xBeforeZ, zBeforeY⟩
          (by simp [keepTriple])
      have reverseDistinct :
          [sourceY, sourceX, zSecondSource].Nodup := by
        simp [Ne.symm xyDifferent, xNeZSecond, yNeZSecond]
      have isoterm :=
        Isoterm.reverse
          (alternatingTriple_isoterm reverseDistinct)
      have sourceFiltered :
          source.toList.filter
              (keepTriple sourceX sourceY zSecondSource) =
            ((alternatingTripleIsotermWord
              sourceY sourceX zSecondSource).reverse).toList := by
        rw [Word.toList_reverse]
        simpa [alternatingTripleIsotermWord] using projection
      have xStable : SingletonStable source sourceX := by
        apply singletonStable_of_filtered_isoterm isoterm
          (keepTriple sourceX sourceY zSecondSource)
          sourceFiltered
        intro letter kept
        simp [singletonKeep] at kept
        subst letter
        simp [keepTriple]
      have yStable : SingletonStable source sourceY := by
        apply singletonStable_of_filtered_isoterm isoterm
          (keepTriple sourceX sourceY zSecondSource)
          sourceFiltered
        intro letter kept
        simp [singletonKeep] at kept
        subst letter
        simp [keepTriple]
      have xyStable :
          PairStable source sourceX sourceY := by
        apply pairStable_of_filtered_isoterm isoterm
          (keepTriple sourceX sourceY zSecondSource)
          sourceFiltered
        intro letter kept
        simp [pairKeep] at kept
        rcases kept with rfl | rfl <;> simp [keepTriple]
      exact
        keepSixStable_RRL
          xCount xStable yCount yStable
          zFirstCount zSecondCount
          (fun _ => xyStable)
  have contributors :=
    contributors_eq_keepSixSources_of_markerPreimages
      mapped pattern targetShape
      xFirstPreimage xSecondPreimage
      xFirstAt xSecondAt xImage xImage
      (Or.inr ⟨rfl, xCount⟩)
      yFirstPreimage ySecondPreimage
      yFirstAt ySecondAt yImage yImage
      (Or.inr ⟨rfl, yCount⟩)
      zFirstPreimage zSecondPreimage
      zFirstAt zSecondAt zFirstImage zSecondImage
      (Or.inl ⟨zFirstCount, zSecondCount⟩)
  exact
    bind_projection_stable_of_keepSixStable substitution
      (keepTriple 0 1 z) valid stable contributors

/-- Stability of the complete source inverse set of a target projection
transports through a nonempty-word substitution.  The hypothesis
`contributors` identifies that inverse set with three source labels. -/
theorem bind_projection_stable_of_tripleStable
    {source other : Word Nat}
    (substitution : Nat → Word Nat)
    {sourceX sourceY sourceZ targetX targetY targetZ : Nat}
    (valid :
      (Identity.mk source other).SatisfiedBy table.semigroup)
    (stable : TripleStable source sourceX sourceY sourceZ)
    (contributors :
      ∀ sourceLetter, sourceLetter ∈ source.toList →
        contributesTo substitution
            (keepTriple targetX targetY targetZ) sourceLetter =
          keepTriple sourceX sourceY sourceZ sourceLetter) :
    (source.bind substitution).toList.filter
          (keepTriple targetX targetY targetZ) =
      (other.bind substitution).toList.filter
          (keepTriple targetX targetY targetZ) := by
  let targetKeep := keepTriple targetX targetY targetZ
  let sourceKeep := keepTriple sourceX sourceY sourceZ
  have sourceContributors :
      source.toList.filter
          (contributesTo substitution targetKeep) =
        source.toList.filter sourceKeep :=
    filter_eq_of_predicate_eq_on_members
      source.toList
      (contributesTo substitution targetKeep) sourceKeep
      contributors
  have otherContributors :
      other.toList.filter
          (contributesTo substitution targetKeep) =
        other.toList.filter sourceKeep := by
    apply filter_eq_of_predicate_eq_on_members
    intro sourceLetter member
    have sourceMember :=
      (valid_identity_support_iff valid sourceLetter).mpr member
    exact contributors sourceLetter sourceMember
  have sourceStable := stable other valid
  apply bind_projection_stable_of_contributor_filter
  rw [sourceContributors, otherContributors, sourceStable]

/-- Repeated preimages of three target markers transport any established
triple stability directly through the substitution.  Contributor
exclusivity is discharged by
`contributors_eq_keepTriple_of_repeatedSources`. -/
theorem bind_projection_stable_of_repeatedSources
    {source other target : Word Nat}
    (substitution : Nat → Word Nat)
    {sourceX sourceY sourceZ targetX targetY targetZ : Nat}
    (mapped : source.bind substitution = target)
    (pattern : OccurrencePattern extra target.toList)
    (valid :
      (Identity.mk source other).SatisfiedBy table.semigroup)
    (stable : TripleStable source sourceX sourceY sourceZ)
    (xCount : source.toList.count sourceX = 2)
    (yCount : source.toList.count sourceY = 2)
    (zCount : source.toList.count sourceZ = 2)
    (xImage : targetX ∈ (substitution sourceX).toList)
    (yImage : targetY ∈ (substitution sourceY).toList)
    (zImage : targetZ ∈ (substitution sourceZ).toList) :
    (source.bind substitution).toList.filter
          (keepTriple targetX targetY targetZ) =
      (other.bind substitution).toList.filter
          (keepTriple targetX targetY targetZ) := by
  exact
    bind_projection_stable_of_tripleStable substitution valid stable
      (contributors_eq_keepTriple_of_repeatedSources
        mapped pattern xCount yCount zCount xImage yImage zImage)

/-- Complete target-projection transport for the all-repeated branch of the
three-marker `2occ` split. -/
theorem bind_projection_stable_of_repeatedPerkinsPreimages
    {source other target : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : source.bind substitution = target)
    (pattern : OccurrencePattern extra target.toList)
    (valid :
      (Identity.mk source other).SatisfiedBy table.semigroup)
    {firstBlock secondBlock : List Nat}
    (firstPerm : firstBlock.Perm (middleVariables extra))
    (secondPerm : secondBlock.Perm (middleVariables extra))
    (targetShape :
      target.toList =
        [0, 1] ++ firstBlock ++ [0] ++ secondBlock ++ [1])
    (independent :
      IndependentBlockPreimageSelection source substitution
        extra firstBlock secondBlock)
    {z : Nat} (zMiddle : z ∈ middleVariables extra)
    (xRepeated :
      RepeatedTwoBlockMarkerPreimages source substitution
        [] [0] ([0, 1] ++ firstBlock) [0] 0)
    (yRepeated :
      RepeatedTwoBlockMarkerPreimages source substitution
        [0] [1]
        ([0, 1] ++ firstBlock ++ [0] ++ secondBlock) [1] 1)
    (zRepeated :
      RepeatedTwoBlockMarkerPreimages source substitution
        [0, 1] firstBlock
        ([0, 1] ++ firstBlock ++ [0]) secondBlock z) :
    (source.bind substitution).toList.filter (keepTriple 0 1 z) =
      (other.bind substitution).toList.filter (keepTriple 0 1 z) := by
  rcases
      tripleStable_of_repeatedPerkinsPreimages
        mapped pattern firstPerm secondPerm targetShape
        independent zMiddle xRepeated yRepeated zRepeated with
    ⟨sourceX, sourceY, sourceZ, stable,
      xCount, yCount, zCount, xImage, yImage, zImage⟩
  exact
    bind_projection_stable_of_repeatedSources substitution
      mapped pattern valid stable
      xCount yCount zCount xImage yImage zImage

/-- Complete eight-way target-projection transport for the distinguished
Perkins preimages. -/
theorem bind_projection_stable_of_PerkinsDistinguishedPreimages
    {source other target : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : source.bind substitution = target)
    (pattern : OccurrencePattern extra target.toList)
    (valid :
      (Identity.mk source other).SatisfiedBy table.semigroup)
    {firstBlock secondBlock : List Nat}
    (firstPerm : firstBlock.Perm (middleVariables extra))
    (secondPerm : secondBlock.Perm (middleVariables extra))
    (targetShape :
      target.toList =
        [0, 1] ++ firstBlock ++ [0] ++ secondBlock ++ [1])
    (independent :
      IndependentBlockPreimageSelection source substitution
        extra firstBlock secondBlock)
    (distinguished :
      PerkinsDistinguishedPreimages source substitution
        extra firstBlock secondBlock)
    {z : Nat} (zMiddle : z ∈ middleVariables extra) :
    (source.bind substitution).toList.filter (keepTriple 0 1 z) =
      (other.bind substitution).toList.filter
        (keepTriple 0 1 z) := by
  rcases distinguished.markerAlternatives zMiddle with
    ⟨xAlternative, yAlternative, zAlternative⟩
  rcases xAlternative with xLinear | xRepeated
  · rcases yAlternative with yLinear | yRepeated
    · rcases zAlternative with zLinear | zRepeated
      · exact
          bind_projection_stable_of_LLLPerkinsPreimages
            mapped pattern valid targetShape
            xLinear yLinear zLinear
      · exact
          bind_projection_stable_of_LLRPerkinsPreimages
            mapped pattern valid targetShape
            xLinear yLinear zRepeated
    · rcases zAlternative with zLinear | zRepeated
      · exact
          bind_projection_stable_of_LRLPerkinsPreimages
            mapped pattern valid targetShape
            xLinear yRepeated zLinear
      · exact
          bind_projection_stable_of_LRRPerkinsPreimages
            mapped pattern valid targetShape
            xLinear yRepeated zRepeated
  · rcases yAlternative with yLinear | yRepeated
    · rcases zAlternative with zLinear | zRepeated
      · exact
          bind_projection_stable_of_RLLPerkinsPreimages
            mapped pattern valid targetShape
            xRepeated yLinear zLinear
      · exact
          bind_projection_stable_of_RLRPerkinsPreimages
            mapped pattern valid targetShape
            xRepeated yLinear zRepeated
    · rcases zAlternative with zLinear | zRepeated
      · exact
          bind_projection_stable_of_RRLPerkinsPreimages
            mapped pattern valid targetShape
            xRepeated yRepeated zLinear
      · exact
          bind_projection_stable_of_repeatedPerkinsPreimages
            mapped pattern valid firstPerm secondPerm targetShape
            independent zMiddle xRepeated yRepeated zRepeated

end SemigroupBasis.Nonfinite.B2One
