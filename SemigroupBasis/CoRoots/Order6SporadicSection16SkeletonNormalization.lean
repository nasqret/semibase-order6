import SemigroupBasis.CoRoots.Order6SporadicSection16BlockNormalization

/-!
A total first-occurrence skeleton normalization for Lee and Zhang (2015),
Lemma 16.3, pp.50-51. Every nonsimple first occurrence is doubled using
(16.1a); blocks of non-first occurrences are collapsed using (16.1a-c).

The theorem is an actual derivation for EVERY finite word, not a plan with
an assumed normalization field. The later removal of redundant anchor
separators (condition IV) and semantic uniqueness remain separate steps.
-/

namespace SemigroupBasis.CoRoots.Order6SporadicSection16

open SemigroupBasis

def closeGap (anchor : Nat) (gap pending : List Nat) : List Nat :=
  if pending = [] then gap else gap ++ [anchor, anchor]

def nextBlock (letter : Nat) (rest : List Nat) : List Nat :=
  if letter ∈ rest then [letter, letter] else [letter]

private theorem closeGap_mem (anchor letter : Nat) (gap pending : List Nat) :
    letter ∈ [anchor, anchor] ++ closeGap anchor gap pending ↔
      letter ∈ [anchor, anchor] ++ gap := by
  by_cases empty : pending = []
  · simp [closeGap, empty]
  · simp [closeGap, empty, List.mem_append, or_comm]

private theorem closeGap_square (anchor letter : Nat) (gap pending : List Nat)
    (seen : SquareSeen letter ([anchor, anchor] ++ gap)) :
    SquareSeen letter ([anchor, anchor] ++ closeGap anchor gap pending) := by
  by_cases empty : pending = []
  · simpa [closeGap, empty] using seen
  · simpa [closeGap, empty, List.append_assoc] using squareSeen_append seen [anchor, anchor]

private theorem closeGap_derives (anchor : Nat) (gap pending : List Nat)
    (seen : ∀ letter ∈ pending, SquareSeen letter ([anchor, anchor] ++ gap)) :
    ListDerives ([anchor, anchor] ++ gap ++ pending)
      ([anchor, anchor] ++ closeGap anchor gap pending) := by
  by_cases empty : pending = []
  · subst pending
    simpa [closeGap] using S5_107.ListDerives.refl (basis := basis) ([anchor, anchor] ++ gap)
  · simpa [closeGap, empty, List.append_assoc] using collapseSquaredSeenBlock anchor gap pending empty seen

private theorem nextBlock_derives (letter : Nat) (rest : List Nat) :
    ListDerives (letter :: rest) (nextBlock letter rest ++ rest) := by
  by_cases again : letter ∈ rest
  · simpa [nextBlock, again] using duplicateFirstOfSeen letter rest again
  · simp only [nextBlock, if_neg again, List.singleton_append]
    exact S5_107.ListDerives.refl _

private theorem futureAfterNextBlock (stem rest : List Nat) (letter : Nat)
    (safe : ∀ x ∈ rest, x ∈ stem → SquareSeen x stem) :
    ∀ x ∈ rest, x ∈ stem ++ nextBlock letter rest →
      SquareSeen x (stem ++ nextBlock letter rest) := by
  intro x inRest inExtended
  rcases List.mem_append.mp inExtended with inStem | inBlock
  · exact squareSeen_append (safe x inRest inStem) _
  · by_cases again : letter ∈ rest
    · have equal : x = letter := by simpa [nextBlock, again] using inBlock
      subst x
      refine ⟨stem, [], ?_⟩
      simp [nextBlock, again]
    · have equal : x = letter := by simpa [nextBlock, again] using inBlock
      subst x
      exact False.elim (again inRest)

/-- The pending block contains only already-seen letters. Encountering a new
letter first closes that block, then records one or two copies of the letter.
The recursion decreases the unprocessed input list at every call. -/
def normalizeAux (anchor : Nat) (gap pending : List Nat) : List Nat → List Nat
  | [] => closeGap anchor gap pending
  | letter :: rest =>
      if letter ∈ [anchor, anchor] ++ gap then
        normalizeAux anchor gap (pending ++ [letter]) rest
      else
        normalizeAux anchor
          (closeGap anchor gap pending ++ nextBlock letter rest) [] rest

theorem normalizeAux_derives (anchor : Nat) (gap pending rest : List Nat)
    (pendingSafe : ∀ x ∈ pending, SquareSeen x ([anchor, anchor] ++ gap))
    (futureSafe : ∀ x ∈ rest, x ∈ [anchor, anchor] ++ gap →
      SquareSeen x ([anchor, anchor] ++ gap)) :
    ListDerives ([anchor, anchor] ++ gap ++ pending ++ rest)
      ([anchor, anchor] ++ normalizeAux anchor gap pending rest) := by
  induction rest generalizing gap pending with
  | nil =>
      simpa [normalizeAux] using closeGap_derives anchor gap pending pendingSafe
  | cons letter rest ih =>
      by_cases seen : letter ∈ [anchor, anchor] ++ gap
      · have pendingSafeNext : ∀ x ∈ pending ++ [letter],
            SquareSeen x ([anchor, anchor] ++ gap) := by
          intro x member
          rcases List.mem_append.mp member with old | last
          · exact pendingSafe x old
          · have equal : x = letter := by simpa using last
            subst x
            exact futureSafe letter (by simp) seen
        have futureSafeNext : ∀ x ∈ rest, x ∈ [anchor, anchor] ++ gap →
            SquareSeen x ([anchor, anchor] ++ gap) := by
          intro x member inStem
          exact futureSafe x (List.mem_cons_of_mem letter member) inStem
        have normalized := ih gap (pending ++ [letter]) pendingSafeNext futureSafeNext
        rw [normalizeAux, if_pos seen]
        simpa [List.append_assoc] using normalized
      · let closed := closeGap anchor gap pending
        let next := closed ++ nextBlock letter rest
        have closedSafe : ∀ x ∈ rest, x ∈ [anchor, anchor] ++ closed →
            SquareSeen x ([anchor, anchor] ++ closed) := by
          intro x member inClosed
          have inOriginal : x ∈ [anchor, anchor] ++ gap :=
            (closeGap_mem anchor x gap pending).mp inClosed
          exact closeGap_square anchor x gap pending
            (futureSafe x (List.mem_cons_of_mem letter member) inOriginal)
        have nextSafe : ∀ x ∈ rest, x ∈ [anchor, anchor] ++ next →
            SquareSeen x ([anchor, anchor] ++ next) := by
          simpa [next, List.append_assoc] using
            futureAfterNextBlock ([anchor, anchor] ++ closed) rest letter closedSafe
        have normalized : ListDerives ([anchor, anchor] ++ next ++ rest)
            ([anchor, anchor] ++ normalizeAux anchor next [] rest) := by
          simpa using ih next [] (by simp) nextSafe
        have closeStep : ListDerives ([anchor, anchor] ++ gap ++ pending ++ (letter :: rest))
            (([anchor, anchor] ++ closed) ++ (letter :: rest)) :=
          (closeGap_derives anchor gap pending pendingSafe).append (letter :: rest)
        have letterStep : ListDerives (([anchor, anchor] ++ closed) ++ (letter :: rest))
            ([anchor, anchor] ++ next ++ rest) := by
          simpa [next, List.append_assoc] using
            (nextBlock_derives letter rest).prepend ([anchor, anchor] ++ closed)
        rw [normalizeAux, if_neg seen]
        simpa [next, closed] using closeStep.trans (letterStep.trans normalized)

/-- Retain the initial simple-letter prefix, then normalize around the first
nonsimple letter. This is the pre-pruning skeleton, not the final canonical
form and not an assertion of completeness. -/
def normalizeSkeleton : List Nat → List Nat
  | [] => []
  | letter :: rest =>
      if letter ∈ rest then [letter, letter] ++ normalizeAux letter [] [] rest
      else letter :: normalizeSkeleton rest

theorem normalizeSkeleton_derives (letters : List Nat) :
    ListDerives letters (normalizeSkeleton letters) := by
  induction letters with
  | nil => exact S5_107.ListDerives.empty
  | cons letter rest ih =>
      by_cases again : letter ∈ rest
      · have futureSafe : ∀ x ∈ rest, x ∈ [letter, letter] ++ [] →
            SquareSeen x ([letter, letter] ++ []) := by
          intro x _ inStem
          have equal : x = letter := by simpa using inStem
          subst x
          exact ⟨[], [], rfl⟩
        have normalized : ListDerives (letter :: letter :: rest)
            ([letter, letter] ++ normalizeAux letter [] [] rest) := by
          simpa using normalizeAux_derives letter [] [] rest (by simp) futureSafe
        simpa [normalizeSkeleton, again] using
          (duplicateFirstOfSeen letter rest again).trans normalized
      · simpa [normalizeSkeleton, again] using ih.prepend [letter]

#print axioms normalizeAux_derives
#print axioms normalizeSkeleton_derives

end SemigroupBasis.CoRoots.Order6SporadicSection16
