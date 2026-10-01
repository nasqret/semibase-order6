import SemigroupBasis.CoRoots.Order6LeeLiP2G2
import SemigroupBasis.CoRoots.Order6LeeLiP2G2SeparationData
import SemigroupBasis.FiniteCertificate

/-!
# G2 injection: constructive NormalizationWitness + InvariantSeparation
  for the representative S6_11405  (msg-0187 items 1 and 2)

TARGET INTERFACE: `SemigroupBasis/CoRoots/Order6LeeLiP2G2.lean` at commit
`b3e4e98cc6e61632c11515119eb8e928886c4c00` (sha256 16763d143b28…).

EVIDENCE LABEL: source-complete and authoring-green on the pinned WMI
toolchain; this warm-cache build is development feedback, not v3 release
evidence.  The data file is machine-emitted and kernel-checkable (`decide`
on 132 fingerprints and four separator valuations).

ARCHITECTURE
* One reusable core lemma, `derivesRenderPerm`: permuting the interior of
  `render stem p2 p1` is derivable.  Proof by induction on `List.Perm`
  (swap ↦ `derivesInteriorSwap`; cons ↦ context prepend; trans ↦ trans).
  This single lemma powers stage 1 (sorting), seam A repositioning, and
  the post-padding re-sort of stage 3 — the `interiorSortLemma` requested
  in msg-0187, in its strongest form.
* Stage 2 = adjacent contraction on the sorted stem + seam-A contraction
  of the surviving interior copy of p2 across the penult boundary
  (fresh case only; the copy is unique because the stem is Nodup).
* Stage 3 = boundary duplication of the ≤ 2 missing stem letters
  (⊆ {p2, p1}, p1 only when p2 = p1), then `derivesRenderPerm` re-sorts.
* Separation: alphabet-generic merge-collapse onto ≤ 3 letters, then the
  132-canonical fingerprint injectivity (`fingerprints_nodup`, kernel).

API LEDGER (exact spellings assumed; mechanical to re-spell on WMI):
  Derives.prepend, Derives.appendRight, Derives.trans, Derives.symm,
  Derives.refl, Word.toList, Word.append, Word.singleton,
  Word.toList_injective, List.mergeSort, List.Perm (core),
  List.perm_mergeSort (mergeSort ~ original), List.sorted_mergeSort
  (pairwise ≤ of mergeSort), List.Perm.count_eq, List.Perm.mem_iff.
-/

namespace SemigroupBasis.CoRoots.Order6LeeLiP2G2.Injection

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6LeeLiP2G2

/-! ## Rendering and the split of a word into stem / p2 / p1 -/

/-- `render stem p2 p1` is the word `stem ++ [p2, p1]`. -/
def render (stem : List Nat) (p2 p1 : Nat) : Word Nat :=
  match stem with
  | [] => ⟨p2, [p1]⟩
  | head :: tail => ⟨head, tail ++ [p2, p1]⟩

theorem render_toList (stem : List Nat) (p2 p1 : Nat) :
    (render stem p2 p1).toList = stem ++ [p2, p1] := by
  cases stem <;> simp [render, Word.toList]

/-- Words of length ≥ 2 split as stem/p2/p1; shorter words are already
canonical singletons. -/
def split3 (word : Word Nat) : Option (List Nat × Nat × Nat) :=
  match word.toList.reverse with
  | p1 :: p2 :: revStem => some (revStem.reverse, p2, p1)
  | _ => none

theorem split3_render {word : Word Nat} {stem : List Nat} {p2 p1 : Nat}
    (h : split3 word = some (stem, p2, p1)) :
    word = render stem p2 p1 := by
  apply Word.toList_injective
  rw [render_toList]
  unfold split3 at h
  generalize reversedEq : word.toList.reverse = reversed at h
  cases reversed with
  | nil => simp at h
  | cons last rest =>
      cases rest with
      | nil => simp at h
      | cons penult revStem =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨stemEq, p2Eq, p1Eq⟩
          subst stem
          subst p2
          subst p1
          have restored := congrArg List.reverse reversedEq
          simpa [List.reverse_cons, List.append_assoc] using restored

/-! ## The reusable interior-permutation lemma (msg-0187 interiorSortLemma) -/

private def wordOf : List Nat → Nat → Word Nat
  | [], d => Word.singleton d
  | h :: t, _ => ⟨h, t⟩

private theorem singleton_append_render (head : Nat) (stem : List Nat)
    (p2 p1 : Nat) :
    Word.singleton head ++ render stem p2 p1 =
      render (head :: stem) p2 p1 := by
  apply Word.toList_injective
  simp only [Word.toList_append, Word.toList_singleton, render_toList]
  rfl

private theorem wordOf_append_singleton_toList (letters : List Nat) (last : Nat) :
    (wordOf (letters ++ [last]) last).toList = letters ++ [last] := by
  cases letters <;> simp [wordOf, Word.toList]

/-- Permuting the stem of a rendered word is derivable.  Induction over
`List.Perm`; the swap case is `derivesInteriorSwap` with the two swapped
letters as singleton factors, the remaining stem plus `p2` as the third
factor, and `p1` as the fourth — both trailing factors are nonempty for
EVERY stem, which is exactly why the interior of a rendered word is fully
sortable. -/
theorem derivesRenderPerm {stem stem' : List Nat} (perm : stem.Perm stem')
    (p2 p1 : Nat) :
    Derives basis (render stem p2 p1) (render stem' p2 p1) := by
  induction perm with
  | nil => exact Derives.refl _
  | cons head _ ih =>
      simpa only [singleton_append_render] using
        Derives.prepend (Word.singleton head) ih
  | swap a b rest =>
      have step := derivesInteriorSwap
        (Word.singleton b) (Word.singleton a)
        (wordOf (rest ++ [p2]) p2) (Word.singleton p1)
      have sourceEq :
          (((Word.singleton b ++ Word.singleton a) ++
              wordOf (rest ++ [p2]) p2) ++ Word.singleton p1) =
            render (b :: a :: rest) p2 p1 := by
        apply Word.toList_injective
        simp only [Word.toList_append, Word.toList_singleton,
          wordOf_append_singleton_toList, render_toList]
        simp [List.append_assoc]
      have targetEq :
          (((Word.singleton a ++ Word.singleton b) ++
              wordOf (rest ++ [p2]) p2) ++ Word.singleton p1) =
            render (a :: b :: rest) p2 p1 := by
        apply Word.toList_injective
        simp only [Word.toList_append, Word.toList_singleton,
          wordOf_append_singleton_toList, render_toList]
        simp [List.append_assoc]
      simpa only [sourceEq, targetEq] using step
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ## Stage 1: sort the interior -/

def leNat (a b : Nat) : Bool := decide (a ≤ b)

def sortInteriorFn (word : Word Nat) : Word Nat :=
  match split3 word with
  | some (stem, p2, p1) => render (stem.mergeSort leNat) p2 p1
  | none => word

theorem sortInterior_derives (word : Word Nat) :
    Derives basis word (sortInteriorFn word) := by
  cases h : split3 word with
  | none => simpa [sortInteriorFn, h] using Derives.refl word
  | some triple =>
      obtain ⟨stem, p2, p1⟩ := triple
      rw [sortInteriorFn, h]
      rw [split3_render h]
      exact derivesRenderPerm (List.mergeSort_perm stem leNat).symm p2 p1

/-! ## Stage 2: contract duplicates, then the seam-A contraction -/

/-- Remove adjacent duplicates from a sorted list. -/
def dedupSorted : List Nat → List Nat
  | [] => []
  | [a] => [a]
  | a :: b :: t => if a = b then dedupSorted (b :: t) else a :: dedupSorted (b :: t)

/-- One adjacent contraction inside the stem is derivable: with the stem
split as `l ++ a :: a :: r`, contract via `derivesLeftContraction ⟨a⟩ v`
where `v = r ++ [p2, p1]` (always nonempty), inside the left context `l`. -/
theorem derivesStemContraction (l r : List Nat) (a p2 p1 : Nat) :
    Derives basis
      (render (l ++ a :: a :: r) p2 p1)
      (render (l ++ a :: r) p2 p1) := by
  have step := derivesLeftContraction
    (Word.singleton a) (wordOf (r ++ [p2, p1]) p1)
  cases l with
  | nil =>
      cases r with
      | nil =>
          simpa [render, wordOf, Word.singleton, Word.append,
            List.append_assoc] using step
      | cons head tail =>
          simpa [render, wordOf, Word.singleton, Word.append,
            List.append_assoc] using step
  | cons head tail =>
      have prefixed := Derives.prepend (Word.mk head tail) step
      cases r with
      | nil =>
          simpa [render, wordOf, Word.singleton, Word.append,
            List.append_assoc] using prefixed
      | cons rHead rTail =>
          simpa [render, wordOf, Word.singleton, Word.append,
            List.append_assoc] using prefixed

/-- Seam A: the unique interior copy of `p2` (fresh case) is first moved to
the right end of the stem by `derivesRenderPerm`, then contracted across
the penult boundary: `(stem' ++ [p2])·p2·p1 → stem'·p2·p1` is
`derivesLeftContraction ⟨p2⟩ ⟨p1⟩` in left context `stem'`. -/
theorem derivesSeamContraction (stem' : List Nat) (p2 p1 : Nat) :
    Derives basis
      (render (stem' ++ [p2]) p2 p1)
      (render stem' p2 p1) := by
  have step := derivesLeftContraction
    (Word.singleton p2) (Word.singleton p1)
  cases stem' with
  | nil =>
      simpa [render, Word.singleton, Word.append, List.append_assoc] using step
  | cons head tail =>
      have prefixed := Derives.prepend (Word.mk head tail) step
      simpa [render, Word.singleton, Word.append, List.append_assoc] using prefixed

def collapseFn (word : Word Nat) : Word Nat :=
  match split3 word with
  | some (stem, p2, p1) =>
      let deduped := dedupSorted stem
      let seamless :=
        if (invariant word).fresh then
          deduped.filter (fun c => decide (c ≠ p2 ∧ c ≠ p1))
        else deduped
      render seamless p2 p1
  | none => word

/-! ## Stage 3: pad missing support (repeat case), re-sort, land on canonical -/

def padFn (word : Word Nat) : Word Nat :=
  match split3 word with
  | some (stem, p2, p1) =>
      if (invariant word).fresh then
        render stem p2 p1
      else
        -- repeat case: stem must become sortedSupport word
        render ((invariant word).support) p2 p1
  | none => word

/-- Boundary duplication inserts `p2` at the stem end:
`stem·p2·p1 → stem·p2·p2·p1` is `derivesLeftDuplication ⟨p2⟩ ⟨p1⟩` in
context `stem`; when `p2 = p1` the same instance reads `c·c → c·c·c`. -/
theorem derivesBoundaryPad (stem : List Nat) (p2 p1 : Nat) :
    Derives basis
      (render stem p2 p1)
      (render (stem ++ [p2]) p2 p1) :=
  (derivesSeamContraction stem p2 p1).symm

/-! ## List facts used by the witness -/

private theorem split3_render_eq (stem : List Nat) (p2 p1 : Nat) :
    split3 (render stem p2 p1) = some (stem, p2, p1) := by
  simp [split3, render_toList, List.reverse_append]

private theorem interior_render (stem : List Nat) (p2 p1 : Nat) :
    interior (render stem p2 p1) = stem := by
  simp [interior, render_toList]

private theorem trailingPair_render (stem : List Nat) (p2 p1 : Nat) :
    trailingPair (render stem p2 p1) = some (p2, p1) := by
  simp [trailingPair, render_toList, List.reverse_append]

private theorem finalLetter_render (stem : List Nat) (p2 p1 : Nat) :
    finalLetter (render stem p2 p1) = p1 := by
  simp [finalLetter, render_toList, List.reverse_append]

private theorem deduplicateSupport_mem (letter : Nat) (letters : List Nat) :
    letter ∈ deduplicateSupport letters ↔ letter ∈ letters := by
  induction letters with
  | nil => simp [deduplicateSupport]
  | cons head tail ih =>
      by_cases h : head ∈ tail
      · have headCase : letter = head → letter ∈ tail := by
          intro letterEq
          simpa [letterEq] using h
        simpa [deduplicateSupport, h, ih] using headCase
      · simp [deduplicateSupport, h, ih]

private theorem deduplicateSupport_nodup (letters : List Nat) :
    (deduplicateSupport letters).Nodup := by
  induction letters with
  | nil => simp [deduplicateSupport]
  | cons head tail ih =>
      by_cases h : head ∈ tail
      · simpa [deduplicateSupport, h] using ih
      · simp [deduplicateSupport, h, ih, deduplicateSupport_mem]

private theorem sortedSupport_mem (word : Word Nat) (letter : Nat) :
    letter ∈ sortedSupport word ↔ letter ∈ word.toList := by
  simp [sortedSupport, deduplicateSupport_mem]

private theorem sortedSupport_nodup (word : Word Nat) :
    (sortedSupport word).Nodup := by
  exact (List.mergeSort_perm (deduplicateSupport word.toList)
    (fun left right : Nat => decide (left ≤ right))).nodup_iff.mpr
      (deduplicateSupport_nodup _)

private theorem sortedSupport_sorted (word : Word Nat) :
    (sortedSupport word).Pairwise (· ≤ ·) := by
  unfold sortedSupport
  have sorted := List.pairwise_mergeSort
    (le := fun left right : Nat => decide (left ≤ right))
    (fun _ _ _ => by simp; omega)
    (fun _ _ => by simp; omega)
    (deduplicateSupport word.toList)
  exact sorted.imp (by intro _ _ h; simpa using h)

private theorem sortedNodup_eq_of_mem_iff
    {left right : List Nat}
    (leftSorted : left.Pairwise (· ≤ ·))
    (rightSorted : right.Pairwise (· ≤ ·))
    (leftNodup : left.Nodup)
    (rightNodup : right.Nodup)
    (member : ∀ letter, letter ∈ left ↔ letter ∈ right) :
    left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons head tail =>
          have : head ∈ ([] : List Nat) := (member head).mpr (by simp)
          simp at this
  | cons leftHead leftTail ih =>
      cases right with
      | nil =>
          have : leftHead ∈ ([] : List Nat) :=
            (member leftHead).mp (by simp)
          simp at this
      | cons rightHead rightTail =>
          have leftHeadMem : leftHead ∈ rightHead :: rightTail :=
            (member leftHead).mp (by simp)
          have rightHeadMem : rightHead ∈ leftHead :: leftTail :=
            (member rightHead).mpr (by simp)
          have leftLeRight : leftHead ≤ rightHead := by
            simp only [List.mem_cons] at rightHeadMem
            rcases rightHeadMem with rfl | memberTail
            · exact Nat.le_refl _
            · exact (List.pairwise_cons.mp leftSorted).1 _ memberTail
          have rightLeLeft : rightHead ≤ leftHead := by
            simp only [List.mem_cons] at leftHeadMem
            rcases leftHeadMem with rfl | memberTail
            · exact Nat.le_refl _
            · exact (List.pairwise_cons.mp rightSorted).1 _ memberTail
          have headsEq : leftHead = rightHead := Nat.le_antisymm leftLeRight rightLeLeft
          subst rightHead
          congr 1
          apply ih
          · exact (List.pairwise_cons.mp leftSorted).2
          · exact (List.pairwise_cons.mp rightSorted).2
          · exact (List.nodup_cons.mp leftNodup).2
          · exact (List.nodup_cons.mp rightNodup).2
          · intro letter
            have leftFresh := (List.nodup_cons.mp leftNodup).1
            have rightFresh := (List.nodup_cons.mp rightNodup).1
            constructor
            · intro memberLeft
              have letterNe : letter ≠ leftHead := by
                intro letterEq
                exact leftFresh (letterEq ▸ memberLeft)
              have memberFull : letter ∈ leftHead :: leftTail := by simp [memberLeft]
              have := (member letter).mp memberFull
              simpa [letterNe] using this
            · intro memberRight
              have letterNe : letter ≠ leftHead := by
                intro letterEq
                exact rightFresh (letterEq ▸ memberRight)
              have memberFull : letter ∈ leftHead :: rightTail := by simp [memberRight]
              have := (member letter).mpr memberFull
              simpa [letterNe] using this

private theorem sortedSupport_eq_of_mem_iff (left right : Word Nat)
    (member : ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList) :
    sortedSupport left = sortedSupport right := by
  apply sortedNodup_eq_of_mem_iff
  · exact sortedSupport_sorted left
  · exact sortedSupport_sorted right
  · exact sortedSupport_nodup left
  · exact sortedSupport_nodup right
  · intro letter
    simpa [sortedSupport_mem] using member letter

private theorem invariant_render_perm {left right : List Nat}
    (perm : left.Perm right) (p2 p1 : Nat) :
    invariant (render left p2 p1) = invariant (render right p2 p1) := by
  have supportEq :
      sortedSupport (render left p2 p1) =
        sortedSupport (render right p2 p1) := by
    apply sortedSupport_eq_of_mem_iff
    intro letter
    simp only [render_toList, List.mem_append, List.mem_cons,
      List.mem_singleton]
    constructor
    · rintro (memberLeft | letterEq | letterEq)
      · exact Or.inl (perm.mem_iff.mp memberLeft)
      · exact Or.inr (Or.inl letterEq)
      · exact Or.inr (Or.inr letterEq)
    · rintro (memberRight | letterEq | letterEq)
      · exact Or.inl (perm.mem_iff.mpr memberRight)
      · exact Or.inr (Or.inl letterEq)
      · exact Or.inr (Or.inr letterEq)
  have countEq :
      (render left p2 p1).toList.count p1 =
        (render right p2 p1).toList.count p1 := by
    simp [render_toList, perm.count_eq]
  simp [invariant, trailingPair_render, finalLetter_render, finalIsFresh,
    supportEq, countEq]

private theorem dedupSorted_mem (letter : Nat) (letters : List Nat) :
    letter ∈ dedupSorted letters ↔ letter ∈ letters := by
  induction letters with
  | nil => simp [dedupSorted]
  | cons head tail ih =>
      cases tail with
      | nil => simp [dedupSorted]
      | cons next rest =>
          by_cases headsEq : head = next
          · subst next
            simpa [dedupSorted, ih]
          · simp [dedupSorted, headsEq, ih]

private theorem dedupSorted_nodup_of_sorted {letters : List Nat}
    (sorted : letters.Pairwise (· ≤ ·)) :
    (dedupSorted letters).Nodup := by
  induction letters with
  | nil => simp [dedupSorted]
  | cons head tail ih =>
      cases tail with
      | nil => simp [dedupSorted]
      | cons next rest =>
          have sortedTail : (next :: rest).Pairwise (· ≤ ·) :=
            (List.pairwise_cons.mp sorted).2
          by_cases headsEq : head = next
          · subst next
            simpa [dedupSorted] using ih sortedTail
          · rw [dedupSorted]
            simp only [headsEq, ↓reduceIte]
            apply List.nodup_cons.mpr
            constructor
            · intro memberDeduped
              have memberTail : head ∈ next :: rest :=
                (dedupSorted_mem head (next :: rest)).mp memberDeduped
              have headLeNext : head ≤ next :=
                (List.pairwise_cons.mp sorted).1 next (by simp)
              have nextLeHead : next ≤ head := by
                simp only [List.mem_cons] at memberTail
                rcases memberTail with memberEq | memberRest
                · exact Nat.le_of_eq memberEq.symm
                · exact (List.pairwise_cons.mp sortedTail).1 head memberRest
              exact headsEq (Nat.le_antisymm headLeNext nextLeHead)
            · exact ih sortedTail

private theorem derivesDedupSorted (stem : List Nat) (p2 p1 : Nat) :
    Derives basis (render stem p2 p1)
      (render (dedupSorted stem) p2 p1) := by
  induction stem with
  | nil => exact Derives.refl _
  | cons head tail ih =>
      cases tail with
      | nil => exact Derives.refl _
      | cons next rest =>
          by_cases headsEq : head = next
          · subst next
            rw [dedupSorted]
            simp only [↓reduceIte]
            exact (derivesStemContraction [] rest head p2 p1).trans ih
          · rw [dedupSorted]
            simp only [headsEq, ↓reduceIte]
            simpa only [singleton_append_render] using
              Derives.prepend (Word.singleton head) ih

private theorem fresh_render_iff (stem : List Nat) (p2 p1 : Nat) :
    (invariant (render stem p2 p1)).fresh = true ↔
      p1 ∉ stem ∧ p2 ≠ p1 := by
  simp only [invariant, finalIsFresh, finalLetter_render]
  simp only [render_toList, List.count_append, decide_eq_true_eq]
  by_cases p1Member : p1 ∈ stem
  · have countPositive : 0 < stem.count p1 :=
      List.count_pos_iff.mpr p1Member
    constructor
    · intro countEq
      simp only [List.count_cons, List.count_nil] at countEq
      simp at countEq
      omega
    · intro facts
      exact False.elim (facts.1 p1Member)
  · have countZero : stem.count p1 = 0 := List.count_eq_zero.mpr p1Member
    by_cases pairEq : p2 = p1
    · subst p2
      simp [countZero]
    · simp [countZero, pairEq, p1Member]

private theorem invariant_render_eq_of_mem_and_fresh
    (left right : List Nat) (p2 p1 : Nat)
    (member : ∀ letter,
      letter ∈ (render left p2 p1).toList ↔
        letter ∈ (render right p2 p1).toList)
    (freshEq :
      (invariant (render left p2 p1)).fresh =
        (invariant (render right p2 p1)).fresh) :
    invariant (render left p2 p1) = invariant (render right p2 p1) := by
  have supportEq :
      sortedSupport (render left p2 p1) =
        sortedSupport (render right p2 p1) := by
    exact sortedSupport_eq_of_mem_iff _ _ member
  have finalFreshEq :
      finalIsFresh (render left p2 p1) =
        finalIsFresh (render right p2 p1) := by
    simpa [invariant, trailingPair_render, finalLetter_render] using freshEq
  simp [invariant, trailingPair_render, finalLetter_render, supportEq,
    finalFreshEq]

private theorem bool_eq_false_of_ne_true (value : Bool)
    (notTrue : value ≠ true) : value = false := by
  cases value <;> simp_all

private theorem collapse_sort_invariant (word : Word Nat) :
    invariant (collapseFn (sortInteriorFn word)) = invariant word := by
  cases h : split3 word with
  | none => simp [sortInteriorFn, collapseFn, h]
  | some triple =>
      obtain ⟨stem, p2, p1⟩ := triple
      let sortedStem := stem.mergeSort leNat
      let deduped := dedupSorted sortedStem
      have sortedInvariant :
          invariant (render sortedStem p2 p1) = invariant word := by
        rw [split3_render h]
        exact invariant_render_perm (List.mergeSort_perm stem leNat) p2 p1
      simp only [sortInteriorFn, h]
      change invariant (collapseFn (render sortedStem p2 p1)) = invariant word
      simp only [collapseFn, split3_render_eq]
      by_cases fresh : (invariant (render sortedStem p2 p1)).fresh = true
      · let filtered := deduped.filter
          (fun c => decide (c ≠ p2 ∧ c ≠ p1))
        have freshFacts := (fresh_render_iff sortedStem p2 p1).mp fresh
        have filteredFresh :
            (invariant (render filtered p2 p1)).fresh = true := by
          apply (fresh_render_iff filtered p2 p1).mpr
          constructor
          · simp [filtered]
          · exact freshFacts.2
        have fullMember : ∀ letter,
            letter ∈ (render filtered p2 p1).toList ↔
              letter ∈ (render sortedStem p2 p1).toList := by
          intro letter
          simp only [filtered, deduped, render_toList, List.mem_append,
            List.mem_cons, List.mem_nil_iff, or_false, List.mem_filter,
            decide_eq_true_eq]
          rw [dedupSorted_mem]
          constructor
          · rintro (⟨member, _, _⟩ | eqP2 | eqP1)
            · exact Or.inl member
            · exact Or.inr (Or.inl eqP2)
            · exact Or.inr (Or.inr eqP1)
          · rintro (member | eqP2 | eqP1)
            · by_cases letterEqP2 : letter = p2
              · exact Or.inr (Or.inl letterEqP2)
              · by_cases letterEqP1 : letter = p1
                · exact Or.inr (Or.inr letterEqP1)
                · exact Or.inl ⟨member, letterEqP2, letterEqP1⟩
            · exact Or.inr (Or.inl eqP2)
            · exact Or.inr (Or.inr eqP1)
        have collapsedInvariant := invariant_render_eq_of_mem_and_fresh
          filtered sortedStem p2 p1 fullMember (filteredFresh.trans fresh.symm)
        rw [if_pos fresh]
        exact collapsedInvariant.trans sortedInvariant
      · have dedupedFreshNot :
            (invariant (render deduped p2 p1)).fresh ≠ true := by
          intro dedupedFresh
          have dedupedFacts := (fresh_render_iff deduped p2 p1).mp dedupedFresh
          apply fresh
          apply (fresh_render_iff sortedStem p2 p1).mpr
          constructor
          · intro member
            exact dedupedFacts.1
              ((dedupSorted_mem p1 sortedStem).mpr member)
          · exact dedupedFacts.2
        have dedupedFreshFalse :
            (invariant (render deduped p2 p1)).fresh = false :=
          bool_eq_false_of_ne_true _ dedupedFreshNot
        have sortedFreshFalse :
            (invariant (render sortedStem p2 p1)).fresh = false :=
          bool_eq_false_of_ne_true _ fresh
        have fullMember : ∀ letter,
            letter ∈ (render deduped p2 p1).toList ↔
              letter ∈ (render sortedStem p2 p1).toList := by
          intro letter
          simp only [deduped, render_toList, List.mem_append, List.mem_cons,
            List.mem_nil_iff, or_false]
          rw [dedupSorted_mem]
        have collapsedInvariant := invariant_render_eq_of_mem_and_fresh
          deduped sortedStem p2 p1 fullMember
            (dedupedFreshFalse.trans sortedFreshFalse.symm)
        rw [if_neg fresh]
        exact collapsedInvariant.trans sortedInvariant

private theorem collapse_sort_nodup (word : Word Nat) :
    (interior (collapseFn (sortInteriorFn word))).Nodup := by
  cases h : split3 word with
  | none =>
      cases word with
      | mk head tail =>
          cases tail with
          | nil => simp [sortInteriorFn, collapseFn, h, interior, Word.toList]
          | cons next rest =>
              unfold split3 at h
              generalize reversedEq :
                (Word.mk head (next :: rest)).toList.reverse = reversed at h
              cases reversed with
              | nil =>
                  have lengthEq := congrArg List.length reversedEq
                  simp [Word.toList] at lengthEq
              | cons last reversedTail =>
                  cases reversedTail with
                  | nil =>
                      have lengthEq := congrArg List.length reversedEq
                      simp [Word.toList] at lengthEq
                  | cons penult reversedStem => simp at h
  | some triple =>
      obtain ⟨stem, p2, p1⟩ := triple
      let sortedStem := stem.mergeSort leNat
      have dedupNodup : (dedupSorted sortedStem).Nodup := by
        apply dedupSorted_nodup_of_sorted
        have sorted := List.pairwise_mergeSort
          (le := leNat)
          (fun _ _ _ => by simp [leNat]; omega)
          (fun _ _ => by simp [leNat]; omega)
          stem
        exact sorted.imp (by intro _ _ step; simpa [leNat] using step)
      simp only [sortInteriorFn, h, collapseFn, split3_render_eq,
        interior_render]
      split
      · exact dedupNodup.filter _
      · exact dedupNodup

private theorem nodup_perm_of_mem_iff {left right : List Nat}
    (leftNodup : left.Nodup) (rightNodup : right.Nodup)
    (member : ∀ letter, letter ∈ left ↔ letter ∈ right) :
    left.Perm right := by
  apply List.perm_iff_count.mpr
  intro letter
  rw [leftNodup.count, rightNodup.count]
  simp [member letter]

private theorem pad_derives_of_interior_nodup (word : Word Nat)
    (interiorNodup : (interior word).Nodup) :
    Derives basis word (padFn word) := by
  cases h : split3 word with
  | none => simpa [padFn, h] using Derives.refl word
  | some triple =>
      obtain ⟨stem, p2, p1⟩ := triple
      have wordEq := split3_render h
      have stemNodup : stem.Nodup := by
        rw [wordEq, interior_render] at interiorNodup
        exact interiorNodup
      rw [wordEq]
      simp only [padFn, split3_render_eq]
      by_cases fresh : (invariant (render stem p2 p1)).fresh = true
      · rw [if_pos fresh]
        exact Derives.refl _
      · have notFreshFacts : ¬(p1 ∉ stem ∧ p2 ≠ p1) := by
          intro facts
          exact fresh ((fresh_render_iff stem p2 p1).mpr facts)
        have p1Covered : p1 ∈ stem ∨ p1 = p2 := by
          by_cases p1Member : p1 ∈ stem
          · exact Or.inl p1Member
          · by_cases pairEq : p2 = p1
            · exact Or.inr pairEq.symm
            · exact False.elim (notFreshFacts ⟨p1Member, pairEq⟩)
        have supportNodup :
            (invariant (render stem p2 p1)).support.Nodup :=
          sortedSupport_nodup _
        by_cases p2Member : p2 ∈ stem
        · have sameMember : ∀ letter,
              letter ∈ stem ↔
                letter ∈ (invariant (render stem p2 p1)).support := by
            intro letter
            change letter ∈ stem ↔
              letter ∈ sortedSupport (render stem p2 p1)
            rw [sortedSupport_mem]
            simp only [render_toList, List.mem_append, List.mem_cons,
              List.mem_nil_iff, or_false]
            constructor
            · exact Or.inl
            · rintro (memberStem | eqP2 | eqP1)
              · exact memberStem
              · exact eqP2 ▸ p2Member
              · rcases p1Covered with memberP1 | eqP1P2
                · exact eqP1 ▸ memberP1
                · exact eqP1 ▸ eqP1P2 ▸ p2Member
          have perm := nodup_perm_of_mem_iff stemNodup supportNodup sameMember
          rw [if_neg fresh]
          exact (Derives.refl _).trans (derivesRenderPerm perm p2 p1)
        · have augmentedNodup : (stem ++ [p2]).Nodup := by
            rw [List.nodup_append]
            refine ⟨stemNodup, by simp, ?_⟩
            intro letter memberStem terminal memberTerminal
            have terminalEq : terminal = p2 := by simpa using memberTerminal
            subst terminal
            intro letterEq
            exact p2Member (letterEq ▸ memberStem)
          have sameMember : ∀ letter,
              letter ∈ stem ++ [p2] ↔
                letter ∈ (invariant (render stem p2 p1)).support := by
            intro letter
            change letter ∈ stem ++ [p2] ↔
              letter ∈ sortedSupport (render stem p2 p1)
            rw [sortedSupport_mem]
            simp only [render_toList, List.mem_append, List.mem_cons,
              List.mem_nil_iff, or_false]
            constructor
            · rintro (memberStem | eqP2)
              · exact Or.inl memberStem
              · exact Or.inr (Or.inl eqP2)
            · rintro (memberStem | eqP2 | eqP1)
              · exact Or.inl memberStem
              · exact Or.inr eqP2
              · rcases p1Covered with memberP1 | eqP1P2
                · exact Or.inl (eqP1 ▸ memberP1)
                · exact Or.inr (eqP1.trans eqP1P2)
          have perm := nodup_perm_of_mem_iff augmentedNodup supportNodup sameMember
          rw [if_neg fresh]
          exact (derivesBoundaryPad stem p2 p1).trans
            (derivesRenderPerm perm p2 p1)

private theorem pad_invariant_self (word : Word Nat) :
    invariant (padFn word) = invariant word := by
  cases h : split3 word with
  | none => simp [padFn, h]
  | some triple =>
      obtain ⟨stem, p2, p1⟩ := triple
      have wordEq := split3_render h
      rw [wordEq]
      simp only [padFn, split3_render_eq]
      by_cases fresh : (invariant (render stem p2 p1)).fresh = true
      · rw [if_pos fresh]
      · let support := (invariant (render stem p2 p1)).support
        have p2InSupport : p2 ∈ support := by
          change p2 ∈ sortedSupport (render stem p2 p1)
          rw [sortedSupport_mem]
          simp [render_toList]
        have p1InSupport : p1 ∈ support := by
          change p1 ∈ sortedSupport (render stem p2 p1)
          rw [sortedSupport_mem]
          simp [render_toList]
        have targetFreshNot :
            (invariant (render support p2 p1)).fresh ≠ true := by
          intro targetFresh
          exact ((fresh_render_iff support p2 p1).mp targetFresh).1 p1InSupport
        have targetFreshFalse :
            (invariant (render support p2 p1)).fresh = false :=
          bool_eq_false_of_ne_true _ targetFreshNot
        have sourceFreshFalse :
            (invariant (render stem p2 p1)).fresh = false :=
          bool_eq_false_of_ne_true _ fresh
        have fullMember : ∀ letter,
            letter ∈ (render support p2 p1).toList ↔
              letter ∈ (render stem p2 p1).toList := by
          intro letter
          simp only [render_toList, List.mem_append, List.mem_cons,
            List.mem_nil_iff, or_false]
          constructor
          · rintro (memberSupport | eqP2 | eqP1)
            · simpa [render_toList] using
                (sortedSupport_mem _ _).mp memberSupport
            · exact Or.inr (Or.inl eqP2)
            · exact Or.inr (Or.inr eqP1)
          · intro memberWord
            exact Or.inl ((sortedSupport_mem _ _).mpr (by
              simpa [render_toList] using memberWord))
        rw [if_neg fresh]
        exact invariant_render_eq_of_mem_and_fresh support stem p2 p1
          fullMember (targetFreshFalse.trans sourceFreshFalse.symm)

private theorem dedupSorted_sorted_of_sorted {letters : List Nat}
    (sorted : letters.Pairwise (· ≤ ·)) :
    (dedupSorted letters).Pairwise (· ≤ ·) := by
  induction letters with
  | nil => simp [dedupSorted]
  | cons head tail ih =>
      cases tail with
      | nil => simp [dedupSorted]
      | cons next rest =>
          have sortedTail : (next :: rest).Pairwise (· ≤ ·) :=
            (List.pairwise_cons.mp sorted).2
          by_cases headsEq : head = next
          · subst next
            simpa [dedupSorted] using ih sortedTail
          · rw [dedupSorted]
            simp only [headsEq, ↓reduceIte]
            apply List.pairwise_cons.mpr
            constructor
            · intro letter member
              exact (List.pairwise_cons.mp sorted).1 letter
                ((dedupSorted_mem letter (next :: rest)).mp member)
            · exact ih sortedTail

private theorem collapse_sort_sorted (word : Word Nat) :
    (interior (collapseFn (sortInteriorFn word))).Pairwise (· ≤ ·) := by
  cases h : split3 word with
  | none =>
      cases word with
      | mk head tail =>
          cases tail with
          | nil => simp [sortInteriorFn, collapseFn, h, interior, Word.toList]
          | cons next rest =>
              unfold split3 at h
              generalize reversedEq :
                (Word.mk head (next :: rest)).toList.reverse = reversed at h
              cases reversed with
              | nil =>
                  have lengthEq := congrArg List.length reversedEq
                  simp [Word.toList] at lengthEq
              | cons last reversedTail =>
                  cases reversedTail with
                  | nil =>
                      have lengthEq := congrArg List.length reversedEq
                      simp [Word.toList] at lengthEq
                  | cons penult reversedStem => simp at h
  | some triple =>
      obtain ⟨stem, p2, p1⟩ := triple
      let sortedStem := stem.mergeSort leNat
      have dedupSorted : (dedupSorted sortedStem).Pairwise (· ≤ ·) := by
        apply dedupSorted_sorted_of_sorted
        have sorted := List.pairwise_mergeSort
          (le := leNat)
          (fun _ _ _ => by simp [leNat]; omega)
          (fun _ _ => by simp [leNat]; omega)
          stem
        exact sorted.imp (by intro _ _ step; simpa [leNat] using step)
      simp only [sortInteriorFn, h, collapseFn, split3_render_eq,
        interior_render]
      split
      · exact dedupSorted.filter _
      · exact dedupSorted

private theorem normalForm_render (stem : List Nat) (p2 p1 : Nat) :
    normalForm (render stem p2 p1) =
      if (invariant (render stem p2 p1)).fresh then
        render ((invariant (render stem p2 p1)).support.filter
          (fun letter => decide (letter ≠ p2 ∧ letter ≠ p1))) p2 p1
      else
        render (invariant (render stem p2 p1)).support p2 p1 := by
  unfold normalForm
  rw [canonical]
  simp only [invariant, trailingPair_render, Option.map]
  rw [finalLetter_render]
  rfl

/-! ## The witness -/

/-- Constructive witness for the three-stage normalizer.  The measures:
stage 1 — inversion count of the stem (strictly decreased by every
`Perm.swap` step of the sorting permutation); stage 2 — stem length
(strictly decreased by every contraction); stage 3 — number of missing
stem letters (≤ 2, each padding step decreases it), then inversions again
for the final re-sort inside `derivesRenderPerm`. -/
def witness : NormalizationWitness where
  sortInterior := sortInteriorFn
  collapseInteriorDuplicates := collapseFn
  padRepeatMissingSupport := padFn
  sort_derives := sortInterior_derives
  sort_invariant := by
    intro word
    -- interior permutation: support is membership-invariant under Perm
    -- (dedup + mergeSort of same-membership Nodup lists agree), trailing
    -- pair fixed by construction, count of the final letter Perm-invariant
    cases h : split3 word with
    | none => simp [sortInteriorFn, h]
    | some triple =>
        obtain ⟨stem, p2, p1⟩ := triple
        rw [split3_render h]
        simp only [sortInteriorFn, split3_render_eq]
        exact invariant_render_perm (List.mergeSort_perm stem leNat) p2 p1
  sort_sorted := by
    intro word
    -- interior (render (mergeSort stem) p2 p1) = mergeSort stem, sorted
    cases h : split3 word with
    | none =>
        cases word with
        | mk head tail =>
            cases tail with
            | nil => simp [sortInteriorFn, h, interior, Word.toList]
            | cons next rest =>
                unfold split3 at h
                generalize reversedEq :
                  (Word.mk head (next :: rest)).toList.reverse = reversed at h
                cases reversed with
                | nil =>
                    have lengthEq := congrArg List.length reversedEq
                    simp [Word.toList] at lengthEq
                | cons last reversedTail =>
                    cases reversedTail with
                    | nil =>
                        have lengthEq := congrArg List.length reversedEq
                        simp [Word.toList] at lengthEq
                    | cons penult reversedStem => simp at h
    | some triple =>
        obtain ⟨stem, p2, p1⟩ := triple
        simp only [sortInteriorFn, h, interior_render]
        have sorted := List.pairwise_mergeSort
          (le := leNat)
          (fun _ _ _ => by simp [leNat]; omega)
          (fun _ _ => by simp [leNat]; omega)
          stem
        exact sorted.imp (by intro _ _ step; simpa [leNat] using step)
  collapse_derives := by
    intro word
    -- fold derivesStemContraction along dedupSorted's recursion, then
    -- derivesRenderPerm to expose the p2 copy + derivesSeamContraction
    cases h : split3 word with
    | none =>
        simpa [sortInteriorFn, collapseFn, h] using Derives.refl word
    | some triple =>
        obtain ⟨stem, p2, p1⟩ := triple
        let sortedStem := stem.mergeSort leNat
        have sortedNodup : (dedupSorted sortedStem).Nodup := by
          apply dedupSorted_nodup_of_sorted
          have sorted := List.pairwise_mergeSort
            (le := leNat)
            (fun _ _ _ => by simp [leNat]; omega)
            (fun _ _ => by simp [leNat]; omega)
            stem
          exact sorted.imp (by intro _ _ step; simpa [leNat] using step)
        have dedupDerivation := derivesDedupSorted sortedStem p2 p1
        simp only [sortInteriorFn, h]
        change Derives basis (render sortedStem p2 p1)
          (collapseFn (render sortedStem p2 p1))
        simp only [collapseFn, split3_render_eq]
        by_cases fresh : (invariant (render sortedStem p2 p1)).fresh = true
        · have freshFacts := (fresh_render_iff sortedStem p2 p1).mp fresh
          have p1NotDedup : p1 ∉ dedupSorted sortedStem := by
            intro member
            exact freshFacts.1 ((dedupSorted_mem p1 sortedStem).mp member)
          have filterEq :
              (dedupSorted sortedStem).filter
                  (fun c => decide (c ≠ p2 ∧ c ≠ p1)) =
                (dedupSorted sortedStem).erase p2 := by
            rw [sortedNodup.erase_eq_filter p2]
            apply List.filter_congr
            intro letter member
            have letterNeP1 : letter ≠ p1 := by
              intro letterEq
              exact p1NotDedup (letterEq ▸ member)
            by_cases letterEqP2 : letter = p2 <;>
              simp [letterEqP2, letterNeP1]
          by_cases p2Member : p2 ∈ dedupSorted sortedStem
          · have movedPerm :
                (dedupSorted sortedStem).Perm
                  ((dedupSorted sortedStem).erase p2 ++ [p2]) :=
              (List.perm_cons_erase p2Member).trans
                (List.perm_append_singleton p2
                  ((dedupSorted sortedStem).erase p2)).symm
            have removed :=
              (derivesRenderPerm movedPerm p2 p1).trans
                (derivesSeamContraction
                  ((dedupSorted sortedStem).erase p2) p2 p1)
            rw [if_pos fresh, filterEq]
            exact dedupDerivation.trans removed
          · have unchanged :
                (dedupSorted sortedStem).filter
                    (fun c => decide (c ≠ p2 ∧ c ≠ p1)) =
                  dedupSorted sortedStem := by
              apply List.filter_eq_self.mpr
              intro letter member
              simp only [decide_eq_true_eq]
              exact ⟨fun eq => p2Member (eq ▸ member),
                fun eq => p1NotDedup (eq ▸ member)⟩
            rw [if_pos fresh, unchanged]
            exact dedupDerivation
        · rw [if_neg fresh]
          exact dedupDerivation
  collapse_invariant := by
    intro word
    -- contraction keeps support (a copy survives: stem was sorted with a
    -- duplicate, and the seam copy of p2 survives at the penult); the
    -- final-letter count can only drop from ≥ 3 to ≥ 2, never to 1,
    -- because an interior duplicate of p1 forces count ≥ 3 — so `fresh`
    -- never flips
    exact collapse_sort_invariant word
  collapse_nodup := by
    intro word
    exact collapse_sort_nodup word
  pad_derives := by
    intro word
    -- fresh: refl.  repeat: derivesBoundaryPad for each of the ≤ 2 missing
    -- letters (p2 always; p1 exactly when p2 = p1 and the stem lacks it),
    -- then derivesRenderPerm onto the sorted support
    exact pad_derives_of_interior_nodup _ (collapse_sort_nodup word)
  pad_invariant := by
    intro word
    exact (pad_invariant_self _).trans (collapse_sort_invariant word)
  result_eq_canonical := by
    intro word
    -- both sides are `render X p2 p1` with X a sorted Nodup list of the
    -- same membership: fresh → support minus {p2, p1}; repeat → support.
    -- Sorted + Nodup + equal membership ⇒ equal lists.
    cases h : split3 word with
    | none =>
        cases word with
        | mk head tail =>
            cases tail with
            | nil =>
                simp [sortInteriorFn, collapseFn, padFn, h, normalForm,
                  canonical, invariant, trailingPair, finalLetter,
                  sortedSupport, deduplicateSupport, Word.toList]
                rfl
            | cons next rest =>
                unfold split3 at h
                generalize reversedEq :
                  (Word.mk head (next :: rest)).toList.reverse = reversed at h
                cases reversed with
                | nil =>
                    have lengthEq := congrArg List.length reversedEq
                    simp [Word.toList] at lengthEq
                | cons last reversedTail =>
                    cases reversedTail with
                    | nil =>
                        have lengthEq := congrArg List.length reversedEq
                        simp [Word.toList] at lengthEq
                    | cons penult reversedStem => simp at h
    | some triple =>
        obtain ⟨stem, p2, p1⟩ := triple
        rw [split3_render h]
        let sortedStem := stem.mergeSort leNat
        let deduped := dedupSorted sortedStem
        have sortedStemSorted : sortedStem.Pairwise (· ≤ ·) := by
          have sorted := List.pairwise_mergeSort
            (le := leNat)
            (fun _ _ _ => by simp [leNat]; omega)
            (fun _ _ => by simp [leNat]; omega)
            stem
          exact sorted.imp (by intro _ _ step; simpa [leNat] using step)
        have dedupedSorted : deduped.Pairwise (· ≤ ·) :=
          dedupSorted_sorted_of_sorted sortedStemSorted
        have dedupedNodup : deduped.Nodup :=
          dedupSorted_nodup_of_sorted sortedStemSorted
        have sortedInvariant :
            invariant (render sortedStem p2 p1) =
              invariant (render stem p2 p1) :=
          invariant_render_perm (List.mergeSort_perm stem leNat) p2 p1
        have normalEq :
            normalForm (render sortedStem p2 p1) =
              normalForm (render stem p2 p1) :=
          congrArg canonical sortedInvariant
        simp only [sortInteriorFn, split3_render_eq]
        change padFn (collapseFn (render sortedStem p2 p1)) =
          normalForm (render stem p2 p1)
        simp only [collapseFn, split3_render_eq]
        by_cases fresh : (invariant (render sortedStem p2 p1)).fresh = true
        · let filtered := deduped.filter
            (fun letter => decide (letter ≠ p2 ∧ letter ≠ p1))
          have freshFacts := (fresh_render_iff sortedStem p2 p1).mp fresh
          have filteredFresh :
              (invariant (render filtered p2 p1)).fresh = true := by
            apply (fresh_render_iff filtered p2 p1).mpr
            constructor
            · simp [filtered]
            · exact freshFacts.2
          have canonicalPrefixEq :
              filtered =
                (invariant (render sortedStem p2 p1)).support.filter
                  (fun letter => decide (letter ≠ p2 ∧ letter ≠ p1)) := by
            apply sortedNodup_eq_of_mem_iff
            · exact dedupedSorted.filter _
            · exact (sortedSupport_sorted _).filter _
            · exact dedupedNodup.filter _
            · exact (sortedSupport_nodup _).filter _
            · intro letter
              simp only [filtered, List.mem_filter, decide_eq_true_eq]
              constructor
              · rintro ⟨memberDeduped, exclusions⟩
                constructor
                · apply (sortedSupport_mem _ _).mpr
                  simp [render_toList,
                    (dedupSorted_mem letter sortedStem).mp memberDeduped]
                · exact exclusions
              · rintro ⟨memberSupport, exclusions⟩
                constructor
                · apply (dedupSorted_mem letter sortedStem).mpr
                  have memberWord := (sortedSupport_mem _ _).mp memberSupport
                  simp only [render_toList, List.mem_append, List.mem_cons,
                    List.mem_nil_iff, or_false] at memberWord
                  rcases memberWord with memberStem | eqP2 | eqP1
                  · exact memberStem
                  · exact False.elim (exclusions.1 eqP2)
                  · exact False.elim (exclusions.2 eqP1)
                · exact exclusions
          rw [if_pos fresh]
          change padFn (render filtered p2 p1) =
            normalForm (render stem p2 p1)
          simp only [padFn, split3_render_eq]
          rw [if_pos filteredFresh]
          rw [← normalEq, normalForm_render, if_pos fresh,
            canonicalPrefixEq]
        · have stemFreshNot :
              (invariant (render stem p2 p1)).fresh ≠ true := by
            intro stemFresh
            apply fresh
            exact congrArg (fun key : Invariant => key.fresh)
              sortedInvariant |>.trans stemFresh
          have collapsedInvariant :
              invariant (render deduped p2 p1) =
                invariant (render stem p2 p1) := by
            simpa [sortedStem, deduped, sortInteriorFn, collapseFn,
              split3_render_eq, fresh] using
                collapse_sort_invariant (render stem p2 p1)
          have dedupedFreshNot :
              (invariant (render deduped p2 p1)).fresh ≠ true := by
            intro dedupedFresh
            apply stemFreshNot
            exact (congrArg (fun key : Invariant => key.fresh)
              collapsedInvariant).symm.trans dedupedFresh
          rw [if_neg fresh]
          change padFn (render deduped p2 p1) =
            normalForm (render stem p2 p1)
          simp only [padFn, split3_render_eq]
          rw [if_neg dedupedFreshNot]
          rw [normalForm_render, if_neg stemFreshNot]
          exact congrArg
            (fun key : Invariant => render key.support p2 p1)
            collapsedInvariant

/-! ## Merge-collapse (alphabet-generic) -/

private theorem word_toList_map (word : Word Nat) (σ : Nat → Nat) :
    (word.map σ).toList = word.toList.map σ := by
  cases word
  rfl

private theorem support_map_mem (σ : Nat → Nat) (word : Word Nat)
    (letter : Nat) :
    letter ∈ (invariant (word.map σ)).support ↔
      ∃ source, source ∈ (invariant word).support ∧ σ source = letter := by
  change letter ∈ sortedSupport (word.map σ) ↔
    ∃ source, source ∈ sortedSupport word ∧ σ source = letter
  constructor
  · intro member
    have listed := (sortedSupport_mem (word.map σ) letter).mp member
    rw [word_toList_map] at listed
    rcases List.mem_map.mp listed with ⟨source, sourceMember, imageEq⟩
    exact ⟨source, (sortedSupport_mem word source).mpr sourceMember, imageEq⟩
  · rintro ⟨source, sourceMember, rfl⟩
    apply (sortedSupport_mem (word.map σ) (σ source)).mpr
    rw [word_toList_map]
    exact List.mem_map.mpr
      ⟨source, (sortedSupport_mem word source).mp sourceMember, rfl⟩

private theorem finalLetter_map (σ : Nat → Nat) (word : Word Nat) :
    finalLetter (word.map σ) = σ (finalLetter word) := by
  unfold finalLetter
  rw [word_toList_map, ← List.map_reverse]
  cases word.toList.reverse <;> simp [Word.map]

private theorem trailingPair_map (σ : Nat → Nat) (word : Word Nat) :
    trailingPair (word.map σ) =
      (trailingPair word).map (fun pair => (σ pair.1, σ pair.2)) := by
  unfold trailingPair
  rw [word_toList_map, ← List.map_reverse]
  cases reversed : word.toList.reverse with
  | nil => simp
  | cons last rest =>
      cases rest with
      | nil => simp
      | cons penultimate stem => simp

private theorem secondToLast_map (σ : Nat → Nat) (word : Word Nat) :
    (invariant (word.map σ)).secondToLast =
      (invariant word).secondToLast.map σ := by
  change (trailingPair (word.map σ)).map Prod.fst =
    ((trailingPair word).map Prod.fst).map σ
  rw [trailingPair_map]
  cases trailingPair word <;> rfl

private theorem count_map_of_fiber (σ : Nat → Nat) (target : Nat)
    (fiber : ∀ letter, σ letter = σ target → letter = target) :
    ∀ letters : List Nat,
      (letters.map σ).count (σ target) = letters.count target
  | [] => by simp
  | head :: tail => by
      by_cases headEq : head = target
      · subst head
        simp [count_map_of_fiber σ target fiber tail]
      · have imageNe : σ head ≠ σ target := by
          intro imageEq
          exact headEq (fiber head imageEq)
        simp [headEq, imageNe, count_map_of_fiber σ target fiber tail]

private theorem fresh_map_of_fiber (σ : Nat → Nat) (word : Word Nat)
    (fiber : ∀ letter,
      σ letter = σ (finalLetter word) → letter = finalLetter word) :
    (invariant (word.map σ)).fresh = (invariant word).fresh := by
  change finalIsFresh (word.map σ) = finalIsFresh word
  simp only [finalIsFresh]
  rw [finalLetter_map, word_toList_map,
    count_map_of_fiber σ (finalLetter word) fiber]

private def collapseAt (chosen letter : Nat) : Nat :=
  if letter = chosen then 0 else 1

private theorem collapseAt_bound (chosen letter : Nat) :
    collapseAt chosen letter ≤ 2 := by
  unfold collapseAt
  split <;> omega

private theorem collapseAt_support_separates {u v : Word Nat} {chosen : Nat}
    (present : chosen ∈ (invariant u).support)
    (absent : chosen ∉ (invariant v).support) :
    invariant (u.map (collapseAt chosen)) ≠
      invariant (v.map (collapseAt chosen)) := by
  intro same
  have zeroPresent :
      0 ∈ (invariant (u.map (collapseAt chosen))).support := by
    apply (support_map_mem (collapseAt chosen) u 0).mpr
    exact ⟨chosen, present, by simp [collapseAt]⟩
  have zeroAbsent :
      0 ∉ (invariant (v.map (collapseAt chosen))).support := by
    intro member
    rcases (support_map_mem (collapseAt chosen) v 0).mp member with
      ⟨source, sourceMember, imageEq⟩
    have sourceEq : source = chosen := by
      by_cases equality : source = chosen
      · exact equality
      · simp [collapseAt, equality] at imageEq
    exact absent (sourceEq ▸ sourceMember)
  apply zeroAbsent
  rw [← congrArg Invariant.support same]
  exact zeroPresent

private theorem support_disagreement {u v : Word Nat}
    (different : (invariant u).support ≠ (invariant v).support) :
    ∃ letter,
      (letter ∈ (invariant u).support ∧
          letter ∉ (invariant v).support) ∨
        (letter ∈ (invariant v).support ∧
          letter ∉ (invariant u).support) := by
  apply Classical.byContradiction
  intro noWitness
  apply different
  change sortedSupport u = sortedSupport v
  apply sortedNodup_eq_of_mem_iff
  · exact sortedSupport_sorted u
  · exact sortedSupport_sorted v
  · exact sortedSupport_nodup u
  · exact sortedSupport_nodup v
  · intro letter
    constructor
    · intro leftMember
      by_cases rightMember : letter ∈ sortedSupport v
      · exact rightMember
      · exact False.elim <| noWitness
          ⟨letter, Or.inl ⟨leftMember, rightMember⟩⟩
    · intro rightMember
      by_cases leftMember : letter ∈ sortedSupport u
      · exact leftMember
      · exact False.elim <| noWitness
          ⟨letter, Or.inr ⟨rightMember, leftMember⟩⟩

private def separatePair (left right letter : Nat) : Nat :=
  if letter = left then 0 else if letter = right then 1 else 2

private theorem separatePair_bound (left right letter : Nat) :
    separatePair left right letter ≤ 2 := by
  unfold separatePair
  split
  · omega
  · split <;> omega

/-- Any invariant disagreement survives an explicit letter-merging onto
`{0, 1, 2}`.  Case map (σ is total on `Nat`):
* support differs at `c` (wlog `c ∈ u`, `∉ v`): σ := (if · = c then 0 else 1);
* last letters differ (`a ≠ b`): σ := (if · = a then 0 else if · = b then 1 else 0);
* p2 letters differ (`a ≠ b`, common last `t`): σ := (if · = a then 0 else
  if · = b then 1 else 2) — p2 maps pointwise, so the images differ;
* only `fresh` differs (common last `t`): σ := (if · = t then 0 else 1) —
  the count of the last letter is preserved exactly, so the fresh bits of
  the images still disagree. -/
theorem merge_collapse {u v : Word Nat}
    (h : invariant u ≠ invariant v) :
    ∃ σ : Nat → Nat, (∀ n, σ n ≤ 2) ∧
      invariant (u.map σ) ≠ invariant (v.map σ) := by
  by_cases supportEq : (invariant u).support = (invariant v).support
  · by_cases lastEq : (invariant u).last = (invariant v).last
    · by_cases secondEq :
          (invariant u).secondToLast = (invariant v).secondToLast
      · have freshNe : (invariant u).fresh ≠ (invariant v).fresh := by
          intro freshEq
          apply h
          cases leftInvariant : invariant u
          cases rightInvariant : invariant v
          simp_all
        have sourceLastEq : finalLetter u = finalLetter v := by
          simpa [invariant] using lastEq
        let σ := collapseAt (finalLetter u)
        have fiberLeft : ∀ letter,
            σ letter = σ (finalLetter u) → letter = finalLetter u := by
          intro letter imageEq
          by_cases letterEq : letter = finalLetter u
          · exact letterEq
          · simp [σ, collapseAt, letterEq] at imageEq
        have fiberRight : ∀ letter,
            σ letter = σ (finalLetter v) → letter = finalLetter v := by
          intro letter imageEq
          have targetEq : σ (finalLetter v) = σ (finalLetter u) := by
            rw [← sourceLastEq]
          have leftEq : σ letter = σ (finalLetter u) :=
            imageEq.trans targetEq
          exact (fiberLeft letter leftEq).trans sourceLastEq
        refine ⟨σ, ?_, ?_⟩
        · exact collapseAt_bound (finalLetter u)
        · intro mappedEq
          have mappedFreshEq := congrArg Invariant.fresh mappedEq
          rw [fresh_map_of_fiber σ u fiberLeft,
            fresh_map_of_fiber σ v fiberRight] at mappedFreshEq
          exact freshNe mappedFreshEq
      · cases leftSecond : (invariant u).secondToLast with
        | none =>
            cases rightSecond : (invariant v).secondToLast with
            | none =>
                exact False.elim
                  (secondEq (leftSecond.trans rightSecond.symm))
            | some right =>
                refine ⟨fun _ : Nat => (0 : Nat), by intro; simp, ?_⟩
                intro mappedEq
                have mappedSecondEq :=
                  congrArg Invariant.secondToLast mappedEq
                rw [secondToLast_map, secondToLast_map] at mappedSecondEq
                simp [leftSecond, rightSecond] at mappedSecondEq
        | some left =>
            cases rightSecond : (invariant v).secondToLast with
            | none =>
                refine ⟨fun _ : Nat => (0 : Nat), by intro; simp, ?_⟩
                intro mappedEq
                have mappedSecondEq :=
                  congrArg Invariant.secondToLast mappedEq
                rw [secondToLast_map, secondToLast_map] at mappedSecondEq
                simp [leftSecond, rightSecond] at mappedSecondEq
            | some right =>
                have pairNe : left ≠ right := by
                  intro pairEq
                  subst right
                  exact secondEq (leftSecond.trans rightSecond.symm)
                refine ⟨separatePair left right, separatePair_bound left right,
                  ?_⟩
                intro mappedEq
                have mappedSecondEq :=
                  congrArg Invariant.secondToLast mappedEq
                rw [secondToLast_map, secondToLast_map] at mappedSecondEq
                simp [leftSecond, rightSecond, separatePair,
                  Ne.symm pairNe] at mappedSecondEq
    · have sourceLastNe : finalLetter u ≠ finalLetter v := by
        simpa [invariant] using lastEq
      refine ⟨collapseAt (finalLetter u),
        collapseAt_bound (finalLetter u), ?_⟩
      intro mappedEq
      have mappedLastEq := congrArg Invariant.last mappedEq
      change finalLetter (u.map (collapseAt (finalLetter u))) =
        finalLetter (v.map (collapseAt (finalLetter u))) at mappedLastEq
      rw [finalLetter_map, finalLetter_map] at mappedLastEq
      simp [collapseAt, Ne.symm sourceLastNe] at mappedLastEq
  · rcases support_disagreement supportEq with
      ⟨letter, presentLeft | presentRight⟩
    · exact ⟨collapseAt letter, collapseAt_bound letter,
        collapseAt_support_separates presentLeft.1 presentLeft.2⟩
    · exact ⟨collapseAt letter, collapseAt_bound letter,
        (collapseAt_support_separates presentRight.1 presentRight.2).symm⟩

/-! ## The representative semigroup and its separation -/

def repMul (a b : Fin 6) : Fin 6 :=
  ⟨S6_11405Data.mul a.val b.val % 6, Nat.mod_lt _ (by decide)⟩

def repTable : FiniteTable where
  order := 6
  mul := repMul
  assoc := by decide

def repSemigroup : Semigroup (Fin 6) := repTable.semigroup

private def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

set_option maxRecDepth 100000 in
theorem models_rep : Models repSemigroup basis :=
  FiniteCertificate.checkModels_sound repTable basis toFinFour (by decide)

private def smallSupports : List (List Nat) :=
  [[], [0], [1], [2], [0, 1], [0, 2], [1, 2], [0, 1, 2]]

private theorem smallSupports_complete : ∀ letters : List Nat,
    letters.Pairwise (· ≤ ·) →
    letters.Nodup →
    (∀ letter, letter ∈ letters → letter ≤ 2) →
    letters ∈ smallSupports
  | [], _, _, _ => by simp [smallSupports]
  | head :: tail, sorted, nodup, bounded => by
      have tailSorted := (List.pairwise_cons.mp sorted).2
      have tailNodup := (List.nodup_cons.mp nodup).2
      have tailBounded : ∀ letter, letter ∈ tail → letter ≤ 2 := by
        intro letter member
        exact bounded letter (by simp [member])
      have headBounded : head ≤ 2 := bounded head (by simp)
      have tailComplete :=
        smallSupports_complete tail tailSorted tailNodup tailBounded
      simp [smallSupports] at tailComplete
      rcases tailComplete with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [smallSupports] at * <;> omega

private theorem finalLetter_mem_toList (word : Word Nat) :
    finalLetter word ∈ word.toList := by
  unfold finalLetter
  generalize reverseEq : word.toList.reverse = reversed
  cases reversed with
  | nil =>
      have originalEmpty : word.toList = [] := by
        have reversedAgain := congrArg List.reverse reverseEq
        simpa using reversedAgain
      cases word
      simp [Word.toList] at originalEmpty
  | cons last rest =>
      have memberReverse : last ∈ word.toList.reverse := by
        rw [reverseEq]
        simp
      simpa only [List.mem_reverse] using memberReverse

private theorem secondToLast_mem_toList {word : Word Nat} {letter : Nat}
    (second : (invariant word).secondToLast = some letter) :
    letter ∈ word.toList := by
  change (trailingPair word).map Prod.fst = some letter at second
  unfold trailingPair at second
  generalize reverseEq : word.toList.reverse = reversed at second
  cases reversed with
  | nil => simp at second
  | cons last rest =>
      cases rest with
      | nil => simp at second
      | cons penultimate stem =>
          simp at second
          subst letter
          have memberReverse : penultimate ∈ word.toList.reverse := by
            rw [reverseEq]
            simp
          simpa only [List.mem_reverse] using memberReverse

private theorem secondToLast_ne_last_of_fresh {word : Word Nat}
    {penultimate : Nat}
    (second : (invariant word).secondToLast = some penultimate)
    (fresh : (invariant word).fresh = true) :
    penultimate ≠ (invariant word).last := by
  change (trailingPair word).map Prod.fst = some penultimate at second
  change finalIsFresh word = true at fresh
  unfold trailingPair at second
  generalize reverseEq : word.toList.reverse = reversed at second
  cases reversed with
  | nil => simp at second
  | cons last rest =>
      cases rest with
      | nil => simp at second
      | cons previous stem =>
          simp at second
          subst penultimate
          have finalEq : finalLetter word = last := by
            unfold finalLetter
            rw [reverseEq]
          change previous ≠ finalLetter word
          intro previousEq
          rw [finalEq] at previousEq
          subst previous
          have countEq :
              word.toList.count last = (last :: last :: stem).count last := by
            rw [← List.count_reverse, reverseEq]
          have countOne : word.toList.count last = 1 := by
            apply of_decide_eq_true
            simpa [finalIsFresh, finalEq] using fresh
          rw [countEq] at countOne
          simp at countOne

private def smallSeconds : List (Option Nat) :=
  [none, some 0, some 1, some 2]

private def smallLasts : List Nat := [0, 1, 2]

private def booleanValues : List Bool := [false, true]

private def fieldsAdmissible
    (support : List Nat) (second : Option Nat) (last : Nat)
    (fresh : Bool) : Bool :=
  decide (last ∈ support) &&
    match second with
    | none => true
    | some penultimate =>
        decide (penultimate ∈ support) &&
          (!fresh || decide (penultimate ≠ last))

private def canonicalInventoryCheck : Bool :=
  smallSupports.all fun support =>
    smallSeconds.all fun second =>
      smallLasts.all fun last =>
        booleanValues.all fun fresh =>
          !fieldsAdmissible support second last fresh ||
            decide
              (canonical
                  { support := support
                    secondToLast := second
                    last := last
                    fresh := fresh } ∈ S6_11405Data.canonicals)

set_option maxRecDepth 100000 in
private theorem canonicalInventory_checked : canonicalInventoryCheck = true := by
  decide

private theorem smallSupport_member_cases {support : List Nat} {letter : Nat}
    (supportSmall : support ∈ smallSupports)
    (member : letter ∈ support) :
    letter = 0 ∨ letter = 1 ∨ letter = 2 := by
  simp [smallSupports] at supportSmall
  rcases supportSmall with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp at member <;> omega

private theorem canonical_mem_of_small_fields
    (support : List Nat) (second : Option Nat) (last : Nat) (fresh : Bool)
    (supportSmall : support ∈ smallSupports)
    (lastMember : last ∈ support)
    (secondMember : ∀ penultimate,
      second = some penultimate → penultimate ∈ support)
    (freshDistinct : ∀ penultimate,
      second = some penultimate → fresh = true → penultimate ≠ last) :
    canonical
        { support := support
          secondToLast := second
          last := last
          fresh := fresh } ∈ S6_11405Data.canonicals := by
  have lastSmall : last ∈ smallLasts := by
    rcases smallSupport_member_cases supportSmall lastMember with
      rfl | rfl | rfl <;> simp [smallLasts]
  have secondSmall : second ∈ smallSeconds := by
    cases second with
    | none => simp [smallSeconds]
    | some penultimate =>
        have member := secondMember penultimate rfl
        rcases smallSupport_member_cases supportSmall member with
          rfl | rfl | rfl <;> simp [smallSeconds]
  have freshSmall : fresh ∈ booleanValues := by
    cases fresh <;> simp [booleanValues]
  have admissible : fieldsAdmissible support second last fresh = true := by
    cases second with
    | none => simp [fieldsAdmissible, lastMember]
    | some penultimate =>
        have member := secondMember penultimate rfl
        cases fresh with
        | false => simp [fieldsAdmissible, lastMember, member]
        | true =>
            have different := freshDistinct penultimate rfl rfl
            simp [fieldsAdmissible, lastMember, member, different]
  have checked := canonicalInventory_checked
  unfold canonicalInventoryCheck at checked
  have supportChecked :=
    (List.all_eq_true.mp checked) support supportSmall
  have secondChecked :=
    (List.all_eq_true.mp supportChecked) second secondSmall
  have lastChecked :=
    (List.all_eq_true.mp secondChecked) last lastSmall
  have freshChecked :=
    (List.all_eq_true.mp lastChecked) fresh freshSmall
  simp [admissible] at freshChecked
  exact freshChecked

private theorem normalForm_mem_canonicals_of_bound (word : Word Nat)
    (bounded : ∀ letter, letter ∈ word.toList → letter ≤ 2) :
    normalForm word ∈ S6_11405Data.canonicals := by
  have supportSorted :
      (invariant word).support.Pairwise (· ≤ ·) := by
    exact sortedSupport_sorted word
  have supportNodup : (invariant word).support.Nodup := by
    exact sortedSupport_nodup word
  have supportBounded : ∀ letter,
      letter ∈ (invariant word).support → letter ≤ 2 := by
    intro letter member
    exact bounded letter ((sortedSupport_mem word letter).mp member)
  have supportSmall := smallSupports_complete
    (invariant word).support supportSorted supportNodup supportBounded
  have lastMember :
      (invariant word).last ∈ (invariant word).support := by
    apply (sortedSupport_mem word (finalLetter word)).mpr
    exact finalLetter_mem_toList word
  have secondMember : ∀ penultimate,
      (invariant word).secondToLast = some penultimate →
        penultimate ∈ (invariant word).support := by
    intro penultimate second
    apply (sortedSupport_mem word penultimate).mpr
    exact secondToLast_mem_toList second
  have freshDistinct : ∀ penultimate,
      (invariant word).secondToLast = some penultimate →
      (invariant word).fresh = true →
        penultimate ≠ (invariant word).last := by
    exact fun penultimate second fresh =>
      secondToLast_ne_last_of_fresh second fresh
  exact canonical_mem_of_small_fields
    (invariant word).support (invariant word).secondToLast
    (invariant word).last (invariant word).fresh
    supportSmall lastMember secondMember freshDistinct

private def separatorValuation (values : List Nat) (letter : Nat) : Fin 6 :=
  ⟨values.getD letter 0 % 6, Nat.mod_lt _ (by decide)⟩

private def dataFingerprint (word : Word Nat) : List Nat :=
  S6_11405Data.separatorValuations.map fun values =>
    S6_11405Data.evalWord values word

/-! `memberFingerprint` is the reusable semantic boundary for every G2
member.  The normalization proof is shared; a class wrapper only has to prove
that these fingerprints are injective on the fixed three-letter canonical
inventory. -/
def memberFingerprint (S : Semigroup (Fin 6))
    (separatorValuations : List (List Nat)) (word : Word Nat) : List Nat :=
  separatorValuations.map fun values =>
    (S.eval (separatorValuation values) word).val

private def repFingerprint (word : Word Nat) : List Nat :=
  memberFingerprint repSemigroup S6_11405Data.separatorValuations word

set_option maxRecDepth 100000 in
private theorem repFingerprints_eq :
    S6_11405Data.canonicals.map repFingerprint =
      S6_11405Data.fingerprints := by
  decide

private theorem map_eq_pointwise_of_mem
    {entries : List α} {left right : α → β}
    (mappedEq : entries.map left = entries.map right)
    {entry : α} (member : entry ∈ entries) :
    left entry = right entry := by
  induction entries with
  | nil => simp at member
  | cons head tail ih =>
      simp only [List.map_cons] at mappedEq
      injection mappedEq with headEq tailEq
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact headEq
      · exact ih tailEq member

private theorem map_injective_on_of_nodup
    {entries : List α} {project : α → β}
    (mappedNodup : (entries.map project).Nodup)
    {left right : α}
    (leftMember : left ∈ entries) (rightMember : right ∈ entries)
    (sameImage : project left = project right) :
    left = right := by
  induction entries with
  | nil => simp at leftMember
  | cons head tail ih =>
      simp only [List.map_cons, List.nodup_cons] at mappedNodup
      rcases mappedNodup with ⟨headAbsent, tailNodup⟩
      simp only [List.mem_cons] at leftMember rightMember
      rcases leftMember with rfl | leftMember <;>
        rcases rightMember with rfl | rightMember
      · rfl
      · exfalso
        apply headAbsent
        rw [sameImage]
        exact List.mem_map.mpr ⟨right, rightMember, rfl⟩
      · exfalso
        apply headAbsent
        rw [← sameImage]
        exact List.mem_map.mpr ⟨left, leftMember, rfl⟩
      · exact ih tailNodup leftMember rightMember

private theorem dataFingerprint_ne_of_canonical_ne
    {left right : Word Nat}
    (leftMember : left ∈ S6_11405Data.canonicals)
    (rightMember : right ∈ S6_11405Data.canonicals)
    (different : left ≠ right) :
    dataFingerprint left ≠ dataFingerprint right := by
  intro sameFingerprint
  apply different
  apply map_injective_on_of_nodup
    (entries := S6_11405Data.canonicals)
    (project := dataFingerprint)
  · simpa [S6_11405Data.fingerprints, dataFingerprint] using
      S6_11405Data.fingerprints_nodup
  · exact leftMember
  · exact rightMember
  · exact sameFingerprint

private theorem repFingerprint_eq_dataFingerprint
    {word : Word Nat} (member : word ∈ S6_11405Data.canonicals) :
    repFingerprint word = dataFingerprint word := by
  apply map_eq_pointwise_of_mem (entry := word) (member := member)
  simpa [S6_11405Data.fingerprints, dataFingerprint] using
    repFingerprints_eq

private theorem repFingerprint_ne_of_canonical_ne
    {left right : Word Nat}
    (leftMember : left ∈ S6_11405Data.canonicals)
    (rightMember : right ∈ S6_11405Data.canonicals)
    (different : left ≠ right) :
    repFingerprint left ≠ repFingerprint right := by
  intro sameFingerprint
  apply dataFingerprint_ne_of_canonical_ne leftMember rightMember different
  rw [← repFingerprint_eq_dataFingerprint leftMember,
    ← repFingerprint_eq_dataFingerprint rightMember]
  exact sameFingerprint

private theorem exists_separator_of_repFingerprint_ne
    {left right : Word Nat}
    (different : repFingerprint left ≠ repFingerprint right) :
    ∃ values, values ∈ S6_11405Data.separatorValuations ∧
      repSemigroup.eval (separatorValuation values) left ≠
        repSemigroup.eval (separatorValuation values) right := by
  apply Classical.byContradiction
  intro noSeparator
  apply different
  unfold repFingerprint memberFingerprint
  apply List.map_congr_left
  intro values member
  by_cases sameValue :
      repSemigroup.eval (separatorValuation values) left =
        repSemigroup.eval (separatorValuation values) right
  · exact congrArg Fin.val sameValue
  · exact False.elim <| noSeparator ⟨values, member, sameValue⟩

private theorem exists_separator_of_memberFingerprint_ne
    (S : Semigroup (Fin 6)) (separatorValuations : List (List Nat))
    {left right : Word Nat}
    (different :
      memberFingerprint S separatorValuations left ≠
        memberFingerprint S separatorValuations right) :
    ∃ values, values ∈ separatorValuations ∧
      S.eval (separatorValuation values) left ≠
        S.eval (separatorValuation values) right := by
  apply Classical.byContradiction
  intro noSeparator
  apply different
  unfold memberFingerprint
  apply List.map_congr_left
  intro values member
  by_cases sameValue :
      S.eval (separatorValuation values) left =
        S.eval (separatorValuation values) right
  · exact congrArg Fin.val sameValue
  · exact False.elim <| noSeparator ⟨values, member, sameValue⟩

private theorem invariant_normalForm (word : Word Nat) :
    invariant (normalForm word) = invariant word := by
  rw [← witness.result_eq_canonical word]
  exact witness.pad_invariant word

private theorem mapped_letters_bound (σ : Nat → Nat)
    (bounded : ∀ letter, σ letter ≤ 2) (word : Word Nat) :
    ∀ letter, letter ∈ (word.map σ).toList → letter ≤ 2 := by
  intro letter member
  rw [word_toList_map] at member
  rcases List.mem_map.mp member with ⟨source, _, rfl⟩
  exact bounded source

/-! The all-member G2 endpoint.  All combinatorial normalization and
merge-collapse work is shared.  The two class-specific inputs are validity of
the two displayed laws and injectivity of a finite list of semantic
fingerprints on the fixed 132-word canonical inventory. -/
theorem invariantSeparation_of_fingerprints
    (S : Semigroup (Fin 6)) (models : Models S basis)
    (separatorValuations : List (List Nat))
    (fingerprintsNodup :
      (S6_11405Data.canonicals.map
        (memberFingerprint S separatorValuations)).Nodup) :
    InvariantSeparation S := by
  intro identity valid
  apply Classical.byContradiction
  intro invariantNe
  obtain ⟨σ, bounded, separated⟩ := merge_collapse invariantNe
  have mappedValid :
      (identity.map σ).SatisfiedBy S :=
    Identity.satisfiedBy_map identity σ S valid
  have leftMember := normalForm_mem_canonicals_of_bound
    (identity.lhs.map σ) (mapped_letters_bound σ bounded identity.lhs)
  have rightMember := normalForm_mem_canonicals_of_bound
    (identity.rhs.map σ) (mapped_letters_bound σ bounded identity.rhs)
  have normalFormsNe :
      normalForm (identity.lhs.map σ) ≠
        normalForm (identity.rhs.map σ) := by
    intro normalFormsEq
    apply separated
    have invariantsEq := congrArg invariant normalFormsEq
    rw [invariant_normalForm, invariant_normalForm] at invariantsEq
    exact invariantsEq
  have fingerprintsNe :
      memberFingerprint S separatorValuations
          (normalForm (identity.lhs.map σ)) ≠
        memberFingerprint S separatorValuations
          (normalForm (identity.rhs.map σ)) := by
    intro sameFingerprint
    apply normalFormsNe
    exact map_injective_on_of_nodup fingerprintsNodup
      leftMember rightMember sameFingerprint
  obtain ⟨values, _, separatedValues⟩ :=
    exists_separator_of_memberFingerprint_ne S separatorValuations
      fingerprintsNe
  have validValues :
      S.eval (separatorValuation values) (identity.lhs.map σ) =
        S.eval (separatorValuation values) (identity.rhs.map σ) := by
    simpa [Identity.map] using mappedValid (separatorValuation values)
  have leftSound := Derives.sound models
    (witness.derives_normalForm (identity.lhs.map σ))
    (separatorValuation values)
  have rightSound := Derives.sound models
    (witness.derives_normalForm (identity.rhs.map σ))
    (separatorValuation values)
  exact separatedValues (leftSound.symm.trans (validValues.trans rightSound))

theorem basisFor_of_fingerprints
    (S : Semigroup (Fin 6)) (models : Models S basis)
    (separatorValuations : List (List Nat))
    (fingerprintsNodup :
      (S6_11405Data.canonicals.map
        (memberFingerprint S separatorValuations)).Nodup) :
    BasisFor S basis :=
  basisFor_of_models_invariantSeparation models witness
    (invariantSeparation_of_fingerprints S models separatorValuations
      fingerprintsNodup)

private theorem repFingerprints_nodup :
    (S6_11405Data.canonicals.map
      (memberFingerprint repSemigroup
        S6_11405Data.separatorValuations)).Nodup := by
  change (S6_11405Data.canonicals.map repFingerprint).Nodup
  rw [repFingerprints_eq]
  exact S6_11405Data.fingerprints_nodup

/-- Semantic separation for S6_11405 through the four separator
valuations: if two words have different invariants, merge-collapse gives
≤ 3-letter images with different invariants; their canonical forms are
distinct members of `canonicals`, hence have distinct fingerprints
(`fingerprints_nodup`), hence some separator valuation distinguishes their
values; soundness of the witness derivations transports the distinction
back to the original words, refuting validity. -/
theorem invariantSeparation_rep :
    InvariantSeparation repSemigroup :=
  invariantSeparation_of_fingerprints repSemigroup models_rep
    S6_11405Data.separatorValuations repFingerprints_nodup

/-- The endpoint for the representative. -/
theorem basisFor_rep : BasisFor repSemigroup basis :=
  basisFor_of_fingerprints repSemigroup models_rep
    S6_11405Data.separatorValuations repFingerprints_nodup

end SemigroupBasis.CoRoots.Order6LeeLiP2G2.Injection
