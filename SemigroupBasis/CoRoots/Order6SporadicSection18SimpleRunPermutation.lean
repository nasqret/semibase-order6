import SemigroupBasis.CoRoots.Order6SporadicSection18SimpleRunScanner
import SemigroupBasis.CoRoots.Order6SporadicSection18ActualAdjacency

/-! Lemma18.8(i,ii): canonical simple factors agree up to permutation, with
equal factor counts. Only generic path combinatorics is reused from S5_107;
the semantic hypotheses are proved for the actual C7 table. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
open SemigroupBasis

/-- The complete witness matrix of the frozen CanonicalForm definition,
with its alphabet and chain kept explicit for subsequent comparison proofs. -/
def CanonicalWitness (whole alphabet : List Nat) (first : Slot) (rest : List Slot) : Prop :=
  alphabet.Pairwise (· < ·) ∧ alphabet.Nodup ∧
  (∀ x, x ∈ alphabet ↔ x ∈ whole ∧ whole.count x ≠ 1) ∧
  rest ≠ [] ∧ first.gap = [] ∧ (∀ slot ∈ rest, slot.gap ≠ []) ∧
  (∀ slot ∈ first :: rest, ∀ x ∈ slot.gap, whole.count x = 1) ∧
  CanonicalChain alphabet (first :: rest) ∧ render (first :: rest) = whole

theorem CanonicalWitness.form {whole alphabet : List Nat} {first : Slot} {rest : List Slot}
    (witness : CanonicalWitness whole alphabet first rest) : CanonicalForm whole :=
  ⟨alphabet, first, rest, witness⟩

theorem CanonicalWitness.simpleBlocks {whole alphabet : List Nat} {first : Slot} {rest : List Slot}
    (witness : CanonicalWitness whole alphabet first rest) :
    S5_107.simpleBlocks whole = rest.map Slot.gap := by
  obtain ⟨_, _, exactAlphabet, _, firstEmpty, laterNonempty, simple, canonical, shape⟩ := witness
  apply canonicalGapScanner whole first rest shape firstEmpty laterNonempty
  · intro slot member
    exact (canonical.1 slot member).1
  · intro slot member x present
    exact ((exactAlphabet x).mp ((canonical.1 slot member).bounded x present)).2
  · exact simple

private theorem render_endsWithN (whole : List Nat) :
    ∀ (first : Slot) (rest : List Slot),
      (∀ slot ∈ first :: rest, slot.block ≠ []) →
      (∀ slot ∈ first :: rest, ∀ x ∈ slot.block, whole.count x ≠ 1) →
      EndsWithN (fun x => whole.count x ≠ 1) (render (first :: rest))
  | first, [], nonempty, nonsimple => by
      have squareNonempty : squareList first.block ≠ [] := by
        obtain ⟨head, tail, shape⟩ := List.exists_cons_of_ne_nil
          (nonempty first (List.Mem.head []))
        rw [shape, squareList_cons]
        simp
      have reverseNonempty : (squareList first.block).reverse ≠ [] := by
        simpa using squareNonempty
      obtain ⟨last, beforeRev, reverseShape⟩ := List.exists_cons_of_ne_nil reverseNonempty
      have squareShape : squareList first.block = beforeRev.reverse ++ [last] := by
        simpa only [List.reverse_reverse, List.reverse_cons] using
          congrArg List.reverse reverseShape
      have member : last ∈ squareList first.block := by
        rw [squareShape]
        simp
      refine ⟨first.gap ++ beforeRev.reverse, last, ?_,
        nonsimple first (List.Mem.head []) last ((squareList_mem first.block last).mp member)⟩
      simp only [render, List.append_nil, squareShape, List.append_assoc]
  | first, next :: tail, nonempty, nonsimple => by
      obtain ⟨before, last, shape, notOne⟩ := render_endsWithN whole next tail
        (fun slot member => nonempty slot (List.Mem.tail first member))
        (fun slot member => nonsimple slot (List.Mem.tail first member))
      refine ⟨(first.gap ++ squareList first.block) ++ before, last, ?_, notOne⟩
      simpa only [render, List.append_assoc] using
        congrArg (fun letters => (first.gap ++ squareList first.block) ++ letters) shape

theorem CanonicalForm.nonsimpleEnds {letters : List Nat} (formed : CanonicalForm letters) :
    StartsN letters ∧ EndsN letters := by
  obtain ⟨first, rest, shape, firstEmpty, _, _, properties, _, _⟩ := formed.explicitBlocks
  have member : first ∈ first :: rest := List.Mem.head rest
  have nonempty : ∀ slot ∈ first :: rest, slot.block ≠ [] :=
    fun slot present => (properties slot present).1
  have nonsimple : ∀ slot ∈ first :: rest, ∀ x ∈ slot.block, letters.count x ≠ 1 :=
    fun slot present => (properties slot present).2.2.2.1
  obtain ⟨head, tail, blockShape⟩ := List.exists_cons_of_ne_nil (nonempty first member)
  have beginning : letters = head :: (head :: (squareList tail ++ render rest)) := by
    simpa only [render, firstEmpty, List.nil_append, blockShape, squareList_cons,
      List.cons_append, List.append_assoc] using shape.symm
  refine ⟨⟨head, head :: (squareList tail ++ render rest), beginning,
    nonsimple first member head (by simp [blockShape])⟩, ?_⟩
  simpa only [EndsN, shape] using render_endsWithN letters first rest nonempty nonsimple

private theorem no_simpleInitial {word : Word Nat} (starts : StartsN word.toList) (x : Nat) :
    ¬ S5_107.SimpleInitial word x := by
  obtain ⟨head, tail, shape, nonsimple⟩ := starts
  change word.head :: word.tail = head :: tail at shape
  have heads := (List.cons.inj shape).1
  rintro ⟨simple, initial⟩
  have equal : x = head := initial.symm.trans heads
  exact nonsimple (by simpa only [S5_107.SimpleIn, equal] using simple)

private theorem word_toList_eq_prefix_final (word : Word Nat) :
    ∃ initial, word.toList = initial ++ [word.final] := by
  cases word with
  | mk head tail =>
      refine ⟨(head :: tail).dropLast, ?_⟩
      have reconstruct := (List.dropLast_concat_getLast (l := head :: tail) (by simp)).symm
      rw [List.getLast_eq_getLastD] at reconstruct
      simpa [Word.toList, Word.final] using reconstruct

private theorem no_simpleFinal {word : Word Nat} (ends : EndsN word.toList) (x : Nat) :
    ¬ S5_107.SimpleFinal word x := by
  obtain ⟨before, last, shape, nonsimple⟩ := ends
  obtain ⟨initial, finalShape⟩ := word_toList_eq_prefix_final word
  have reversed := congrArg List.reverse (finalShape.symm.trans shape)
  have boundary : word.final :: initial.reverse = last :: before.reverse := by
    simpa only [List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append] using reversed
  have finals := (List.cons.inj boundary).1
  rintro ⟨simple, final⟩
  have equal : x = last := final.symm.trans finals
  exact nonsimple (by simpa only [S5_107.SimpleIn, equal] using simple)

theorem sameCappedMultiplicity {left right : Word Nat}
    (same : Actual.SameEval left.toList right.toList) (x : Nat) :
    S5_107.cappedMultiplicity left x = S5_107.cappedMultiplicity right x := by
  have absent : left.toList.count x = 0 ↔ right.toList.count x = 0 := by
    simpa only [List.count_eq_zero] using not_congr (same.mem x)
  have simple := same.countOne x
  unfold S5_107.cappedMultiplicity
  by_cases zeroLeft : left.toList.count x = 0
  · rw [zeroLeft, absent.mp zeroLeft]
  · by_cases oneLeft : left.toList.count x = 1
    · rw [oneLeft, simple.mp oneLeft]
    · have leftBound : 2 ≤ left.toList.count x := by omega
      have zeroRight : right.toList.count x ≠ 0 := fun zero => zeroLeft (absent.mpr zero)
      have oneRight : right.toList.count x ≠ 1 := fun one => oneLeft (simple.mpr one)
      have rightBound : 2 ≤ right.toList.count x := by omega
      exact (Nat.min_eq_left leftBound).trans (Nat.min_eq_left rightBound).symm

/-- This is a combinatorial signature, not an S5 identity or derivation.
Both marked-simple endpoint predicates are false on canonical C7 words. -/
theorem canonicalSimpleSignature {left right : Word Nat}
    (same : Actual.SameEval left.toList right.toList)
    (leftForm : CanonicalForm left.toList) (rightForm : CanonicalForm right.toList) :
    S5_107.SameSimpleAdjacencySignature left right := by
  have leftEnds := leftForm.nonsimpleEnds
  have rightEnds := rightForm.nonsimpleEnds
  refine ⟨sameCappedMultiplicity same, ?_, ?_, ?_⟩
  · intro x
    exact ⟨fun impossible => False.elim (no_simpleInitial leftEnds.1 x impossible),
      fun impossible => False.elim (no_simpleInitial rightEnds.1 x impossible)⟩
  · intro x
    exact ⟨fun impossible => False.elim (no_simpleFinal leftEnds.2 x impossible),
      fun impossible => False.elim (no_simpleFinal rightEnds.2 x impossible)⟩
  · intro x y
    simpa only [S5_107.SimpleAdjacent, S5_107.SimpleIn,
      S5_107.mem_adjacentPairs_iff_exists_split, Actual.SimpleAdjacent] using
        same.simpleAdjacent x y

theorem lemma18_8_simpleRuns {left right : Word Nat}
    (same : Actual.SameEval left.toList right.toList)
    (leftForm : CanonicalForm left.toList) (rightForm : CanonicalForm right.toList) :
    (S5_107.simpleBlocks left.toList).Perm (S5_107.simpleBlocks right.toList) :=
  (canonicalSimpleSignature same leftForm rightForm).simpleBlocks_perm

theorem canonicalGapPermutation {left right : Word Nat}
    {leftAlphabet rightAlphabet : List Nat} {leftFirst rightFirst : Slot}
    {leftRest rightRest : List Slot}
    (same : Actual.SameEval left.toList right.toList)
    (leftWitness : CanonicalWitness left.toList leftAlphabet leftFirst leftRest)
    (rightWitness : CanonicalWitness right.toList rightAlphabet rightFirst rightRest) :
    (leftRest.map Slot.gap).Perm (rightRest.map Slot.gap) ∧ leftRest.length = rightRest.length := by
  have permutation := lemma18_8_simpleRuns same leftWitness.form rightWitness.form
  rw [leftWitness.simpleBlocks, rightWitness.simpleBlocks] at permutation
  refine ⟨permutation, ?_⟩
  simpa only [List.length_map] using permutation.length_eq

/-- Both complete canonical witnesses are retained. The permutation and
equal length concern the literal gap lists in those same witnesses. -/
theorem lemma18_8_i_ii (identity : Identity Nat)
    (valid : identity.SatisfiedBy Actual.table.semigroup)
    (leftForm : CanonicalForm identity.lhs.toList) (rightForm : CanonicalForm identity.rhs.toList) :
    ∃ (leftAlphabet : List Nat) (leftFirst : Slot) (leftRest : List Slot)
      (rightAlphabet : List Nat) (rightFirst : Slot) (rightRest : List Slot),
      CanonicalWitness identity.lhs.toList leftAlphabet leftFirst leftRest ∧
      CanonicalWitness identity.rhs.toList rightAlphabet rightFirst rightRest ∧
      (leftRest.map Slot.gap).Perm (rightRest.map Slot.gap) ∧ leftRest.length = rightRest.length := by
  obtain ⟨leftAlphabet, leftFirst, leftRest, leftWitness⟩ :
      ∃ alphabet first rest, CanonicalWitness identity.lhs.toList alphabet first rest := leftForm
  obtain ⟨rightAlphabet, rightFirst, rightRest, rightWitness⟩ :
      ∃ alphabet first rest, CanonicalWitness identity.rhs.toList alphabet first rest := rightForm
  exact ⟨leftAlphabet, leftFirst, leftRest, rightAlphabet, rightFirst, rightRest,
    leftWitness, rightWitness,
    canonicalGapPermutation (Actual.sameEval_valid identity valid) leftWitness rightWitness⟩

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.CanonicalWitness.form
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.CanonicalWitness.simpleBlocks
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.CanonicalForm.nonsimpleEnds
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.sameCappedMultiplicity
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.canonicalSimpleSignature
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.lemma18_8_simpleRuns
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.canonicalGapPermutation
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.lemma18_8_i_ii

end SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
