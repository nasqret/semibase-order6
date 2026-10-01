import SemigroupBasis.CoRoots.Order6SporadicSection13Derivations
import SemigroupBasis.CoRoots.S5_254Assembly
import SemigroupBasis.CoRoots.S5_870GapBlocks
import SemigroupBasis.Examples.CyclicTwo
import SemigroupBasis.Examples.FinalMarkerThree

namespace SemigroupBasis.CoRoots.Order6SporadicSection13

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_870

def parityBlock (letters : List Nat) : List Nat :=
  S5_254.canonicalGapParityResidue letters

/-- Replace every first-occurrence gap by its deterministic parity residue. -/
def renderParityGapBlocks :
    List FirstOccurrenceGapBlock → List Nat
  | [] => []
  | block :: rest =>
      block.marker ::
        (parityBlock block.seconds ++ renderParityGapBlocks rest)

def canonicalPrefix (letters : List Nat) : List Nat :=
  renderParityGapBlocks (gapBlocksList letters)

/-- Split off the final letter and normalize every preceding first-occurrence
gap modulo two.  The final letter supplies a nonempty context throughout. -/
def canonicalWord (word : Word Nat) : Word Nat :=
  let split := splitPrefixFinal word
  wordOfPrefixFinal (canonicalPrefix split.1) split.2

private theorem source_mem_of_parityReduce_mem
    {letter : Nat} {letters : List Nat}
    (member : letter ∈ parityReduce letters) :
    letter ∈ letters := by
  have odd := (mem_parityReduce_iff letter letters).1 member
  apply List.count_pos_iff.mp
  omega

private theorem parityReduce_count
    (letters : List Nat) (tested : Nat) :
    (parityReduce letters).count tested =
      letters.count tested % 2 := by
  have nodup := parityReduce_nodup letters
  rw [nodup.count]
  simp only [mem_parityReduce_iff]
  by_cases odd : letters.count tested % 2 = 1
  · simp [odd]
  · have even : letters.count tested % 2 = 0 := by omega
    simp [odd, even]

private theorem parityReduce_perm_parityBlock
    (letters : List Nat) :
    (parityReduce letters).Perm (parityBlock letters) := by
  have sortedEq :=
    S5_254.canonicalGapResidue_eq_parityResidue
      letters (parityReduce letters) (parityReduce_count letters)
  have sortedPerm :
      (S5_254.canonicalGapResidue (parityReduce letters)).Perm
        (parityReduce letters) :=
    List.mergeSort_perm
      (parityReduce letters)
      (fun left right : Nat => decide (left ≤ right))
  rw [sortedEq] at sortedPerm
  exact sortedPerm.symm

theorem parityBlock_nodup (letters : List Nat) :
    (parityBlock letters).Nodup := by
  exact (parityReduce_perm_parityBlock letters).nodup_iff.mp
    (parityReduce_nodup letters)

theorem mem_of_mem_parityBlock
    {letter : Nat} {letters : List Nat}
    (member : letter ∈ parityBlock letters) :
    letter ∈ letters := by
  have reduced : letter ∈ parityReduce letters :=
    (parityReduce_perm_parityBlock letters).mem_iff.mpr member
  exact source_mem_of_parityReduce_mem reduced

/-- Normalize one later-occurrence block by suffix induction.  A duplicated
parity bit is exposed as an adjacent pair, then removed using the earlier copy
already present in `prefix`. -/
theorem listDerivesParityReduceAfterSeen
    (suffix : List Nat) (suffixNonempty : suffix ≠ []) :
    ∀ (stem letters : List Nat),
      (∀ letter, letter ∈ letters → letter ∈ stem) →
      ListDerives
        (stem ++ letters ++ suffix)
        (stem ++ parityReduce letters ++ suffix)
  | stem, [], _ => by
      simpa [parityReduce] using
        (S5_107.ListDerives.refl (basis := basis) (stem ++ suffix))
  | stem, head :: tail, lettersSeen => by
      have tailSeen :
          ∀ letter, letter ∈ tail →
            letter ∈ stem ++ [head] := by
        intro letter member
        exact List.mem_append.mpr <| Or.inl <|
          lettersSeen letter (List.Mem.tail head member)
      have tailDerivation :=
        listDerivesParityReduceAfterSeen suffix suffixNonempty
          (stem ++ [head]) tail tailSeen
      by_cases member : head ∈ parityReduce tail
      · have headSeen : head ∈ stem :=
          lettersSeen head (List.Mem.head tail)
        have reducedSeen :
            ∀ letter, letter ∈ parityReduce tail →
              letter ∈ stem := by
          intro letter reducedMember
          exact lettersSeen letter <| List.Mem.tail head <|
            source_mem_of_parityReduce_mem reducedMember
        have blockSeen :
            ∀ letter, letter ∈ head :: parityReduce tail →
              letter ∈ stem := by
          intro letter blockMember
          rcases List.mem_cons.mp blockMember with equal | reducedMember
          · simpa [equal] using headSeen
          · exact reducedSeen letter reducedMember
        have expose :
            (head :: parityReduce tail).Perm
              (head :: head :: (parityReduce tail).erase head) :=
          List.Perm.cons head (List.perm_cons_erase member)
        have arranged :=
          listDerivesPermuteAfterSeen
            stem suffix blockSeen expose
        have remainingNonempty :
            (parityReduce tail).erase head ++ suffix ≠ [] := by
          intro empty
          exact suffixNonempty (List.append_eq_nil_iff.mp empty).2
        have deleted :=
          listDerivesDeleteAdjacentPairAfterPrefix
            stem ((parityReduce tail).erase head ++ suffix)
            head headSeen remainingNonempty
        have deleted' :
            ListDerives
              (stem ++
                (head :: head :: (parityReduce tail).erase head) ++ suffix)
              (stem ++ (parityReduce tail).erase head ++ suffix) := by
          simpa [List.append_assoc] using deleted
        have cancelled :
            ListDerives
              (stem ++ [head] ++ parityReduce tail ++ suffix)
              (stem ++ (parityReduce tail).erase head ++ suffix) := by
          simpa [List.append_assoc] using arranged.trans deleted'
        exact by
          simpa [parityReduce, member, List.append_assoc] using
            tailDerivation.trans cancelled
      · simpa [parityReduce, member, List.append_assoc] using
          tailDerivation

/-- Sort the duplicate-free residue after pair cancellation. -/
theorem listDerivesParityBlockAfterSeen
    (stem letters suffix : List Nat)
    (lettersSeen : ∀ letter, letter ∈ letters → letter ∈ stem)
    (suffixNonempty : suffix ≠ []) :
    ListDerives
      (stem ++ letters ++ suffix)
      (stem ++ parityBlock letters ++ suffix) := by
  have reduced :=
    listDerivesParityReduceAfterSeen suffix suffixNonempty
      stem letters lettersSeen
  have reducedSeen :
      ∀ letter, letter ∈ parityReduce letters → letter ∈ stem := by
    intro letter member
    exact lettersSeen letter (source_mem_of_parityReduce_mem member)
  have sorted :=
    listDerivesPermuteAfterSeen stem suffix reducedSeen
      (parityReduce_perm_parityBlock letters)
  exact reduced.trans sorted

/-- Normalize every parsed prefix block while retaining a fixed final letter.
`seen` is the reverse marker list used by the parser; `seenInPrefix` records
that all of those protected first copies remain in the derivation prefix. -/
theorem listDerivesNormalizeGapBlocks
    (final : Nat)
    {seen : List Nat} {blocks : List FirstOccurrenceGapBlock}
    (formed : GapBlocksWellFormed seen blocks)
    (stem : List Nat)
    (seenInPrefix : ∀ letter, letter ∈ seen → letter ∈ stem) :
    ListDerives
      (stem ++ renderGapBlocks blocks ++ [final])
      (stem ++ renderParityGapBlocks blocks ++ [final]) := by
  induction formed generalizing stem with
  | nil =>
      simpa [renderGapBlocks, renderParityGapBlocks] using
        (S5_107.ListDerives.refl (basis := basis) (stem ++ [final]))
  | cons seen block rest markerFresh secondsSeen tailFormed induction =>
      have currentSeen :
          ∀ letter, letter ∈ block.seconds →
            letter ∈ stem ++ [block.marker] := by
        intro letter member
        rcases List.mem_cons.mp (secondsSeen letter member) with
          atMarker | inSeen
        · subst letter
          simp
        · exact List.mem_append.mpr <| Or.inl <|
            seenInPrefix letter inSeen
      have current :=
        listDerivesParityBlockAfterSeen
          (stem ++ [block.marker]) block.seconds
          (renderGapBlocks rest ++ [final]) currentSeen (by simp)
      have nextSeenInPrefix :
          ∀ letter, letter ∈ block.marker :: seen →
            letter ∈
              stem ++ [block.marker] ++ parityBlock block.seconds := by
        intro letter member
        rcases List.mem_cons.mp member with atMarker | inSeen
        · subst letter
          simp
        · exact List.mem_append.mpr <| Or.inl <|
            List.mem_append.mpr <| Or.inl <|
              seenInPrefix letter inSeen
      have recurse :=
        induction
          (stem ++ [block.marker] ++ parityBlock block.seconds)
          nextSeenInPrefix
      have recurse' :
          ListDerives
            ((stem ++ [block.marker]) ++ parityBlock block.seconds ++
              (renderGapBlocks rest ++ [final]))
            ((stem ++ [block.marker]) ++ parityBlock block.seconds ++
              (renderParityGapBlocks rest ++ [final])) := by
        simpa [List.append_assoc] using recurse
      simpa [renderGapBlocks, renderParityGapBlocks,
        List.append_assoc] using current.trans recurse'

/-- Prefix normalization with the final marker retained literally. -/
theorem listDerivesCanonicalPrefixFinal
    (stem : List Nat) (final : Nat) :
    ListDerives
      (stem ++ [final])
      (canonicalPrefix stem ++ [final]) := by
  have normalized :=
    listDerivesNormalizeGapBlocks final
      (gapBlocksList_wellFormed stem) [] (by simp)
  simpa [canonicalPrefix, render_gapBlocksList] using normalized

theorem toList_eq_splitPrefixFinal (word : Word Nat) :
    word.toList =
      (splitPrefixFinal word).1 ++ [(splitPrefixFinal word).2] := by
  have reconstructed :=
    congrArg Word.toList (wordOfPrefixFinal_split word)
  rw [toList_wordOfPrefixFinal] at reconstructed
  exact reconstructed.symm

theorem canonicalWord_toList (word : Word Nat) :
    (canonicalWord word).toList =
      canonicalPrefix (splitPrefixFinal word).1 ++
        [(splitPrefixFinal word).2] := by
  simp [canonicalWord, toList_wordOfPrefixFinal]

theorem listDerivesCanonicalWord (word : Word Nat) :
    ListDerives word.toList (canonicalWord word).toList := by
  rw [toList_eq_splitPrefixFinal, canonicalWord_toList]
  exact listDerivesCanonicalPrefixFinal
    (splitPrefixFinal word).1 (splitPrefixFinal word).2

theorem derives_of_listDerives_toList
    (left right : Word Nat)
    (derivation : ListDerives left.toList right.toList) :
    Derives basis left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simpa [S5_107.listWordOfCons] using
            S5_107.ListDerives.toWord derivation

/-- Unrestricted derivation to the parity-block renderer.  Completeness later
uses this theorem only when the original final letter is globally simple. -/
theorem derivesCanonicalWord (word : Word Nat) :
    Derives basis word (canonicalWord word) :=
  derives_of_listDerives_toList word (canonicalWord word)
    (listDerivesCanonicalWord word)

end SemigroupBasis.CoRoots.Order6SporadicSection13
