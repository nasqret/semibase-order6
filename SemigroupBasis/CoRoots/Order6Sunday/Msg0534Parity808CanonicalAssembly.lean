import SemigroupBasis.CoRoots.Order6Sunday.Msg0534Parity808CanonicalSpine

/-! Exact assembly boundary for the remaining Parity808 run comparison.
SameRunCounts is stated explicitly, never inferred from a finite screen.
As a genuine unrestricted fragment, no-simple-variable left words need no
gap comparison: actual factor validity then gives a raw-basis derivation. -/
namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0534Parity808CanonicalAssembly

open SemigroupBasis
open Msg0524Parity808Gather
open Msg0524Parity808RunSort
open Msg0524Parity808RunNormal
open Msg0524Parity808RunUnique
open Msg0524Parity808RunMultiplicity
open Msg0524Parity808Canonical
open Msg0524Parity808LastNecessary
open Msg0534Parity808CanonicalSpine

theorem canonicalPrefix_fixed (word : Word Nat) :
    sortRuns (canonicalPrefix word) = canonicalPrefix word := sortRuns_idempotent _

theorem blocks_eq_of_runCounts {left right : Word Nat} (same : JointSignature left right)
    (runs : SameRunCounts (canonicalPrefix left) (canonicalPrefix right)) :
    blocks left = blocks right := by
  have stems := sameRunCounts_sort_eq runs
  rw [canonicalPrefix_fixed,canonicalPrefix_fixed] at stems
  rw [blocks_decomposition,blocks_decomposition,stems,terminalBlock_eq same]

theorem canonicalWord_eq_of_runCounts {left right : Word Nat} (same : JointSignature left right)
    (runs : SameRunCounts (canonicalPrefix left) (canonicalPrefix right)) :
    canonicalWord left = canonicalWord right := by
  apply Word.toList_injective
  rw [canonicalWord_toList,canonicalWord_toList,← blocks_render,← blocks_render,
    blocks_eq_of_runCounts same runs]

theorem derives_of_runCounts {left right : Word Nat} (same : JointSignature left right)
    (runs : SameRunCounts (canonicalPrefix left) (canonicalPrefix right)) :
    Derives basis left right := by
  have first := canonicalWord_derives left
  rw [canonicalWord_eq_of_runCounts same runs] at first
  exact first.trans (canonicalWord_derives right).symm

theorem pure_runCounts {left right : Word Nat} (same : JointSignature left right)
    (pure : AllRepeated (canonicalPrefix left)) :
    SameRunCounts (canonicalPrefix left) (canonicalPrefix right) :=
  SameRunCounts.last _ _ (canonicalPrefix_distinct left) (canonicalPrefix_distinct right)
    pure (canonicalPrefix_counts_eq same)

theorem derives_of_pure_prefix {left right : Word Nat} (same : JointSignature left right)
    (pure : AllRepeated (canonicalPrefix left)) : Derives basis left right :=
  derives_of_runCounts same (pure_runCounts same pure)

theorem blocks_support (word : Word Nat) (letter : Nat) :
    letter ∈ (blocks word).map Prod.fst ↔ letter ∈ word.toList := by
  have perm := (terminalSort_perm (spine word.toList.length word.toList)).map Prod.fst
  exact perm.mem_iff.trans (spine_keys_mem _ _ letter)

theorem prefix_pure_of_no_simple (word : Word Nat)
    (repeated : ∀ letter ∈ word.toList, 2 ≤ word.toList.count letter) :
    AllRepeated (canonicalPrefix word) := by
  intro block member single
  have fullMember : block ∈ blocks word := by
    rw [blocks_decomposition]
    exact List.mem_append_left _ member
  have inWord : block.1 ∈ word.toList :=
    (blocks_support word block.1).mp (List.mem_map_of_mem fullMember)
  have large := repeated block.1 inWord
  have reducedLarge : 2 ≤ reducedExponent (word.toList.count block.1) := by
    rw [reducedExponent,if_neg (by omega : ¬word.toList.count block.1 < 2)]
    omega
  have multiplicity := block_multiplicity word block fullMember
  rw [single] at multiplicity
  omega

theorem no_simple_complete (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy Msg0524Parity808FactorEval.factor)
    (rightValid : identity.SatisfiedBy rightFactor)
    (repeated : ∀ letter ∈ identity.lhs.toList, 2 ≤ identity.lhs.toList.count letter) :
    Derives basis identity.lhs identity.rhs :=
  derives_of_pure_prefix (joint_signature_necessary identity leftValid rightValid)
    (prefix_pure_of_no_simple identity.lhs repeated)

end SemigroupBasis.CoRoots.Order6Sunday.Msg0534Parity808CanonicalAssembly
