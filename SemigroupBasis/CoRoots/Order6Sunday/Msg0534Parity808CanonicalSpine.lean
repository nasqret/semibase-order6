import SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808Canonical
import SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808LastNecessary
import SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808SignatureInvariant
import SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808RunMultiplicity

/-! Connect the callable canonicalizer to actual factor observations. Its block
keys are distinct, counts are exact, and joint validity determines both the
distinguished terminal block and the prefix block multiset. Equality of the
singleton-separated runs is a further obligation, not a premise stamped here. -/
namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0534Parity808CanonicalSpine

open SemigroupBasis
open Msg0524Parity808Gather
open Msg0524Parity808Blocks
open Msg0524Parity808RunSort
open Msg0524Parity808Canonical
open Msg0524Parity808LastNecessary
open Msg0524Parity808SignatureInvariant
open Msg0524Parity808RunMultiplicity

theorem spine_keys_mem (fuel : Nat) (word : List Nat) (letter : Nat) :
    letter ∈ (spine fuel word).map Prod.fst ↔ letter ∈ word := by
  induction fuel generalizing word with
  | zero => simp [spine, List.map_map]
  | succ fuel ih =>
    cases reversed : word.reverse with
    | nil =>
      have empty : word = [] := by simpa using congrArg List.reverse reversed
      subst word
      simp [spine]
    | cons a stem =>
      have represented : word = stem.reverse ++ [a] := by
        simpa using congrArg List.reverse reversed
      simp only [spine,reversed,List.map_append,List.map_cons,List.map_nil,
        List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
      rw [ih]
      simp only [eraseLetter,List.mem_filter,bne_iff_ne]
      rw [represented]
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
      by_cases same : letter = a <;> simp [same]

theorem spine_keys_nodup (fuel : Nat) (word : List Nat) (enough : word.length ≤ fuel) :
    ((spine fuel word).map Prod.fst).Nodup := by
  induction fuel generalizing word with
  | zero =>
    cases word with
    | nil => exact List.nodup_nil
    | cons a tail => simp at enough
  | succ fuel ih =>
    cases reversed : word.reverse with
    | nil =>
      have empty : word = [] := by simpa using congrArg List.reverse reversed
      subst word
      exact List.nodup_nil
    | cons a stem =>
      have represented : word = stem.reverse ++ [a] := by
        simpa using congrArg List.reverse reversed
      have small : (eraseLetter a stem.reverse).length ≤ fuel := by
        have bound := List.length_filter_le (fun b => b != a) stem.reverse
        simp only [List.length_reverse] at bound
        rw [represented,List.length_append,List.length_reverse,List.length_singleton] at enough
        unfold eraseLetter
        omega
      have absent : a ∉ (spine fuel (eraseLetter a stem.reverse)).map Prod.fst := by
        rw [spine_keys_mem]
        simp [eraseLetter]
      simp only [spine,reversed,List.map_append,List.map_cons,List.map_nil]
      apply List.nodup_append.mpr
      refine ⟨ih _ small, by simp, ?_⟩
      intro x member y last same
      have ya : y = a := by simpa using last
      have xa : x = a := same.trans ya
      exact absent (xa ▸ member)

def blocks (word : Word Nat) : List (Nat × Nat) :=
  terminalSort (spine word.toList.length word.toList)

theorem blocks_render (word : Word Nat) : render (blocks word) = canonical word.toList := rfl

theorem blocks_distinct (word : Word Nat) : ((blocks word).map Prod.fst).Nodup := by
  have perm := (terminalSort_perm (spine word.toList.length word.toList)).map Prod.fst
  exact perm.nodup_iff.mpr (spine_keys_nodup _ _ (Nat.le_refl _))

theorem blocks_count (word : Word Nat) (letter : Nat) :
    (render (blocks word)).count letter = reducedExponent (word.toList.count letter) :=
  canonical_count word.toList letter

theorem block_multiplicity (word : Word Nat) (block : Nat × Nat) (member : block ∈ blocks word) :
    block.2 + 1 = reducedExponent (word.toList.count block.1) :=
  (render_count_of_mem (blocks word) (blocks_distinct word) block member).symm.trans
    (blocks_count word block.1)

theorem block_excess_bound (word : Word Nat) (block : Nat × Nat) (member : block ∈ blocks word) :
    block.2 ≤ 2 := by
  have exactCount := block_multiplicity word block member
  have bound := reducedExponent_bound (word.toList.count block.1)
  omega

theorem reduced_counts_eq {left right : Word Nat} (same : JointSignature left right) (letter : Nat) :
    reducedExponent (left.toList.count letter) = reducedExponent (right.toList.count letter) :=
  (reducedExponent_eq_iff_cap_parity _ _).mpr
    ⟨reversed_signature_capped same.2 letter, same.1.2 letter⟩

theorem blocks_counts_eq {left right : Word Nat} (same : JointSignature left right) (letter : Nat) :
    (render (blocks left)).count letter = (render (blocks right)).count letter := by
  rw [blocks_count,blocks_count]
  exact reduced_counts_eq same letter

theorem blocks_perm {left right : Word Nat} (same : JointSignature left right) :
    (blocks left).Perm (blocks right) :=
  perm_of_render_counts _ _ (blocks_distinct left) (blocks_distinct right) (blocks_counts_eq same)

theorem spine_snoc (fuel : Nat) (stem : List Nat) (last : Nat) :
    spine (fuel+1) (stem ++ [last]) =
      spine fuel (eraseLetter last stem) ++ [(last,reducedExponent (stem.count last+1)-1)] := by
  simp only [spine,List.reverse_append,List.reverse_cons,List.reverse_nil,
    List.cons_append,List.nil_append,List.reverse_reverse]

theorem terminalSort_snoc (stemBlocks : List (Nat × Nat)) (last : Nat × Nat) :
    terminalSort (stemBlocks ++ [last]) = sortRuns stemBlocks ++ [last] := by
  simp only [terminalSort,List.reverse_append,List.reverse_cons,List.reverse_nil,
    List.cons_append,List.nil_append,List.reverse_reverse]

def terminalBlock (word : Word Nat) : Nat × Nat :=
  (word.reverse.head,reducedExponent (word.toList.count word.reverse.head)-1)

def canonicalPrefix (word : Word Nat) : List (Nat × Nat) :=
  sortRuns (spine word.reverse.tail.length (eraseLetter word.reverse.head word.reverse.tail.reverse))

theorem word_snoc (word : Word Nat) :
    word.toList = word.reverse.tail.reverse ++ [word.reverse.head] := by
  calc
    word.toList = word.toList.reverse.reverse := (List.reverse_reverse _).symm
    _ = word.reverse.toList.reverse := congrArg List.reverse (Word.toList_reverse word).symm
    _ = word.reverse.tail.reverse ++ [word.reverse.head] := List.reverse_cons

theorem blocks_decomposition (word : Word Nat) :
    blocks word = canonicalPrefix word ++ [terminalBlock word] := by
  unfold blocks
  rw [word_snoc word]
  simp only [List.length_append,List.length_reverse,List.length_singleton]
  rw [spine_snoc,terminalSort_snoc]
  simp only [canonicalPrefix,terminalBlock,word_snoc word,List.count_append,
    List.count_cons_self,List.count_nil,Nat.zero_add]

theorem terminalBlock_eq {left right : Word Nat} (same : JointSignature left right) :
    terminalBlock left = terminalBlock right := by
  apply Prod.ext same.2.head
  change reducedExponent (left.toList.count left.reverse.head)-1 =
    reducedExponent (right.toList.count right.reverse.head)-1
  rw [← same.2.head]
  exact congrArg (fun n : Nat => n-1) (reduced_counts_eq same left.reverse.head)

theorem canonicalPrefix_distinct (word : Word Nat) :
    ((canonicalPrefix word).map Prod.fst).Nodup := by
  have distinct := blocks_distinct word
  rw [blocks_decomposition,List.map_append] at distinct
  exact (List.nodup_append.mp distinct).1

theorem canonicalPrefix_counts_eq {left right : Word Nat}
    (same : JointSignature left right) (letter : Nat) :
    (render (canonicalPrefix left)).count letter = (render (canonicalPrefix right)).count letter := by
  have counts := blocks_counts_eq same letter
  rw [blocks_decomposition,blocks_decomposition,terminalBlock_eq same] at counts
  simp only [render,List.flatMap_append,List.count_append] at counts
  exact Nat.add_right_cancel counts

theorem canonicalPrefix_perm {left right : Word Nat} (same : JointSignature left right) :
    (canonicalPrefix left).Perm (canonicalPrefix right) :=
  perm_of_render_counts _ _ (canonicalPrefix_distinct left) (canonicalPrefix_distinct right)
    (canonicalPrefix_counts_eq same)

theorem canonical_signature {left right : Word Nat} (same : JointSignature left right) :
    S5_848.SameTailSquareSignature (canonicalWord left).reverse (canonicalWord right).reverse :=
  ((rawDerives_tailSignature (canonicalWord_derives left)).symm.trans same.2).trans
    (rawDerives_tailSignature (canonicalWord_derives right))

theorem actualFactors_blocks (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy Msg0524Parity808FactorEval.factor)
    (rightValid : identity.SatisfiedBy rightFactor) :
    (blocks identity.lhs).Perm (blocks identity.rhs) ∧
      terminalBlock identity.lhs = terminalBlock identity.rhs ∧
      (canonicalPrefix identity.lhs).Perm (canonicalPrefix identity.rhs) := by
  have same := joint_signature_necessary identity leftValid rightValid
  exact ⟨blocks_perm same,terminalBlock_eq same,canonicalPrefix_perm same⟩

end SemigroupBasis.CoRoots.Order6Sunday.Msg0534Parity808CanonicalSpine
