import SemigroupBasis.CoRoots.Order6Astra.C8CanonicalBranches
import SemigroupBasis.CoRoots.Order6Astra.C8BranchAlgebra

namespace SemigroupBasis.CoRoots.Order6Astra.C8RawChain

open Order6SporadicSection19.Published
open MaximalFactors C8BranchPieces C8CanonicalBranches C8BranchAlgebra

/-- Empty lists are literal empty gaps, not substitution words. -/
def rawChain (separator : Word Nat) : List (List Nat) → Word Nat
  | [] => separator
  | [] :: rest => separator ++ rawChain separator rest
  | (x :: xs) :: rest => (separator ++ (⟨x, xs⟩ : Word Nat)) ++ rawChain separator rest

def pack : List (List Nat) → List (Word Nat)
  | [] => []
  | [] :: rest => pack rest
  | (x :: xs) :: rest => (⟨x, xs⟩ : Word Nat) :: pack rest

theorem square_idempotent (root : Word Nat) :
    Derives basis ((root ++ root) ++ (root ++ root)) (root ++ root) := by
  have cube : Derives basis ((root ++ root) ++ root) (root ++ root) :=
    Derives.subst derives_a_cube (fun _ => root)
  simpa only [Word.append_assoc] using (Derives.appendRight cube root).trans cube

theorem absorb_initial (separator : Word Nat)
    (idem : Derives basis (separator ++ separator) separator) (branches : List (Word Nat)) :
    Derives basis (separator ++ chain separator branches) (chain separator branches) := by
  cases branches with
  | nil => exact idem
  | cons b rest =>
    simpa only [chain, Word.append_assoc] using
      Derives.appendRight idem (b ++ chain separator rest)

/-- Empty gaps are removed by the actual idempotence derivation, not erased
from syntax without a proof. Nonempty branch words remain unchanged. -/
theorem raw_to_chain (separator : Word Nat)
    (idem : Derives basis (separator ++ separator) separator) (gaps : List (List Nat)) :
    Derives basis (rawChain separator gaps) (chain separator (pack gaps)) := by
  induction gaps with
  | nil => exact Derives.refl _
  | cons gap rest ih =>
    cases gap with
    | nil => exact (Derives.prepend separator ih).trans (absorb_initial separator idem _)
    | cons x xs => exact Derives.prepend (separator ++ (⟨x, xs⟩ : Word Nat)) ih

theorem raw_pieces (separator : Word Nat) (gaps : List (List (Word Nat))) :
    (rawChain separator (gaps.map flatten)).toList =
      separator.toList ++ flatten (afterPieces separator gaps) := by
  induction gaps with
  | nil => simp only [List.map_nil, rawChain, afterPieces, flatten, List.append_nil]
  | cons gap rest ih =>
    simp only [List.map_cons, afterPieces, FactorBoundaries.flatten_append, flatten]
    cases h : flatten gap with
    | nil =>
      simp only [rawChain, Word.toList_append, ih, List.nil_append]
    | cons x xs =>
      rw [rawChain, Word.toList_append, Word.toList_append, ih]
      simp only [List.append_assoc]
      rfl

theorem decomposition_to_chain (word : Word Nat) (d : Decomposition word) :
    Derives basis word (chain (d.root ++ d.root) (pack (d.gaps.map flatten))) := by
  have literal : word = rawChain (d.root ++ d.root) (d.gaps.map flatten) :=
    Word.toList_injective (d.literal.trans (raw_pieces (d.root ++ d.root) d.gaps).symm)
  exact Eq.mpr (congrArg (fun source =>
    Derives basis source (chain (d.root ++ d.root) (pack (d.gaps.map flatten)))) literal)
    (raw_to_chain (d.root ++ d.root) (square_idempotent d.root) _)

theorem mem_pack (gaps : List (List Nat)) (word : Word Nat) :
    word ∈ pack gaps ↔ word.toList ∈ gaps := by
  induction gaps with
  | nil => simp only [pack, List.not_mem_nil]
  | cons gap rest ih =>
    cases gap with
    | nil =>
      rw [pack, ih, List.mem_cons]
      have ne : word.toList ≠ [] := by cases word; simp [Word.toList]
      simp only [ne, false_or]
    | cons x xs =>
      rw [pack, List.mem_cons, List.mem_cons, ih]
      have equal : word = (⟨x, xs⟩ : Word Nat) ↔ word.toList = x :: xs := by
        constructor
        · intro h
          subst word
          rfl
        · intro h
          exact Word.toList_injective h
      rw [equal]

/-- Every retained branch comes from a real nonempty gap of the original
decomposition. Its terminal marker remains simple in the original word. -/
theorem packed_branch (word : Word Nat) (d : Decomposition word) (branch : Word Nat)
    (member : branch ∈ pack (d.gaps.map flatten)) :
    C8TailCuts.Disjoint branch.toList d.root.toList ∧
      ∃ leading : List Nat, ∃ marker : Nat,
        branch.toList = leading ++ [marker] ∧ word.toList.count marker = 1 := by
  have present := (mem_pack (d.gaps.map flatten) branch).mp member
  obtain ⟨gap, gapMember, equal⟩ := List.mem_map.mp present
  have nonempty : gap ≠ [] := by
    intro empty
    subst gap
    have impossible : branch.toList = [] := equal.symm
    cases branch
    cases impossible
  have marker := d.markers gap gapMember nonempty
  rw [equal] at marker
  refine ⟨?_, marker⟩
  simpa only [equal] using d.root_apart gap gapMember

end SemigroupBasis.CoRoots.Order6Astra.C8RawChain

#print axioms SemigroupBasis.CoRoots.Order6Astra.C8RawChain.raw_to_chain
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8RawChain.decomposition_to_chain
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8RawChain.packed_branch
