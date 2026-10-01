import SemigroupBasis.CoRoots.Order6Astra.C8BranchSupport
import SemigroupBasis.CoRoots.Order6Astra.C8ListDerives

namespace SemigroupBasis.CoRoots.Order6Astra.C8Star

open Order6SporadicSection19.Published
open C8TailCuts C8BranchAlgebra C8RawChain C8CanonicalBranches C8BranchSupport
open RootFamily ConnectedTerminalEndpoints SemanticSimpleAdjacency

/-- One actual recursive layer, without a supplied normalizer or completeness
premise. Branch order remains free: the checked exchange law realizes it. -/
structure Star where
  root : Word Nat
  branches : List (Word Nat)
  shape : RootShape root
  pairwise : branches.Pairwise (fun u v => Disjoint u.toList v.toList)
  apart : ∀ branch ∈ branches, Disjoint branch.toList root.toList
  marked : ∀ branch ∈ branches, ∃ leading : List Nat, ∃ marker : Nat,
    branch.toList = leading ++ [marker] ∧ marker ∉ leading

def Star.word (star : Star) : Word Nat := chain (star.root ++ star.root) star.branches

theorem mem_chain (separator : Word Nat) (branches : List (Word Nat)) (x : Nat) :
    x ∈ (chain separator branches).toList ↔
      x ∈ separator.toList ∨ ∃ branch ∈ branches, x ∈ branch.toList := by
  induction branches with
  | nil => simp only [chain, List.not_mem_nil, false_and, exists_false, or_false]
  | cons branch rest ih =>
    simp only [chain, Word.toList_append, List.mem_append, ih, List.mem_cons]
    constructor
    · rintro ((root | here) | root | ⟨b, hb, hx⟩)
      · exact Or.inl root
      · exact Or.inr ⟨branch, Or.inl rfl, here⟩
      · exact Or.inl root
      · exact Or.inr ⟨b, Or.inr hb, hx⟩
    · rintro (root | ⟨b, hb, hx⟩)
      · exact Or.inl (Or.inl root)
      · rcases hb with equal | later
        · subst b
          exact Or.inl (Or.inr hx)
        · exact Or.inr (Or.inr ⟨b, later, hx⟩)

theorem count_branch_le (separator : Word Nat) (branches : List (Word Nat))
    (branch : Word Nat) (member : branch ∈ branches) (x : Nat) :
    branch.toList.count x ≤ (chain separator branches).toList.count x := by
  induction branches with
  | nil => cases member
  | cons first rest ih =>
    simp only [chain, Word.toList_append, List.count_append]
    rcases List.mem_cons.mp member with equal | later
    · subst branch
      omega
    · have bound := ih later
      omega

theorem of_decomposition (word : Word Nat) (d : Decomposition word) :
    ∃ star : Star, Derives basis word star.word := by
  let branches := pack (d.gaps.map MaximalFactors.flatten)
  have derived := decomposition_to_chain word d
  have marked : ∀ branch ∈ branches, ∃ leading : List Nat, ∃ marker : Nat,
      branch.toList = leading ++ [marker] ∧ marker ∉ leading := by
    intro branch member
    obtain ⟨_, leading, marker, literal, simple⟩ := packed_branch word d branch member
    have outputSimple : (chain (d.root ++ d.root) branches).toList.count marker = 1 :=
      (semantic_occurrence_categories word _
        (fun valuation => Derives.sound models derived valuation) marker).2.1.mp simple
    have bound := count_branch_le (d.root ++ d.root) branches branch member marker
    have small : leading.count marker + 1 ≤ 1 := by
      simpa [literal, outputSimple] using bound
    exact ⟨leading, marker, literal, List.count_eq_zero.mp (by omega)⟩
  let star : Star := ⟨d.root, branches, d.shape, branches_pairwise word d,
    (fun branch member => (packed_branch word d branch member).1), marked⟩
  exact ⟨star, derived⟩

theorem normalize_connected (word : Word Nat) (connected : Connected word) :
    ∃ star : Star, Derives basis word star.word := by
  obtain ⟨normal, derived, ⟨d⟩⟩ := C8CanonicalBranches.normalize_connected word connected
  obtain ⟨star, next⟩ := of_decomposition normal d
  exact ⟨star, derived.trans next⟩

theorem Star.support (star : Star) (x : Nat) :
    x ∈ star.word.toList ↔ x ∈ star.root.toList ∨ ∃ b ∈ star.branches, x ∈ b.toList := by
  rw [Star.word, mem_chain, Word.toList_append, List.mem_append]
  exact ⟨fun h => h.elim (fun h => Or.inl (h.elim id id)) Or.inr,
    fun h => h.elim (fun h => Or.inl (Or.inl h)) Or.inr⟩

theorem Star.root_head_present (star : Star) : star.root.head ∈ star.word.toList :=
  (star.support star.root.head).mpr (Or.inl List.mem_cons_self)

theorem Star.branch_erase (star : Star) (alphabet : List Nat)
    (covered : ∀ x ∈ star.word.toList, x ∈ alphabet) (branch : Word Nat)
    (member : branch ∈ star.branches) :
    ∀ x ∈ branch.toList, x ∈ alphabet.erase star.root.head := by
  intro x hx
  have different : x ≠ star.root.head := by
    intro same
    subst x
    exact star.apart branch member star.root.head hx List.mem_cons_self
  exact (List.mem_erase_of_ne different).mpr
    (covered x ((star.support x).mpr (Or.inr ⟨branch, member, hx⟩)))

theorem erase_shorter (alphabet : List Nat) (x : Nat) (member : x ∈ alphabet) :
    (alphabet.erase x).length < alphabet.length := by
  induction alphabet with
  | nil => cases member
  | cons y ys ih =>
    by_cases equal : y = x
    · subst y
      simp
    · have later : x ∈ ys := (List.mem_cons.mp member).resolve_left (Ne.symm equal)
      have small := ih later
      simpa [List.erase_cons, equal] using Nat.succ_lt_succ small

end SemigroupBasis.CoRoots.Order6Astra.C8Star

#print axioms SemigroupBasis.CoRoots.Order6Astra.C8Star.normalize_connected
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8Star.Star.branch_erase
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8Star.erase_shorter
