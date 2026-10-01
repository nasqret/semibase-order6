import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedPresentation

namespace SemigroupBasis.CoRoots.Order6Astra.C8BranchAlgebra

open Order6SporadicSection19.Published

/-- A nonempty separator between every pair of nonempty branches and at both
ends. Empty lists of branches produce the separator, not a semigroup unit. -/
def chain (separator : Word Nat) : List (Word Nat) → Word Nat
  | [] => separator
  | branch :: rest => (separator ++ branch) ++ chain separator rest

theorem exchange (separator left right : Word Nat) :
    Derives basis ((((separator ++ left) ++ separator) ++ right) ++ separator)
      ((((separator ++ right) ++ separator) ++ left) ++ separator) := by
  exact Derives.subst derives_b_exchange
    (fun x => if x = 0 then separator else if x = 1 then left else right)

theorem swap_first (separator left right : Word Nat) (rest : List (Word Nat)) :
    Derives basis (chain separator (left :: right :: rest))
      (chain separator (right :: left :: rest)) := by
  cases rest with
  | nil => simpa only [chain, Word.append_assoc] using exchange separator left right
  | cons next rest =>
    simpa only [chain, Word.append_assoc] using
      Derives.appendRight (exchange separator left right) (next ++ chain separator rest)

/-- Any finite permutation of branches is justified by actual (19.1b) word
substitutions, with all outside branches retained literally. -/
theorem chain_perm (separator : Word Nat) {left right : List (Word Nat)}
    (permutation : left.Perm right) :
    Derives basis (chain separator left) (chain separator right) := by
  induction permutation with
  | nil => exact Derives.refl _
  | cons branch _ ih => exact Derives.prepend (separator ++ branch) ih
  | swap left right rest => exact swap_first separator right left rest
  | trans _ _ first second => exact first.trans second

theorem chain_map (separator : Word Nat) (branches : List (Word Nat))
    (normal : Word Nat → Word Nat)
    (derived : ∀ branch ∈ branches, Derives basis branch (normal branch)) :
    Derives basis (chain separator branches) (chain separator (branches.map normal)) := by
  induction branches with
  | nil => exact Derives.refl _
  | cons branch rest ih =>
    have head := derived branch List.mem_cons_self
    have tail := ih (fun b hb => derived b (List.mem_cons_of_mem branch hb))
    exact (Derives.appendRight (Derives.prepend separator head) (chain separator rest)).trans
      (Derives.prepend (separator ++ normal branch) tail)

theorem chain_root {left right : Word Nat} (derived : Derives basis left right)
    (branches : List (Word Nat)) :
    Derives basis (chain left branches) (chain right branches) := by
  induction branches with
  | nil => exact derived
  | cons branch rest ih =>
    exact (Derives.appendRight (Derives.appendRight derived branch) (chain left rest)).trans
      (Derives.prepend (right ++ branch) ih)

end SemigroupBasis.CoRoots.Order6Astra.C8BranchAlgebra

#print axioms SemigroupBasis.CoRoots.Order6Astra.C8BranchAlgebra.exchange
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8BranchAlgebra.chain_perm
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8BranchAlgebra.chain_map
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8BranchAlgebra.chain_root
