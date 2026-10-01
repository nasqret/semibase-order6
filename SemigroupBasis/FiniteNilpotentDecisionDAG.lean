import SemigroupBasis.FiniteCertificate

namespace SemigroupBasis
namespace FiniteNilpotentDecisionDAG

/-- A total, proof-friendly list lookup used by generated node references. -/
def lookup : List α → Nat → Option α
  | [], _ => none
  | value :: _, 0 => some value
  | _ :: rest, index + 1 => lookup rest index

private theorem lookup_mem {values : List α} {index : Nat} {value : α}
    (found : lookup values index = some value) : value ∈ values := by
  induction values generalizing index with
  | nil =>
      simp [lookup] at found
  | cons head tail induction =>
      cases index with
      | zero =>
          simp [lookup] at found
          subst value
          exact List.Mem.head tail
      | succ index =>
          apply List.Mem.tail head
          exact induction (by simpa [lookup] using found)

/-- Sparse renamings default to the unchanged variable name. -/
def rename (mapping : List Nat) (name : Nat) : Nat :=
  (lookup mapping name).getD name

/-- Orient a basis leaf before applying its simultaneous renaming. -/
def orient (identity : Identity Nat) (symmetry : Bool) : Identity Nat :=
  if symmetry then ⟨identity.rhs, identity.lhs⟩ else identity

/-- One inventory root in the shared basis-leaf decision DAG.  Basis leaves
are referenced by index and may be shared by arbitrarily many roots. -/
structure Root where
  target : Identity Nat
  basisIndex : Nat
  symmetry : Bool
  mapping : List Nat
deriving Repr, DecidableEq

/-- Check one root against its referenced basis leaf. -/
def checkRoot (basis : List (Identity Nat)) (root : Root) : Bool :=
  match lookup basis root.basisIndex with
  | none => false
  | some source =>
      decide ((orient source root.symmetry).map (rename root.mapping) =
        root.target)

private theorem checkRoot_sound {basis : List (Identity Nat)} {root : Root}
    (checked : checkRoot basis root = true) :
    Derives basis root.target.lhs root.target.rhs := by
  unfold checkRoot at checked
  cases sourceFound : lookup basis root.basisIndex with
  | none =>
      simp [sourceFound] at checked
  | some source =>
      rw [sourceFound] at checked
      have targetEq :
          (orient source root.symmetry).map (rename root.mapping) =
            root.target :=
        of_decide_eq_true checked
      have sourceDerivation : Derives basis source.lhs source.rhs :=
        Derives.fromBasis (lookup_mem sourceFound)
      have orientedDerivation :
          Derives basis (orient source root.symmetry).lhs
            (orient source root.symmetry).rhs := by
        cases root.symmetry with
        | false =>
            simpa [orient] using sourceDerivation
        | true =>
            simpa [orient] using Derives.symm sourceDerivation
      have renamed :=
        Derives.rename orientedDerivation (rename root.mapping)
      rw [← targetEq]
      simpa [Identity.map] using renamed

/-- Check the root order and every local root computation. -/
def check (basis identities : List (Identity Nat))
    (roots : List Root) : Bool :=
  decide (roots.map Root.target = identities) &&
    roots.all (checkRoot basis)

/-- A successful shared-leaf DAG check derives every listed inventory row. -/
theorem check_sound {basis identities : List (Identity Nat)}
    {roots : List Root} (checked : check basis identities roots = true) :
    FiniteCertificate.DerivesAll basis identities := by
  change
    (decide (roots.map Root.target = identities) &&
      roots.all (checkRoot basis)) = true at checked
  simp only [Bool.and_eq_true] at checked
  have targets : roots.map Root.target = identities :=
    of_decide_eq_true checked.1
  intro identity member
  rw [← targets] at member
  rcases List.mem_map.mp member with ⟨root, rootMember, rfl⟩
  exact checkRoot_sound
    ((List.all_eq_true.mp checked.2) root rootMember)

end FiniteNilpotentDecisionDAG
end SemigroupBasis
