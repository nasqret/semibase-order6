import SemigroupBasis.FiniteReflection

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6SporadicSection19

def mul (a b : Fin 6) : Fin 6 :=
  match a.val, b.val with
  | 1, 5 => 1
  | 2, 5 => 2
  | 3, 2 => 1
  | 3, 4 => 3
  | 4, 2 => 2
  | 4, 4 => 4
  | 5, 1 => 1
  | 5, 2 => 1
  | 5, 3 => 3
  | 5, 4 => 3
  | 5, 5 => 5
  | _, _ => 0

theorem mul_assoc : ∀ a b c : Fin 6, mul (mul a b) c = mul a (mul b c) := by
  decide

def table : FiniteTable := ⟨6, mul, mul_assoc⟩

theorem table_rows :
    (List.finRange 6).map (fun (a : Fin 6) =>
      (List.finRange 6).map (fun (b : Fin 6) =>
        (show Fin 6 from table.mul a b).val)) =
      [[0,0,0,0,0,0], [0,0,0,0,0,1], [0,0,0,0,0,2],
       [0,0,1,0,3,0], [0,0,2,0,4,0], [0,1,1,3,3,5]] := by
  decide

def finiteBasis : List (Identity (Fin 3)) :=
  [ ⟨⟨0, [0]⟩, ⟨0, [0,0]⟩⟩,
    ⟨⟨0, [1,0]⟩, ⟨0, [0,1,0]⟩⟩,
    ⟨⟨0, [1,0]⟩, ⟨0, [1,0,0]⟩⟩,
    ⟨⟨0, [1,0,1]⟩, ⟨0, [1,1,0]⟩⟩,
    ⟨⟨0, [1,0,1]⟩, ⟨1, [0,0,1]⟩⟩,
    ⟨⟨0, [1,0,2,0]⟩, ⟨0, [2,0,1,0]⟩⟩,
    ⟨⟨0, [1,0,2,1]⟩, ⟨0, [1,2,0,1]⟩⟩,
    ⟨⟨0, [1,0,2,1]⟩, ⟨0, [1,2,1,0]⟩⟩,
    ⟨⟨0, [1,0,2,1]⟩, ⟨0, [2,1,1,0]⟩⟩ ]

def basis : List (Identity Nat) :=
  finiteBasis.map (fun identity : Identity (Fin 3) => identity.map Fin.val)

theorem basis_length : basis.length = 9 := by decide

theorem basis_exact :
    basis.map (fun identity => (identity.lhs.toList, identity.rhs.toList)) =
      [([0,0], [0,0,0]),
       ([0,1,0], [0,0,1,0]),
       ([0,1,0], [0,1,0,0]),
       ([0,1,0,1], [0,1,1,0]),
       ([0,1,0,1], [1,0,0,1]),
       ([0,1,0,2,0], [0,2,0,1,0]),
       ([0,1,0,2,1], [0,1,2,0,1]),
       ([0,1,0,2,1], [0,1,2,1,0]),
       ([0,1,0,2,1], [0,2,1,1,0])] := by
  rfl

theorem finite_basis_checked :
    finiteBasis.all (fun identity : Identity (Fin 3) =>
      table.checkIdentityFused identity) = true := by
  decide

theorem models : Models table.semigroup basis := by
  intro identity member
  change identity ∈ finiteBasis.map
    (fun item : Identity (Fin 3) => item.map Fin.val) at member
  obtain ⟨finiteIdentity, finiteMember, rfl⟩ := List.mem_map.mp member
  have checked : table.checkIdentityFused finiteIdentity = true :=
    (List.all_eq_true.mp finite_basis_checked) finiteIdentity finiteMember
  exact finiteIdentity.satisfiedBy_map Fin.val table.semigroup
    (table.checkIdentityFused_sound finiteIdentity checked)

theorem derive_substitution (identity : Identity Nat) (member : identity ∈ basis)
    (substitution : Nat → Word Nat) :
    Derives basis (identity.lhs.bind substitution) (identity.rhs.bind substitution) :=
  (Derives.fromBasis member).subst substitution

def law03 : Identity Nat := ⟨⟨0, [1,0,1]⟩, ⟨0, [1,1,0]⟩⟩

theorem law03_mem : law03 ∈ basis := by decide

theorem law03_derives : Derives basis law03.lhs law03.rhs :=
  Derives.fromBasis law03_mem

def hasYY (letters : List Nat) : Bool :=
  (letters.zip letters.tail).contains (1, 1)

theorem not_rawYY_invariant :
    ¬ (∀ u v : Word Nat, Derives basis u v → hasYY u.toList = hasYY v.toList) := by
  intro invariant
  have same : hasYY law03.lhs.toList = hasYY law03.rhs.toList :=
    invariant law03.lhs law03.rhs law03_derives
  have left : hasYY law03.lhs.toList = false := by decide
  have right : hasYY law03.rhs.toList = true := by decide
  have impossible : (false : Bool) = true := left.symm.trans (same.trans right)
  cases impossible

end SemigroupBasis.CoRoots.Order6SporadicSection19

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.mul_assoc
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.table_rows
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.basis_length
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.basis_exact
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.finite_basis_checked
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.models
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.derive_substitution
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.law03_mem
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.law03_derives
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.not_rawYY_invariant
