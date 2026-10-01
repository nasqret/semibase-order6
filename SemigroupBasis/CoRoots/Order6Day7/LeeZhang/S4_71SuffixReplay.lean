import SemigroupBasis.Examples.EdmundsFourSeventyOne

/-! Reuse the proved S4_71 basis strictly before a nonempty suffix.
The three fields are contextual derivations, not completeness assumptions. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S4_71Suffix

open SemigroupBasis
open SemigroupBasis.Examples

abbrev lowerTable := edmundsFourSeventyOne
abbrev lowerMul := edmundsFourSeventyOneMul
abbrev lowerBasis := edmundsFourSeventyOneBasis

theorem lower_unit_left (value : Fin 4) : lowerMul 3 value = value := by decide +revert
theorem lower_unit_right (value : Fin 4) : lowerMul value 3 = value := by decide +revert
theorem lower_zero_left (value : Fin 4) : lowerMul 0 value = 0 := by decide +revert
theorem lower_zero_right (value : Fin 4) : lowerMul value 0 = 0 := by decide +revert

theorem lower_assoc (first second third : Fin 4) :
    lowerMul (lowerMul first second) third = lowerMul first (lowerMul second third) :=
  lowerTable.semigroup.assoc first second third

def listEval (valuation : Nat → Fin 4) : List Nat → Fin 4
  | [] => 3
  | first :: rest => lowerMul (valuation first) (listEval valuation rest)

theorem listEval_append (valuation : Nat → Fin 4) (left right : List Nat) :
    listEval valuation (left ++ right) = lowerMul (listEval valuation left) (listEval valuation right) := by
  induction left with
  | nil => simp [listEval, lower_unit_left]
  | cons first rest ih => simp only [List.cons_append, listEval, ih, lower_assoc]

private theorem evalWord (valuation : Nat → Fin 4) (first : Nat) (rest : List Nat) :
    lowerTable.semigroup.eval valuation ⟨first, rest⟩ = lowerMul (valuation first) (listEval valuation rest) := by
  induction rest generalizing first with
  | nil => simp [Semigroup.eval, listEval, lower_unit_right]
  | cons next rest ih =>
      change lowerTable.semigroup.eval valuation (Word.singleton first ++ Word.mk next rest) =
        lowerMul (valuation first) (listEval valuation (next :: rest))
      rw [Semigroup.eval_append, Semigroup.eval_singleton]
      exact congrArg (lowerMul (valuation first)) (ih next)

theorem listEval_toList (valuation : Nat → Fin 4) (word : Word Nat) :
    listEval valuation word.toList = lowerTable.semigroup.eval valuation word := by
  cases word with
  | mk first rest => exact (evalWord valuation first rest).symm

theorem listEval_congr_on (left right : Nat → Fin 4) (word : List Nat)
    (same : ∀ letter, letter ∈ word → left letter = right letter) :
    listEval left word = listEval right word := by
  induction word with
  | nil => rfl
  | cons first rest ih =>
      simp only [listEval]
      rw [same first (List.Mem.head rest)]
      exact congrArg (lowerMul (right first)) (ih (fun letter member => same letter (List.Mem.tail first member)))

def put (front : List Nat) (suffix : Word Nat) : Word Nat :=
  match front with
  | [] => suffix
  | first :: rest => Word.singleton first ++ put rest suffix

theorem put_toList (front : List Nat) (suffix : Word Nat) :
    (put front suffix).toList = front ++ suffix.toList := by
  induction front with
  | nil => rfl
  | cons first rest ih =>
      change first :: (put rest suffix).toList = first :: (rest ++ suffix.toList)
      exact congrArg (List.cons first) ih

theorem put_append (left right : List Nat) (suffix : Word Nat) :
    put (left ++ right) suffix = put left (put right suffix) := by
  induction left with
  | nil => rfl
  | cons first rest ih => simp only [List.cons_append, put, ih]

theorem put_word (front suffix : Word Nat) : put front.toList suffix = front ++ suffix := by
  apply Word.toList_injective
  simp only [put_toList, Word.toList_append]

structure Rules (basis : List (Identity Nat)) : Prop where
  power : ∀ x suffix : Word Nat,
    Derives basis ((x ++ x) ++ suffix) (((x ++ x) ++ x) ++ suffix)
  gather : ∀ x y suffix : Word Nat,
    Derives basis (((x ++ y) ++ x) ++ suffix) (((y ++ x) ++ x) ++ suffix)
  squareCommute : ∀ x y suffix : Word Nat,
    Derives basis (((x ++ x) ++ (y ++ y)) ++ suffix) (((y ++ y) ++ (x ++ x)) ++ suffix)

private theorem bind_append (left right : Word Nat) (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution = left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind (word : Word Nat) (first second : Nat → Word Nat) :
    (word.bind first).bind second = word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) : word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

namespace Rules

variable {basis : List (Identity Nat)}

theorem liftLowerDerivation (rules : Rules basis) {left right : Word Nat}
    (derivation : Derives lowerBasis left right) (suffix : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis (left.bind substitution ++ suffix) (right.bind substitution ++ suffix) := by
  induction derivation generalizing suffix substitution with
  | fromBasis member =>
      simp only [lowerBasis, edmundsFourSeventyOneBasis, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · simpa [edmundsFourSeventyOnePowerLaw, edmundsFourSeventyOneXX, edmundsFourSeventyOneXXX,
          Word.bind, Word.append, Word.append_assoc] using rules.power (substitution 0) suffix
      · simpa [edmundsFourSeventyOneGatherLaw, edmundsFourSeventyOneXYX, edmundsFourSeventyOneYXX,
          Word.bind, Word.append, Word.append_assoc] using rules.gather (substitution 0) (substitution 1) suffix
      · simpa [edmundsFourSeventyOneSquareCommutationLaw, edmundsFourSeventyOneXXYY, edmundsFourSeventyOneYYXX,
          Word.bind, Word.append, Word.append_assoc] using rules.squareCommute (substitution 0) (substitution 1) suffix
  | refl => exact Derives.refl _
  | symm _ ih => exact (ih suffix substitution).symm
  | trans _ _ first second => exact (first suffix substitution).trans (second suffix substitution)
  | prepend before _ ih =>
      simpa only [bind_append, Word.append_assoc] using
        Derives.prepend (before.bind substitution) (ih suffix substitution)
  | appendRight _ after ih =>
      simpa only [bind_append, Word.append_assoc] using ih (after.bind substitution ++ suffix) substitution
  | subst _ replacement ih =>
      simpa only [bind_bind] using ih suffix (fun letter => (replacement letter).bind substitution)

private theorem eq_nil_of_listTheory (right : List Nat)
    (same : ∀ valuation, listEval valuation [] = listEval valuation right) : right = [] := by
  cases right with
  | nil => rfl
  | cons first rest =>
      have equal := same (fun _ => 0)
      simp only [listEval, lower_zero_left] at equal
      exact False.elim ((by decide : (3 : Fin 4) ≠ 0) equal)

/-- Reuse genuine unrestricted S4_71 completeness, including the empty-prefix boundary. -/
theorem derivesLists (rules : Rules basis) (left right : List Nat) (suffix : Word Nat)
    (same : ∀ valuation, listEval valuation left = listEval valuation right) :
    Derives basis (put left suffix) (put right suffix) := by
  cases left with
  | nil =>
      have equal := eq_nil_of_listTheory right same
      subst right
      exact Derives.refl _
  | cons first rest =>
      cases right with
      | nil =>
          have impossible := eq_nil_of_listTheory (first :: rest) (fun valuation => (same valuation).symm)
          cases impossible
      | cons other tail =>
          let identity : Identity Nat := ⟨Word.mk first rest, Word.mk other tail⟩
          have valid : identity.SatisfiedBy lowerTable.semigroup := by
            intro valuation
            change lowerTable.semigroup.eval valuation (Word.mk first rest) =
              lowerTable.semigroup.eval valuation (Word.mk other tail)
            rw [← listEval_toList, ← listEval_toList]
            exact same valuation
          have lowerDerivation := edmundsFourSeventyOneBasis_complete.2 identity valid
          have lifted := rules.liftLowerDerivation lowerDerivation suffix Word.singleton
          simpa only [identity, bind_singleton, ← put_word] using lifted

end Rules
end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S4_71Suffix
