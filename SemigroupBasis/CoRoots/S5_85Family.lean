import SemigroupBasis.CoRoots.S5_85
import SemigroupBasis.Examples.LeftZeroTwo
import SemigroupBasis.Generated.CatalogueOrder5Part01
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.Transfer

namespace SemigroupBasis.CoRoots.S5_85Family

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_85

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def finiteBasis : List (Identity (Fin 3)) :=
  basis.map fun e => e.map toFinThree

private theorem basis_roundTrip_checked :
    basis.all (fun e =>
      decide ((e.map toFinThree).map Fin.val = e)) = true := by
  decide

private theorem basis_roundTrip
    (e : Identity Nat) (member : e ∈ basis) :
    (e.map toFinThree).map Fin.val = e := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basis_roundTrip_checked) e member

private theorem models_of_finite_checks
    (T : FiniteTable)
    (checked : finiteBasis.all T.checkIdentity = true) :
    Models T.semigroup basis := by
  intro e member
  have finiteMember : e.map toFinThree ∈ finiteBasis :=
    List.mem_map.mpr ⟨e, member, rfl⟩
  have finiteValid :=
    T.checkIdentityNat_sound (e.map toFinThree)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [basis_roundTrip e member] at finiteValid
  exact finiteValid

private theorem fold_sink
    (mul : Fin 5 → Fin 5 → Fin 5)
    (marker sink : Fin 5)
    (sinkStep : mul sink marker = sink)
    (xs : List Nat) :
    xs.foldl (fun current _ => mul current marker) sink = sink := by
  induction xs with
  | nil =>
      rfl
  | cons next rest ih =>
      simp only [List.foldl_cons, sinkStep]
      exact ih

private theorem eval_constant_eq_marker_iff_length_one
    (G : Semigroup (Fin 5))
    (marker sink : Fin 5)
    (markerNeSink : marker ≠ sink)
    (markerSquare : G.mul marker marker = sink)
    (sinkStep : G.mul sink marker = sink)
    (w : Word Nat) :
    G.eval (fun _ => marker) w = marker ↔
      w.toList.length = 1 := by
  cases w with
  | mk head tail =>
      cases tail with
      | nil =>
          simp [Semigroup.eval, Word.toList]
      | cons next rest =>
          change
            rest.foldl
                (fun current _ => G.mul current marker)
                (G.mul marker marker) = marker ↔
              (head :: next :: rest).length = 1
          rw [markerSquare, fold_sink G.mul marker sink sinkStep rest]
          simp [Ne.symm markerNeSink]

private theorem valid_length_one_of_constant
    (G : Semigroup (Fin 5))
    (marker sink : Fin 5)
    (markerNeSink : marker ≠ sink)
    (markerSquare : G.mul marker marker = sink)
    (sinkStep : G.mul sink marker = sink)
    (e : Identity Nat) (valid : e.SatisfiedBy G) :
    e.lhs.toList.length = 1 ↔ e.rhs.toList.length = 1 := by
  have evaluated := valid (fun _ => marker)
  have lhsIff :=
    eval_constant_eq_marker_iff_length_one
      G marker sink markerNeSink markerSquare sinkStep e.lhs
  have rhsIff :=
    eval_constant_eq_marker_iff_length_one
      G marker sink markerNeSink markerSquare sinkStep e.rhs
  constructor
  · intro lhsOne
    apply rhsIff.mp
    rw [← evaluated]
    exact lhsIff.mpr lhsOne
  · intro rhsOne
    apply lhsIff.mp
    rw [evaluated]
    exact rhsIff.mpr rhsOne

namespace S5_85

private def headEmbedding :
    Embedding leftZeroTwo.semigroup
      Generated.Catalogue.S5_85.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else ⟨4, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_85.table.semigroup basis :=
  models_of_finite_checks Generated.Catalogue.S5_85.table (by decide)

theorem valid_head (e : Identity Nat)
    (valid : e.SatisfiedBy Generated.Catalogue.S5_85.table.semigroup) :
    e.lhs.head = e.rhs.head := by
  have pulled := headEmbedding.pullback_identity e valid
  apply Decidable.byContradiction
  intro headsNe
  let valuation : Nat → Fin 2 :=
    fun z => if z = e.lhs.head then 0 else 1
  have evaluated := pulled valuation
  rw [leftZeroTwo_eval, leftZeroTwo_eval] at evaluated
  simp [valuation, Ne.symm headsNe] at evaluated

theorem valid_length_one (e : Identity Nat)
    (valid : e.SatisfiedBy Generated.Catalogue.S5_85.table.semigroup) :
    e.lhs.toList.length = 1 ↔ e.rhs.toList.length = 1 :=
  valid_length_one_of_constant
    Generated.Catalogue.S5_85.table.semigroup
    2 0 (by decide) (by decide) (by decide) e valid

private def firstCoordinateSeparator (z : Nat) : Nat → Fin 5 :=
  fun x => if x = z then 4 else 0

private theorem firstCoordinateSeparator_pair_eval
    (z a b : Nat) :
    Generated.Catalogue.S5_85.table.semigroup.eval
        (firstCoordinateSeparator z) (wordOfCons a [b]) =
      if a = z then (4 : Fin 5) else 0 := by
  change
    Generated.Catalogue.S5_85.mul
        (firstCoordinateSeparator z a)
        (firstCoordinateSeparator z b) =
      if a = z then (4 : Fin 5) else 0
  by_cases ha : a = z <;>
    simp [firstCoordinateSeparator, ha,
      Generated.Catalogue.S5_85.mul]

private theorem validPair_first_eq {a b c d : Nat}
    (valid :
      (Identity.mk
        (wordOfCons a [b]) (wordOfCons c [d])).SatisfiedBy
          Generated.Catalogue.S5_85.table.semigroup) :
    a = c := by
  have evaluated := valid (firstCoordinateSeparator a)
  rw [firstCoordinateSeparator_pair_eval,
    firstCoordinateSeparator_pair_eval] at evaluated
  apply Decidable.byContradiction
  intro different
  simp [Ne.symm different] at evaluated

theorem valid_pair_eq {a b c d : Nat}
    (valid :
      (Identity.mk
        (wordOfCons a [b]) (wordOfCons c [d])).SatisfiedBy
          Generated.Catalogue.S5_85.table.semigroup) :
    a = c ∧ b = d := by
  have first := validPair_first_eq valid
  subst c
  have second : b = d := by
    apply Decidable.byContradiction
    intro different
    by_cases ba : b = a
    · have da : d ≠ a := by
        intro da
        exact different (ba.trans da.symm)
      let valuation : Nat → Fin 5 :=
        fun x => if x = a then 3 else if x = d then 2 else 0
      have evaluated := valid valuation
      change
        Generated.Catalogue.S5_85.mul
            (valuation a) (valuation b) =
          Generated.Catalogue.S5_85.mul
            (valuation a) (valuation d) at evaluated
      simp [valuation, ba, da, Generated.Catalogue.S5_85.mul] at evaluated
    · let valuation : Nat → Fin 5 :=
        fun x => if x = a then 3 else if x = b then 2 else 0
      have evaluated := valid valuation
      change
        Generated.Catalogue.S5_85.mul
            (valuation a) (valuation b) =
          Generated.Catalogue.S5_85.mul
            (valuation a) (valuation d) at evaluated
      by_cases da : d = a
      · simp [valuation, ba, da,
          Generated.Catalogue.S5_85.mul] at evaluated
      · simp [valuation, ba, da, Ne.symm different,
          Generated.Catalogue.S5_85.mul] at evaluated
  exact ⟨rfl, second⟩

private theorem mul_triple_spec (a b c : Fin 5) :
    Generated.Catalogue.S5_85.mul
        (Generated.Catalogue.S5_85.mul a b) c =
      if a = 4 then (4 : Fin 5) else 0 := by
  decide +revert

private theorem mul_zero_left (a : Fin 5) :
    Generated.Catalogue.S5_85.mul 0 a = 0 := by
  decide +revert

private theorem mul_four_left (a : Fin 5) :
    Generated.Catalogue.S5_85.mul 4 a = 4 := by
  decide +revert

private theorem fold_zero (xs : List Nat) (valuation : Nat → Fin 5) :
    xs.foldl
        (fun current x =>
          Generated.Catalogue.S5_85.mul current (valuation x))
        0 = 0 := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.foldl_cons, mul_zero_left]
      exact ih

private theorem fold_four (xs : List Nat) (valuation : Nat → Fin 5) :
    xs.foldl
        (fun current x =>
          Generated.Catalogue.S5_85.mul current (valuation x))
        4 = 4 := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.foldl_cons, mul_four_left]
      exact ih

private theorem eval_long
    (valuation : Nat → Fin 5) (x y z : Nat) (zs : List Nat) :
    Generated.Catalogue.S5_85.table.semigroup.eval valuation
        (wordOfCons x (y :: z :: zs)) =
      if valuation x = (4 : Fin 5) then (4 : Fin 5) else 0 := by
  change
    zs.foldl
        (fun current t =>
          Generated.Catalogue.S5_85.mul current (valuation t))
        (Generated.Catalogue.S5_85.mul
          (Generated.Catalogue.S5_85.mul
            (valuation x) (valuation y))
          (valuation z)) =
      if valuation x = 4 then 4 else 0
  rw [mul_triple_spec]
  by_cases hx : valuation x = 4
  · simp only [hx, if_pos]
    exact fold_four zs valuation
  · simp only [hx, if_false]
    exact fold_zero zs valuation

theorem valid_distinct_pair_not_long {a b : Nat}
    (different : a ≠ b) (v : Word Nat)
    (long : 3 ≤ v.toList.length) :
    ¬ (Identity.mk (wordOfCons a [b]) v).SatisfiedBy
      Generated.Catalogue.S5_85.table.semigroup := by
  intro valid
  cases v with
  | mk head tail =>
      cases tail with
      | nil =>
          simp [Word.toList] at long
      | cons next rest =>
          cases rest with
          | nil =>
              simp [Word.toList] at long
          | cons third more =>
              let valuation : Nat → Fin 5 :=
                fun x => if x = a then 3 else if x = b then 2 else 0
              have evaluated := valid valuation
              change
                Generated.Catalogue.S5_85.mul
                    (valuation a) (valuation b) =
                  Generated.Catalogue.S5_85.table.semigroup.eval
                    valuation
                    (wordOfCons head (next :: third :: more))
                at evaluated
              rw [eval_long] at evaluated
              have headNe : valuation head ≠ (4 : Fin 5) := by
                by_cases headA : head = a
                · simp [valuation, headA]
                · by_cases headB : head = b
                  · simp [valuation, headB, Ne.symm different]
                  · simp [valuation, headA, headB]
              simp [valuation, Ne.symm different,
                Generated.Catalogue.S5_85.mul, headNe] at evaluated

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_85.table.semigroup basis :=
  basis_complete_of_separates Generated.Catalogue.S5_85.table
    models valid_head valid_length_one valid_pair_eq
    valid_distinct_pair_not_long

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_85.table.semigroup.opposite
      (reversedBasis basis) :=
  basis_complete.oppositeReversed

end S5_85

end SemigroupBasis.CoRoots.S5_85Family
