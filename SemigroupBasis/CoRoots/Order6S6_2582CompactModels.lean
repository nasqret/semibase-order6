import SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.Signature
import SemigroupBasis.Generated.Order6Nilpotent.S6_2582

namespace SemigroupBasis.CoRoots.Order6S6_2582CompactModels

open SemigroupBasis

abbrev table := SemigroupBasis.Generated.Order6Nilpotent.S6_2582.table
abbrev target : Semigroup (Fin 6) := table.semigroup
abbrev basis :=
  SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.basis

private theorem mul_commutative (a b : Fin 6) :
    target.mul a b = target.mul b a := by
  decide +revert

private theorem mul_zero_left (a : Fin 6) :
    target.mul 0 a = 0 := by
  decide +revert

private theorem product_five (a b c d e : Fin 6) :
    target.mul
        (target.mul
          (target.mul (target.mul a b) c) d) e =
      if a = 5 ∧ b = 5 ∧ c = 5 ∧ d = 5 ∧ e = 5 then 2 else 0 := by
  decide +revert

private def nilpotenceRank (value : Fin 6) : Nat :=
  if value = 0 then 0
  else if value = 1 then 2
  else if value = 2 then 1
  else if value = 3 then 3
  else if value = 4 then 4
  else 5

private theorem nilpotenceRank_le_five (value : Fin 6) :
    nilpotenceRank value ≤ 5 := by
  decide +revert

private theorem nilpotenceRank_mul_le (left right : Fin 6) :
    nilpotenceRank (target.mul left right) ≤
      nilpotenceRank left - 1 := by
  decide +revert

private theorem nilpotenceRank_eq_zero (value : Fin 6) :
    nilpotenceRank value = 0 ↔ value = 0 := by
  decide +revert

private theorem product_six (a b c d e f : Fin 6) :
    target.mul
        (target.mul
          (target.mul
            (target.mul (target.mul a b) c) d) e) f = 0 := by
  let ab := target.mul a b
  let abc := target.mul ab c
  let abcd := target.mul abc d
  let abcde := target.mul abcd e
  let abcdef := target.mul abcde f
  have h0 : nilpotenceRank a ≤ 5 := nilpotenceRank_le_five a
  have h1 : nilpotenceRank ab ≤ nilpotenceRank a - 1 :=
    nilpotenceRank_mul_le a b
  have h2 : nilpotenceRank abc ≤ nilpotenceRank ab - 1 :=
    nilpotenceRank_mul_le ab c
  have h3 : nilpotenceRank abcd ≤ nilpotenceRank abc - 1 :=
    nilpotenceRank_mul_le abc d
  have h4 : nilpotenceRank abcde ≤ nilpotenceRank abcd - 1 :=
    nilpotenceRank_mul_le abcd e
  have h5 : nilpotenceRank abcdef ≤ nilpotenceRank abcde - 1 :=
    nilpotenceRank_mul_le abcde f
  have rankZero : nilpotenceRank abcdef = 0 := by omega
  exact (nilpotenceRank_eq_zero abcdef).mp rankZero

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private theorem eval_prepend
    (valuation : Nat → Fin 6) (p u v : Word Nat)
    (h : target.eval valuation u =
      target.eval valuation v) :
    target.eval valuation (p ++ u) =
      target.eval valuation (p ++ v) := by
  rw [Semigroup.eval_append, Semigroup.eval_append, h]

private theorem eval_append_right
    (valuation : Nat → Fin 6) (u v q : Word Nat)
    (h : target.eval valuation u =
      target.eval valuation v) :
    target.eval valuation (u ++ q) =
      target.eval valuation (v ++ q) := by
  rw [Semigroup.eval_append, Semigroup.eval_append, h]

private theorem eval_commute
    (valuation : Nat → Fin 6) (u v : Word Nat) :
    target.eval valuation (u ++ v) =
      target.eval valuation (v ++ u) := by
  rw [Semigroup.eval_append, Semigroup.eval_append]
  exact mul_commutative _ _

private inductive ListEvalEq
    (valuation : Nat → Fin 6) : List Nat → List Nat → Prop
  | empty : ListEvalEq valuation [] []
  | words {x y : Nat} {xs ys : List Nat} :
      target.eval valuation (wordOfCons x xs) =
        target.eval valuation (wordOfCons y ys) →
      ListEvalEq valuation (x :: xs) (y :: ys)

private theorem listEvalEq_of_perm
    (valuation : Nat → Fin 6) {xs ys : List Nat}
    (h : xs.Perm ys) : ListEvalEq valuation xs ys := by
  induction h with
  | nil =>
      exact ListEvalEq.empty
  | cons x _ ih =>
      cases ih with
      | empty =>
          exact ListEvalEq.words rfl
      | words equality =>
          exact ListEvalEq.words <| by
            simpa [wordOfCons, Word.singleton, Word.append] using
              eval_prepend valuation (Word.singleton x) _ _ equality
  | swap x y xs =>
      exact ListEvalEq.words <| by
        cases xs with
        | nil =>
            simpa [wordOfCons, Word.append, Word.singleton] using
              eval_commute valuation (Word.singleton y) (Word.singleton x)
        | cons z zs =>
            have swapped :=
              eval_append_right valuation
                (Word.singleton y ++ Word.singleton x)
                (Word.singleton x ++ Word.singleton y)
                (wordOfCons z zs)
                (eval_commute valuation
                  (Word.singleton y) (Word.singleton x))
            simpa [wordOfCons, Word.append, Word.singleton,
              Word.append_assoc] using swapped
  | trans _ _ ih₁ ih₂ =>
      cases ih₁ with
      | empty =>
          cases ih₂
          exact ListEvalEq.empty
      | words first =>
          cases ih₂ with
          | words second =>
              exact ListEvalEq.words (first.trans second)

private theorem eval_eq_of_perm
    (valuation : Nat → Fin 6) (u v : Word Nat)
    (h : u.toList.Perm v.toList) :
    target.eval valuation u =
      target.eval valuation v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          cases listEvalEq_of_perm valuation h with
          | words equality => exact equality

private def allGenerator
    (valuation : Nat → Fin 6) (xs : List Nat) : Prop :=
  ∀ x ∈ xs, valuation x = 5

private noncomputable instance allGeneratorDecidable
    (valuation : Nat → Fin 6) (xs : List Nat) :
    Decidable (allGenerator valuation xs) :=
  Classical.propDecidable _

private theorem eval_length_five
    (valuation : Nat → Fin 6) (w : Word Nat)
    (hlength : w.toList.length = 5) :
    target.eval valuation w =
      if allGenerator valuation w.toList then 2 else 0 := by
  classical
  cases w with
  | mk a tail =>
      cases tail with
      | nil => simp [Word.toList] at hlength
      | cons b tail =>
          cases tail with
          | nil => simp [Word.toList] at hlength
          | cons c tail =>
              cases tail with
              | nil => simp [Word.toList] at hlength
              | cons d tail =>
                  cases tail with
                  | nil => simp [Word.toList] at hlength
                  | cons e tail =>
                      have htail : tail = [] := by
                        cases tail with
                        | nil => rfl
                        | cons f tail => simp [Word.toList] at hlength
                      subst tail
                      simp only [Semigroup.eval, List.foldl_cons,
                        List.foldl_nil, Word.toList]
                      simpa [allGenerator] using
                        product_five (valuation a) (valuation b)
                          (valuation c) (valuation d) (valuation e)

private def sameSupport (xs ys : List Nat) : Bool :=
  (xs.all fun x => decide (x ∈ ys)) &&
    (ys.all fun y => decide (y ∈ xs))

private theorem sameSupport_eq_true_iff
    {xs ys : List Nat} :
    sameSupport xs ys = true ↔
      ∀ tested, tested ∈ xs ↔ tested ∈ ys := by
  constructor
  · intro checked
    simp only [sameSupport, Bool.and_eq_true] at checked
    intro tested
    constructor
    · intro member
      exact of_decide_eq_true <|
        (List.all_eq_true.mp checked.1) tested member
    · intro member
      exact of_decide_eq_true <|
        (List.all_eq_true.mp checked.2) tested member
  · intro support
    simp only [sameSupport, Bool.and_eq_true]
    constructor
    · apply List.all_eq_true.mpr
      intro tested member
      exact decide_eq_true ((support tested).1 member)
    · apply List.all_eq_true.mpr
      intro tested member
      exact decide_eq_true ((support tested).2 member)

private theorem allGenerator_iff_of_sameSupport
    (valuation : Nat → Fin 6) {xs ys : List Nat}
    (hsupport : sameSupport xs ys = true) :
    allGenerator valuation xs ↔ allGenerator valuation ys := by
  have support := sameSupport_eq_true_iff.mp hsupport
  constructor
  · intro hall x hx
    exact hall x ((support x).2 hx)
  · intro hall x hx
    exact hall x ((support x).1 hx)

private theorem foldl_from_zero
    (valuation : Nat → Fin 6) (xs : List Nat) :
    xs.foldl
        (fun current x => target.mul current (valuation x)) 0 = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons, mul_zero_left]
      exact ih

private theorem eval_length_at_least_six
    (valuation : Nat → Fin 6) (w : Word Nat)
    (hlength : 6 ≤ w.toList.length) :
    target.eval valuation w = 0 := by
  cases w with
  | mk a tail =>
      cases tail with
      | nil => simp [Word.toList] at hlength
      | cons b tail =>
          cases tail with
          | nil => simp [Word.toList] at hlength
          | cons c tail =>
              cases tail with
              | nil => simp [Word.toList] at hlength
              | cons d tail =>
                  cases tail with
                  | nil => simp [Word.toList] at hlength
                  | cons e tail =>
                      cases tail with
                      | nil => simp [Word.toList] at hlength
                      | cons f tail =>
                          simp only [Semigroup.eval, List.foldl_cons]
                          rw [product_six]
                          exact foldl_from_zero valuation tail

private def eraseOnce (x : Nat) : List Nat → Option (List Nat)
  | [] => none
  | y :: ys =>
      if x = y then
        some ys
      else
        match eraseOnce x ys with
        | none => none
        | some zs => some (y :: zs)

private theorem eraseOnce_perm
    {x : Nat} {ys zs : List Nat}
    (herase : eraseOnce x ys = some zs) :
    ys.Perm (x :: zs) := by
  induction ys generalizing zs with
  | nil =>
      simp [eraseOnce] at herase
  | cons y ys ih =>
      by_cases hxy : x = y
      · subst y
        simp [eraseOnce] at herase
        cases herase
        exact List.Perm.refl _
      · cases htail : eraseOnce x ys with
        | none =>
            simp [eraseOnce, hxy, htail] at herase
        | some tail =>
            simp [eraseOnce, hxy, htail] at herase
            cases herase
            exact
              (List.Perm.cons y (ih htail)).trans
                (List.Perm.swap x y tail)

private def permCheck : List Nat → List Nat → Bool
  | [], [] => true
  | [], _ :: _ => false
  | x :: xs, ys =>
      match eraseOnce x ys with
      | none => false
      | some zs => permCheck xs zs

private theorem permCheck_true
    {xs ys : List Nat} (hcheck : permCheck xs ys = true) :
    xs.Perm ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => exact List.Perm.nil
      | cons y ys => simp [permCheck] at hcheck
  | cons x xs ih =>
      cases herase : eraseOnce x ys with
      | none =>
          simp [permCheck, herase] at hcheck
      | some zs =>
          have htail : xs.Perm zs := ih (by
            simpa [permCheck, herase] using hcheck)
          exact
            (List.Perm.cons x htail).trans
              (eraseOnce_perm herase).symm

private def CompactShape (e : Identity Nat) : Prop :=
  e.lhs.toList.Perm e.rhs.toList ∨
    (e.lhs.toList.length = 5 ∧ e.rhs.toList.length = 5 ∧
      sameSupport e.lhs.toList e.rhs.toList = true) ∨
    (6 ≤ e.lhs.toList.length ∧ 6 ≤ e.rhs.toList.length)

private abbrev CompactCheck (e : Identity Nat) : Prop :=
  permCheck e.lhs.toList e.rhs.toList = true ∨
    (e.lhs.toList.length = 5 ∧ e.rhs.toList.length = 5 ∧
      sameSupport e.lhs.toList e.rhs.toList = true) ∨
    (6 ≤ e.lhs.toList.length ∧ 6 ≤ e.rhs.toList.length)

private theorem compactShape_of_check
    (e : Identity Nat) (hcheck : CompactCheck e) : CompactShape e := by
  rcases hcheck with hperm | hfive | hsix
  · exact Or.inl (permCheck_true hperm)
  · exact Or.inr (Or.inl hfive)
  · exact Or.inr (Or.inr hsix)

private theorem satisfiedBy_of_compactShape
    (e : Identity Nat) (hshape : CompactShape e) :
    e.SatisfiedBy target := by
  intro valuation
  rcases hshape with hperm | hfive | hsix
  · exact eval_eq_of_perm valuation e.lhs e.rhs hperm
  · rcases hfive with ⟨hlength, hrlength, hsupport⟩
    rw [eval_length_five valuation e.lhs hlength,
      eval_length_five valuation e.rhs hrlength]
    have hall := allGenerator_iff_of_sameSupport valuation hsupport
    by_cases hl : allGenerator valuation e.lhs.toList
    · simp [hl, hall.mp hl]
    · have hr : ¬ allGenerator valuation e.rhs.toList := by
        intro hr
        exact hl (hall.mpr hr)
      simp [hl, hr]
  · rw [eval_length_at_least_six valuation e.lhs hsix.1,
      eval_length_at_least_six valuation e.rhs hsix.2]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 65536 in
private theorem basis_compactShape_checked :
    basis.all (fun e => decide (CompactCheck e)) = true := by
  change
    SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.basis.all
      (fun e => decide (CompactCheck e)) = true
  rw [SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.basis_eq]
  decide

private theorem basis_compactShape
    (e : Identity Nat) (he : e ∈ basis) : CompactShape e := by
  apply compactShape_of_check e
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basis_compactShape_checked) e he

/-- One structural model proof replaces 3,513 independent finite-valuation
checks. Short laws are commutative permutations, length-five laws depend only
on support, and every product of six elements is zero. -/
theorem models : Models table.semigroup basis := by
  intro e he
  exact satisfiedBy_of_compactShape e (basis_compactShape e he)

end SemigroupBasis.CoRoots.Order6S6_2582CompactModels
