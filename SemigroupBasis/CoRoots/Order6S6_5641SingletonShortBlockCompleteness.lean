import SemigroupBasis.CoRoots.Order6S6_5641SingletonShortBlockPrelude
import SemigroupBasis.CoRoots.S5_530Normalization

namespace SemigroupBasis
namespace CoRoots
namespace Order6S6_5641SingletonShortBlock

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_530

private def toLrb : Fin 6 → Fin 3
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 0
  | ⟨3, _⟩ => 0
  | ⟨4, _⟩ => 2
  | ⟨5, _⟩ => 1

private def lrbQuotient :
    Hom table.semigroup leftRegularBandThree.semigroup where
  toFun := toLrb
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide

private def liftLrb : Fin 3 → Fin 6
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 5
  | ⟨2, _⟩ => 4

private theorem toLrb_liftLrb (x : Fin 3) : toLrb (liftLrb x) = x := by
  revert x
  decide

private theorem valid_order (e : Identity Nat)
    (h : e.SatisfiedBy table.semigroup) :
    firstOccurrenceSequence e.lhs.toList =
      firstOccurrenceSequence e.rhs.toList := by
  apply SemigroupBasis.CoRoots.S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq e
  intro valuation
  have mapped := congrArg lrbQuotient.toFun (h (fun x => liftLrb (valuation x)))
  have lhsMap := lrbQuotient.map_eval
    (fun x => liftLrb (valuation x)) e.lhs
  have rhsMap := lrbQuotient.map_eval
    (fun x => liftLrb (valuation x)) e.rhs
  rw [lhsMap, rhsMap] at mapped
  have hlift : (fun x => lrbQuotient.toFun (liftLrb (valuation x))) = valuation := by
    funext x
    exact toLrb_liftLrb (valuation x)
  rw [hlift] at mapped
  exact mapped

private theorem t03 : table.semigroup.mul ⟨0, by simp [table]⟩ ⟨3, by simp [table]⟩ = ⟨0, by simp [table]⟩ := by
  apply Fin.ext
  decide

private theorem t13 : table.semigroup.mul ⟨1, by simp [table]⟩ ⟨3, by simp [table]⟩ = ⟨0, by simp [table]⟩ := by
  apply Fin.ext
  decide

private theorem t33 : table.semigroup.mul ⟨3, by simp [table]⟩ ⟨3, by simp [table]⟩ = ⟨1, by simp [table]⟩ := by
  apply Fin.ext
  decide

private theorem t05 : table.semigroup.mul ⟨0, by simp [table]⟩ ⟨5, by simp [table]⟩ = ⟨0, by simp [table]⟩ := by
  apply Fin.ext
  decide

private theorem t15 : table.semigroup.mul ⟨1, by simp [table]⟩ ⟨5, by simp [table]⟩ = ⟨1, by simp [table]⟩ := by
  apply Fin.ext
  decide

private theorem t35 : table.semigroup.mul ⟨3, by simp [table]⟩ ⟨5, by simp [table]⟩ = ⟨3, by simp [table]⟩ := by
  apply Fin.ext
  decide

private theorem t02 : table.semigroup.mul ⟨0, by simp [table]⟩ ⟨2, by simp [table]⟩ = ⟨0, by simp [table]⟩ := by
  apply Fin.ext
  decide

private theorem t22 : table.semigroup.mul ⟨2, by simp [table]⟩ ⟨2, by simp [table]⟩ = ⟨0, by simp [table]⟩ := by
  apply Fin.ext
  decide

private theorem t52 : table.semigroup.mul ⟨5, by simp [table]⟩ ⟨2, by simp [table]⟩ = ⟨2, by simp [table]⟩ := by
  apply Fin.ext
  decide

private theorem t25 : table.semigroup.mul ⟨2, by simp [table]⟩ ⟨5, by simp [table]⟩ = ⟨2, by simp [table]⟩ := by
  apply Fin.ext
  decide

private theorem t55 : table.semigroup.mul ⟨5, by simp [table]⟩ ⟨5, by simp [table]⟩ = ⟨5, by simp [table]⟩ := by
  apply Fin.ext
  decide
private def firstValuation (x : Nat) : Nat → Fin table.order :=
  fun z => if z = x then ⟨3, by simp [table]⟩ else ⟨5, by simp [table]⟩

private theorem first_folds (x : Nat) (xs : List Nat) :
    (xs.foldl (fun a y => table.semigroup.mul a (firstValuation x y))
      ⟨0, by simp [table]⟩ = ⟨0, by simp [table]⟩) ∧
    (xs.foldl (fun a y => table.semigroup.mul a (firstValuation x y))
      ⟨1, by simp [table]⟩ =
      if xs.count x = 0 then ⟨1, by simp [table]⟩ else ⟨0, by simp [table]⟩) ∧
    (xs.foldl (fun a y => table.semigroup.mul a (firstValuation x y))
      ⟨3, by simp [table]⟩ =
      if xs.count x = 0 then ⟨3, by simp [table]⟩
      else if xs.count x = 1 then ⟨1, by simp [table]⟩ else ⟨0, by simp [table]⟩) := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    by_cases hy : y = x
    · subst y
      simp only [List.foldl_cons, firstValuation, if_pos]
      rw [t03, t13, t33]
      simpa [firstValuation] using (And.intro ih.1 ih.2.1)
    · simp only [List.foldl_cons, firstValuation, if_neg hy]
      rw [t05, t15, t35]
      simpa [firstValuation, hy, List.count_cons] using ih

private theorem first_fold_three (x : Nat) (xs : List Nat) :
    xs.foldl (fun a y => table.semigroup.mul a (firstValuation x y))
      ⟨3, by simp [table]⟩ =
      if xs.count x = 0 then ⟨3, by simp [table]⟩
      else if xs.count x = 1 then ⟨1, by simp [table]⟩ else ⟨0, by simp [table]⟩ :=
  (first_folds x xs).2.2

private theorem eval_firstValuation (x : Nat) (w : Word Nat)
    (hh : w.head = x) :
    table.semigroup.eval (firstValuation x) w =
      if w.toList.count x = 1 then ⟨3, by simp [table]⟩
      else if w.toList.count x = 2 then ⟨1, by simp [table]⟩
      else ⟨0, by simp [table]⟩ := by
  cases w with
  | mk head tail =>
    simp only [Word.head] at hh
    subst head
    simpa [Word.toList, Semigroup.eval, firstValuation] using
      first_fold_three x tail

private def laterValuation (z : Nat) : Nat → Fin table.order :=
  fun x => if x = z then ⟨2, by simp [table]⟩ else ⟨5, by simp [table]⟩

private theorem later_folds (z : Nat) (xs : List Nat) :
    (xs.foldl (fun a y => table.semigroup.mul a (laterValuation z y))
      ⟨0, by simp [table]⟩ = ⟨0, by simp [table]⟩) ∧
    (xs.foldl (fun a y => table.semigroup.mul a (laterValuation z y))
      ⟨2, by simp [table]⟩ =
      if xs.count z = 0 then ⟨2, by simp [table]⟩ else ⟨0, by simp [table]⟩) ∧
    (xs.foldl (fun a y => table.semigroup.mul a (laterValuation z y))
      ⟨5, by simp [table]⟩ =
      if xs.count z = 0 then ⟨5, by simp [table]⟩
      else if xs.count z = 1 then ⟨2, by simp [table]⟩ else ⟨0, by simp [table]⟩) := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    by_cases hy : y = z
    · subst y
      simp only [List.foldl_cons, laterValuation, if_pos]
      rw [t02, t22, t52]
      simpa [laterValuation] using (And.intro ih.1 ih.2.1)
    · simp only [List.foldl_cons, laterValuation, if_neg hy]
      rw [t05, t25, t55]
      simpa [laterValuation, hy, List.count_cons] using ih

private theorem later_fold_five (z : Nat) (xs : List Nat) :
    xs.foldl (fun a y => table.semigroup.mul a (laterValuation z y))
      ⟨5, by simp [table]⟩ =
      if xs.count z = 0 then ⟨5, by simp [table]⟩
      else if xs.count z = 1 then ⟨2, by simp [table]⟩ else ⟨0, by simp [table]⟩ :=
  (later_folds z xs).2.2

private theorem eval_laterValuation (z : Nat) (w : Word Nat)
    (hne : w.head ≠ z) :
    table.semigroup.eval (laterValuation z) w =
      if w.toList.count z = 0 then ⟨5, by simp [table]⟩
      else if w.toList.count z = 1 then ⟨2, by simp [table]⟩
      else ⟨0, by simp [table]⟩ := by
  cases w with
  | mk head tail =>
    simpa [Word.toList, Semigroup.eval, laterValuation, hne] using
      later_fold_five z tail

private theorem valid_heads_eq (e : Identity Nat)
    (h : e.SatisfiedBy table.semigroup) : e.lhs.head = e.rhs.head := by
  have ho := valid_order e h
  simpa [Word.toList, firstOccurrenceSequence] using congrArg List.head? ho

private theorem valid_first_count (e : Identity Nat)
    (h : e.SatisfiedBy table.semigroup) :
    min (e.lhs.toList.count e.lhs.head) 3 =
      min (e.rhs.toList.count e.lhs.head) 3 := by
  have heads := valid_heads_eq e h
  have sem := h (firstValuation e.lhs.head)
  rw [eval_firstValuation e.lhs.head e.lhs rfl,
    eval_firstValuation e.lhs.head e.rhs heads.symm] at sem
  have semval := congrArg Fin.val sem
  have posL : 0 < e.lhs.toList.count e.lhs.head := by simp [Word.toList]
  have posR : 0 < e.rhs.toList.count e.lhs.head := by simp [Word.toList, heads]
  by_cases a1 : e.lhs.toList.count e.lhs.head = 1
  · by_cases b1 : e.rhs.toList.count e.lhs.head = 1
    · simp [a1, b1]
    · by_cases b2 : e.rhs.toList.count e.lhs.head = 2
      · simp [a1, b1, b2, table] at semval <;> omega
      · simp [a1, b1, b2, table] at semval <;> omega
  · by_cases a2 : e.lhs.toList.count e.lhs.head = 2
    · by_cases b1 : e.rhs.toList.count e.lhs.head = 1
      · simp [a1, a2, b1, table] at semval <;> omega
      · by_cases b2 : e.rhs.toList.count e.lhs.head = 2
        · simp [a2, b2]
        · simp [a1, a2, b1, b2, table] at semval <;> omega
    · by_cases b1 : e.rhs.toList.count e.lhs.head = 1
      · simp [a1, a2, b1, table] at semval <;> omega
      · by_cases b2 : e.rhs.toList.count e.lhs.head = 2
        · simp [a1, a2, b1, b2, table] at semval <;> omega
        · simp [Nat.min_eq_right (by omega : 3 ≤ e.lhs.toList.count e.lhs.head),
            Nat.min_eq_right (by omega : 3 ≤ e.rhs.toList.count e.lhs.head)]

private theorem valid_later_count (e : Identity Nat)
    (h : e.SatisfiedBy table.semigroup) (z : Nat)
    (hz : z ≠ e.lhs.head) :
    min (e.lhs.toList.count z) 2 =
      min (e.rhs.toList.count z) 2 := by
  have heads := valid_heads_eq e h
  have hL : e.lhs.head ≠ z := Ne.symm hz
  have hR : e.rhs.head ≠ z := by simpa [heads] using hL
  have sem := h (laterValuation z)
  rw [eval_laterValuation z e.lhs hL,
    eval_laterValuation z e.rhs hR] at sem
  have semval := congrArg Fin.val sem
  by_cases a0 : e.lhs.toList.count z = 0
  · by_cases b0 : e.rhs.toList.count z = 0
    · simp [a0, b0]
    · by_cases b1 : e.rhs.toList.count z = 1
      · simp [a0, b0, b1, table] at semval <;> omega
      · simp [a0, b0, b1, table] at semval <;> omega
  · by_cases a1 : e.lhs.toList.count z = 1
    · by_cases b0 : e.rhs.toList.count z = 0
      · simp [a0, a1, b0, table] at semval <;> omega
      · by_cases b1 : e.rhs.toList.count z = 1
        · simp [a1, b1]
        · simp [a0, a1, b0, b1, table] at semval <;> omega
    · by_cases b0 : e.rhs.toList.count z = 0
      · simp [a0, a1, b0, table] at semval <;> omega
      · by_cases b1 : e.rhs.toList.count z = 1
        · simp [a0, a1, b0, b1, table] at semval <;> omega
        · simp [Nat.min_eq_right (by omega : 2 ≤ e.lhs.toList.count z),
            Nat.min_eq_right (by omega : 2 ≤ e.rhs.toList.count z)]

private theorem source_axioms :
    ∀ e : Identity Nat, e ∈ s5_530Basis →
      Derives basis e.lhs e.rhs := by
  unfold s5_530Basis;
  simp +zetaDelta at *;
  constructor <;> apply Derives.fromBasis <;> (unfold basis; simp +decide)

private def tailInstantiate (p q : Word Nat) : Nat → Word Nat
  | 0 => p
  | 1 => q
  | n + 2 => Word.singleton (n + 2)

private theorem derives_tail_contract (p : Word Nat) (y : Nat) (suffix : Word Nat) :
    Derives basis
      (((p ++ Word.singleton y) ++ Word.singleton y) ++ Word.singleton y ++ suffix)
      (((p ++ Word.singleton y) ++ Word.singleton y) ++ suffix) := by
  have hbase : Derives basis xyyy xyy :=
    Derives.symm (Derives.fromBasis (e := tailLaw) (by
      simp [basis]))
  have hbase' : Derives basis
      (⟨0, [1, 1, 1]⟩ : Word Nat) ⟨0, [1, 1]⟩ := by
    exact hbase
  have h := Derives.subst hbase' (tailInstantiate p (Word.singleton y))
  have hs := Derives.appendRight h suffix
  simpa [tailInstantiate, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using hs

private def appendLetters (p : Word Nat) (xs : List Nat) : Word Nat :=
  xs.foldl (fun q x => q ++ Word.singleton x) p

private inductive ShortTailEq : List Nat → List Nat → Prop
  | nil : ShortTailEq [] []
  | single (x) {xs ys} : ShortTailEq xs ys → ShortTailEq (x :: xs) (x :: ys)
  | double (x) {xs ys} : ShortTailEq xs ys →
      ShortTailEq (x :: x :: xs) (x :: x :: ys)
  | doubleTriple (x) {xs ys} : ShortTailEq xs ys →
      ShortTailEq (x :: x :: xs) (x :: x :: x :: ys)
  | tripleDouble (x) {xs ys} : ShortTailEq xs ys →
      ShortTailEq (x :: x :: x :: xs) (x :: x :: ys)
  | triple (x) {xs ys} : ShortTailEq xs ys →
      ShortTailEq (x :: x :: x :: xs) (x :: x :: x :: ys)

private theorem appendLetters_append (p : Word Nat) (xs ys : List Nat) :
    appendLetters p (xs ++ ys) = appendLetters (appendLetters p xs) ys := by
  unfold appendLetters; simp +decide [ List.foldl_append ] ;

private theorem appendLetters_derives {p q : Word Nat}
    (h : Derives basis p q) (xs : List Nat) :
    Derives basis (appendLetters p xs) (appendLetters q xs) := by
  induction xs generalizing p q with
  | nil => exact h
  | cons x xs ih =>
      simp only [appendLetters, List.foldl_cons]
      exact ih (Derives.appendRight h (Word.singleton x))

private theorem tail_contract_no_suffix (p : Word Nat) (y : Nat) :
    Derives basis (appendLetters p [y, y, y]) (appendLetters p [y, y]) := by
  have hbase : Derives basis xyyy xyy :=
    Derives.symm (Derives.fromBasis (e := tailLaw) (by
      simp [basis]));
  have hbase' : Derives basis
      (⟨0, [1, 1, 1]⟩ : Word Nat) ⟨0, [1, 1]⟩ := hbase
  have h := Derives.subst hbase' (tailInstantiate p (Word.singleton y))
  simpa [appendLetters, tailInstantiate, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using h

private theorem shortTailEq_derives (p : Word Nat) {xs ys : List Nat}
    (h : ShortTailEq xs ys) :
    Derives basis (appendLetters p xs) (appendLetters p ys) := by
  induction h generalizing p with
  | nil => exact Derives.refl _
  | single x h ih =>
      simpa [appendLetters] using ih (appendLetters p [x])
  | double x h ih =>
      simpa [appendLetters] using ih (appendLetters p [x, x])
  | @doubleTriple x xs ys h ih =>
      have expand := Derives.symm (tail_contract_no_suffix p x)
      have expanded := appendLetters_derives expand ys
      exact Derives.trans (by
        simpa [appendLetters] using ih (appendLetters p [x, x])) (by
        simpa [appendLetters, appendLetters_append] using expanded)
  | @tripleDouble x xs ys h ih =>
      have contracted := appendLetters_derives (tail_contract_no_suffix p x) xs
      exact Derives.trans (by
        simpa [appendLetters, appendLetters_append] using contracted) (by
        simpa [appendLetters] using ih (appendLetters p [x, x]))
  | triple x h ih =>
      simpa [appendLetters] using ih (appendLetters p [x, x, x])

private theorem mem_firstOccurrenceSequence_iff (z : Nat) :
    ∀ xs : List Nat, z ∈ firstOccurrenceSequence xs ↔ z ∈ xs := by
  intro xs; induction xs <;> simp +decide [ *, firstOccurrenceSequence ] ;
  grind

private theorem filter_firstOccurrences_ne {x : Nat} {xs : List Nat}
    (h : x ∉ xs) :
    (firstOccurrenceSequence xs).filter (fun z => decide (z ≠ x)) =
      firstOccurrenceSequence xs := by
  apply List.filter_eq_self.mpr
  intro z hz
  simp only [decide_eq_true_eq]
  intro hzx
  subst z
  exact h ((mem_firstOccurrenceSequence_iff x xs).mp hz)

private theorem firstOccurrences_single {x : Nat} {xs : List Nat}
    (h : x ∉ xs) :
    firstOccurrenceSequence (x :: xs) = x :: firstOccurrenceSequence xs := by
  rw [firstOccurrenceSequence]
  congr 1
  exact filter_firstOccurrences_ne h

private theorem firstOccurrences_double {x : Nat} {xs : List Nat}
    (h : x ∉ xs) :
    firstOccurrenceSequence (x :: x :: xs) = x :: firstOccurrenceSequence xs := by
  simp [firstOccurrenceSequence]
  intro a ha haeq
  subst a
  exact h ((mem_firstOccurrenceSequence_iff x xs).mp ha)

private theorem firstOccurrences_triple {x : Nat} {xs : List Nat}
    (h : x ∉ xs) :
    firstOccurrenceSequence (x :: x :: x :: xs) = x :: firstOccurrenceSequence xs := by
  simp [firstOccurrenceSequence]
  intro a ha haeq
  subst a
  exact h ((mem_firstOccurrenceSequence_iff x xs).mp ha)

private theorem shortTailEq_of_normal
    {xs ys : List Nat}
    (nx : S5_530Normal xs) (ny : S5_530Normal ys)
    (ord : firstOccurrenceSequence xs = firstOccurrenceSequence ys)
    (caps : ∀ z, min (xs.count z) 2 = min (ys.count z) 2) :
    ShortTailEq xs ys := by
  induction nx generalizing ys with
  | nil =>
      cases ny with
      | nil => exact .nil
      | single y ys ny hy =>
          rw [firstOccurrences_single hy] at ord
          contradiction
      | double y ys ny hy =>
          rw [firstOccurrences_double hy] at ord
          contradiction
      | triple y ys ny hy =>
          rw [firstOccurrences_triple hy] at ord
          contradiction
  | single x xs nx hx ih =>
      cases ny with
      | nil =>
          rw [firstOccurrences_single hx] at ord
          contradiction
      | single y ys ny hy =>
          rw [firstOccurrences_single hx, firstOccurrences_single hy] at ord
          have hxy := (List.cons.inj ord).1
          subst y
          apply ShortTailEq.single x
          apply ih ny (List.cons.inj ord).2
          intro z
          by_cases hz : z = x
          · subst z
            simp [List.count_eq_zero.mpr hx, List.count_eq_zero.mpr hy]
          · specialize caps z
            simpa [List.count_cons_of_ne (Ne.symm hz)] using caps
      | double y ys ny hy =>
          rw [firstOccurrences_single hx, firstOccurrences_double hy] at ord
          have hxy := (List.cons.inj ord).1
          subst y
          have hc := caps x
          simp [List.count_eq_zero.mpr hx, List.count_eq_zero.mpr hy] at hc
      | triple y ys ny hy =>
          rw [firstOccurrences_single hx, firstOccurrences_triple hy] at ord
          have hxy := (List.cons.inj ord).1
          subst y
          have hc := caps x
          simp [List.count_eq_zero.mpr hx, List.count_eq_zero.mpr hy] at hc
  | double x xs nx hx ih =>
      cases ny with
      | nil =>
          rw [firstOccurrences_double hx] at ord
          contradiction
      | single y ys ny hy =>
          rw [firstOccurrences_double hx, firstOccurrences_single hy] at ord
          have hxy := (List.cons.inj ord).1
          subst y
          have hc := caps x
          simp [List.count_eq_zero.mpr hx, List.count_eq_zero.mpr hy] at hc
      | double y ys ny hy =>
          rw [firstOccurrences_double hx, firstOccurrences_double hy] at ord
          have hxy := (List.cons.inj ord).1
          subst y
          apply ShortTailEq.double x
          apply ih ny (List.cons.inj ord).2
          intro z
          by_cases hz : z = x
          · subst z
            simp [List.count_eq_zero.mpr hx, List.count_eq_zero.mpr hy]
          · specialize caps z
            simpa [List.count_cons_of_ne (Ne.symm hz)] using caps
      | triple y ys ny hy =>
          rw [firstOccurrences_double hx, firstOccurrences_triple hy] at ord
          have hxy := (List.cons.inj ord).1
          subst y
          apply ShortTailEq.doubleTriple x
          apply ih ny (List.cons.inj ord).2
          intro z
          by_cases hz : z = x
          · subst z
            simp [List.count_eq_zero.mpr hx, List.count_eq_zero.mpr hy]
          · specialize caps z
            simpa [List.count_cons_of_ne (Ne.symm hz)] using caps
  | triple x xs nx hx ih =>
      cases ny with
      | nil =>
          rw [firstOccurrences_triple hx] at ord
          contradiction
      | single y ys ny hy =>
          rw [firstOccurrences_triple hx, firstOccurrences_single hy] at ord
          have hxy := (List.cons.inj ord).1
          subst y
          have hc := caps x
          simp [List.count_eq_zero.mpr hx, List.count_eq_zero.mpr hy] at hc
      | double y ys ny hy =>
          rw [firstOccurrences_triple hx, firstOccurrences_double hy] at ord
          have hxy := (List.cons.inj ord).1
          subst y
          apply ShortTailEq.tripleDouble x
          apply ih ny (List.cons.inj ord).2
          intro z
          by_cases hz : z = x
          · subst z
            simp [List.count_eq_zero.mpr hx, List.count_eq_zero.mpr hy]
          · specialize caps z
            simpa [List.count_cons_of_ne (Ne.symm hz)] using caps
      | triple y ys ny hy =>
          rw [firstOccurrences_triple hx, firstOccurrences_triple hy] at ord
          have hxy := (List.cons.inj ord).1
          subst y
          apply ShortTailEq.triple x
          apply ih ny (List.cons.inj ord).2
          intro z
          by_cases hz : z = x
          · subst z
            simp [List.count_eq_zero.mpr hx, List.count_eq_zero.mpr hy]
          · specialize caps z
            simpa [List.count_cons_of_ne (Ne.symm hz)] using caps

private theorem normal_tail {x : Nat} {xs : List Nat}
    (h : S5_530Normal (x :: xs)) : S5_530Normal xs := by
  cases h with
  | single x xs hn hx => exact hn
  | double x xs hn hx => exact S5_530Normal.single x xs hn hx
  | triple x xs hn hx => exact S5_530Normal.double x xs hn hx

private theorem appendLetters_singleton (x : Nat) (xs : List Nat) :
    appendLetters (Word.singleton x) xs = ⟨x, xs⟩ := by
  have aux : ∀ (tail rest : List Nat),
      appendLetters (⟨x, tail⟩ : Word Nat) rest = ⟨x, tail ++ rest⟩ := by
    intro tail rest
    induction rest generalizing tail with
    | nil => simp [appendLetters]
    | cons y ys ih =>
        simp only [appendLetters, List.foldl_cons]
        simpa [Word.append] using ih (tail ++ [y])
  simpa [Word.singleton] using aux [] xs

private theorem firstOccurrences_head (w : Word Nat) :
    (firstOccurrenceSequence w.toList).head? = some w.head := by
  rfl

private inductive InitialShortEq : List Nat → List Nat → Prop
  | single (x) {xs ys} : ShortTailEq xs ys →
      InitialShortEq (x :: xs) (x :: ys)
  | double (x) {xs ys} : ShortTailEq xs ys →
      InitialShortEq (x :: x :: xs) (x :: x :: ys)
  | triple (x) {xs ys} : ShortTailEq xs ys →
      InitialShortEq (x :: x :: x :: xs) (x :: x :: x :: ys)

private theorem appendLetters_prefix (x : Nat) (pre rest : List Nat) :
    appendLetters (appendLetters (Word.singleton x) pre) rest =
      ⟨x, pre ++ rest⟩ := by
  rw [← appendLetters_append, appendLetters_singleton]

private theorem initialShortEq_derives {xs ys : List Nat}
    (h : InitialShortEq xs ys) :
    match xs, ys with
    | x :: xt, y :: yt => Derives basis ⟨x, xt⟩ ⟨y, yt⟩
    | _, _ => False := by
  cases h with
  | single x h =>
      simpa [appendLetters_singleton] using
        shortTailEq_derives (Word.singleton x) h
  | double x h =>
      have d := shortTailEq_derives
        (appendLetters (Word.singleton x) [x]) h
      simpa only [appendLetters_prefix] using d
  | triple x h =>
      have d := shortTailEq_derives
        (appendLetters (Word.singleton x) [x, x]) h
      simpa only [appendLetters_prefix] using d

private theorem initialShortEq_of_normal
    {xs ys : List Nat}
    (nx : S5_530Normal xs) (ny : S5_530Normal ys)
    (hxne : xs ≠ []) (hyne : ys ≠ [])
    (ord : firstOccurrenceSequence xs = firstOccurrenceSequence ys)
    (headCounts : xs.count xs.head! = ys.count xs.head!)
    (laterCaps : ∀ z, z ≠ xs.head! →
      min (xs.count z) 2 = min (ys.count z) 2) :
    InitialShortEq xs ys := by
  cases nx with
  | nil => contradiction
  | single x xt nxt hx =>
    cases ny with
    | nil => contradiction
    | single y yt nyt hy =>
      rw [firstOccurrences_single hx, firstOccurrences_single hy] at ord
      have hxy := (List.cons.inj ord).1
      subst y
      apply InitialShortEq.single x
      apply shortTailEq_of_normal nxt nyt (List.cons.inj ord).2
      intro z
      by_cases hz : z = x
      · subst z; simp [List.count_eq_zero.mpr hx, List.count_eq_zero.mpr hy]
      · have hc := laterCaps z (by simpa using hz)
        simpa [List.count_cons_of_ne (Ne.symm hz)] using hc
    | double y yt nyt hy =>
      rw [firstOccurrences_single hx, firstOccurrences_double hy] at ord
      have hxy := (List.cons.inj ord).1; subst y
      simp [List.head!, List.count_eq_zero.mpr hx,
        List.count_eq_zero.mpr hy] at headCounts
    | triple y yt nyt hy =>
      rw [firstOccurrences_single hx, firstOccurrences_triple hy] at ord
      have hxy := (List.cons.inj ord).1; subst y
      simp [List.head!, List.count_eq_zero.mpr hx,
        List.count_eq_zero.mpr hy] at headCounts
  | double x xt nxt hx =>
    cases ny with
    | nil => contradiction
    | single y yt nyt hy =>
      rw [firstOccurrences_double hx, firstOccurrences_single hy] at ord
      have hxy := (List.cons.inj ord).1; subst y
      simp [List.head!, List.count_eq_zero.mpr hx,
        List.count_eq_zero.mpr hy] at headCounts
    | double y yt nyt hy =>
      rw [firstOccurrences_double hx, firstOccurrences_double hy] at ord
      have hxy := (List.cons.inj ord).1; subst y
      apply InitialShortEq.double x
      apply shortTailEq_of_normal nxt nyt (List.cons.inj ord).2
      intro z
      by_cases hz : z = x
      · subst z; simp [List.count_eq_zero.mpr hx, List.count_eq_zero.mpr hy]
      · have hc := laterCaps z (by simpa using hz)
        simpa [List.count_cons_of_ne (Ne.symm hz)] using hc
    | triple y yt nyt hy =>
      rw [firstOccurrences_double hx, firstOccurrences_triple hy] at ord
      have hxy := (List.cons.inj ord).1; subst y
      simp [List.head!, List.count_eq_zero.mpr hx,
        List.count_eq_zero.mpr hy] at headCounts
  | triple x xt nxt hx =>
    cases ny with
    | nil => contradiction
    | single y yt nyt hy =>
      rw [firstOccurrences_triple hx, firstOccurrences_single hy] at ord
      have hxy := (List.cons.inj ord).1; subst y
      simp [List.head!, List.count_eq_zero.mpr hx,
        List.count_eq_zero.mpr hy] at headCounts
    | double y yt nyt hy =>
      rw [firstOccurrences_triple hx, firstOccurrences_double hy] at ord
      have hxy := (List.cons.inj ord).1; subst y
      simp [List.head!, List.count_eq_zero.mpr hx,
        List.count_eq_zero.mpr hy] at headCounts
    | triple y yt nyt hy =>
      rw [firstOccurrences_triple hx, firstOccurrences_triple hy] at ord
      have hxy := (List.cons.inj ord).1; subst y
      apply InitialShortEq.triple x
      apply shortTailEq_of_normal nxt nyt (List.cons.inj ord).2
      intro z
      by_cases hz : z = x
      · subst z; simp [List.count_eq_zero.mpr hx, List.count_eq_zero.mpr hy]
      · have hc := laterCaps z (by simpa using hz)
        simpa [List.count_cons_of_ne (Ne.symm hz)] using hc

private theorem derives_of_short_block_invariants
    (left right : Word Nat)
    (order : firstOccurrenceSequence left.toList =
      firstOccurrenceSequence right.toList)
    (firstCount : min (left.toList.count left.head) 3 =
      min (right.toList.count left.head) 3)
    (laterCounts : ∀ z, z ≠ left.head →
      min (left.toList.count z) 2 = min (right.toList.count z) 2) :
    Derives basis left right := by
  have leftNormal := s5_530DerivesNormal left
  have rightNormal := s5_530DerivesNormal right
  cases hl : s5_530NormalList left.toList with
  | nil =>
      exact False.elim <|
        s5_530NormalList_cons_ne_nil left.head left.tail <| by
          simpa [Word.toList] using hl
  | cons x xs =>
      cases hr : s5_530NormalList right.toList with
      | nil =>
          exact False.elim <|
            s5_530NormalList_cons_ne_nil right.head right.tail <| by
              simpa [Word.toList] using hr
      | cons y ys =>
          rw [hl] at leftNormal
          rw [hr] at rightNormal
          have normalOrder :
              firstOccurrenceSequence (x :: xs) =
                firstOccurrenceSequence (y :: ys) := by
            have leftPreserved :=
              s5_530Derives_firstOccurrenceSequence_eq leftNormal
            have rightPreserved :=
              s5_530Derives_firstOccurrenceSequence_eq rightNormal
            exact leftPreserved.symm.trans <|
              order.trans rightPreserved
          have leftHead : x = left.head := by
            have preserved :=
              s5_530Derives_firstOccurrenceSequence_eq leftNormal
            have heads := congrArg List.head? preserved
            rw [firstOccurrences_head left,
              firstOccurrences_head (s5_530WordOfCons x xs)] at heads
            simpa [s5_530WordOfCons] using heads.symm
          have leftCount (z : Nat) :
              (x :: xs).count z =
                s5_530Exponent (left.toList.count z) := by
            calc
              (x :: xs).count z =
                  (s5_530NormalList left.toList).count z := by
                    rw [hl]
              _ = s5_530Exponent (left.toList.count z) :=
                    s5_530NormalList_count z left.toList
          have rightCount (z : Nat) :
              (y :: ys).count z =
                s5_530Exponent (right.toList.count z) := by
            calc
              (y :: ys).count z =
                  (s5_530NormalList right.toList).count z := by
                    rw [hr]
              _ = s5_530Exponent (right.toList.count z) :=
                    s5_530NormalList_count z right.toList
          have leftForm : S5_530Normal (x :: xs) := by
            rw [← hl]
            exact s5_530NormalList_normal left.toList
          have rightForm : S5_530Normal (y :: ys) := by
            rw [← hr]
            exact s5_530NormalList_normal right.toList
          have normalHeadCounts :
              (x :: xs).count (x :: xs).head! =
                (y :: ys).count (x :: xs).head! := by
            change (x :: xs).count x = (y :: ys).count x
            rw [leftCount x, rightCount x]
            simpa [s5_530Exponent, leftHead] using firstCount
          have normalLaterCaps :
              ∀ z, z ≠ (x :: xs).head! →
                min ((x :: xs).count z) 2 =
                  min ((y :: ys).count z) 2 := by
            intro z hz
            change z ≠ x at hz
            rw [leftCount z, rightCount z]
            have capped := laterCounts z <| by
              simpa [leftHead] using hz
            simpa [s5_530Exponent, Nat.min_assoc] using capped
          have sameShortForm :=
            initialShortEq_of_normal leftForm rightForm
              (by simp) (by simp) normalOrder
              normalHeadCounts normalLaterCaps
          have middle :
              Derives basis
                (s5_530WordOfCons x xs)
                (s5_530WordOfCons y ys) := by
            simpa [s5_530WordOfCons] using
              initialShortEq_derives sameShortForm
          exact Derives.trans
            (leftNormal.transport source_axioms) <|
              Derives.trans middle <|
                Derives.symm (rightNormal.transport source_axioms)

theorem basis_complete_aristotle : BasisFor table.semigroup basis := by
  refine ⟨basis_models, ?_⟩
  intro e valid
  apply derives_of_short_block_invariants e.lhs e.rhs
  · exact valid_order e valid
  · exact valid_first_count e valid
  · exact valid_later_count e valid

end Order6S6_5641SingletonShortBlock
end CoRoots
end SemigroupBasis
