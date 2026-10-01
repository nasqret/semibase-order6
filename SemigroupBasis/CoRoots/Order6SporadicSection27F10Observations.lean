import SemigroupBasis.CoRoots.Order6SporadicSection27F10Tables
import SemigroupBasis.CoRoots.Order6SporadicSection27F10Combinatorics
import SemigroupBasis.CoRoots.S5_345Factors

/-! F10 observations use a fixed left context 3 and right context 5.
This avoids a nonempty-prefix exception and provides the paper's fresh right
fence even at the final block. Neither context is cancelled in any proof.
-/

namespace SemigroupBasis.CoRoots.Order6SporadicSection27.F10

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_870

def scan (v : Nat → Fin 6) (state : Fin 6) (letters : List Nat) : Fin 6 :=
  letters.foldl (fun a x => mul a (v x)) state

def observe (v : Nat → Fin 6) (letters : List Nat) : Fin 6 :=
  mul (scan v 3 letters) 5

theorem scan_nil (v : Nat → Fin 6) (a : Fin 6) : scan v a [] = a := rfl
theorem scan_cons (v : Nat → Fin 6) (a : Fin 6) (x : Nat) (xs : List Nat) :
    scan v a (x :: xs) = scan v (mul a (v x)) xs := rfl

theorem scan_append (v : Nat → Fin 6) (a : Fin 6) (xs ys : List Nat) :
    scan v a (xs ++ ys) = scan v (scan v a xs) ys := by
  simp only [scan, List.foldl_append]

theorem scan_fixed (v : Nat → Fin 6) (a value : Fin 6) (letters : List Nat)
    (same : ∀ x, x ∈ letters → v x = value) (fixed : mul a value = a) :
    scan v a letters = a := by
  induction letters with
  | nil => rfl
  | cons x xs ih =>
      rw [scan_cons, same x (by simp), fixed]
      exact ih (fun y member => same y (List.Mem.tail x member))

theorem scan_absorbs (v : Nat → Fin 6) (a : Fin 6) (letters : List Nat)
    (absorbs : ∀ b, mul a b = a) : scan v a letters = a := by
  induction letters with
  | nil => rfl
  | cons x xs ih => rw [scan_cons, absorbs]; exact ih

theorem finish_absorbs (a b : Fin 6) : mul (mul a 5) b = mul a 5 := by
  revert a b
  decide

theorem finish_sparse {seen : List Nat} {blocks : List FirstOccurrenceGapBlock}
    (sparse : SparseBlocks seen blocks) (v : Nat → Fin 6)
    (future : ∀ x, x ∉ seen → v x = 5) (a : Fin 6) :
    mul (scan v a (renderGapBlocks blocks)) 5 = mul a 5 := by
  cases blocks with
  | nil => rfl
  | cons block rest =>
      change mul (scan v a (block.marker :: (block.seconds ++ renderGapBlocks rest))) 5 = _
      rw [scan_cons, future block.marker sparse.cons_inv.1]
      rw [scan_absorbs v (mul a 5) _ (finish_absorbs a)]
      exact finish_absorbs a 5

theorem scan_mul (v : Nat → Fin 6) (a b : Fin 6) (letters : List Nat) :
    scan v (mul a b) letters = mul a (scan v b letters) := by
  induction letters generalizing b with
  | nil => rfl
  | cons x xs ih =>
      have associate : mul (mul a b) (v x) = mul a (mul b (v x)) := table.assoc a b (v x)
      rw [scan_cons, scan_cons, associate]
      exact ih (mul b (v x))

theorem scan_word (v : Nat → Fin 6) (a : Fin 6) (word : Word Nat) :
    scan v a word.toList = mul a (table.semigroup.eval v word) := by
  cases word with
  | mk head tail => exact scan_mul v a (v head) tail

theorem valid_observe (e : Identity Nat) (valid : e.SatisfiedBy table.semigroup)
    (v : Nat → Fin 6) : observe v e.lhs.toList = observe v e.rhs.toList := by
  unfold observe
  rw [scan_word, scan_word, valid v]

def iniEmbedding : Embedding Examples.leftRegularBandThree.semigroup table.semigroup where
  toFun := fun a : Fin 3 => if a = 0 then (0 : Fin 6) else if a = 1 then (3 : Fin 6) else (2 : Fin 6)
  map_mul := by intro a b; apply Fin.ext; revert a b; decide
  injective := by intro a b; revert a b; decide

theorem firstScans_agree (seen letters : List Nat) :
    firstOccurrenceSequenceAux seen letters =
      (Examples.firstOccurrenceSequence letters).filter (fun x => decide (x ∉ seen)) := by
  induction letters generalizing seen with
  | nil => rfl
  | cons head tail ih =>
      by_cases member : head ∈ seen
      · simp only [firstOccurrenceSequenceAux, if_pos member, ih,
          Examples.firstOccurrenceSequence, List.filter_cons]
        simp only [member, not_true_eq_false, decide_false, Bool.false_eq_true, if_false,
          List.filter_filter]
        apply congrArg (fun predicate => (Examples.firstOccurrenceSequence tail).filter predicate)
        funext x
        by_cases hx : x ∈ seen
        · simp [hx]
        · have different : x ≠ head := by
            intro equal
            exact hx (by simpa [equal] using member)
          simp [hx, different]
      · simp only [firstOccurrenceSequenceAux, if_neg member, ih,
          Examples.firstOccurrenceSequence, List.filter_cons]
        simp only [member, not_false_eq_true, decide_true, if_true, List.filter_filter]
        apply congrArg (List.cons head)
        apply congrArg (fun predicate => (Examples.firstOccurrenceSequence tail).filter predicate)
        funext x
        by_cases equal : x = head <;> by_cases hx : x ∈ seen <;> simp [equal, hx]

theorem firstSequence_agree (letters : List Nat) :
    firstOccurrenceSequenceList letters = Examples.firstOccurrenceSequence letters := by
  have allTrue :
      (Examples.firstOccurrenceSequence letters).filter (fun x => decide (x ∉ ([] : List Nat))) =
        Examples.firstOccurrenceSequence letters := by
    induction Examples.firstOccurrenceSequence letters with
    | nil => rfl
    | cons head tail ih => simpa only [List.filter_cons, List.not_mem_nil,
        not_false_eq_true, decide_true, if_true] using congrArg (List.cons head) ih
  exact (firstScans_agree [] letters).trans allTrue

theorem valid_ini (e : Identity Nat) (valid : e.SatisfiedBy table.semigroup) :
    firstOccurrenceSequenceList e.lhs.toList = firstOccurrenceSequenceList e.rhs.toList := by
  rw [firstSequence_agree, firstSequence_agree]
  exact S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq e
    (iniEmbedding.pullback_identity e valid)

structure Observations (left right : List Nat) : Prop where
  ini : firstOccurrenceSequenceList left = firstOccurrenceSequenceList right
  probes : ∀ v, observe v left = observe v right

theorem Observations.refl (letters : List Nat) : Observations letters letters :=
  ⟨rfl, fun _ => rfl⟩
theorem Observations.symm {left right : List Nat} (h : Observations left right) :
    Observations right left := ⟨h.ini.symm, fun v => (h.probes v).symm⟩
theorem Observations.trans {a b c : List Nat} (h : Observations a b) (k : Observations b c) :
    Observations a c := ⟨h.ini.trans k.ini, fun v => (h.probes v).trans (k.probes v)⟩

theorem valid_observations (e : Identity Nat) (valid : e.SatisfiedBy table.semigroup) :
    Observations e.lhs.toList e.rhs.toList := ⟨valid_ini e valid, valid_observe e valid⟩

theorem observations_of_listDerives {left right : List Nat}
    (derivation : S5_107.ListDerives basis left right) : Observations left right := by
  cases derivation with
  | empty => exact Observations.refl []
  | @words lh rh lt rt proof =>
      exact valid_observations ⟨S5_107.listWordOfCons lh lt, S5_107.listWordOfCons rh rt⟩
        (proof.sound models)

end SemigroupBasis.CoRoots.Order6SporadicSection27.F10

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.scan_append
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.scan_fixed
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.scan_absorbs
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.finish_absorbs
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.finish_sparse
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.scan_mul
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.scan_word
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.valid_observe
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.iniEmbedding
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.firstScans_agree
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.firstSequence_agree
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.valid_ini
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.valid_observations
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.observations_of_listDerives
