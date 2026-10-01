import SemigroupBasis.CoRoots.Order6SporadicSection17C5CubicExpansion

/-! Input-determined global cubic preparation. Each unrestricted letter is
selected once by the proved finite recognizer, and each of its occurrences
becomes exactly one cube. Simple letters and restricted squares are retained.
This is the first stage of beta normalization, not a completeness theorem. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
open SemigroupBasis

def unrestrictedMask (letters : List Nat) (x : Nat) : Bool :=
  decide (2 ≤ letters.count x ∧ restrictedScan x .fresh letters ≠ .square)

theorem unrestrictedMask_true (letters : List Nat) (x : Nat) :
    unrestrictedMask letters x = true ↔ Unrestricted x letters := by
  simp only [unrestrictedMask,decide_eq_true_eq]
  constructor
  · rintro ⟨two,notSquare⟩
    refine ⟨?_,by omega,?_⟩
    · by_cases present : x ∈ letters
      · exact present
      · have zero := List.count_eq_zero.mpr present
        omega
    · intro restricted
      exact notSquare ((restrictedScan_fresh_square x letters).mpr restricted)
  · rintro ⟨member,notOne,notRestricted⟩
    have notZero : letters.count x ≠ 0 := fun zero => (List.count_eq_zero.mp zero) member
    refine ⟨by omega,?_⟩
    intro square
    exact notRestricted ((restrictedScan_fresh_square x letters).mp square)

def uniqueMarkers : List Nat → List Nat
  | [] => []
  | x :: xs => if x ∈ xs then uniqueMarkers xs else x :: uniqueMarkers xs

theorem uniqueMarkers_mem (letters : List Nat) (x : Nat) :
    x ∈ uniqueMarkers letters ↔ x ∈ letters := by
  induction letters with
  | nil => simp [uniqueMarkers]
  | cons y ys ih =>
      by_cases present : y ∈ ys
      · simp only [uniqueMarkers,if_pos present,ih,List.mem_cons]
        constructor
        · exact fun member => Or.inr member
        · rintro (rfl | member)
          · exact present
          · exact member
      · simp [uniqueMarkers,present,ih]

theorem uniqueMarkers_nodup (letters : List Nat) : (uniqueMarkers letters).Nodup := by
  induction letters with
  | nil => simp [uniqueMarkers]
  | cons x xs ih =>
      by_cases present : x ∈ xs
      · simpa [uniqueMarkers,present] using ih
      · simp only [uniqueMarkers,if_neg present,List.nodup_cons]
        exact ⟨fun member => present ((uniqueMarkers_mem xs x).mp member),ih⟩

def unrestrictedMarkers (letters : List Nat) : List Nat :=
  uniqueMarkers (letters.filter (unrestrictedMask letters))

theorem unrestrictedMarkers_mem (letters : List Nat) (x : Nat) :
    x ∈ unrestrictedMarkers letters ↔ Unrestricted x letters := by
  rw [unrestrictedMarkers,uniqueMarkers_mem]
  simp only [List.mem_filter,unrestrictedMask_true]
  exact ⟨fun pair => pair.2,fun unrestricted => ⟨unrestricted.1,unrestricted⟩⟩

theorem unrestrictedMarkers_nodup (letters : List Nat) : (unrestrictedMarkers letters).Nodup :=
  uniqueMarkers_nodup _

def cubeTile (markers : List Nat) (x : Nat) : List Nat :=
  if x ∈ markers then [x,x,x] else [x]

theorem tripleMarkers_nil (markers : List Nat) : tripleMarkers markers [] = [] := by
  induction markers with
  | nil => rfl
  | cons x xs ih => simp [tripleMarkers,ih,tripleMarker]

theorem tripleMarkers_append (markers left right : List Nat) :
    tripleMarkers markers (left ++ right) = tripleMarkers markers left ++ tripleMarkers markers right := by
  induction markers with
  | nil => rfl
  | cons x xs ih => simp [tripleMarkers,ih,tripleMarker_append]

theorem tripleMarkers_singleton (markers : List Nat) (distinct : markers.Nodup) (x : Nat) :
    tripleMarkers markers [x] = cubeTile markers x := by
  induction markers generalizing x with
  | nil => simp [tripleMarkers,cubeTile]
  | cons marker rest ih =>
      have absent := (List.nodup_cons.mp distinct).1
      have tailDistinct := (List.nodup_cons.mp distinct).2
      have previous := ih tailDistinct x
      by_cases equal : x = marker
      · subst x
        simp [tripleMarkers,previous,cubeTile,absent,tripleMarker]
      · by_cases present : x ∈ rest
        · simp [tripleMarkers,previous,cubeTile,present,equal,Ne.symm equal,tripleMarker]
        · simp [tripleMarkers,previous,cubeTile,present,equal,Ne.symm equal,tripleMarker]

theorem tripleMarkers_pointwise (markers letters : List Nat) (distinct : markers.Nodup) :
    tripleMarkers markers letters = letters.flatMap (cubeTile markers) := by
  induction letters with
  | nil => exact tripleMarkers_nil markers
  | cons x xs ih =>
      calc
        tripleMarkers markers (x :: xs) = tripleMarkers markers [x] ++ tripleMarkers markers xs :=
          tripleMarkers_append markers [x] xs
        _ = cubeTile markers x ++ xs.flatMap (cubeTile markers) := by
          rw [tripleMarkers_singleton markers distinct x,ih]
        _ = (x :: xs).flatMap (cubeTile markers) := rfl

def cubicForm (letters : List Nat) : List Nat :=
  letters.flatMap (cubeTile (unrestrictedMarkers letters))

theorem cubicForm_derives (letters : List Nat) : ListDerives letters (cubicForm letters) := by
  have derivation := tripleMarkers_derives (unrestrictedMarkers letters) letters
    (fun x member => (unrestrictedMarkers_mem letters x).mp member)
  rw [tripleMarkers_pointwise _ _ (unrestrictedMarkers_nodup letters)] at derivation
  exact derivation

theorem cubeTile_unrestricted (letters : List Nat) (x : Nat) (unrestricted : Unrestricted x letters) :
    cubeTile (unrestrictedMarkers letters) x = [x,x,x] := by
  exact if_pos ((unrestrictedMarkers_mem letters x).mpr unrestricted)

theorem cubeTile_restricted (letters : List Nat) (x : Nat) (restricted : Restricted x letters) :
    cubeTile (unrestrictedMarkers letters) x = [x] := by
  apply if_neg
  intro member
  exact ((unrestrictedMarkers_mem letters x).mp member).2.2 restricted

theorem cubeTile_simple (letters : List Nat) (x : Nat) (simple : letters.count x = 1) :
    cubeTile (unrestrictedMarkers letters) x = [x] := by
  apply if_neg
  intro member
  exact ((unrestrictedMarkers_mem letters x).mp member).2.1 simple

theorem cubicForm_restricted (letters : List Nat) (x : Nat) :
    Restricted x (cubicForm letters) ↔ Restricted x letters :=
  ((Semantics.derives_sameEval false (cubicForm_derives letters)).restricted x).symm

theorem cubicForm_unrestricted (letters : List Nat) (x : Nat) :
    Unrestricted x (cubicForm letters) ↔ Unrestricted x letters :=
  (ListDerives.unrestricted_iff (cubicForm_derives letters) x).symm

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.unrestrictedMask_true
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.unrestrictedMarkers_mem
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.unrestrictedMarkers_nodup
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.tripleMarkers_pointwise
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.cubicForm_derives
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.cubeTile_unrestricted
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.cubeTile_restricted
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.cubeTile_simple
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.cubicForm_restricted
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.cubicForm_unrestricted

end SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
