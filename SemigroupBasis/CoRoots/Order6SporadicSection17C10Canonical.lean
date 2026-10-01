import SemigroupBasis.CoRoots.Order6SporadicSection17C10Doubling
import SemigroupBasis.CoRoots.Order6SporadicSection17C10Saturation

/-! An unrestricted square-block normalizer for C10/D1. Parsing preserves every simple
separator, square expansion is justified by the original occurrence counts,
and saturation gives the descending nonempty-body contents of Lemma17.7. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1
open SemigroupBasis

def decompose (simple : Nat → Bool) : List Nat → SquareForm
  | [] => ⟨[],[]⟩
  | x :: xs =>
      let later := decompose simple xs
      if simple x then ⟨[],(x,later.initial) :: later.slots⟩
      else ⟨x :: later.initial,later.slots⟩

def separators (form : SquareForm) : List Nat := form.slots.map Prod.fst
def bodySupport (form : SquareForm) : List Nat := form.initial ++ slotSupport form.slots

theorem decompose_render (simple : Nat → Bool) (letters : List Nat) :
    renderForm (decompose simple letters) = doubleSelected simple letters := by
  induction letters with
  | nil => rfl
  | cons x xs ih =>
      cases flag : simple x <;>
        simpa [decompose,flag,renderForm,renderSlots,squareList_cons,squareList_nil,
          doubleSelected,List.append_assoc] using congrArg (fun rest =>
            if simple x then x :: rest else x :: x :: rest) ih

theorem decompose_separators (simple : Nat → Bool) (letters : List Nat) :
    separators (decompose simple letters) = letters.filter simple := by
  induction letters with
  | nil => rfl
  | cons x xs ih =>
      cases flag : simple x <;> simp [decompose,flag,separators,List.filter,← ih]

theorem decompose_support (simple : Nat → Bool) (letters : List Nat) :
    bodySupport (decompose simple letters) = letters.filter (fun x => !(simple x)) := by
  induction letters with
  | nil => rfl
  | cons x xs ih =>
      cases flag : simple x <;> simp [decompose,flag,bodySupport,slotSupport,List.filter,← ih]

theorem filter_nodup_of_count (simple : Nat → Bool) (letters : List Nat)
    (bounded : ∀ x, simple x = true → letters.count x ≤ 1) : (letters.filter simple).Nodup := by
  induction letters with
  | nil => simp
  | cons x xs ih =>
      have tailBound : ∀ y, simple y = true → xs.count y ≤ 1 := by
        intro y kept
        have bound := bounded y kept
        by_cases same : x = y
        · subst x
          simp only [List.count_cons_self] at bound
          omega
        · simpa [List.count_cons_of_ne same] using bound
      cases flag : simple x with
      | false => simpa [List.filter,flag] using ih tailBound
      | true =>
          have countZero : xs.count x = 0 := by
            have bound := bounded x flag
            simp only [List.count_cons_self] at bound
            omega
          have absent : x ∉ xs.filter simple := by
            intro member
            exact (List.count_eq_zero.mp countZero) (List.mem_filter.mp member).1
          simpa [List.filter,flag] using List.nodup_cons.mpr ⟨absent,ih tailBound⟩

theorem simpleSubsequence_nodup (letters : List Nat) :
    (letters.filter (simpleMask letters)).Nodup := by
  apply filter_nodup_of_count
  intro x kept
  have countOne : letters.count x = 1 := by simpa [simpleMask] using kept
  omega

def WellFormed (form : SquareForm) : Prop :=
  (separators form).Nodup ∧ ∀ x ∈ bodySupport form, x ∉ separators form

theorem decompose_wellFormed (letters : List Nat) :
    WellFormed (decompose (simpleMask letters) letters) := by
  constructor
  · rw [decompose_separators]
    exact simpleSubsequence_nodup letters
  · intro x inBody inSeparators
    rw [decompose_support] at inBody
    rw [decompose_separators] at inSeparators
    have nonsimple : simpleMask letters x = false := by
      simpa using (List.mem_filter.mp inBody).2
    have simple : simpleMask letters x = true := (List.mem_filter.mp inSeparators).2
    simp [nonsimple] at simple

theorem saturateSlots_separators (slots : Slots) :
    (saturateSlots slots).map Prod.fst = slots.map Prod.fst := by
  induction slots with
  | nil => rfl
  | cons slot rest ih =>
      rcases slot with ⟨separator,body⟩
      simp [saturateSlots,ih]

theorem saturateForm_separators (form : SquareForm) :
    separators (saturateForm form) = separators form := saturateSlots_separators form.slots

theorem saturateForm_support (form : SquareForm) (x : Nat) :
    x ∈ bodySupport (saturateForm form) ↔ x ∈ bodySupport form := by
  by_cases empty : form.initial = []
  · simp [bodySupport,saturateForm,saturateBody,empty,saturateSlots_support]
  · simp [bodySupport,saturateForm,saturateBody,empty,saturateSlots_support,or_assoc,or_comm,or_left_comm]

theorem saturateForm_wellFormed (form : SquareForm) (good : WellFormed form) :
    WellFormed (saturateForm form) := by
  constructor
  · rw [saturateForm_separators]
    exact good.1
  · intro x inBody inSeparators
    exact good.2 x ((saturateForm_support form x).mp inBody)
      (by simpa [saturateForm_separators] using inSeparators)

def normalForm (letters : List Nat) : SquareForm := saturateForm (decompose (simpleMask letters) letters)

theorem derives_normalForm (letters : List Nat) : ListDerives letters (renderForm (normalForm letters)) := by
  have doubled : ListDerives letters (renderForm (decompose (simpleMask letters) letters)) := by
    rw [decompose_render]
    exact doubleNonsimple_derives letters
  exact doubled.trans (saturateForm_derives (decompose (simpleMask letters) letters))

theorem normalForm_wellFormed (letters : List Nat) : WellFormed (normalForm letters) :=
  saturateForm_wellFormed _ (decompose_wellFormed letters)

theorem normalForm_saturated (letters : List Nat) : Saturated (normalForm letters) :=
  saturateForm_saturated _

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.decompose_render
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.simpleSubsequence_nodup
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.derives_normalForm
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.normalForm_wellFormed
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.normalForm_saturated

end SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1
