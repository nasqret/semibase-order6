import SemigroupBasis.CoRoots.Order6SporadicSection18BoundarySupport
import SemigroupBasis.CoRoots.Order6SporadicSection18WindowEvaluation

/-! ONE whole-word valuation, with optional boundary-marker overrides.
Its nonzero source value and all nonsimple colors are proved from the actual
canonical witness; a same-evaluation target square cannot straddle the window. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Actual

def windowVal (left right : Option Nat) (inside : List Nat) (x : Nat) : Fin 6 :=
  if some x = left then 3 else if some x = right then 2 else if x ∈ inside then 4 else 5

theorem windowVal_colors (whole : List Nat) (left right : Option Nat) (inside : List Nat)
    (leftSimple : ∀ x, some x = left → whole.count x = 1)
    (rightSimple : ∀ x, some x = right → whole.count x = 1)
    (x : Nat) (nonsimple : whole.count x ≠ 1) :
    windowVal left right inside x = 4 ∨ windowVal left right inside x = 5 := by
  have notLeft : some x ≠ left := fun equal => nonsimple (leftSimple x equal)
  have notRight : some x ≠ right := fun equal => nonsimple (rightSimple x equal)
  simp only [windowVal, if_neg notLeft, if_neg notRight]
  by_cases member : x ∈ inside
  · rw [if_pos member]
    exact Or.inl rfl
  · rw [if_neg member]
    exact Or.inr rfl

end SemigroupBasis.CoRoots.Order6SporadicSection18.Actual

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
open Actual

private theorem mem_regions_inside (before inside after : List Nat) (x : Nat) (member : x ∈ inside) :
    x ∈ before ++ inside ++ after :=
  List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr member)))

private theorem mem_regions_outside (before inside after : List Nat) (x : Nat)
    (member : x ∈ before ++ after) : x ∈ before ++ inside ++ after := by
  rcases List.mem_append.mp member with inBefore | inAfter
  · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl inBefore)))
  · exact List.mem_append.mpr (Or.inr inAfter)

private theorem pairClear_ne (left right x : Nat) (letters : List Nat)
    (clear : PairClear left right letters) (member : x ∈ letters) : x ≠ left ∧ x ≠ right := by
  constructor
  · intro equal
    exact clear.1 (equal ▸ member)
  · intro equal
    exact clear.2 (equal ▸ member)

theorem MarkerForm.separating_valuation {whole before inside after : List Nat}
    (form : MarkerForm whole before inside after)
    (separated : ∀ x ∈ inside, x ∉ before ++ after) :
    ∃ (valuation : Nat → Fin 6) (acc : Fin 6), run valuation acc whole ≠ 0 ∧
      (∀ x ∈ inside, valuation x = 4) ∧ (∀ x ∈ before ++ after, valuation x = 5) ∧
      (∀ x, whole.count x ≠ 1 → valuation x = 4 ∨ valuation x = 5) := by
  cases form with
  | middle left right shape leftSimple rightSimple different clear =>
      let valuation := windowVal (some left) (some right) inside
      have insideFour : ∀ x ∈ inside, valuation x = 4 := by
        intro x member
        have notMarkers := pairClear_ne left right x _ clear (mem_regions_inside before inside after x member)
        simp only [valuation, windowVal, Option.some.injEq, if_neg notMarkers.1,
          if_neg notMarkers.2, if_pos member]
      have outsideFive : ∀ x ∈ before ++ after, valuation x = 5 := by
        intro x member
        have notMarkers := pairClear_ne left right x _ clear (mem_regions_outside before inside after x member)
        have notInside : x ∉ inside := fun present => separated x present member
        simp only [valuation, windowVal, Option.some.injEq, if_neg notMarkers.1,
          if_neg notMarkers.2, if_neg notInside]
      have value : run valuation 5 whole = 1 := by
        rw [shape]
        apply window_middle_value valuation before inside after left right
        · simp [valuation, windowVal]
        · simp [valuation, windowVal, Ne.symm different]
        · exact fun x member => outsideFive x (List.mem_append.mpr (Or.inl member))
        · exact insideFour
        · exact fun x member => outsideFive x (List.mem_append.mpr (Or.inr member))
      refine ⟨valuation, 5, ?_, insideFour, outsideFive, ?_⟩
      · rw [value]
        decide
      · intro x nonsimple
        apply windowVal_colors whole (some left) (some right) inside ?_ ?_ x nonsimple
        · intro y equal
          simpa only [Option.some.inj equal] using leftSimple
        · intro y equal
          simpa only [Option.some.inj equal] using rightSimple
  | initial right beforeEmpty shape rightSimple clear =>
      let valuation := windowVal none (some right) inside
      have insideFour : ∀ x ∈ inside, valuation x = 4 := by
        intro x member
        have notRight : x ≠ right := by
          intro equal
          exact clear (List.mem_append.mpr (Or.inl (equal ▸ member)))
        simp [valuation, windowVal, notRight, member]
      have outsideFive : ∀ x ∈ before ++ after, valuation x = 5 := by
        intro x member
        have inAfter : x ∈ after := by simpa only [beforeEmpty, List.nil_append] using member
        have notRight : x ≠ right := by
          intro equal
          exact clear (List.mem_append.mpr (Or.inr (equal ▸ inAfter)))
        have notInside : x ∉ inside := fun present => separated x present member
        simp [valuation, windowVal, notRight, notInside]
      have value : run valuation 4 whole = 2 := by
        rw [shape]
        apply window_initial_value valuation inside after right
        · simp [valuation, windowVal]
        · exact insideFour
        · exact fun x member => outsideFive x (List.mem_append.mpr (Or.inr member))
      refine ⟨valuation, 4, ?_, insideFour, outsideFive, ?_⟩
      · rw [value]
        decide
      · intro x nonsimple
        apply windowVal_colors whole none (some right) inside ?_ ?_ x nonsimple
        · intro y equal
          cases equal
        · intro y equal
          simpa only [Option.some.inj equal] using rightSimple
  | final left afterEmpty shape leftSimple clear =>
      let valuation := windowVal (some left) none inside
      have insideFour : ∀ x ∈ inside, valuation x = 4 := by
        intro x member
        have notLeft : x ≠ left := by
          intro equal
          exact clear (List.mem_append.mpr (Or.inr (equal ▸ member)))
        simp [valuation, windowVal, notLeft, member]
      have outsideFive : ∀ x ∈ before ++ after, valuation x = 5 := by
        intro x member
        have inBefore : x ∈ before := by simpa only [afterEmpty, List.append_nil] using member
        have notLeft : x ≠ left := by
          intro equal
          exact clear (List.mem_append.mpr (Or.inl (equal ▸ inBefore)))
        have notInside : x ∉ inside := fun present => separated x present member
        simp [valuation, windowVal, notLeft, notInside]
      have value : run valuation 5 whole = 3 := by
        rw [shape]
        apply window_final_value valuation before inside left
        · simp [valuation, windowVal]
        · exact fun x member => outsideFive x (List.mem_append.mpr (Or.inl member))
        · exact insideFour
      refine ⟨valuation, 5, ?_, insideFour, outsideFive, ?_⟩
      · rw [value]
        decide
      · intro x nonsimple
        apply windowVal_colors whole (some left) none inside ?_ ?_ x nonsimple
        · intro y equal
          simpa only [Option.some.inj equal] using leftSimple
        · intro y equal
          cases equal

theorem CanonicalWitness.block_nonsimple {whole alphabet : List Nat} {first : Slot}
    {rest : List Slot} (witness : CanonicalWitness whole alphabet first rest)
    (slot : Slot) (member : slot ∈ first :: rest) (x : Nat) (present : x ∈ slot.block) :
    whole.count x ≠ 1 := by
  obtain ⟨_, _, exactAlphabet, _, _, _, _, canonical, _⟩ := witness
  exact ((exactAlphabet x).mp ((canonical.1 slot member).bounded x present)).2

theorem CanonicalWitness.window_valuation {whole alphabet : List Nat} {first : Slot}
    {rest : List Slot} (witness : CanonicalWitness whole alphabet first rest)
    (before window after : List Slot) (shape : first :: rest = before ++ window ++ after)
    (windowNonempty : window ≠ []) (outside : before ≠ [] ∨ after ≠ [])
    (separated : ∀ inside ∈ window, ∀ out ∈ before ++ after, ∀ x ∈ inside.block, x ∉ out.block) :
    ∃ (valuation : Nat → Fin 6) (acc : Fin 6), run valuation acc whole ≠ 0 ∧
      (∀ slot ∈ window, ∀ x ∈ slot.block, valuation x = 4) ∧
      (∀ slot ∈ before ++ after, ∀ x ∈ slot.block, valuation x = 5) ∧
      (∀ x, whole.count x ≠ 1 → valuation x = 4 ∨ valuation x = 5) := by
  obtain ⟨regions⟩ := witness.boundary_regions before window after shape windowNonempty outside
  obtain ⟨valuation, acc, nonzero, insideFour, outsideFive, colors⟩ :=
    regions.form.separating_valuation (regions.disjoint separated)
  refine ⟨valuation, acc, nonzero, ?_, ?_, colors⟩
  · intro slot member x present
    have globalMember : slot ∈ first :: rest := by
      rw [shape]
      exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr member)))
    exact insideFour x ((regions.insideSupport x (witness.block_nonsimple slot globalMember x present)).mpr
      ⟨slot, member, present⟩)
  · intro slot member x present
    have globalMember : slot ∈ first :: rest := by
      rw [shape]
      rcases List.mem_append.mp member with inBefore | inAfter
      · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl inBefore)))
      · exact List.mem_append.mpr (Or.inr inAfter)
    exact outsideFive x ((regions.outsideSupport x (witness.block_nonsimple slot globalMember x present)).mpr
      ⟨slot, member, present⟩)

/-- A target canonical block cannot contain both a window letter and an outside
letter. All target colors follow from actual C7 count-one preservation. -/
theorem CanonicalWitness.excludes_target_window_mix {left right leftAlphabet rightAlphabet : List Nat}
    {leftFirst rightFirst : Slot} {leftRest rightRest : List Slot}
    (leftWitness : CanonicalWitness left leftAlphabet leftFirst leftRest)
    (rightWitness : CanonicalWitness right rightAlphabet rightFirst rightRest)
    (same : SameEval left right) (before window after : List Slot)
    (shape : leftFirst :: leftRest = before ++ window ++ after)
    (windowNonempty : window ≠ []) (outside : before ≠ [] ∨ after ≠ [])
    (separated : ∀ inside ∈ window, ∀ out ∈ before ++ after, ∀ x ∈ inside.block, x ∉ out.block)
    (target : Slot) (targetMember : target ∈ rightFirst :: rightRest)
    (x y : Nat) (xTarget : x ∈ target.block) (yTarget : y ∈ target.block)
    (xWindow : BlockMember window x) (yOutside : BlockMember (before ++ after) y) : False := by
  obtain ⟨valuation, acc, nonzero, insideFour, outsideFive, colors⟩ :=
    leftWitness.window_valuation before window after shape windowNonempty outside separated
  obtain ⟨front, back, targetShape⟩ := List.mem_iff_append.mp targetMember
  have rendered := rightWitness.2.2.2.2.2.2.2.2
  have rightShape : right = (render front ++ target.gap) ++ squareList target.block ++ render back := by
    rw [targetShape, render_append] at rendered
    simpa only [render, List.append_assoc] using rendered.symm
  have targetColors : ∀ letter ∈ target.block, valuation letter = 4 ∨ valuation letter = 5 := by
    intro letter member
    apply colors letter
    intro leftSimple
    exact rightWitness.block_nonsimple target targetMember letter member ((same.countOne letter).mp leftSimple)
  obtain ⟨inSlot, inMember, inBlock⟩ := xWindow
  obtain ⟨outSlot, outMember, outBlock⟩ := yOutside
  exact same.excludes_mixed_square valuation acc nonzero (render front ++ target.gap)
    target.block (render back) rightShape targetColors
    ⟨x, xTarget, insideFour inSlot inMember x inBlock⟩
    ⟨y, yTarget, outsideFive outSlot outMember y outBlock⟩

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.windowVal_colors
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.MarkerForm.separating_valuation
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.CanonicalWitness.block_nonsimple
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.CanonicalWitness.window_valuation
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.CanonicalWitness.excludes_target_window_mix

end SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
