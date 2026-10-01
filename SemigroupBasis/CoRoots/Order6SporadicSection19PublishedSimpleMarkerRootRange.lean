import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedRootFactorAnnihilation

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleMarkerRootRange

open CanonicalPresentation RootFactorAnnihilation

/-- A simple letter cannot occur in a root, by the actual nonsimple coverage
field of Form. No semantic simple-letter invariant is assumed or reproved. -/
theorem simple_marker_outside_root (word : Word Nat) (form : Form word)
    (marker : Nat) (simple : word.toList.count marker = 1)
    (root : Word Nat) (rootMember : root ∈ form.roots) : marker ∉ root.toList := by
  intro inRoot
  have repeated : 2 ≤ word.toList.count marker :=
    (form.coverage marker).mp ⟨root, rootMember, inRoot⟩
  rw [simple] at repeated
  omega

/-- An arbitrary supplied off-marker valuation is binary on every actual
root; the value of the simple marker itself is unrestricted. -/
theorem off_marker_root_binary (valuation : Nat → Fin 6) (word : Word Nat)
    (form : Form word) (marker : Nat) (simple : word.toList.count marker = 1)
    (offMarker : ∀ x, x ≠ marker → valuation x = 4 ∨ valuation x = 5)
    (root : Word Nat) (rootMember : root ∈ form.roots) :
    ∀ x ∈ root.toList, valuation x = 4 ∨ valuation x = 5 := by
  intro x member
  have outside := simple_marker_outside_root word form marker simple root rootMember
  exact offMarker x (fun equal => outside (equal ▸ member))

theorem simple_marker_mixed_root_zero (valuation : Nat → Fin 6) (word : Word Nat)
    (form : Form word) (marker : Nat) (simple : word.toList.count marker = 1)
    (offMarker : ∀ x, x ≠ marker → valuation x = 4 ∨ valuation x = 5)
    (root : Word Nat) (rootMember : root ∈ form.roots)
    (hasFour : ∃ x ∈ root.toList, valuation x = 4)
    (hasFive : ∃ x ∈ root.toList, valuation x = 5) :
    table.semigroup.eval valuation word = (0 : Fin 6) :=
  form_mixed_root_zero valuation word form root rootMember
    (off_marker_root_binary valuation word form marker simple offMarker root rootMember)
    hasFour hasFive

theorem simple_marker_nonzero_root_uniform (valuation : Nat → Fin 6) (word : Word Nat)
    (form : Form word) (marker : Nat) (simple : word.toList.count marker = 1)
    (offMarker : ∀ x, x ≠ marker → valuation x = 4 ∨ valuation x = 5)
    (root : Word Nat) (rootMember : root ∈ form.roots)
    (nonzero : table.semigroup.eval valuation word ≠ (0 : Fin 6)) :
    (∀ x ∈ root.toList, valuation x = 4) ∨
      (∀ x ∈ root.toList, valuation x = 5) :=
  form_nonzero_root_uniform valuation word form root rootMember
    (off_marker_root_binary valuation word form marker simple offMarker root rootMember) nonzero

/-- At a nonzero target evaluation, any two letters of the same actual root
receive the same value under an off-simple-marker valuation. -/
theorem simple_marker_root_values_agree (valuation : Nat → Fin 6) (word : Word Nat)
    (form : Form word) (marker : Nat) (simple : word.toList.count marker = 1)
    (offMarker : ∀ x, x ≠ marker → valuation x = 4 ∨ valuation x = 5)
    (root : Word Nat) (rootMember : root ∈ form.roots)
    (nonzero : table.semigroup.eval valuation word ≠ (0 : Fin 6))
    (x y : Nat) (inX : x ∈ root.toList) (inY : y ∈ root.toList) :
    valuation x = valuation y := by
  rcases simple_marker_nonzero_root_uniform valuation word form marker simple offMarker
      root rootMember nonzero with allFour | allFive
  · exact (allFour x inX).trans (allFour y inY).symm
  · exact (allFive x inX).trans (allFive y inY).symm

/-- This completes the target-side detector interface: root occurrence and
binary range are derived, while source nonzero and the mixed pair are explicit. -/
theorem simple_marker_split_root_separates (valuation : Nat → Fin 6)
    (source target : Word Nat) (form : Form target) (marker : Nat)
    (simple : target.toList.count marker = 1)
    (offMarker : ∀ x, x ≠ marker → valuation x = 4 ∨ valuation x = 5)
    (root : Word Nat) (rootMember : root ∈ form.roots)
    (x y : Nat) (inX : x ∈ root.toList) (inY : y ∈ root.toList)
    (valueX : valuation x = 4) (valueY : valuation y = 5)
    (sourceNonzero : table.semigroup.eval valuation source ≠ (0 : Fin 6)) :
    table.semigroup.eval valuation source ≠ table.semigroup.eval valuation target :=
  form_mixed_root_separates valuation source target form root rootMember
    (off_marker_root_binary valuation target form marker simple offMarker root rootMember)
    ⟨x, inX, valueX⟩ ⟨y, inY, valueY⟩ sourceNonzero

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleMarkerRootRange

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleMarkerRootRange.simple_marker_outside_root
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleMarkerRootRange.off_marker_root_binary
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleMarkerRootRange.simple_marker_mixed_root_zero
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleMarkerRootRange.simple_marker_nonzero_root_uniform
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleMarkerRootRange.simple_marker_root_values_agree
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleMarkerRootRange.simple_marker_split_root_separates
