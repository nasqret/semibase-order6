import SemigroupBasis.CoRoots.Order6Hull21_1ProfileCountNormalization

/-!
# Hull 21.1 boundary-anchor insertion

This module isolates the exceptional step needed before the right-to-left
Lee--Zhang gap sweep.  When two copies of the distinguished anchor already
occur in the fixed stem, a further copy can be inserted immediately before a
nonempty witnessed debt.

The proof creates a square of the first debt letter, applies Proposition
21.1(b) backwards, permutes the resulting three-letter witnessed tail, and
contracts the square again.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis
namespace CoRoots
namespace Order6Hull21_1BoundaryAnchor

open SemigroupBasis.CoRoots.Order6Hull21_1ProfileCountNormalization

abbrev HullListDerives : List Nat → List Nat → Prop :=
  SemigroupBasis.CoRoots.Order6Hull21_1JointCompleteness.HullListDerives

/-- Insert an anchor immediately before a nonempty debt when the stem already
contains two anchor occurrences and witnesses every debt letter. -/
theorem hullListDerivesInsertBoundaryAnchor
    (stem debt suffix : List Nat)
    (before between after : List Nat)
    (anchor : Nat)
    (stemShape :
      stem =
        before ++ [anchor] ++ between ++ [anchor] ++ after)
    (debtNonempty : debt ≠ [])
    (debtWitnessed :
      ∀ letter, letter ∈ debt → letter ∈ stem) :
    HullListDerives
      (stem ++ debt ++ suffix)
      (stem ++ [anchor] ++ debt ++ suffix) := by
  cases debt with
  | nil =>
      exact False.elim (debtNonempty rfl)
  | cons first rest =>
      have firstWitness : first ∈ stem :=
        debtWitnessed first (List.Mem.head rest)
      have anchorWitness : anchor ∈ stem := by
        rw [stemShape]
        simp
      have expandFirst :
          HullListDerives
            (stem ++ (first :: rest) ++ suffix)
            (stem ++ [first, first] ++ rest ++ suffix) := by
        simpa [List.append_assoc] using
          (hullListDerivesContractAfterWitness
            stem (rest ++ suffix) first firstWitness).symm
      have appendAnchor :
          HullListDerives
            (stem ++ [first, first] ++ rest ++ suffix)
            (stem ++ [first, first, anchor] ++ rest ++ suffix) := by
        rw [stemShape]
        simpa [List.append_assoc] using
          (SemigroupBasis.CoRoots.Order6Hull21_1JointCompleteness.hullListDerivesTerminalContract
            before (rest ++ suffix) between after anchor first).symm
      have tailWitnessed :
          ∀ letter, letter ∈ [first, first, anchor] →
            letter ∈ stem := by
        intro letter member
        simp only [List.mem_cons] at member
        rcases member with atFirst | atFirst | atAnchor
        · subst letter
          exact firstWitness
        · subst letter
          exact firstWitness
        · rcases atAnchor with atAnchor | impossible
          · subst letter
            exact anchorWitness
          · simp at impossible
      have tailPermutation :
          [first, first, anchor].Perm [anchor, first, first] := by
        exact
          (List.Perm.cons first
            (List.Perm.swap anchor first [])).trans
            (List.Perm.swap first anchor [first]).symm
      have moveAnchor :
          HullListDerives
            (stem ++ [first, first, anchor] ++ rest ++ suffix)
            (stem ++ [anchor, first, first] ++ rest ++ suffix) := by
        simpa [List.append_assoc] using
          hullListDerivesPermuteAfterWitnesses
            stem (rest ++ suffix) tailWitnessed tailPermutation
      have contractFirst :
          HullListDerives
            (stem ++ [anchor, first, first] ++ rest ++ suffix)
            (stem ++ [anchor, first] ++ rest ++ suffix) := by
        have firstWitness' : first ∈ stem ++ [anchor] :=
          List.mem_append.mpr (Or.inl firstWitness)
        simpa [List.append_assoc] using
          hullListDerivesContractAfterWitness
            (stem ++ [anchor]) (rest ++ suffix)
            first firstWitness'
      simpa [List.append_assoc] using
        expandFirst.trans <|
          appendAnchor.trans <|
            moveAnchor.trans contractFirst

/-- Prepare the boundary anchor used by the forward gap sweep.

If the final debt already contains the anchor, witnessed-support
normalization duplicates that occurrence at the boundary.  Otherwise the
caller supplies the two earlier anchor occurrences needed by
`hullListDerivesInsertBoundaryAnchor`. -/
theorem hullListDerivesPrepareBoundaryAnchor
    (stem debt suffix : List Nat)
    (anchor : Nat)
    (debtNonempty : debt ≠ [])
    (debtWitnessed :
      ∀ letter, letter ∈ debt → letter ∈ stem)
    (anchorAvailable :
      anchor ∈ debt ∨
        ∃ before between after,
          stem =
            before ++ [anchor] ++ between ++ [anchor] ++ after) :
    HullListDerives
      (stem ++ debt ++ suffix)
      (stem ++ [anchor] ++ debt ++ suffix) := by
  rcases anchorAvailable with inDebt | ⟨before, between, after, stemShape⟩
  · have targetWitnessed :
        ∀ letter, letter ∈ anchor :: debt → letter ∈ stem := by
      intro letter member
      rcases List.mem_cons.mp member with atAnchor | inTail
      · subst letter
        exact debtWitnessed anchor inDebt
      · exact debtWitnessed letter inTail
    have sameSupport :
        ∀ letter, letter ∈ debt ↔ letter ∈ anchor :: debt := by
      intro letter
      constructor
      · exact List.Mem.tail anchor
      · intro member
        rcases List.mem_cons.mp member with atAnchor | inTail
        · simpa [atAnchor] using inDebt
        · exact inTail
    simpa [List.append_assoc] using
      (hullListDerivesOfSameSupportAfterWitnesses
        stem suffix debt (anchor :: debt)
        debtWitnessed targetWitnessed sameSupport)
  · exact
      hullListDerivesInsertBoundaryAnchor
        stem debt suffix before between after anchor
        stemShape debtNonempty debtWitnessed

end Order6Hull21_1BoundaryAnchor
end CoRoots
end SemigroupBasis
