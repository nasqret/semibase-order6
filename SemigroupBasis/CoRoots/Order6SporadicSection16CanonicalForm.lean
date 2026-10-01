import SemigroupBasis.CoRoots.Order6SporadicSection16TokenAssembly

/-!
Lee and Zhang (2015), Lemma16.3: existence of a canonical form for every
nonsimple word. Distinctness of the complete label list makes the initial
prefix globally simple, separates it from the anchor/blocks, and prevents
different blocks from sharing a letter. Marker admissibility includes the
terminal boundary. This is normalization, not yet semantic uniqueness.
-/

namespace SemigroupBasis.CoRoots.Order6SporadicSection16

open SemigroupBasis

structure CanonicalData where
  initial : List Nat
  anchor : Nat
  blocks : List CanonicalBlock
deriving Repr, DecidableEq

def canonicalLabels (data : CanonicalData) : List Nat :=
  data.initial ++ [data.anchor] ++ data.blocks.map CanonicalBlock.letter

def renderCanonical (data : CanonicalData) : List Nat :=
  data.initial ++ [data.anchor, data.anchor] ++ renderBlocks data.anchor data.blocks

def CanonicalWellFormed (data : CanonicalData) : Prop :=
  (canonicalLabels data).Nodup ∧ AdmissibleMarkers data.blocks

/-- A word is either simple, or derives to an actual well-formed canonical
rendering whose labels all came from that word. The label bound is retained
through the induction, so adding an initial simple letter is justified. -/
theorem canonicalForm_cases (letters : List Nat) :
    letters.Nodup ∨ ∃ data : CanonicalData,
      CanonicalWellFormed data ∧ ListDerives letters (renderCanonical data) ∧
        (∀ x ∈ canonicalLabels data, x ∈ letters) := by
  induction letters with
  | nil => exact Or.inl (by simp)
  | cons letter rest ih =>
      by_cases again : letter ∈ rest
      · right
        let data : CanonicalData := ⟨[], letter, canonicalSuffix letter rest⟩
        have distinct := canonicalSuffix_distinct letter rest
        have labelsDistinct : (canonicalLabels data).Nodup := by
          simpa [data, canonicalLabels] using List.nodup_cons.mpr ⟨distinct.2, distinct.1⟩
        have wellFormed : CanonicalWellFormed data :=
          ⟨labelsDistinct, canonicalSuffix_admissible letter rest⟩
        have derivation : ListDerives (letter :: rest) (renderCanonical data) := by
          simpa [renderCanonical, data] using canonicalSuffix_derives letter rest again
        refine ⟨data, wellFormed, derivation, ?_⟩
        intro x member
        have bound : x = letter ∨ x ∈ (canonicalSuffix letter rest).map CanonicalBlock.letter := by
          simpa [canonicalLabels, data] using member
        rcases bound with equal | later
        · exact List.mem_cons.mpr (Or.inl equal)
        · exact List.mem_cons_of_mem letter (canonicalSuffix_letters_subset letter rest x later)
      · rcases ih with simple | ⟨data, wellFormed, derivation, labelsBound⟩
        · exact Or.inl (List.nodup_cons.mpr ⟨again, simple⟩)
        · right
          let extended : CanonicalData := { data with initial := letter :: data.initial }
          have fresh : letter ∉ canonicalLabels data := by
            intro member
            exact again (labelsBound letter member)
          have labelsDistinct : (canonicalLabels extended).Nodup := by
            simpa [canonicalLabels, extended] using List.nodup_cons.mpr ⟨fresh, wellFormed.1⟩
          have extendedWellFormed : CanonicalWellFormed extended := ⟨labelsDistinct, wellFormed.2⟩
          have extendedDerivation : ListDerives (letter :: rest) (renderCanonical extended) := by
            simpa [renderCanonical, extended] using derivation.prepend [letter]
          refine ⟨extended, extendedWellFormed, extendedDerivation, ?_⟩
          intro x member
          have split : x = letter ∨ x ∈ canonicalLabels data := by
            simpa [canonicalLabels, extended] using member
          rcases split with equal | old
          · exact List.mem_cons.mpr (Or.inl equal)
          · exact List.mem_cons_of_mem letter (labelsBound x old)

/-- The unrestricted normalization conclusion of Lemma16.3. -/
theorem existsCanonicalForm (letters : List Nat) (nonsimple : ¬ letters.Nodup) :
    ∃ data : CanonicalData, CanonicalWellFormed data ∧
      ListDerives letters (renderCanonical data) ∧
      (∀ x ∈ canonicalLabels data, x ∈ letters) := by
  rcases canonicalForm_cases letters with simple | canonical
  · exact False.elim (nonsimple simple)
  · exact canonical

theorem canonicalForm_nonempty (data : CanonicalData) : renderCanonical data ≠ [] := by
  simp [renderCanonical]

#print axioms canonicalForm_cases
#print axioms existsCanonicalForm

end SemigroupBasis.CoRoots.Order6SporadicSection16
