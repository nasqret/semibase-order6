import SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006SquareSkeleton

/-!
# Rank006: canonical separator skeletons with actual square roots

A tile stores an optional nonempty square root and an optional separator.
Its canonical quadratic labels are obtained from that root, so goodness
and the lower-calculus normalization are intrinsic to the representation.
Only adjacent squares are merged in Sigma+; no square is contracted to its
canonical double-list in Sigma+. The construction below applies to every
support-disjoint spine, hence every input word, without a bound.
-/

namespace SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006CanonicalTiles

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_107
open SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006SigmaPlus
open SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006PeriodMacros
open SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006SquaredReplay
open SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006BlockSpine
open SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006SquareSkeleton

structure Tile where
  root : Option (Word Nat)
  separator : Option Nat

def Tile.core (tile : Tile) : List Nat :=
  match tile.root with
  | none => []
  | some root => (square root).toList

def Tile.render (tile : Tile) : List Nat := tile.core ++ tile.separator.toList

noncomputable def Tile.quadratic (tile : Tile) : List Nat :=
  match tile.root with
  | none => []
  | some root => squareQuadratic root

noncomputable def Tile.shadow (tile : Tile) : UniqueSeparatorCanonicalSegment :=
  ⟨tile.quadratic, tile.separator⟩

noncomputable def shadows (tiles : List Tile) : List UniqueSeparatorCanonicalSegment :=
  tiles.map Tile.shadow

def tilesRender (tiles : List Tile) : List Nat := tiles.flatMap Tile.render

theorem Tile.quadratic_nodup (tile : Tile) : tile.quadratic.Nodup := by
  cases tile with
  | mk root separator =>
      cases root with
      | none => exact List.nodup_nil
      | some word => exact square_quadratic_nodup word

theorem Tile.quadratic_sorted (tile : Tile) : tile.quadratic.Pairwise (· ≤ ·) := by
  cases tile with
  | mk root separator =>
      cases root with
      | none => exact List.Pairwise.nil
      | some word => exact square_quadratic_sorted word

theorem Tile.quadratic_eq_nil_iff (tile : Tile) :
    tile.quadratic = [] ↔ tile.root = none := by
  cases tile with
  | mk root separator =>
      cases root with
      | none => simp [Tile.quadratic]
      | some word => simp [Tile.quadratic, square_quadratic_ne_nil]

theorem Tile.render_support (tile : Tile) (letter : Nat) :
    letter ∈ tile.render ↔ letter ∈ tile.shadow.labels := by
  cases tile with
  | mk root separator =>
      cases root <;>
        simp only [Tile.render, Tile.core, Tile.shadow, Tile.quadratic,
          UniqueSeparatorCanonicalSegment.labels, square, Word.toList_append,
          List.mem_append, or_self, square_quadratic_support]

theorem Tile.lower_derives (tile : Tile) :
    UniqueSeparatorListDerives tile.render tile.shadow.render := by
  cases tile with
  | mk root separator =>
      cases root with
      | none => exact UniqueSeparatorListDerives.refl _
      | some word =>
          simpa only [Tile.render, Tile.core, Tile.shadow, Tile.quadratic,
            UniqueSeparatorCanonicalSegment.render] using
            (square_derives_quadratic_lower word).append separator.toList

theorem tilesRender_support (tiles : List Tile) (letter : Nat) :
    letter ∈ tilesRender tiles ↔ letter ∈ uniqueSeparatorCanonicalLabels (shadows tiles) := by
  induction tiles with
  | nil => rfl
  | cons tile rest induction =>
      change letter ∈ tile.render ++ tilesRender rest ↔
        letter ∈ tile.shadow.labels ++ uniqueSeparatorCanonicalLabels (shadows rest)
      rw [List.mem_append, List.mem_append, Tile.render_support, induction]

theorem tiles_lower_derives (tiles : List Tile) :
    UniqueSeparatorListDerives (tilesRender tiles) (uniqueSeparatorCanonicalRender (shadows tiles)) := by
  induction tiles with
  | nil => exact UniqueSeparatorListDerives.empty
  | cons tile rest induction =>
      change UniqueSeparatorListDerives (tile.render ++ tilesRender rest)
        (tile.shadow.render ++ uniqueSeparatorCanonicalRender (shadows rest))
      exact (tile.lower_derives.append (tilesRender rest)).trans
        (induction.prepend tile.shadow.render)

theorem spine_to_tiles_support (blocks : List Block) (tiles : List Tile)
    (derivation : ListDerives sigmaPlus (render blocks) (tilesRender tiles)) (letter : Nat) :
    letter ∈ labels blocks ↔ letter ∈ uniqueSeparatorCanonicalLabels (shadows tiles) :=
  (render_support blocks letter).symm.trans
    ((listDerives_support derivation letter).trans (tilesRender_support tiles letter))

private theorem canonical_cons (segment : UniqueSeparatorCanonicalSegment)
    (rest : List UniqueSeparatorCanonicalSegment)
    (tailCanonical : UniqueSeparatorCanonical rest)
    (nodup : segment.labels.Nodup)
    (sorted : segment.quadratic.Pairwise (· ≤ ·))
    (terminal : segment.separator = none → rest = [])
    (nonempty : segment.quadratic = [] → segment.separator.isSome)
    (disjoint : ∀ letter, letter ∈ segment.labels →
      letter ∉ uniqueSeparatorCanonicalLabels rest) :
    UniqueSeparatorCanonical (segment :: rest) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (segment.labels ++ uniqueSeparatorCanonicalLabels rest).Nodup
    refine List.nodup_append.mpr ⟨nodup, tailCanonical.1, ?_⟩
    intro first inHead second inTail same
    subst second
    exact disjoint first inHead inTail
  · intro candidate member
    rcases List.mem_cons.mp member with same | inRest
    · subst candidate
      exact sorted
    · exact tailCanonical.2.1 candidate inRest
  · intro before candidate after split separatorNone
    cases before with
    | nil =>
        have parts := List.cons.inj split
        rcases parts with ⟨rfl, rfl⟩
        exact terminal separatorNone
    | cons first before =>
        have parts := List.cons.inj split
        exact tailCanonical.2.2.1 before candidate after parts.2 separatorNone
  · intro candidate member empty
    rcases List.mem_cons.mp member with same | inRest
    · subst candidate
      exact nonempty empty
    · exact tailCanonical.2.2.2 candidate inRest empty

/-- Merge adjacent squares, while leaving the actual root in every tile. -/
theorem canonicalize_spine (blocks : List Block) (separated : Separated blocks) :
    ∃ tiles : List Tile, UniqueSeparatorCanonical (shadows tiles) ∧
      ListDerives sigmaPlus (render blocks) (tilesRender tiles) := by
  cases blocks with
  | nil =>
      refine ⟨[], ?_, ListDerives.empty⟩
      simp [shadows, UniqueSeparatorCanonical, uniqueSeparatorCanonicalLabels]
  | cons block rest =>
      cases block with
      | single letter =>
          obtain ⟨tiles, canonical, derivation⟩ := canonicalize_spine rest separated.2
          let tile : Tile := ⟨none, some letter⟩
          refine ⟨tile :: tiles, ?_, ?_⟩
          · apply canonical_cons tile.shadow (shadows tiles) canonical
            · simp [tile, Tile.shadow, Tile.quadratic, UniqueSeparatorCanonicalSegment.labels]
            · exact tile.quadratic_sorted
            · simp [tile, Tile.shadow]
            · simp [tile, Tile.shadow]
            · intro tested inHead inTail
              have same : tested = letter := by
                simpa [tile, Tile.shadow, Tile.quadratic,
                  UniqueSeparatorCanonicalSegment.labels] using inHead
              subst tested
              exact separated.1 letter (by simp [Block.labels])
                ((spine_to_tiles_support rest tiles derivation letter).mpr inTail)
          · simpa only [render, tilesRender, List.flatMap_cons, Block.render,
              tile, Tile.render, Tile.core, Option.toList_some, List.nil_append] using
              derivation.prepend [letter]
      | squared word =>
          cases rest with
          | nil =>
              refine ⟨[⟨some word, none⟩], ?_, ?_⟩
              · exact square_quadratic_canonical word
              · simpa [render, Block.render, tilesRender, Tile.render, Tile.core] using
                  ListDerives.refl (basis := sigmaPlus) (square word).toList
          | cons next rest =>
              cases next with
              | single letter =>
                  obtain ⟨tiles, canonical, derivation⟩ := canonicalize_spine rest separated.2.2
                  let tile : Tile := ⟨some word, some letter⟩
                  have separatorAbsent : letter ∉ word.toList := by
                    intro member
                    exact separated.1 letter member (by simp [labels, Block.labels])
                  refine ⟨tile :: tiles, ?_, ?_⟩
                  · apply canonical_cons tile.shadow (shadows tiles) canonical
                    · change (squareQuadratic word ++ [letter]).Nodup
                      refine List.nodup_append.mpr ⟨square_quadratic_nodup word, by simp, ?_⟩
                      intro tested inQuadratic other inSingleton same
                      have otherSame : other = letter := List.mem_singleton.mp inSingleton
                      subst other
                      subst tested
                      exact separatorAbsent ((square_quadratic_support word letter).mp inQuadratic)
                    · exact tile.quadratic_sorted
                    · simp [tile, Tile.shadow]
                    · simp [tile, Tile.shadow]
                    · intro tested inHead inTail
                      have oldTail := (spine_to_tiles_support rest tiles derivation tested).mpr inTail
                      have member : tested ∈ squareQuadratic word ∨ tested = letter := by
                        simpa [tile, Tile.shadow, Tile.quadratic,
                          UniqueSeparatorCanonicalSegment.labels] using inHead
                      rcases member with inQuadratic | same
                      · exact separated.1 tested
                          ((square_quadratic_support word tested).mp inQuadratic)
                          (by simpa [labels, Block.labels] using Or.inr oldTail)
                      · subst tested
                        exact separated.2.1 letter (by simp [Block.labels]) oldTail
                  · simpa only [render, tilesRender, List.flatMap_cons, Block.render,
                      tile, Tile.render, Tile.core, Option.toList_some, List.append_assoc] using
                      derivation.prepend ((square word).toList ++ [letter])
              | squared other =>
                  have mergedSeparated : Separated (Block.squared (word ++ other) :: rest) := by
                    refine ⟨?_, separated.2.2⟩
                    intro tested member inRest
                    have cases : tested ∈ word.toList ∨ tested ∈ other.toList := by
                      simpa only [Block.labels, Word.toList_append, List.mem_append] using member
                    rcases cases with inFirst | inSecond
                    · exact separated.1 tested inFirst
                        (by simpa only [labels, List.flatMap_cons, Block.labels, List.mem_append] using
                          Or.inr inRest)
                    · exact separated.2.1 tested inSecond inRest
                  obtain ⟨tiles, canonical, derivation⟩ :=
                    canonicalize_spine (Block.squared (word ++ other) :: rest) mergedSeparated
                  refine ⟨tiles, canonical, ?_⟩
                  have merge : ListDerives sigmaPlus
                      (render (Block.squared word :: Block.squared other :: rest))
                      (render (Block.squared (word ++ other) :: rest)) := by
                    simpa only [render, List.flatMap_cons, Block.render,
                      Word.toList_append, List.append_assoc] using
                      (ListDerives.ofWord (derivesSquareAppend word other).symm).append (render rest)
                  exact merge.trans derivation
termination_by blocks.length
decreasing_by all_goals simp_all only [List.length_cons] <;> omega

theorem canonical_tiles_list (letters : List Nat) :
    ∃ tiles : List Tile, UniqueSeparatorCanonical (shadows tiles) ∧
      ListDerives sigmaPlus letters (tilesRender tiles) := by
  obtain ⟨blocks, separated, first⟩ := separated_normal_list letters
  obtain ⟨tiles, canonical, second⟩ := canonicalize_spine blocks separated
  exact ⟨tiles, canonical, first.trans second⟩

theorem canonical_tiles_word (word : Word Nat) :
    ∃ tiles : List Tile, UniqueSeparatorCanonical (shadows tiles) ∧
      tilesRender tiles ≠ [] ∧ ListDerives sigmaPlus word.toList (tilesRender tiles) := by
  obtain ⟨tiles, canonical, derivation⟩ := canonical_tiles_list word.toList
  exact ⟨tiles, canonical, ListDerives.target_ne_nil derivation, derivation⟩

end SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006CanonicalTiles
