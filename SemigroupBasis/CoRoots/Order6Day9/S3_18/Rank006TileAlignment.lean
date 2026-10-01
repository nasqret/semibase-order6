import SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006CanonicalTiles

/-!
# Rank006: residue alignment over a common canonical separator skeleton

Global label disjointness makes the residue of each tile visible in the
whole rendered word. Equal separators cancel in natural-number count
data; multiplication by two is invertible modulo three. The squared
converse then compares actual roots. No derivation is cancelled and no
globally commutative rewrite or lower-factor retargeting is used.
-/

namespace SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006TileAlignment

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_107
open SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006SigmaPlus
open SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006PeriodMacros
open SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006SquaredReplay
open SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006SquareSkeleton
open SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006CanonicalTiles

theorem tile_derives_of_shadow_mod (left right : Tile)
    (same : left.shadow = right.shadow)
    (residues : ∀ letter,
      left.render.count letter % 3 = right.render.count letter % 3) :
    ListDerives sigmaPlus left.render right.render := by
  cases left with
  | mk leftRoot leftSeparator =>
      cases right with
      | mk rightRoot rightSeparator =>
          have separatorSame := congrArg UniqueSeparatorCanonicalSegment.separator same
          change leftSeparator = rightSeparator at separatorSame
          subst rightSeparator
          have quadraticSame := congrArg UniqueSeparatorCanonicalSegment.quadratic same
          cases leftRoot with
          | none =>
              cases rightRoot with
              | none => exact ListDerives.refl _
              | some rightWord =>
                  change [] = squareQuadratic rightWord at quadraticSame
                  exact False.elim (square_quadratic_ne_nil rightWord quadraticSame.symm)
          | some leftWord =>
              cases rightRoot with
              | none =>
                  change squareQuadratic leftWord = [] at quadraticSame
                  exact False.elim (square_quadratic_ne_nil leftWord quadraticSame)
              | some rightWord =>
                  change squareQuadratic leftWord = squareQuadratic rightWord at quadraticSame
                  have support : ∀ letter,
                      letter ∈ leftWord.toList ↔ letter ∈ rightWord.toList := by
                    intro letter
                    rw [← square_quadratic_support leftWord,
                      ← square_quadratic_support rightWord, quadraticSame]
                  have rootResidues : ∀ letter,
                      leftWord.toList.count letter % 3 = rightWord.toList.count letter % 3 := by
                    intro letter
                    have total := residues letter
                    simp only [Tile.render, Tile.core, square, Word.toList_append,
                      List.count_append] at total
                    omega
                  have squares := derivesSquaresOfSupportMod leftWord rightWord support rootResidues
                  exact (ListDerives.ofWord squares).append leftSeparator.toList

theorem tile_count_zero_of_not_label (tile : Tile) (letter : Nat)
    (absent : letter ∉ tile.shadow.labels) : tile.render.count letter = 0 :=
  List.count_eq_zero.mpr (fun member => absent ((tile.render_support letter).mp member))

theorem tiles_count_zero_of_not_label (tiles : List Tile) (letter : Nat)
    (absent : letter ∉ uniqueSeparatorCanonicalLabels (shadows tiles)) :
    (tilesRender tiles).count letter = 0 :=
  List.count_eq_zero.mpr (fun member => absent ((tilesRender_support tiles letter).mp member))

/-- Two good realizations of one canonical skeleton are compared tile by
tile using only their total residues and the existing squared converse. -/
theorem tiles_derives_of_shadow_mod (left right : List Tile)
    (leftCanonical : UniqueSeparatorCanonical (shadows left))
    (rightCanonical : UniqueSeparatorCanonical (shadows right))
    (same : shadows left = shadows right)
    (residues : ∀ letter,
      (tilesRender left).count letter % 3 = (tilesRender right).count letter % 3) :
    ListDerives sigmaPlus (tilesRender left) (tilesRender right) := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => exact ListDerives.empty
      | cons tile rest => simp [shadows] at same
  | cons first leftRest induction =>
      cases right with
      | nil => simp [shadows] at same
      | cons second rightRest =>
          change first.shadow :: shadows leftRest = second.shadow :: shadows rightRest at same
          have parts := List.cons.inj same
          have disjoint := uniqueSeparatorCanonical_firstLabels_disjoint leftCanonical
          have headResidues : ∀ letter,
              first.render.count letter % 3 = second.render.count letter % 3 := by
            intro letter
            by_cases member : letter ∈ first.shadow.labels
            · have leftZero := tiles_count_zero_of_not_label leftRest letter (disjoint letter member)
              have rightAbsent : letter ∉ uniqueSeparatorCanonicalLabels (shadows rightRest) := by
                rw [← parts.2]
                exact disjoint letter member
              have rightZero := tiles_count_zero_of_not_label rightRest letter rightAbsent
              have total := residues letter
              change (first.render ++ tilesRender leftRest).count letter % 3 =
                (second.render ++ tilesRender rightRest).count letter % 3 at total
              simpa only [List.count_append, leftZero, rightZero, Nat.add_zero] using total
            · have rightAbsent : letter ∉ second.shadow.labels := by
                rw [← parts.1]
                exact member
              rw [tile_count_zero_of_not_label first letter member,
                tile_count_zero_of_not_label second letter rightAbsent]
          have tailResidues : ∀ letter,
              (tilesRender leftRest).count letter % 3 =
                (tilesRender rightRest).count letter % 3 := by
            intro letter
            have total := residues letter
            have headEqual := headResidues letter
            change (first.render ++ tilesRender leftRest).count letter % 3 =
              (second.render ++ tilesRender rightRest).count letter % 3 at total
            simp only [List.count_append] at total
            omega
          have headDerivation := tile_derives_of_shadow_mod first second parts.1 headResidues
          have tailDerivation := induction rightRest
            (uniqueSeparatorCanonical_tail leftCanonical)
            (uniqueSeparatorCanonical_tail rightCanonical) parts.2 tailResidues
          change ListDerives sigmaPlus (first.render ++ tilesRender leftRest)
            (second.render ++ tilesRender rightRest)
          exact (headDerivation.append (tilesRender leftRest)).trans
            (tailDerivation.prepend second.render)

end SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006TileAlignment
