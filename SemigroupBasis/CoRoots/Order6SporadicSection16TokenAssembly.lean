import SemigroupBasis.CoRoots.Order6SporadicSection16TypedSkeleton

/-!
Typed assembly of the Section16 skeleton into the published block rendering.
Leading and repeated anchor markers are handled by derived contractions;
neither equality of the two representations nor canonical distinctness is
assumed. Reference: Lee and Zhang (2015), Lemma16.3, pp.50-51.
-/

namespace SemigroupBasis.CoRoots.Order6SporadicSection16

open SemigroupBasis

def parseTokens : List SkeletonToken → Bool × List CanonicalBlock
  | [] => (false, [])
  | .marker :: tail => (true, (parseTokens tail).2)
  | .letter value doubled :: tail =>
      (false, ⟨value, doubled, (parseTokens tail).1⟩ :: (parseTokens tail).2)

def renderParsed (anchor : Nat) (parsed : Bool × List CanonicalBlock) : List Nat :=
  (if parsed.1 then [anchor, anchor] else []) ++ renderBlocks anchor parsed.2

theorem parseTokens_letters (tokens : List SkeletonToken) :
    (parseTokens tokens).2.map CanonicalBlock.letter = tokenLetters tokens := by
  induction tokens with
  | nil => rfl
  | cons head tail ih => cases head <;> simp [parseTokens, tokenLetters, ih]

private theorem anchorFourthPower (anchor : Nat) :
    ListDerives [anchor, anchor, anchor, anchor] [anchor, anchor] := by
  have first : ListDerives [anchor, anchor, anchor, anchor] [anchor, anchor, anchor] :=
    (listPower anchor).append [anchor]
  exact first.trans (listPower anchor)

/-- Parsing combines consecutive markers only through a proved fourth-power
contraction. It is a derivation, not an unjustified equality of raw lists. -/
theorem parseTokens_derives (anchor : Nat) (tokens : List SkeletonToken) :
    ListDerives (renderTokens anchor tokens) (renderParsed anchor (parseTokens tokens)) := by
  induction tokens with
  | nil => exact S5_107.ListDerives.empty
  | cons head tail ih =>
      cases head with
      | marker =>
          have prefixed := ih.prepend [anchor, anchor]
          cases parsed : parseTokens tail with
          | mk leading blocks =>
              cases leading with
              | false =>
                  simpa [renderTokens, renderToken, renderParsed, parseTokens, parsed] using prefixed
              | true =>
                  have first : ListDerives ([anchor, anchor] ++ renderTokens anchor tail)
                      ([anchor, anchor, anchor, anchor] ++ renderBlocks anchor blocks) := by
                    simpa [renderParsed, parsed, List.append_assoc] using prefixed
                  have second := (anchorFourthPower anchor).append (renderBlocks anchor blocks)
                  simpa [renderTokens, renderToken, parseTokens, parsed, renderParsed] using first.trans second
      | letter value doubled =>
          have prefixed := ih.prepend (renderToken anchor (.letter value doubled))
          simpa [renderTokens, renderToken, parseTokens, renderParsed, renderBlocks,
            renderBlock, List.append_assoc] using prefixed

theorem pruneSeparators_letters (blocks : List CanonicalBlock) :
    (pruneSeparators blocks).map CanonicalBlock.letter = blocks.map CanonicalBlock.letter := by
  induction blocks with
  | nil => rfl
  | cons head tail ih => simp [pruneSeparators, pruneHead, ih]

def canonicalTokens (tokens : List SkeletonToken) : List CanonicalBlock :=
  pruneSeparators (parseTokens tokens).2

theorem canonicalTokens_letters (tokens : List SkeletonToken) :
    (canonicalTokens tokens).map CanonicalBlock.letter = tokenLetters tokens := by
  rw [canonicalTokens, pruneSeparators_letters, parseTokens_letters]

theorem canonicalTokens_distinct {anchor : Nat} {tokens : List SkeletonToken}
    (wellFormed : TokensWellFormed anchor tokens) :
    ((canonicalTokens tokens).map CanonicalBlock.letter).Nodup ∧
      anchor ∉ (canonicalTokens tokens).map CanonicalBlock.letter := by
  simpa [canonicalTokens_letters, TokensWellFormed] using wellFormed

theorem canonicalTokens_admissible (tokens : List SkeletonToken) :
    AdmissibleMarkers (canonicalTokens tokens) :=
  pruneSeparators_admissible (parseTokens tokens).2

/-- Complete assembly of token parsing, leading-marker contraction and
separator pruning behind the protected initial anchor square. -/
theorem anchoredTokens_derives (anchor : Nat) (tokens : List SkeletonToken) :
    ListDerives ([anchor, anchor] ++ renderTokens anchor tokens)
      ([anchor, anchor] ++ renderBlocks anchor (canonicalTokens tokens)) := by
  have parsed := (parseTokens_derives anchor tokens).prepend [anchor, anchor]
  cases shape : parseTokens tokens with
  | mk leading blocks =>
      have removeLeading :
          ListDerives ([anchor, anchor] ++ renderParsed anchor (leading, blocks))
            ([anchor, anchor] ++ renderBlocks anchor blocks) := by
        cases leading with
        | false => exact S5_107.ListDerives.refl _
        | true =>
            simpa [renderParsed] using (anchorFourthPower anchor).append (renderBlocks anchor blocks)
      have first : ListDerives ([anchor, anchor] ++ renderTokens anchor tokens)
          ([anchor, anchor] ++ renderBlocks anchor blocks) := by
        have parsedStep : ListDerives ([anchor, anchor] ++ renderTokens anchor tokens)
            ([anchor, anchor] ++ renderParsed anchor (leading, blocks)) := by
          simpa [shape] using parsed
        exact parsedStep.trans removeLeading
      have second : ListDerives ([anchor, anchor] ++ renderBlocks anchor blocks)
          ([anchor, anchor] ++ renderBlocks anchor (pruneSeparators blocks)) := by
        simpa using pruneSeparators_derives anchor [] blocks
      simpa [canonicalTokens, shape] using first.trans second

def canonicalSuffix (anchor : Nat) (rest : List Nat) : List CanonicalBlock :=
  canonicalTokens (skeletonTokens anchor rest)

theorem canonicalSuffix_distinct (anchor : Nat) (rest : List Nat) :
    ((canonicalSuffix anchor rest).map CanonicalBlock.letter).Nodup ∧
      anchor ∉ (canonicalSuffix anchor rest).map CanonicalBlock.letter :=
  canonicalTokens_distinct (skeletonTokens_wellFormed anchor rest)

theorem canonicalSuffix_admissible (anchor : Nat) (rest : List Nat) :
    AdmissibleMarkers (canonicalSuffix anchor rest) :=
  canonicalTokens_admissible (skeletonTokens anchor rest)

theorem canonicalSuffix_letters_subset (anchor : Nat) (rest : List Nat) :
    ∀ x ∈ (canonicalSuffix anchor rest).map CanonicalBlock.letter, x ∈ rest := by
  intro x member
  rw [canonicalSuffix, canonicalTokens_letters] at member
  exact skeletonTokens_letters_subset anchor rest x member

/-- Actual canonical-block derivation for a word beginning with a nonsimple
letter. This composes the old all-word scanner theorem with the new typed
representation, rather than assuming its shape. -/
theorem canonicalSuffix_derives (anchor : Nat) (rest : List Nat) (again : anchor ∈ rest) :
    ListDerives (anchor :: rest)
      ([anchor, anchor] ++ renderBlocks anchor (canonicalSuffix anchor rest)) := by
  have scanned : ListDerives (anchor :: rest)
      ([anchor, anchor] ++ normalizeAux anchor [] [] rest) := by
    simpa [normalizeSkeleton, again] using normalizeSkeleton_derives (anchor :: rest)
  have assembled := anchoredTokens_derives anchor (skeletonTokens anchor rest)
  rw [skeletonTokens_render] at assembled
  exact scanned.trans assembled

#print axioms parseTokens_derives
#print axioms anchoredTokens_derives
#print axioms canonicalSuffix_distinct
#print axioms canonicalSuffix_admissible
#print axioms canonicalSuffix_derives

end SemigroupBasis.CoRoots.Order6SporadicSection16
