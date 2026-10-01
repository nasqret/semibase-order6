import SemigroupBasis.CoRoots.Order6SporadicSection14Derivations
import SemigroupBasis.CoRoots.S5_870GapBlocks

namespace SemigroupBasis.CoRoots.Order6SporadicSection14

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_870

/-- Remove the retained later occurrence exactly when it is another copy of
the current first-occurrence marker. -/
def cleanCurrent (block : FirstOccurrenceGapBlock) : List Nat :=
  if keepLast block.seconds = [block.marker] then []
  else keepLast block.seconds

/-- Alpha form: clean every nonterminal block and leave the terminal block's
last later occurrence intact. -/
def renderAlphaCanonical : List FirstOccurrenceGapBlock → List Nat
  | [] => []
  | [block] => block.marker :: keepLast block.seconds
  | block :: next :: rest =>
      block.marker ::
        (cleanCurrent block ++ renderAlphaCanonical (next :: rest))

/-- Clean every block, including the terminal block. -/
def renderCleanCanonical : List FirstOccurrenceGapBlock → List Nat
  | [] => []
  | block :: rest =>
      block.marker :: (cleanCurrent block ++ renderCleanCanonical rest)

/-- Beta form agrees with the one-letter alpha extension, but cleans every
block as soon as at least two first-occurrence markers are present. -/
def renderBetaCanonical : List FirstOccurrenceGapBlock → List Nat
  | [] => []
  | [block] => block.marker :: keepLast block.seconds
  | block :: next :: rest => renderCleanCanonical (block :: next :: rest)

def alphaCanonicalList (letters : List Nat) : List Nat :=
  renderAlphaCanonical (gapBlocksList letters)

def betaCanonicalList (letters : List Nat) : List Nat :=
  renderBetaCanonical (gapBlocksList letters)

namespace Alpha

/-- Remove a repeated current marker when another block follows. -/
theorem listDerivesDropCurrentBeforeRest
    (stem : List Nat) (marker restHead : Nat) (restTail : List Nat) :
    ListDerives
      (stem ++ [marker, marker] ++ (restHead :: restTail))
      (stem ++ [marker] ++ (restHead :: restTail)) := by
  have base := S5_107.ListDerives.ofWord
    (derivesA (Word.singleton marker)
      (S5_107.listWordOfCons restHead restTail))
  simpa [S5_107.listWordOfCons, Word.singleton, Word.append,
    List.append_assoc] using base.prepend stem

private theorem listDerivesCleanCurrentBeforeRest
    (stem : List Nat) (block : FirstOccurrenceGapBlock)
    (restHead : Nat) (restTail : List Nat) :
    ListDerives
      (stem ++ [block.marker] ++ keepLast block.seconds ++
        (restHead :: restTail))
      (stem ++ [block.marker] ++ cleanCurrent block ++
        (restHead :: restTail)) := by
  by_cases current : keepLast block.seconds = [block.marker]
  · simpa [cleanCurrent, current, List.append_assoc] using
      listDerivesDropCurrentBeforeRest
        stem block.marker restHead restTail
  · simpa [cleanCurrent, current] using
      (S5_107.ListDerives.refl (basis := alphaBasis)
        (stem ++ [block.marker] ++ keepLast block.seconds ++
          (restHead :: restTail)))

/-- Normalize all parsed blocks to alpha form. -/
theorem listDerivesNormalizeBlocks
    {seen : List Nat} {blocks : List FirstOccurrenceGapBlock}
    (formed : GapBlocksWellFormed seen blocks)
    (stem : List Nat)
    (seenInPrefix : ∀ letter, letter ∈ seen → letter ∈ stem) :
    ListDerives
      (stem ++ renderGapBlocks blocks)
      (stem ++ renderAlphaCanonical blocks) := by
  induction formed generalizing stem with
  | nil =>
      simpa [renderGapBlocks, renderAlphaCanonical] using
        (S5_107.ListDerives.refl (basis := alphaBasis) stem)
  | cons seen block rest markerFresh secondsSeen tailFormed induction =>
      have currentSeen :
          ∀ letter, letter ∈ block.seconds →
            letter ∈ stem ++ [block.marker] := by
        intro letter member
        rcases List.mem_cons.mp (secondsSeen letter member) with
          atMarker | inSeen
        · subst letter
          simp
        · exact List.mem_append.mpr <| Or.inl <|
            seenInPrefix letter inSeen
      cases rest with
      | nil =>
          have current :=
            listDerivesKeepLastAfterSeen
              (stem ++ [block.marker]) block.seconds [] currentSeen
          simpa [renderGapBlocks, renderAlphaCanonical,
            List.append_assoc] using current
      | cons next tail =>
          have current :=
            listDerivesKeepLastAfterSeen
              (stem ++ [block.marker]) block.seconds
              (renderGapBlocks (next :: tail)) currentSeen
          have cleaned :=
            listDerivesCleanCurrentBeforeRest stem block next.marker
              (next.seconds ++ renderGapBlocks tail)
          have currentClean :
              ListDerives
                (stem ++ renderGapBlocks (block :: next :: tail))
                ((stem ++ [block.marker]) ++ cleanCurrent block ++
                  renderGapBlocks (next :: tail)) := by
            simpa [renderGapBlocks, List.append_assoc] using
              current.trans cleaned
          have nextSeenInPrefix :
              ∀ letter, letter ∈ block.marker :: seen →
                letter ∈
                  stem ++ [block.marker] ++ cleanCurrent block := by
            intro letter member
            rcases List.mem_cons.mp member with atMarker | inSeen
            · subst letter
              simp
            · exact List.mem_append.mpr <| Or.inl <|
                List.mem_append.mpr <| Or.inl <|
                  seenInPrefix letter inSeen
          have recurse :=
            induction
              (stem ++ [block.marker] ++ cleanCurrent block)
              nextSeenInPrefix
          have recurse' :
              ListDerives
                ((stem ++ [block.marker]) ++ cleanCurrent block ++
                  renderGapBlocks (next :: tail))
                ((stem ++ [block.marker]) ++ cleanCurrent block ++
                  renderAlphaCanonical (next :: tail)) := by
            simpa [List.append_assoc] using recurse
          simpa [renderGapBlocks, renderAlphaCanonical,
            List.append_assoc] using currentClean.trans recurse'

theorem listDerivesCanonicalList (letters : List Nat) :
    ListDerives letters (alphaCanonicalList letters) := by
  have normalized :=
    listDerivesNormalizeBlocks
      (gapBlocksList_wellFormed letters) [] (by simp)
  simpa [alphaCanonicalList, render_gapBlocksList] using normalized

end Alpha

namespace Beta

/-- Remove a repeated current marker when another block follows. -/
theorem listDerivesDropCurrentBeforeRest
    (stem : List Nat) (marker restHead : Nat) (restTail : List Nat) :
    ListDerives
      (stem ++ [marker, marker] ++ (restHead :: restTail))
      (stem ++ [marker] ++ (restHead :: restTail)) := by
  have base := S5_107.ListDerives.ofWord
    (derivesA (Word.singleton marker)
      (S5_107.listWordOfCons restHead restTail))
  simpa [S5_107.listWordOfCons, Word.singleton, Word.append,
    List.append_assoc] using base.prepend stem

/-- Remove the terminal repeated marker when a preceding canonical prefix is
present. This is the `xy² ≈ xy` step distinguishing beta from alpha form. -/
theorem listDerivesDropTerminalCurrent
    (prefixHead marker : Nat) (prefixTail : List Nat) :
    ListDerives
      ((prefixHead :: prefixTail) ++ [marker, marker])
      ((prefixHead :: prefixTail) ++ [marker]) := by
  have base := S5_107.ListDerives.ofWord
    (derivesB (S5_107.listWordOfCons prefixHead prefixTail)
      (Word.singleton marker))
  simpa [S5_107.listWordOfCons, Word.singleton, Word.append,
    List.append_assoc] using base

private theorem listDerivesCleanCurrentBeforeRest
    (stem : List Nat) (block : FirstOccurrenceGapBlock)
    (restHead : Nat) (restTail : List Nat) :
    ListDerives
      (stem ++ [block.marker] ++ keepLast block.seconds ++
        (restHead :: restTail))
      (stem ++ [block.marker] ++ cleanCurrent block ++
        (restHead :: restTail)) := by
  by_cases current : keepLast block.seconds = [block.marker]
  · simpa [cleanCurrent, current, List.append_assoc] using
      listDerivesDropCurrentBeforeRest
        stem block.marker restHead restTail
  · simpa [cleanCurrent, current] using
      (S5_107.ListDerives.refl (basis := betaBasis)
        (stem ++ [block.marker] ++ keepLast block.seconds ++
          (restHead :: restTail)))

private theorem listDerivesCleanTerminalCurrent
    (stem : List Nat) (prefixNonempty : stem ≠ [])
    (block : FirstOccurrenceGapBlock) :
    ListDerives
      (stem ++ [block.marker] ++ keepLast block.seconds)
      (stem ++ [block.marker] ++ cleanCurrent block) := by
  by_cases current : keepLast block.seconds = [block.marker]
  · cases stem with
    | nil => contradiction
    | cons prefixHead prefixTail =>
        simpa [cleanCurrent, current, List.append_assoc] using
          listDerivesDropTerminalCurrent
            prefixHead block.marker prefixTail
  · simpa [cleanCurrent, current] using
      (S5_107.ListDerives.refl (basis := betaBasis)
        (stem ++ [block.marker] ++ keepLast block.seconds))

/-- Normalize a noninitial suffix of blocks, cleaning the terminal block too.
The nonempty preceding prefix supplies the `x` in `xy² ≈ xy`. -/
theorem listDerivesNormalizeCleanBlocks
    {seen : List Nat} {blocks : List FirstOccurrenceGapBlock}
    (formed : GapBlocksWellFormed seen blocks)
    (stem : List Nat) (prefixNonempty : stem ≠ [])
    (seenInPrefix : ∀ letter, letter ∈ seen → letter ∈ stem) :
    ListDerives
      (stem ++ renderGapBlocks blocks)
      (stem ++ renderCleanCanonical blocks) := by
  induction formed generalizing stem with
  | nil =>
      simpa [renderGapBlocks, renderCleanCanonical] using
        (S5_107.ListDerives.refl (basis := betaBasis) stem)
  | cons seen block rest markerFresh secondsSeen tailFormed induction =>
      have currentSeen :
          ∀ letter, letter ∈ block.seconds →
            letter ∈ stem ++ [block.marker] := by
        intro letter member
        rcases List.mem_cons.mp (secondsSeen letter member) with
          atMarker | inSeen
        · subst letter
          simp
        · exact List.mem_append.mpr <| Or.inl <|
            seenInPrefix letter inSeen
      cases rest with
      | nil =>
          have current :=
            listDerivesKeepLastAfterSeen
              (stem ++ [block.marker]) block.seconds [] currentSeen
          have cleaned :=
            listDerivesCleanTerminalCurrent stem prefixNonempty block
          have cleaned' :
              ListDerives
                ((stem ++ [block.marker]) ++ keepLast block.seconds ++ [])
                ((stem ++ [block.marker]) ++ cleanCurrent block ++ []) := by
            simpa [List.append_assoc] using cleaned
          simpa [renderGapBlocks, renderCleanCanonical,
            List.append_assoc] using current.trans cleaned'
      | cons next tail =>
          have current :=
            listDerivesKeepLastAfterSeen
              (stem ++ [block.marker]) block.seconds
              (renderGapBlocks (next :: tail)) currentSeen
          have cleaned :=
            listDerivesCleanCurrentBeforeRest stem block next.marker
              (next.seconds ++ renderGapBlocks tail)
          let nextPrefix :=
            stem ++ [block.marker] ++ cleanCurrent block
          have currentClean :
              ListDerives
                (stem ++ renderGapBlocks (block :: next :: tail))
                (nextPrefix ++ renderGapBlocks (next :: tail)) := by
            simpa [renderGapBlocks, nextPrefix, List.append_assoc] using
              current.trans cleaned
          have nextPrefixNonempty : nextPrefix ≠ [] := by
            simp [nextPrefix]
          have nextSeenInPrefix :
              ∀ letter, letter ∈ block.marker :: seen →
                letter ∈ nextPrefix := by
            intro letter member
            rcases List.mem_cons.mp member with atMarker | inSeen
            · subst letter
              simp [nextPrefix]
            · exact List.mem_append.mpr <| Or.inl <|
                List.mem_append.mpr <| Or.inl <|
                  seenInPrefix letter inSeen
          have recurse :=
            induction nextPrefix nextPrefixNonempty nextSeenInPrefix
          have recurse' :
              ListDerives
                (nextPrefix ++ renderGapBlocks (next :: tail))
                (nextPrefix ++ renderCleanCanonical (next :: tail)) := by
            simpa [List.append_assoc] using recurse
          simpa [renderGapBlocks, renderCleanCanonical, nextPrefix,
            List.append_assoc] using currentClean.trans recurse'

/-- Normalize all parsed blocks to beta form. The single-marker extension is
kept at exponent one or two; with two or more markers every block is clean. -/
theorem listDerivesNormalizeBlocks
    {blocks : List FirstOccurrenceGapBlock}
    (formed : GapBlocksWellFormed [] blocks) :
    ListDerives
      (renderGapBlocks blocks)
      (renderBetaCanonical blocks) := by
  cases formed with
  | nil =>
      exact S5_107.ListDerives.refl []
  | cons _ block rest markerFresh secondsSeen tailFormed =>
      have currentSeen :
          ∀ letter, letter ∈ block.seconds → letter ∈ [block.marker] := by
        intro letter member
        simpa using secondsSeen letter member
      cases rest with
      | nil =>
          have current :=
            listDerivesKeepLastAfterSeen
              [block.marker] block.seconds [] currentSeen
          simpa [renderGapBlocks, renderBetaCanonical,
            List.append_assoc] using current
      | cons next tail =>
          have current :=
            listDerivesKeepLastAfterSeen
              [block.marker] block.seconds
              (renderGapBlocks (next :: tail)) currentSeen
          have cleaned :=
            listDerivesCleanCurrentBeforeRest [] block next.marker
              (next.seconds ++ renderGapBlocks tail)
          have currentClean := by
            simpa [renderGapBlocks, List.append_assoc] using
              current.trans cleaned
          let nextPrefix := [block.marker] ++ cleanCurrent block
          have nextPrefixNonempty : nextPrefix ≠ [] := by
            simp [nextPrefix]
          have nextSeenInPrefix :
              ∀ letter, letter ∈ [block.marker] → letter ∈ nextPrefix := by
            intro letter member
            change letter ∈ [block.marker] ++ cleanCurrent block
            exact List.mem_append.mpr (Or.inl member)
          have recurse :=
            listDerivesNormalizeCleanBlocks tailFormed
              nextPrefix nextPrefixNonempty nextSeenInPrefix
          simpa [renderGapBlocks, renderBetaCanonical,
            renderCleanCanonical, nextPrefix, List.append_assoc] using
              currentClean.trans recurse

theorem listDerivesCanonicalList (letters : List Nat) :
    ListDerives letters (betaCanonicalList letters) := by
  have normalized :=
    listDerivesNormalizeBlocks (gapBlocksList_wellFormed letters)
  simpa [betaCanonicalList, render_gapBlocksList] using normalized

end Beta

private def wordOfListOr (fallback : Nat) : List Nat → Word Nat
  | [] => Word.singleton fallback
  | head :: tail => ⟨head, tail⟩

private theorem word_toList_ne_nil (word : Word Nat) :
    word.toList ≠ [] := by
  cases word
  simp [Word.toList]

private theorem gapBlocksList_ne_nil (word : Word Nat) :
    gapBlocksList word.toList ≠ [] := by
  intro empty
  have rendered := render_gapBlocksList word.toList
  rw [empty] at rendered
  simp [renderGapBlocks] at rendered
  exact word_toList_ne_nil word rendered

theorem alphaCanonicalList_ne_nil (word : Word Nat) :
    alphaCanonicalList word.toList ≠ [] := by
  have blocksNonempty := gapBlocksList_ne_nil word
  cases blocks : gapBlocksList word.toList with
  | nil => contradiction
  | cons block rest =>
      cases rest with
      | nil => simp [alphaCanonicalList, blocks, renderAlphaCanonical]
      | cons next tail =>
          simp [alphaCanonicalList, blocks, renderAlphaCanonical]

theorem betaCanonicalList_ne_nil (word : Word Nat) :
    betaCanonicalList word.toList ≠ [] := by
  have blocksNonempty := gapBlocksList_ne_nil word
  cases blocks : gapBlocksList word.toList with
  | nil => contradiction
  | cons block rest =>
      cases rest with
      | nil => simp [betaCanonicalList, blocks, renderBetaCanonical]
      | cons next tail =>
          simp [betaCanonicalList, blocks, renderBetaCanonical,
            renderCleanCanonical]

private theorem toList_wordOfListOr_of_ne_nil
    (fallback : Nat) {letters : List Nat} (nonempty : letters ≠ []) :
    (wordOfListOr fallback letters).toList = letters := by
  cases letters with
  | nil => contradiction
  | cons head tail => rfl

def alphaCanonicalWord (word : Word Nat) : Word Nat :=
  wordOfListOr word.head (alphaCanonicalList word.toList)

def betaCanonicalWord (word : Word Nat) : Word Nat :=
  wordOfListOr word.head (betaCanonicalList word.toList)

theorem alphaCanonicalWord_toList (word : Word Nat) :
    (alphaCanonicalWord word).toList = alphaCanonicalList word.toList := by
  exact toList_wordOfListOr_of_ne_nil word.head
    (alphaCanonicalList_ne_nil word)

theorem betaCanonicalWord_toList (word : Word Nat) :
    (betaCanonicalWord word).toList = betaCanonicalList word.toList := by
  exact toList_wordOfListOr_of_ne_nil word.head
    (betaCanonicalList_ne_nil word)

private theorem derives_of_listDerives_toList
    {basisSet : List (Identity Nat)}
    (left right : Word Nat)
    (derivation :
      S5_107.ListDerives basisSet left.toList right.toList) :
    Derives basisSet left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simpa [S5_107.listWordOfCons] using
            S5_107.ListDerives.toWord derivation

theorem Alpha.derivesCanonicalWord (word : Word Nat) :
    Derives alphaBasis word (alphaCanonicalWord word) := by
  apply derives_of_listDerives_toList
  rw [alphaCanonicalWord_toList]
  exact Alpha.listDerivesCanonicalList word.toList

theorem Beta.derivesCanonicalWord (word : Word Nat) :
    Derives betaBasis word (betaCanonicalWord word) := by
  apply derives_of_listDerives_toList
  rw [betaCanonicalWord_toList]
  exact Beta.listDerivesCanonicalList word.toList

end SemigroupBasis.CoRoots.Order6SporadicSection14
