import SemigroupBasis.CoRoots.S5_110Syntax
import SemigroupBasis.CoRoots.S5_213Normalization

namespace SemigroupBasis.CoRoots.S5_110Normalization

open SemigroupBasis
open SemigroupBasis.CoRoots

private abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives S5_110.basis

/-- Each S5_213 law follows from the stronger S5_110 basis. The power law is
S5_110's `x² = x³` with one copy appended; the gather laws are identical. -/
theorem derivesS5_213Axiom
    (identity : Identity Nat)
    (member : identity ∈ S5_213.basis) :
    Derives S5_110.basis identity.lhs identity.rhs := by
  simp only [S5_213.basis, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl
  next =>
    have appended :=
      Derives.appendRight
        (S5_110.derivesPowerExpansion (Word.singleton 0))
        (Word.singleton 0)
    simpa [S5_213.powerLaw, S5_213.xxx, S5_213.xxxx,
      Word.singleton, Word.append, Word.append_assoc] using appended
  next =>
    simpa [S5_213.leftGatherLaw, S5_213.xyx, S5_213.xxy,
      Word.singleton, Word.append, Word.append_assoc] using
      S5_110.derivesLeftFold
        (Word.singleton 0) (Word.singleton 1)
  next =>
    simpa [S5_213.rightGatherLaw, S5_213.xyx, S5_213.yxx,
      Word.singleton, Word.append, Word.append_assoc] using
      S5_110.derivesRightFold
        (Word.singleton 0) (Word.singleton 1)

/-- Transport the audited S5_213 canonical normalizer to the S5_110 basis. -/
theorem derivesS5_213Canonical (word : Word Nat) :
    Derives S5_110.basis word
      (S5_213Syntax.canonicalWord word) :=
  (S5_213Normalization.derivesCanonical word).transport
    derivesS5_213Axiom

/-- Contract one S5_213 double/triple block to an S5_110 double block. -/
theorem listDerivesRenderedBlockToDouble
    (word : Word Nat) (letter : Nat) :
    ListDerives
      (S5_213Syntax.renderRepeatedBlock word letter)
      (S5_110Syntax.renderRepeatedBlock letter) := by
  unfold S5_213Syntax.renderRepeatedBlock
  by_cases exactlyTwo : word.toList.count letter = 2
  · simp [exactlyTwo, S5_110Syntax.renderRepeatedBlock]
    exact S5_107.ListDerives.refl _
  · rw [if_neg exactlyTwo]
    exact S5_107.ListDerives.words <| by
      simpa [S5_110Syntax.renderRepeatedBlock,
        S5_107.listWordOfCons, Word.singleton, Word.append,
        Word.append_assoc] using
        (S5_110.derivesPowerExpansion
          (Word.singleton letter)).symm

/-- Contract every rendered triple block while retaining block order. -/
theorem listDerivesRenderedBlocksToDoubles
    (word : Word Nat) :
    ∀ letters : List Nat,
      ListDerives
        (letters.flatMap
          (S5_213Syntax.renderRepeatedBlock word))
        (letters.flatMap S5_110Syntax.renderRepeatedBlock)
  | [] => S5_107.ListDerives.empty
  | letter :: rest => by
      have headDerivation :=
        listDerivesRenderedBlockToDouble word letter
      have tailDerivation :=
        listDerivesRenderedBlocksToDoubles word rest
      exact
        (headDerivation.append
          (rest.flatMap
            (S5_213Syntax.renderRepeatedBlock word))).trans <| by
          simpa [S5_110Syntax.renderRepeatedBlock] using
            tailDerivation.prepend
              (S5_110Syntax.renderRepeatedBlock letter)

/-- The S5_213 canonical list contracts to the cap-two canonical list. -/
theorem listDerivesS5_213CanonicalToCanonical
    (word : Word Nat) :
    ListDerives
      (S5_213Syntax.canonicalList word)
      (S5_110Syntax.canonicalList word) := by
  have blocks :=
    listDerivesRenderedBlocksToDoubles word
      (S5_213Syntax.sortedRepeatedLetters word)
  have prefixed :=
    blocks.prepend (S5_213Syntax.singletonSequence word)
  simpa [S5_213Syntax.canonicalList,
    S5_110Syntax.canonicalList,
    S5_110Syntax.singletonSequence,
    S5_110Syntax.sortedRepeatedLetters] using prefixed

private theorem derivesS5_213CanonicalToCanonicalWord
    (word : Word Nat) :
    Derives S5_110.basis
      (S5_213Syntax.canonicalWord word)
      (S5_110Syntax.canonicalWord word) := by
  have listDerivation :=
    listDerivesS5_213CanonicalToCanonical word
  cases sourceShape : S5_213Syntax.canonicalList word with
  | nil =>
      exact False.elim <|
        S5_213Syntax.canonicalList_ne_nil word sourceShape
  | cons sourceHead sourceTail =>
      rw [sourceShape] at listDerivation
      obtain
          ⟨targetHead, targetTail,
            targetShape, wordDerivation⟩ :=
        S5_107.ListDerives.from_cons listDerivation
      have sourceWordEq :
          S5_107.listWordOfCons sourceHead sourceTail =
            S5_213Syntax.canonicalWord word := by
        apply Word.toList_injective
        rw [S5_213Syntax.toList_canonicalWord]
        simpa [S5_107.listWordOfCons, Word.toList] using
          sourceShape.symm
      have targetWordEq :
          S5_107.listWordOfCons targetHead targetTail =
            S5_110Syntax.canonicalWord word := by
        apply Word.toList_injective
        rw [S5_110Syntax.toList_canonicalWord]
        simpa [S5_107.listWordOfCons, Word.toList] using
          targetShape.symm
      rw [sourceWordEq, targetWordEq] at wordDerivation
      exact wordDerivation

/-- Every word derives to the cap-two canonical representative. -/
theorem derivesCanonical (word : Word Nat) :
    Derives S5_110.basis word
      (S5_110Syntax.canonicalWord word) :=
  (derivesS5_213Canonical word).trans
    (derivesS5_213CanonicalToCanonicalWord word)

/-- Canonical equality from the cap-two singleton-order signature. -/
theorem derives_of_sameSignature
    {left right : Word Nat}
    (same :
      S5_110Syntax.SameCappedSingletonSignature left right) :
    Derives S5_110.basis left right := by
  have leftCanonical := derivesCanonical left
  have rightCanonical := derivesCanonical right
  rw [same.canonicalWord_eq] at leftCanonical
  exact leftCanonical.trans rightCanonical.symm

end SemigroupBasis.CoRoots.S5_110Normalization
