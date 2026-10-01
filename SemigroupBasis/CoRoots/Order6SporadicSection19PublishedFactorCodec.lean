import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedUnionPerfection

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorCodec

open MaximalFactors FactorBoundaries CanonicalSquareCover BlockAlignment
  OccurrenceMacro SeparatorSkeleton UnionPerfection

theorem decompose_word_nonempty (classify : Nat → Bool) (piece : Word Nat) :
    decompose classify piece.toList ≠ [] := by
  intro empty
  have covered := flatten_decompose classify piece.toList
  rw [empty] at covered
  exact piece_nonempty piece covered.symm

/-- Every literal factor has a nonempty code, even without perfection. -/
theorem encodeFactor_nonempty (leftRoot rightRoot factor : Word Nat) :
    encodeFactor leftRoot rightRoot factor ≠ [] := by
  by_cases positive : unionTag (supportTag leftRoot) (supportTag rightRoot) factor.head = true
  · rw [encodeFactor, if_pos positive]
    intro empty
    change (decompose (supportTag leftRoot) factor.toList).map
      (blockCode (supportTag leftRoot)) = [] at empty
    exact decompose_word_nonempty (supportTag leftRoot) factor
      (List.eq_nil_of_map_eq_nil empty)
  · rw [encodeFactor, if_neg positive]
    intro empty
    exact piece_nonempty factor (List.eq_nil_of_map_eq_nil empty)

def encodedWord (leftRoot rightRoot factor : Word Nat) : Word Nat :=
  nonemptyWord (encodeFactor leftRoot rightRoot factor)
    (encodeFactor_nonempty leftRoot rightRoot factor)

theorem encodedWord_toList (leftRoot rightRoot factor : Word Nat) :
    (encodedWord leftRoot rightRoot factor).toList =
      encodeFactor leftRoot rightRoot factor :=
  nonemptyWord_toList _ _

theorem encodeFactor_tag (leftRoot rightRoot factor : Word Nat) (code : Nat)
    (member : code ∈ encodeFactor leftRoot rightRoot factor) :
    binaryTag 0 1 code = unionTag (supportTag leftRoot) (supportTag rightRoot) factor.head := by
  by_cases positive : unionTag (supportTag leftRoot) (supportTag rightRoot) factor.head = true
  · rw [encodeFactor, if_pos positive] at member
    change code ∈ (decompose (supportTag leftRoot) factor.toList).map
      (blockCode (supportTag leftRoot)) at member
    obtain ⟨block, _, equal⟩ := List.mem_map.mp member
    rw [← equal, positive]
    exact blockCode_positive (supportTag leftRoot) block
  · rw [encodeFactor, if_neg positive] at member
    obtain ⟨letter, _, equal⟩ := List.mem_map.mp member
    have negative : binaryTag 0 1 (letter + 2) = false := by
      apply false_of_ne_true
      intro tag
      rcases (binaryTag_true 0 1 (letter + 2)).mp tag with zero | one
      · omega
      · omega
    rw [← equal]
    exact negative.trans (false_of_ne_true _ positive).symm

theorem encodedWord_head_tag (leftRoot rightRoot factor : Word Nat) :
    binaryTag 0 1 (encodedWord leftRoot rightRoot factor).head =
      unionTag (supportTag leftRoot) (supportTag rightRoot) factor.head := by
  apply encodeFactor_tag
  rw [← encodedWord_toList]
  exact word_head_member _

theorem encodedWord_constant (leftRoot rightRoot factor : Word Nat) :
    Constant (binaryTag 0 1) (encodedWord leftRoot rightRoot factor) := by
  intro code member
  rw [encodedWord_toList] at member
  exact (encodeFactor_tag leftRoot rightRoot factor code member).trans
    (encodedWord_head_tag leftRoot rightRoot factor).symm

theorem encoded_good (leftRoot rightRoot : Word Nat) (pieces : List (Word Nat))
    (good : Good (unionTag (supportTag leftRoot) (supportTag rightRoot)) pieces) :
    Good (binaryTag 0 1) (pieces.map (encodedWord leftRoot rightRoot)) := by
  induction good with
  | nil => exact Good.nil
  | last uniform => exact Good.last (encodedWord_constant leftRoot rightRoot _)
  | step uniform different tailGood ih =>
      exact Good.step (encodedWord_constant leftRoot rightRoot _)
        (by simpa only [encodedWord_head_tag] using different) ih

theorem flatten_encoded (leftRoot rightRoot : Word Nat) (pieces : List (Word Nat)) :
    flatten (pieces.map (encodedWord leftRoot rightRoot)) =
      encodePieces leftRoot rightRoot pieces := by
  induction pieces with
  | nil => rfl
  | cons first rest ih =>
      change (encodedWord leftRoot rightRoot first).toList ++
        flatten (rest.map (encodedWord leftRoot rightRoot)) =
          encodeFactor leftRoot rightRoot first ++ encodePieces leftRoot rightRoot rest
      rw [encodedWord_toList, ih]

/-- Exact ordered maximal factors of the ACTUAL macro encoder. No decoder
compatibility, perfection, disjointness or rendering equation is assumed. -/
theorem decompose_macroLetters (leftRoot rightRoot word : Word Nat) :
    decompose (binaryTag 0 1) (macroLetters leftRoot rightRoot word) =
      (decompose (unionTag (supportTag leftRoot) (supportTag rightRoot)) word.toList).map
        (encodedWord leftRoot rightRoot) := by
  let pieces := decompose (unionTag (supportTag leftRoot) (supportTag rightRoot)) word.toList
  have covered : flatten (pieces.map (encodedWord leftRoot rightRoot)) =
      macroLetters leftRoot rightRoot word := flatten_encoded leftRoot rightRoot pieces
  rw [← covered]
  exact decompose_flatten_good (binaryTag 0 1) _
    (encoded_good leftRoot rightRoot pieces (decompose_good _ word.toList))

theorem macro_factor_count (leftRoot rightRoot word : Word Nat) :
    (decompose (binaryTag 0 1) (macroLetters leftRoot rightRoot word)).length =
      (decompose (unionTag (supportTag leftRoot) (supportTag rightRoot)) word.toList).length := by
  rw [decompose_macroLetters, List.length_map]

/-- Complementary factors decode literally without any root hypothesis. -/
theorem decode_encodedWord_negative (leftRoot rightRoot factor : Word Nat)
    (negative : unionTag (supportTag leftRoot) (supportTag rightRoot) factor.head = false) :
    (encodedWord leftRoot rightRoot factor).bind (image leftRoot rightRoot) = factor := by
  have notPositive : unionTag (supportTag leftRoot) (supportTag rightRoot) factor.head ≠ true := by
    rw [negative]
    decide
  apply Word.toList_injective
  rw [Word.toList_bind, encodedWord_toList]
  change decodeLetters leftRoot rightRoot (encodeFactor leftRoot rightRoot factor) = factor.toList
  rw [encodeFactor, if_neg notPositive]
  exact decode_complement leftRoot rightRoot factor.toList

/-- Full positive-factor decoding reuses the already proved original-word
perfect-root alignment, rather than assuming a codec inverse. -/
theorem decode_encodedWord_actual (leftRoot rightRoot word factor : Word Nat)
    (apart : ∀ value ∈ leftRoot.toList, value ∉ rightRoot.toList)
    (leftPerfect : CanonicalPerfect leftRoot word)
    (rightPerfect : CanonicalPerfect rightRoot word)
    (member : factor ∈ decompose
      (unionTag (supportTag leftRoot) (supportTag rightRoot)) word.toList) :
    (encodedWord leftRoot rightRoot factor).bind (image leftRoot rightRoot) = factor := by
  apply Word.toList_injective
  rw [Word.toList_bind, encodedWord_toList]
  exact decode_factor leftRoot rightRoot word factor apart leftPerfect rightPerfect member

def taggedToken (classify : Nat → Bool) (piece : Word Nat) : Option (Word Nat) :=
  if classify piece.head = true then none else some piece

def taggedSkeleton (classify : Nat → Bool) (letters : List Nat) : List (Option (Word Nat)) :=
  (decompose classify letters).map (taggedToken classify)

def decodedToken (leftRoot rightRoot : Word Nat) (token : Option (Word Nat)) : Option (Word Nat) :=
  token.map (fun piece => piece.bind (image leftRoot rightRoot))

theorem taggedToken_binary (piece : Word Nat) :
    taggedToken (binaryTag 0 1) piece = factorToken piece := rfl

theorem taggedSkeleton_binary (letters : List Nat) :
    taggedSkeleton (binaryTag 0 1) letters = canonicalSkeleton letters := rfl

theorem decoded_factorToken (leftRoot rightRoot factor : Word Nat) :
    decodedToken leftRoot rightRoot (factorToken (encodedWord leftRoot rightRoot factor)) =
      taggedToken (unionTag (supportTag leftRoot) (supportTag rightRoot)) factor := by
  rw [factorToken, encodedWord_head_tag, taggedToken]
  by_cases positive : unionTag (supportTag leftRoot) (supportTag rightRoot) factor.head = true
  · rw [if_pos positive, if_pos positive]
    rfl
  · rw [if_neg positive, if_neg positive]
    change some ((encodedWord leftRoot rightRoot factor).bind (image leftRoot rightRoot)) = some factor
    exact congrArg some (decode_encodedWord_negative leftRoot rightRoot factor
      (false_of_ne_true _ positive))

/-- All original positive slots and literal complementary factors are recovered
in their exact order. Repeated roots and overlapping supports are allowed here. -/
theorem decoded_macro_skeleton (leftRoot rightRoot word : Word Nat) :
    (canonicalSkeleton (macroLetters leftRoot rightRoot word)).map
        (decodedToken leftRoot rightRoot) =
      taggedSkeleton (unionTag (supportTag leftRoot) (supportTag rightRoot)) word.toList := by
  change ((decompose (binaryTag 0 1) (macroLetters leftRoot rightRoot word)).map factorToken).map
    (decodedToken leftRoot rightRoot) = _
  rw [decompose_macroLetters, List.map_map, List.map_map]
  change (decompose (unionTag (supportTag leftRoot) (supportTag rightRoot)) word.toList).map
      (fun factor => decodedToken leftRoot rightRoot (factorToken (encodedWord leftRoot rightRoot factor))) =
    (decompose (unionTag (supportTag leftRoot) (supportTag rightRoot)) word.toList).map
      (taggedToken (unionTag (supportTag leftRoot) (supportTag rightRoot)))
  apply List.map_congr_left
  intro factor _
  exact decoded_factorToken leftRoot rightRoot factor

theorem decoded_macroWord_skeleton (leftRoot rightRoot word : Word Nat)
    (apart : ∀ value ∈ leftRoot.toList, value ∉ rightRoot.toList)
    (leftPerfect : CanonicalPerfect leftRoot word)
    (rightPerfect : CanonicalPerfect rightRoot word) :
    (canonicalSkeleton (macroWord leftRoot rightRoot word apart leftPerfect rightPerfect).toList).map
        (decodedToken leftRoot rightRoot) =
      taggedSkeleton (unionTag (supportTag leftRoot) (supportTag rightRoot)) word.toList := by
  rw [macroWord_toList]
  exact decoded_macro_skeleton leftRoot rightRoot word

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorCodec

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorCodec.decompose_word_nonempty
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorCodec.encodeFactor_nonempty
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorCodec.encodedWord_toList
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorCodec.encodeFactor_tag
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorCodec.encodedWord_head_tag
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorCodec.encodedWord_constant
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorCodec.encoded_good
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorCodec.flatten_encoded
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorCodec.decompose_macroLetters
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorCodec.macro_factor_count
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorCodec.decode_encodedWord_negative
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorCodec.decode_encodedWord_actual
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorCodec.taggedToken_binary
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorCodec.taggedSkeleton_binary
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorCodec.decoded_factorToken
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorCodec.decoded_macro_skeleton
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorCodec.decoded_macroWord_skeleton
