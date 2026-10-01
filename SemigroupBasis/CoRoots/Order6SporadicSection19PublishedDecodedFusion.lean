import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedNormalizerLayout

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.DecodedFusion

open CrossFactor FactorContexts MarkedZones SquareCoalescing BinaryPowers
  CanonicalSquareCover BlockAlignment OccurrenceMacro MacroWitnesses SeparatorSkeleton

theorem bind_singleton (letter : Nat) (substitution : Nat → Word Nat) :
    (Word.singleton letter).bind substitution = substitution letter := rfl

theorem bind_append (left right : Word Nat) (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution = left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp only [Word.toList_bind, Word.toList_append, List.flatMap_append]

/-- Substitution acts on present contexts only. No empty semigroup word is added. -/
def bindContext (substitution : Nat → Word Nat) : Option (Word Nat) → Option (Word Nat)
  | none => none
  | some word => some (word.bind substitution)

theorem contextLetters_bindContext (substitution : Nat → Word Nat)
    (context : Option (Word Nat)) :
    contextLetters (bindContext substitution context) =
      (contextLetters context).flatMap (fun letter => (substitution letter).toList) := by
  cases context with
  | none => rfl
  | some word => exact Word.toList_bind word substitution

theorem bindContext_contextWord (substitution : Nat → Word Nat) (letters : List Nat) :
    bindContext substitution (contextWord letters) =
      contextWord (letters.flatMap (fun letter => (substitution letter).toList)) := by
  calc
    bindContext substitution (contextWord letters) =
        contextWord (contextLetters (bindContext substitution (contextWord letters))) :=
      (contextWord_contextLetters _).symm
    _ = contextWord (letters.flatMap (fun letter => (substitution letter).toList)) := by
      rw [contextLetters_bindContext, contextLetters_contextWord]

theorem bind_gap (word : Word Nat) (context : Option (Word Nat))
    (substitution : Nat → Word Nat) :
    (gap word context).bind substitution =
      gap (word.bind substitution) (bindContext substitution context) := by
  cases context with
  | none => rfl
  | some suffix => exact bind_append word suffix substitution

theorem bind_frame (before after : Option (Word Nat)) (word : Word Nat)
    (substitution : Nat → Word Nat) :
    (Context.frame before after word).bind substitution =
      Context.frame (bindContext substitution before) (bindContext substitution after)
        (word.bind substitution) := by
  cases before with
  | none =>
      cases after with
      | none => rfl
      | some suffix => exact bind_append word suffix substitution
  | some beforeWord =>
      cases after with
      | none => exact bind_append beforeWord word substitution
      | some suffix =>
          change ((beforeWord ++ word) ++ suffix).bind substitution =
            (beforeWord.bind substitution ++ word.bind substitution) ++ suffix.bind substitution
          rw [bind_append, bind_append]

theorem bind_framed_lists (before after : List Nat) (word : Word Nat)
    (substitution : Nat → Word Nat) :
    (Context.frame (contextWord before) (contextWord after) word).bind substitution =
      Context.frame
        (contextWord (before.flatMap (fun letter => (substitution letter).toList)))
        (contextWord (after.flatMap (fun letter => (substitution letter).toList)))
        (word.bind substitution) := by
  rw [bind_frame, bindContext_contextWord, bindContext_contextWord]

theorem bind_prefixChain (block finalWord : Word Nat) (gaps : List (List Nat))
    (substitution : Nat → Word Nat) :
    (prefixChain block gaps finalWord).bind substitution =
      prefixChain (block.bind substitution)
        (gaps.map (fun letters => letters.flatMap (fun letter => (substitution letter).toList)))
        (finalWord.bind substitution) := by
  induction gaps with
  | nil => rfl
  | cons letters rest ih =>
      change (gap block (contextWord letters) ++ prefixChain block rest finalWord).bind
          substitution =
        gap (block.bind substitution)
            (contextWord (letters.flatMap (fun letter => (substitution letter).toList))) ++
          prefixChain (block.bind substitution)
            (rest.map (fun later => later.flatMap (fun letter => (substitution letter).toList)))
            (finalWord.bind substitution)
      rw [bind_append, bind_gap, bindContext_contextWord, ih]

theorem bind_chain (block : Word Nat) (gaps : List (List Nat))
    (substitution : Nat → Word Nat) :
    (chain block gaps).bind substitution =
      chain (block.bind substitution)
        (gaps.map (fun letters => letters.flatMap (fun letter => (substitution letter).toList))) :=
  bind_prefixChain block block gaps substitution

theorem bind_square (left right : Word Nat) (substitution : Nat → Word Nat) :
    (square left right).bind substitution =
      square (left.bind substitution) (right.bind substitution) := by
  simp only [square, bind_append]

theorem bind_binary_square (leftRoot rightRoot : Word Nat) :
    (square (Word.singleton 0) (Word.singleton 1)).bind (image leftRoot rightRoot) =
      square (leftRoot ++ leftRoot) (rightRoot ++ rightRoot) := by
  rw [bind_square]
  rfl

theorem decode_word_toList (leftRoot rightRoot word : Word Nat) :
    decodeLetters leftRoot rightRoot word.toList =
      (word.bind (image leftRoot rightRoot)).toList :=
  (Word.toList_bind word (image leftRoot rightRoot)).symm

theorem decode_word_nonempty (leftRoot rightRoot word : Word Nat) :
    decodeLetters leftRoot rightRoot word.toList ≠ [] := by
  rw [decode_word_toList]
  exact MaximalFactors.piece_nonempty (word.bind (image leftRoot rightRoot))

def binaryFrame (leading trailing : List Nat) (gaps : List (Word Nat)) : Word Nat :=
  Context.frame (contextWord leading) (contextWord trailing)
    (chain (square (Word.singleton 0) (Word.singleton 1)) (gaps.map Word.toList))

def decodedFrame (leftRoot rightRoot : Word Nat) (leading trailing : List Nat)
    (gaps : List (Word Nat)) : Word Nat :=
  Context.frame (contextWord (decodeLetters leftRoot rightRoot leading))
    (contextWord (decodeLetters leftRoot rightRoot trailing))
    (chain (square (leftRoot ++ leftRoot) (rightRoot ++ rightRoot))
      (gaps.map (fun (separator : Word Nat) => decodeLetters leftRoot rightRoot separator.toList)))

def fusedFrame (leftRoot rightRoot : Word Nat) (leading trailing : List Nat)
    (gaps : List (Word Nat)) : Word Nat :=
  Context.frame (contextWord (decodeLetters leftRoot rightRoot leading))
    (contextWord (decodeLetters leftRoot rightRoot trailing))
    (chain (SquarePermutation.sortedRoot (leftRoot ++ rightRoot) ++
        SquarePermutation.sortedRoot (leftRoot ++ rightRoot))
      (gaps.map (fun (separator : Word Nat) => decodeLetters leftRoot rightRoot separator.toList)))

/-- Decode the actual frame and every actual gap; substitution is not an
assumed renderer equation. This identity needs no color-compatibility premise. -/
theorem decode_binaryFrame (leftRoot rightRoot : Word Nat) (leading trailing : List Nat)
    (gaps : List (Word Nat)) :
    (binaryFrame leading trailing gaps).bind (image leftRoot rightRoot) =
      decodedFrame leftRoot rightRoot leading trailing gaps := by
  unfold binaryFrame decodedFrame
  rw [bind_framed_lists, bind_chain, bind_binary_square, List.map_map]
  rfl

/-- Fusion and sorting change the positive block only. This reuses the proved
published-basis chain theorem, without inferring duplicate-free roots. -/
theorem decoded_fusion (leftRoot rightRoot : Word Nat) (leading trailing : List Nat)
    (gaps : List (Word Nat)) :
    Derives basis (decodedFrame leftRoot rightRoot leading trailing gaps)
      (fusedFrame leftRoot rightRoot leading trailing gaps) := by
  let gapLetters : List (List Nat) :=
    gaps.map (fun (separator : Word Nat) => decodeLetters leftRoot rightRoot separator.toList)
  have fused : Derives basis
      (Context.frame (contextWord (decodeLetters leftRoot rightRoot leading))
        (contextWord (decodeLetters leftRoot rightRoot trailing))
        (chain (square (leftRoot ++ leftRoot) (rightRoot ++ rightRoot)) gapLetters))
      (Context.frame (contextWord (decodeLetters leftRoot rightRoot leading))
        (contextWord (decodeLetters leftRoot rightRoot trailing))
        (chain (SquarePermutation.sortedRoot (leftRoot ++ rightRoot) ++
          SquarePermutation.sortedRoot (leftRoot ++ rightRoot)) gapLetters)) :=
    SquarePermutation.fused_sorted_framed_chain leftRoot rightRoot gapLetters
      (decodeLetters leftRoot rightRoot leading) (decodeLetters leftRoot rightRoot trailing)
  exact fused

theorem perfect_decoded_fusion (leftRoot rightRoot normal : Word Nat)
    (perfect : BinaryPerfect.Perfect 0 1 normal) :
    ∃ leading trailing : List Nat, ∃ gaps : List (Word Nat),
      Outside 0 1 leading ∧ Outside 0 1 trailing ∧
      (∀ separator ∈ gaps, Outside 0 1 separator.toList) ∧
      normal = binaryFrame leading trailing gaps ∧
      normal.bind (image leftRoot rightRoot) =
        decodedFrame leftRoot rightRoot leading trailing gaps ∧
      Derives basis (normal.bind (image leftRoot rightRoot))
        (fusedFrame leftRoot rightRoot leading trailing gaps) := by
  obtain ⟨leading, trailing, gaps, headClean, tailClean, clean, equal⟩ := perfect
  have framed : normal = binaryFrame leading trailing gaps := equal
  have decoded : normal.bind (image leftRoot rightRoot) =
      decodedFrame leftRoot rightRoot leading trailing gaps := by
    rw [framed]
    exact decode_binaryFrame leftRoot rightRoot leading trailing gaps
  refine ⟨leading, trailing, gaps, headClean, tailClean, clean, framed, decoded, ?_⟩
  rw [decoded]
  exact decoded_fusion leftRoot rightRoot leading trailing gaps

/-- The original word reaches an actual sorted union-root frame. Its macro
separator skeleton is retained verbatim for the next local support-transport
proof. Canonical union perfection is not silently assumed here. -/
theorem generalized_fused_frame (leftRoot rightRoot word : Word Nat)
    (apart : ∀ value ∈ leftRoot.toList, value ∉ rightRoot.toList)
    (leftPerfect : CanonicalPerfect leftRoot word)
    (rightPerfect : CanonicalPerfect rightRoot word)
    (related : GeneralizedRelated leftRoot rightRoot word) :
    ∃ leading trailing : List Nat, ∃ gaps : List (Word Nat),
      Outside 0 1 leading ∧ Outside 0 1 trailing ∧
      (∀ separator ∈ gaps, Outside 0 1 separator.toList) ∧
      canonicalSkeleton (macroWord leftRoot rightRoot word apart leftPerfect rightPerfect).toList =
        canonicalSkeleton (binaryFrame leading trailing gaps).toList ∧
      Derives basis word (decodedFrame leftRoot rightRoot leading trailing gaps) ∧
      Derives basis word (fusedFrame leftRoot rightRoot leading trailing gaps) := by
  obtain ⟨normal, step, perfect, same⟩ :=
    NormalizerLayout.generalized_preserving_macro_perfect
      leftRoot rightRoot word apart leftPerfect rightPerfect related
  obtain ⟨leading, trailing, gaps, headClean, tailClean, clean, framed, decoded, fused⟩ :=
    perfect_decoded_fusion leftRoot rightRoot normal perfect
  refine ⟨leading, trailing, gaps, headClean, tailClean, clean, ?_, ?_, step.trans fused⟩
  · rw [← framed]
    exact same
  · rw [← decoded]
    exact step

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.DecodedFusion

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.DecodedFusion.bind_singleton
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.DecodedFusion.bind_append
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.DecodedFusion.contextLetters_bindContext
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.DecodedFusion.bindContext_contextWord
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.DecodedFusion.bind_gap
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.DecodedFusion.bind_frame
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.DecodedFusion.bind_framed_lists
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.DecodedFusion.bind_prefixChain
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.DecodedFusion.bind_chain
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.DecodedFusion.bind_square
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.DecodedFusion.bind_binary_square
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.DecodedFusion.decode_word_toList
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.DecodedFusion.decode_word_nonempty
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.DecodedFusion.decode_binaryFrame
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.DecodedFusion.decoded_fusion
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.DecodedFusion.perfect_decoded_fusion
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.DecodedFusion.generalized_fused_frame
