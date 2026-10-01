import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedFactorCodec

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SkeletonTransport

open MaximalFactors FactorBoundaries FactorContexts CanonicalSquareCover BlockAlignment
  OccurrenceMacro MacroWitnesses SeparatorSkeleton UnionPerfection FactorCodec
  DecodedFusion MaximalSquareCover BinaryPowers SquareCoalescing MarkedZones

/-- Compatibility is local to the actual letters, not an assertion about all
fresh codes. The final macro theorem derives it from the original skeleton. -/
def Compatible (fromTag toTag : Nat → Bool) (substitution : Nat → Word Nat)
    (letters : List Nat) : Prop :=
  ∀ letter ∈ letters, ∀ value ∈ (substitution letter).toList,
    toTag value = fromTag letter

theorem bound_factor_tag (fromTag toTag : Nat → Bool) (substitution : Nat → Word Nat)
    (piece : Word Nat) (uniform : Constant fromTag piece)
    (compatible : Compatible fromTag toTag substitution piece.toList)
    (value : Nat) (member : value ∈ (piece.bind substitution).toList) :
    toTag value = fromTag piece.head := by
  rw [Word.toList_bind] at member
  obtain ⟨letter, letterMember, imageMember⟩ := List.mem_flatMap.mp member
  exact (compatible letter letterMember value imageMember).trans (uniform letter letterMember)

theorem bound_factor_head_tag (fromTag toTag : Nat → Bool) (substitution : Nat → Word Nat)
    (piece : Word Nat) (uniform : Constant fromTag piece)
    (compatible : Compatible fromTag toTag substitution piece.toList) :
    toTag (piece.bind substitution).head = fromTag piece.head :=
  bound_factor_tag fromTag toTag substitution piece uniform compatible
    (piece.bind substitution).head (word_head_member _)

theorem bound_factor_constant (fromTag toTag : Nat → Bool) (substitution : Nat → Word Nat)
    (piece : Word Nat) (uniform : Constant fromTag piece)
    (compatible : Compatible fromTag toTag substitution piece.toList) :
    Constant toTag (piece.bind substitution) := by
  intro value member
  exact (bound_factor_tag fromTag toTag substitution piece uniform compatible value member).trans
    (bound_factor_head_tag fromTag toTag substitution piece uniform compatible).symm

theorem bound_good (fromTag toTag : Nat → Bool) (substitution : Nat → Word Nat)
    (pieces : List (Word Nat)) (good : Good fromTag pieces)
    (compatible : ∀ piece ∈ pieces, Compatible fromTag toTag substitution piece.toList) :
    Good toTag (pieces.map (fun piece => piece.bind substitution)) := by
  revert compatible
  induction good with
  | nil => intro _; exact Good.nil
  | @last piece uniform =>
      intro compatible
      exact Good.last (bound_factor_constant fromTag toTag substitution piece uniform
        (compatible piece (List.mem_cons.mpr (Or.inl rfl))))
  | @step first second rest uniform different tailGood ih =>
      intro compatible
      have firstCompatible := compatible first (List.mem_cons.mpr (Or.inl rfl))
      have secondCompatible := compatible second
        (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
      have secondUniform : Constant fromTag second :=
        good_member_constant fromTag tailGood (List.mem_cons.mpr (Or.inl rfl))
      exact Good.step (bound_factor_constant fromTag toTag substitution first uniform firstCompatible)
        (by
          rw [bound_factor_head_tag fromTag toTag substitution first uniform firstCompatible,
            bound_factor_head_tag fromTag toTag substitution second secondUniform secondCompatible]
          exact different)
        (ih (fun piece member => compatible piece (List.mem_cons.mpr (Or.inr member))))

theorem flatten_bound (substitution : Nat → Word Nat) (pieces : List (Word Nat)) :
    flatten (pieces.map (fun piece => piece.bind substitution)) =
      (flatten pieces).flatMap (fun letter => (substitution letter).toList) := by
  induction pieces with
  | nil => rfl
  | cons first rest ih =>
      change (first.bind substitution).toList ++
        flatten (rest.map (fun piece => piece.bind substitution)) =
          (first.toList ++ flatten rest).flatMap (fun letter => (substitution letter).toList)
      rw [Word.toList_bind, ih, List.flatMap_append]

/-- A locally color-compatible nonempty substitution preserves the ACTUAL
ordered maximal factor list, not merely the union of its letters. -/
theorem decompose_substituted (fromTag toTag : Nat → Bool) (substitution : Nat → Word Nat)
    (letters : List Nat) (compatible : Compatible fromTag toTag substitution letters) :
    decompose toTag (letters.flatMap (fun letter => (substitution letter).toList)) =
      (decompose fromTag letters).map (fun piece => piece.bind substitution) := by
  have localCompatible : ∀ piece ∈ decompose fromTag letters,
      Compatible fromTag toTag substitution piece.toList := by
    intro piece member letter inside value imageMember
    exact compatible letter ((decompose_covers fromTag letter letters).mpr ⟨piece, member, inside⟩)
      value imageMember
  have covered : flatten ((decompose fromTag letters).map (fun piece => piece.bind substitution)) =
      letters.flatMap (fun letter => (substitution letter).toList) := by
    rw [flatten_bound, flatten_decompose]
  rw [← covered]
  exact decompose_flatten_good toTag _
    (bound_good fromTag toTag substitution _ (decompose_good fromTag letters) localCompatible)

theorem taggedToken_bound (fromTag toTag : Nat → Bool) (substitution : Nat → Word Nat)
    (piece : Word Nat) (uniform : Constant fromTag piece)
    (compatible : Compatible fromTag toTag substitution piece.toList) :
    taggedToken toTag (piece.bind substitution) =
      (taggedToken fromTag piece).map (fun factor => factor.bind substitution) := by
  change (if toTag (piece.bind substitution).head = true then none else some (piece.bind substitution)) =
    (if fromTag piece.head = true then none else some piece).map (fun factor => factor.bind substitution)
  rw [bound_factor_head_tag fromTag toTag substitution piece uniform compatible]
  by_cases positive : fromTag piece.head = true
  · rw [if_pos positive, if_pos positive]
    rfl
  · rw [if_neg positive, if_neg positive]
    rfl

theorem taggedSkeleton_substituted (fromTag toTag : Nat → Bool) (substitution : Nat → Word Nat)
    (letters : List Nat) (compatible : Compatible fromTag toTag substitution letters) :
    taggedSkeleton toTag (letters.flatMap (fun letter => (substitution letter).toList)) =
      (taggedSkeleton fromTag letters).map
        (fun token => token.map (fun piece => piece.bind substitution)) := by
  unfold taggedSkeleton
  rw [decompose_substituted fromTag toTag substitution letters compatible, List.map_map, List.map_map]
  apply List.map_congr_left
  intro piece member
  apply taggedToken_bound fromTag toTag substitution piece
    (good_member_constant fromTag (decompose_good fromTag letters) member)
  intro letter inside value imageMember
  exact compatible letter ((decompose_covers fromTag letter letters).mpr ⟨piece, member, inside⟩)
    value imageMember

theorem positive_image (leftRoot rightRoot : Word Nat) (code : Nat)
    (positive : binaryTag 0 1 code = true) (value : Nat)
    (member : value ∈ (image leftRoot rightRoot code).toList) :
    unionTag (supportTag leftRoot) (supportTag rightRoot) value = true := by
  rcases (binaryTag_true 0 1 code).mp positive with zero | one
  · subst code
    have belongs : value ∈ leftRoot.toList := by
      change value ∈ (leftRoot ++ leftRoot).toList at member
      rw [Word.toList_append] at member
      exact (List.mem_append.mp member).elim id id
    exact union_left _ _ value ((supportTag_true leftRoot value).mpr belongs)
  · subst code
    have belongs : value ∈ rightRoot.toList := by
      change value ∈ (rightRoot ++ rightRoot).toList at member
      rw [Word.toList_append] at member
      exact (List.mem_append.mp member).elim id id
    exact union_right _ _ value ((supportTag_true rightRoot value).mpr belongs)

/-- The possible negative-code aliases are excluded by their actual original
factor origin. Compatibility is DERIVED from the exact preserved skeleton. -/
theorem macro_image_compatible (leftRoot rightRoot word : Word Nat) (codes : List Nat)
    (same : canonicalSkeleton (macroLetters leftRoot rightRoot word) = canonicalSkeleton codes) :
    Compatible (binaryTag 0 1) (unionTag (supportTag leftRoot) (supportTag rightRoot))
      (image leftRoot rightRoot) codes := by
  intro code member value imageMember
  by_cases positive : binaryTag 0 1 code = true
  · exact (positive_image leftRoot rightRoot code positive value imageMember).trans positive.symm
  · have negative : binaryTag 0 1 code = false := false_of_ne_true _ positive
    exact (transported_negative_image leftRoot rightRoot word codes same code member negative
      value imageMember).trans negative.symm

theorem decoded_normal_skeleton (leftRoot rightRoot word normal : Word Nat)
    (same : canonicalSkeleton (macroLetters leftRoot rightRoot word) =
      canonicalSkeleton normal.toList) :
    taggedSkeleton (unionTag (supportTag leftRoot) (supportTag rightRoot))
        (normal.bind (image leftRoot rightRoot)).toList =
      (canonicalSkeleton normal.toList).map (decodedToken leftRoot rightRoot) := by
  rw [Word.toList_bind]
  exact taggedSkeleton_substituted (binaryTag 0 1)
    (unionTag (supportTag leftRoot) (supportTag rightRoot)) (image leftRoot rightRoot)
    normal.toList (macro_image_compatible leftRoot rightRoot word normal.toList same)

theorem decoded_binary_block_color (leftRoot rightRoot : Word Nat) :
    unionTag (supportTag leftRoot) (supportTag rightRoot)
        (square (leftRoot ++ leftRoot) (rightRoot ++ rightRoot)).head = true ∧
      Constant (unionTag (supportTag leftRoot) (supportTag rightRoot))
        (square (leftRoot ++ leftRoot) (rightRoot ++ rightRoot)) := by
  have compatible : Compatible (binaryTag 0 1)
      (unionTag (supportTag leftRoot) (supportTag rightRoot)) (image leftRoot rightRoot)
      (square (Word.singleton 0) (Word.singleton 1)).toList := by
    intro code member value imageMember
    have positive : binaryTag 0 1 code = true :=
      (square_constant 0 1 code member).trans (square_head_tag 0 1)
    exact (positive_image leftRoot rightRoot code positive value imageMember).trans positive.symm
  have headed := bound_factor_head_tag (binaryTag 0 1)
    (unionTag (supportTag leftRoot) (supportTag rightRoot)) (image leftRoot rightRoot)
    (square (Word.singleton 0) (Word.singleton 1)) (square_constant 0 1) compatible
  have uniform := bound_factor_constant (binaryTag 0 1)
    (unionTag (supportTag leftRoot) (supportTag rightRoot)) (image leftRoot rightRoot)
    (square (Word.singleton 0) (Word.singleton 1)) (square_constant 0 1) compatible
  rw [bind_binary_square] at headed uniform
  exact ⟨headed.trans (square_head_tag 0 1), uniform⟩

theorem framed_decompose (classify : Nat → Bool) (block : Word Nat)
    (positive : classify block.head = true) (uniform : Constant classify block)
    (leading trailing : List Nat) (gaps : List (Word Nat))
    (headClean : TagClean classify leading) (tailClean : TagClean classify trailing)
    (clean : ∀ piece ∈ gaps, TagClean classify piece.toList) :
    decompose classify (Context.frame (contextWord leading) (contextWord trailing)
      (chain block (gaps.map Word.toList))).toList = framedPieces block gaps leading trailing := by
  rw [← flatten_framedPieces]
  exact decompose_flatten_good classify _
    (tagged_framedPieces_good classify block positive uniform gaps leading trailing headClean tailClean clean)

theorem afterSquares_tokens_replace (classify : Nat → Bool) (first second : Word Nat)
    (firstPositive : classify first.head = true) (secondPositive : classify second.head = true)
    (gaps : List (Word Nat)) (trailing : List Nat) :
    (afterSquares first gaps trailing).map (taggedToken classify) =
      (afterSquares second gaps trailing).map (taggedToken classify) := by
  have firstToken : taggedToken classify first = none := by rw [taggedToken, if_pos firstPositive]
  have secondToken : taggedToken classify second = none := by rw [taggedToken, if_pos secondPositive]
  induction gaps with
  | nil => rfl
  | cons separator rest ih =>
      change taggedToken classify separator :: taggedToken classify first ::
          (afterSquares first rest trailing).map (taggedToken classify) =
        taggedToken classify separator :: taggedToken classify second ::
          (afterSquares second rest trailing).map (taggedToken classify)
      rw [firstToken, secondToken, ih]

theorem framed_tokens_replace (classify : Nat → Bool) (first second : Word Nat)
    (firstPositive : classify first.head = true) (secondPositive : classify second.head = true)
    (gaps : List (Word Nat)) (leading trailing : List Nat) :
    (framedPieces first gaps leading trailing).map (taggedToken classify) =
      (framedPieces second gaps leading trailing).map (taggedToken classify) := by
  have firstToken : taggedToken classify first = none := by rw [taggedToken, if_pos firstPositive]
  have secondToken : taggedToken classify second = none := by rw [taggedToken, if_pos secondPositive]
  simp only [framedPieces, squarePieces, List.map_append, List.map_cons]
  rw [firstToken, secondToken,
    afterSquares_tokens_replace classify first second firstPositive secondPositive gaps trailing]

theorem tagged_frame_replace (classify : Nat → Bool) (first second : Word Nat)
    (firstPositive : classify first.head = true) (firstUniform : Constant classify first)
    (secondPositive : classify second.head = true) (secondUniform : Constant classify second)
    (leading trailing : List Nat) (gaps : List (Word Nat))
    (headClean : TagClean classify leading) (tailClean : TagClean classify trailing)
    (clean : ∀ piece ∈ gaps, TagClean classify piece.toList) :
    taggedSkeleton classify (Context.frame (contextWord leading) (contextWord trailing)
        (chain first (gaps.map Word.toList))).toList =
      taggedSkeleton classify (Context.frame (contextWord leading) (contextWord trailing)
        (chain second (gaps.map Word.toList))).toList := by
  unfold taggedSkeleton
  rw [framed_decompose classify first firstPositive firstUniform leading trailing gaps headClean tailClean clean,
    framed_decompose classify second secondPositive secondUniform leading trailing gaps headClean tailClean clean]
  exact framed_tokens_replace classify first second firstPositive secondPositive gaps leading trailing

theorem decoded_frame_skeleton (leftRoot rightRoot word : Word Nat)
    (leading trailing : List Nat) (gaps : List (Word Nat))
    (headClean : Outside 0 1 leading) (tailClean : Outside 0 1 trailing)
    (clean : ∀ separator ∈ gaps, Outside 0 1 separator.toList)
    (same : canonicalSkeleton (macroLetters leftRoot rightRoot word) =
      canonicalSkeleton (binaryFrame leading trailing gaps).toList) :
    taggedSkeleton (unionTag (supportTag leftRoot) (supportTag rightRoot))
        (decodedFrame leftRoot rightRoot leading trailing gaps).toList =
      taggedSkeleton (unionTag (supportTag leftRoot) (supportTag rightRoot))
        (fusedFrame leftRoot rightRoot leading trailing gaps).toList := by
  obtain ⟨headDecoded, tailDecoded, gapsDecoded⟩ :=
    decoded_frame_clean leftRoot rightRoot word leading trailing gaps headClean tailClean clean same
  let decodedGaps : List (Word Nat) :=
    gaps.map (fun (separator : Word Nat) => separator.bind (image leftRoot rightRoot))
  have gapLists : decodedGaps.map Word.toList =
      gaps.map (fun (separator : Word Nat) => decodeLetters leftRoot rightRoot separator.toList) := by
    simp only [decodedGaps, List.map_map, Function.comp_def, Word.toList_bind, decodeLetters]
  have gapClean : ∀ piece ∈ decodedGaps,
      TagClean (unionTag (supportTag leftRoot) (supportTag rightRoot)) piece.toList := by
    intro piece member
    obtain ⟨separator, separatorMember, equal⟩ := List.mem_map.mp member
    subst piece
    rw [← decode_word_toList]
    exact gapsDecoded separator separatorMember
  let root := SquarePermutation.sortedRoot (leftRoot ++ rightRoot)
  have secondPositive : unionTag (supportTag leftRoot) (supportTag rightRoot) (root ++ root).head = true := by
    change unionTag (supportTag leftRoot) (supportTag rightRoot) root.head = true
    rw [← sorted_union_tag]
    exact (supportTag_true root root.head).mpr (word_head_member root)
  have secondUniform : Constant (unionTag (supportTag leftRoot) (supportTag rightRoot)) (root ++ root) := by
    rw [← sorted_union_tag]
    exact root_square_constant root
  obtain ⟨firstPositive, firstUniform⟩ := decoded_binary_block_color leftRoot rightRoot
  have actual := tagged_frame_replace (unionTag (supportTag leftRoot) (supportTag rightRoot))
    (square (leftRoot ++ leftRoot) (rightRoot ++ rightRoot)) (root ++ root)
    firstPositive firstUniform secondPositive secondUniform
    (decodeLetters leftRoot rightRoot leading) (decodeLetters leftRoot rightRoot trailing)
    decodedGaps headDecoded tailDecoded gapClean
  rw [gapLists] at actual
  exact actual

/-- Generalized fusion preserves the ORIGINAL tagged union skeleton, including
every literal complementary factor in its original slot. No compatibility,
renderer, bound, disjoint-third-root premise, or duplicate-free root is assumed. -/
theorem generalized_sorted_union_preserving (leftRoot rightRoot word : Word Nat)
    (apart : ∀ value ∈ leftRoot.toList, value ∉ rightRoot.toList)
    (leftPerfect : CanonicalPerfect leftRoot word)
    (rightPerfect : CanonicalPerfect rightRoot word)
    (related : GeneralizedRelated leftRoot rightRoot word) :
    ∃ normal : Word Nat,
      Derives basis word normal ∧
      CanonicalPerfect (SquarePermutation.sortedRoot (leftRoot ++ rightRoot)) normal ∧
      taggedSkeleton (unionTag (supportTag leftRoot) (supportTag rightRoot)) word.toList =
        taggedSkeleton (unionTag (supportTag leftRoot) (supportTag rightRoot)) normal.toList := by
  obtain ⟨leading, trailing, gaps, headClean, tailClean, clean, sameMacro, _, step⟩ :=
    generalized_fused_frame leftRoot rightRoot word apart leftPerfect rightPerfect related
  have same : canonicalSkeleton (macroLetters leftRoot rightRoot word) =
      canonicalSkeleton (binaryFrame leading trailing gaps).toList := by
    simpa only [macroWord_toList] using sameMacro
  have decoded := decoded_normal_skeleton leftRoot rightRoot word (binaryFrame leading trailing gaps) same
  rw [decode_binaryFrame] at decoded
  refine ⟨fusedFrame leftRoot rightRoot leading trailing gaps, step,
    fused_frame_canonical leftRoot rightRoot word leading trailing gaps headClean tailClean clean same, ?_⟩
  calc
    taggedSkeleton (unionTag (supportTag leftRoot) (supportTag rightRoot)) word.toList =
        (canonicalSkeleton (macroLetters leftRoot rightRoot word)).map (decodedToken leftRoot rightRoot) :=
      (decoded_macro_skeleton leftRoot rightRoot word).symm
    _ = (canonicalSkeleton (binaryFrame leading trailing gaps).toList).map (decodedToken leftRoot rightRoot) :=
      congrArg (List.map (decodedToken leftRoot rightRoot)) same
    _ = taggedSkeleton (unionTag (supportTag leftRoot) (supportTag rightRoot))
        (decodedFrame leftRoot rightRoot leading trailing gaps).toList := decoded.symm
    _ = taggedSkeleton (unionTag (supportTag leftRoot) (supportTag rightRoot))
        (fusedFrame leftRoot rightRoot leading trailing gaps).toList :=
      decoded_frame_skeleton leftRoot rightRoot word leading trailing gaps headClean tailClean clean same

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SkeletonTransport

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SkeletonTransport.bound_factor_tag
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SkeletonTransport.bound_factor_head_tag
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SkeletonTransport.bound_factor_constant
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SkeletonTransport.bound_good
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SkeletonTransport.flatten_bound
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SkeletonTransport.decompose_substituted
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SkeletonTransport.taggedToken_bound
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SkeletonTransport.taggedSkeleton_substituted
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SkeletonTransport.positive_image
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SkeletonTransport.macro_image_compatible
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SkeletonTransport.decoded_normal_skeleton
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SkeletonTransport.decoded_binary_block_color
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SkeletonTransport.framed_decompose
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SkeletonTransport.afterSquares_tokens_replace
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SkeletonTransport.framed_tokens_replace
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SkeletonTransport.tagged_frame_replace
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SkeletonTransport.decoded_frame_skeleton
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SkeletonTransport.generalized_sorted_union_preserving
