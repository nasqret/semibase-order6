import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedDecodedFusion

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.UnionPerfection

open MaximalFactors FactorBoundaries FactorContexts MarkedZones MaximalSquareCover
  CanonicalSquareCover SquareCoalescing BlockAlignment OccurrenceMacro MacroWitnesses
  SeparatorSkeleton DecodedFusion

/-- A literal negative Word occurs in the skeleton precisely when it is an
actual negative maximal factor. Positive placeholders cannot witness this. -/
theorem negative_token_member (letters : List Nat) (piece : Word Nat) :
    some piece ∈ canonicalSkeleton letters ↔
      piece ∈ decompose (binaryTag 0 1) letters ∧ binaryTag 0 1 piece.head = false := by
  constructor
  · intro member
    change some piece ∈ (decompose (binaryTag 0 1) letters).map factorToken at member
    obtain ⟨actual, actualMember, token⟩ := List.mem_map.mp member
    by_cases positive : binaryTag 0 1 actual.head = true
    · have impossible : (none : Option (Word Nat)) = some piece := by
        simpa only [factorToken, if_pos positive] using token
      cases impossible
    · have equal : actual = piece := Option.some.inj (by
        simpa only [factorToken, if_neg positive] using token)
      subst actual
      exact ⟨actualMember, false_of_ne_true _ positive⟩
  · rintro ⟨member, negative⟩
    change some piece ∈ (decompose (binaryTag 0 1) letters).map factorToken
    have notPositive : binaryTag 0 1 piece.head ≠ true := by
      rw [negative]
      decide
    exact List.mem_map.mpr ⟨piece, member, by rw [factorToken, if_neg notPositive]⟩

theorem negative_factor_transport (left right : List Nat)
    (same : canonicalSkeleton left = canonicalSkeleton right) (piece : Word Nat)
    (member : piece ∈ decompose (binaryTag 0 1) left)
    (negative : binaryTag 0 1 piece.head = false) :
    piece ∈ decompose (binaryTag 0 1) right := by
  have token : some piece ∈ canonicalSkeleton left :=
    (negative_token_member left piece).mpr ⟨member, negative⟩
  rw [same] at token
  exact ((negative_token_member right piece).mp token).1

theorem negative_member_transport (left right : List Nat)
    (same : canonicalSkeleton left = canonicalSkeleton right) (code : Nat)
    (negative : binaryTag 0 1 code = false) (member : code ∈ left) : code ∈ right := by
  obtain ⟨piece, pieceMember, inside⟩ :=
    (decompose_covers (binaryTag 0 1) code left).mp member
  have uniform : Constant (binaryTag 0 1) piece :=
    good_member_constant _ (decompose_good _ left) pieceMember
  have headNegative : binaryTag 0 1 piece.head = false :=
    (uniform code inside).symm.trans negative
  exact (decompose_covers (binaryTag 0 1) code right).mpr
    ⟨piece, negative_factor_transport left right same piece pieceMember headNegative, inside⟩

theorem blockCode_positive (left : Nat → Bool) (block : Word Nat) :
    binaryTag 0 1 (blockCode left block) = true := by
  by_cases positive : left block.head = true
  · rw [blockCode, if_pos positive]
    decide
  · rw [blockCode, if_neg positive]
    decide

/-- An actual negative macro code comes from a letter of an actual original
complementary factor. No global property of arbitrary codes is asserted. -/
theorem encoded_negative_origin (leftRoot rightRoot word factor : Word Nat)
    (factorMember : factor ∈ decompose
      (unionTag (supportTag leftRoot) (supportTag rightRoot)) word.toList)
    (code : Nat) (member : code ∈ encodeFactor leftRoot rightRoot factor)
    (negative : binaryTag 0 1 code = false) :
    ∃ original ∈ factor.toList, code = original + 2 ∧
      unionTag (supportTag leftRoot) (supportTag rightRoot) original = false := by
  cases tag : unionTag (supportTag leftRoot) (supportTag rightRoot) factor.head with
  | false =>
      have notPositive : unionTag (supportTag leftRoot) (supportTag rightRoot) factor.head ≠ true := by
        rw [tag]
        decide
      rw [encodeFactor, if_neg notPositive] at member
      obtain ⟨original, inside, equal⟩ := List.mem_map.mp member
      have uniform := good_member_constant _ (decompose_good _ word.toList) factorMember
      exact ⟨original, inside, equal.symm, (uniform original inside).trans tag⟩
  | true =>
      rw [encodeFactor, if_pos tag] at member
      change code ∈ (decompose (supportTag leftRoot) factor.toList).map
        (blockCode (supportTag leftRoot)) at member
      obtain ⟨block, _, equal⟩ := List.mem_map.mp member
      have positive : binaryTag 0 1 code = true := by
        rw [← equal]
        exact blockCode_positive (supportTag leftRoot) block
      have impossible : (false : Bool) = true := negative.symm.trans positive
      cases impossible

theorem macro_negative_image (leftRoot rightRoot word : Word Nat) (code : Nat)
    (member : code ∈ macroLetters leftRoot rightRoot word)
    (negative : binaryTag 0 1 code = false) :
    ∀ value ∈ (image leftRoot rightRoot code).toList,
      unionTag (supportTag leftRoot) (supportTag rightRoot) value = false := by
  change code ∈ (decompose (unionTag (supportTag leftRoot) (supportTag rightRoot))
    word.toList).flatMap (encodeFactor leftRoot rightRoot) at member
  obtain ⟨factor, factorMember, codeMember⟩ := List.mem_flatMap.mp member
  obtain ⟨original, _, codeEqual, excluded⟩ :=
    encoded_negative_origin leftRoot rightRoot word factor factorMember code codeMember negative
  intro value inside
  rw [codeEqual] at inside
  change value ∈ [original] at inside
  have equal : value = original := List.mem_singleton.mp inside
  rw [equal]
  exact excluded

theorem transported_negative_image (leftRoot rightRoot word : Word Nat) (codes : List Nat)
    (same : canonicalSkeleton (macroLetters leftRoot rightRoot word) = canonicalSkeleton codes)
    (code : Nat) (member : code ∈ codes) (negative : binaryTag 0 1 code = false) :
    ∀ value ∈ (image leftRoot rightRoot code).toList,
      unionTag (supportTag leftRoot) (supportTag rightRoot) value = false := by
  have original : code ∈ macroLetters leftRoot rightRoot word :=
    negative_member_transport codes (macroLetters leftRoot rightRoot word)
      same.symm code negative member
  exact macro_negative_image leftRoot rightRoot word code original negative

theorem chain_gap_member (block : Word Nat) (gaps : List (Word Nat))
    (separator : Word Nat) (member : separator ∈ gaps) (letter : Nat)
    (inside : letter ∈ separator.toList) :
    letter ∈ (chain block (gaps.map Word.toList)).toList := by
  revert member
  induction gaps with
  | nil => intro member; cases member
  | cons first rest ih =>
      intro member
      rw [List.map_cons, chain_cons_word, Word.toList_append, Word.toList_append]
      rcases List.mem_cons.mp member with equal | later
      · subst separator
        exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr inside)))
      · exact List.mem_append.mpr (Or.inr (ih later))

def TagClean (classify : Nat → Bool) (letters : List Nat) : Prop :=
  ∀ letter ∈ letters, classify letter = false

/-- Every decoded exterior and every decoded nonempty gap is outside BOTH
root supports, because its literal codes came from the original skeleton. -/
theorem decoded_frame_clean (leftRoot rightRoot word : Word Nat)
    (leading trailing : List Nat) (gaps : List (Word Nat))
    (headClean : Outside 0 1 leading) (tailClean : Outside 0 1 trailing)
    (clean : ∀ separator ∈ gaps, Outside 0 1 separator.toList)
    (same : canonicalSkeleton (macroLetters leftRoot rightRoot word) =
      canonicalSkeleton (binaryFrame leading trailing gaps).toList) :
    TagClean (unionTag (supportTag leftRoot) (supportTag rightRoot))
        (decodeLetters leftRoot rightRoot leading) ∧
      TagClean (unionTag (supportTag leftRoot) (supportTag rightRoot))
        (decodeLetters leftRoot rightRoot trailing) ∧
      ∀ separator ∈ gaps,
        TagClean (unionTag (supportTag leftRoot) (supportTag rightRoot))
          (decodeLetters leftRoot rightRoot separator.toList) := by
  let classify : Nat → Bool := unionTag (supportTag leftRoot) (supportTag rightRoot)
  have decodeClean (letters : List Nat)
      (occurs : ∀ code ∈ letters, code ∈ (binaryFrame leading trailing gaps).toList)
      (outside : Outside 0 1 letters) :
      TagClean classify (decodeLetters leftRoot rightRoot letters) := by
    intro value inside
    change value ∈ letters.flatMap (fun code => (image leftRoot rightRoot code).toList) at inside
    obtain ⟨code, codeMember, imageMember⟩ := List.mem_flatMap.mp inside
    exact transported_negative_image leftRoot rightRoot word _ same code
      (occurs code codeMember) (outside_tag 0 1 letters outside code codeMember) value imageMember
  have headOccurs : ∀ code ∈ leading, code ∈ (binaryFrame leading trailing gaps).toList := by
    intro code member
    rw [binaryFrame, frame_of_lists_toList]
    exact List.mem_append.mpr (Or.inl member)
  have tailOccurs : ∀ code ∈ trailing, code ∈ (binaryFrame leading trailing gaps).toList := by
    intro code member
    rw [binaryFrame, frame_of_lists_toList]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr member)))
  refine ⟨decodeClean leading headOccurs headClean, decodeClean trailing tailOccurs tailClean, ?_⟩
  intro separator member
  apply decodeClean separator.toList _ (clean separator member)
  intro code inside
  rw [binaryFrame, frame_of_lists_toList]
  exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl
    (chain_gap_member _ gaps separator member code inside))))

theorem clean_head (classify : Nat → Bool) (piece : Word Nat)
    (clean : TagClean classify piece.toList) : classify piece.head = false :=
  clean piece.head (word_head_member piece)

theorem clean_constant (classify : Nat → Bool) (piece : Word Nat)
    (clean : TagClean classify piece.toList) : Constant classify piece := by
  intro letter member
  exact (clean letter member).trans (clean_head classify piece clean).symm

/-- The existing concrete frame constructor is maximal for any classification
when its positive block and its literal negative contexts have opposite tags. -/
theorem tagged_squarePieces_good (classify : Nat → Bool) (block : Word Nat)
    (positive : classify block.head = true) (uniform : Constant classify block)
    (gaps : List (Word Nat)) (trailing : List Nat)
    (tailClean : TagClean classify trailing)
    (clean : ∀ piece ∈ gaps, TagClean classify piece.toList) :
    Good classify (squarePieces block gaps trailing) := by
  revert clean
  induction gaps with
  | nil =>
      intro clean
      cases trailing with
      | nil => exact Good.last uniform
      | cons first later =>
          have negative := clean_head classify (⟨first, later⟩ : Word Nat) tailClean
          exact Good.step uniform (by rw [positive, negative]; decide)
            (Good.last (clean_constant classify (⟨first, later⟩ : Word Nat) tailClean))
  | cons separator rest ih =>
      intro clean
      have separatorClean := clean separator (List.mem_cons.mpr (Or.inl rfl))
      have negative := clean_head classify separator separatorClean
      have restClean : ∀ piece ∈ rest, TagClean classify piece.toList := by
        intro piece member
        exact clean piece (List.mem_cons.mpr (Or.inr member))
      change Good classify (block :: separator :: block :: afterSquares block rest trailing)
      exact Good.step uniform (by rw [positive, negative]; decide)
        (Good.step (clean_constant classify separator separatorClean)
          (by rw [negative, positive]; decide) (ih restClean))

theorem tagged_framedPieces_good (classify : Nat → Bool) (block : Word Nat)
    (positive : classify block.head = true) (uniform : Constant classify block)
    (gaps : List (Word Nat)) (leading trailing : List Nat)
    (headClean : TagClean classify leading) (tailClean : TagClean classify trailing)
    (clean : ∀ piece ∈ gaps, TagClean classify piece.toList) :
    Good classify (framedPieces block gaps leading trailing) := by
  have core := tagged_squarePieces_good classify block positive uniform gaps trailing tailClean clean
  cases leading with
  | nil => exact core
  | cons first later =>
      have negative := clean_head classify (⟨first, later⟩ : Word Nat) headClean
      exact Good.step (clean_constant classify (⟨first, later⟩ : Word Nat) headClean)
        (by rw [negative, positive]; decide) core

theorem tagged_squarePieces_positive (classify : Nat → Bool) (block : Word Nat)
    (gaps : List (Word Nat)) (trailing : List Nat)
    (tailClean : TagClean classify trailing)
    (clean : ∀ part ∈ gaps, TagClean classify part.toList)
    (piece : Word Nat) (member : piece ∈ squarePieces block gaps trailing)
    (positive : classify piece.head = true) : piece = block := by
  rcases squarePieces_member block gaps trailing piece member with equal | inside | tailEqual
  · exact equal
  · have negative := clean_head classify piece (clean piece inside)
    have impossible : (false : Bool) = true := negative.symm.trans positive
    cases impossible
  · have pieceClean : TagClean classify piece.toList := by
      rw [tailEqual]
      exact tailClean
    have negative := clean_head classify piece pieceClean
    have impossible : (false : Bool) = true := negative.symm.trans positive
    cases impossible

theorem tagged_framedPieces_positive (classify : Nat → Bool) (block : Word Nat)
    (gaps : List (Word Nat)) (leading trailing : List Nat)
    (headClean : TagClean classify leading) (tailClean : TagClean classify trailing)
    (clean : ∀ part ∈ gaps, TagClean classify part.toList)
    (piece : Word Nat) (member : piece ∈ framedPieces block gaps leading trailing)
    (positive : classify piece.head = true) : piece = block := by
  rcases List.mem_append.mp member with first | later
  · cases leading with
    | nil => cases first
    | cons head tail =>
        have equal : piece = (⟨head, tail⟩ : Word Nat) := List.mem_singleton.mp first
        subst piece
        have negative := clean_head classify (⟨head, tail⟩ : Word Nat) headClean
        have impossible : (false : Bool) = true := negative.symm.trans positive
        cases impossible
  · exact tagged_squarePieces_positive classify block gaps trailing tailClean clean piece later positive

theorem canonical_framed_root (root : Word Nat) (leading trailing : List Nat)
    (gaps : List (Word Nat)) (headClean : TagClean (supportTag root) leading)
    (tailClean : TagClean (supportTag root) trailing)
    (clean : ∀ piece ∈ gaps, TagClean (supportTag root) piece.toList) :
    CanonicalPerfect root
      (Context.frame (contextWord leading) (contextWord trailing)
        (chain (root ++ root) (gaps.map Word.toList))) := by
  have positive : supportTag root (root ++ root).head = true :=
    (supportTag_true root root.head).mpr (word_head_member root)
  have good : Good (supportTag root) (framedPieces (root ++ root) gaps leading trailing) :=
    tagged_framedPieces_good (supportTag root) (root ++ root) positive
      (root_square_constant root) gaps leading trailing headClean tailClean clean
  have canonical : decompose (supportTag root)
      (Context.frame (contextWord leading) (contextWord trailing)
        (chain (root ++ root) (gaps.map Word.toList))).toList =
      framedPieces (root ++ root) gaps leading trailing := by
    rw [← flatten_framedPieces]
    exact decompose_flatten_good _ _ good
  constructor
  · rw [canonical]
    exact BinaryPerfect.framed_block_member (root ++ root) gaps leading trailing
  · intro piece member positivePiece
    rw [canonical] at member
    exact tagged_framedPieces_positive (supportTag root) (root ++ root) gaps
      leading trailing headClean tailClean clean piece member positivePiece

/-- Sorting preserves support even for repeated roots. No Nodup hypothesis is
needed for this equality, nor is one inferred from CanonicalPerfect. -/
theorem sorted_union_tag (leftRoot rightRoot : Word Nat) :
    supportTag (SquarePermutation.sortedRoot (leftRoot ++ rightRoot)) =
      unionTag (supportTag leftRoot) (supportTag rightRoot) := by
  funext value
  have members : value ∈ (SquarePermutation.sortedRoot (leftRoot ++ rightRoot)).toList ↔
      value ∈ leftRoot.toList ∨ value ∈ rightRoot.toList := by
    simpa only [Word.toList_append, List.mem_append] using
      (SquarePermutation.sortedRoot_perm (leftRoot ++ rightRoot)).symm.mem_iff (a := value)
  have sameTrue : supportTag (SquarePermutation.sortedRoot (leftRoot ++ rightRoot)) value = true ↔
      unionTag (supportTag leftRoot) (supportTag rightRoot) value = true := by
    rw [supportTag_true, unionTag, Bool.or_eq_true, supportTag_true, supportTag_true]
    exact members
  cases sortedTag : supportTag (SquarePermutation.sortedRoot (leftRoot ++ rightRoot)) value with
  | false =>
      cases unionValue : unionTag (supportTag leftRoot) (supportTag rightRoot) value with
      | false => rfl
      | true =>
          have impossible : (false : Bool) = true :=
            sortedTag.symm.trans (sameTrue.mpr unionValue)
          cases impossible
  | true => exact (sameTrue.mp sortedTag).symm

theorem fused_frame_canonical (leftRoot rightRoot word : Word Nat)
    (leading trailing : List Nat) (gaps : List (Word Nat))
    (headClean : Outside 0 1 leading) (tailClean : Outside 0 1 trailing)
    (clean : ∀ separator ∈ gaps, Outside 0 1 separator.toList)
    (same : canonicalSkeleton (macroLetters leftRoot rightRoot word) =
      canonicalSkeleton (binaryFrame leading trailing gaps).toList) :
    CanonicalPerfect (SquarePermutation.sortedRoot (leftRoot ++ rightRoot))
      (fusedFrame leftRoot rightRoot leading trailing gaps) := by
  obtain ⟨headDecoded, tailDecoded, gapsDecoded⟩ :=
    decoded_frame_clean leftRoot rightRoot word leading trailing gaps headClean tailClean clean same
  let decodedGaps : List (Word Nat) :=
    gaps.map (fun (separator : Word Nat) => separator.bind (image leftRoot rightRoot))
  have gapLists : decodedGaps.map Word.toList =
      gaps.map (fun (separator : Word Nat) => decodeLetters leftRoot rightRoot separator.toList) := by
    simp only [decodedGaps, List.map_map, Function.comp_def, Word.toList_bind, decodeLetters]
  have headSupport : TagClean (supportTag (SquarePermutation.sortedRoot (leftRoot ++ rightRoot)))
      (decodeLetters leftRoot rightRoot leading) := by
    rw [sorted_union_tag]
    exact headDecoded
  have tailSupport : TagClean (supportTag (SquarePermutation.sortedRoot (leftRoot ++ rightRoot)))
      (decodeLetters leftRoot rightRoot trailing) := by
    rw [sorted_union_tag]
    exact tailDecoded
  have gapSupport : ∀ piece ∈ decodedGaps,
      TagClean (supportTag (SquarePermutation.sortedRoot (leftRoot ++ rightRoot))) piece.toList := by
    intro piece member
    obtain ⟨separator, separatorMember, equal⟩ := List.mem_map.mp member
    subst piece
    rw [sorted_union_tag]
    change TagClean (unionTag (supportTag leftRoot) (supportTag rightRoot))
      (separator.bind (image leftRoot rightRoot)).toList
    rw [← decode_word_toList]
    exact gapsDecoded separator separatorMember
  have actual := canonical_framed_root (SquarePermutation.sortedRoot (leftRoot ++ rightRoot))
    (decodeLetters leftRoot rightRoot leading) (decodeLetters leftRoot rightRoot trailing)
    decodedGaps headSupport tailSupport gapSupport
  rw [gapLists] at actual
  exact actual

/-- Disjoint actual perfect roots with a real generalized witness derive an
actual sorted union-root perfect word. All hypotheses are on the original
word; no rendering, reachability, or decoder compatibility is assumed. -/
theorem generalized_sorted_union_perfect (leftRoot rightRoot word : Word Nat)
    (apart : ∀ value ∈ leftRoot.toList, value ∉ rightRoot.toList)
    (leftPerfect : CanonicalPerfect leftRoot word)
    (rightPerfect : CanonicalPerfect rightRoot word)
    (related : GeneralizedRelated leftRoot rightRoot word) :
    ∃ normal : Word Nat, Derives basis word normal ∧
      CanonicalPerfect (SquarePermutation.sortedRoot (leftRoot ++ rightRoot)) normal := by
  obtain ⟨leading, trailing, gaps, headClean, tailClean, clean, same, _, step⟩ :=
    generalized_fused_frame leftRoot rightRoot word apart leftPerfect rightPerfect related
  have rawSame : canonicalSkeleton (macroLetters leftRoot rightRoot word) =
      canonicalSkeleton (binaryFrame leading trailing gaps).toList := by
    simpa only [macroWord_toList] using same
  exact ⟨fusedFrame leftRoot rightRoot leading trailing gaps, step,
    fused_frame_canonical leftRoot rightRoot word leading trailing gaps
      headClean tailClean clean rawSame⟩

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.UnionPerfection

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.UnionPerfection.negative_token_member
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.UnionPerfection.negative_factor_transport
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.UnionPerfection.negative_member_transport
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.UnionPerfection.blockCode_positive
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.UnionPerfection.encoded_negative_origin
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.UnionPerfection.macro_negative_image
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.UnionPerfection.transported_negative_image
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.UnionPerfection.chain_gap_member
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.UnionPerfection.decoded_frame_clean
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.UnionPerfection.clean_head
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.UnionPerfection.clean_constant
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.UnionPerfection.tagged_squarePieces_good
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.UnionPerfection.tagged_framedPieces_good
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.UnionPerfection.tagged_squarePieces_positive
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.UnionPerfection.tagged_framedPieces_positive
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.UnionPerfection.canonical_framed_root
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.UnionPerfection.sorted_union_tag
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.UnionPerfection.fused_frame_canonical
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.UnionPerfection.generalized_sorted_union_perfect
