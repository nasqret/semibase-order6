import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedOccurrenceMacro

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroWitnesses

open MaximalFactors FactorBoundaries FactorContexts CanonicalSquareCover BlockAlignment
  OccurrenceMacro OccurrenceWitnesses

theorem member_before {α : Type} (whole before : List α) (piece : α) (after : List α)
    (split : whole = before ++ piece :: after) (value : α) (member : value ∈ before) :
    value ∈ whole := by
  rw [split]
  exact List.mem_append.mpr (Or.inl member)

theorem member_after {α : Type} (whole before : List α) (piece : α) (after : List α)
    (split : whole = before ++ piece :: after) (value : α) (member : value ∈ after) :
    value ∈ whole := by
  rw [split]
  exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr member)))

theorem member_at {α : Type} (whole before : List α) (piece : α) (after : List α)
    (split : whole = before ++ piece :: after) : piece ∈ whole := by
  rw [split]
  exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

/-- Locate the chosen occurrence in its actual coarse factor, then saturate
its fine factor without changing either chosen exterior string. -/
theorem nested_occurrence_position (fine coarse : Nat → Bool) (block word : Word Nat)
    (contained : ∀ value, fine value = true → coarse value = true)
    (uniform : Constant fine block) (positive : fine block.head = true)
    (saturated : ∀ run ∈ decompose fine word.toList, fine run.head = true → run = block)
    (before after : List Nat) (split : word.toList = before ++ (block.toList ++ after)) :
    ∃ earlier later insideBefore insideAfter : List (Word Nat), ∃ factor : Word Nat,
      decompose coarse word.toList = earlier ++ factor :: later ∧
      coarse factor.head = true ∧
      decompose fine factor.toList = insideBefore ++ block :: insideAfter ∧
      before = flatten earlier ++ flatten insideBefore ∧
      after = flatten insideAfter ++ flatten later := by
  have blockPositive : coarse block.head = true := contained block.head positive
  have coarseUniform : Constant coarse block := by
    intro value member
    exact (contained value ((uniform value member).trans positive)).trans blockPositive.symm
  obtain ⟨earlier, later, factor, innerBefore, innerAfter,
    parts, inner, leftContext, rightContext, headTag⟩ :=
    located_occurrence coarse block before after coarseUniform
  have outerParts : decompose coarse word.toList = earlier ++ factor :: later := by
    rw [split]
    exact parts
  have outerMember := member_at _ earlier factor later outerParts
  have outerPositive := headTag.trans blockPositive
  have localSaturated : ∀ run ∈ decompose fine factor.toList,
      fine run.head = true → run = block := by
    intro run member runPositive
    exact saturated run
      (positive_refinement fine coarse word factor run contained outerMember outerPositive member runPositive)
      runPositive
  obtain ⟨insideBefore, insideAfter, fineParts, leftExact, rightExact⟩ :=
    saturated_occurrence_position fine block factor.toList innerBefore innerAfter
      inner uniform positive localSaturated
  refine ⟨earlier, later, insideBefore, insideAfter, factor,
    outerParts, outerPositive, fineParts, ?_, ?_⟩
  · rw [leftContext, leftExact]
  · rw [rightContext, rightExact]

theorem disjoint_tags (leftRoot rightRoot : Word Nat)
    (apart : ∀ value ∈ leftRoot.toList, value ∉ rightRoot.toList) :
    ∀ value, supportTag leftRoot value = true → supportTag rightRoot value = false := by
  intro value leftTag
  cases rightTag : supportTag rightRoot value with
  | false => rfl
  | true =>
      exact False.elim (apart value ((supportTag_true leftRoot value).mp leftTag)
        ((supportTag_true rightRoot value).mp rightTag))

theorem right_factors_on_union (leftRoot rightRoot word factor : Word Nat)
    (apart : ∀ value ∈ leftRoot.toList, value ∉ rightRoot.toList)
    (member : factor ∈ decompose
      (unionTag (supportTag leftRoot) (supportTag rightRoot)) word.toList)
    (positive : unionTag (supportTag leftRoot) (supportTag rightRoot) factor.head = true) :
    decompose (supportTag rightRoot) factor.toList = decompose (supportTag leftRoot) factor.toList := by
  have uniform := good_member_constant _ (decompose_good _ word.toList) member
  have complement : ∀ value ∈ factor.toList,
      supportTag rightRoot value = Bool.not (supportTag leftRoot value) := by
    intro value inside
    exact complement_on_union _ _ (disjoint_tags leftRoot rightRoot apart) value
      ((uniform value inside).trans positive)
  exact (decompose_congr_on (supportTag rightRoot)
    (fun value => Bool.not (supportTag leftRoot value)) factor.toList complement).trans
      (decompose_not (supportTag leftRoot) factor.toList)

theorem fine_block_images (leftRoot rightRoot word factor : Word Nat)
    (apart : ∀ value ∈ leftRoot.toList, value ∉ rightRoot.toList)
    (leftPerfect : CanonicalPerfect leftRoot word)
    (rightPerfect : CanonicalPerfect rightRoot word)
    (member : factor ∈ decompose
      (unionTag (supportTag leftRoot) (supportTag rightRoot)) word.toList)
    (positive : unionTag (supportTag leftRoot) (supportTag rightRoot) factor.head = true) :
    ∀ block ∈ decompose (supportTag leftRoot) factor.toList,
      image leftRoot rightRoot (blockCode (supportTag leftRoot) block) = block := by
  obtain ⟨_, _, blocks, _, _, actual, _, _, _, prescribed⟩ :=
    disjoint_perfect_roots_align leftRoot rightRoot word factor apart leftPerfect rightPerfect member positive
  intro block inside
  have inBlocks : block ∈ blocks := by rw [actual]; exact inside
  rcases prescribed block inBlocks with left | right
  · rw [blockCode, if_pos left.1]
    exact left.2.1.symm
  · have negative : supportTag leftRoot block.head ≠ true := by
      intro leftTag
      exact apart block.head ((supportTag_true leftRoot block.head).mp leftTag)
        ((supportTag_true rightRoot block.head).mp right.1)
    rw [blockCode, if_neg negative]
    exact right.2.1.symm

theorem encode_pieces_append (leftRoot rightRoot : Word Nat)
    (before after : List (Word Nat)) :
    encodePieces leftRoot rightRoot (before ++ after) =
      encodePieces leftRoot rightRoot before ++ encodePieces leftRoot rightRoot after := by
  exact List.flatMap_append

theorem encode_pieces_cons (leftRoot rightRoot factor : Word Nat) (after : List (Word Nat)) :
    encodePieces leftRoot rightRoot (factor :: after) =
      encodeFactor leftRoot rightRoot factor ++ encodePieces leftRoot rightRoot after := rfl

/-- A selected macro occurrence retains both decoded original contexts. -/
def MacroOccurrence (leftRoot rightRoot : Word Nat) (codes : List Nat) (code : Nat)
    (before after : List Nat) : Prop :=
  ∃ macroBefore macroAfter : List Nat,
    codes = macroBefore ++ code :: macroAfter ∧
    decodeLetters leftRoot rightRoot macroBefore = before ∧
    decodeLetters leftRoot rightRoot macroAfter = after

theorem occurrence_from_nested (leftRoot rightRoot word block factor : Word Nat)
    (apart : ∀ value ∈ leftRoot.toList, value ∉ rightRoot.toList)
    (leftPerfect : CanonicalPerfect leftRoot word)
    (rightPerfect : CanonicalPerfect rightRoot word)
    (earlier later insideBefore insideAfter : List (Word Nat))
    (before after : List Nat) (code : Nat)
    (outerParts : decompose (unionTag (supportTag leftRoot) (supportTag rightRoot)) word.toList =
      earlier ++ factor :: later)
    (positive : unionTag (supportTag leftRoot) (supportTag rightRoot) factor.head = true)
    (fineParts : decompose (supportTag leftRoot) factor.toList = insideBefore ++ block :: insideAfter)
    (leftContext : before = flatten earlier ++ flatten insideBefore)
    (rightContext : after = flatten insideAfter ++ flatten later)
    (codeEq : blockCode (supportTag leftRoot) block = code) :
    MacroOccurrence leftRoot rightRoot (macroLetters leftRoot rightRoot word) code before after := by
  have outerMember := member_at _ earlier factor later outerParts
  have images := fine_block_images leftRoot rightRoot word factor apart leftPerfect rightPerfect outerMember positive
  have selected : encodeFactor leftRoot rightRoot factor =
      encodeBlocks (supportTag leftRoot) insideBefore ++ code :: encodeBlocks (supportTag leftRoot) insideAfter := by
    rw [encodeFactor, if_pos positive, fineParts]
    simp only [encodeBlocks, List.map_append, List.map_cons, codeEq]
  refine ⟨encodePieces leftRoot rightRoot earlier ++ encodeBlocks (supportTag leftRoot) insideBefore,
    encodeBlocks (supportTag leftRoot) insideAfter ++ encodePieces leftRoot rightRoot later, ?_, ?_, ?_⟩
  · unfold macroLetters
    rw [outerParts, encode_pieces_append, encode_pieces_cons, selected]
    simp only [List.append_assoc, List.cons_append]
  · rw [decode_append]
    rw [decode_pieces leftRoot rightRoot word apart leftPerfect rightPerfect earlier
      (member_before _ earlier factor later outerParts)]
    rw [decode_blocks leftRoot rightRoot (supportTag leftRoot) insideBefore
      (fun value member => images value (member_before _ insideBefore block insideAfter fineParts value member))]
    exact leftContext.symm
  · rw [decode_append]
    rw [decode_blocks leftRoot rightRoot (supportTag leftRoot) insideAfter
      (fun value member => images value (member_after _ insideBefore block insideAfter fineParts value member))]
    rw [decode_pieces leftRoot rightRoot word apart leftPerfect rightPerfect later
      (member_after _ earlier factor later outerParts)]
    exact rightContext.symm

theorem left_square_occurrence_lifts (leftRoot rightRoot word : Word Nat)
    (apart : ∀ value ∈ leftRoot.toList, value ∉ rightRoot.toList)
    (leftPerfect : CanonicalPerfect leftRoot word)
    (rightPerfect : CanonicalPerfect rightRoot word)
    (before after : List Nat)
    (split : word.toList = before ++ ((leftRoot ++ leftRoot).toList ++ after)) :
    MacroOccurrence leftRoot rightRoot (macroLetters leftRoot rightRoot word) 0 before after := by
  have positive : supportTag leftRoot (leftRoot ++ leftRoot).head = true :=
    (supportTag_true leftRoot leftRoot.head).mpr (word_head_member leftRoot)
  obtain ⟨earlier, later, insideBefore, insideAfter, factor,
    outerParts, unionPositive, fineParts, leftContext, rightContext⟩ :=
    nested_occurrence_position (supportTag leftRoot)
      (unionTag (supportTag leftRoot) (supportTag rightRoot)) (leftRoot ++ leftRoot) word
      (union_left _ _) (root_square_constant leftRoot) positive leftPerfect.2 before after split
  apply occurrence_from_nested leftRoot rightRoot word (leftRoot ++ leftRoot) factor apart
    leftPerfect rightPerfect earlier later insideBefore insideAfter before after 0
    outerParts unionPositive fineParts leftContext rightContext
  rw [blockCode, if_pos positive]

theorem right_square_occurrence_lifts (leftRoot rightRoot word : Word Nat)
    (apart : ∀ value ∈ leftRoot.toList, value ∉ rightRoot.toList)
    (leftPerfect : CanonicalPerfect leftRoot word)
    (rightPerfect : CanonicalPerfect rightRoot word)
    (before after : List Nat)
    (split : word.toList = before ++ ((rightRoot ++ rightRoot).toList ++ after)) :
    MacroOccurrence leftRoot rightRoot (macroLetters leftRoot rightRoot word) 1 before after := by
  have positive : supportTag rightRoot (rightRoot ++ rightRoot).head = true :=
    (supportTag_true rightRoot rightRoot.head).mpr (word_head_member rightRoot)
  obtain ⟨earlier, later, insideBefore, insideAfter, factor,
    outerParts, unionPositive, fineParts, leftContext, rightContext⟩ :=
    nested_occurrence_position (supportTag rightRoot)
      (unionTag (supportTag leftRoot) (supportTag rightRoot)) (rightRoot ++ rightRoot) word
      (union_right _ _) (root_square_constant rightRoot) positive rightPerfect.2 before after split
  have sameFactors := right_factors_on_union leftRoot rightRoot word factor apart
    (member_at _ earlier factor later outerParts) unionPositive
  have leftParts : decompose (supportTag leftRoot) factor.toList =
      insideBefore ++ (rightRoot ++ rightRoot) :: insideAfter := sameFactors.symm.trans fineParts
  apply occurrence_from_nested leftRoot rightRoot word (rightRoot ++ rightRoot) factor apart
    leftPerfect rightPerfect earlier later insideBefore insideAfter before after 1
    outerParts unionPositive leftParts leftContext rightContext
  have negative : supportTag leftRoot (rightRoot ++ rightRoot).head ≠ true := by
    intro leftTag
    exact apart rightRoot.head ((supportTag_true leftRoot rightRoot.head).mp leftTag)
      (word_head_member rightRoot)
  rw [blockCode, if_neg negative]

theorem decode_cons (leftRoot rightRoot : Word Nat) (code : Nat) (rest : List Nat) :
    decodeLetters leftRoot rightRoot (code :: rest) =
      (image leftRoot rightRoot code).toList ++ decodeLetters leftRoot rightRoot rest := rfl

theorem decode_singleton (leftRoot rightRoot : Word Nat) (code : Nat) :
    decodeLetters leftRoot rightRoot [code] = (image leftRoot rightRoot code).toList := by
  exact List.append_nil _

theorem decode_eq_nil (leftRoot rightRoot : Word Nat) (codes : List Nat)
    (empty : decodeLetters leftRoot rightRoot codes = []) : codes = [] := by
  cases codes with
  | nil => rfl
  | cons first rest =>
      change (image leftRoot rightRoot first).head ::
        ((image leftRoot rightRoot first).tail ++ decodeLetters leftRoot rightRoot rest) = [] at empty
      cases empty

theorem cancel_front {α : Type} (front left right : List α)
    (equal : front ++ left = front ++ right) : left = right := by
  induction front with
  | nil => exact equal
  | cons first rest ih => exact ih (List.cons.inj equal).2

/-- Nonempty substitution images strictly preserve the order of cut positions
in a fixed word. This is not injectivity of substitution on arbitrary words. -/
theorem decoder_prefix_order (leftRoot rightRoot : Word Nat)
    (first second tailFirst tailSecond : List Nat)
    (same : first ++ tailFirst = second ++ tailSecond)
    (ordered : (decodeLetters leftRoot rightRoot first).length ≤
      (decodeLetters leftRoot rightRoot second).length) :
    ∃ middle, second = first ++ middle := by
  induction first generalizing second with
  | nil => exact ⟨second, rfl⟩
  | cons a first ih =>
      cases second with
      | nil =>
          have nonempty : 0 < (decodeLetters leftRoot rightRoot (a :: first)).length := by
            change 0 < ((image leftRoot rightRoot a).head ::
              ((image leftRoot rightRoot a).tail ++ decodeLetters leftRoot rightRoot first)).length
            simp only [List.length_cons]
            omega
          change (decodeLetters leftRoot rightRoot (a :: first)).length ≤ 0 at ordered
          omega
      | cons b second =>
          have equal : a = b := (List.cons.inj same).1
          subst b
          have tails := (List.cons.inj same).2
          simp only [decode_cons, List.length_append] at ordered
          have restOrdered : (decodeLetters leftRoot rightRoot first).length ≤
              (decodeLetters leftRoot rightRoot second).length := by omega
          obtain ⟨middle, restSplit⟩ := ih second tails restOrdered
          exact ⟨middle, congrArg (List.cons a) restSplit⟩

theorem gap_between_occurrences (leftRoot rightRoot : Word Nat) (codes : List Nat)
    (a b : Nat) (beforeA afterA beforeB afterB middle : List Nat)
    (first : codes = beforeA ++ a :: afterA)
    (second : codes = beforeB ++ b :: afterB)
    (contexts : decodeLetters leftRoot rightRoot beforeB =
      decodeLetters leftRoot rightRoot beforeA ++ ((image leftRoot rightRoot a).toList ++ middle)) :
    ∃ gap, beforeB = beforeA ++ a :: gap ∧ decodeLetters leftRoot rightRoot gap = middle := by
  have common : (beforeA ++ [a]) ++ afterA = beforeB ++ b :: afterB := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using first.symm.trans second
  have ordered : (decodeLetters leftRoot rightRoot (beforeA ++ [a])).length ≤
      (decodeLetters leftRoot rightRoot beforeB).length := by
    rw [decode_append, decode_singleton, contexts]
    simp only [List.length_append]
    omega
  obtain ⟨gap, extension⟩ := decoder_prefix_order leftRoot rightRoot
    (beforeA ++ [a]) beforeB afterA (b :: afterB) common ordered
  have actual : beforeB = beforeA ++ a :: gap := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using extension
  refine ⟨gap, actual, ?_⟩
  rw [actual, decode_append, decode_cons] at contexts
  exact cancel_front (image leftRoot rightRoot a).toList _ _
    (cancel_front (decodeLetters leftRoot rightRoot beforeA) _ _ contexts)

/-- The paper's G1/G2 statements use whole nonempty blocks, including the
actual adjacency in G1, not letter-membership projections. -/
def G1 (left right : Word Nat) (letters : List Nat) : Prop :=
  ∃ before middle after : List Nat,
    letters = before ++ (left.toList ++ (middle ++ (right.toList ++ (left.toList ++ after))))

def G2 (left right : Word Nat) (letters : List Nat) : Prop :=
  ∃ before first second third after : List Nat,
    letters = before ++ (left.toList ++ (first ++ (right.toList ++
      (second ++ (left.toList ++ (third ++ (right.toList ++ after)))))))

def LiftsOccurrences (leftRoot rightRoot : Word Nat) (letters codes : List Nat) (code : Nat) : Prop :=
  ∀ before after : List Nat,
    letters = before ++ ((image leftRoot rightRoot code).toList ++ after) →
    MacroOccurrence leftRoot rightRoot codes code before after

theorem g1_transport (leftRoot rightRoot : Word Nat) (letters codes : List Nat) (a b : Nat)
    (liftA : LiftsOccurrences leftRoot rightRoot letters codes a)
    (liftB : LiftsOccurrences leftRoot rightRoot letters codes b)
    (related : G1 (image leftRoot rightRoot a) (image leftRoot rightRoot b) letters) :
    C1 a b codes := by
  obtain ⟨before, middle, after, split⟩ := related
  let aWord : Word Nat := image leftRoot rightRoot a
  let bWord : Word Nat := image leftRoot rightRoot b
  let beforeB := before ++ (aWord.toList ++ middle)
  let beforeA2 := beforeB ++ bWord.toList
  have splitB : letters = beforeB ++ (bWord.toList ++ (aWord.toList ++ after)) := by
    simpa only [beforeB, List.append_assoc] using split
  have splitA2 : letters = beforeA2 ++ (aWord.toList ++ after) := by
    simpa only [beforeA2, beforeB, List.append_assoc] using split
  obtain ⟨p0, q0, first, firstBefore, _⟩ :=
    liftA before (middle ++ (bWord.toList ++ (aWord.toList ++ after))) split
  obtain ⟨p1, q1, second, secondBefore, _⟩ := liftB beforeB (aWord.toList ++ after) splitB
  obtain ⟨p2, q2, third, thirdBefore, _⟩ := liftA beforeA2 after splitA2
  have firstContext : decodeLetters leftRoot rightRoot p1 =
      decodeLetters leftRoot rightRoot p0 ++ (aWord.toList ++ middle) := by
    rw [firstBefore, secondBefore]
  have secondContext : decodeLetters leftRoot rightRoot p2 =
      decodeLetters leftRoot rightRoot p1 ++ (bWord.toList ++ []) := by
    rw [secondBefore, thirdBefore, List.append_nil]
  obtain ⟨gap1, positions1, _⟩ := gap_between_occurrences leftRoot rightRoot codes a b
    p0 q0 p1 q1 middle first second firstContext
  obtain ⟨gap2, positions2, decoded2⟩ := gap_between_occurrences leftRoot rightRoot codes b a
    p1 q1 p2 q2 [] second third secondContext
  have adjacent : gap2 = [] := decode_eq_nil leftRoot rightRoot gap2 decoded2
  refine ⟨p0, gap1, q2, ?_⟩
  rw [third, positions2, adjacent, positions1]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem empty_sublist (letters : List Nat) : ([] : List Nat).Sublist letters := by
  induction letters with
  | nil => exact List.Sublist.slnil
  | cons first rest ih => exact List.Sublist.cons first ih

theorem add_prefix_sublist (before short long : List Nat) (member : short.Sublist long) :
    short.Sublist (before ++ long) := by
  induction before with
  | nil => exact member
  | cons first rest ih => exact List.Sublist.cons first ih

theorem c2_of_split (a b : Nat) (letters before first second third after : List Nat)
    (split : letters = before ++ a :: (first ++ b :: (second ++ a :: (third ++ b :: after)))) :
    C2 a b letters := by
  rw [split]
  exact add_prefix_sublist before _ _ (List.Sublist.cons₂ a
    (add_prefix_sublist first _ _ (List.Sublist.cons₂ b
      (add_prefix_sublist second _ _ (List.Sublist.cons₂ a
        (add_prefix_sublist third _ _ (List.Sublist.cons₂ b (empty_sublist after))))))))

theorem g2_transport (leftRoot rightRoot : Word Nat) (letters codes : List Nat) (a b : Nat)
    (liftA : LiftsOccurrences leftRoot rightRoot letters codes a)
    (liftB : LiftsOccurrences leftRoot rightRoot letters codes b)
    (related : G2 (image leftRoot rightRoot a) (image leftRoot rightRoot b) letters) :
    C2 a b codes := by
  obtain ⟨before, firstGap, secondGap, thirdGap, after, split⟩ := related
  let aWord : Word Nat := image leftRoot rightRoot a
  let bWord : Word Nat := image leftRoot rightRoot b
  let beforeB := before ++ (aWord.toList ++ firstGap)
  let beforeA2 := beforeB ++ (bWord.toList ++ secondGap)
  let beforeB2 := beforeA2 ++ (aWord.toList ++ thirdGap)
  have splitB : letters = beforeB ++ (bWord.toList ++
      (secondGap ++ (aWord.toList ++ (thirdGap ++ (bWord.toList ++ after))))) := by
    simpa only [beforeB, List.append_assoc] using split
  have splitA2 : letters = beforeA2 ++ (aWord.toList ++ (thirdGap ++ (bWord.toList ++ after))) := by
    simpa only [beforeA2, beforeB, List.append_assoc] using split
  have splitB2 : letters = beforeB2 ++ (bWord.toList ++ after) := by
    simpa only [beforeB2, beforeA2, beforeB, List.append_assoc] using split
  obtain ⟨p0, q0, first, firstBefore, _⟩ := liftA before
    (firstGap ++ (bWord.toList ++ (secondGap ++ (aWord.toList ++ (thirdGap ++ (bWord.toList ++ after)))))) split
  obtain ⟨p1, q1, second, secondBefore, _⟩ := liftB beforeB
    (secondGap ++ (aWord.toList ++ (thirdGap ++ (bWord.toList ++ after)))) splitB
  obtain ⟨p2, q2, third, thirdBefore, _⟩ := liftA beforeA2 (thirdGap ++ (bWord.toList ++ after)) splitA2
  obtain ⟨p3, q3, fourth, fourthBefore, _⟩ := liftB beforeB2 after splitB2
  have firstContext : decodeLetters leftRoot rightRoot p1 =
      decodeLetters leftRoot rightRoot p0 ++ (aWord.toList ++ firstGap) := by
    rw [firstBefore, secondBefore]
  have secondContext : decodeLetters leftRoot rightRoot p2 =
      decodeLetters leftRoot rightRoot p1 ++ (bWord.toList ++ secondGap) := by
    rw [secondBefore, thirdBefore]
  have thirdContext : decodeLetters leftRoot rightRoot p3 =
      decodeLetters leftRoot rightRoot p2 ++ (aWord.toList ++ thirdGap) := by
    rw [thirdBefore, fourthBefore]
  obtain ⟨gap1, positions1, _⟩ := gap_between_occurrences leftRoot rightRoot codes a b
    p0 q0 p1 q1 firstGap first second firstContext
  obtain ⟨gap2, positions2, _⟩ := gap_between_occurrences leftRoot rightRoot codes b a
    p1 q1 p2 q2 secondGap second third secondContext
  obtain ⟨gap3, positions3, _⟩ := gap_between_occurrences leftRoot rightRoot codes a b
    p2 q2 p3 q3 thirdGap third fourth thirdContext
  apply c2_of_split a b codes p0 gap1 gap2 gap3 q3
  rw [fourth, positions3, positions2, positions1]
  simp only [List.append_assoc, List.cons_append]

def GeneralizedRelated (leftRoot rightRoot word : Word Nat) : Prop :=
  G1 (leftRoot ++ leftRoot) (rightRoot ++ rightRoot) word.toList ∨
  G1 (rightRoot ++ rightRoot) (leftRoot ++ leftRoot) word.toList ∨
  G2 (leftRoot ++ leftRoot) (rightRoot ++ rightRoot) word.toList ∨
  G2 (rightRoot ++ rightRoot) (leftRoot ++ leftRoot) word.toList

/-- Actual generalized block witnesses yield the binary relation in the
constructed macro word. No second-occurrence/count premise is supplied. -/
theorem generalized_related_macro (leftRoot rightRoot word : Word Nat)
    (apart : ∀ value ∈ leftRoot.toList, value ∉ rightRoot.toList)
    (leftPerfect : CanonicalPerfect leftRoot word)
    (rightPerfect : CanonicalPerfect rightRoot word)
    (related : GeneralizedRelated leftRoot rightRoot word) :
    PairRelated 0 1 (macroLetters leftRoot rightRoot word) := by
  have liftLeft : LiftsOccurrences leftRoot rightRoot word.toList
      (macroLetters leftRoot rightRoot word) 0 :=
    left_square_occurrence_lifts leftRoot rightRoot word apart leftPerfect rightPerfect
  have liftRight : LiftsOccurrences leftRoot rightRoot word.toList
      (macroLetters leftRoot rightRoot word) 1 :=
    right_square_occurrence_lifts leftRoot rightRoot word apart leftPerfect rightPerfect
  rcases related with first | second | third | fourth
  · exact Or.inl (g1_transport leftRoot rightRoot _ _ 0 1 liftLeft liftRight first)
  · exact Or.inr (Or.inl (g1_transport leftRoot rightRoot _ _ 1 0 liftRight liftLeft second))
  · exact Or.inr (Or.inr (Or.inl (g2_transport leftRoot rightRoot _ _ 0 1 liftLeft liftRight third)))
  · exact Or.inr (Or.inr (Or.inr (g2_transport leftRoot rightRoot _ _ 1 0 liftRight liftLeft fourth)))

theorem generalized_related_macroWord (leftRoot rightRoot word : Word Nat)
    (apart : ∀ value ∈ leftRoot.toList, value ∉ rightRoot.toList)
    (leftPerfect : CanonicalPerfect leftRoot word)
    (rightPerfect : CanonicalPerfect rightRoot word)
    (related : GeneralizedRelated leftRoot rightRoot word) :
    PairRelated 0 1 (macroWord leftRoot rightRoot word apart leftPerfect rightPerfect).toList := by
  rw [macroWord_toList]
  exact generalized_related_macro leftRoot rightRoot word apart leftPerfect rightPerfect related

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroWitnesses

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroWitnesses.member_before
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroWitnesses.member_after
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroWitnesses.member_at
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroWitnesses.nested_occurrence_position
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroWitnesses.disjoint_tags
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroWitnesses.right_factors_on_union
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroWitnesses.fine_block_images
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroWitnesses.encode_pieces_append
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroWitnesses.encode_pieces_cons
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroWitnesses.occurrence_from_nested
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroWitnesses.left_square_occurrence_lifts
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroWitnesses.right_square_occurrence_lifts
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroWitnesses.decode_cons
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroWitnesses.decode_singleton
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroWitnesses.decode_eq_nil
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroWitnesses.cancel_front
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroWitnesses.decoder_prefix_order
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroWitnesses.gap_between_occurrences
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroWitnesses.g1_transport
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroWitnesses.empty_sublist
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroWitnesses.add_prefix_sublist
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroWitnesses.c2_of_split
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroWitnesses.g2_transport
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroWitnesses.generalized_related_macro
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroWitnesses.generalized_related_macroWord
