import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedBlockAlignment

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceMacro

open MaximalFactors FactorBoundaries FactorContexts CanonicalSquareCover BlockAlignment

theorem foldr_join_run (classify : Nat → Bool) (first : Nat) (later : List Nat)
    (run : Word Nat) (rest : List (Word Nat))
    (uniform : ∀ value ∈ later, classify value = classify first)
    (same : classify first = classify run.head) :
    (first :: later).foldr (insertLetter classify) (run :: rest) =
      (⟨first, later ++ run.toList⟩ : Word Nat) :: rest := by
  induction later generalizing first with
  | nil =>
      change insertLetter classify first (run :: rest) = _
      rw [insertLetter, if_pos same]
      rfl
  | cons second tail ih =>
      have secondSame := uniform second (List.mem_cons.mpr (Or.inl rfl))
      have tailUniform : ∀ value ∈ tail, classify value = classify second := by
        intro value member
        exact (uniform value (List.mem_cons.mpr (Or.inr member))).trans secondSame.symm
      change insertLetter classify first
        ((second :: tail).foldr (insertLetter classify) (run :: rest)) = _
      rw [ih second tailUniform (secondSame.trans same)]
      have boundary : classify first =
          classify (⟨second, tail ++ run.toList⟩ : Word Nat).head := secondSame.symm
      rw [insertLetter, if_pos boundary]
      rfl

theorem insert_before_run (classify : Nat → Bool) (letter : Nat)
    (first run : Word Nat) (middle later : List (Word Nat)) :
    insertLetter classify letter ((first :: middle) ++ run :: later) =
      insertLetter classify letter (first :: middle) ++ run :: later := by
  by_cases same : classify letter = classify first.head
  · simp only [List.cons_append, insertLetter, if_pos same]
  · simp only [List.cons_append, insertLetter, if_neg same]

/-- A selected literal occurrence is contained in one computed run. The two
internal extensions and BOTH original exterior strings are recorded. -/
def Located (classify : Nat → Bool) (piece : Word Nat) (before after : List Nat) : Prop :=
  ∃ earlier later : List (Word Nat), ∃ run : Word Nat, ∃ insideBefore insideAfter : List Nat,
    decompose classify (before ++ (piece.toList ++ after)) = earlier ++ run :: later ∧
    run.toList = insideBefore ++ (piece.toList ++ insideAfter) ∧
    before = flatten earlier ++ insideBefore ∧
    after = insideAfter ++ flatten later ∧
    classify run.head = classify piece.head

theorem located_at_start (classify : Nat → Bool) (piece : Word Nat) (after : List Nat)
    (uniform : Constant classify piece) : Located classify piece [] after := by
  have tailUniform : ∀ value ∈ piece.tail, classify value = classify piece.head :=
    fun value member => uniform value (List.mem_cons.mpr (Or.inr member))
  cases split : decompose classify after with
  | nil =>
      have afterEmpty : after = [] := by
        have covered := flatten_decompose classify after
        rw [split] at covered
        exact covered.symm
      refine ⟨[], [], piece, [], [], ?_, ?_, rfl, afterEmpty, rfl⟩
      · change decompose classify (piece.toList ++ after) = [piece]
        rw [decompose_append, split]
        exact foldr_run classify piece.head piece.tail [] tailUniform True.intro
      · exact (List.append_nil piece.toList).symm
  | cons first rest =>
      have afterSplit : after = first.toList ++ flatten rest := by
        have covered := flatten_decompose classify after
        rw [split] at covered
        exact covered.symm
      by_cases same : classify piece.head = classify first.head
      · refine ⟨[], rest, piece ++ first, [], first.toList, ?_, ?_, rfl, afterSplit, rfl⟩
        · change decompose classify (piece.toList ++ after) = (piece ++ first) :: rest
          rw [decompose_append, split]
          exact foldr_join_run classify piece.head piece.tail first rest tailUniform same
        · exact Word.toList_append piece first
      · refine ⟨[], first :: rest, piece, [], [], ?_, ?_, rfl, afterSplit, rfl⟩
        · change decompose classify (piece.toList ++ after) = piece :: first :: rest
          rw [decompose_append, split]
          exact foldr_run classify piece.head piece.tail (first :: rest) tailUniform same
        · exact (List.append_nil piece.toList).symm

theorem located_occurrence (classify : Nat → Bool) (piece : Word Nat)
    (before after : List Nat) (uniform : Constant classify piece) :
    Located classify piece before after := by
  induction before with
  | nil => exact located_at_start classify piece after uniform
  | cons letter before ih =>
      obtain ⟨earlier, later, run, insideBefore, insideAfter,
        parts, inside, leftContext, rightContext, sameTag⟩ := ih
      cases earlier with
      | nil =>
          have atRun : decompose classify (before ++ (piece.toList ++ after)) = run :: later := by
            simpa only [List.nil_append] using parts
          have beforeEq : before = insideBefore := leftContext
          by_cases same : classify letter = classify run.head
          · let extended : Word Nat := ⟨letter, run.toList⟩
            refine ⟨[], later, extended, letter :: insideBefore, insideAfter,
              ?_, ?_, ?_, rightContext, same.trans sameTag⟩
            · change insertLetter classify letter
                (decompose classify (before ++ (piece.toList ++ after))) = extended :: later
              rw [atRun, insertLetter, if_pos same]
            · change letter :: run.toList = (letter :: insideBefore) ++ (piece.toList ++ insideAfter)
              rw [inside]
              rfl
            · exact congrArg (List.cons letter) beforeEq
          · refine ⟨[Word.singleton letter], later, run, insideBefore, insideAfter,
              ?_, inside, ?_, rightContext, sameTag⟩
            · change insertLetter classify letter
                (decompose classify (before ++ (piece.toList ++ after))) =
                  Word.singleton letter :: run :: later
              rw [atRun, insertLetter, if_neg same]
            · exact congrArg (List.cons letter) beforeEq
      | cons first middle =>
          refine ⟨insertLetter classify letter (first :: middle), later, run,
            insideBefore, insideAfter, ?_, inside, ?_, rightContext, sameTag⟩
          · change insertLetter classify letter
              (decompose classify (before ++ (piece.toList ++ after))) = _
            rw [parts]
            exact insert_before_run classify letter first run middle later
          · rw [flatten_insert]
            exact congrArg (List.cons letter) leftContext

/-- Saturation fixes the length of the containing run. Thus a chosen full
block occurrence has no clipped extension, even when equal blocks repeat. -/
theorem saturated_occurrence_position (classify : Nat → Bool) (block : Word Nat)
    (letters before after : List Nat)
    (split : letters = before ++ (block.toList ++ after))
    (uniform : Constant classify block) (positive : classify block.head = true)
    (saturated : ∀ run ∈ decompose classify letters,
      classify run.head = true → run = block) :
    ∃ earlier later : List (Word Nat),
      decompose classify letters = earlier ++ block :: later ∧
      flatten earlier = before ∧ flatten later = after := by
  obtain ⟨earlier, later, run, insideBefore, insideAfter,
    parts, inside, leftContext, rightContext, sameTag⟩ :=
    located_occurrence classify block before after uniform
  have member : run ∈ decompose classify letters := by
    rw [split, parts]
    exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
  have equal : run = block := saturated run member (sameTag.trans positive)
  have size := congrArg List.length inside
  rw [equal] at size
  simp only [List.length_append] at size
  have emptyBefore : insideBefore = [] := by
    cases insideBefore with
    | nil => rfl
    | cons first rest =>
        simp only [List.length_cons] at size
        omega
  have emptyAfter : insideAfter = [] := by
    cases insideAfter with
    | nil => rfl
    | cons first rest =>
        simp only [List.length_cons] at size
        omega
  subst insideBefore
  subst insideAfter
  refine ⟨earlier, later, ?_, ?_, ?_⟩
  · rw [split, parts, equal]
  · simpa only [List.append_nil] using leftContext.symm
  · exact rightContext.symm

theorem root_square_constant (root : Word Nat) :
    Constant (supportTag root) (root ++ root) := by
  intro value member
  have belongs : value ∈ root.toList := by
    rw [Word.toList_append] at member
    rcases List.mem_append.mp member with first | second
    · exact first
    · exact second
  have valueTrue := (supportTag_true root value).mpr belongs
  have headTrue := (supportTag_true root root.head).mpr (word_head_member root)
  exact valueTrue.trans headTrue.symm

theorem root_square_occurrence_position (root word : Word Nat)
    (perfect : CanonicalPerfect root word) (before after : List Nat)
    (split : word.toList = before ++ ((root ++ root).toList ++ after)) :
    ∃ earlier later : List (Word Nat),
      decompose (supportTag root) word.toList = earlier ++ (root ++ root) :: later ∧
      flatten earlier = before ∧ flatten later = after := by
  exact saturated_occurrence_position (supportTag root) (root ++ root) word.toList before after
    split (root_square_constant root)
    ((supportTag_true root root.head).mpr (word_head_member root)) perfect.2

/-- Macro variables 0/1 denote the whole squares. All complementary letters
are retained with disjoint fresh codes, and all substitution images are nonempty. -/
def image (leftRoot rightRoot : Word Nat) : Nat → Word Nat
  | 0 => leftRoot ++ leftRoot
  | 1 => rightRoot ++ rightRoot
  | Nat.succ (Nat.succ value) => Word.singleton value

def decodeLetters (leftRoot rightRoot : Word Nat) (letters : List Nat) : List Nat :=
  letters.flatMap (fun value => (image leftRoot rightRoot value).toList)

def blockCode (left : Nat → Bool) (block : Word Nat) : Nat :=
  if left block.head = true then 0 else 1

def encodeBlocks (left : Nat → Bool) (blocks : List (Word Nat)) : List Nat :=
  blocks.map (blockCode left)

def encodeFactor (leftRoot rightRoot factor : Word Nat) : List Nat :=
  if unionTag (supportTag leftRoot) (supportTag rightRoot) factor.head = true then
    encodeBlocks (supportTag leftRoot) (decompose (supportTag leftRoot) factor.toList)
  else factor.toList.map (fun value => value + 2)

def encodePieces (leftRoot rightRoot : Word Nat) (pieces : List (Word Nat)) : List Nat :=
  pieces.flatMap (encodeFactor leftRoot rightRoot)

def macroLetters (leftRoot rightRoot word : Word Nat) : List Nat :=
  encodePieces leftRoot rightRoot
    (decompose (unionTag (supportTag leftRoot) (supportTag rightRoot)) word.toList)

theorem decode_append (leftRoot rightRoot : Word Nat) (first second : List Nat) :
    decodeLetters leftRoot rightRoot (first ++ second) =
      decodeLetters leftRoot rightRoot first ++ decodeLetters leftRoot rightRoot second := by
  exact List.flatMap_append

theorem decode_complement (leftRoot rightRoot : Word Nat) (letters : List Nat) :
    decodeLetters leftRoot rightRoot (letters.map (fun value => value + 2)) = letters := by
  induction letters with
  | nil => rfl
  | cons first rest ih =>
      change first :: decodeLetters leftRoot rightRoot (rest.map (fun value => value + 2)) = first :: rest
      rw [ih]

theorem decode_blocks (leftRoot rightRoot : Word Nat) (left : Nat → Bool)
    (blocks : List (Word Nat))
    (images : ∀ block ∈ blocks, image leftRoot rightRoot (blockCode left block) = block) :
    decodeLetters leftRoot rightRoot (encodeBlocks left blocks) = flatten blocks := by
  induction blocks with
  | nil => rfl
  | cons first rest ih =>
      change (image leftRoot rightRoot (blockCode left first)).toList ++
        decodeLetters leftRoot rightRoot (encodeBlocks left rest) = first.toList ++ flatten rest
      rw [images first (List.mem_cons.mpr (Or.inl rfl))]
      rw [ih (fun block member => images block (List.mem_cons.mpr (Or.inr member)))]

theorem decode_factor (leftRoot rightRoot word factor : Word Nat)
    (apart : ∀ value ∈ leftRoot.toList, value ∉ rightRoot.toList)
    (leftPerfect : CanonicalPerfect leftRoot word)
    (rightPerfect : CanonicalPerfect rightRoot word)
    (member : factor ∈ decompose
      (unionTag (supportTag leftRoot) (supportTag rightRoot)) word.toList) :
    decodeLetters leftRoot rightRoot (encodeFactor leftRoot rightRoot factor) = factor.toList := by
  cases tag : unionTag (supportTag leftRoot) (supportTag rightRoot) factor.head with
  | false =>
      have negative : unionTag (supportTag leftRoot) (supportTag rightRoot) factor.head ≠ true := by
        rw [tag]
        decide
      rw [encodeFactor, if_neg negative]
      exact decode_complement leftRoot rightRoot factor.toList
  | true =>
      obtain ⟨before, after, blocks, _, _, actual, covered, _, _, prescribed⟩ :=
        disjoint_perfect_roots_align leftRoot rightRoot word factor apart leftPerfect rightPerfect member tag
      have images : ∀ block ∈ blocks,
          image leftRoot rightRoot (blockCode (supportTag leftRoot) block) = block := by
        intro block inside
        rcases prescribed block inside with left | right
        · rw [blockCode, if_pos left.1]
          exact left.2.1.symm
        · have negative : supportTag leftRoot block.head ≠ true := by
            intro positive
            exact apart block.head ((supportTag_true leftRoot block.head).mp positive)
              ((supportTag_true rightRoot block.head).mp right.1)
          rw [blockCode, if_neg negative]
          exact right.2.1.symm
      rw [encodeFactor, if_pos tag, ← actual]
      exact (decode_blocks leftRoot rightRoot (supportTag leftRoot) blocks images).trans covered

theorem decode_pieces (leftRoot rightRoot word : Word Nat)
    (apart : ∀ value ∈ leftRoot.toList, value ∉ rightRoot.toList)
    (leftPerfect : CanonicalPerfect leftRoot word)
    (rightPerfect : CanonicalPerfect rightRoot word)
    (pieces : List (Word Nat))
    (members : ∀ piece ∈ pieces, piece ∈ decompose
      (unionTag (supportTag leftRoot) (supportTag rightRoot)) word.toList) :
    decodeLetters leftRoot rightRoot (encodePieces leftRoot rightRoot pieces) = flatten pieces := by
  induction pieces with
  | nil => rfl
  | cons first rest ih =>
      change decodeLetters leftRoot rightRoot
        (encodeFactor leftRoot rightRoot first ++ encodePieces leftRoot rightRoot rest) =
          first.toList ++ flatten rest
      rw [decode_append]
      rw [decode_factor leftRoot rightRoot word first apart leftPerfect rightPerfect
        (members first (List.mem_cons.mpr (Or.inl rfl)))]
      rw [ih (fun piece member => members piece (List.mem_cons.mpr (Or.inr member)))]

theorem macro_roundtrip (leftRoot rightRoot word : Word Nat)
    (apart : ∀ value ∈ leftRoot.toList, value ∉ rightRoot.toList)
    (leftPerfect : CanonicalPerfect leftRoot word)
    (rightPerfect : CanonicalPerfect rightRoot word) :
    decodeLetters leftRoot rightRoot (macroLetters leftRoot rightRoot word) = word.toList := by
  exact (decode_pieces leftRoot rightRoot word apart leftPerfect rightPerfect
    (decompose (unionTag (supportTag leftRoot) (supportTag rightRoot)) word.toList)
    (fun _ member => member)).trans
      (flatten_decompose (unionTag (supportTag leftRoot) (supportTag rightRoot)) word.toList)

theorem macro_nonempty (leftRoot rightRoot word : Word Nat)
    (apart : ∀ value ∈ leftRoot.toList, value ∉ rightRoot.toList)
    (leftPerfect : CanonicalPerfect leftRoot word)
    (rightPerfect : CanonicalPerfect rightRoot word) :
    macroLetters leftRoot rightRoot word ≠ [] := by
  intro empty
  have roundtrip := macro_roundtrip leftRoot rightRoot word apart leftPerfect rightPerfect
  rw [empty] at roundtrip
  exact piece_nonempty word roundtrip.symm

def nonemptyWord : (letters : List Nat) → letters ≠ [] → Word Nat
  | [], nonempty => False.elim (nonempty rfl)
  | first :: rest, _ => ⟨first, rest⟩

theorem nonemptyWord_toList (letters : List Nat) (nonempty : letters ≠ []) :
    (nonemptyWord letters nonempty).toList = letters := by
  cases letters with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest => rfl

def macroWord (leftRoot rightRoot word : Word Nat)
    (apart : ∀ value ∈ leftRoot.toList, value ∉ rightRoot.toList)
    (leftPerfect : CanonicalPerfect leftRoot word)
    (rightPerfect : CanonicalPerfect rightRoot word) : Word Nat :=
  nonemptyWord (macroLetters leftRoot rightRoot word)
    (macro_nonempty leftRoot rightRoot word apart leftPerfect rightPerfect)

theorem macroWord_toList (leftRoot rightRoot word : Word Nat)
    (apart : ∀ value ∈ leftRoot.toList, value ∉ rightRoot.toList)
    (leftPerfect : CanonicalPerfect leftRoot word)
    (rightPerfect : CanonicalPerfect rightRoot word) :
    (macroWord leftRoot rightRoot word apart leftPerfect rightPerfect).toList =
      macroLetters leftRoot rightRoot word :=
  nonemptyWord_toList _ _

/-- The macro renderer is constructed and proved, never an input assumption. -/
theorem macroWord_bind (leftRoot rightRoot word : Word Nat)
    (apart : ∀ value ∈ leftRoot.toList, value ∉ rightRoot.toList)
    (leftPerfect : CanonicalPerfect leftRoot word)
    (rightPerfect : CanonicalPerfect rightRoot word) :
    (macroWord leftRoot rightRoot word apart leftPerfect rightPerfect).bind
      (image leftRoot rightRoot) = word := by
  apply Word.toList_injective
  rw [Word.toList_bind, macroWord_toList]
  exact macro_roundtrip leftRoot rightRoot word apart leftPerfect rightPerfect

theorem macro_derivation_lifts (leftRoot rightRoot word normal : Word Nat)
    (apart : ∀ value ∈ leftRoot.toList, value ∉ rightRoot.toList)
    (leftPerfect : CanonicalPerfect leftRoot word)
    (rightPerfect : CanonicalPerfect rightRoot word)
    (step : Derives basis (macroWord leftRoot rightRoot word apart leftPerfect rightPerfect) normal) :
    Derives basis word (normal.bind (image leftRoot rightRoot)) := by
  have lifted := Derives.subst step (image leftRoot rightRoot)
  rw [macroWord_bind] at lifted
  exact lifted

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceMacro

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceMacro.foldr_join_run
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceMacro.insert_before_run
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceMacro.located_at_start
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceMacro.located_occurrence
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceMacro.saturated_occurrence_position
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceMacro.root_square_constant
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceMacro.root_square_occurrence_position
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceMacro.decode_append
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceMacro.decode_complement
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceMacro.decode_blocks
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceMacro.decode_factor
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceMacro.decode_pieces
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceMacro.macro_roundtrip
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceMacro.macro_nonempty
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceMacro.nonemptyWord_toList
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceMacro.macroWord_toList
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceMacro.macroWord_bind
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceMacro.macro_derivation_lifts
