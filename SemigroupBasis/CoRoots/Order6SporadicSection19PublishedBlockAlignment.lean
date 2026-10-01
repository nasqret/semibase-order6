import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedSquarePermutation

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BlockAlignment

open MaximalFactors FactorBoundaries FactorContexts CanonicalSquareCover

/-- Tests of the actual first/last factor, vacuous only when the context is empty. -/
def FirstOK {α : Type} (test : α → Prop) (pieces : List α) : Prop :=
  ∀ first rest, pieces = first :: rest → test first

def LastOK {α : Type} (test : α → Prop) (pieces : List α) : Prop :=
  FirstOK test pieces.reverse

theorem firstOK_append {α : Type} (test : α → Prop) (left right : List α)
    (leftOK : FirstOK test left) (rightOK : FirstOK test right) :
    FirstOK test (left ++ right) := by
  intro first rest split
  cases left with
  | nil => exact rightOK first rest split
  | cons head tail =>
      have equal : head = first := (List.cons.inj split).1
      have tested : test head := leftOK head tail rfl
      exact equal ▸ tested

theorem lastOK_append {α : Type} (test : α → Prop) (left right : List α)
    (leftOK : LastOK test left) (rightOK : LastOK test right) :
    LastOK test (left ++ right) := by
  exact (by
    simpa only [LastOK, List.reverse_append] using
      firstOK_append test right.reverse left.reverse rightOK leftOK)

theorem lastOK_of_witness {α : Type} (test : α → Prop) (pieces : List α)
    (witness : ∀ earlier last, pieces = earlier ++ [last] → test last) :
    LastOK test pieces := by
  intro last earlier split
  have mirrored := congrArg List.reverse split
  have actual : pieces = earlier.reverse ++ [last] := by
    simpa only [List.reverse_reverse, List.reverse_cons] using mirrored
  exact witness earlier.reverse last actual

theorem lastOK_witness {α : Type} (test : α → Prop) (pieces : List α)
    (good : LastOK test pieces) (earlier : List α) (last : α)
    (split : pieces = earlier ++ [last]) : test last := by
  apply good last earlier.reverse
  rw [split, List.reverse_append]
  rfl

theorem nil_or_last {α : Type} (pieces : List α) :
    pieces = [] ∨ ∃ earlier last, pieces = earlier ++ [last] := by
  induction pieces with
  | nil => exact Or.inl rfl
  | cons first rest ih =>
      right
      rcases ih with empty | last
      · subst rest
        exact ⟨[], first, rfl⟩
      · obtain ⟨earlier, last, split⟩ := last
        exact ⟨first :: earlier, last, by rw [split]; rfl⟩

theorem bool_eq_of_ne (left right other : Bool)
    (leftNe : left ≠ other) (rightNe : right ≠ other) : left = right := by
  cases left <;> cases right <;> cases other
  all_goals first | rfl | exact False.elim (leftNe rfl) | exact False.elim (rightNe rfl)

/-- Inserting an arbitrary prefix can change the first run, never its protected tail. -/
theorem foldr_protected_tail (classify : Nat → Bool) (letters : List Nat)
    (first : Word Nat) (rest : List (Word Nat)) :
    ∃ head before, letters.foldr (insertLetter classify) (first :: rest) =
      head :: (before ++ rest) := by
  induction letters with
  | nil => exact ⟨first, [], rfl⟩
  | cons letter later ih =>
      obtain ⟨head, before, split⟩ := ih
      by_cases same : classify letter = classify head.head
      · refine ⟨(⟨letter, head.toList⟩ : Word Nat), before, ?_⟩
        simp only [List.foldr, split, insertLetter, if_pos same]
      · refine ⟨Word.singleton letter, head :: before, ?_⟩
        simp only [List.foldr, split, insertLetter, if_neg same, List.cons_append]

theorem decompose_first_head (classify : Nat → Bool) (first : Nat) (later : List Nat)
    (piece : Word Nat) (rest : List (Word Nat))
    (split : decompose classify (first :: later) = piece :: rest) : piece.head = first := by
  have covered := flatten_decompose classify (first :: later)
  rw [split] at covered
  exact (List.cons.inj covered).1

theorem separated_after (classify : Nat → Bool) (piece : Word Nat)
    (after : List (Word Nat))
    (boundary : FirstOK (fun next =>
      ∀ value ∈ next.toList, classify value ≠ classify piece.head) after) :
    SeparatedHead classify piece.head (decompose classify (flatten after)) := by
  cases after with
  | nil => trivial
  | cons next later =>
      have different := boundary next later rfl next.head (word_head_member next)
      cases split : decompose classify (flatten (next :: later)) with
      | nil =>
          have covered := flatten_decompose classify (flatten (next :: later))
          rw [split] at covered
          cases covered
      | cons head rest =>
          have headEqual : head.head = next.head :=
            decompose_first_head classify next.head (next.tail ++ flatten later) head rest split
          change classify piece.head ≠ classify head.head
          intro equal
          exact different ((congrArg classify headEqual).symm.trans equal.symm)

/-- A literal homogeneous factor with both actual adjacent boundaries is a
canonical maximal run. No caller-supplied decomposition of the whole word is assumed. -/
theorem canonical_member_of_boundaries (classify : Nat → Bool) (letters : List Nat)
    (piece : Word Nat) (before after : List (Word Nat))
    (split : letters = flatten before ++ (piece.toList ++ flatten after))
    (uniform : Constant classify piece)
    (leftBoundary : LastOK (fun previous =>
      ∀ value ∈ previous.toList, classify value ≠ classify piece.head) before)
    (rightBoundary : FirstOK (fun next =>
      ∀ value ∈ next.toList, classify value ≠ classify piece.head) after) :
    piece ∈ decompose classify letters := by
  have core : decompose classify (piece.toList ++ flatten after) =
      piece :: decompose classify (flatten after) := by
    rw [decompose_append]
    exact foldr_run classify piece.head piece.tail (decompose classify (flatten after))
      (fun value member => uniform value (List.mem_cons.mpr (Or.inr member)))
      (separated_after classify piece after rightBoundary)
  rw [split, decompose_append, core]
  rcases nil_or_last before with empty | last
  · subst before
    exact List.mem_cons.mpr (Or.inl rfl)
  · obtain ⟨earlier, last, beforeSplit⟩ := last
    have different := lastOK_witness _ before leftBoundary earlier last beforeSplit
    have lastUniform : ∀ value ∈ last.tail, classify value = classify last.head := by
      intro value member
      exact bool_eq_of_ne _ _ (classify piece.head)
        (different value (List.mem_cons.mpr (Or.inr member)))
        (different last.head (word_head_member last))
    have lastFold : last.toList.foldr (insertLetter classify)
        (piece :: decompose classify (flatten after)) =
        last :: piece :: decompose classify (flatten after) :=
      foldr_run classify last.head last.tail
        (piece :: decompose classify (flatten after)) lastUniform
        (different last.head (word_head_member last))
    rw [beforeSplit, FactorBoundaries.flatten_append]
    simp only [flatten, List.append_nil, List.foldr_append]
    rw [lastFold]
    obtain ⟨head, middleRuns, suffixShape⟩ := foldr_protected_tail classify (flatten earlier)
      last (piece :: decompose classify (flatten after))
    rw [suffixShape]
    exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr
      (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

/-- Positive fine runs inside a positive coarse run are maximal in the ORIGINAL
word, because both exterior coarse neighbours exclude the finer support. -/
theorem positive_refinement (fine coarse : Nat → Bool) (word outer inner : Word Nat)
    (contained : ∀ value, fine value = true → coarse value = true)
    (outerMember : outer ∈ decompose coarse word.toList)
    (outerPositive : coarse outer.head = true)
    (innerMember : inner ∈ decompose fine outer.toList)
    (innerPositive : fine inner.head = true) :
    inner ∈ decompose fine word.toList := by
  obtain ⟨before, after, _, outerSplit, _, outerLeft, outerRight⟩ :=
    factor_witness coarse word.toList outer outerMember
  obtain ⟨insideBefore, insideAfter, _, innerSplit, uniform, innerLeft, innerRight⟩ :=
    factor_witness fine outer.toList inner innerMember
  have leftOuter : LastOK (fun previous =>
      ∀ value ∈ previous.toList, fine value ≠ fine inner.head) before := by
    apply lastOK_of_witness
    intro earlier last boundary value member equal
    have coarsePositive := contained value (equal.trans innerPositive)
    exact outerLeft earlier last boundary value member (coarsePositive.trans outerPositive.symm)
  have rightOuter : FirstOK (fun next =>
      ∀ value ∈ next.toList, fine value ≠ fine inner.head) after := by
    intro next later boundary value member equal
    have coarsePositive := contained value (equal.trans innerPositive)
    exact outerRight next later boundary value member (coarsePositive.trans outerPositive.symm)
  have leftInner : LastOK (fun previous =>
      ∀ value ∈ previous.toList, fine value ≠ fine inner.head) insideBefore :=
    lastOK_of_witness _ insideBefore innerLeft
  have actual : word.toList = flatten (before ++ insideBefore) ++
      (inner.toList ++ flatten (insideAfter ++ after)) := by
    rw [outerSplit, innerSplit]
    simp only [FactorBoundaries.flatten_append, List.append_assoc]
  exact canonical_member_of_boundaries fine word.toList inner
    (before ++ insideBefore) (insideAfter ++ after) actual uniform
    (lastOK_append _ before insideBefore leftOuter leftInner)
    (firstOK_append _ insideAfter after innerRight rightOuter)

theorem insertLetter_not (classify : Nat → Bool) (letter : Nat)
    (pieces : List (Word Nat)) :
    insertLetter (fun value => !(classify value)) letter pieces =
      insertLetter classify letter pieces := by
  cases pieces with
  | nil => rfl
  | cons first rest =>
      let extended : Word Nat := ⟨letter, first.toList⟩
      change (if Bool.not (classify letter) = Bool.not (classify first.head) then extended :: rest
          else Word.singleton letter :: first :: rest) =
        (if classify letter = classify first.head then extended :: rest
          else Word.singleton letter :: first :: rest)
      cases classify letter <;> cases classify first.head <;> rfl

theorem decompose_not (classify : Nat → Bool) (letters : List Nat) :
    decompose (fun value => !(classify value)) letters = decompose classify letters := by
  induction letters with
  | nil => rfl
  | cons first rest ih =>
      simp only [decompose, ih, insertLetter_not]

theorem decompose_congr_on (left right : Nat → Bool) (letters : List Nat)
    (same : ∀ value ∈ letters, left value = right value) :
    decompose left letters = decompose right letters := by
  induction letters with
  | nil => rfl
  | cons first rest ih =>
      have firstEqual := same first (List.mem_cons.mpr (Or.inl rfl))
      have restEqual := ih (fun value member => same value (List.mem_cons.mpr (Or.inr member)))
      simp only [decompose]
      rw [← restEqual]
      cases split : decompose left rest with
      | nil => rfl
      | cons piece pieces =>
          have headMember : piece.head ∈ rest := by
            apply (decompose_covers left piece.head rest).mpr
            refine ⟨piece, ?_, word_head_member piece⟩
            rw [split]
            exact List.mem_cons.mpr (Or.inl rfl)
          have headEqual := same piece.head (List.mem_cons.mpr (Or.inr headMember))
          simp only [insertLetter, firstEqual, headEqual]

def unionTag (left right : Nat → Bool) (value : Nat) : Bool := left value || right value

theorem union_left (left right : Nat → Bool) (value : Nat) (positive : left value = true) :
    unionTag left right value = true := by
  unfold unionTag
  rw [positive]
  rfl

theorem union_right (left right : Nat → Bool) (value : Nat) (positive : right value = true) :
    unionTag left right value = true := by
  unfold unionTag
  rw [positive]
  cases left value <;> rfl

theorem complement_on_union (left right : Nat → Bool)
    (apart : ∀ value, left value = true → right value = false)
    (value : Nat) (positive : unionTag left right value = true) :
    right value = !(left value) := by
  cases leftTag : left value with
  | true => exact apart value leftTag
  | false =>
      cases rightTag : right value with
      | true => rfl
      | false =>
          unfold unionTag at positive
          rw [leftTag, rightTag] at positive
          cases positive

/-- The output records computed macro blocks and the unchanged original factor
contexts. Membership in the ORIGINAL fine decompositions is retained per block. -/
def Aligned (left right : Nat → Bool) (leftBlock rightBlock word factor : Word Nat) : Prop :=
  ∃ before after blocks : List (Word Nat),
    decompose (unionTag left right) word.toList = before ++ factor :: after ∧
    word = Context.frame (contextWord (flatten before)) (contextWord (flatten after)) factor ∧
    blocks = decompose left factor.toList ∧
    flatten blocks = factor.toList ∧ blocks ≠ [] ∧ Good left blocks ∧
    (∀ block ∈ blocks,
      (left block.head = true ∧ block = leftBlock ∧ block ∈ decompose left word.toList) ∨
      (right block.head = true ∧ block = rightBlock ∧ block ∈ decompose right word.toList))

theorem disjoint_alignment (left right : Nat → Bool)
    (leftBlock rightBlock word factor : Word Nat)
    (apart : ∀ value, left value = true → right value = false)
    (leftPerfect : ∀ piece ∈ decompose left word.toList,
      left piece.head = true → piece = leftBlock)
    (rightPerfect : ∀ piece ∈ decompose right word.toList,
      right piece.head = true → piece = rightBlock)
    (member : factor ∈ decompose (unionTag left right) word.toList)
    (positive : unionTag left right factor.head = true) :
    Aligned left right leftBlock rightBlock word factor := by
  obtain ⟨before, after, split, actual, uniform, _, _⟩ :=
    factor_witness (unionTag left right) word.toList factor member
  have complement : ∀ value ∈ factor.toList, right value = !(left value) := by
    intro value inside
    exact complement_on_union left right apart value ((uniform value inside).trans positive)
  have sameFactors : decompose right factor.toList = decompose left factor.toList := by
    exact (decompose_congr_on right (fun value => !(left value)) factor.toList complement).trans
      (decompose_not left factor.toList)
  refine ⟨before, after, decompose left factor.toList, split,
    word_frame_of_split (flatten before) (flatten after) word factor actual,
    rfl, flatten_decompose left factor.toList, decompose_word_nonempty left factor,
    decompose_good left factor.toList, ?_⟩
  intro block inside
  have headInside : block.head ∈ factor.toList :=
    (decompose_covers left block.head factor.toList).mpr ⟨block, inside, word_head_member block⟩
  cases leftTag : left block.head with
  | true =>
      have original := positive_refinement left (unionTag left right) word factor block
        (union_left left right) member positive inside leftTag
      exact Or.inl ⟨rfl, leftPerfect block original leftTag, original⟩
  | false =>
      have rightTag : right block.head = true := by
        have equal := complement block.head headInside
        rw [leftTag] at equal
        exact equal
      have rightInside : block ∈ decompose right factor.toList := by
        rw [sameFactors]
        exact inside
      have original := positive_refinement right (unionTag left right) word factor block
        (union_right left right) member positive rightInside rightTag
      exact Or.inr ⟨rightTag, rightPerfect block original rightTag, original⟩

def supportTag (root : Word Nat) (value : Nat) : Bool := decide (value ∈ root.toList)

theorem supportTag_true (root : Word Nat) (value : Nat) :
    supportTag root value = true ↔ value ∈ root.toList := by
  constructor
  · exact of_decide_eq_true
  · exact decide_eq_true

/-- Non-vacuous maximal-factor perfection for an actual root square. For a
Nodup alphabetically ordered root this is precisely the perfect-support square
criterion; the stronger alignment theorem below does not need those restrictions. -/
def CanonicalPerfect (root word : Word Nat) : Prop :=
  (root ++ root) ∈ decompose (supportTag root) word.toList ∧
  ∀ piece ∈ decompose (supportTag root) word.toList,
    supportTag root piece.head = true → piece = root ++ root

theorem canonical_perfect_literal_factor (root word : Word Nat)
    (perfect : CanonicalPerfect root word) :
    ∃ before after : List Nat, word.toList = before ++ ((root ++ root).toList ++ after) := by
  obtain ⟨before, after, _, actual, _, _, _⟩ :=
    factor_witness (supportTag root) word.toList (root ++ root) perfect.1
  exact ⟨flatten before, flatten after, actual⟩

theorem two_letter_support (x y : Nat) :
    supportTag (⟨x, [y]⟩ : Word Nat) = binaryTag x y := by
  funext value
  simp only [supportTag, Word.toList, List.mem_cons, List.not_mem_nil, or_false, binaryTag]

theorem binary_perfect_canonical (x y : Nat) (word : Word Nat)
    (perfect : BinaryPerfect.Perfect x y word) :
    CanonicalPerfect (⟨x, [y]⟩ : Word Nat) word := by
  constructor
  · rw [two_letter_support]
    exact BinaryPerfect.perfect_has_canonical_square x y word perfect
  · rw [two_letter_support]
    exact BinaryPerfect.perfect_canonical x y word perfect

theorem disjoint_perfect_roots_align (leftRoot rightRoot word factor : Word Nat)
    (apart : ∀ value ∈ leftRoot.toList, value ∉ rightRoot.toList)
    (leftPerfect : CanonicalPerfect leftRoot word)
    (rightPerfect : CanonicalPerfect rightRoot word)
    (member : factor ∈ decompose (unionTag (supportTag leftRoot) (supportTag rightRoot)) word.toList)
    (positive : unionTag (supportTag leftRoot) (supportTag rightRoot) factor.head = true) :
    Aligned (supportTag leftRoot) (supportTag rightRoot)
      (leftRoot ++ leftRoot) (rightRoot ++ rightRoot) word factor := by
  have disjoint : ∀ value, supportTag leftRoot value = true → supportTag rightRoot value = false := by
    intro value leftTag
    cases rightTag : supportTag rightRoot value with
    | false => rfl
    | true =>
        exact False.elim (apart value ((supportTag_true leftRoot value).mp leftTag)
          ((supportTag_true rightRoot value).mp rightTag))
  exact disjoint_alignment (supportTag leftRoot) (supportTag rightRoot)
    (leftRoot ++ leftRoot) (rightRoot ++ rightRoot) word factor
    disjoint leftPerfect.2 rightPerfect.2 member positive

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BlockAlignment

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BlockAlignment.firstOK_append
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BlockAlignment.lastOK_append
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BlockAlignment.lastOK_of_witness
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BlockAlignment.lastOK_witness
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BlockAlignment.nil_or_last
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BlockAlignment.bool_eq_of_ne
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BlockAlignment.foldr_protected_tail
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BlockAlignment.decompose_first_head
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BlockAlignment.separated_after
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BlockAlignment.canonical_member_of_boundaries
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BlockAlignment.positive_refinement
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BlockAlignment.insertLetter_not
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BlockAlignment.decompose_not
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BlockAlignment.decompose_congr_on
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BlockAlignment.union_left
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BlockAlignment.union_right
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BlockAlignment.complement_on_union
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BlockAlignment.disjoint_alignment
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BlockAlignment.supportTag_true
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BlockAlignment.canonical_perfect_literal_factor
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BlockAlignment.two_letter_support
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BlockAlignment.binary_perfect_canonical
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BlockAlignment.disjoint_perfect_roots_align
