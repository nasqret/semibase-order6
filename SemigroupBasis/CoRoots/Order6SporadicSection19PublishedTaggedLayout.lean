import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedRootFamily

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.TaggedLayout

open MaximalFactors FactorContexts OccurrenceWitnesses FactorCodec
  CrossFactor CrossSweep CrossLeftSweep AnchorPropagation MiddleSweep BinaryPowers
  MarkedZones SquareCoalescing
open LayoutAction (Layout pushPositive pushNegative pushPositive_idempotent)

/-- The existing layout state, now acting under the actual support classifier. -/
def insertAction (classify : Nat → Bool) (letter : Nat) (layout : Layout) : Layout :=
  if classify letter = true then pushPositive layout else pushNegative letter layout

def effect (classify : Nat → Bool) (letters : List Nat) (layout : Layout) : Layout :=
  letters.foldr (insertAction classify) layout

def SameEffect (classify : Nat → Bool) (left right : List Nat) : Prop :=
  ∀ layout : Layout, effect classify left layout = effect classify right layout

def SameWordEffect (classify : Nat → Bool) (left right : Word Nat) : Prop :=
  SameEffect classify left.toList right.toList

def SameContextEffect (classify : Nat → Bool) (left right : Option (Word Nat)) : Prop :=
  SameEffect classify (contextLetters left) (contextLetters right)

def Positive (classify : Nat → Bool) (word : Word Nat) : Prop :=
  ∀ letter ∈ word.toList, classify letter = true

variable {classify : Nat → Bool}

theorem token_insert (classify : Nat → Bool) (letter : Nat) (pieces : List (Word Nat)) :
    (insertLetter classify letter pieces).map (taggedToken classify) =
      insertAction classify letter (pieces.map (taggedToken classify)) := by
  cases pieces with
  | nil =>
      cases tagged : classify letter <;>
        simp [insertLetter, taggedToken, Word.singleton,
          insertAction, pushPositive, pushNegative, tagged]
  | cons piece rest =>
      cases tagged : classify letter <;> cases firstTag : classify piece.head <;>
        simp [insertLetter, taggedToken, Word.singleton,
          insertAction, pushPositive, pushNegative, tagged, firstTag]

theorem skeleton_cons (classify : Nat → Bool) (letter : Nat) (letters : List Nat) :
    taggedSkeleton classify (letter :: letters) =
      insertAction classify letter (taggedSkeleton classify letters) :=
  token_insert classify letter (decompose classify letters)

theorem canonical_action (classify : Nat → Bool) (letters : List Nat) :
    taggedSkeleton classify letters = effect classify letters [] := by
  induction letters with
  | nil => rfl
  | cons first rest ih =>
      rw [skeleton_cons, ih]
      rfl

theorem effect_append (classify : Nat → Bool) (before after : List Nat) (layout : Layout) :
    effect classify (before ++ after) layout =
      effect classify before (effect classify after layout) := by
  induction before with
  | nil => rfl
  | cons first rest ih =>
      change insertAction classify first (effect classify (rest ++ after) layout) =
        insertAction classify first (effect classify rest (effect classify after layout))
      rw [ih]

theorem same_refl (letters : List Nat) : SameEffect classify letters letters := by
  intro layout
  rfl

theorem same_trans {left middle right : List Nat}
    (first : SameEffect classify left middle) (second : SameEffect classify middle right) :
    SameEffect classify left right := by
  intro layout
  exact (first layout).trans (second layout)

theorem same_append {left right before after : List Nat}
    (front : SameEffect classify left right) (back : SameEffect classify before after) :
    SameEffect classify (left ++ before) (right ++ after) := by
  intro layout
  rw [effect_append, effect_append, back layout]
  exact front (effect classify after layout)

theorem same_skeleton {left right : List Nat} (same : SameEffect classify left right) :
    taggedSkeleton classify left = taggedSkeleton classify right := by
  rw [canonical_action, canonical_action]
  exact same []

theorem word_refl (word : Word Nat) : SameWordEffect classify word word := same_refl word.toList

theorem word_trans {left middle right : Word Nat}
    (first : SameWordEffect classify left middle) (second : SameWordEffect classify middle right) :
    SameWordEffect classify left right := same_trans first second

theorem word_append {left right before after : Word Nat}
    (front : SameWordEffect classify left right) (back : SameWordEffect classify before after) :
    SameWordEffect classify (left ++ before) (right ++ after) := by
  change SameEffect classify (left ++ before).toList (right ++ after).toList
  rw [Word.toList_append, Word.toList_append]
  exact same_append front back

theorem word_skeleton {left right : Word Nat} (same : SameWordEffect classify left right) :
    taggedSkeleton classify left.toList = taggedSkeleton classify right.toList := same_skeleton same

theorem context_refl (context : Option (Word Nat)) : SameContextEffect classify context context :=
  same_refl (contextLetters context)

theorem word_gap {left right : Word Nat} {before after : Option (Word Nat)}
    (same : SameWordEffect classify left right) (contexts : SameContextEffect classify before after) :
    SameWordEffect classify (gap left before) (gap right after) := by
  change SameEffect classify (gap left before).toList (gap right after).toList
  rw [gap_toList, gap_toList]
  exact same_append same contexts

theorem context_join {left right before after : Option (Word Nat)}
    (front : SameContextEffect classify left right) (back : SameContextEffect classify before after) :
    SameContextEffect classify (joinGap left before) (joinGap right after) := by
  change SameEffect classify (contextLetters (joinGap left before)) (contextLetters (joinGap right after))
  rw [join_letters, join_letters]
  exact same_append front back

theorem context_push {left right : Option (Word Nat)} {before after : Word Nat}
    (front : SameContextEffect classify left right) (back : SameWordEffect classify before after) :
    SameContextEffect classify (pushGap left before) (pushGap right after) :=
  context_join front back

theorem word_frame (before after : Option (Word Nat)) {left right : Word Nat}
    (same : SameWordEffect classify left right) :
    SameWordEffect classify (Context.frame before after left) (Context.frame before after right) := by
  change SameEffect classify (Context.frame before after left).toList
    (Context.frame before after right).toList
  rw [frame_toList, frame_toList]
  exact same_append (same_refl _) (same_append same (same_refl _))

theorem insert_positive (letter : Nat) (marked : classify letter = true)
    (layout : Layout) : insertAction classify letter layout = pushPositive layout :=
  if_pos marked

theorem positive_tail (letters : List Nat) :
    (∀ letter ∈ letters, classify letter = true) →
      ∀ layout : Layout, pushPositive (effect classify letters layout) = pushPositive layout := by
  induction letters with
  | nil => intro _ layout; rfl
  | cons first rest ih =>
      intro marked layout
      have firstMarked : classify first = true := marked first (List.mem_cons.mpr (Or.inl rfl))
      have restMarked : ∀ letter ∈ rest, classify letter = true := by
        intro letter member
        exact marked letter (List.mem_cons.mpr (Or.inr member))
      change pushPositive (insertAction classify first (effect classify rest layout)) = pushPositive layout
      rw [insert_positive first firstMarked, pushPositive_idempotent]
      exact ih restMarked layout

theorem positive_word_action (word : Word Nat) (marked : Positive classify word) (layout : Layout) :
    effect classify word.toList layout = pushPositive layout := by
  cases word with
  | mk first rest =>
      have firstMarked : classify first = true := marked first (List.mem_cons.mpr (Or.inl rfl))
      have restMarked : ∀ letter ∈ rest, classify letter = true := by
        intro letter member
        exact marked letter (List.mem_cons.mpr (Or.inr member))
      change insertAction classify first (effect classify rest layout) = pushPositive layout
      rw [insert_positive first firstMarked]
      exact positive_tail rest restMarked layout

theorem positive_singleton (letter : Nat) (marked : classify letter = true) :
    Positive classify (Word.singleton letter) := by
  intro value member
  have equal : value = letter := List.mem_singleton.mp member
  rw [equal]
  exact marked

theorem positive_append {left right : Word Nat}
    (front : Positive classify left) (back : Positive classify right) : Positive classify (left ++ right) := by
  intro letter member
  rw [Word.toList_append] at member
  rcases List.mem_append.mp member with inside | later
  · exact front letter inside
  · exact back letter later

theorem positive_square {left right : Word Nat}
    (front : Positive classify left) (back : Positive classify right) : Positive classify (square left right) :=
  positive_append (positive_append front back) (positive_append front back)

theorem positive_value {left right : Word Nat}
    (front : Positive classify left) (back : Positive classify right)
    (letter : Letter) : Positive classify (value left right letter) := by
  unfold value
  split
  · exact front
  · exact back

theorem positive_words {left right : Word Nat}
    (front : Positive classify left) (back : Positive classify right) :
    SameWordEffect classify left right := by
  intro layout
  rw [positive_word_action left front, positive_word_action right back]

/-- Forget positive placeholders, retaining every literal negative letter. -/
def negativeLetters : Layout → List Nat
  | [] => []
  | none :: rest => negativeLetters rest
  | some piece :: rest => piece.toList ++ negativeLetters rest

theorem negative_positive (layout : Layout) :
    negativeLetters (pushPositive layout) = negativeLetters layout := by
  cases layout with
  | nil => rfl
  | cons first rest => cases first <;> rfl

theorem negative_negative (letter : Nat) (layout : Layout) :
    negativeLetters (pushNegative letter layout) = letter :: negativeLetters layout := by
  cases layout with
  | nil => rfl
  | cons first rest => cases first <;> rfl

theorem negative_effect (classify : Nat → Bool) (letters : List Nat) (layout : Layout) :
    negativeLetters (effect classify letters layout) =
      letters.filter (fun value => !(classify value)) ++ negativeLetters layout := by
  induction letters with
  | nil => rfl
  | cons first rest ih =>
      change negativeLetters (insertAction classify first (effect classify rest layout)) = _
      cases tagged : classify first
      · simp only [insertAction, tagged, Bool.false_eq_true, if_false, negative_negative, ih]
        simp [tagged]
      · rw [insert_positive first tagged, negative_positive, ih]
        simp [tagged]

theorem filtered_count (classify : Nat → Bool) (letter : Nat) (letters : List Nat)
    (negative : classify letter = false) :
    (letters.filter (fun value => !(classify value))).count letter = letters.count letter := by
  induction letters with
  | nil => rfl
  | cons first rest ih =>
      by_cases equal : first = letter
      · subst first
        simp [negative, ih]
      · cases tagged : classify first <;>
          simp [tagged, List.count_cons_of_ne equal, ih]

theorem same_negative_count {left right : List Nat} (same : SameEffect classify left right)
    (letter : Nat) (negative : classify letter = false) : left.count letter = right.count letter := by
  have filtered := congrArg negativeLetters (same [])
  rw [negative_effect, negative_effect] at filtered
  simp only [negativeLetters, List.append_nil] at filtered
  have counted :
      (left.filter (fun value => !(classify value))).count letter =
        (right.filter (fun value => !(classify value))).count letter :=
    congrArg (fun letters : List Nat => letters.count letter) filtered
  rw [filtered_count classify letter left negative, filtered_count classify letter right negative] at counted
  exact counted

theorem render_layout (first second : Letter → Word Nat) (items : List Segment)
    (images : ∀ letter, SameWordEffect classify (first letter) (second letter))
    {left right : Word Nat} (initial : SameWordEffect classify left right) :
    SameWordEffect classify (render first left items) (render second right items) := by
  induction items generalizing left right with
  | nil => exact initial
  | cons item rest ih =>
      change SameWordEffect classify (render first (gap left item.1 ++ first item.2) rest)
        (render second (gap right item.1 ++ second item.2) rest)
      exact ih (word_append (word_gap initial (context_refl item.1)) (images item.2))

theorem renderLeft_layout (first second : Letter → Word Nat) (items : List Segment)
    (images : ∀ letter, SameWordEffect classify (first letter) (second letter))
    {left right : Word Nat} (initial : SameWordEffect classify left right) :
    SameWordEffect classify (renderLeft first left items) (renderLeft second right items) := by
  induction items with
  | nil => exact initial
  | cons item rest ih =>
      exact word_append (word_gap (images item.2) (context_refl item.1)) ih

theorem foldGap_layout (first second : Letter → Word Nat) (items : List Segment)
    (images : ∀ letter, SameWordEffect classify (first letter) (second letter)) :
    SameContextEffect classify (foldGap first items) (foldGap second items) := by
  induction items with
  | nil => exact context_refl none
  | cons item rest ih =>
      exact context_join (context_push (context_refl item.1) (images item.2)) ih

theorem anchor_square_layout (u v : Word Nat) {before after : Option (Word Nat)}
    (positiveU : Positive classify u) (positiveV : Positive classify v)
    (middle : SameContextEffect classify before after) :
    SameWordEffect classify (anchor u v before) (gap (square u v) after ++ square u v) := by
  have front : SameWordEffect classify (gap u before) (gap (square u v) after) :=
    word_gap (positive_words positiveU (positive_square positiveU positiveV)) middle
  have back : SameWordEffect classify (v ++ (v ++ u)) (square u v) :=
    positive_words (positive_append positiveV (positive_append positiveV positiveU))
      (positive_square positiveU positiveV)
  have step := word_append front back
  simpa only [anchor, Word.append_assoc] using step

theorem three_zone_layout (u v : Word Nat) (hGap kGap : Option (Word Nat))
    (before middle after : List Segment) (positiveU : Positive classify u) (positiveV : Positive classify v) :
    SameWordEffect classify
      (render (value u v)
        (renderLeft (value u v)
          (anchor u v (joinGap (joinGap hGap (foldGap (value u v) middle)) kGap)) before) after)
      (render (fun _ => square u v)
        (renderLeft (fun _ => square u v)
          (gap (square u v)
            (joinGap (joinGap hGap (foldGap (fun _ => square u v) middle)) kGap) ++
              square u v) before) after) := by
  have images : ∀ letter, SameWordEffect classify (value u v letter) (square u v) := by
    intro letter
    exact positive_words (positive_value positiveU positiveV letter) (positive_square positiveU positiveV)
  have middleSame : SameContextEffect classify
      (joinGap (joinGap hGap (foldGap (value u v) middle)) kGap)
      (joinGap (joinGap hGap (foldGap (fun _ => square u v) middle)) kGap) :=
    context_join
      (context_join (context_refl hGap) (foldGap_layout _ _ middle images)) (context_refl kGap)
  exact render_layout _ _ after images
    (renderLeft_layout _ _ before images (anchor_square_layout u v positiveU positiveV middleSame))

theorem arbitrary_anchor_square_layout (x y : Nat) (before middle after : List Nat)
    (markedX : classify x = true) (markedY : classify y = true) :
    SameWordEffect classify
      (Context.frame (contextWord before) (contextWord after)
        (anchor (Word.singleton x) (Word.singleton y) (contextWord middle)))
      (squareBlocks x y before middle after) := by
  have step := word_frame
    (contextWord (encodeLeft x y before).1) (contextWord (encodeRight x y after).2)
    (three_zone_layout (Word.singleton x) (Word.singleton y)
      none (contextWord (encodeRight x y middle).2)
      (segments (encodeLeft x y before).2) (segments (encodeRight x y middle).1)
      (segments (encodeRight x y after).1)
      (positive_singleton x markedX) (positive_singleton y markedY))
  change SameWordEffect classify (markedSource x y before middle after)
    (squareBlocks x y before middle after) at step
  rw [marked_source_eq] at step
  exact step

theorem chain_layout {left right : Word Nat} (same : SameWordEffect classify left right)
    (gaps : List (List Nat)) : SameWordEffect classify (chain left gaps) (chain right gaps) := by
  induction gaps with
  | nil => exact same
  | cons letters rest ih =>
      exact word_append (word_gap same (context_refl (contextWord letters))) ih

theorem prefix_collapse_layout (block : Word Nat) (marked : Positive classify block)
    (gaps : List (List Nat)) :
    SameWordEffect classify (block ++ chain block gaps) (chain block gaps) := by
  cases gaps with
  | nil => exact positive_words (positive_append marked marked) marked
  | cons letters rest =>
      have step := word_append
        (word_gap (positive_words (positive_append marked marked) marked)
          (context_refl (contextWord letters))) (word_refl (chain block rest))
      simpa only [chain, prefixChain, gap_append, Word.append_assoc] using step

theorem coalesce_layout (block : Word Nat) (marked : Positive classify block)
    (gaps : List (List Nat)) :
    SameWordEffect classify (chain block gaps) (chain block (keepNonempty gaps)) := by
  induction gaps with
  | nil => exact word_refl block
  | cons letters rest ih =>
      cases letters with
      | nil =>
          change SameWordEffect classify (block ++ chain block rest) (chain block (keepNonempty rest))
          exact word_trans (word_append (word_refl block) ih)
            (prefix_collapse_layout block marked (keepNonempty rest))
      | cons first later =>
          exact word_append (word_refl (gap block (some ⟨first, later⟩))) ih

/-- Actual arbitrary anchor normalization retains the entire tagged complement,
for the caller's support classifier, including the singleton case x = y. -/
theorem arbitrary_anchor_coalesced_layout (x y : Nat) (before middle after : List Nat)
    (markedX : classify x = true) (markedY : classify y = true) :
    SameWordEffect classify
      (Context.frame (contextWord before) (contextWord after)
        (anchor (Word.singleton x) (Word.singleton y) (contextWord middle)))
      (coalescedSquareBlocks x y before middle after) := by
  apply word_trans (arbitrary_anchor_square_layout x y before middle after markedX markedY)
  rw [squareBlocks_as_chain]
  unfold coalescedSquareBlocks
  exact word_frame _ _
    (coalesce_layout (square (Word.singleton x) (Word.singleton y))
      (positive_square (positive_singleton x markedX) (positive_singleton y markedY))
      (actualGaps x y before middle after))

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.TaggedLayout

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.TaggedLayout.token_insert
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.TaggedLayout.canonical_action
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.TaggedLayout.word_skeleton
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.TaggedLayout.positive_words
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.TaggedLayout.negative_effect
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.TaggedLayout.same_negative_count
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.TaggedLayout.three_zone_layout
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.TaggedLayout.chain_layout
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.TaggedLayout.coalesce_layout
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.TaggedLayout.arbitrary_anchor_coalesced_layout
