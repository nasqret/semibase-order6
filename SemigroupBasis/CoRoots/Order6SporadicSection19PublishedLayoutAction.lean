import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedSeparatorSkeleton

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.LayoutAction

open MaximalFactors SeparatorSkeleton FactorContexts OccurrenceWitnesses
  CrossFactor CrossSweep BinaryPowers

abbrev Layout := List (Option (Word Nat))

def pushPositive : Layout → Layout
  | none :: rest => none :: rest
  | rest => none :: rest

def pushNegative (letter : Nat) : Layout → Layout
  | some piece :: rest => some (⟨letter, piece.toList⟩ : Word Nat) :: rest
  | rest => some (Word.singleton letter) :: rest

def insertAction (letter : Nat) (layout : Layout) : Layout :=
  if binaryTag 0 1 letter = true then pushPositive layout else pushNegative letter layout

def effect (letters : List Nat) (layout : Layout) : Layout :=
  letters.foldr insertAction layout

def SameEffect (left right : List Nat) : Prop :=
  ∀ layout : Layout, effect left layout = effect right layout

def SameWordEffect (left right : Word Nat) : Prop := SameEffect left.toList right.toList

def SameContextEffect (left right : Option (Word Nat)) : Prop :=
  SameEffect (contextLetters left) (contextLetters right)

def Positive (word : Word Nat) : Prop :=
  ∀ letter ∈ word.toList, binaryTag 0 1 letter = true

theorem token_insert (letter : Nat) (pieces : List (Word Nat)) :
    factorSkeleton (insertLetter (binaryTag 0 1) letter pieces) =
      insertAction letter (factorSkeleton pieces) := by
  cases pieces with
  | nil =>
      cases tagged : binaryTag 0 1 letter <;>
        simp [factorSkeleton, insertLetter, factorToken, Word.singleton,
          insertAction, pushPositive, pushNegative, tagged]
  | cons piece rest =>
      cases tagged : binaryTag 0 1 letter <;>
        cases firstTag : binaryTag 0 1 piece.head <;>
        simp [factorSkeleton, insertLetter, factorToken, Word.singleton,
          insertAction, pushPositive, pushNegative, tagged, firstTag]

theorem skeleton_cons (letter : Nat) (letters : List Nat) :
    canonicalSkeleton (letter :: letters) = insertAction letter (canonicalSkeleton letters) :=
  token_insert letter (decompose (binaryTag 0 1) letters)

theorem canonical_action (letters : List Nat) :
    canonicalSkeleton letters = effect letters [] := by
  induction letters with
  | nil => rfl
  | cons first rest ih =>
      rw [skeleton_cons, ih]
      rfl

theorem effect_append (before after : List Nat) (layout : Layout) :
    effect (before ++ after) layout = effect before (effect after layout) := by
  induction before with
  | nil => rfl
  | cons first rest ih =>
      change insertAction first (effect (rest ++ after) layout) =
        insertAction first (effect rest (effect after layout))
      rw [ih]

theorem same_refl (letters : List Nat) : SameEffect letters letters := by
  intro layout
  rfl

theorem same_symm {left right : List Nat} (same : SameEffect left right) :
    SameEffect right left := by
  intro layout
  exact (same layout).symm

theorem same_trans {left middle right : List Nat}
    (first : SameEffect left middle) (second : SameEffect middle right) :
    SameEffect left right := by
  intro layout
  exact (first layout).trans (second layout)

theorem same_append {left right before after : List Nat}
    (front : SameEffect left right) (back : SameEffect before after) :
    SameEffect (left ++ before) (right ++ after) := by
  intro layout
  rw [effect_append, effect_append, back layout]
  exact front (effect after layout)

theorem same_skeleton {left right : List Nat} (same : SameEffect left right) :
    canonicalSkeleton left = canonicalSkeleton right := by
  rw [canonical_action, canonical_action]
  exact same []

theorem word_refl (word : Word Nat) : SameWordEffect word word := same_refl word.toList

theorem word_symm {left right : Word Nat} (same : SameWordEffect left right) :
    SameWordEffect right left := same_symm same

theorem word_trans {left middle right : Word Nat}
    (first : SameWordEffect left middle) (second : SameWordEffect middle right) :
    SameWordEffect left right := same_trans first second

theorem word_append {left right before after : Word Nat}
    (front : SameWordEffect left right) (back : SameWordEffect before after) :
    SameWordEffect (left ++ before) (right ++ after) := by
  change SameEffect (left ++ before).toList (right ++ after).toList
  rw [Word.toList_append, Word.toList_append]
  exact same_append front back

theorem word_skeleton {left right : Word Nat} (same : SameWordEffect left right) :
    canonicalSkeleton left.toList = canonicalSkeleton right.toList := same_skeleton same

theorem context_refl (context : Option (Word Nat)) : SameContextEffect context context :=
  same_refl (contextLetters context)

theorem word_gap {left right : Word Nat} {before after : Option (Word Nat)}
    (same : SameWordEffect left right) (contexts : SameContextEffect before after) :
    SameWordEffect (gap left before) (gap right after) := by
  change SameEffect (gap left before).toList (gap right after).toList
  rw [gap_toList, gap_toList]
  exact same_append same contexts

theorem context_join {left right before after : Option (Word Nat)}
    (front : SameContextEffect left right) (back : SameContextEffect before after) :
    SameContextEffect (joinGap left before) (joinGap right after) := by
  change SameEffect (contextLetters (joinGap left before)) (contextLetters (joinGap right after))
  rw [MarkedZones.join_letters, MarkedZones.join_letters]
  exact same_append front back

theorem context_push {left right : Option (Word Nat)} {before after : Word Nat}
    (front : SameContextEffect left right) (back : SameWordEffect before after) :
    SameContextEffect (pushGap left before) (pushGap right after) :=
  context_join front back

theorem word_frame (before after : Option (Word Nat)) {left right : Word Nat}
    (same : SameWordEffect left right) :
    SameWordEffect (Context.frame before after left) (Context.frame before after right) := by
  change SameEffect (Context.frame before after left).toList
    (Context.frame before after right).toList
  rw [frame_toList, frame_toList]
  exact same_append (same_refl _) (same_append same (same_refl _))

theorem pushPositive_idempotent (layout : Layout) :
    pushPositive (pushPositive layout) = pushPositive layout := by
  cases layout with
  | nil => rfl
  | cons first rest => cases first <;> rfl

theorem insert_positive (letter : Nat) (marked : binaryTag 0 1 letter = true)
    (layout : Layout) : insertAction letter layout = pushPositive layout :=
  if_pos marked

theorem positive_tail (letters : List Nat) :
    (∀ letter ∈ letters, binaryTag 0 1 letter = true) →
      ∀ layout : Layout, pushPositive (effect letters layout) = pushPositive layout := by
  induction letters with
  | nil => intro _ layout; rfl
  | cons first rest ih =>
      intro marked layout
      have firstMarked : binaryTag 0 1 first = true :=
        marked first (List.mem_cons.mpr (Or.inl rfl))
      have restMarked : ∀ letter ∈ rest, binaryTag 0 1 letter = true := by
        intro letter member
        exact marked letter (List.mem_cons.mpr (Or.inr member))
      change pushPositive (insertAction first (effect rest layout)) = pushPositive layout
      rw [insert_positive first firstMarked, pushPositive_idempotent]
      exact ih restMarked layout

theorem positive_word_action (word : Word Nat) (marked : Positive word) (layout : Layout) :
    effect word.toList layout = pushPositive layout := by
  cases word with
  | mk first rest =>
      have firstMarked : binaryTag 0 1 first = true :=
        marked first (List.mem_cons.mpr (Or.inl rfl))
      have restMarked : ∀ letter ∈ rest, binaryTag 0 1 letter = true := by
        intro letter member
        exact marked letter (List.mem_cons.mpr (Or.inr member))
      change insertAction first (effect rest layout) = pushPositive layout
      rw [insert_positive first firstMarked]
      exact positive_tail rest restMarked layout

theorem positive_singleton (letter : Nat) (marked : binaryTag 0 1 letter = true) :
    Positive (Word.singleton letter) := by
  intro value member
  have equal : value = letter := List.mem_singleton.mp member
  rw [equal]
  exact marked

theorem positive_append {left right : Word Nat} (front : Positive left) (back : Positive right) :
    Positive (left ++ right) := by
  intro letter member
  rw [Word.toList_append] at member
  rcases List.mem_append.mp member with inside | later
  · exact front letter inside
  · exact back letter later

theorem positive_square {left right : Word Nat} (front : Positive left) (back : Positive right) :
    Positive (square left right) :=
  positive_append (positive_append front back) (positive_append front back)

theorem positive_value {left right : Word Nat} (front : Positive left) (back : Positive right)
    (letter : Letter) : Positive (value left right letter) := by
  unfold value
  split
  · exact front
  · exact back

theorem positive_words {left right : Word Nat} (front : Positive left) (back : Positive right) :
    SameWordEffect left right := by
  intro layout
  rw [positive_word_action left front, positive_word_action right back]

/-- Every nonempty marked block has the same action on every suffix layout.
The two external contexts are retained literally. -/
theorem contextual_positive_replacement (before after : Option (Word Nat))
    {left right : Word Nat} (front : Positive left) (back : Positive right) :
    canonicalSkeleton (Context.frame before after left).toList =
      canonicalSkeleton (Context.frame before after right).toList :=
  word_skeleton (word_frame before after (positive_words front back))

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.LayoutAction

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.LayoutAction.token_insert
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.LayoutAction.skeleton_cons
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.LayoutAction.canonical_action
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.LayoutAction.effect_append
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.LayoutAction.same_refl
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.LayoutAction.same_symm
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.LayoutAction.same_trans
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.LayoutAction.same_append
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.LayoutAction.same_skeleton
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.LayoutAction.word_refl
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.LayoutAction.word_symm
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.LayoutAction.word_trans
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.LayoutAction.word_append
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.LayoutAction.word_skeleton
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.LayoutAction.context_refl
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.LayoutAction.word_gap
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.LayoutAction.context_join
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.LayoutAction.context_push
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.LayoutAction.word_frame
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.LayoutAction.pushPositive_idempotent
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.LayoutAction.insert_positive
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.LayoutAction.positive_tail
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.LayoutAction.positive_word_action
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.LayoutAction.positive_singleton
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.LayoutAction.positive_append
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.LayoutAction.positive_square
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.LayoutAction.positive_value
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.LayoutAction.positive_words
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.LayoutAction.contextual_positive_replacement
