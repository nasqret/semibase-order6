import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedTaggedLayout

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.Coarsening

open MaximalFactors FactorCodec TaggedLayout
open LayoutAction (Layout pushPositive)

/-- Every fine-positive letter remains positive for the coarser classifier. -/
def Coarser (fine coarse : Nat → Bool) : Prop :=
  ∀ value, fine value = true → coarse value = true

def tokenEffect (classify : Nat → Bool) (token : Option (Word Nat))
    (suffix : Layout) : Layout :=
  match token with
  | none => pushPositive suffix
  | some piece => effect classify piece.toList suffix

def layoutEffect (classify : Nat → Bool) (layout suffix : Layout) : Layout :=
  layout.foldr (tokenEffect classify) suffix

theorem token_effect (fine coarse : Nat → Bool) (piece : Word Nat)
    (uniform : Constant fine piece) (contained : Coarser fine coarse) (suffix : Layout) :
    tokenEffect coarse (taggedToken fine piece) suffix = effect coarse piece.toList suffix := by
  by_cases marked : fine piece.head = true
  · rw [taggedToken, if_pos marked]
    change pushPositive suffix = effect coarse piece.toList suffix
    apply (positive_word_action piece ?_ suffix).symm
    intro value member
    exact contained value ((uniform value member).trans marked)
  · rw [taggedToken, if_neg marked]
    rfl

theorem factors_effect (fine coarse : Nat → Bool) (pieces : List (Word Nat))
    (contained : Coarser fine coarse)
    (uniform : ∀ piece ∈ pieces, Constant fine piece) (suffix : Layout) :
    layoutEffect coarse (pieces.map (taggedToken fine)) suffix =
      effect coarse (flatten pieces) suffix := by
  induction pieces with
  | nil => rfl
  | cons piece rest ih =>
      have first : Constant fine piece := uniform piece (List.mem_cons.mpr (Or.inl rfl))
      have later : ∀ item ∈ rest, Constant fine item := by
        intro item member
        exact uniform item (List.mem_cons.mpr (Or.inr member))
      change tokenEffect coarse (taggedToken fine piece)
          (layoutEffect coarse (rest.map (taggedToken fine)) suffix) =
        effect coarse (piece.toList ++ flatten rest) suffix
      rw [effect_append, ih later]
      exact token_effect fine coarse piece first contained _

/-- Interpret the actual fine maximal factors, including every literal
negative word, as actions on an arbitrary coarser suffix state. -/
theorem skeleton_effect (fine coarse : Nat → Bool) (letters : List Nat)
    (contained : Coarser fine coarse) (suffix : Layout) :
    layoutEffect coarse (taggedSkeleton fine letters) suffix = effect coarse letters suffix := by
  have uniform : ∀ piece ∈ decompose fine letters, Constant fine piece := by
    intro piece member
    exact good_member_constant fine (decompose_good fine letters) member
  have interpreted := factors_effect fine coarse (decompose fine letters) contained uniform suffix
  rw [flatten_decompose] at interpreted
  exact interpreted

theorem same_effect_of_skeleton (fine coarse : Nat → Bool) {left right : List Nat}
    (contained : Coarser fine coarse)
    (same : taggedSkeleton fine left = taggedSkeleton fine right) :
    SameEffect coarse left right := by
  intro suffix
  rw [← skeleton_effect fine coarse left contained suffix,
    ← skeleton_effect fine coarse right contained suffix, same]

theorem same_skeleton_coarser (fine coarse : Nat → Bool) {left right : List Nat}
    (contained : Coarser fine coarse)
    (same : taggedSkeleton fine left = taggedSkeleton fine right) :
    taggedSkeleton coarse left = taggedSkeleton coarse right :=
  same_skeleton (same_effect_of_skeleton fine coarse contained same)

theorem negative_count_of_skeleton (classify : Nat → Bool) {left right : List Nat}
    (same : taggedSkeleton classify left = taggedSkeleton classify right)
    (value : Nat) (negative : classify value = false) : left.count value = right.count value :=
  same_negative_count
    (same_effect_of_skeleton classify classify (fun _ marked => marked) same) value negative

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.Coarsening

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.Coarsening.token_effect
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.Coarsening.factors_effect
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.Coarsening.skeleton_effect
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.Coarsening.same_effect_of_skeleton
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.Coarsening.same_skeleton_coarser
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.Coarsening.negative_count_of_skeleton
