import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedMacroExpansion

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SeparatorSkeleton

open MaximalFactors FactorBoundaries CanonicalSquareCover MacroExpansion

theorem expansion_members (value letter : Nat) :
    value ∈ (expansion letter).toList ↔ value = letter := by
  cases letter with
  | zero =>
      change value ∈ [0, 0] ↔ value = 0
      constructor
      · intro member
        rcases List.mem_cons.mp member with equal | later
        · exact equal
        · exact List.mem_singleton.mp later
      · intro equal
        exact List.mem_cons.mpr (Or.inl equal)
  | succ letter =>
      cases letter with
      | zero =>
          change value ∈ [1, 1] ↔ value = 1
          constructor
          · intro member
            rcases List.mem_cons.mp member with equal | later
            · exact equal
            · exact List.mem_singleton.mp later
          · intro equal
            exact List.mem_cons.mpr (Or.inl equal)
      | succ letter =>
          change value ∈ [letter + 2] ↔ value = letter + 2
          exact List.mem_singleton

theorem expanded_members (value : Nat) (letters : List Nat) :
    value ∈ expandLetters letters ↔ value ∈ letters := by
  change value ∈ letters.flatMap (fun letter => (expansion letter).toList) ↔ _
  constructor
  · intro member
    obtain ⟨letter, inside, expanded⟩ := List.mem_flatMap.mp member
    have equal : value = letter := (expansion_members value letter).mp expanded
    rw [equal]
    exact inside
  · intro member
    exact List.mem_flatMap.mpr ⟨value, member, (expansion_members value value).mpr rfl⟩

theorem expanded_head (piece : Word Nat) : (expandWord piece).head = piece.head := by
  apply Option.some.inj
  change ((expandWord piece).toList).head? = some piece.head
  rw [expandWord_toList]
  cases piece with
  | mk first rest =>
      cases first with
      | zero => rfl
      | succ first =>
          cases first with
          | zero => rfl
          | succ first => rfl

theorem expanded_constant (classify : Nat → Bool) (piece : Word Nat)
    (uniform : Constant classify piece) : Constant classify (expandWord piece) := by
  intro value member
  rw [expandWord_toList] at member
  have original : value ∈ piece.toList := (expanded_members value piece.toList).mp member
  have same := uniform value original
  simpa only [expanded_head] using same

theorem expanded_good (classify : Nat → Bool) (pieces : List (Word Nat))
    (good : Good classify pieces) : Good classify (pieces.map expandWord) := by
  induction good with
  | nil => exact Good.nil
  | last uniform => exact Good.last (expanded_constant classify _ uniform)
  | step uniform different tailGood ih =>
      exact Good.step (expanded_constant classify _ uniform)
        (by simpa only [expanded_head] using different) ih

theorem flatten_expanded (pieces : List (Word Nat)) :
    flatten (pieces.map expandWord) = expandLetters (flatten pieces) := by
  induction pieces with
  | nil => rfl
  | cons piece rest ih =>
      change (expandWord piece).toList ++ flatten (rest.map expandWord) =
        expandLetters (piece.toList ++ flatten rest)
      rw [expandWord_toList, ih, expand_append]

/-- Actual expansion commutes with canonical maximal factorization for every
classification, not merely for the marked binary alphabet. -/
theorem decompose_expanded (classify : Nat → Bool) (letters : List Nat) :
    decompose classify (expandLetters letters) =
      (decompose classify letters).map expandWord := by
  have covered : flatten ((decompose classify letters).map expandWord) =
      expandLetters letters := by
    rw [flatten_expanded, flatten_decompose]
  rw [← covered]
  exact decompose_flatten_good classify _
    (expanded_good classify _ (decompose_good classify letters))

theorem expanded_factor_count (classify : Nat → Bool) (letters : List Nat) :
    (decompose classify (expandLetters letters)).length =
      (decompose classify letters).length := by
  rw [decompose_expanded, List.length_map]

theorem negative_image (value : Nat) (negative : binaryTag 0 1 value = false) :
    expansion value = Word.singleton value := by
  have outside := binaryTag_false 0 1 value negative
  cases value with
  | zero => exact False.elim (outside.1 rfl)
  | succ value =>
      cases value with
      | zero => exact False.elim (outside.2 rfl)
      | succ value => rfl

theorem expanded_outside (letters : List Nat) :
    (∀ value ∈ letters, binaryTag 0 1 value = false) → expandLetters letters = letters := by
  induction letters with
  | nil => intro _; rfl
  | cons first rest ih =>
      intro outside
      have firstOutside : binaryTag 0 1 first = false :=
        outside first (List.mem_cons.mpr (Or.inl rfl))
      have tailOutside : ∀ value ∈ rest, binaryTag 0 1 value = false := by
        intro value member
        exact outside value (List.mem_cons.mpr (Or.inr member))
      calc
        expandLetters (first :: rest) =
            (expansion first).toList ++ expandLetters rest := expand_cons first rest
        _ = (Word.singleton first).toList ++ rest := by
            rw [negative_image first firstOutside, ih tailOutside]
        _ = first :: rest := rfl

theorem expanded_negative (piece : Word Nat)
    (uniform : Constant (binaryTag 0 1) piece)
    (negative : binaryTag 0 1 piece.head = false) : expandWord piece = piece := by
  apply Word.toList_injective
  rw [expandWord_toList]
  apply expanded_outside
  intro value member
  exact (uniform value member).trans negative

/-- A positive factor retains its slot as a marker; a negative factor retains
its entire literal Word. In particular, positive separators cannot disappear. -/
def factorToken (piece : Word Nat) : Option (Word Nat) :=
  if binaryTag 0 1 piece.head = true then none else some piece

def factorSkeleton (pieces : List (Word Nat)) : List (Option (Word Nat)) :=
  pieces.map factorToken

def canonicalSkeleton (letters : List Nat) : List (Option (Word Nat)) :=
  factorSkeleton (decompose (binaryTag 0 1) letters)

theorem factorToken_expanded (piece : Word Nat)
    (uniform : Constant (binaryTag 0 1) piece) :
    factorToken (expandWord piece) = factorToken piece := by
  by_cases positive : binaryTag 0 1 piece.head = true
  · simp only [factorToken, expanded_head, if_pos positive]
  · have negative : binaryTag 0 1 piece.head = false :=
      false_of_ne_true _ positive
    rw [expanded_negative piece uniform negative]

theorem factorSkeleton_expanded (pieces : List (Word Nat)) :
    Good (binaryTag 0 1) pieces →
      factorSkeleton (pieces.map expandWord) = factorSkeleton pieces := by
  induction pieces with
  | nil => intro _; rfl
  | cons piece rest ih =>
      intro good
      have uniform : Constant (binaryTag 0 1) piece :=
        good_member_constant _ good (List.mem_cons.mpr (Or.inl rfl))
      have tailGood : Good (binaryTag 0 1) rest := good_tail _ piece rest good
      change factorToken (expandWord piece) :: factorSkeleton (rest.map expandWord) =
        factorToken piece :: factorSkeleton rest
      rw [factorToken_expanded piece uniform, ih tailGood]

/-- Every negative run is unchanged in its original slot, and every positive
run remains present. Exterior placement and intervening runs are retained. -/
theorem skeleton_expanded (letters : List Nat) :
    canonicalSkeleton (expandLetters letters) = canonicalSkeleton letters := by
  unfold canonicalSkeleton
  rw [decompose_expanded]
  exact factorSkeleton_expanded _ (decompose_good _ letters)

theorem skeleton_expandWord (word : Word Nat) :
    canonicalSkeleton (expandWord word).toList = canonicalSkeleton word.toList := by
  rw [expandWord_toList]
  exact skeleton_expanded word.toList

/-- Equality of the complementary projection alone loses an intervening
positive slot and can merge distinct original complementary factors. -/
theorem projection_alone_insufficient :
    complementLetters [0, 2, 0, 3] = complementLetters [0, 2, 3] ∧
    canonicalSkeleton [0, 2, 0, 3] ≠ canonicalSkeleton [0, 2, 3] := by
  decide

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SeparatorSkeleton

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SeparatorSkeleton.expansion_members
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SeparatorSkeleton.expanded_members
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SeparatorSkeleton.expanded_head
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SeparatorSkeleton.expanded_constant
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SeparatorSkeleton.expanded_good
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SeparatorSkeleton.flatten_expanded
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SeparatorSkeleton.decompose_expanded
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SeparatorSkeleton.expanded_factor_count
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SeparatorSkeleton.negative_image
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SeparatorSkeleton.expanded_outside
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SeparatorSkeleton.expanded_negative
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SeparatorSkeleton.factorToken_expanded
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SeparatorSkeleton.factorSkeleton_expanded
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SeparatorSkeleton.skeleton_expanded
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SeparatorSkeleton.skeleton_expandWord
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SeparatorSkeleton.projection_alone_insufficient
