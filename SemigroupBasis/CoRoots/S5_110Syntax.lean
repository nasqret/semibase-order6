import SemigroupBasis.CoRoots.S5_110
import SemigroupBasis.CoRoots.S5_213Syntax

namespace SemigroupBasis.CoRoots.S5_110Syntax

open SemigroupBasis

/-- Multiplicity capped at `2`, representing `0`, `1`, and `2+`. -/
def cappedMultiplicity (word : Word Nat) (letter : Nat) : Nat :=
  Nat.min 2 (word.toList.count letter)

theorem cappedMultiplicity_eq_zero_iff
    (word : Word Nat) (letter : Nat) :
    cappedMultiplicity word letter = 0 ↔
      word.toList.count letter = 0 := by
  unfold cappedMultiplicity
  simp only [Nat.min_def]
  split <;> omega

theorem cappedMultiplicity_eq_one_iff
    (word : Word Nat) (letter : Nat) :
    cappedMultiplicity word letter = 1 ↔
      word.toList.count letter = 1 := by
  unfold cappedMultiplicity
  simp only [Nat.min_def]
  split <;> omega

theorem cappedMultiplicity_eq_two_iff
    (word : Word Nat) (letter : Nat) :
    cappedMultiplicity word letter = 2 ↔
      2 ≤ word.toList.count letter := by
  unfold cappedMultiplicity
  simp only [Nat.min_def]
  split <;> omega

/-- Keep exactly the globally singleton variables, in literal order. -/
abbrev singletonSequence (word : Word Nat) : List Nat :=
  S5_213Syntax.singletonSequence word

theorem singletonSequence_nodup (word : Word Nat) :
    (singletonSequence word).Nodup :=
  S5_213Syntax.singletonSequence_nodup word

theorem mem_singletonSequence_iff
    (word : Word Nat) (letter : Nat) :
    letter ∈ singletonSequence word ↔
      word.toList.count letter = 1 :=
  S5_213Syntax.mem_singletonSequence_iff word letter

inductive PairSymbol where
  | other
  | x
  | y
deriving DecidableEq, Repr

/-- Exact cap-two two-letter projection states. The only order-sensitive
states are `xy` and `yx`, where both variables occur exactly once. -/
inductive PairState where
  | empty
  | x1
  | x2
  | y1
  | y2
  | xy
  | yx
  | x1y2
  | x2y1
  | x2y2
deriving DecidableEq, Repr

def pairStep : PairState → PairSymbol → PairState
  | state, .other => state
  | .empty, .x => .x1
  | .x1, .x => .x2
  | .x2, .x => .x2
  | .y1, .x => .yx
  | .y2, .x => .x1y2
  | .xy, .x => .x2y1
  | .yx, .x => .x2y1
  | .x1y2, .x => .x2y2
  | .x2y1, .x => .x2y1
  | .x2y2, .x => .x2y2
  | .empty, .y => .y1
  | .x1, .y => .xy
  | .x2, .y => .x2y1
  | .y1, .y => .y2
  | .y2, .y => .y2
  | .xy, .y => .x1y2
  | .yx, .y => .x1y2
  | .x1y2, .y => .x1y2
  | .x2y1, .y => .x2y2
  | .x2y2, .y => .x2y2

def PairState.xCount : PairState → Nat
  | .empty | .y1 | .y2 => 0
  | .x1 | .xy | .yx | .x1y2 => 1
  | .x2 | .x2y1 | .x2y2 => 2

def PairState.yCount : PairState → Nat
  | .empty | .x1 | .x2 => 0
  | .y1 | .xy | .yx | .x2y1 => 1
  | .y2 | .x1y2 | .x2y2 => 2

def pairSymbol (x y letter : Nat) : PairSymbol :=
  if letter = x then .x else if letter = y then .y else .other

def pairScan (word : Word Nat) (x y : Nat) : PairState :=
  word.toList.foldl
    (fun state letter => pairStep state (pairSymbol x y letter))
    .empty

/-- Pairwise order on globally singleton variables. -/
def SimplePrecedes (word : Word Nat) (x y : Nat) : Prop :=
  x ≠ y ∧ pairScan word x y = .xy

private def pairKeep (x y value : Nat) : Bool :=
  value == x || value == y

private def pairProjection
    (word : Word Nat) (x y : Nat) : List Nat :=
  word.toList.filter (pairKeep x y)

private theorem count_filter_of_kept
    (letters : List Nat) (keep : Nat → Bool) (letter : Nat)
    (kept : keep letter = true) :
    (letters.filter keep).count letter = letters.count letter := by
  induction letters with
  | nil => simp
  | cons first rest induction =>
      by_cases equality : first = letter
      · subst first
        simp [kept, induction]
      · by_cases firstKept : keep first
        · simp [firstKept, equality, induction]
        · simp [firstKept, equality, induction]

private theorem pairKeep_member
    {letters : List Nat} {x y value : Nat}
    (member : value ∈ letters.filter (pairKeep x y)) :
    value = x ∨ value = y := by
  have kept := (List.mem_filter.mp member).2
  simpa [pairKeep] using kept

private theorem length_eq_pair_counts
    {x y : Nat} (different : x ≠ y) :
    ∀ letters : List Nat,
      (∀ value, value ∈ letters → value = x ∨ value = y) →
      letters.length = letters.count x + letters.count y
  | [], _ => by simp
  | value :: rest, onlyPair => by
      have headPair := onlyPair value (by simp)
      have restPair :
          ∀ selected, selected ∈ rest →
            selected = x ∨ selected = y := by
        intro selected member
        exact onlyPair selected (by simp [member])
      have induction :=
        length_eq_pair_counts different rest restPair
      rcases headPair with rfl | rfl
      · simp [different, induction]
        omega
      · simp [Ne.symm different, induction]
        omega

private theorem pairList_shape_of_counts_one
    (letters : List Nat) {x y : Nat}
    (different : x ≠ y)
    (xCount : letters.count x = 1)
    (yCount : letters.count y = 1)
    (onlyPair :
      ∀ value, value ∈ letters → value = x ∨ value = y) :
    letters = [x, y] ∨ letters = [y, x] := by
  have lengthTwo : letters.length = 2 := by
    rw [length_eq_pair_counts different letters onlyPair,
      xCount, yCount]
  rcases letters with _ | ⟨head, rest⟩
  · simp at lengthTwo
  rcases rest with _ | ⟨next, rest⟩
  · simp at lengthTwo
  have restEmpty : rest = [] := by
    apply List.eq_nil_of_length_eq_zero
    simpa using lengthTwo
  subst rest
  have headPair := onlyPair head (by simp)
  have nextPair := onlyPair next (by simp)
  rcases headPair with rfl | rfl
  · rcases nextPair with rfl | rfl
    · simp at xCount
    · exact Or.inl rfl
  · rcases nextPair with rfl | rfl
    · exact Or.inr rfl
    · simp at yCount

private theorem pairFold_filter (x y : Nat) :
    ∀ (letters : List Nat) (initial : PairState),
      letters.foldl
          (fun state value =>
            pairStep state (pairSymbol x y value))
          initial =
        (letters.filter (pairKeep x y)).foldl
          (fun state value =>
            pairStep state (pairSymbol x y value))
          initial
  | [], _ => rfl
  | value :: rest, initial => by
      by_cases isX : value = x
      · subst value
        have induction :=
          pairFold_filter x y rest
            (pairStep initial (pairSymbol x y x))
        simpa [pairKeep, pairSymbol] using induction
      · by_cases isY : value = y
        · subst value
          have induction :=
            pairFold_filter x y rest
              (pairStep initial (pairSymbol x y y))
          simpa [pairKeep, pairSymbol, isX] using induction
        · have induction := pairFold_filter x y rest initial
          simpa [pairKeep, pairSymbol, pairStep, isX, isY]
            using induction

private theorem pairScan_eq_projectionFold
    (word : Word Nat) (x y : Nat) :
    pairScan word x y =
      (pairProjection word x y).foldl
        (fun state value =>
          pairStep state (pairSymbol x y value))
        .empty := by
  unfold pairScan pairProjection
  exact pairFold_filter x y word.toList .empty

private theorem pairProjection_shape
    (word : Word Nat) {x y : Nat}
    (different : x ≠ y)
    (xSimple : word.toList.count x = 1)
    (ySimple : word.toList.count y = 1) :
    pairProjection word x y = [x, y] ∨
      pairProjection word x y = [y, x] := by
  apply pairList_shape_of_counts_one
  · exact different
  · unfold pairProjection
    rw [count_filter_of_kept word.toList (pairKeep x y) x]
    · exact xSimple
    · simp [pairKeep]
  · unfold pairProjection
    rw [count_filter_of_kept word.toList (pairKeep x y) y]
    · exact ySimple
    · simp [pairKeep]
  · intro value member
    exact pairKeep_member member

private theorem simplePrecedes_iff_pairProjection_head
    (word : Word Nat) {x y : Nat}
    (different : x ≠ y)
    (xSimple : word.toList.count x = 1)
    (ySimple : word.toList.count y = 1) :
    SimplePrecedes word x y ↔
      (pairProjection word x y).head? = some x := by
  unfold SimplePrecedes
  rw [pairScan_eq_projectionFold]
  rcases pairProjection_shape word different xSimple ySimple with
      shape | shape <;>
    rw [shape] <;>
    simp [pairSymbol, pairStep, different, Ne.symm different]

private theorem singletonSequence_pairProjection
    (word : Word Nat) {x y : Nat}
    (different : x ≠ y)
    (xSimple : word.toList.count x = 1)
    (ySimple : word.toList.count y = 1) :
    (singletonSequence word).filter (pairKeep x y) =
      pairProjection word x y := by
  unfold singletonSequence S5_213Syntax.singletonSequence pairProjection
  rw [List.filter_filter]
  apply List.filter_congr
  intro value _
  by_cases isX : value = x
  · subst value
    simp [pairKeep, xSimple]
  · by_cases isY : value = y
    · subst value
      simp [pairKeep, isX, ySimple]
    · simp [pairKeep, isX, isY]

private theorem nodup_eq_of_pairProjection_head :
    ∀ {left right : List Nat},
      left.Nodup →
      right.Nodup →
      (∀ value, value ∈ left ↔ value ∈ right) →
      (∀ x y,
        x ≠ y →
        x ∈ left →
        y ∈ left →
        (left.filter (pairKeep x y)).head? =
          (right.filter (pairKeep x y)).head?) →
      left = right
  | [], [], _, _, _, _ => rfl
  | [], head :: tail, _, _, sameMembers, _ => by
      have : head ∈ ([] : List Nat) :=
        (sameMembers head).mpr (by simp)
      simp at this
  | head :: tail, [], _, _, sameMembers, _ => by
      have : head ∈ ([] : List Nat) :=
        (sameMembers head).mp (by simp)
      simp at this
  | leftHead :: leftTail, rightHead :: rightTail,
      leftNodup, rightNodup, sameMembers, sameHeads => by
      simp only [List.nodup_cons] at leftNodup rightNodup
      have headsEqual : leftHead = rightHead := by
        apply Decidable.byContradiction
        intro different
        have leftHeadMember :
            leftHead ∈ leftHead :: leftTail := by simp
        have rightHeadMember :
            rightHead ∈ leftHead :: leftTail :=
          (sameMembers rightHead).mpr (by simp)
        have pairHeads :=
          sameHeads leftHead rightHead different
            leftHeadMember rightHeadMember
        simp [pairKeep, different] at pairHeads
      subst rightHead
      have tailMembers :
          ∀ value, value ∈ leftTail ↔ value ∈ rightTail := by
        intro value
        constructor
        · intro member
          have inRight :
              value ∈ leftHead :: rightTail :=
            (sameMembers value).mp (by simp [member])
          rcases List.mem_cons.mp inRight with equality | tailMember
          · subst value
            exact False.elim (leftNodup.1 member)
          · exact tailMember
        · intro member
          have inLeft :
              value ∈ leftHead :: leftTail :=
            (sameMembers value).mpr (by simp [member])
          rcases List.mem_cons.mp inLeft with equality | tailMember
          · subst value
            exact False.elim (rightNodup.1 member)
          · exact tailMember
      have tailHeads :
          ∀ x y,
            x ≠ y →
            x ∈ leftTail →
            y ∈ leftTail →
            (leftTail.filter (pairKeep x y)).head? =
              (rightTail.filter (pairKeep x y)).head? := by
        intro x y different xMember yMember
        have xNotHead : x ≠ leftHead := by
          intro equality
          subst x
          exact leftNodup.1 xMember
        have yNotHead : y ≠ leftHead := by
          intro equality
          subst y
          exact leftNodup.1 yMember
        have inherited :=
          sameHeads x y different
            (by simp [xMember]) (by simp [yMember])
        simpa [pairKeep, Ne.symm xNotHead,
          Ne.symm yNotHead] using inherited
      have tailEqual :=
        nodup_eq_of_pairProjection_head
          leftNodup.2 rightNodup.2 tailMembers tailHeads
      rw [tailEqual]

/-- The exact S5_110 signature: cap every multiplicity at two and retain the
complete order relation on globally singleton variables. -/
structure SameCappedSingletonSignature
    (left right : Word Nat) : Prop where
  capped :
    ∀ letter,
      cappedMultiplicity left letter =
        cappedMultiplicity right letter
  singletonOrder :
    ∀ x y,
      SimplePrecedes left x y ↔
        SimplePrecedes right x y

abbrev sameSignature (left right : Word Nat) : Prop :=
  SameCappedSingletonSignature left right

namespace SameCappedSingletonSignature

theorem refl (word : Word Nat) :
    SameCappedSingletonSignature word word :=
  ⟨fun _ => rfl, fun _ _ => Iff.rfl⟩

theorem symm {left right : Word Nat}
    (same : SameCappedSingletonSignature left right) :
    SameCappedSingletonSignature right left :=
  ⟨fun letter => (same.capped letter).symm,
    fun x y => (same.singletonOrder x y).symm⟩

theorem trans {left middle right : Word Nat}
    (first : SameCappedSingletonSignature left middle)
    (second : SameCappedSingletonSignature middle right) :
    SameCappedSingletonSignature left right :=
  ⟨fun letter =>
      (first.capped letter).trans (second.capped letter),
    fun x y =>
      (first.singletonOrder x y).trans
        (second.singletonOrder x y)⟩

theorem absent {left right : Word Nat}
    (same : SameCappedSingletonSignature left right)
    (letter : Nat) :
    letter ∉ left.toList ↔ letter ∉ right.toList := by
  rw [← List.count_eq_zero, ← List.count_eq_zero,
    ← cappedMultiplicity_eq_zero_iff,
    ← cappedMultiplicity_eq_zero_iff,
    same.capped letter]

theorem support {left right : Word Nat}
    (same : SameCappedSingletonSignature left right)
    (letter : Nat) :
    letter ∈ left.toList ↔ letter ∈ right.toList := by
  simpa using not_congr (same.absent letter)

theorem simple {left right : Word Nat}
    (same : SameCappedSingletonSignature left right)
    (letter : Nat) :
    left.toList.count letter = 1 ↔
      right.toList.count letter = 1 := by
  rw [← cappedMultiplicity_eq_one_iff,
    ← cappedMultiplicity_eq_one_iff,
    same.capped letter]

theorem multiple {left right : Word Nat}
    (same : SameCappedSingletonSignature left right)
    (letter : Nat) :
    2 ≤ left.toList.count letter ↔
      2 ≤ right.toList.count letter := by
  rw [← cappedMultiplicity_eq_two_iff,
    ← cappedMultiplicity_eq_two_iff,
    same.capped letter]

theorem singletonSequence_eq {left right : Word Nat}
    (same : SameCappedSingletonSignature left right) :
    singletonSequence left = singletonSequence right := by
  apply nodup_eq_of_pairProjection_head
  · exact singletonSequence_nodup left
  · exact singletonSequence_nodup right
  · intro letter
    rw [mem_singletonSequence_iff,
      mem_singletonSequence_iff]
    exact same.simple letter
  · intro x y different xMember yMember
    have leftX :
        left.toList.count x = 1 :=
      (mem_singletonSequence_iff left x).1 xMember
    have leftY :
        left.toList.count y = 1 :=
      (mem_singletonSequence_iff left y).1 yMember
    have rightX :
        right.toList.count x = 1 :=
      (same.simple x).1 leftX
    have rightY :
        right.toList.count y = 1 :=
      (same.simple y).1 leftY
    have leftProjection :=
      singletonSequence_pairProjection
        left different leftX leftY
    have rightProjection :=
      singletonSequence_pairProjection
        right different rightX rightY
    rw [leftProjection, rightProjection]
    rcases pairProjection_shape left different leftX leftY with
        leftXY | leftYX <;>
      rcases pairProjection_shape right different rightX rightY with
        rightXY | rightYX
    · simp [leftXY, rightXY]
    · have leftPrecedes :
          SimplePrecedes left x y :=
        (simplePrecedes_iff_pairProjection_head
          left different leftX leftY).2 <| by
            simp [leftXY]
      have rightPrecedes :=
        (same.singletonOrder x y).1 leftPrecedes
      have rightHead :=
        (simplePrecedes_iff_pairProjection_head
          right different rightX rightY).1 rightPrecedes
      have impossible : False := by
        rw [rightYX] at rightHead
        have equal : y = x := Option.some.inj rightHead
        exact different equal.symm
      exact impossible.elim
    · have rightPrecedes :
          SimplePrecedes right x y :=
        (simplePrecedes_iff_pairProjection_head
          right different rightX rightY).2 <| by
            simp [rightXY]
      have leftPrecedes :=
        (same.singletonOrder x y).2 rightPrecedes
      have leftHead :=
        (simplePrecedes_iff_pairProjection_head
          left different leftX leftY).1 leftPrecedes
      have impossible : False := by
        rw [leftYX] at leftHead
        have equal : y = x := Option.some.inj leftHead
        exact different equal.symm
      exact impossible.elim
    · simp [leftYX, rightYX]

end SameCappedSingletonSignature

/-- Repeated variables in the deterministic order used by S5_213. -/
abbrev sortedRepeatedLetters (word : Word Nat) : List Nat :=
  S5_213Syntax.sortedRepeatedLetters word

theorem mem_sortedRepeatedLetters_iff
    (word : Word Nat) (letter : Nat) :
    letter ∈ sortedRepeatedLetters word ↔
      2 ≤ word.toList.count letter :=
  S5_213Syntax.mem_sortedRepeatedLetters_iff word letter

theorem sortedRepeatedLetters_nodup (word : Word Nat) :
    (sortedRepeatedLetters word).Nodup :=
  S5_213Syntax.sortedRepeatedLetters_nodup word

theorem sortedRepeatedLetters_pairwise (word : Word Nat) :
    (sortedRepeatedLetters word).Pairwise (· ≤ ·) :=
  S5_213Syntax.sortedRepeatedLetters_pairwise word

private theorem sorted_nodup_eq_of_mem_iff
    {left right : List Nat}
    (leftSorted : left.Pairwise (· ≤ ·))
    (rightSorted : right.Pairwise (· ≤ ·))
    (leftNodup : left.Nodup)
    (rightNodup : right.Nodup)
    (sameMem : ∀ letter, letter ∈ left ↔ letter ∈ right) :
    left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons head tail =>
          have := (sameMem head).2 (List.Mem.head tail)
          contradiction
  | cons leftHead leftTail induction =>
      cases right with
      | nil =>
          have := (sameMem leftHead).1
            (List.Mem.head leftTail)
          contradiction
      | cons rightHead rightTail =>
          have leftInRight :=
            (sameMem leftHead).1 (List.Mem.head leftTail)
          have rightInLeft :=
            (sameMem rightHead).2 (List.Mem.head rightTail)
          have rightLeLeft : rightHead ≤ leftHead := by
            by_cases equal : leftHead = rightHead
            · omega
            · have tailMember : leftHead ∈ rightTail := by
                simpa [equal] using leftInRight
              exact
                List.rel_of_pairwise_cons rightSorted tailMember
          have leftLeRight : leftHead ≤ rightHead := by
            by_cases equal : rightHead = leftHead
            · omega
            · have tailMember : rightHead ∈ leftTail := by
                simpa [equal] using rightInLeft
              exact
                List.rel_of_pairwise_cons leftSorted tailMember
          have headsEqual : leftHead = rightHead := by omega
          subst rightHead
          congr 1
          apply induction
            leftSorted.tail rightSorted.tail
            leftNodup.tail rightNodup.tail
          intro letter
          by_cases equal : letter = leftHead
          · subst letter
            have leftAbsent : leftHead ∉ leftTail :=
              (List.nodup_cons.mp leftNodup).1
            have rightAbsent : leftHead ∉ rightTail :=
              (List.nodup_cons.mp rightNodup).1
            simp [leftAbsent, rightAbsent]
          · simpa [equal] using sameMem letter

/-- Every repeated variable is rendered by one double block. -/
def renderRepeatedBlock (letter : Nat) : List Nat :=
  [letter, letter]

/-- Canonical form: ordered singletons followed by sorted double blocks. -/
def canonicalList (word : Word Nat) : List Nat :=
  singletonSequence word ++
    (sortedRepeatedLetters word).flatMap renderRepeatedBlock

namespace SameCappedSingletonSignature

theorem sortedRepeatedLetters_eq {left right : Word Nat}
    (same : SameCappedSingletonSignature left right) :
    sortedRepeatedLetters left =
      sortedRepeatedLetters right := by
  apply sorted_nodup_eq_of_mem_iff
    (sortedRepeatedLetters_pairwise left)
    (sortedRepeatedLetters_pairwise right)
    (sortedRepeatedLetters_nodup left)
    (sortedRepeatedLetters_nodup right)
  intro letter
  rw [mem_sortedRepeatedLetters_iff,
    mem_sortedRepeatedLetters_iff]
  exact same.multiple letter

theorem canonicalList_eq {left right : Word Nat}
    (same : SameCappedSingletonSignature left right) :
    canonicalList left = canonicalList right := by
  unfold canonicalList
  rw [same.singletonSequence_eq,
    same.sortedRepeatedLetters_eq]

end SameCappedSingletonSignature

private def wordOfListOr
    (fallback : Nat) : List Nat → Word Nat
  | [] => Word.singleton fallback
  | head :: tail => ⟨head, tail⟩

def canonicalWord (word : Word Nat) : Word Nat :=
  wordOfListOr word.head (canonicalList word)

theorem head_mem_canonicalList (word : Word Nat) :
    word.head ∈ canonicalList word := by
  have headMember : word.head ∈ word.toList := by
    cases word with
    | mk head tail =>
        simp [Word.toList]
  have headPositive : 0 < word.toList.count word.head :=
    List.count_pos_iff.mpr headMember
  by_cases simple : word.toList.count word.head = 1
  · apply List.mem_append_left
    exact (mem_singletonSequence_iff word word.head).2 simple
  · have multiple : 2 ≤ word.toList.count word.head := by
      omega
    apply List.mem_append_right (singletonSequence word)
    apply List.mem_flatMap.mpr
    exact
      ⟨word.head,
        (mem_sortedRepeatedLetters_iff word word.head).2 multiple,
        by simp [renderRepeatedBlock]⟩

theorem canonicalList_ne_nil (word : Word Nat) :
    canonicalList word ≠ [] :=
  List.ne_nil_of_mem (head_mem_canonicalList word)

@[simp]
theorem toList_canonicalWord (word : Word Nat) :
    (canonicalWord word).toList = canonicalList word := by
  unfold canonicalWord
  cases canonical : canonicalList word with
  | nil =>
      exact False.elim <|
        canonicalList_ne_nil word canonical
  | cons head tail =>
      rfl

namespace SameCappedSingletonSignature

theorem canonicalWord_eq {left right : Word Nat}
    (same : SameCappedSingletonSignature left right) :
    canonicalWord left = canonicalWord right := by
  apply Word.toList_injective
  rw [toList_canonicalWord, toList_canonicalWord,
    same.canonicalList_eq]

end SameCappedSingletonSignature

end SemigroupBasis.CoRoots.S5_110Syntax
