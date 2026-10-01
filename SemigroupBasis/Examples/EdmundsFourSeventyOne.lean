import SemigroupBasis.Examples.EdmundsFiveTwoFour

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- The zero-based multiplication of the opposite of Edmunds' `S(4,23)`. -/
def edmundsFourSeventyOneOppositeMul (a b : Fin 4) : Fin 4 :=
  if a = 0 then 0 else
    if a = 1 then
      (if b = 0 then 0 else if b = 1 then 0 else 1)
    else
      if a = 2 then (if b = 0 then 0 else if b = 1 then 0 else 2) else b

/-- The opposite orientation is convenient for the first-occurrence block
normal form: `xyx = xxy` gathers repeats into their first block. -/
def edmundsFourSeventyOneOpposite : FiniteTable where
  order := 4
  mul := edmundsFourSeventyOneOppositeMul
  assoc := by decide

/-- The zero-based multiplication of Edmunds' `S(4,23)` in the stored
Smallsemi orientation. -/
def edmundsFourSeventyOneMul (a b : Fin 4) : Fin 4 :=
  edmundsFourSeventyOneOppositeMul b a

def edmundsFourSeventyOne : FiniteTable where
  order := 4
  mul := edmundsFourSeventyOneMul
  assoc := by decide

def squareBlockXX : Word Nat := ⟨0, [0]⟩
def squareBlockXXX : Word Nat := ⟨0, [0, 0]⟩
def squareBlockXYX : Word Nat := ⟨0, [1, 0]⟩
def squareBlockXXY : Word Nat := ⟨0, [0, 1]⟩
def squareBlockXXYY : Word Nat := ⟨0, [0, 1, 1]⟩
def squareBlockYYXX : Word Nat := ⟨1, [1, 0, 0]⟩

def squareBlockPowerLaw : Identity Nat :=
  ⟨squareBlockXX, squareBlockXXX⟩

def squareBlockGatherLaw : Identity Nat :=
  ⟨squareBlockXYX, squareBlockXXY⟩

def squareBlockCommutationLaw : Identity Nat :=
  ⟨squareBlockYYXX, squareBlockXXYY⟩

/-- The reversed Edmunds basis
`xx = xxx`, `xyx = xxy`, `xxyy = yyxx`. -/
def squareBlockBasis : List (Identity Nat) :=
  [squareBlockPowerLaw, squareBlockGatherLaw,
    squareBlockCommutationLaw]

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

theorem squareBlockDerivesSquareCommutation (u v : Word Nat) :
    Derives squareBlockBasis
      ((u ++ u) ++ (v ++ v)) ((v ++ v) ++ (u ++ u)) := by
  have hbase :
      Derives squareBlockBasis squareBlockXXYY squareBlockYYXX :=
    Derives.symm <|
      Derives.fromBasis (e := squareBlockCommutationLaw) <| by
        exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [squareBlockBasis, squareBlockCommutationLaw,
    squareBlockXXYY, squareBlockYYXX, instantiateTwoWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using h

private theorem edmundsAxiomsDerive :
    ∀ e : Identity Nat, e ∈ edmundsFiveTwoFourBasis →
      Derives squareBlockBasis e.lhs e.rhs := by
  intro e he
  simp only [edmundsFiveTwoFourBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact Derives.fromBasis (e := squareBlockPowerLaw) <| by
      exact List.Mem.head _
  · exact Derives.fromBasis (e := squareBlockGatherLaw) <| by
      exact List.Mem.tail _ (List.Mem.head _)

theorem squareBlockDerivesEdmundsNormal (w : Word Nat) :
    match edmundsNormalList w.toList with
    | [] => False
    | x :: xs =>
        Derives squareBlockBasis w ⟨x, xs⟩ := by
  have h := edmundsDerivesNormal w
  cases hn : edmundsNormalList w.toList with
  | nil =>
      rw [hn] at h
      exact h
  | cons x xs =>
      rw [hn] at h
      exact h.transport edmundsAxiomsDerive

private inductive BlockNormal : List Nat → Prop
  | nil : BlockNormal []
  | single (x : Nat) (xs : List Nat) :
      BlockNormal xs → x ∉ xs → BlockNormal (x :: xs)
  | double (x : Nat) (xs : List Nat) :
      BlockNormal xs → x ∉ xs → BlockNormal (x :: x :: xs)

private theorem BlockNormal.filter_ne
    {xs : List Nat} (normal : BlockNormal xs) (x : Nat) :
    BlockNormal (xs.filter (fun y => decide (y ≠ x))) := by
  induction normal with
  | nil =>
      exact BlockNormal.nil
  | single y ys normalY yNotMem ih =>
      by_cases hyx : y = x
      · subst y
        have tailFilterEq :
            ys.filter (fun z => decide (z ≠ x)) = ys := by
          apply List.filter_eq_self.mpr
          intro z hz
          have hzx : z ≠ x := by
            intro h
            subst z
            exact yNotMem hz
          simp [hzx]
        simpa using ih
      · have yNotMemFilter :
            y ∉ ys.filter (fun z => decide (z ≠ x)) := by
          simp only [List.mem_filter]
          exact fun h => yNotMem h.1
        simpa [hyx] using
          BlockNormal.single y
            (ys.filter (fun z => decide (z ≠ x))) ih yNotMemFilter
  | double y ys normalY yNotMem ih =>
      by_cases hyx : y = x
      · subst y
        have tailFilterEq :
            ys.filter (fun z => decide (z ≠ x)) = ys := by
          apply List.filter_eq_self.mpr
          intro z hz
          have hzx : z ≠ x := by
            intro h
            subst z
            exact yNotMem hz
          simp [hzx]
        simpa using ih
      · have yNotMemFilter :
            y ∉ ys.filter (fun z => decide (z ≠ x)) := by
          simp only [List.mem_filter]
          exact fun h => yNotMem h.1
        simpa [hyx] using
          BlockNormal.double y
            (ys.filter (fun z => decide (z ≠ x))) ih yNotMemFilter

private theorem edmundsNormalList_blockNormal :
    ∀ xs : List Nat, BlockNormal (edmundsNormalList xs)
  | [] => BlockNormal.nil
  | x :: xs => by
      have restNormal := edmundsNormalList_blockNormal xs
      by_cases hx : x ∈ edmundsNormalList xs
      · have filteredNormal := restNormal.filter_ne x
        have xNotMem :
            x ∉ (edmundsNormalList xs).filter
              (fun y => decide (y ≠ x)) := by
          simp
        simpa [edmundsNormalList, hx] using
          BlockNormal.double x
            ((edmundsNormalList xs).filter
              (fun y => decide (y ≠ x)))
            filteredNormal xNotMem
      · simpa [edmundsNormalList, hx] using
          BlockNormal.single x (edmundsNormalList xs) restNormal hx

private inductive SquareBlock where
  | single : Nat → SquareBlock
  | double : Nat → SquareBlock
deriving DecidableEq, Repr

private def SquareBlock.label : SquareBlock → Nat
  | .single x => x
  | .double x => x

private def SquareBlock.render : SquareBlock → List Nat
  | .single x => [x]
  | .double x => [x, x]

private def renderBlocks (blocks : List SquareBlock) : List Nat :=
  blocks.flatMap SquareBlock.render

private def blocksOfList : List Nat → List SquareBlock
  | [] => []
  | [x] => [.single x]
  | x :: y :: xs =>
      if x = y then
        .double x :: blocksOfList xs
      else
        .single x :: blocksOfList (y :: xs)
termination_by xs => xs.length

private theorem render_blocksOfList_of_normal
    {xs : List Nat} (normal : BlockNormal xs) :
    renderBlocks (blocksOfList xs) = xs := by
  induction normal with
  | nil => simp [renderBlocks, blocksOfList]
  | single x xs normal xNotMem ih =>
      cases xs with
      | nil => simp [renderBlocks, blocksOfList, SquareBlock.render]
      | cons y ys =>
          have hxy : x ≠ y := by
            intro h
            subst y
            exact xNotMem (List.Mem.head ys)
          simp only [blocksOfList, hxy, ↓reduceIte, renderBlocks,
            List.flatMap_cons, SquareBlock.render]
          change [x] ++ renderBlocks (blocksOfList (y :: ys)) =
            x :: y :: ys
          rw [ih]
          rfl
  | double x xs normal _ ih =>
      simp only [blocksOfList, ↓reduceIte, renderBlocks,
        List.flatMap_cons, SquareBlock.render]
      change [x, x] ++ renderBlocks (blocksOfList xs) = x :: x :: xs
      rw [ih]
      rfl

private structure SquareSegment where
  doubles : List Nat
  singleton : Option Nat
deriving DecidableEq, Repr

private def blocksToSegments : List SquareBlock → List SquareSegment
  | [] => []
  | .single x :: blocks =>
      ⟨[], some x⟩ :: blocksToSegments blocks
  | .double x :: blocks =>
      match blocksToSegments blocks with
      | [] => [⟨[x], none⟩]
      | segment :: rest =>
          ⟨x :: segment.doubles, segment.singleton⟩ :: rest

private def segmentToBlocks (segment : SquareSegment) : List SquareBlock :=
  segment.doubles.map SquareBlock.double ++
    match segment.singleton with
    | none => []
    | some x => [.single x]

private def segmentsToBlocks (segments : List SquareSegment) :
    List SquareBlock :=
  segments.flatMap segmentToBlocks

private theorem segments_blocks_roundtrip :
    ∀ blocks : List SquareBlock,
      segmentsToBlocks (blocksToSegments blocks) = blocks
  | [] => rfl
  | .single x :: blocks => by
      simp only [blocksToSegments, segmentsToBlocks, List.flatMap_cons,
        segmentToBlocks, List.map_nil, List.nil_append, Option.toList_some,
        List.append_nil]
      change SquareBlock.single x ::
          segmentsToBlocks (blocksToSegments blocks) =
        SquareBlock.single x :: blocks
      rw [segments_blocks_roundtrip blocks]
  | .double x :: blocks => by
      cases h : blocksToSegments blocks with
      | nil =>
          have blocksEmpty : blocks = [] := by
            have roundtrip := segments_blocks_roundtrip blocks
            rw [h] at roundtrip
            simpa [segmentsToBlocks] using roundtrip.symm
          subst blocks
          rfl
      | cons segment rest =>
          have roundtrip := segments_blocks_roundtrip blocks
          rw [h] at roundtrip
          simp only [segmentsToBlocks, List.flatMap_cons] at roundtrip
          simp only [blocksToSegments, h, segmentsToBlocks,
            List.flatMap_cons, segmentToBlocks, List.map_cons]
          change SquareBlock.double x ::
              (segmentToBlocks segment ++
                segmentsToBlocks rest) =
            SquareBlock.double x :: blocks
          change SquareBlock.double x ::
              (segmentToBlocks segment ++
                List.flatMap segmentToBlocks rest) =
            SquareBlock.double x :: blocks
          rw [roundtrip]

private def sortSegment (segment : SquareSegment) : SquareSegment :=
  ⟨segment.doubles.mergeSort (fun x y : Nat => decide (x ≤ y)),
    segment.singleton⟩

private def canonicalBlocks (blocks : List SquareBlock) : List SquareBlock :=
  segmentsToBlocks ((blocksToSegments blocks).map sortSegment)

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private inductive ListDerives :
    List Nat → List Nat → Prop
  | empty : ListDerives [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives squareBlockBasis
        (wordOfCons x xs) (wordOfCons y ys) →
      ListDerives (x :: xs) (y :: ys)

private theorem ListDerives.refl :
    ∀ xs : List Nat, ListDerives xs xs
  | [] => ListDerives.empty
  | x :: xs => ListDerives.words (Derives.refl _)

private theorem ListDerives.trans
    {xs ys zs : List Nat}
    (first : ListDerives xs ys) (second : ListDerives ys zs) :
    ListDerives xs zs := by
  cases first with
  | empty =>
      cases second
      exact ListDerives.empty
  | words hfirst =>
      cases second with
      | words hsecond =>
          exact ListDerives.words (Derives.trans hfirst hsecond)

private theorem ListDerives.symm
    {xs ys : List Nat} (h : ListDerives xs ys) :
    ListDerives ys xs := by
  cases h with
  | empty => exact ListDerives.empty
  | words derivation =>
      exact ListDerives.words (Derives.symm derivation)

private theorem ListDerives.from_cons
    {x : Nat} {xs target : List Nat}
    (h : ListDerives (x :: xs) target) :
    ∃ y ys, target = y :: ys ∧
      Derives squareBlockBasis
        (wordOfCons x xs) (wordOfCons y ys) := by
  cases h with
  | words derivation =>
      exact ⟨_, _, rfl, derivation⟩

private theorem ListDerives.prepend
    (pre : List Nat) {xs ys : List Nat}
    (h : ListDerives xs ys) :
    ListDerives (pre ++ xs) (pre ++ ys) := by
  cases pre with
  | nil => simpa using h
  | cons p ps =>
      cases h with
      | empty =>
          simpa using ListDerives.refl (p :: ps)
      | @words x y xs ys derivation =>
          exact ListDerives.words <| by
            have prefixed :=
              Derives.prepend (wordOfCons p ps) derivation
            simpa [wordOfCons, Word.append, List.append_assoc] using prefixed

private theorem ListDerives.append
    {xs ys : List Nat} (h : ListDerives xs ys)
    (suffix : List Nat) :
    ListDerives (xs ++ suffix) (ys ++ suffix) := by
  cases h with
  | empty =>
      exact ListDerives.refl suffix
  | @words x y xs ys derivation =>
      cases suffix with
      | nil =>
          simpa using ListDerives.words derivation
      | cons z zs =>
          exact ListDerives.words <| by
            have appended :=
              Derives.appendRight derivation (wordOfCons z zs)
            simpa [wordOfCons, Word.append, List.append_assoc] using appended

private def renderDoubles (xs : List Nat) : List Nat :=
  xs.flatMap (fun x => [x, x])

private theorem count_renderDoubles (z : Nat) :
    ∀ xs : List Nat,
      (renderDoubles xs).count z = 2 * xs.count z
  | [] => by simp [renderDoubles]
  | x :: xs => by
      simp only [renderDoubles, List.flatMap_cons, List.count_append]
      change List.count z [x, x] + List.count z (renderDoubles xs) =
        2 * List.count z (x :: xs)
      rw [count_renderDoubles z xs]
      by_cases hx : x = z
      · subst x
        simp
        omega
      · simp [hx]

private theorem squareBlockDerivesDoublePermutation
    {xs ys : List Nat} (h : xs.Perm ys) :
    ListDerives (renderDoubles xs) (renderDoubles ys) := by
  induction h with
  | nil =>
      exact ListDerives.empty
  | cons x _ ih =>
      simpa [renderDoubles] using ih.prepend [x, x]
  | swap x y rest =>
      have swapWords :
          ListDerives [x, x, y, y] [y, y, x, x] :=
        ListDerives.words <| by
          simpa [wordOfCons, Word.append, Word.singleton,
            Word.append_assoc] using
              squareBlockDerivesSquareCommutation
                (Word.singleton x) (Word.singleton y)
      simpa [renderDoubles] using
        (swapWords.append (renderDoubles rest)).symm
  | trans _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂

private def renderSegment (segment : SquareSegment) : List Nat :=
  renderDoubles segment.doubles ++ segment.singleton.toList

private def renderSegments (segments : List SquareSegment) : List Nat :=
  segments.flatMap renderSegment

private theorem renderBlocks_append
    (left right : List SquareBlock) :
    renderBlocks (left ++ right) =
      renderBlocks left ++ renderBlocks right := by
  simp [renderBlocks, List.flatMap_append]

private theorem render_double_blocks (xs : List Nat) :
    renderBlocks (xs.map SquareBlock.double) = renderDoubles xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, renderBlocks, List.flatMap_cons,
        SquareBlock.render, renderDoubles]
      change [x, x] ++ renderBlocks (xs.map SquareBlock.double) =
        [x, x] ++ renderDoubles xs
      rw [ih]

private theorem render_segmentToBlocks (segment : SquareSegment) :
    renderBlocks (segmentToBlocks segment) = renderSegment segment := by
  cases segment with
  | mk doubles singleton =>
      cases singleton <;>
        simp only [segmentToBlocks, renderSegment, Option.toList_none,
          Option.toList_some, List.append_nil]
      · exact render_double_blocks doubles
      · rw [renderBlocks_append, render_double_blocks]
        rfl

private theorem render_segments_eq_render_blocks (segments : List SquareSegment) :
    renderBlocks (segmentsToBlocks segments) = renderSegments segments := by
  induction segments with
  | nil => rfl
  | cons segment rest ih =>
      simp only [segmentsToBlocks, List.flatMap_cons, renderSegments,
        List.flatMap_cons]
      change
        renderBlocks (segmentToBlocks segment ++
            segmentsToBlocks rest) =
          renderSegment segment ++ renderSegments rest
      rw [renderBlocks_append, render_segmentToBlocks, ih]

private theorem canonicalSegmentsDerive :
    ∀ segments : List SquareSegment,
      ListDerives (renderSegments segments)
        (renderSegments (segments.map sortSegment))
  | [] => ListDerives.empty
  | segment :: rest => by
      have runPerm :
          (segment.doubles.mergeSort (fun x y => x ≤ y)).Perm
            segment.doubles :=
        List.mergeSort_perm _ _
      have runDerives :
          ListDerives (renderDoubles segment.doubles)
            (renderDoubles
              (segment.doubles.mergeSort (fun x y => x ≤ y))) :=
        squareBlockDerivesDoublePermutation runPerm.symm
      have segmentDerives :
          ListDerives (renderSegment segment)
            (renderSegment (sortSegment segment)) := by
        simpa [renderSegment, sortSegment] using
          runDerives.append segment.singleton.toList
      have firstStep :=
        segmentDerives.append (renderSegments rest)
      have restStep :=
        (canonicalSegmentsDerive rest).prepend
          (renderSegment (sortSegment segment))
      simpa only [renderSegments, List.flatMap_cons, List.map_cons] using
        firstStep.trans restStep

private theorem canonicalBlocksDerive (blocks : List SquareBlock) :
    ListDerives (renderBlocks blocks)
      (renderBlocks (canonicalBlocks blocks)) := by
  have h := canonicalSegmentsDerive (blocksToSegments blocks)
  rw [← render_segments_eq_render_blocks,
    ← render_segments_eq_render_blocks] at h
  simpa [canonicalBlocks, segments_blocks_roundtrip] using h

private def statusState (n : Nat) : Fin 4 :=
  if n = 0 then 3 else if n = 1 then 1 else 0

private def statusValuation (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 1 else 3

private theorem statusTransition (n : Nat) :
    edmundsFourSeventyOneOppositeMul
        (statusState n) 1 =
      statusState (n + 1) := by
  by_cases hn0 : n = 0
  · subst n
    rfl
  · by_cases hn1 : n = 1
    · subst n
      rfl
    · simp [edmundsFourSeventyOneOppositeMul, statusState, hn0, hn1]

private theorem statusIdentity (n : Nat) :
    edmundsFourSeventyOneOppositeMul
        (statusState n) 3 = statusState n := by
  by_cases hn0 : n = 0
  · subst n
    rfl
  · by_cases hn1 : n = 1
    · subst n
      rfl
    · simp [edmundsFourSeventyOneOppositeMul, statusState, hn0, hn1]

private theorem statusFold (z : Nat) :
    ∀ (xs : List Nat) (n : Nat),
      xs.foldl
          (fun current x =>
            edmundsFourSeventyOneOppositeMul current
              (statusValuation z x))
          (statusState n) =
        statusState (n + xs.count z)
  | [], n => by simp
  | x :: xs, n => by
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [show statusValuation z z = (1 : Fin 4) by
          simp [statusValuation]]
        rw [statusTransition, statusFold]
        rw [List.count_cons_self]
        congr 1
        omega
      · rw [show statusValuation z x = (3 : Fin 4) by
          simp [statusValuation, hx]]
        rw [statusIdentity, statusFold, List.count_cons_of_ne hx]

private def listEval
    (valuation : Nat → Fin 4) (xs : List Nat) : Fin 4 :=
  xs.foldl
    (fun current x =>
      edmundsFourSeventyOneOppositeMul current (valuation x)) 3

private theorem listEval_status (z : Nat) (xs : List Nat) :
    listEval (statusValuation z) xs =
      statusState (xs.count z) := by
  simpa [listEval, statusState] using statusFold z xs 0

private theorem statusState_injective_below_three
    {m n : Nat} (hm : m ≤ 2) (hn : n ≤ 2)
    (h : statusState m = statusState n) :
    m = n := by
  by_cases hm0 : m = 0
  · subst m
    by_cases hn0 : n = 0
    · exact hn0.symm
    · by_cases hn1 : n = 1
      · subst n
        simp [statusState] at h
      · have hn2 : n = 2 := by omega
        subst n
        simp [statusState] at h
  · by_cases hm1 : m = 1
    · subst m
      by_cases hn0 : n = 0
      · subst n
        simp [statusState] at h
      · by_cases hn1 : n = 1
        · exact hn1.symm
        · have hn2 : n = 2 := by omega
          subst n
          simp [statusState] at h
    · have hm2 : m = 2 := by omega
      subst m
      by_cases hn0 : n = 0
      · subst n
        simp [statusState] at h
      · by_cases hn1 : n = 1
        · subst n
          simp [statusState] at h
        · omega

private theorem blockNormal_count_le_two
    {xs : List Nat} (normal : BlockNormal xs) (z : Nat) :
    xs.count z ≤ 2 := by
  induction normal with
  | nil => simp
  | single x xs _ xNotMem ih =>
      by_cases hzx : z = x
      · subst z
        simp [List.count_eq_zero.mpr xNotMem]
      · rw [List.count_cons_of_ne (Ne.symm hzx)]
        exact ih
  | double x xs _ xNotMem ih =>
      by_cases hzx : z = x
      · subst z
        simp [List.count_eq_zero.mpr xNotMem]
      · rw [List.count_cons_of_ne (Ne.symm hzx),
          List.count_cons_of_ne (Ne.symm hzx)]
        exact ih

private theorem fold_all_three :
    ∀ (xs : List Nat) (acc : Fin 4),
      xs.foldl
          (fun current _ =>
            edmundsFourSeventyOneOppositeMul current 3) acc = acc
  | [], _ => rfl
  | _ :: xs, acc => by
      simp only [List.foldl_cons]
      have rightIdentity :
          edmundsFourSeventyOneOppositeMul acc 3 = acc := by
        decide +revert
      rw [rightIdentity]
      exact fold_all_three xs acc

private theorem fold_congr
    (v₁ v₂ : Nat → Fin 4) :
    ∀ (xs : List Nat) (acc : Fin 4),
      (∀ x, x ∈ xs → v₁ x = v₂ x) →
      xs.foldl
          (fun current x =>
            edmundsFourSeventyOneOppositeMul current (v₁ x)) acc =
        xs.foldl
          (fun current x =>
            edmundsFourSeventyOneOppositeMul current (v₂ x)) acc
  | [], _, _ => rfl
  | x :: xs, acc, agree => by
      simp only [List.foldl_cons]
      rw [agree x (List.Mem.head xs)]
      exact fold_congr v₁ v₂ xs
        (edmundsFourSeventyOneOppositeMul acc (v₂ x))
        (fun y hy => agree y (List.Mem.tail x hy))

private theorem listEval_congr
    (v₁ v₂ : Nat → Fin 4) (xs : List Nat)
    (agree : ∀ x, x ∈ xs → v₁ x = v₂ x) :
    listEval v₁ xs = listEval v₂ xs :=
  fold_congr v₁ v₂ xs 3 agree

private theorem eval_eq_listEval
    (valuation : Nat → Fin 4) (w : Word Nat) :
    edmundsFourSeventyOneOpposite.semigroup.eval valuation w =
      listEval valuation w.toList := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              edmundsFourSeventyOneOppositeMul current (valuation x))
            (valuation head) =
          tail.foldl
            (fun current x =>
              edmundsFourSeventyOneOppositeMul current (valuation x))
            (edmundsFourSeventyOneOppositeMul 3 (valuation head))
      have leftIdentity :
          edmundsFourSeventyOneOppositeMul 3 (valuation head) =
            valuation head := by
        cases h : valuation head <;> rfl
      rw [leftIdentity]

private def markerValuation (marker selected : Nat) : Nat → Fin 4 :=
  fun x => if x = marker then 1 else if x = selected then 2 else 3

private theorem fold_values_two_three_preserves_one
    (marker selected : Nat) :
    ∀ xs : List Nat,
      marker ∉ xs →
      xs.foldl
          (fun current x =>
            edmundsFourSeventyOneOppositeMul current
              (markerValuation marker selected x))
          1 = 1
  | [], _ => rfl
  | x :: xs, markerNotMem => by
      have hx : x ≠ marker := by
        intro h
        subst x
        exact markerNotMem (List.Mem.head xs)
      simp only [List.foldl_cons]
      have step :
          edmundsFourSeventyOneOppositeMul 1
              (markerValuation marker selected x) = 1 := by
        by_cases hsel : x = selected
        · subst x
          simp [markerValuation, hx,
            edmundsFourSeventyOneOppositeMul]
        · simp [markerValuation, hx, hsel,
            edmundsFourSeventyOneOppositeMul]
      rw [step]
      exact fold_values_two_three_preserves_one marker selected xs
        (fun h => markerNotMem (List.Mem.tail x h))

private theorem fold_values_two_three_preserves_zero
    (marker selected : Nat) :
    ∀ xs : List Nat,
      marker ∉ xs →
      xs.foldl
          (fun current x =>
            edmundsFourSeventyOneOppositeMul current
              (markerValuation marker selected x))
          0 = 0
  | [], _ => rfl
  | x :: xs, markerNotMem => by
      have hx : x ≠ marker := by
        intro h
        subst x
        exact markerNotMem (List.Mem.head xs)
      simp only [List.foldl_cons]
      have step :
          edmundsFourSeventyOneOppositeMul 0
              (markerValuation marker selected x) = 0 := by
        simp [edmundsFourSeventyOneOppositeMul]
      rw [step]
      exact fold_values_two_three_preserves_zero marker selected xs
        (fun h => markerNotMem (List.Mem.tail x h))

private theorem fold_values_two_three_preserves_two
    (marker selected : Nat) :
    ∀ xs : List Nat,
      marker ∉ xs →
      xs.foldl
          (fun current x =>
            edmundsFourSeventyOneOppositeMul current
              (markerValuation marker selected x))
          2 = 2
  | [], _ => rfl
  | x :: xs, markerNotMem => by
      have hx : x ≠ marker := by
        intro h
        subst x
        exact markerNotMem (List.Mem.head xs)
      simp only [List.foldl_cons]
      have step :
          edmundsFourSeventyOneOppositeMul 2
              (markerValuation marker selected x) = 2 := by
        by_cases hsel : x = selected
        · subst x
          simp [markerValuation, hx,
            edmundsFourSeventyOneOppositeMul]
        · simp [markerValuation, hx, hsel,
            edmundsFourSeventyOneOppositeMul]
      rw [step]
      exact fold_values_two_three_preserves_two marker selected xs
        (fun h => markerNotMem (List.Mem.tail x h))

private theorem fold_before_marker
    (marker selected : Nat) :
    ∀ xs : List Nat,
      marker ∉ xs →
      xs.foldl
          (fun current x =>
            edmundsFourSeventyOneOppositeMul current
              (markerValuation marker selected x))
          3 =
        (if selected ∈ xs then 2 else 3)
  | [], _ => by simp
  | x :: xs, markerNotMem => by
      have hx : x ≠ marker := by
        intro h
        subst x
        exact markerNotMem (List.Mem.head xs)
      simp only [List.foldl_cons]
      by_cases hsel : x = selected
      · subst x
        have selectedStep :
            edmundsFourSeventyOneOppositeMul 3
              (markerValuation marker selected selected) = 2 := by
          simp [markerValuation, hx,
            edmundsFourSeventyOneOppositeMul]
        rw [selectedStep]
        have preserveTwo :=
          fold_values_two_three_preserves_two
            marker selected xs
            (fun h => markerNotMem (List.Mem.tail selected h))
        rw [preserveTwo]
        simp
      · have identityStep :
            edmundsFourSeventyOneOppositeMul 3
              (markerValuation marker selected x) = 3 := by
          simp [markerValuation, hx, hsel,
            edmundsFourSeventyOneOppositeMul]
        rw [identityStep, fold_before_marker marker selected xs
          (fun h => markerNotMem (List.Mem.tail x h))]
        have hne : selected ≠ x := Ne.symm hsel
        simp [hne]

private theorem listEval_marker_split
    (marker selected : Nat) (pre suffix : List Nat)
    (markerPrefix : marker ∉ pre)
    (markerSuffix : marker ∉ suffix) :
    listEval (markerValuation marker selected)
        (pre ++ marker :: suffix) =
      if selected ∈ pre then 0 else 1 := by
  unfold listEval
  rw [List.foldl_append]
  rw [fold_before_marker marker selected pre markerPrefix]
  simp only [List.foldl_cons]
  split <;> rename_i hselected
  · have markerNeSelected : marker ≠ selected := by
      intro h
      subst selected
      exact markerPrefix hselected
    have markerValue :
        markerValuation marker selected marker = (1 : Fin 4) := by
      simp [markerValuation]
    rw [markerValue]
    have kill :
        edmundsFourSeventyOneOppositeMul 2 1 = (0 : Fin 4) := rfl
    rw [kill]
    exact fold_values_two_three_preserves_zero
      marker selected suffix markerSuffix
  · have markerValue :
        markerValuation marker selected marker = (1 : Fin 4) := by
      simp [markerValuation]
    rw [markerValue]
    have start :
        edmundsFourSeventyOneOppositeMul 3 1 = (1 : Fin 4) := rfl
    rw [start]
    exact fold_values_two_three_preserves_one
      marker selected suffix markerSuffix

private theorem sorted_eq_of_mem_iff
    {xs ys : List Nat}
    (sortedX : xs.Pairwise (· ≤ ·))
    (sortedY : ys.Pairwise (· ≤ ·))
    (nodupX : xs.Nodup) (nodupY : ys.Nodup)
    (sameMem : ∀ z, z ∈ xs ↔ z ∈ ys) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys =>
          have := (sameMem y).2 (List.Mem.head ys)
          contradiction
  | cons x xs ih =>
      cases ys with
      | nil =>
          have := (sameMem x).1 (List.Mem.head xs)
          contradiction
      | cons y ys =>
          have xInY := (sameMem x).1 (List.Mem.head xs)
          have yInX := (sameMem y).2 (List.Mem.head ys)
          have yLeX : y ≤ x := by
            by_cases hxy : x = y
            · omega
            · have xTail : x ∈ ys := by
                simpa [hxy] using xInY
              exact List.rel_of_pairwise_cons sortedY xTail
          have xLeY : x ≤ y := by
            by_cases hyx : y = x
            · omega
            · have yTail : y ∈ xs := by
                simpa [hyx] using yInX
              exact List.rel_of_pairwise_cons sortedX yTail
          have hxy : x = y := by omega
          subst y
          congr 1
          apply ih sortedX.tail sortedY.tail nodupX.tail nodupY.tail
          intro z
          by_cases hzx : z = x
          · subst z
            have hxnot : x ∉ xs := by
              intro hx
              exact (List.rel_of_pairwise_cons nodupX hx) rfl
            have hynot : x ∉ ys := by
              intro hy
              exact (List.rel_of_pairwise_cons nodupY hy) rfl
            simp [hxnot, hynot]
          · simpa [hzx] using sameMem z

private def segmentLabels (segment : SquareSegment) : List Nat :=
  segment.doubles ++ segment.singleton.toList

private def allSegmentLabels (segments : List SquareSegment) : List Nat :=
  segments.flatMap segmentLabels

private def SegmentsCanonical (segments : List SquareSegment) : Prop :=
  (allSegmentLabels segments).Nodup ∧
    (∀ segment, segment ∈ segments →
      segment.doubles.Pairwise (· ≤ ·)) ∧
    (∀ before segment rest,
      segments = before ++ segment :: rest →
      segment.singleton = none → rest = []) ∧
    (∀ segment, segment ∈ segments →
      segment.doubles = [] → segment.singleton.isSome)

private theorem count_renderSegments (z : Nat) :
    ∀ segments : List SquareSegment,
      (renderSegments segments).count z =
        2 * (segments.flatMap SquareSegment.doubles).count z +
          (segments.filterMap SquareSegment.singleton).count z
  | [] => by simp [renderSegments]
  | segment :: rest => by
      rw [show renderSegments (segment :: rest) =
        renderSegment segment ++ renderSegments rest by rfl]
      rw [List.count_append]
      cases segment with
      | mk doubles singleton =>
          cases singleton with
          | none =>
              simp only [renderSegment, Option.toList_none,
                List.append_nil, List.flatMap_cons,
                List.filterMap_cons_none]
              rw [count_renderDoubles, count_renderSegments]
              rw [List.count_append]
              omega
          | some x =>
              change
                (renderDoubles doubles ++ [x]).count z +
                    (renderSegments rest).count z =
                  2 * (doubles ++
                    rest.flatMap SquareSegment.doubles).count z +
                    (x :: rest.filterMap
                      SquareSegment.singleton).count z
              rw [List.count_append, count_renderDoubles,
                count_renderSegments, List.count_append]
              simp only [List.count_cons, List.count_nil, Nat.zero_add]
              omega

private theorem count_allSegmentLabels (z : Nat) :
    ∀ segments : List SquareSegment,
      (allSegmentLabels segments).count z =
        (segments.flatMap SquareSegment.doubles).count z +
          (segments.filterMap SquareSegment.singleton).count z
  | [] => by simp [allSegmentLabels]
  | segment :: rest => by
      rw [show allSegmentLabels (segment :: rest) =
        segmentLabels segment ++ allSegmentLabels rest by rfl]
      rw [List.count_append]
      cases segment with
      | mk doubles singleton =>
          cases singleton with
          | none =>
              simp only [segmentLabels, Option.toList_none,
                List.append_nil, List.flatMap_cons,
                List.filterMap_cons_none]
              change
                doubles.count z +
                    (allSegmentLabels rest).count z =
                  (doubles ++
                    rest.flatMap SquareSegment.doubles).count z +
                    (rest.filterMap
                      SquareSegment.singleton).count z
              rw [List.count_append]
              rw [count_allSegmentLabels]
              omega
          | some x =>
              change
                (doubles ++ [x]).count z +
                    (allSegmentLabels rest).count z =
                  (doubles ++
                    rest.flatMap SquareSegment.doubles).count z +
                    (x :: rest.filterMap
                      SquareSegment.singleton).count z
              rw [List.count_append, List.count_append]
              rw [count_allSegmentLabels]
              simp only [List.count_cons, List.count_nil, Nat.zero_add]
              omega

private theorem blockNormal_labels_nodup
    {xs : List Nat} (normal : BlockNormal xs) :
    (blocksOfList xs).map SquareBlock.label |>.Nodup := by
  induction normal with
  | nil => simp [blocksOfList]
  | single x xs normal xNotMem ih =>
      cases xs with
      | nil => simp [blocksOfList]
      | cons y ys =>
          have hxy : x ≠ y := by
            intro h
            subst y
            exact xNotMem (List.Mem.head ys)
          simp only [blocksOfList, hxy, ↓reduceIte, List.map_cons]
          apply List.nodup_cons.mpr
          constructor
          · intro labelMem
            have renderedMem :
                x ∈ renderBlocks (blocksOfList (y :: ys)) := by
              rcases List.mem_map.mp labelMem with
                ⟨block, blockMem, labelEq⟩
              have blockRenderMem :
                  block.label ∈ block.render := by
                cases block <;> simp [SquareBlock.label,
                  SquareBlock.render]
              rw [labelEq] at blockRenderMem
              exact List.mem_flatMap.mpr
                ⟨block, blockMem, blockRenderMem⟩
            rw [render_blocksOfList_of_normal normal] at renderedMem
            exact xNotMem renderedMem
          · exact ih
  | double x xs normal xNotMem ih =>
      simp only [blocksOfList, ↓reduceIte, List.map_cons]
      apply List.nodup_cons.mpr
      constructor
      · intro labelMem
        have renderedMem :
            x ∈ renderBlocks (blocksOfList xs) := by
          rcases List.mem_map.mp labelMem with
            ⟨block, blockMem, labelEq⟩
          have blockRenderMem :
              block.label ∈ block.render := by
            cases block <;> simp [SquareBlock.label,
              SquareBlock.render]
          rw [labelEq] at blockRenderMem
          exact List.mem_flatMap.mpr
            ⟨block, blockMem, blockRenderMem⟩
        rw [render_blocksOfList_of_normal normal] at renderedMem
        exact xNotMem renderedMem
      · exact ih

private theorem labels_segments_roundtrip (blocks : List SquareBlock) :
    allSegmentLabels (blocksToSegments blocks) =
      blocks.map SquareBlock.label := by
  induction blocks with
  | nil => rfl
  | cons block blocks ih =>
      cases block with
      | single x =>
          simp only [blocksToSegments, allSegmentLabels,
            List.flatMap_cons, segmentLabels, List.nil_append,
            Option.toList_some, List.singleton_append,
            List.map_cons, SquareBlock.label]
          simpa using congrArg (List.cons x) ih
      | double x =>
          cases h : blocksToSegments blocks with
          | nil =>
              have blocksEmpty : blocks = [] := by
                have roundtrip := segments_blocks_roundtrip blocks
                rw [h] at roundtrip
                simpa [segmentsToBlocks] using roundtrip.symm
              subst blocks
              rfl
          | cons segment rest =>
              have ih' := ih
              rw [h] at ih'
              simp [blocksToSegments, h, allSegmentLabels,
                segmentLabels, SquareBlock.label] at ih' ⊢
              exact ih'

private theorem sorted_segment_labels_perm (segment : SquareSegment) :
    (segmentLabels (sortSegment segment)).Perm
      (segmentLabels segment) := by
  apply List.Perm.append
  · exact List.mergeSort_perm _ _
  · exact List.Perm.refl _

private theorem sorted_all_labels_perm :
    ∀ segments : List SquareSegment,
      (allSegmentLabels (segments.map sortSegment)).Perm
        (allSegmentLabels segments)
  | [] => List.Perm.nil
  | segment :: rest => by
      simp only [List.map_cons, allSegmentLabels, List.flatMap_cons]
      exact List.Perm.append
        (sorted_segment_labels_perm segment)
        (sorted_all_labels_perm rest)

private theorem blocksToSegments_first_none_tail :
    ∀ (blocks : List SquareBlock) (segment : SquareSegment)
      (rest : List SquareSegment),
      blocksToSegments blocks = segment :: rest →
      segment.singleton = none →
      rest = []
  | [], _, _, h, _ => by simp [blocksToSegments] at h
  | .single x :: blocks, segment, rest, h, hnone => by
      simp only [blocksToSegments] at h
      injection h with headEq
      subst segment
      simp at hnone
  | .double x :: blocks, segment, rest, h, hnone => by
      cases ht : blocksToSegments blocks with
      | nil =>
          simp [blocksToSegments, ht] at h
          exact h.2
      | cons next more =>
          simp only [blocksToSegments, ht] at h
          injection h with headEq tailEq
          subst segment rest
          exact blocksToSegments_first_none_tail
            blocks next more ht hnone

private theorem blocksToSegments_none_terminal :
    ∀ (blocks : List SquareBlock) (before : List SquareSegment)
      (segment : SquareSegment) (rest : List SquareSegment),
      blocksToSegments blocks = before ++ segment :: rest →
      segment.singleton = none →
      rest = []
  | [], _, _, _, h, _ => by simp [blocksToSegments] at h
  | .single x :: blocks, before, segment, rest, h, hnone => by
      cases before with
      | nil =>
          simp only [blocksToSegments, List.nil_append] at h
          injection h with headEq
          subst segment
          simp at hnone
      | cons first more =>
          simp only [blocksToSegments, List.cons_append] at h
          injection h with _ tailEq
          exact blocksToSegments_none_terminal
            blocks more segment rest tailEq hnone
  | .double x :: blocks, before, segment, rest, h, hnone => by
      cases ht : blocksToSegments blocks with
      | nil =>
          have blocksEmpty : blocks = [] := by
            have roundtrip := segments_blocks_roundtrip blocks
            rw [ht] at roundtrip
            simpa [segmentsToBlocks] using roundtrip.symm
          subst blocks
          simp only [blocksToSegments] at h
          cases before with
          | nil =>
              simpa using congrArg List.tail h
          | cons first more => simp at h
      | cons next more =>
          cases before with
          | nil =>
              simp only [blocksToSegments, ht, List.nil_append] at h
              injection h with headEq tailEq
              subst segment rest
              exact blocksToSegments_first_none_tail
                blocks next more ht hnone
          | cons first beforeTail =>
              simp only [blocksToSegments, ht, List.cons_append] at h
              injection h with _ tailEq
              exact blocksToSegments_none_terminal
                blocks (next :: beforeTail) segment rest
                  (by simpa [ht] using congrArg (List.cons next) tailEq)
                  hnone

private theorem blocksToSegments_empty_run_some :
    ∀ (blocks : List SquareBlock) (segment : SquareSegment),
      segment ∈ blocksToSegments blocks →
      segment.doubles = [] →
      segment.singleton.isSome
  | [], _, h, _ => by simp [blocksToSegments] at h
  | .single x :: blocks, segment, h, hempty => by
      simp only [blocksToSegments, List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · exact blocksToSegments_empty_run_some blocks segment h hempty
  | .double x :: blocks, segment, h, hempty => by
      cases ht : blocksToSegments blocks with
      | nil =>
          simp [blocksToSegments, ht] at h
          subst segment
          contradiction
      | cons next more =>
          simp only [blocksToSegments, ht, List.mem_cons] at h
          rcases h with rfl | h
          · contradiction
          · exact blocksToSegments_empty_run_some
              blocks segment (by
                rw [ht]
                exact List.Mem.tail next h) hempty

private theorem canonical_segments_properties
    {xs : List Nat} (normal : BlockNormal xs) :
    SegmentsCanonical
      ((blocksToSegments (blocksOfList xs)).map sortSegment) := by
  let blocks := blocksOfList xs
  let segments := blocksToSegments blocks
  have labelsNodup : (blocks.map SquareBlock.label).Nodup :=
    blockNormal_labels_nodup normal
  have segmentLabelsNodup :
      (allSegmentLabels segments).Nodup := by
    rw [labels_segments_roundtrip]
    exact labelsNodup
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (sorted_all_labels_perm segments).symm.nodup
      segmentLabelsNodup
  · intro segment hsegment
    rcases List.mem_map.mp hsegment with ⟨source, _, rfl⟩
    have transitive :
        ∀ a b c : Nat,
          decide (a ≤ b) = true →
          decide (b ≤ c) = true →
          decide (a ≤ c) = true := by
      intro a b c hab hbc
      have hab' : a ≤ b := of_decide_eq_true hab
      have hbc' : b ≤ c := of_decide_eq_true hbc
      exact decide_eq_true (Nat.le_trans hab' hbc')
    have total :
        ∀ a b : Nat,
          (decide (a ≤ b) || decide (b ≤ a)) = true := by
      intro a b
      by_cases hab : a ≤ b
      · simp [hab]
      · have hba : b ≤ a := by omega
        simp [hab, hba]
    exact (List.pairwise_mergeSort transitive total source.doubles).imp
      (fun h => of_decide_eq_true h)
  · intro before segment rest heq hnone
    change segments.map sortSegment =
      before ++ segment :: rest at heq
    have beforeSources :
        ∃ sourceBefore source sourceRest,
          before = sourceBefore.map sortSegment ∧
          segment = sortSegment source ∧
          rest = sourceRest.map sortSegment ∧
          segments = sourceBefore ++ source :: sourceRest := by
      have split := List.map_eq_append_iff.mp heq
      rcases split with ⟨sourceBefore, sourceTail,
        sourceBeforeEq, sourceTailEq⟩
      rcases sourceTailEq with ⟨beforeEq, tailMapEq⟩
      cases sourceTail with
      | nil => simp at tailMapEq
      | cons source sourceRest =>
          simp only [List.map_cons] at tailMapEq
          injection tailMapEq with segmentEq restEq
          exact ⟨sourceBefore, source, sourceRest,
            beforeEq.symm, segmentEq.symm, restEq.symm,
            by simpa using sourceBeforeEq⟩
    rcases beforeSources with
      ⟨sourceBefore, source, sourceRest, rfl, rfl, rfl, sourceSplit⟩
    have sourceNone : source.singleton = none := by
      simpa [sortSegment] using hnone
    have sourceRestEmpty :=
      blocksToSegments_none_terminal
        blocks sourceBefore source sourceRest sourceSplit sourceNone
    subst sourceRest
    rfl
  · intro segment hsegment hdoubles
    rcases List.mem_map.mp hsegment with ⟨source, _, rfl⟩
    have sourceDoublesEmpty : source.doubles = [] := by
      have perm := List.mergeSort_perm source.doubles
        (fun x y => x ≤ y)
      have : source.doubles.mergeSort
          (fun x y : Nat => decide (x ≤ y)) = [] :=
        hdoubles
      rw [this] at perm
      exact perm.nil_eq.symm
    simpa [sortSegment] using
      blocksToSegments_empty_run_some blocks source
        (by assumption) sourceDoublesEmpty

private theorem renderSegments_count_le_two
    {segments : List SquareSegment}
    (canonical : SegmentsCanonical segments) (z : Nat) :
    (renderSegments segments).count z ≤ 2 := by
  let doubleLabels := segments.flatMap SquareSegment.doubles
  let singletonLabels :=
    segments.filterMap SquareSegment.singleton
  have renderCount :
      (renderSegments segments).count z =
        2 * doubleLabels.count z + singletonLabels.count z := by
    simpa [doubleLabels, singletonLabels] using
      count_renderSegments z segments
  have labelCount :
      (allSegmentLabels segments).count z =
        doubleLabels.count z + singletonLabels.count z := by
    simpa [doubleLabels, singletonLabels] using
      count_allSegmentLabels z segments
  have atMostOne :
      (allSegmentLabels segments).count z ≤ 1 := by
    rw [canonical.1.count]
    split <;> omega
  rw [labelCount] at atMostOne
  rw [renderCount]
  omega

private theorem renderSegments_count_classification
    {segments : List SquareSegment}
    (canonical : SegmentsCanonical segments) (z : Nat) :
    let doubleLabels := segments.flatMap SquareSegment.doubles
    let singletonLabels :=
      segments.filterMap SquareSegment.singleton
    (renderSegments segments).count z =
      if z ∈ doubleLabels then 2
      else if z ∈ singletonLabels then 1
      else 0 := by
  dsimp
  let doubleLabels := segments.flatMap SquareSegment.doubles
  let singletonLabels :=
    segments.filterMap SquareSegment.singleton
  have renderCount :
      (renderSegments segments).count z =
        2 * doubleLabels.count z + singletonLabels.count z := by
    simpa [doubleLabels, singletonLabels] using
      count_renderSegments z segments
  have labelCount :
      (allSegmentLabels segments).count z =
        doubleLabels.count z + singletonLabels.count z := by
    simpa [doubleLabels, singletonLabels] using
      count_allSegmentLabels z segments
  have atMostOne :
      doubleLabels.count z + singletonLabels.count z ≤ 1 := by
    rw [← labelCount, canonical.1.count]
    split <;> omega
  by_cases hd : z ∈ doubleLabels
  · have hdpos : 0 < doubleLabels.count z :=
      List.count_pos_iff.mpr hd
    have hs0 : singletonLabels.count z = 0 := by omega
    have hd1 : doubleLabels.count z = 1 := by omega
    change (renderSegments segments).count z =
      if z ∈ doubleLabels then 2
      else if z ∈ singletonLabels then 1 else 0
    rw [renderCount]
    simp [hd, hd1, hs0]
  · have hd0 : doubleLabels.count z = 0 :=
      List.count_eq_zero.mpr hd
    by_cases hs : z ∈ singletonLabels
    · have hspos : 0 < singletonLabels.count z :=
        List.count_pos_iff.mpr hs
      have hs1 : singletonLabels.count z = 1 := by omega
      change (renderSegments segments).count z =
        if z ∈ doubleLabels then 2
        else if z ∈ singletonLabels then 1 else 0
      rw [renderCount]
      simp [hd, hs, hd0, hs1]
    · have hs0 : singletonLabels.count z = 0 :=
        List.count_eq_zero.mpr hs
      change (renderSegments segments).count z =
        if z ∈ doubleLabels then 2
        else if z ∈ singletonLabels then 1 else 0
      rw [renderCount]
      simp [hd, hs, hd0, hs0]

private theorem mem_doubleLabels_iff_count_two
    {segments : List SquareSegment}
    (canonical : SegmentsCanonical segments) (z : Nat) :
    z ∈ segments.flatMap SquareSegment.doubles ↔
      (renderSegments segments).count z = 2 := by
  rw [renderSegments_count_classification canonical z]
  by_cases hd : z ∈ segments.flatMap SquareSegment.doubles
  · simp [hd]
  · by_cases hs :
        z ∈ segments.filterMap SquareSegment.singleton
    · simp [hd, hs]
    · simp [hd, hs]

private theorem mem_singletonLabels_iff_count_one
    {segments : List SquareSegment}
    (canonical : SegmentsCanonical segments) (z : Nat) :
    z ∈ segments.filterMap SquareSegment.singleton ↔
      (renderSegments segments).count z = 1 := by
  rw [renderSegments_count_classification canonical z]
  by_cases hd : z ∈ segments.flatMap SquareSegment.doubles
  · have hsNot :
        z ∉ segments.filterMap SquareSegment.singleton := by
      intro hs
      have hdpos :
          0 < (segments.flatMap SquareSegment.doubles).count z :=
        List.count_pos_iff.mpr hd
      have hspos :
          0 < (segments.filterMap
            SquareSegment.singleton).count z :=
        List.count_pos_iff.mpr hs
      have labelCount :=
        count_allSegmentLabels z segments
      have atMostOne :
          (allSegmentLabels segments).count z ≤ 1 := by
        rw [canonical.1.count]
        split <;> omega
      rw [labelCount] at atMostOne
      omega
    rw [if_pos hd]
    constructor
    · exact fun hs => (hsNot hs).elim
    · omega
  · by_cases hs :
        z ∈ segments.filterMap SquareSegment.singleton
    · simp [hd, hs]
    · simp [hd, hs]

private theorem mem_renderDoubles (z : Nat) :
    ∀ xs : List Nat, z ∈ renderDoubles xs ↔ z ∈ xs
  | [] => by simp [renderDoubles]
  | x :: xs => by
      simp [renderDoubles, mem_renderDoubles z xs]

private theorem renderSegments_append
    (left right : List SquareSegment) :
    renderSegments (left ++ right) =
      renderSegments left ++ renderSegments right := by
  simp [renderSegments, List.flatMap_append]

private theorem singleton_mem_split
    (z : Nat) :
    ∀ {segments : List SquareSegment},
      z ∈ segments.filterMap SquareSegment.singleton →
      ∃ before doubles after,
        segments =
          before ++ ⟨doubles, some z⟩ :: after
  | [], h => by simp at h
  | segment :: rest, h => by
      cases hs : segment.singleton with
      | none =>
          have tailMem :
              z ∈ rest.filterMap SquareSegment.singleton := by
            simpa [hs] using h
          obtain ⟨before, doubles, after, split⟩ :=
            singleton_mem_split z tailMem
          exact ⟨segment :: before, doubles, after, by
            simp [split]⟩
      | some x =>
          have casesMem :
              z = x ∨
                z ∈ rest.filterMap SquareSegment.singleton := by
            simpa [hs] using h
          rcases casesMem with rfl | tailMem
          · exact ⟨[], segment.doubles, rest, by
              cases segment
              simp at hs
              subst hs
              rfl⟩
          · obtain ⟨before, doubles, after, split⟩ :=
              singleton_mem_split z tailMem
            exact ⟨segment :: before, doubles, after, by
              simp [split]⟩

private theorem marker_not_mem_parts_of_count_one
    (marker : Nat) (pre suffix : List Nat)
    (hcount : (pre ++ marker :: suffix).count marker = 1) :
    marker ∉ pre ∧ marker ∉ suffix := by
  rw [List.count_append, List.count_cons_self] at hcount
  constructor
  · intro hmem
    have positive : 0 < pre.count marker :=
      List.count_pos_iff.mpr hmem
    omega
  · intro hmem
    have positive : 0 < suffix.count marker :=
      List.count_pos_iff.mpr hmem
    omega

private theorem marker_eval_first_segment
    (marker selected : Nat) (doubles : List Nat)
    (rest : List SquareSegment)
    (markerCount :
      (renderSegments
        (⟨doubles, some marker⟩ :: rest)).count marker = 1) :
    listEval (markerValuation marker selected)
        (renderSegments (⟨doubles, some marker⟩ :: rest)) =
      if selected ∈ doubles then 0 else 1 := by
  have rendered :
      renderSegments (⟨doubles, some marker⟩ :: rest) =
        renderDoubles doubles ++ marker :: renderSegments rest := by
    simp [renderSegments, renderSegment]
  have countSplit :
      (renderDoubles doubles ++ marker ::
        renderSegments rest).count marker = 1 := by
    rw [← rendered]
    exact markerCount
  have notMem :=
    marker_not_mem_parts_of_count_one marker
      (renderDoubles doubles) (renderSegments rest) countSplit
  rw [rendered]
  rw [listEval_marker_split marker selected
    (renderDoubles doubles) (renderSegments rest)
    notMem.1 notMem.2]
  simp [mem_renderDoubles]

private theorem marker_eval_after_first_singleton
    (marker selected : Nat) (firstDoubles : List Nat)
    (rest : List SquareSegment)
    (hne : marker ≠ selected)
    (markerInRest :
      marker ∈ rest.filterMap SquareSegment.singleton)
    (markerCount :
      (renderSegments
        (⟨firstDoubles, some selected⟩ :: rest)).count marker = 1) :
    listEval (markerValuation marker selected)
        (renderSegments
          (⟨firstDoubles, some selected⟩ :: rest)) = 0 := by
  obtain ⟨before, markerDoubles, after, split⟩ :=
    singleton_mem_split marker markerInRest
  let pre :=
    renderSegment ⟨firstDoubles, some selected⟩ ++
      renderSegments before ++ renderDoubles markerDoubles
  let suffix := renderSegments after
  have rendered :
      renderSegments
          (⟨firstDoubles, some selected⟩ :: rest) =
        pre ++ marker :: suffix := by
    rw [split]
    simp [renderSegments, pre, suffix, renderSegment,
      List.flatMap_append, List.append_assoc]
  have countSplit :
      (pre ++ marker :: suffix).count marker = 1 := by
    rw [← rendered]
    exact markerCount
  have notMem :=
    marker_not_mem_parts_of_count_one marker pre suffix countSplit
  have selectedInPre : selected ∈ pre := by
    simp [pre, renderSegment, hne]
  rw [rendered]
  rw [listEval_marker_split marker selected pre suffix
    notMem.1 notMem.2]
  simp [selectedInPre]

private theorem marker_eval_first_segment_of_eq
    (marker selected : Nat) (segment : SquareSegment)
    (rest : List SquareSegment)
    (singletonEq : segment.singleton = some marker)
    (markerCount :
      (renderSegments (segment :: rest)).count marker = 1) :
    listEval (markerValuation marker selected)
        (renderSegments (segment :: rest)) =
      if selected ∈ segment.doubles then 0 else 1 := by
  cases segment with
  | mk doubles singleton =>
      simp only at singletonEq
      subst singleton
      exact marker_eval_first_segment marker selected doubles rest
        markerCount

private theorem marker_eval_after_first_singleton_of_eq
    (marker selected : Nat) (segment : SquareSegment)
    (rest : List SquareSegment)
    (singletonEq : segment.singleton = some selected)
    (hne : marker ≠ selected)
    (markerInRest :
      marker ∈ rest.filterMap SquareSegment.singleton)
    (markerCount :
      (renderSegments (segment :: rest)).count marker = 1) :
    listEval (markerValuation marker selected)
        (renderSegments (segment :: rest)) = 0 := by
  cases segment with
  | mk doubles singleton =>
      simp only at singletonEq
      subst singleton
      exact marker_eval_after_first_singleton
        marker selected doubles rest hne markerInRest markerCount

private theorem tail_canonical
    {segment : SquareSegment} {rest : List SquareSegment}
    (canonical : SegmentsCanonical (segment :: rest)) :
    SegmentsCanonical rest := by
  have nodupAppend :
      (segmentLabels segment ++ allSegmentLabels rest).Nodup := by
    simpa [allSegmentLabels] using canonical.1
  refine ⟨(List.nodup_append.mp nodupAppend).2.1, ?_, ?_, ?_⟩
  · intro candidate hcandidate
    exact canonical.2.1 candidate (List.Mem.tail segment hcandidate)
  · intro before candidate tail heq hnone
    exact canonical.2.2.1 (segment :: before) candidate tail
      (by simpa [heq]) hnone
  · intro candidate hcandidate hempty
    exact canonical.2.2.2 candidate
      (List.Mem.tail segment hcandidate) hempty

private theorem first_segment_disjoint
    {segment : SquareSegment} {rest : List SquareSegment}
    (canonical : SegmentsCanonical (segment :: rest)) :
    ∀ z, z ∈ segmentLabels segment →
      z ∉ allSegmentLabels rest := by
  have nodupAppend :
      (segmentLabels segment ++ allSegmentLabels rest).Nodup := by
    simpa [allSegmentLabels] using canonical.1
  exact fun z hz hrest =>
    (List.nodup_append.mp nodupAppend).2.2 z hz z hrest rfl

private theorem mem_renderSegments_allSegmentLabels
    (z : Nat) :
    ∀ {segments : List SquareSegment},
      z ∈ renderSegments segments →
      z ∈ allSegmentLabels segments
  | [], h => by simp [renderSegments] at h
  | segment :: rest, h => by
      simp only [renderSegments, List.flatMap_cons,
        allSegmentLabels, List.mem_append] at h ⊢
      rcases h with h | h
      · left
        cases segment with
        | mk doubles singleton =>
            cases singleton <;>
              simpa [renderSegment, segmentLabels,
                mem_renderDoubles] using h
      · exact Or.inr (mem_renderSegments_allSegmentLabels z h)

private theorem eval_tail_via_mask
    (segment : SquareSegment) (rest : List SquareSegment)
    (canonical : SegmentsCanonical (segment :: rest))
    (valuation : Nat → Fin 4) :
    let masked : Nat → Fin 4 :=
      fun z => if z ∈ segmentLabels segment then 3 else valuation z
    listEval masked (renderSegments (segment :: rest)) =
      listEval valuation (renderSegments rest) := by
  dsimp
  let masked : Nat → Fin 4 :=
    fun z => if z ∈ segmentLabels segment then 3 else valuation z
  have prefixAllThree :
      ∀ z, z ∈ renderSegment segment → masked z = 3 := by
    intro z hz
    have labelMem : z ∈ segmentLabels segment := by
      cases segment with
      | mk doubles singleton =>
          cases singleton <;>
            simpa [renderSegment, segmentLabels,
              mem_renderDoubles] using hz
    simp [masked, labelMem]
  have prefixFold :
      (renderSegment segment).foldl
          (fun current z =>
            edmundsFourSeventyOneOppositeMul current (masked z)) 3 = 3 := by
    have congruent :=
      fold_congr masked (fun _ => (3 : Fin 4))
        (renderSegment segment) 3
        (fun z hz => prefixAllThree z hz)
    rw [congruent]
    exact fold_all_three (renderSegment segment) 3
  have tailAgree :
      ∀ z, z ∈ renderSegments rest → masked z = valuation z := by
    intro z hz
    have tailLabel : z ∈ allSegmentLabels rest :=
      mem_renderSegments_allSegmentLabels z hz
    have notFirst : z ∉ segmentLabels segment := by
      intro firstLabel
      exact (first_segment_disjoint canonical z firstLabel) tailLabel
    simp [masked, notFirst]
  unfold listEval
  simp only [renderSegments, List.flatMap_cons, List.foldl_append]
  rw [prefixFold]
  exact fold_congr masked valuation
    (renderSegments rest) 3 tailAgree

private theorem canonical_segments_eq_of_eval_eq
    {left right : List SquareSegment}
    (leftCanonical : SegmentsCanonical left)
    (rightCanonical : SegmentsCanonical right)
    (equalEval :
      ∀ valuation : Nat → Fin 4,
        listEval valuation (renderSegments left) =
          listEval valuation (renderSegments right)) :
    left = right := by
  have countEq :
      ∀ z,
        (renderSegments left).count z =
          (renderSegments right).count z := by
    intro z
    apply statusState_injective_below_three
      (renderSegments_count_le_two leftCanonical z)
      (renderSegments_count_le_two rightCanonical z)
    rw [← listEval_status z (renderSegments left),
      ← listEval_status z (renderSegments right)]
    exact equalEval (statusValuation z)
  have doubleMemEq :
      ∀ z,
        z ∈ left.flatMap SquareSegment.doubles ↔
          z ∈ right.flatMap SquareSegment.doubles := by
    intro z
    rw [mem_doubleLabels_iff_count_two leftCanonical z,
      mem_doubleLabels_iff_count_two rightCanonical z,
      countEq z]
  have singletonMemEq :
      ∀ z,
        z ∈ left.filterMap SquareSegment.singleton ↔
          z ∈ right.filterMap SquareSegment.singleton := by
    intro z
    rw [mem_singletonLabels_iff_count_one leftCanonical z,
      mem_singletonLabels_iff_count_one rightCanonical z,
      countEq z]
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons first rest =>
          exfalso
          cases hs : first.singleton with
          | some x =>
              have hx :
                  x ∈ (first :: rest).filterMap
                    SquareSegment.singleton := by
                simp [hs]
              have impossible := (singletonMemEq x).2 hx
              simpa using impossible
          | none =>
              have nonempty : first.doubles ≠ [] := by
                intro hempty
                have some :=
                  rightCanonical.2.2.2 first
                    (List.Mem.head rest) hempty
                simp [hs] at some
              obtain ⟨x, hx⟩ :=
                List.exists_mem_of_ne_nil first.doubles nonempty
              have hx' :
                  x ∈ (first :: rest).flatMap
                    SquareSegment.doubles := by
                simp [hx]
              have impossible := (doubleMemEq x).2 hx'
              simpa using impossible
  | cons first leftRest ih =>
      cases hs : first.singleton with
      | none =>
          have leftRestEmpty : leftRest = [] :=
            leftCanonical.2.2.1 [] first leftRest
              (by rfl) hs
          subst leftRest
          cases right with
          | nil =>
              exfalso
              have nonempty : first.doubles ≠ [] := by
                intro hempty
                have some :=
                  leftCanonical.2.2.2 first
                    (List.Mem.head []) hempty
                simp [hs] at some
              obtain ⟨x, hx⟩ :=
                List.exists_mem_of_ne_nil first.doubles nonempty
              have hx' :
                  x ∈ (first :: []).flatMap
                    SquareSegment.doubles := by
                simp [hx]
              have impossible := (doubleMemEq x).1 hx'
              simpa using impossible
          | cons second rightRest =>
              cases ht : second.singleton with
              | some y =>
                  exfalso
                  have hy :
                      y ∈ (second :: rightRest).filterMap
                        SquareSegment.singleton := by
                    simp [ht]
                  have impossible := (singletonMemEq y).2 hy
                  simpa [hs] using impossible
              | none =>
                  have rightRestEmpty : rightRest = [] :=
                    rightCanonical.2.2.1 [] second rightRest
                      (by rfl) ht
                  subst rightRest
                  have sameMem :
                      ∀ z, z ∈ first.doubles ↔
                        z ∈ second.doubles := by
                    intro z
                    simpa using doubleMemEq z
                  have sortedFirst :
                      first.doubles.Pairwise (· ≤ ·) :=
                    leftCanonical.2.1 first (List.Mem.head [])
                  have sortedSecond :
                      second.doubles.Pairwise (· ≤ ·) :=
                    rightCanonical.2.1 second (List.Mem.head [])
                  have nodupFirst : first.doubles.Nodup := by
                    simpa [allSegmentLabels, segmentLabels, hs] using
                      leftCanonical.1
                  have nodupSecond : second.doubles.Nodup := by
                    simpa [allSegmentLabels, segmentLabels, ht] using
                      rightCanonical.1
                  have doublesEqual :=
                    sorted_eq_of_mem_iff sortedFirst sortedSecond
                      nodupFirst nodupSecond sameMem
                  cases first
                  cases second
                  simp_all
      | some x =>
          cases right with
          | nil =>
              exfalso
              have hx :
                  x ∈ (first :: leftRest).filterMap
                    SquareSegment.singleton := by
                simp [hs]
              have impossible := (singletonMemEq x).1 hx
              simpa using impossible
          | cons second rightRest =>
              cases ht : second.singleton with
              | none =>
                  exfalso
                  have rightRestEmpty : rightRest = [] :=
                    rightCanonical.2.2.1 [] second rightRest
                      (by rfl) ht
                  subst rightRest
                  have hx :
                      x ∈ (first :: leftRest).filterMap
                        SquareSegment.singleton := by
                    simp [hs]
                  have impossible := (singletonMemEq x).1 hx
                  simpa [ht] using impossible
              | some y =>
                  have singletonXLeft :
                      x ∈ (first :: leftRest).filterMap
                        SquareSegment.singleton := by
                    simp [hs]
                  have singletonYRight :
                      y ∈ (second :: rightRest).filterMap
                        SquareSegment.singleton := by
                    simp [ht]
                  have countXLeft :
                      (renderSegments
                        (first :: leftRest)).count x = 1 :=
                    (mem_singletonLabels_iff_count_one
                      leftCanonical x).mp singletonXLeft
                  have countXRight :
                      (renderSegments
                        (second :: rightRest)).count x = 1 := by
                    rw [← countEq x]
                    exact countXLeft
                  have countYRight :
                      (renderSegments
                        (second :: rightRest)).count y = 1 :=
                    (mem_singletonLabels_iff_count_one
                      rightCanonical y).mp singletonYRight
                  have countYLeft :
                      (renderSegments
                        (first :: leftRest)).count y = 1 := by
                    rw [countEq y]
                    exact countYRight
                  have hxy : x = y := by
                    apply Classical.byContradiction
                    intro hne
                    have xInRightTail :
                        x ∈ rightRest.filterMap
                          SquareSegment.singleton := by
                      have xInRight :=
                        (singletonMemEq x).1 singletonXLeft
                      simpa [ht, hne] using xInRight
                    have yNotFirstDoubles :
                        y ∉ first.doubles := by
                      intro hy
                      have doubleY :
                          y ∈ (first :: leftRest).flatMap
                            SquareSegment.doubles := by
                        simp [hy]
                      have countTwo :=
                        (mem_doubleLabels_iff_count_two
                          leftCanonical y).mp doubleY
                      omega
                    have leftMarker :=
                      marker_eval_first_segment_of_eq
                        x y first leftRest hs countXLeft
                    have rightMarker :=
                      marker_eval_after_first_singleton_of_eq
                        x y second rightRest ht hne
                        xInRightTail countXRight
                    have sameMarker :=
                      equalEval (markerValuation x y)
                    rw [leftMarker, rightMarker] at sameMarker
                    simp [yNotFirstDoubles] at sameMarker
                  subst y
                  have firstCount :
                      (renderSegments
                        (first :: leftRest)).count x = 1 :=
                    countXLeft
                  have secondCount :
                      (renderSegments
                        (second :: rightRest)).count x = 1 :=
                    countXRight
                  have sameFirstDoubles :
                      ∀ z, z ∈ first.doubles ↔
                        z ∈ second.doubles := by
                    intro z
                    have leftMarker :=
                      marker_eval_first_segment_of_eq
                        x z first leftRest hs firstCount
                    have rightMarker :=
                      marker_eval_first_segment_of_eq
                        x z second rightRest ht secondCount
                    have sameMarker :=
                      equalEval (markerValuation x z)
                    rw [leftMarker, rightMarker] at sameMarker
                    by_cases hl : z ∈ first.doubles <;>
                      by_cases hr : z ∈ second.doubles <;>
                        simp_all
                  have sortedFirst :
                      first.doubles.Pairwise (· ≤ ·) :=
                    leftCanonical.2.1 first
                      (List.Mem.head leftRest)
                  have sortedSecond :
                      second.doubles.Pairwise (· ≤ ·) :=
                    rightCanonical.2.1 second
                      (List.Mem.head rightRest)
                  have nodupFirst : first.doubles.Nodup := by
                    have labels :
                        (segmentLabels first ++
                          allSegmentLabels leftRest).Nodup := by
                      simpa [allSegmentLabels] using leftCanonical.1
                    have firstLabels :=
                      (List.nodup_append.mp labels).1
                    cases first
                    simpa [segmentLabels] using
                      (List.nodup_append.mp firstLabels).1
                  have nodupSecond : second.doubles.Nodup := by
                    have labels :
                        (segmentLabels second ++
                          allSegmentLabels rightRest).Nodup := by
                      simpa [allSegmentLabels] using rightCanonical.1
                    have firstLabels :=
                      (List.nodup_append.mp labels).1
                    cases second
                    simpa [segmentLabels] using
                      (List.nodup_append.mp firstLabels).1
                  have doublesEqual :
                      first.doubles = second.doubles :=
                    sorted_eq_of_mem_iff sortedFirst sortedSecond
                      nodupFirst nodupSecond sameFirstDoubles
                  have firstEqual : first = second := by
                    cases first
                    cases second
                    simp_all
                  subst second
                  have tailEvalEqual :
                      ∀ valuation : Nat → Fin 4,
                        listEval valuation
                            (renderSegments leftRest) =
                          listEval valuation
                            (renderSegments rightRest) := by
                    intro valuation
                    let masked : Nat → Fin 4 :=
                      fun z =>
                        if z ∈ segmentLabels first
                        then 3 else valuation z
                    exact
                      (eval_tail_via_mask first leftRest
                        leftCanonical valuation).symm.trans <|
                        (equalEval masked).trans <|
                          eval_tail_via_mask first rightRest
                            rightCanonical valuation
                  have tailCountEq :
                      ∀ z,
                        (renderSegments leftRest).count z =
                          (renderSegments rightRest).count z := by
                    intro z
                    apply statusState_injective_below_three
                      (renderSegments_count_le_two
                        (tail_canonical leftCanonical) z)
                      (renderSegments_count_le_two
                        (tail_canonical rightCanonical) z)
                    rw [← listEval_status z
                          (renderSegments leftRest),
                      ← listEval_status z
                          (renderSegments rightRest)]
                    exact tailEvalEqual (statusValuation z)
                  have tailsEqual :=
                    ih (tail_canonical leftCanonical)
                      (tail_canonical rightCanonical)
                      tailEvalEqual
                      tailCountEq
                      (by
                        intro z
                        rw [mem_doubleLabels_iff_count_two
                              (tail_canonical leftCanonical) z,
                          mem_doubleLabels_iff_count_two
                              (tail_canonical rightCanonical) z,
                          tailCountEq z])
                      (by
                        intro z
                        rw [mem_singletonLabels_iff_count_one
                              (tail_canonical leftCanonical) z,
                          mem_singletonLabels_iff_count_one
                              (tail_canonical rightCanonical) z,
                          tailCountEq z])
                  rw [tailsEqual]

private theorem oppositeMul_power (a : Fin 4) :
    edmundsFourSeventyOneOppositeMul a a =
      edmundsFourSeventyOneOppositeMul
        (edmundsFourSeventyOneOppositeMul a a) a := by
  decide +revert

private theorem oppositeMul_gather (a b : Fin 4) :
    edmundsFourSeventyOneOppositeMul
        (edmundsFourSeventyOneOppositeMul a b) a =
      edmundsFourSeventyOneOppositeMul
        (edmundsFourSeventyOneOppositeMul a a) b := by
  decide +revert

private theorem oppositeMul_squares_commute (a b : Fin 4) :
    edmundsFourSeventyOneOppositeMul
        (edmundsFourSeventyOneOppositeMul
          (edmundsFourSeventyOneOppositeMul b b) a) a =
      edmundsFourSeventyOneOppositeMul
        (edmundsFourSeventyOneOppositeMul
          (edmundsFourSeventyOneOppositeMul a a) b) b := by
  decide +revert

private theorem squareBlockBasis_models :
    Models edmundsFourSeventyOneOpposite.semigroup squareBlockBasis := by
  intro e he
  simp only [squareBlockBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · intro valuation
    change
      edmundsFourSeventyOneOppositeMul
          (valuation 0) (valuation 0) =
        edmundsFourSeventyOneOppositeMul
          (edmundsFourSeventyOneOppositeMul
            (valuation 0) (valuation 0))
          (valuation 0)
    exact oppositeMul_power (valuation 0)
  · intro valuation
    change
      edmundsFourSeventyOneOppositeMul
          (edmundsFourSeventyOneOppositeMul
            (valuation 0) (valuation 1))
          (valuation 0) =
        edmundsFourSeventyOneOppositeMul
          (edmundsFourSeventyOneOppositeMul
            (valuation 0) (valuation 0))
          (valuation 1)
    exact oppositeMul_gather (valuation 0) (valuation 1)
  · intro valuation
    change
      edmundsFourSeventyOneOppositeMul
          (edmundsFourSeventyOneOppositeMul
            (edmundsFourSeventyOneOppositeMul
              (valuation 1) (valuation 1))
            (valuation 0))
          (valuation 0) =
        edmundsFourSeventyOneOppositeMul
          (edmundsFourSeventyOneOppositeMul
            (edmundsFourSeventyOneOppositeMul
              (valuation 0) (valuation 0))
            (valuation 1))
          (valuation 1)
    exact oppositeMul_squares_commute
      (valuation 0) (valuation 1)

/-- Completeness for the reversed basis. First-occurrence normalization
gathers each variable into one block, and square commutation sorts every
maximal run of doubled blocks. The exact table separates the resulting
canonical segmented forms. -/
theorem squareBlockBasis_complete :
    BasisFor edmundsFourSeventyOneOpposite.semigroup
      squareBlockBasis := by
  refine ⟨squareBlockBasis_models, ?_⟩
  intro e valid
  have lhsEdmunds := squareBlockDerivesEdmundsNormal e.lhs
  have rhsEdmunds := squareBlockDerivesEdmundsNormal e.rhs
  cases hl : edmundsNormalList e.lhs.toList with
  | nil =>
      have headMem : e.lhs.head ∈ edmundsNormalList e.lhs.toList :=
        (edmundsNormalList_mem e.lhs.head e.lhs.toList).2 <| by
          simp [Word.toList]
      rw [hl] at headMem
      contradiction
  | cons lx ltail =>
      cases hr : edmundsNormalList e.rhs.toList with
      | nil =>
          have headMem : e.rhs.head ∈ edmundsNormalList e.rhs.toList :=
            (edmundsNormalList_mem e.rhs.head e.rhs.toList).2 <| by
              simp [Word.toList]
          rw [hr] at headMem
          contradiction
      | cons rx rtail =>
          rw [hl] at lhsEdmunds
          rw [hr] at rhsEdmunds
          let lhsList := lx :: ltail
          let rhsList := rx :: rtail
          let lhsBlocks := blocksOfList lhsList
          let rhsBlocks := blocksOfList rhsList
          let lhsSegments :=
            (blocksToSegments lhsBlocks).map sortSegment
          let rhsSegments :=
            (blocksToSegments rhsBlocks).map sortSegment
          have lhsNormal : BlockNormal lhsList := by
            simpa [lhsList, hl] using
              edmundsNormalList_blockNormal e.lhs.toList
          have rhsNormal : BlockNormal rhsList := by
            simpa [rhsList, hr] using
              edmundsNormalList_blockNormal e.rhs.toList
          have lhsCanonical : SegmentsCanonical lhsSegments := by
            simpa [lhsSegments, lhsBlocks, lhsList] using
              canonical_segments_properties lhsNormal
          have rhsCanonical : SegmentsCanonical rhsSegments := by
            simpa [rhsSegments, rhsBlocks, rhsList] using
              canonical_segments_properties rhsNormal
          have lhsCanonDerives :=
            canonicalBlocksDerive lhsBlocks
          have rhsCanonDerives :=
            canonicalBlocksDerive rhsBlocks
          have lhsRendered :
              renderBlocks lhsBlocks = lhsList := by
            exact render_blocksOfList_of_normal lhsNormal
          have rhsRendered :
              renderBlocks rhsBlocks = rhsList := by
            exact render_blocksOfList_of_normal rhsNormal
          have lhsCanonRendered :
              renderBlocks (canonicalBlocks lhsBlocks) =
                renderSegments lhsSegments := by
            simp [canonicalBlocks, lhsSegments, lhsBlocks,
              render_segments_eq_render_blocks]
          have rhsCanonRendered :
              renderBlocks (canonicalBlocks rhsBlocks) =
                renderSegments rhsSegments := by
            simp [canonicalBlocks, rhsSegments, rhsBlocks,
              render_segments_eq_render_blocks]
          rw [lhsRendered, lhsCanonRendered] at lhsCanonDerives
          rw [rhsRendered, rhsCanonRendered] at rhsCanonDerives
          have lhsNonempty :
              ListDerives (lx :: ltail)
                (renderSegments lhsSegments) := by
            simpa [lhsList] using lhsCanonDerives
          have rhsNonempty :
              ListDerives (rx :: rtail)
                (renderSegments rhsSegments) := by
            simpa [rhsList] using rhsCanonDerives
          obtain ⟨lch, lct, lhsCanonicalList,
            lhsCanonicalDerivation⟩ :=
            ListDerives.from_cons lhsNonempty
          obtain ⟨rch, rct, rhsCanonicalList,
            rhsCanonicalDerivation⟩ :=
            ListDerives.from_cons rhsNonempty
          have canonicalEvalEqual :
              ∀ valuation : Nat → Fin 4,
                listEval valuation (renderSegments lhsSegments) =
                  listEval valuation
                    (renderSegments rhsSegments) := by
            intro valuation
            have lhsSound :=
              lhsEdmunds.sound squareBlockBasis_models valuation
            have rhsSound :=
              rhsEdmunds.sound squareBlockBasis_models valuation
            have lhsCanonSound :=
              lhsCanonicalDerivation.sound
                squareBlockBasis_models valuation
            have rhsCanonSound :=
              rhsCanonicalDerivation.sound
                squareBlockBasis_models valuation
            rw [eval_eq_listEval] at lhsSound rhsSound
            rw [eval_eq_listEval valuation (wordOfCons lx ltail),
              eval_eq_listEval valuation (wordOfCons lch lct)] at lhsCanonSound
            rw [eval_eq_listEval valuation (wordOfCons rx rtail),
              eval_eq_listEval valuation (wordOfCons rch rct)] at rhsCanonSound
            simp only [wordOfCons, Word.toList] at lhsCanonSound rhsCanonSound
            rw [← lhsCanonicalList] at lhsCanonSound
            rw [← rhsCanonicalList] at rhsCanonSound
            exact lhsCanonSound.symm.trans <|
              lhsSound.symm.trans <|
                (valid valuation).trans <|
                  rhsSound.trans rhsCanonSound
          have segmentsEqual :
              lhsSegments = rhsSegments :=
            canonical_segments_eq_of_eval_eq
              lhsCanonical rhsCanonical canonicalEvalEqual
          have renderedEqual :
              renderSegments lhsSegments =
                renderSegments rhsSegments := by
            rw [segmentsEqual]
          have canonicalWordsEqual :
              wordOfCons lch lct = wordOfCons rch rct := by
            apply Word.toList_injective
            change lch :: lct = rch :: rct
            rw [← lhsCanonicalList, ← rhsCanonicalList,
              renderedEqual]
          exact Derives.trans lhsEdmunds <|
            Derives.trans lhsCanonicalDerivation <|
              Derives.trans
                (canonicalWordsEqual ▸ Derives.refl _)
                (Derives.trans
                  (Derives.symm rhsCanonicalDerivation)
                  (Derives.symm rhsEdmunds))

def edmundsFourSeventyOneXX : Word Nat := ⟨0, [0]⟩
def edmundsFourSeventyOneXXX : Word Nat := ⟨0, [0, 0]⟩
def edmundsFourSeventyOneXYX : Word Nat := ⟨0, [1, 0]⟩
def edmundsFourSeventyOneYXX : Word Nat := ⟨1, [0, 0]⟩
def edmundsFourSeventyOneXXYY : Word Nat := ⟨0, [0, 1, 1]⟩
def edmundsFourSeventyOneYYXX : Word Nat := ⟨1, [1, 0, 0]⟩

def edmundsFourSeventyOnePowerLaw : Identity Nat :=
  ⟨edmundsFourSeventyOneXX, edmundsFourSeventyOneXXX⟩

def edmundsFourSeventyOneGatherLaw : Identity Nat :=
  ⟨edmundsFourSeventyOneXYX, edmundsFourSeventyOneYXX⟩

def edmundsFourSeventyOneSquareCommutationLaw : Identity Nat :=
  ⟨edmundsFourSeventyOneXXYY, edmundsFourSeventyOneYYXX⟩

/-- Edmunds' basis for `S(4,23)`:
`xx = xxx`, `xyx = yxx`, `xxyy = yyxx`. -/
def edmundsFourSeventyOneBasis : List (Identity Nat) :=
  [edmundsFourSeventyOnePowerLaw,
    edmundsFourSeventyOneGatherLaw,
    edmundsFourSeventyOneSquareCommutationLaw]

private theorem reversed_squareBlockBasis :
    reversedBasis squareBlockBasis =
      edmundsFourSeventyOneBasis := by
  decide

/-- Completeness of Edmunds' basis for the stored `S4_71` orientation. -/
theorem edmundsFourSeventyOneBasis_complete :
    BasisFor edmundsFourSeventyOne.semigroup
      edmundsFourSeventyOneBasis := by
  have reversed := squareBlockBasis_complete.oppositeReversed
  rw [reversed_squareBlockBasis] at reversed
  simpa [edmundsFourSeventyOne, edmundsFourSeventyOneMul,
    edmundsFourSeventyOneOpposite, FiniteTable.semigroup,
    Semigroup.opposite] using reversed

end SemigroupBasis.Examples
