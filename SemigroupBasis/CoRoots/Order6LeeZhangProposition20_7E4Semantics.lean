import SemigroupBasis.CoRoots.Order6LeeZhangProposition20_7E4Canonical
import SemigroupBasis.CoRoots.Order6LeeZhangProposition20_7E4Targets
import SemigroupBasis.Examples.CommutativeExponentFour
import SemigroupBasis.Examples.LeftZeroTwo
import SemigroupBasis.Generated.S4_40

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeZhangProposition20_7E4

open SemigroupBasis
open SemigroupBasis.Examples

/-!
# Lee--Zhang Lemma 20.8: unrestricted E4 semantics

This file proves only the four necessary invariants of Lemma 20.8 for an
arbitrary identity valid in the published table `E4`.  The proof uses the
literal capped-multiplicity and left-zero subsemigroups, together with one
direct scanner for both `F_SN` and `F_SS`.  It contains no normalization or
completeness assertion.
-/

/-! ## Capped multiplicity and the first letter -/

/-- The copy of `S4_40` on the zero-based E4 elements `[0,2,3,4]`. -/
def capThreeToPublished (value : Fin 4) : Fin 6 :=
  if value = 0 then 0 else
    if value = 1 then 2 else
      if value = 2 then 3 else 4

def capThreeEmbeddingZeroBased : List Nat :=
  List.ofFn fun value : Fin 4 => (capThreeToPublished value).val

theorem capThreeEmbeddingZeroBased_certificate :
    capThreeEmbeddingZeroBased = [0, 2, 3, 4] := by
  decide

def capThreeEmbedding :
    Embedding Generated.S4_40.table.semigroup publishedTable.semigroup where
  toFun := capThreeToPublished
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

/-- Every E4-valid identity preserves every multiplicity capped at three. -/
theorem publishedValid_cappedCount_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedTable.semigroup) :
    ∀ letter,
      min (identity.lhs.toList.count letter) 3 =
        min (identity.rhs.toList.count letter) 3 :=
  exponentFourValid_capped_count_eq identity <| by
    simpa [Generated.S4_40.table, commutativeExponentFour] using
      capThreeEmbedding.pullback_identity identity valid

/-- The copy of the two-element left-zero semigroup on zero-based E4
elements `[4,5]`. -/
def leftZeroToPublished (value : Fin 2) : Fin 6 :=
  if value = 0 then 4 else 5

def leftZeroEmbeddingZeroBased : List Nat :=
  List.ofFn fun value : Fin 2 => (leftZeroToPublished value).val

theorem leftZeroEmbeddingZeroBased_certificate :
    leftZeroEmbeddingZeroBased = [4, 5] := by
  decide

def leftZeroEmbedding :
    Embedding leftZeroTwo.semigroup publishedTable.semigroup where
  toFun := leftZeroToPublished
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

theorem publishedValid_head_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedTable.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  have pulled := leftZeroEmbedding.pullback_identity identity valid
  apply Decidable.byContradiction
  intro different
  let valuation : Nat → Fin 2 := fun letter =>
    if letter = identity.lhs.head then 0 else 1
  have evaluated := pulled valuation
  rw [leftZeroTwo_eval, leftZeroTwo_eval] at evaluated
  simp [valuation, Ne.symm different] at evaluated

theorem publishedValid_firstLetter_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedTable.semigroup) :
    identity.lhs.toList.head? = identity.rhs.toList.head? := by
  have heads := publishedValid_head_eq identity valid
  simpa [Word.toList] using
    congrArg (fun letter : Nat => some letter) heads

private theorem sameMultiplicityClass_of_cappedCount_eq
    {left right : List Nat} {letter : Nat}
    (capped :
      min (left.count letter) 3 = min (right.count letter) 3) :
    SameMultiplicityClass left right letter := by
  unfold SameMultiplicityClass
  by_cases leftSmall : left.count letter ≤ 2
  · have rightSmall : right.count letter ≤ 2 := by
      by_cases rightSmall : right.count letter ≤ 2
      · exact rightSmall
      · have rightLarge : 3 ≤ right.count letter := by omega
        rw [Nat.min_eq_left (by omega),
          Nat.min_eq_right rightLarge] at capped
        omega
    apply Or.inl
    constructor
    · rw [Nat.min_eq_left (by omega),
        Nat.min_eq_left (by omega)] at capped
      exact capped
    · exact leftSmall
  · have leftLarge : 3 ≤ left.count letter := by omega
    have rightLarge : 3 ≤ right.count letter := by
      by_cases rightLarge : 3 ≤ right.count letter
      · exact rightLarge
      · have rightSmall : right.count letter ≤ 2 := by omega
        rw [Nat.min_eq_right leftLarge,
          Nat.min_eq_left (by omega)] at capped
        omega
    exact Or.inr ⟨leftLarge, rightLarge⟩

theorem publishedValid_sameMultiplicityClass
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedTable.semigroup)
    (letter : Nat) :
    SameMultiplicityClass identity.lhs.toList identity.rhs.toList letter :=
  sameMultiplicityClass_of_cappedCount_eq
    (publishedValid_cappedCount_eq identity valid letter)

theorem publishedValid_simple_iff
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedTable.semigroup)
    (letter : Nat) :
    Simple identity.lhs.toList letter ↔
      Simple identity.rhs.toList letter := by
  have same := publishedValid_sameMultiplicityClass identity valid letter
  unfold SameMultiplicityClass at same
  unfold Simple
  rcases same with exactCounts | large <;> omega

theorem publishedValid_nonSimple_iff
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedTable.semigroup)
    (letter : Nat) :
    NonSimple identity.lhs.toList letter ↔
      NonSimple identity.rhs.toList letter := by
  have same := publishedValid_sameMultiplicityClass identity valid letter
  unfold SameMultiplicityClass at same
  unfold NonSimple
  rcases same with exactCounts | large <;> omega

theorem publishedValid_mem_iff
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedTable.semigroup)
    (letter : Nat) :
    letter ∈ identity.lhs.toList ↔ letter ∈ identity.rhs.toList := by
  rw [← List.count_pos_iff, ← List.count_pos_iff]
  have same := publishedValid_sameMultiplicityClass identity valid letter
  unfold SameMultiplicityClass at same
  rcases same with exactCounts | large <;> omega

/-! ## The direct E4 adjacency scanner -/

/-- Send the globally simple source to zero-based E4 element `1`, the tested
target to element `4`, and every other variable to element `5`. -/
def proposition20_7AdjacencyValuation
    (source target : Nat) : Nat → Fin 6 :=
  fun letter =>
    if letter = source then 1
    else if letter = target then 4
    else 5

@[simp]
private theorem proposition20_7AdjacencyValuation_source
    (source target : Nat) :
    proposition20_7AdjacencyValuation source target source = 1 := by
  simp [proposition20_7AdjacencyValuation]

private theorem proposition20_7AdjacencyValuation_target
    {source target : Nat} (different : source ≠ target) :
    proposition20_7AdjacencyValuation source target target = 4 := by
  simp [proposition20_7AdjacencyValuation, Ne.symm different]

private def listEvalStep :
    Option (Fin 6) → Fin 6 → Option (Fin 6)
  | none, next => some next
  | some current, next => some (publishedMul current next)

private def listEvalFrom
    (initial : Option (Fin 6)) (valuation : Nat → Fin 6)
    (letters : List Nat) : Option (Fin 6) :=
  letters.foldl
    (fun current letter => listEvalStep current (valuation letter))
    initial

@[simp]
private theorem listEvalFrom_nil
    (initial : Option (Fin 6)) (valuation : Nat → Fin 6) :
    listEvalFrom initial valuation [] = initial :=
  rfl

@[simp]
private theorem listEvalFrom_cons
    (initial : Option (Fin 6)) (valuation : Nat → Fin 6)
    (first : Nat) (rest : List Nat) :
    listEvalFrom initial valuation (first :: rest) =
      listEvalFrom
        (listEvalStep initial (valuation first)) valuation rest :=
  rfl

private theorem listEvalFrom_append
    (initial : Option (Fin 6)) (valuation : Nat → Fin 6)
    (left right : List Nat) :
    listEvalFrom initial valuation (left ++ right) =
      listEvalFrom (listEvalFrom initial valuation left) valuation right := by
  simp [listEvalFrom, List.foldl_append]

private theorem listEvalFrom_some
    (initial : Fin 6) (valuation : Nat → Fin 6)
    (letters : List Nat) :
    listEvalFrom (some initial) valuation letters =
      some
        (letters.foldl
          (fun current letter => publishedMul current (valuation letter))
          initial) := by
  induction letters generalizing initial with
  | nil =>
      rfl
  | cons first rest induction =>
      rw [listEvalFrom_cons]
      simp only [listEvalStep, List.foldl_cons]
      exact induction (publishedMul initial (valuation first))

private theorem listEvalFrom_toList
    (valuation : Nat → Fin 6) (word : Word Nat) :
    listEvalFrom none valuation word.toList =
      some (publishedTable.semigroup.eval valuation word) := by
  cases word with
  | mk head tail =>
      simp only [Word.toList, listEvalFrom_cons, listEvalStep,
        Semigroup.eval]
      exact listEvalFrom_some (valuation head) valuation tail

private theorem listEvalFrom_sourceFree_fixed
    {source target : Nat} (different : source ≠ target)
    (state : Fin 6)
    (stateFour : publishedMul state 4 = state)
    (stateFive : publishedMul state 5 = state)
    {letters : List Nat} (sourceFree : source ∉ letters) :
    listEvalFrom (some state)
        (proposition20_7AdjacencyValuation source target) letters =
      some state := by
  induction letters with
  | nil =>
      rfl
  | cons first rest induction =>
      have firstNe : first ≠ source := by
        intro equal
        apply sourceFree
        simp [equal]
      have restFree : source ∉ rest := by
        intro member
        exact sourceFree (by simp [member])
      rw [listEvalFrom_cons]
      by_cases firstTarget : first = target
      · subst first
        rw [proposition20_7AdjacencyValuation_target different]
        simp only [listEvalStep, stateFour]
        exact induction restFree
      · rw [show proposition20_7AdjacencyValuation source target first = 5 by
          simp [proposition20_7AdjacencyValuation, firstNe, firstTarget]]
        simp only [listEvalStep, stateFive]
        exact induction restFree

private theorem listEvalFrom_none_sourceFree_cons
    {source target first : Nat} (different : source ≠ target)
    {rest : List Nat} (sourceFree : source ∉ first :: rest) :
    listEvalFrom none
        (proposition20_7AdjacencyValuation source target) (first :: rest) =
      some (proposition20_7AdjacencyValuation source target first) := by
  have firstNe : first ≠ source := by
    intro equal
    apply sourceFree
    simp [equal]
  have restFree : source ∉ rest := by
    intro member
    exact sourceFree (by simp [member])
  rw [listEvalFrom_cons]
  simp only [listEvalStep]
  by_cases firstTarget : first = target
  · subst first
    rw [proposition20_7AdjacencyValuation_target different]
    exact listEvalFrom_sourceFree_fixed different 4
      (by decide) (by decide) restFree
  · rw [show proposition20_7AdjacencyValuation source target first = 5 by
      simp [proposition20_7AdjacencyValuation, firstNe, firstTarget]]
    exact listEvalFrom_sourceFree_fixed different 5
      (by decide) (by decide) restFree

private theorem listEval_prefix_source
    {source target : Nat} (different : source ≠ target)
    (before after : List Nat) (beforeFree : source ∉ before) :
    listEvalFrom none
        (proposition20_7AdjacencyValuation source target)
        (before ++ source :: after) =
      listEvalFrom (some 1)
        (proposition20_7AdjacencyValuation source target) after := by
  rw [listEvalFrom_append]
  cases before with
  | nil =>
      simp [listEvalStep]
  | cons first rest =>
      have fullFree : source ∉ first :: rest := beforeFree
      rw [listEvalFrom_none_sourceFree_cons different fullFree]
      rw [listEvalFrom_cons, proposition20_7AdjacencyValuation_source]
      by_cases firstTarget : first = target
      · subst first
        rw [proposition20_7AdjacencyValuation_target different]
        simp only [listEvalStep]
        rw [show publishedMul (4 : Fin 6) (1 : Fin 6) = 1 by decide]
      · have firstNe : first ≠ source := by
          intro equal
          apply fullFree
          simp [equal]
        rw [show proposition20_7AdjacencyValuation source target first = 5 by
          simp [proposition20_7AdjacencyValuation, firstNe, firstTarget]]
        simp only [listEvalStep]
        rw [show publishedMul (5 : Fin 6) (1 : Fin 6) = 1 by decide]

private theorem listEval_adjacent
    {source target : Nat} (different : source ≠ target)
    (before after : List Nat) (beforeFree : source ∉ before)
    (afterFree : source ∉ after) :
    listEvalFrom none
        (proposition20_7AdjacencyValuation source target)
        (before ++ source :: target :: after) = some 0 := by
  rw [listEval_prefix_source different before (target :: after) beforeFree]
  rw [listEvalFrom_cons,
    proposition20_7AdjacencyValuation_target different]
  simp only [listEvalStep]
  rw [show publishedMul (1 : Fin 6) (4 : Fin 6) = 0 by decide]
  exact listEvalFrom_sourceFree_fixed different 0
    (by decide) (by decide) afterFree

private theorem listEval_nonadjacent
    {source target next : Nat} (different : source ≠ target)
    (nextNeSource : next ≠ source) (nextNeTarget : next ≠ target)
    (before rest : List Nat) (beforeFree : source ∉ before)
    (restFree : source ∉ rest) :
    listEvalFrom none
        (proposition20_7AdjacencyValuation source target)
        (before ++ source :: next :: rest) = some 2 := by
  rw [listEval_prefix_source different before (next :: rest) beforeFree]
  rw [listEvalFrom_cons]
  rw [show proposition20_7AdjacencyValuation source target next = 5 by
    simp [proposition20_7AdjacencyValuation,
      nextNeSource, nextNeTarget]]
  simp only [listEvalStep]
  rw [show publishedMul (1 : Fin 6) (5 : Fin 6) = 2 by decide]
  exact listEvalFrom_sourceFree_fixed different 2
    (by decide) (by decide) restFree

private theorem sourceFree_parts_of_count_one
    {letters before after : List Nat} {source : Nat}
    (split : letters = before ++ source :: after)
    (countOne : letters.count source = 1) :
    source ∉ before ∧ source ∉ after := by
  constructor
  · intro member
    have positive : 0 < before.count source :=
      List.count_pos_iff.mpr member
    rw [split, List.count_append, List.count_cons_self] at countOne
    omega
  · intro member
    have positive : 0 < after.count source :=
      List.count_pos_iff.mpr member
    rw [split, List.count_append, List.count_cons_self] at countOne
    omega

/-- The direct E4 scanner used by both `F_SN` and `F_SS`.  With a globally
simple source and a present target, evaluation is zero exactly when the
target immediately follows the source.  Every non-edge evaluates to one or
two. -/
theorem publishedAdjacencyDetector_scan
    (source target : Nat) (word : Word Nat)
    (different : source ≠ target)
    (sourceSimple : Simple word.toList source)
    (_targetPresent : target ∈ word.toList) :
    (publishedTable.semigroup.eval
          (proposition20_7AdjacencyValuation source target) word = (0 : Fin 6) ↔
        (source, target) ∈ word.adjacentPairs) ∧
      ((source, target) ∉ word.adjacentPairs →
        publishedTable.semigroup.eval
              (proposition20_7AdjacencyValuation source target) word = (1 : Fin 6) ∨
          publishedTable.semigroup.eval
              (proposition20_7AdjacencyValuation source target) word = (2 : Fin 6)) := by
  by_cases adjacent : (source, target) ∈ word.adjacentPairs
  · obtain ⟨before, after, split⟩ :=
      (S5_107.mem_adjacentPairs_iff_exists_split
        source target word).mp adjacent
    have countOne :
        (before ++ source :: target :: after).count source = 1 := by
      rw [← split]
      exact sourceSimple
    have free :=
      sourceFree_parts_of_count_one (letters := word.toList)
        split sourceSimple
    have afterFree : source ∉ after := by
      intro member
      exact free.2 (List.mem_cons_of_mem target member)
    have evaluated :
        listEvalFrom none
            (proposition20_7AdjacencyValuation source target)
            word.toList = some 0 := by
      rw [split]
      exact listEval_adjacent different before after free.1 afterFree
    rw [listEvalFrom_toList] at evaluated
    have exactEval :
        publishedTable.semigroup.eval
            (proposition20_7AdjacencyValuation source target) word = (0 : Fin 6) :=
      Option.some.inj evaluated
    constructor
    · constructor
      · intro _
        exact adjacent
      · intro _
        exact exactEval
    · intro absent
      exact False.elim (absent adjacent)
  · have sourceMember : source ∈ word.toList := sourceSimple.mem
    obtain ⟨before, after, split⟩ :=
      List.mem_iff_append.mp sourceMember
    have free :=
      sourceFree_parts_of_count_one split sourceSimple
    cases after with
    | nil =>
        have evaluated :
            listEvalFrom none
                (proposition20_7AdjacencyValuation source target)
                word.toList = some 1 := by
          rw [split]
          exact listEval_prefix_source different before [] free.1
        rw [listEvalFrom_toList] at evaluated
        have exactEval :
            publishedTable.semigroup.eval
                (proposition20_7AdjacencyValuation source target) word = (1 : Fin 6) :=
          Option.some.inj evaluated
        constructor
        · constructor
          · intro zero
            have oneNeZero : (1 : Fin 6) ≠ 0 := by decide
            exact False.elim (oneNeZero (exactEval.symm.trans zero))
          · intro edge
            exact False.elim (adjacent edge)
        · intro _
          exact Or.inl exactEval
    | cons next rest =>
        have nextNeTarget : next ≠ target := by
          intro equal
          subst next
          apply adjacent
          exact
            (S5_107.mem_adjacentPairs_iff_exists_split
              source target word).mpr ⟨before, rest, split⟩
        have nextNeSource : next ≠ source := by
          intro equal
          apply free.2
          simp [equal]
        have restFree : source ∉ rest := by
          intro member
          exact free.2 (by simp [member])
        have evaluated :
            listEvalFrom none
                (proposition20_7AdjacencyValuation source target)
                word.toList = some 2 := by
          rw [split]
          exact listEval_nonadjacent different nextNeSource nextNeTarget
            before rest free.1 restFree
        rw [listEvalFrom_toList] at evaluated
        have exactEval :
            publishedTable.semigroup.eval
                (proposition20_7AdjacencyValuation source target) word = (2 : Fin 6) :=
          Option.some.inj evaluated
        constructor
        · constructor
          · intro zero
            have twoNeZero : (2 : Fin 6) ≠ 0 := by decide
            exact False.elim (twoNeZero (exactEval.symm.trans zero))
          · intro edge
            exact False.elim (adjacent edge)
        · intro _
          exact Or.inr exactEval

/-! ## Semantic transport of the two factor relations -/

private theorem simple_source_ne_of_adjacent
    {whole : List Nat} {source target : Nat}
    (simple : Simple whole source)
    (adjacent : (source, target) ∈ S5_107.listAdjacentPairs whole) :
    source ≠ target := by
  intro equal
  subst target
  obtain ⟨before, after, split⟩ :=
    (S5_107.mem_listAdjacentPairs_iff_exists_split
      source source whole).mp adjacent
  unfold Simple at simple
  rw [split, List.count_append, List.count_cons_self,
    List.count_cons_self] at simple
  omega

private theorem publishedValid_adjacency_iff
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedTable.semigroup)
    (source target : Nat) (different : source ≠ target)
    (lhsSourceSimple : Simple identity.lhs.toList source)
    (lhsTargetPresent : target ∈ identity.lhs.toList) :
    (source, target) ∈ S5_107.listAdjacentPairs identity.lhs.toList ↔
      (source, target) ∈ S5_107.listAdjacentPairs identity.rhs.toList := by
  have rhsSourceSimple :=
    (publishedValid_simple_iff identity valid source).mp lhsSourceSimple
  have rhsTargetPresent :=
    (publishedValid_mem_iff identity valid target).mp lhsTargetPresent
  have lhsScan :=
    publishedAdjacencyDetector_scan source target identity.lhs
      different lhsSourceSimple lhsTargetPresent
  have rhsScan :=
    publishedAdjacencyDetector_scan source target identity.rhs
      different rhsSourceSimple rhsTargetPresent
  have evaluated :=
    valid (proposition20_7AdjacencyValuation source target)
  rw [S5_107.listAdjacentPairs_toList,
    S5_107.listAdjacentPairs_toList]
  constructor
  · intro lhsEdge
    have lhsZero := lhsScan.1.mpr lhsEdge
    exact rhsScan.1.mp (evaluated.symm.trans lhsZero)
  · intro rhsEdge
    have rhsZero := rhsScan.1.mpr rhsEdge
    exact lhsScan.1.mp (evaluated.trans rhsZero)

theorem publishedValid_fsn_iff
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedTable.semigroup)
    (source target : Nat) :
    FSN identity.lhs.toList source target ↔
      FSN identity.rhs.toList source target := by
  constructor
  · rintro ⟨lhsSimple, lhsMultiple, lhsEdge⟩
    have different : source ≠ target := by
      intro equal
      subst target
      exact lhsSimple.not_nonSimple lhsMultiple
    have rhsSimple :=
      (publishedValid_simple_iff identity valid source).mp lhsSimple
    have rhsMultiple :=
      (publishedValid_nonSimple_iff identity valid target).mp lhsMultiple
    have sameEdge :=
      publishedValid_adjacency_iff identity valid source target different
        lhsSimple lhsMultiple.mem
    exact ⟨rhsSimple, rhsMultiple, sameEdge.mp lhsEdge⟩
  · rintro ⟨rhsSimple, rhsMultiple, rhsEdge⟩
    have different : source ≠ target := by
      intro equal
      subst target
      exact rhsSimple.not_nonSimple rhsMultiple
    have lhsSimple :=
      (publishedValid_simple_iff identity valid source).mpr rhsSimple
    have lhsMultiple :=
      (publishedValid_nonSimple_iff identity valid target).mpr rhsMultiple
    have sameEdge :=
      publishedValid_adjacency_iff identity valid source target different
        lhsSimple lhsMultiple.mem
    exact ⟨lhsSimple, lhsMultiple, sameEdge.mpr rhsEdge⟩

theorem publishedValid_fss_iff
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedTable.semigroup)
    (source target : Nat) :
    FSS identity.lhs.toList source target ↔
      FSS identity.rhs.toList source target := by
  constructor
  · rintro ⟨lhsSourceSimple, lhsTargetSimple, lhsEdge⟩
    have different :=
      simple_source_ne_of_adjacent lhsSourceSimple lhsEdge
    have rhsSourceSimple :=
      (publishedValid_simple_iff identity valid source).mp lhsSourceSimple
    have rhsTargetSimple :=
      (publishedValid_simple_iff identity valid target).mp lhsTargetSimple
    have sameEdge :=
      publishedValid_adjacency_iff identity valid source target different
        lhsSourceSimple lhsTargetSimple.mem
    exact ⟨rhsSourceSimple, rhsTargetSimple, sameEdge.mp lhsEdge⟩
  · rintro ⟨rhsSourceSimple, rhsTargetSimple, rhsEdge⟩
    have different :=
      simple_source_ne_of_adjacent rhsSourceSimple rhsEdge
    have lhsSourceSimple :=
      (publishedValid_simple_iff identity valid source).mpr rhsSourceSimple
    have lhsTargetSimple :=
      (publishedValid_simple_iff identity valid target).mpr rhsTargetSimple
    have sameEdge :=
      publishedValid_adjacency_iff identity valid source target different
        lhsSourceSimple lhsTargetSimple.mem
    exact ⟨lhsSourceSimple, lhsTargetSimple, sameEdge.mpr rhsEdge⟩

/-- The unrestricted necessary invariant of Lee--Zhang Lemma 20.8 for the
published table E4. -/
theorem publishedValidInvariant
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedTable.semigroup) :
    SameInvariant identity.lhs.toList identity.rhs.toList :=
  { multiplicity := publishedValid_sameMultiplicityClass identity valid
    firstLetter := publishedValid_firstLetter_eq identity valid
    fsn := publishedValid_fsn_iff identity valid
    fss := publishedValid_fss_iff identity valid }

end SemigroupBasis.CoRoots.Order6LeeZhangProposition20_7E4
