import SemigroupBasis.CoRoots.Order6SporadicSection18ReductionSemantics
import SemigroupBasis.Examples.ConnectedComponentFourComponents
import SemigroupBasis.Examples.UniqueSeparatorFourInvariant

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Reduction

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6SporadicSection12
open SemigroupBasis.CoRoots.Order6SporadicSection18.Actual
open SemigroupBasis.Examples


/-!
The C7 reduction specializes the pinned B7 proof of the operational form of Lee--Zhang Lemma 2.6(ii).
The embedded `S4_69 = B0` transports every exact unique-separator cut of a
valid identity.  Idempotent separability then makes the two aligned factors
valid identities of the actual C7 table.  Strong recursion removes all such cuts.

An exact-cut-free word need not itself be connected: its deterministic
support components are the pairwise-disjoint connected factors appearing in
the paper.  The final bridge below records this implication explicitly.
-/

/-- The source domain left after every `B0` exact separator cut is split. -/
def NoExactSeparatorCut (word : Word Nat) : Prop :=
  ¬∃ left separator right,
    UniqueSeparatorFourExactCut word.toList left separator right

private theorem valid_b0_equalEval
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ valuation : Nat → Fin 4,
      uniqueSeparatorFour.semigroup.eval valuation identity.lhs =
        uniqueSeparatorFour.semigroup.eval valuation identity.rhs := by
  exact valid_b0 identity valid

private theorem valid_sameContent
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SameContent identity.lhs identity.rhs := by
  intro letter
  exact uniqueSeparatorFourEqualEval_support_iff
    identity.lhs identity.rhs
      (valid_b0_equalEval identity valid) letter

private theorem noExactSeparatorCut_rhs
    {identity : Identity Nat}
    (valid : identity.SatisfiedBy table.semigroup)
    (sourceFree : NoExactSeparatorCut identity.lhs) :
    NoExactSeparatorCut identity.rhs := by
  intro targetCutExists
  rcases targetCutExists with
    ⟨targetLeft, separator, targetRight, targetCut⟩
  obtain ⟨sourceLeft, sourceRight, sourceCut, _, _⟩ :=
    uniqueSeparatorFourEqualEval_transportExactCut
      identity.rhs identity.lhs
      (fun valuation => (valid_b0_equalEval identity valid valuation).symm)
      targetCut
  exact sourceFree ⟨sourceLeft, separator, sourceRight, sourceCut⟩

private theorem wordDisjoint_symm
    {left right : Word Nat}
    (disjoint : WordDisjoint left right) :
    WordDisjoint right left := by
  intro letter rightMember leftMember
  exact disjoint letter leftMember rightMember

private theorem component_left_valid
    {identity : Identity Nat} {left right left' right' : Word Nat}
    (valid : identity.SatisfiedBy table.semigroup)
    (leftSplit : identity.lhs = left ++ right)
    (rightSplit : identity.rhs = left' ++ right')
    (disjoint : WordDisjoint left right)
    (leftContent : SameContent left left')
    (rightContent : SameContent right right') :
    (Identity.mk left left').SatisfiedBy table.semigroup := by
  intro valuation
  by_cases same :
      table.semigroup.eval valuation left =
        table.semigroup.eval valuation left'
  · exact same
  have different :
      table.semigroup.eval valuation left ≠
        table.semigroup.eval valuation left' := same
  rcases idempotentSeparable
      (table.semigroup.eval valuation left)
      (table.semigroup.eval valuation left') different with
    ⟨_, ⟨rightIdempotent, rightIdempotent_mul, separates⟩⟩
  let combined : Nat → Fin table.order := fun letter =>
    if letter ∈ left.toList then valuation letter else rightIdempotent
  have evalLeft :
      table.semigroup.eval combined left =
        table.semigroup.eval valuation left :=
    eval_eq_of_agree_on_word table (by
      intro letter member
      simp [combined, member])
  have evalLeft' :
      table.semigroup.eval combined left' =
        table.semigroup.eval valuation left' :=
    eval_eq_of_agree_on_word table (by
      intro letter member
      have inLeft := (leftContent letter).mpr member
      simp [combined, inLeft])
  have evalRight :
      table.semigroup.eval combined right = rightIdempotent := by
    rw [eval_eq_of_agree_on_word table
      (second := fun _ => rightIdempotent) (by
        intro letter member
        have notLeft := wordDisjoint_symm disjoint letter member
        simp [combined, notLeft])]
    exact eval_constant_idempotent table rightIdempotent
      rightIdempotent_mul right
  have evalRight' :
      table.semigroup.eval combined right' = rightIdempotent := by
    rw [eval_eq_of_agree_on_word table
      (second := fun _ => rightIdempotent) (by
        intro letter member
        have inRight := (rightContent letter).mpr member
        have notLeft := wordDisjoint_symm disjoint letter inRight
        simp [combined, notLeft])]
    exact eval_constant_idempotent table rightIdempotent
      rightIdempotent_mul right'
  have wholeEquality := valid combined
  rw [leftSplit, rightSplit, Semigroup.eval_append,
    Semigroup.eval_append, evalLeft, evalLeft', evalRight,
    evalRight'] at wholeEquality
  exact (separates wholeEquality).elim

private theorem component_right_valid
    {identity : Identity Nat} {left right left' right' : Word Nat}
    (valid : identity.SatisfiedBy table.semigroup)
    (leftSplit : identity.lhs = left ++ right)
    (rightSplit : identity.rhs = left' ++ right')
    (disjoint : WordDisjoint left right)
    (leftContent : SameContent left left')
    (rightContent : SameContent right right') :
    (Identity.mk right right').SatisfiedBy table.semigroup := by
  intro valuation
  by_cases same :
      table.semigroup.eval valuation right =
        table.semigroup.eval valuation right'
  · exact same
  have different :
      table.semigroup.eval valuation right ≠
        table.semigroup.eval valuation right' := same
  rcases idempotentSeparable
      (table.semigroup.eval valuation right)
      (table.semigroup.eval valuation right') different with
    ⟨⟨leftIdempotent, leftIdempotent_mul, separates⟩, _⟩
  let combined : Nat → Fin table.order := fun letter =>
    if letter ∈ right.toList then valuation letter else leftIdempotent
  have evalRight :
      table.semigroup.eval combined right =
        table.semigroup.eval valuation right :=
    eval_eq_of_agree_on_word table (by
      intro letter member
      simp [combined, member])
  have evalRight' :
      table.semigroup.eval combined right' =
        table.semigroup.eval valuation right' :=
    eval_eq_of_agree_on_word table (by
      intro letter member
      have inRight := (rightContent letter).mpr member
      simp [combined, inRight])
  have evalLeft :
      table.semigroup.eval combined left = leftIdempotent := by
    rw [eval_eq_of_agree_on_word table
      (second := fun _ => leftIdempotent) (by
        intro letter member
        have notRight := disjoint letter member
        simp [combined, notRight])]
    exact eval_constant_idempotent table leftIdempotent
      leftIdempotent_mul left
  have evalLeft' :
      table.semigroup.eval combined left' = leftIdempotent := by
    rw [eval_eq_of_agree_on_word table
      (second := fun _ => leftIdempotent) (by
        intro letter member
        have inLeft := (leftContent letter).mpr member
        have notRight := disjoint letter inLeft
        simp [combined, notRight])]
    exact eval_constant_idempotent table leftIdempotent
      leftIdempotent_mul left'
  have wholeEquality := valid combined
  rw [leftSplit, rightSplit, Semigroup.eval_append,
    Semigroup.eval_append, evalLeft, evalLeft', evalRight,
    evalRight'] at wholeEquality
  exact (separates wholeEquality).elim

private theorem foldl_constantOne_from_zero :
    ∀ letters : List Nat,
      letters.foldl
          (fun current _ =>
            uniqueSeparatorFourMul current (1 : Fin 4))
          (0 : Fin 4) = 0
  | [] => rfl
  | _ :: rest => by
      simp only [List.foldl_cons]
      rw [show uniqueSeparatorFourMul (0 : Fin 4) 1 = 0 by decide]
      exact foldl_constantOne_from_zero rest

private theorem eval_constantOne_eq_one_iff_tail_nil
    (word : Word Nat) :
    uniqueSeparatorFour.semigroup.eval (fun _ => (1 : Fin 4)) word =
        (1 : Fin 4) ↔
      word.tail = [] := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil => simp [Semigroup.eval]
      | cons next rest =>
          simp only [Semigroup.eval, List.foldl_cons]
          change
            rest.foldl
                (fun current _ =>
                  uniqueSeparatorFourMul current (1 : Fin 4))
                (uniqueSeparatorFourMul (1 : Fin 4) (1 : Fin 4)) =
              (1 : Fin 4) ↔ next :: rest = []
          rw [show uniqueSeparatorFourMul (1 : Fin 4) 1 = 0 by decide,
            foldl_constantOne_from_zero]
          simp

theorem singletonRigidity : SingletonRigidity table := by
  intro identity valid lengthOne
  cases sourceEq : identity.lhs with
  | mk sourceHead sourceTail =>
      simp only [sourceEq, Word.toList, List.length_cons] at lengthOne
      have sourceTailEmpty : sourceTail = [] :=
        List.eq_nil_of_length_eq_zero (by omega)
      subst sourceTail
      have equalEval := valid_b0_equalEval identity valid
      have sourceEval :
          uniqueSeparatorFour.semigroup.eval
              (fun _ => (1 : Fin 4)) identity.lhs = (1 : Fin 4) := by
        simp [sourceEq, Semigroup.eval]
      have targetEval :
          uniqueSeparatorFour.semigroup.eval
              (fun _ => (1 : Fin 4)) identity.rhs = (1 : Fin 4) :=
        (equalEval (fun _ => (1 : Fin 4))).symm.trans sourceEval
      have targetTailEmpty :=
        (eval_constantOne_eq_one_iff_tail_nil identity.rhs).mp targetEval
      cases targetEq : identity.rhs with
      | mk targetHead targetTail =>
          have targetTailEq : targetTail = [] := by
            simpa [targetEq] using targetTailEmpty
          subst targetTail
          have sourceMember : sourceHead ∈ identity.lhs.toList := by
            simp [sourceEq, Word.toList]
          have targetMember : sourceHead ∈ identity.rhs.toList :=
            (valid_sameContent identity valid sourceHead).mp sourceMember
          have headEq : sourceHead = targetHead := by
            simpa [targetEq, Word.toList] using targetMember
          subst targetHead
          rfl

private theorem exactCut_separator_not_mem_left
    {letters left right : List Nat} {separator : Nat}
    (cut :
      UniqueSeparatorFourExactCut letters left separator right) :
    separator ∉ left := by
  rintro member
  rcases cut with ⟨shape, countOne, _⟩
  have positive : 0 < left.count separator :=
    List.count_pos_iff.mpr member
  rw [shape, List.count_append, List.count_cons_self] at countOne
  omega

private theorem exactCut_separator_not_mem_right
    {letters left right : List Nat} {separator : Nat}
    (cut :
      UniqueSeparatorFourExactCut letters left separator right) :
    separator ∉ right := by
  rintro member
  rcases cut with ⟨shape, countOne, _⟩
  have positive : 0 < right.count separator :=
    List.count_pos_iff.mpr member
  rw [shape, List.count_append, List.count_cons_self] at countOne
  omega

private structure ExactCutBinarySplit
    (identity : Identity Nat) where
  left : Word Nat
  right : Word Nat
  targetLeft : Word Nat
  targetRight : Word Nat
  sourceShape : identity.lhs = left ++ right
  targetShape : identity.rhs = targetLeft ++ targetRight
  leftValid :
    (Identity.mk left targetLeft).SatisfiedBy table.semigroup
  rightValid :
    (Identity.mk right targetRight).SatisfiedBy table.semigroup
  leftShort : left.toList.length < identity.lhs.toList.length
  rightShort : right.toList.length < identity.lhs.toList.length

private theorem exists_binarySplit_of_exactCut
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup)
    (notSingleton : identity.lhs.toList.length ≠ 1)
    {sourceLeft sourceRight : List Nat} {separator : Nat}
    (sourceCut :
      UniqueSeparatorFourExactCut identity.lhs.toList
        sourceLeft separator sourceRight) :
    Nonempty (ExactCutBinarySplit identity) := by
  have equalEval := valid_b0_equalEval identity valid
  obtain
    ⟨targetLeftList, targetRightList, targetCut,
      targetLeftSupport, targetRightSupport⟩ :=
    uniqueSeparatorFourEqualEval_transportExactCut
      identity.lhs identity.rhs equalEval sourceCut
  have sourceSeparatorNotLeft :=
    exactCut_separator_not_mem_left sourceCut
  have sourceSeparatorNotRight :=
    exactCut_separator_not_mem_right sourceCut
  rcases sourceCut with
    ⟨sourceListShape, _, sourceSidesDisjoint⟩
  rcases targetCut with
    ⟨targetListShape, _, _⟩
  by_cases sourceLeftNonempty : sourceLeft ≠ []
  · have targetLeftNonempty : targetLeftList ≠ [] := by
      intro targetLeftEmpty
      apply sourceLeftNonempty
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro letter sourceMember
      have targetMember :=
        (targetLeftSupport letter).mpr sourceMember
      simpa [targetLeftEmpty] using targetMember
    let leftWord :=
      connectedComponentWordOfNonempty sourceLeft sourceLeftNonempty
    let rightWord :=
      connectedComponentWordOfNonempty
        (separator :: sourceRight) (by simp)
    let targetLeftWord :=
      connectedComponentWordOfNonempty
        targetLeftList targetLeftNonempty
    let targetRightWord :=
      connectedComponentWordOfNonempty
        (separator :: targetRightList) (by simp)
    have sourceShape : identity.lhs = leftWord ++ rightWord := by
      apply Word.toList_injective
      simpa [leftWord, rightWord, Word.toList_append] using
        sourceListShape
    have targetShape :
        identity.rhs = targetLeftWord ++ targetRightWord := by
      apply Word.toList_injective
      simpa [targetLeftWord, targetRightWord, Word.toList_append] using
        targetListShape
    have sourceDisjoint : WordDisjoint leftWord rightWord := by
      intro letter leftMember rightMember
      have leftMember' : letter ∈ sourceLeft := by
        simpa [leftWord] using leftMember
      have rightMember' : letter ∈ separator :: sourceRight := by
        simpa [rightWord] using rightMember
      rcases List.mem_cons.mp rightMember' with separatorEq | inRight
      · subst letter
        exact sourceSeparatorNotLeft leftMember'
      · exact sourceSidesDisjoint letter leftMember' inRight
    have leftContent : SameContent leftWord targetLeftWord := by
      intro letter
      simpa [leftWord, targetLeftWord] using
        (targetLeftSupport letter).symm
    have rightContent : SameContent rightWord targetRightWord := by
      intro letter
      rw [show rightWord.toList = separator :: sourceRight by
          simp [rightWord],
        show targetRightWord.toList = separator :: targetRightList by
          simp [targetRightWord]]
      simp only [List.mem_cons]
      rw [targetRightSupport letter]
    have leftShort :
        leftWord.toList.length < identity.lhs.toList.length := by
      rw [show leftWord.toList = sourceLeft by simp [leftWord],
        sourceListShape, List.length_append, List.length_cons]
      omega
    have rightShort :
        rightWord.toList.length < identity.lhs.toList.length := by
      have leftPositive : 0 < sourceLeft.length :=
        List.length_pos_iff.mpr sourceLeftNonempty
      rw [show rightWord.toList = separator :: sourceRight by
          simp [rightWord],
        sourceListShape, List.length_append, List.length_cons]
      omega
    refine ⟨?_⟩
    exact
      { left := leftWord
        right := rightWord
        targetLeft := targetLeftWord
        targetRight := targetRightWord
        sourceShape := sourceShape
        targetShape := targetShape
        leftValid :=
          component_left_valid valid sourceShape targetShape
            sourceDisjoint leftContent rightContent
        rightValid :=
          component_right_valid valid sourceShape targetShape
            sourceDisjoint leftContent rightContent
        leftShort := leftShort
        rightShort := rightShort }
  · have sourceLeftEmpty : sourceLeft = [] := by
      exact Decidable.not_not.mp sourceLeftNonempty
    have targetLeftEmpty : targetLeftList = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro letter targetMember
      have sourceMember := (targetLeftSupport letter).mp targetMember
      simpa [sourceLeftEmpty] using sourceMember
    have sourceRightNonempty : sourceRight ≠ [] := by
      intro sourceRightEmpty
      apply notSingleton
      rw [sourceListShape, sourceLeftEmpty, sourceRightEmpty]
      simp
    have targetRightNonempty : targetRightList ≠ [] := by
      intro targetRightEmpty
      apply sourceRightNonempty
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro letter sourceMember
      have targetMember :=
        (targetRightSupport letter).mpr sourceMember
      simpa [targetRightEmpty] using targetMember
    let leftWord := Word.singleton separator
    let rightWord :=
      connectedComponentWordOfNonempty
        sourceRight sourceRightNonempty
    let targetLeftWord := Word.singleton separator
    let targetRightWord :=
      connectedComponentWordOfNonempty
        targetRightList targetRightNonempty
    have sourceShape : identity.lhs = leftWord ++ rightWord := by
      apply Word.toList_injective
      rw [Word.toList_append]
      have leftList : leftWord.toList = [separator] := rfl
      have rightList : rightWord.toList = sourceRight := by
        simp only [rightWord, connectedComponentWordOfNonempty_toList]
      rw [leftList, rightList]
      simpa only [sourceLeftEmpty, List.nil_append] using sourceListShape
    have targetShape :
        identity.rhs = targetLeftWord ++ targetRightWord := by
      apply Word.toList_injective
      rw [Word.toList_append]
      have leftList : targetLeftWord.toList = [separator] := rfl
      have rightList : targetRightWord.toList = targetRightList := by
        simp only [targetRightWord, connectedComponentWordOfNonempty_toList]
      rw [leftList, rightList]
      simpa only [targetLeftEmpty, List.nil_append] using targetListShape
    have sourceDisjoint : WordDisjoint leftWord rightWord := by
      intro letter leftMember rightMember
      have letterEq : letter = separator := by
        simpa [leftWord] using leftMember
      subst letter
      have inRight : separator ∈ sourceRight := by
        simpa [rightWord] using rightMember
      exact sourceSeparatorNotRight inRight
    have leftContent : SameContent leftWord targetLeftWord := by
      intro letter
      simp [leftWord, targetLeftWord]
    have rightContent : SameContent rightWord targetRightWord := by
      intro letter
      simpa [rightWord, targetRightWord] using
        (targetRightSupport letter).symm
    have sourceLong : 2 ≤ identity.lhs.toList.length := by
      have positive : 0 < identity.lhs.toList.length := by
        cases identity.lhs
        simp [Word.toList]
      omega
    have leftShort :
        leftWord.toList.length < identity.lhs.toList.length := by
      simpa [leftWord] using sourceLong
    have rightShort :
        rightWord.toList.length < identity.lhs.toList.length := by
      rw [show rightWord.toList = sourceRight by simp [rightWord],
        sourceListShape, sourceLeftEmpty]
      simp
    refine ⟨?_⟩
    exact
      { left := leftWord
        right := rightWord
        targetLeft := targetLeftWord
        targetRight := targetRightWord
        sourceShape := sourceShape
        targetShape := targetShape
        leftValid :=
          component_left_valid valid sourceShape targetShape
            sourceDisjoint leftContent rightContent
        rightValid :=
          component_right_valid valid sourceShape targetShape
            sourceDisjoint leftContent rightContent
        leftShort := leftShort
        rightShort := rightShort }

private structure ExactCutFreeDecomposition
    (identity : Identity Nat) (pieces : List (Identity Nat)) : Prop where
  models : Models table.semigroup pieces
  cutFree :
    ∀ piece, piece ∈ pieces →
      NoExactSeparatorCut piece.lhs ∧
        NoExactSeparatorCut piece.rhs
  derives : Derives pieces identity.lhs identity.rhs

private theorem derives_mono
    {source target : List (Identity Nat)} {left right : Word Nat}
    (subset : ∀ identity, identity ∈ source → identity ∈ target)
    (derivation : Derives source left right) :
    Derives target left right :=
  derivation.transport fun identity member =>
    Derives.fromBasis (subset identity member)

private theorem exists_exactCutFree_decomposition
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∃ pieces, ExactCutFreeDecomposition identity pieces := by
  classical
  let targetLength := identity.lhs.toList.length
  have inductionStatement :
      ∀ length,
        (∀ smaller < length,
          ∀ current : Identity Nat,
            current.lhs.toList.length = smaller →
            current.SatisfiedBy table.semigroup →
            ∃ pieces,
              ExactCutFreeDecomposition current pieces) →
        ∀ current : Identity Nat,
          current.lhs.toList.length = length →
          current.SatisfiedBy table.semigroup →
          ∃ pieces,
            ExactCutFreeDecomposition current pieces := by
    intro length smaller current lengthEq currentValid
    by_cases lengthOne : length = 1
    · have currentLengthOne : current.lhs.toList.length = 1 := by
        omega
      have currentEq :=
        singletonRigidity current currentValid currentLengthOne
      refine ⟨[], ?_⟩
      refine
        { models := ?_
          cutFree := ?_
          derives := ?_ }
      · intro piece member
        simp at member
      · intro piece member
        simp at member
      · rw [currentEq]
        exact Derives.refl current.rhs
    · by_cases sourceFree : NoExactSeparatorCut current.lhs
      · have targetFree :=
          noExactSeparatorCut_rhs currentValid sourceFree
        refine ⟨[current], ?_⟩
        refine
          { models := ?_
            cutFree := ?_
            derives := ?_ }
        · intro piece member
          simp only [List.mem_singleton] at member
          subst piece
          exact currentValid
        · intro piece member
          simp only [List.mem_singleton] at member
          subst piece
          exact ⟨sourceFree, targetFree⟩
        · exact Derives.fromBasis (by simp)
      · have cutExists :
          ∃ sourceLeft separator sourceRight,
            UniqueSeparatorFourExactCut current.lhs.toList
              sourceLeft separator sourceRight := by
          apply Classical.byContradiction
          intro noCut
          exact sourceFree noCut
        rcases cutExists with
          ⟨sourceLeft, separator, sourceRight, sourceCut⟩
        have notSingleton : current.lhs.toList.length ≠ 1 := by
          omega
        obtain ⟨split⟩ :=
          exists_binarySplit_of_exactCut current currentValid
            notSingleton sourceCut
        let leftIdentity : Identity Nat :=
          ⟨split.left, split.targetLeft⟩
        let rightIdentity : Identity Nat :=
          ⟨split.right, split.targetRight⟩
        have leftLengthEq :
            leftIdentity.lhs.toList.length =
              split.left.toList.length := rfl
        have rightLengthEq :
            rightIdentity.lhs.toList.length =
              split.right.toList.length := rfl
        rcases smaller split.left.toList.length
            (by simpa [lengthEq] using split.leftShort)
            leftIdentity leftLengthEq split.leftValid with
          ⟨leftPieces, leftDecomposition⟩
        rcases smaller split.right.toList.length
            (by simpa [lengthEq] using split.rightShort)
            rightIdentity rightLengthEq split.rightValid with
          ⟨rightPieces, rightDecomposition⟩
        refine ⟨leftPieces ++ rightPieces, ?_⟩
        refine
          { models := ?_
            cutFree := ?_
            derives := ?_ }
        · intro piece member
          rcases List.mem_append.mp member with member | member
          · exact leftDecomposition.models piece member
          · exact rightDecomposition.models piece member
        · intro piece member
          rcases List.mem_append.mp member with member | member
          · exact leftDecomposition.cutFree piece member
          · exact rightDecomposition.cutFree piece member
        · have leftDerives :
              Derives (leftPieces ++ rightPieces)
                split.left split.targetLeft :=
            derives_mono
              (fun piece member =>
                List.mem_append.mpr (Or.inl member))
              leftDecomposition.derives
          have rightDerives :
              Derives (leftPieces ++ rightPieces)
                split.right split.targetRight :=
            derives_mono
              (fun piece member =>
                List.mem_append.mpr (Or.inr member))
              rightDecomposition.derives
          rw [split.sourceShape, split.targetShape]
          exact Derives.trans
            (Derives.appendRight leftDerives split.right)
            (Derives.prepend split.targetLeft rightDerives)
  exact
    Nat.strongRecOn
      (motive := fun length =>
        ∀ current : Identity Nat,
          current.lhs.toList.length = length →
          current.SatisfiedBy table.semigroup →
          ∃ pieces,
            ExactCutFreeDecomposition current pieces)
      targetLength inductionStatement identity rfl valid

/-- Every valid C7 identity has finite derivational support consisting only
of valid exact-cut-free identities. -/
theorem restrictedBasisReductionNoExact :
    RestrictedBasisReduction table NoExactSeparatorCut := by
  refine ⟨?_⟩
  intro identity valid
  rcases exists_exactCutFree_decomposition identity valid with
    ⟨pieces, decomposition⟩
  exact
    ⟨pieces, decomposition.models, decomposition.cutFree,
      decomposition.derives⟩

private def wordOfListOr
    (fallback : Nat) : List Nat → Word Nat
  | [] => Word.singleton fallback
  | head :: tail => ⟨head, tail⟩

private theorem wordOfListOr_toList
    (fallback : Nat) {letters : List Nat}
    (nonempty : letters ≠ []) :
    (wordOfListOr fallback letters).toList = letters := by
  cases letters with
  | nil => contradiction
  | cons head tail => rfl

private theorem word_toList_ne_nil (word : Word Nat) :
    word.toList ≠ [] := by
  cases word
  simp [Word.toList]

private theorem connected_of_supportConnected
    (word : Word Nat)
    (lengthAtLeastTwo : 2 ≤ word.toList.length)
    (supportConnected :
      ConnectedComponentSupportConnected word.toList) :
    Connected word := by
  refine ⟨lengthAtLeastTwo, ?_⟩
  rintro ⟨left, right, shape, disjoint⟩
  have listShape :
      word.toList = left.toList ++ right.toList := by
    rw [shape, Word.toList_append]
  rcases supportConnected left.toList right.toList listShape
      (word_toList_ne_nil left) (word_toList_ne_nil right) with
    ⟨letter, leftMember, rightMember⟩
  exact disjoint letter leftMember rightMember

private def connectedFactorWords (word : Word Nat) : List (Word Nat) :=
  (connectedComponentDecomposeList word.toList).map
    (wordOfListOr word.head)

private theorem connectedFactorWords_nonempty (word : Word Nat) :
    connectedFactorWords word ≠ [] := by
  have componentsNonempty :
      connectedComponentDecomposeList word.toList ≠ [] :=
    connectedComponentDecomposeList_nonempty
      (word_toList_ne_nil word)
  obtain ⟨first, rest, componentsShape⟩ :=
    List.exists_cons_of_ne_nil componentsNonempty
  rw [connectedFactorWords, componentsShape]
  simp

private theorem connectedFactorWords_connected
    (word : Word Nat)
    (noExactCut : NoExactSeparatorCut word) :
    ∀ factor, factor ∈ connectedFactorWords word → Connected factor := by
  intro factor factorMember
  rcases List.mem_map.mp factorMember with
    ⟨component, componentMember, factorEq⟩
  subst factor
  have componentNonempty : component ≠ [] :=
    connectedComponentDecomposeList_nonempty_components
      word.toList component componentMember
  have componentLength : 2 ≤ component.length :=
    connectedComponentDecomposeList_components_length_ge_two_of_no_exactCut
      noExactCut component componentMember
  apply connected_of_supportConnected
  · simpa [wordOfListOr_toList word.head componentNonempty] using
      componentLength
  · simpa [wordOfListOr_toList word.head componentNonempty] using
      connectedComponentDecomposeList_supportConnected
        word.toList component componentMember

private theorem mappedFactorWords_pairwiseDisjoint
    (fallback : Nat) :
    ∀ components : List (List Nat),
      (∀ component, component ∈ components → component ≠ []) →
      components.Pairwise ConnectedComponentSupportsDisjoint →
      (components.map (wordOfListOr fallback)).Pairwise WordDisjoint
  | [], _, _ => by simp
  | component :: remaining, nonempty, pairwise => by
      simp only [List.map_cons, List.pairwise_cons] at pairwise ⊢
      refine ⟨?_, mappedFactorWords_pairwiseDisjoint fallback remaining
        (fun candidate member =>
          nonempty candidate (List.Mem.tail component member))
        pairwise.2⟩
      intro factor factorMember letter componentMember factorLetterMember
      rcases List.mem_map.mp factorMember with
        ⟨candidate, candidateMember, factorEq⟩
      subst factor
      have componentNonempty : component ≠ [] :=
        nonempty component (List.Mem.head remaining)
      have candidateNonempty : candidate ≠ [] :=
        nonempty candidate (List.Mem.tail component candidateMember)
      have componentMember' : letter ∈ component := by
        simpa [wordOfListOr_toList fallback componentNonempty] using
          componentMember
      have candidateMember' : letter ∈ candidate := by
        simpa [wordOfListOr_toList fallback candidateNonempty] using
          factorLetterMember
      exact
        pairwise.1 candidate candidateMember letter
          componentMember' candidateMember'

private theorem connectedFactorWords_pairwiseDisjoint
    (word : Word Nat) :
    (connectedFactorWords word).Pairwise WordDisjoint := by
  apply mappedFactorWords_pairwiseDisjoint word.head
  · exact connectedComponentDecomposeList_nonempty_components word.toList
  · exact connectedComponentDecomposeList_pairwiseDisjoint word.toList

private theorem mappedFactorWords_toLists
    (fallback : Nat) :
    ∀ components : List (List Nat),
      (∀ component, component ∈ components → component ≠ []) →
      (components.map (wordOfListOr fallback)).map Word.toList =
        components
  | [], _ => rfl
  | component :: remaining, nonempty => by
      simp only [List.map_cons]
      rw [wordOfListOr_toList fallback
        (nonempty component (List.Mem.head remaining))]
      rw [mappedFactorWords_toLists fallback remaining
        (fun candidate member =>
          nonempty candidate (List.Mem.tail component member))]

private theorem connectedFactorWords_toLists (word : Word Nat) :
    (connectedFactorWords word).map Word.toList =
      connectedComponentDecomposeList word.toList := by
  exact mappedFactorWords_toLists word.head
    (connectedComponentDecomposeList word.toList)
    (connectedComponentDecomposeList_nonempty_components word.toList)

private theorem appendFactors_toList
    (first : Word Nat) :
    ∀ rest : List (Word Nat),
      (appendFactors first rest).toList =
        ((first :: rest).map Word.toList).flatten
  | [] => by simp [appendFactors]
  | next :: remaining => by
      change
        (appendFactors (first ++ next) remaining).toList =
          ((first :: next :: remaining).map Word.toList).flatten
      rw [appendFactors_toList (first ++ next) remaining]
      simp only [List.map_cons, List.flatten_cons, Word.toList_append]
      simp [List.append_assoc]

/-- An exact-cut-free word is a product of the pairwise-disjoint connected
support components required by Lee--Zhang Lemma 2.6(ii). -/
theorem noExactSeparatorCut_pairwiseProduct
    (word : Word Nat)
    (noExactCut : NoExactSeparatorCut word) :
    PairwiseDisjointConnectedProduct word := by
  have factorsNonempty := connectedFactorWords_nonempty word
  obtain ⟨first, rest, factorsShape⟩ :=
    List.exists_cons_of_ne_nil factorsNonempty
  refine ⟨first, rest, ?_, ?_, ?_⟩
  · intro factor factorMember
    apply connectedFactorWords_connected word noExactCut factor
    rw [factorsShape]
    exact factorMember
  · rw [← factorsShape]
    exact connectedFactorWords_pairwiseDisjoint word
  · apply Word.toList_injective
    rw [appendFactors_toList]
    have factorLists := connectedFactorWords_toLists word
    rw [factorsShape] at factorLists
    calc
      word.toList =
          (connectedComponentDecomposeList word.toList).flatten :=
        (connectedComponentDecomposeList_flatten word.toList).symm
      _ = ((first :: rest).map Word.toList).flatten := by
        rw [← factorLists]

/-- Unrestricted C7 basis reduction to the published connected-product domain.
This constructs finite derivational support, not a complete finite basis. -/
theorem restrictedBasisReduction :
    RestrictedBasisReduction table PairwiseDisjointConnectedProduct := by
  refine ⟨?_⟩
  intro identity valid
  rcases restrictedBasisReductionNoExact.reduce identity valid with
    ⟨source, sourceModels, sourceFree, sourceDerives⟩
  refine ⟨source, sourceModels, ?_, sourceDerives⟩
  intro sourceIdentity member
  exact
    ⟨noExactSeparatorCut_pairwiseProduct sourceIdentity.lhs
        (sourceFree sourceIdentity member).1,
      noExactSeparatorCut_pairwiseProduct sourceIdentity.rhs
        (sourceFree sourceIdentity member).2⟩


/-- Exact final assembly boundary: a proof for EVERY valid identity in the
restricted domain implies the full C7 basis theorem. No such domain-completeness
proof is assumed to have been constructed by this module. -/
theorem basisFor_of_pairwiseConnected
    (complete : ∀ identity : Identity Nat,
      identity.SatisfiedBy Actual.table.semigroup →
      PairwiseDisjointConnectedProduct identity.lhs →
      PairwiseDisjointConnectedProduct identity.rhs →
      Derives basis identity.lhs identity.rhs) :
    BasisFor Actual.table.semigroup basis := by
  refine ⟨Actual.models, ?_⟩
  intro identity valid
  obtain ⟨source, sourceModels, sourceDomain, sourceDerives⟩ :=
    restrictedBasisReduction.reduce identity valid
  exact sourceDerives.transport (fun law member =>
    complete law (sourceModels law member)
      (sourceDomain law member).1 (sourceDomain law member).2)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Reduction.singletonRigidity
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Reduction.restrictedBasisReductionNoExact
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Reduction.noExactSeparatorCut_pairwiseProduct
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Reduction.restrictedBasisReduction
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Reduction.basisFor_of_pairwiseConnected

end SemigroupBasis.CoRoots.Order6SporadicSection18.Reduction
