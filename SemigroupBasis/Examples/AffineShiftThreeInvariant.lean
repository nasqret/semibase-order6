import SemigroupBasis.Examples.AffineShiftThree
import SemigroupBasis.Examples.CyclicThree

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- The semantic decomposition of `S6_15903` into its cyclic unit group and
its three-element left-zero ideal. -/
inductive AffineShiftThreeValue where
  | unit (residue : Fin 3)
  | ideal (residue : Fin 3)
  deriving DecidableEq, Repr

/-- Reconstruct a table element from its semantic class and residue. -/
def affineShiftThreeReconstruct : AffineShiftThreeValue → Fin 6
  | .unit residue => affineShiftThreeUnitResidue residue
  | .ideal residue => affineShiftThreeIdealResidue residue

/-- Classify every table element as a unit residue or an ideal residue. -/
def affineShiftThreeClassify (value : Fin 6) : AffineShiftThreeValue :=
  if value = 1 then .unit 0
  else if value = 4 then .unit 1
  else if value = 5 then .unit 2
  else if value = 0 then .ideal 0
  else if value = 2 then .ideal 1
  else .ideal 2

/-- Classification followed by reconstruction returns the original table
element. -/
theorem affineShiftThreeReconstruct_classify (value : Fin 6) :
    affineShiftThreeReconstruct (affineShiftThreeClassify value) = value := by
  decide +revert

/-- Reconstruction followed by classification returns the semantic value. -/
theorem affineShiftThreeClassify_reconstruct
    (value : AffineShiftThreeValue) :
    affineShiftThreeClassify (affineShiftThreeReconstruct value) = value := by
  cases value with
  | unit residue => decide +revert
  | ideal residue => decide +revert

/-- Every table element has one of the two residue forms. -/
theorem affineShiftThree_exists_unit_or_ideal (value : Fin 6) :
    (∃ residue, value = affineShiftThreeUnitResidue residue) ∨
      ∃ residue, value = affineShiftThreeIdealResidue residue := by
  cases classified : affineShiftThreeClassify value with
  | unit residue =>
      left
      refine ⟨residue, ?_⟩
      have reconstructed := affineShiftThreeReconstruct_classify value
      rw [classified] at reconstructed
      exact reconstructed.symm
  | ideal residue =>
      right
      refine ⟨residue, ?_⟩
      have reconstructed := affineShiftThreeReconstruct_classify value
      rw [classified] at reconstructed
      exact reconstructed.symm

/-- Multiplication on the semantic unit/ideal decomposition. -/
def affineShiftThreeValueMul :
    AffineShiftThreeValue → AffineShiftThreeValue →
      AffineShiftThreeValue
  | .unit left, .unit right => .unit (left + right)
  | .unit left, .ideal right => .ideal (left + right)
  | .ideal left, _ => .ideal left

/-- Semantic multiplication reconstructs to the exact table product. -/
theorem affineShiftThreeReconstruct_mul
    (left right : AffineShiftThreeValue) :
    affineShiftThreeReconstruct
        (affineShiftThreeValueMul left right) =
      affineShiftThree.mul
        (affineShiftThreeReconstruct left)
        (affineShiftThreeReconstruct right) := by
  cases left with
  | unit leftResidue =>
      cases right with
      | unit rightResidue =>
          exact
            (affineShiftThreeMul_unitResidues
              leftResidue rightResidue).symm
      | ideal rightResidue =>
          exact
            (affineShiftThreeMul_unit_ideal
              leftResidue rightResidue).symm
  | ideal leftResidue =>
      exact
        (affineShiftThreeMul_ideal_left leftResidue
          (affineShiftThreeReconstruct right)).symm

theorem affineShiftThreeUnitResidue_injective :
    Function.Injective affineShiftThreeUnitResidue := by
  intro left right equal
  have classified := congrArg affineShiftThreeClassify equal
  change
    affineShiftThreeClassify
        (affineShiftThreeReconstruct (.unit left)) =
      affineShiftThreeClassify
        (affineShiftThreeReconstruct (.unit right)) at classified
  rw [affineShiftThreeClassify_reconstruct,
    affineShiftThreeClassify_reconstruct] at classified
  exact AffineShiftThreeValue.unit.inj classified

theorem affineShiftThreeIdealResidue_injective :
    Function.Injective affineShiftThreeIdealResidue := by
  intro left right equal
  have classified := congrArg affineShiftThreeClassify equal
  change
    affineShiftThreeClassify
        (affineShiftThreeReconstruct (.ideal left)) =
      affineShiftThreeClassify
        (affineShiftThreeReconstruct (.ideal right)) at classified
  rw [affineShiftThreeClassify_reconstruct,
    affineShiftThreeClassify_reconstruct] at classified
  exact AffineShiftThreeValue.ideal.inj classified

theorem affineShiftThreeUnitResidue_ne_idealResidue
    (unit ideal : Fin 3) :
    affineShiftThreeUnitResidue unit ≠
      affineShiftThreeIdealResidue ideal := by
  decide +revert

@[simp]
theorem affineShiftThreeMul_identity_left (right : Fin 6) :
    affineShiftThree.mul (affineShiftThreeUnitResidue 0) right = right := by
  decide +revert

@[simp]
theorem affineShiftThreeMul_identity_right (left : Fin 6) :
    affineShiftThree.mul left (affineShiftThreeUnitResidue 0) = left := by
  decide +revert

/-- Evaluate a possibly empty list in `S6_15903`. The empty list is the
identity unit, whose residue is zero. -/
def affineShiftThreeEvalList
    {alpha : Type} (valuation : alpha → Fin 6) (letters : List alpha) :
    Fin 6 :=
  letters.foldr
    (fun letter current =>
      affineShiftThree.mul (valuation letter) current)
    (affineShiftThreeUnitResidue 0)

@[simp]
theorem affineShiftThreeEvalList_nil
    {alpha : Type} (valuation : alpha → Fin 6) :
    affineShiftThreeEvalList valuation [] =
      affineShiftThreeUnitResidue 0 :=
  rfl

@[simp]
theorem affineShiftThreeEvalList_cons
    {alpha : Type} (valuation : alpha → Fin 6)
    (letter : alpha) (rest : List alpha) :
    affineShiftThreeEvalList valuation (letter :: rest) =
      affineShiftThree.mul (valuation letter)
        (affineShiftThreeEvalList valuation rest) :=
  rfl

private theorem affineShiftThreeFoldl_eq_mul_evalList
    {alpha : Type} (valuation : alpha → Fin 6) :
    ∀ (letters : List alpha) (current : Fin 6),
      letters.foldl
          (fun value letter =>
            affineShiftThree.mul value (valuation letter))
          current =
        affineShiftThree.mul current
          (affineShiftThreeEvalList valuation letters)
  | [], current => (affineShiftThreeMul_identity_right current).symm
  | letter :: rest, current => by
      calc
        rest.foldl
            (fun value next =>
              affineShiftThree.mul value (valuation next))
            (affineShiftThree.mul current (valuation letter)) =
            affineShiftThree.mul
              (affineShiftThree.mul current (valuation letter))
              (affineShiftThreeEvalList valuation rest) :=
          affineShiftThreeFoldl_eq_mul_evalList valuation rest _
        _ = affineShiftThree.mul current
              (affineShiftThree.mul (valuation letter)
                (affineShiftThreeEvalList valuation rest)) :=
          affineShiftThree.semigroup.assoc _ _ _
        _ = affineShiftThree.mul current
              (affineShiftThreeEvalList valuation (letter :: rest)) := rfl

/-- The possibly-empty evaluator agrees with semigroup evaluation on the
nonempty list underlying a word. -/
theorem affineShiftThreeEval_eq_evalList
    {alpha : Type} (valuation : alpha → Fin 6) (word : Word alpha) :
    affineShiftThree.semigroup.eval valuation word =
      affineShiftThreeEvalList valuation word.toList := by
  cases word with
  | mk head tail =>
      change
        tail.foldl
            (fun current letter =>
              affineShiftThree.mul current (valuation letter))
            (valuation head) =
          affineShiftThree.mul (valuation head)
            (affineShiftThreeEvalList valuation tail)
      exact affineShiftThreeFoldl_eq_mul_evalList valuation tail _

/-- Evaluation of concatenated lists is multiplication of their values. -/
theorem affineShiftThreeEvalList_append
    {alpha : Type} (valuation : alpha → Fin 6) :
    ∀ left right : List alpha,
      affineShiftThreeEvalList valuation (left ++ right) =
        affineShiftThree.mul
          (affineShiftThreeEvalList valuation left)
          (affineShiftThreeEvalList valuation right)
  | [], right =>
      (affineShiftThreeMul_identity_left
        (affineShiftThreeEvalList valuation right)).symm
  | letter :: rest, right => by
      calc
        affineShiftThreeEvalList valuation
            ((letter :: rest) ++ right) =
            affineShiftThree.mul (valuation letter)
              (affineShiftThreeEvalList valuation (rest ++ right)) := rfl
        _ = affineShiftThree.mul (valuation letter)
              (affineShiftThree.mul
                (affineShiftThreeEvalList valuation rest)
                (affineShiftThreeEvalList valuation right)) := by
          rw [affineShiftThreeEvalList_append valuation rest right]
        _ = affineShiftThree.mul
              (affineShiftThree.mul (valuation letter)
                (affineShiftThreeEvalList valuation rest))
              (affineShiftThreeEvalList valuation right) :=
          (affineShiftThree.semigroup.assoc _ _ _).symm
        _ = affineShiftThree.mul
              (affineShiftThreeEvalList valuation (letter :: rest))
              (affineShiftThreeEvalList valuation right) := rfl

/-- Sum residues in the cyclic group `Fin 3`. -/
def affineShiftThreeResidueSum
    {alpha : Type} (residue : alpha → Fin 3) : List alpha → Fin 3
  | [] => 0
  | letter :: rest =>
      residue letter + affineShiftThreeResidueSum residue rest

private theorem affineShiftThreeAdd_assoc
    (left middle right : Fin 3) :
    left + (middle + right) = (left + middle) + right := by
  decide +revert

private theorem affineShiftThreeAdd_comm
    (left right : Fin 3) : left + right = right + left := by
  decide +revert

theorem affineShiftThreeResidueSum_append
    {alpha : Type} (residue : alpha → Fin 3) :
    ∀ left right : List alpha,
      affineShiftThreeResidueSum residue (left ++ right) =
        affineShiftThreeResidueSum residue left +
          affineShiftThreeResidueSum residue right
  | [], right => by simp [affineShiftThreeResidueSum]
  | letter :: rest, right => by
      simp only [List.cons_append, affineShiftThreeResidueSum]
      rw [affineShiftThreeResidueSum_append residue rest right,
        affineShiftThreeAdd_assoc]

theorem affineShiftThreeResidueSum_perm
    {alpha : Type} (residue : alpha → Fin 3)
    {left right : List alpha} (permutation : left.Perm right) :
    affineShiftThreeResidueSum residue left =
      affineShiftThreeResidueSum residue right := by
  induction permutation with
  | nil => rfl
  | cons letter _ inductionHypothesis =>
      simp [affineShiftThreeResidueSum, inductionHypothesis]
  | swap left right rest =>
      simp only [affineShiftThreeResidueSum]
      calc
        residue right +
            (residue left + affineShiftThreeResidueSum residue rest) =
            (residue right + residue left) +
              affineShiftThreeResidueSum residue rest :=
          affineShiftThreeAdd_assoc _ _ _
        _ = (residue left + residue right) +
              affineShiftThreeResidueSum residue rest := by
          rw [affineShiftThreeAdd_comm (residue right) (residue left)]
        _ = residue left +
              (residue right + affineShiftThreeResidueSum residue rest) :=
          (affineShiftThreeAdd_assoc _ _ _).symm
  | trans _ _ first second =>
      exact first.trans second

/-- If every letter is assigned to a unit, list evaluation is the total unit
residue modulo three. -/
theorem affineShiftThreeEvalList_allUnits
    {alpha : Type} (residue : alpha → Fin 3) :
    ∀ letters : List alpha,
      affineShiftThreeEvalList
          (fun letter => affineShiftThreeUnitResidue (residue letter))
          letters =
        affineShiftThreeUnitResidue
          (affineShiftThreeResidueSum residue letters)
  | [] => rfl
  | letter :: rest => by
      rw [affineShiftThreeEvalList_cons,
        affineShiftThreeEvalList_allUnits residue rest,
        affineShiftThreeMul_unitResidues]
      rfl

/-- A pointwise all-unit hypothesis on one list suffices for the same residue
formula. -/
theorem affineShiftThreeEvalList_allUnits_of
    {alpha : Type} (valuation : alpha → Fin 6)
    (residue : alpha → Fin 3) :
    ∀ letters : List alpha,
      (∀ letter, letter ∈ letters →
        valuation letter =
          affineShiftThreeUnitResidue (residue letter)) →
      affineShiftThreeEvalList valuation letters =
        affineShiftThreeUnitResidue
          (affineShiftThreeResidueSum residue letters)
  | [], _ => rfl
  | letter :: rest, allUnits => by
      have headUnit :
          valuation letter =
            affineShiftThreeUnitResidue (residue letter) :=
        allUnits letter (List.Mem.head rest)
      have tailUnits :
          ∀ next, next ∈ rest →
            valuation next =
              affineShiftThreeUnitResidue (residue next) := by
        intro next member
        exact allUnits next (List.Mem.tail letter member)
      rw [affineShiftThreeEvalList_cons, headUnit,
        affineShiftThreeEvalList_allUnits_of
          valuation residue rest tailUnits,
        affineShiftThreeMul_unitResidues]
      rfl

/-- Once the first ideal-valued letter is reached, the suffix is ignored. The
result is that letter's ideal residue shifted by the sum of unit residues in
the preceding prefix. -/
theorem affineShiftThreeEvalList_firstIdeal
    {alpha : Type} (valuation : alpha → Fin 6)
    (unitResidue : alpha → Fin 3)
    (before : List alpha) (pivot : alpha) (suffix : List alpha)
    (idealResidue : Fin 3)
    (prefixUnits :
      ∀ letter, letter ∈ before →
        valuation letter =
          affineShiftThreeUnitResidue (unitResidue letter))
    (pivotIdeal :
      valuation pivot = affineShiftThreeIdealResidue idealResidue) :
    affineShiftThreeEvalList valuation (before ++ pivot :: suffix) =
      affineShiftThreeIdealResidue
        (affineShiftThreeResidueSum unitResidue before + idealResidue) := by
  induction before with
  | nil =>
      simpa [affineShiftThreeResidueSum, pivotIdeal] using
        affineShiftThreeMul_ideal_left idealResidue
          (affineShiftThreeEvalList valuation suffix)
  | cons letter rest inductionHypothesis =>
      have headUnit :
          valuation letter =
            affineShiftThreeUnitResidue (unitResidue letter) :=
        prefixUnits letter (List.Mem.head rest)
      have tailUnits :
          ∀ next, next ∈ rest →
            valuation next =
              affineShiftThreeUnitResidue (unitResidue next) := by
        intro next member
        exact prefixUnits next (List.Mem.tail letter member)
      simp only [List.cons_append, affineShiftThreeEvalList_cons,
        affineShiftThreeResidueSum]
      rw [headUnit, inductionHypothesis tailUnits,
        affineShiftThreeMul_unit_ideal, affineShiftThreeAdd_assoc]

/-- The maximal prefix strictly before the first selected letter. If the
selected letter is absent, this is the whole list. -/
def affineShiftThreePrefixBeforeFirst (selected : Nat) :
    List Nat → List Nat
  | [] => []
  | letter :: rest =>
      if letter = selected then []
      else letter :: affineShiftThreePrefixBeforeFirst selected rest

theorem affineShiftThreePrefixBeforeFirst_eq_self_of_not_mem
    (selected : Nat) :
    ∀ letters : List Nat, selected ∉ letters →
      affineShiftThreePrefixBeforeFirst selected letters = letters
  | [], _ => rfl
  | letter :: rest, absent => by
      have different : letter ≠ selected := by
        intro equal
        subst letter
        exact absent (List.Mem.head rest)
      have tailAbsent : selected ∉ rest := by
        intro member
        exact absent (List.Mem.tail letter member)
      simp [affineShiftThreePrefixBeforeFirst, different,
        affineShiftThreePrefixBeforeFirst_eq_self_of_not_mem
          selected rest tailAbsent]

theorem affineShiftThreePrefixBeforeFirst_avoids
    (selected : Nat) :
    ∀ letters : List Nat,
      selected ∉ affineShiftThreePrefixBeforeFirst selected letters
  | [] => by simp [affineShiftThreePrefixBeforeFirst]
  | letter :: rest => by
      by_cases hit : letter = selected
      · simp [affineShiftThreePrefixBeforeFirst, hit]
      · simp [affineShiftThreePrefixBeforeFirst, hit, Ne.symm hit,
          affineShiftThreePrefixBeforeFirst_avoids selected rest]

theorem affineShiftThreePrefixBeforeFirst_split
    (selected : Nat) :
    ∀ {letters : List Nat}, selected ∈ letters →
      ∃ suffix,
        letters =
          affineShiftThreePrefixBeforeFirst selected letters ++
            selected :: suffix
  | [], member => by simp at member
  | letter :: rest, member => by
      by_cases hit : letter = selected
      · subst letter
        exact ⟨rest, by simp [affineShiftThreePrefixBeforeFirst]⟩
      · have tailMember : selected ∈ rest := by
          simpa [Ne.symm hit] using member
        obtain ⟨suffix, split⟩ :=
          affineShiftThreePrefixBeforeFirst_split selected tailMember
        refine ⟨suffix, ?_⟩
        simpa only [affineShiftThreePrefixBeforeFirst, if_neg hit,
          List.cons_append] using congrArg (List.cons letter) split

theorem affineShiftThreePrefixBeforeFirst_append_hit
    (selected : Nat) :
    ∀ (before after : List Nat), selected ∉ before →
      affineShiftThreePrefixBeforeFirst selected
          (before ++ selected :: after) = before
  | [], after, _ => by simp [affineShiftThreePrefixBeforeFirst]
  | letter :: rest, after, absent => by
      have different : letter ≠ selected := by
        intro equal
        subst letter
        exact absent (List.Mem.head rest)
      have tailAbsent : selected ∉ rest := by
        intro member
        exact absent (List.Mem.tail letter member)
      simp [affineShiftThreePrefixBeforeFirst, different,
        affineShiftThreePrefixBeforeFirst_append_hit
          selected rest after tailAbsent]

/-- The modulo-three occurrence count, represented directly in `Fin 3`. -/
def affineShiftThreeCountResidue
    (tested : Nat) (letters : List Nat) : Fin 3 :=
  affineShiftThreeResidueSum
    (fun letter => if letter = tested then 1 else 0) letters

@[simp]
theorem affineShiftThreeCountResidue_nil (tested : Nat) :
    affineShiftThreeCountResidue tested [] = 0 :=
  rfl

theorem affineShiftThreeCountResidue_cons
    (tested letter : Nat) (rest : List Nat) :
    affineShiftThreeCountResidue tested (letter :: rest) =
      (if letter = tested then 1 else 0) +
        affineShiftThreeCountResidue tested rest :=
  rfl

theorem affineShiftThreeCountResidue_append
    (tested : Nat) (left right : List Nat) :
    affineShiftThreeCountResidue tested (left ++ right) =
      affineShiftThreeCountResidue tested left +
        affineShiftThreeCountResidue tested right := by
  exact affineShiftThreeResidueSum_append
    (fun letter : Nat => if letter = tested then 1 else 0) left right

theorem affineShiftThreeCountResidue_eq_zero_of_not_mem
    (tested : Nat) :
    ∀ letters : List Nat, tested ∉ letters →
      affineShiftThreeCountResidue tested letters = 0
  | [], _ => rfl
  | letter :: rest, absent => by
      have different : letter ≠ tested := by
        intro equal
        subst letter
        exact absent (List.Mem.head rest)
      have tailAbsent : tested ∉ rest := by
        intro member
        exact absent (List.Mem.tail letter member)
      simp [affineShiftThreeCountResidue_cons, different,
        affineShiftThreeCountResidue_eq_zero_of_not_mem
          tested rest tailAbsent]

/-- A natural number represented modulo three. -/
def affineShiftThreeNatResidue (count : Nat) : Fin 3 :=
  ⟨count % 3, Nat.mod_lt _ (by decide)⟩

private theorem affineShiftThreeNatResidue_succ (count : Nat) :
    (1 : Fin 3) + affineShiftThreeNatResidue count =
      affineShiftThreeNatResidue (count + 1) := by
  apply Fin.ext
  change (1 + count % 3) % 3 = (count + 1) % 3
  omega

theorem affineShiftThreeCountResidue_eq_natResidue
    (tested : Nat) :
    ∀ letters : List Nat,
      affineShiftThreeCountResidue tested letters =
        affineShiftThreeNatResidue (letters.count tested)
  | [] => rfl
  | letter :: rest => by
      rw [affineShiftThreeCountResidue_cons]
      by_cases same : letter = tested
      · subst letter
        rw [List.count_cons_self,
          affineShiftThreeCountResidue_eq_natResidue tested rest]
        simpa using affineShiftThreeNatResidue_succ (rest.count tested)
      · rw [List.count_cons_of_ne same,
          affineShiftThreeCountResidue_eq_natResidue tested rest]
        simp [same]

/-- First occurrences in their left-to-right order, with `seen` used only by
the recursive scan. -/
def affineShiftThreeFirstOccurrencesFrom
    (seen : List Nat) : List Nat → List Nat
  | [] => []
  | letter :: rest =>
      if letter ∈ seen then
        affineShiftThreeFirstOccurrencesFrom seen rest
      else
        letter ::
          affineShiftThreeFirstOccurrencesFrom (seen ++ [letter]) rest

theorem affineShiftThreeFirstOccurrencesFrom_mem_iff
    (seen : List Nat) (tested : Nat) :
    ∀ letters : List Nat,
      tested ∈ affineShiftThreeFirstOccurrencesFrom seen letters ↔
        tested ∈ letters ∧ tested ∉ seen
  | [] => by simp [affineShiftThreeFirstOccurrencesFrom]
  | letter :: rest => by
      by_cases present : letter ∈ seen
      · rw [affineShiftThreeFirstOccurrencesFrom, if_pos present,
          affineShiftThreeFirstOccurrencesFrom_mem_iff seen tested rest]
        constructor
        · rintro ⟨restMember, testedAbsent⟩
          exact ⟨List.Mem.tail letter restMember, testedAbsent⟩
        · intro data
          rcases data with ⟨inputMember, testedAbsent⟩
          rcases List.mem_cons.mp inputMember with equal | restMember
          · cases equal
            exact False.elim (testedAbsent present)
          · exact ⟨restMember, testedAbsent⟩
      · rw [affineShiftThreeFirstOccurrencesFrom, if_neg present]
        constructor
        · intro member
          rcases List.mem_cons.mp member with equal | tailMember
          · cases equal
            exact ⟨List.Mem.head rest, present⟩
          · have tailData :=
              (affineShiftThreeFirstOccurrencesFrom_mem_iff
                (seen ++ [letter]) tested rest).mp tailMember
            exact ⟨List.Mem.tail letter tailData.1, by
              intro testedSeen
              exact tailData.2 (List.mem_append_left _ testedSeen)⟩
        · intro data
          rcases data with ⟨inputMember, testedAbsent⟩
          rcases List.mem_cons.mp inputMember with equal | restMember
          · cases equal
            exact List.Mem.head _
          · by_cases equal : tested = letter
            · cases equal
              exact List.Mem.head _
            · exact List.Mem.tail letter <|
                (affineShiftThreeFirstOccurrencesFrom_mem_iff
                  (seen ++ [letter]) tested rest).mpr
                    ⟨restMember, by simp [testedAbsent, equal]⟩

theorem affineShiftThreeFirstOccurrencesFrom_nodup
    (seen : List Nat) :
    ∀ letters : List Nat,
      (affineShiftThreeFirstOccurrencesFrom seen letters).Nodup
  | [] => List.nodup_nil
  | letter :: rest => by
      by_cases present : letter ∈ seen
      · simpa [affineShiftThreeFirstOccurrencesFrom, present] using
          affineShiftThreeFirstOccurrencesFrom_nodup seen rest
      · rw [affineShiftThreeFirstOccurrencesFrom, if_neg present]
        apply List.nodup_cons.2
        constructor
        · intro member
          have data :=
            (affineShiftThreeFirstOccurrencesFrom_mem_iff
              (seen ++ [letter]) letter rest).mp member
          exact data.2 (by simp)
        · exact affineShiftThreeFirstOccurrencesFrom_nodup
            (seen ++ [letter]) rest

theorem affineShiftThreeFirstOccurrencesFrom_append
    (seen : List Nat) :
    ∀ left right : List Nat,
      affineShiftThreeFirstOccurrencesFrom seen (left ++ right) =
        affineShiftThreeFirstOccurrencesFrom seen left ++
          affineShiftThreeFirstOccurrencesFrom
            (seen ++ affineShiftThreeFirstOccurrencesFrom seen left) right
  | [], right => by simp [affineShiftThreeFirstOccurrencesFrom]
  | letter :: rest, right => by
      by_cases present : letter ∈ seen
      · simpa [affineShiftThreeFirstOccurrencesFrom, present] using
          affineShiftThreeFirstOccurrencesFrom_append seen rest right
      · simpa [affineShiftThreeFirstOccurrencesFrom, present,
          List.append_assoc] using
            affineShiftThreeFirstOccurrencesFrom_append
              (seen ++ [letter]) rest right

theorem affineShiftThreeFirstOccurrencesFrom_skip
    (seen : List Nat) :
    ∀ (skipped rest : List Nat),
      (∀ letter, letter ∈ skipped → letter ∈ seen) →
      affineShiftThreeFirstOccurrencesFrom seen (skipped ++ rest) =
        affineShiftThreeFirstOccurrencesFrom seen rest
  | [], rest, _ => rfl
  | letter :: skipped, rest, supported => by
      have headSeen := supported letter (List.Mem.head skipped)
      have tailSupported :
          ∀ next, next ∈ skipped → next ∈ seen := by
        intro next member
        exact supported next (List.Mem.tail letter member)
      simp [affineShiftThreeFirstOccurrencesFrom, headSeen,
        affineShiftThreeFirstOccurrencesFrom_skip
          seen skipped rest tailSupported]

/-- First occurrences in a possibly empty list. -/
def affineShiftThreeFirstOccurrenceOrderList
    (letters : List Nat) : List Nat :=
  affineShiftThreeFirstOccurrencesFrom [] letters

/-- The contract's first-occurrence order invariant. -/
def affineShiftThreeFirstOccurrenceOrder (word : Word Nat) : List Nat :=
  affineShiftThreeFirstOccurrenceOrderList word.toList

theorem affineShiftThreeFirstOccurrenceOrderList_nodup
    (letters : List Nat) :
    (affineShiftThreeFirstOccurrenceOrderList letters).Nodup :=
  affineShiftThreeFirstOccurrencesFrom_nodup [] letters

theorem affineShiftThreeFirstOccurrenceOrderList_mem_iff
    (tested : Nat) (letters : List Nat) :
    tested ∈ affineShiftThreeFirstOccurrenceOrderList letters ↔
      tested ∈ letters := by
  simpa [affineShiftThreeFirstOccurrenceOrderList] using
    affineShiftThreeFirstOccurrencesFrom_mem_iff [] tested letters

theorem affineShiftThreePrefixBeforeFirst_firstOccurrenceOrder
    (selected : Nat) {letters : List Nat}
    (member : selected ∈ letters) :
    affineShiftThreePrefixBeforeFirst selected
        (affineShiftThreeFirstOccurrenceOrderList letters) =
      affineShiftThreeFirstOccurrenceOrderList
        (affineShiftThreePrefixBeforeFirst selected letters) := by
  obtain ⟨suffix, split⟩ :=
    affineShiftThreePrefixBeforeFirst_split selected member
  let before := affineShiftThreePrefixBeforeFirst selected letters
  have selectedAbsent : selected ∉ before :=
    affineShiftThreePrefixBeforeFirst_avoids selected letters
  have selectedAbsentOrder :
      selected ∉ affineShiftThreeFirstOccurrenceOrderList before := by
    intro orderMember
    exact selectedAbsent <|
      (affineShiftThreeFirstOccurrenceOrderList_mem_iff
        selected before).mp orderMember
  have scanSplit :
      affineShiftThreeFirstOccurrenceOrderList letters =
        affineShiftThreeFirstOccurrenceOrderList before ++
          selected ::
            affineShiftThreeFirstOccurrencesFrom
              (affineShiftThreeFirstOccurrenceOrderList before ++
                [selected]) suffix := by
    rw [show letters = before ++ selected :: suffix by
      simpa [before] using split]
    unfold affineShiftThreeFirstOccurrenceOrderList
    rw [affineShiftThreeFirstOccurrencesFrom_append]
    simp only [List.nil_append]
    have selectedAbsentScan :
        selected ∉ affineShiftThreeFirstOccurrencesFrom [] before :=
      selectedAbsentOrder
    rw [affineShiftThreeFirstOccurrencesFrom,
      if_neg selectedAbsentScan]
  rw [scanSplit,
    affineShiftThreePrefixBeforeFirst_append_hit
      selected _ _ selectedAbsentOrder]

theorem affineShiftThreePrefixBeforeFirst_order_mem_iff
    (selected tested : Nat) {letters : List Nat}
    (member : selected ∈ letters) :
    tested ∈ affineShiftThreePrefixBeforeFirst selected
        (affineShiftThreeFirstOccurrenceOrderList letters) ↔
      tested ∈ affineShiftThreePrefixBeforeFirst selected letters := by
  rw [affineShiftThreePrefixBeforeFirst_firstOccurrenceOrder
      selected member,
    affineShiftThreeFirstOccurrenceOrderList_mem_iff]

private theorem affineShiftThreeTwoCopiesPerm
    (letter : Nat) (letters : List Nat)
    (count : letters.count letter = 2) :
    letters.Perm
      (letter :: letter :: (letters.erase letter).erase letter) := by
  have member : letter ∈ letters :=
    List.count_pos_iff.mp (by omega)
  have first := List.perm_cons_erase member
  have erasedCount : (letters.erase letter).count letter = 1 := by
    rw [List.count_erase_self, count]
  have erasedMember : letter ∈ letters.erase letter :=
    List.count_pos_iff.mp (by omega)
  exact first.trans
    (List.Perm.cons letter (List.perm_cons_erase erasedMember))

private theorem affineShiftThreeAddTriple
    (residue rest : Fin 3) :
    residue + (residue + (residue + rest)) = rest := by
  decide +revert

theorem affineShiftThreeResidueSum_ternaryReduce
    (residue : Nat → Fin 3) :
    ∀ letters : List Nat,
      affineShiftThreeResidueSum residue letters =
        affineShiftThreeResidueSum residue (ternaryReduce letters)
  | [] => rfl
  | letter :: rest => by
      simp only [ternaryReduce]
      split <;> rename_i reducedCount
      · simp only [affineShiftThreeResidueSum]
        rw [affineShiftThreeResidueSum_ternaryReduce residue rest]
      · have reducedLt : (ternaryReduce rest).count letter < 3 := by
          rw [count_ternaryReduce]
          exact Nat.mod_lt _ (by decide)
        have reducedEq : (ternaryReduce rest).count letter = 2 := by
          omega
        let remainder :=
          ((ternaryReduce rest).erase letter).erase letter
        have permutation :
            (ternaryReduce rest).Perm
              (letter :: letter :: remainder) := by
          exact affineShiftThreeTwoCopiesPerm
            letter (ternaryReduce rest) reducedEq
        calc
          affineShiftThreeResidueSum residue (letter :: rest) =
              residue letter +
                affineShiftThreeResidueSum residue rest := rfl
          _ = residue letter +
                affineShiftThreeResidueSum residue
                  (ternaryReduce rest) := by
              rw [affineShiftThreeResidueSum_ternaryReduce residue rest]
          _ = residue letter +
                affineShiftThreeResidueSum residue
                  (letter :: letter :: remainder) := by
              rw [affineShiftThreeResidueSum_perm residue permutation]
          _ = affineShiftThreeResidueSum residue remainder := by
              simpa [affineShiftThreeResidueSum] using
                affineShiftThreeAddTriple (residue letter)
                  (affineShiftThreeResidueSum residue remainder)

/-- Coordinatewise modulo-three counts determine every weighted residue sum. -/
theorem affineShiftThreeResidueSum_eq_of_countResidue_eq
    (residue : Nat → Fin 3) (left right : List Nat)
    (sameCounts : ∀ tested,
      affineShiftThreeCountResidue tested left =
        affineShiftThreeCountResidue tested right) :
    affineShiftThreeResidueSum residue left =
      affineShiftThreeResidueSum residue right := by
  have sameMod :
      ∀ tested, left.count tested % 3 = right.count tested % 3 := by
    intro tested
    have equalValues := congrArg Fin.val (sameCounts tested)
    rw [affineShiftThreeCountResidue_eq_natResidue,
      affineShiftThreeCountResidue_eq_natResidue] at equalValues
    exact equalValues
  have permutation :
      (ternaryReduce left).Perm (ternaryReduce right) :=
    ternaryReduce_perm_of_mod_eq sameMod
  calc
    affineShiftThreeResidueSum residue left =
        affineShiftThreeResidueSum residue (ternaryReduce left) :=
      affineShiftThreeResidueSum_ternaryReduce residue left
    _ = affineShiftThreeResidueSum residue (ternaryReduce right) :=
      affineShiftThreeResidueSum_perm residue permutation
    _ = affineShiftThreeResidueSum residue right :=
      (affineShiftThreeResidueSum_ternaryReduce residue right).symm

/-- The contract's total exponent residue for one tested variable. -/
def affineShiftThreeWordTotalResidue
    (tested : Nat) (word : Word Nat) : Fin 3 :=
  affineShiftThreeCountResidue tested word.toList

/-- The contract's prefix residue: occurrences of `tested` strictly before
the first occurrence of `selected`, modulo three. -/
def affineShiftThreeWordPrefixResidue
    (selected tested : Nat) (word : Word Nat) : Fin 3 :=
  affineShiftThreeCountResidue tested
    (affineShiftThreePrefixBeforeFirst selected word.toList)

/-- The unit residue of a valuation entry. The value is used only on entries
whose classification is a unit. -/
def affineShiftThreeUnitPart
    (valuation : Nat → Fin 6) (letter : Nat) : Fin 3 :=
  match affineShiftThreeClassify (valuation letter) with
  | .unit residue => residue
  | .ideal _ => 0

/-- The first ideal-valued letter and its ideal residue, if one occurs. -/
def affineShiftThreeFirstIdeal
    (valuation : Nat → Fin 6) : List Nat → Option (Nat × Fin 3)
  | [] => none
  | letter :: rest =>
      match affineShiftThreeClassify (valuation letter) with
      | .unit _ => affineShiftThreeFirstIdeal valuation rest
      | .ideal residue => some (letter, residue)

private theorem affineShiftThreeValuation_eq_unit_of_classify
    (valuation : Nat → Fin 6) (letter : Nat) (residue : Fin 3)
    (classified :
      affineShiftThreeClassify (valuation letter) =
        AffineShiftThreeValue.unit residue) :
    valuation letter = affineShiftThreeUnitResidue residue := by
  have reconstructed :=
    affineShiftThreeReconstruct_classify (valuation letter)
  rw [classified] at reconstructed
  exact reconstructed.symm

private theorem affineShiftThreeValuation_eq_ideal_of_classify
    (valuation : Nat → Fin 6) (letter : Nat) (residue : Fin 3)
    (classified :
      affineShiftThreeClassify (valuation letter) =
        AffineShiftThreeValue.ideal residue) :
    valuation letter = affineShiftThreeIdealResidue residue := by
  have reconstructed :=
    affineShiftThreeReconstruct_classify (valuation letter)
  rw [classified] at reconstructed
  exact reconstructed.symm

theorem affineShiftThreeFirstIdeal_some_classify
    (valuation : Nat → Fin 6) :
    ∀ (letters : List Nat) {letter : Nat} {residue : Fin 3},
      affineShiftThreeFirstIdeal valuation letters =
          some (letter, residue) →
        affineShiftThreeClassify (valuation letter) =
          AffineShiftThreeValue.ideal residue
  | [], _, _, equal => by simp [affineShiftThreeFirstIdeal] at equal
  | head :: rest, letter, residue, equal => by
      cases classified : affineShiftThreeClassify (valuation head) with
      | unit headResidue =>
          apply affineShiftThreeFirstIdeal_some_classify valuation rest
          simpa [affineShiftThreeFirstIdeal, classified] using equal
      | ideal headResidue =>
          have pairEqual : (head, headResidue) = (letter, residue) := by
            exact Option.some.inj <| by
              simpa [affineShiftThreeFirstIdeal, classified] using equal
          have headEqual : head = letter := congrArg Prod.fst pairEqual
          have residueEqual : headResidue = residue :=
            congrArg Prod.snd pairEqual
          cases headEqual
          cases residueEqual
          exact classified

/-- Arbitrary evaluation is read from the first ideal hit, or from the total
unit residue when there is no ideal hit. -/
theorem affineShiftThreeEvalList_firstIdeal_formula
    (valuation : Nat → Fin 6) :
    ∀ letters : List Nat,
      affineShiftThreeEvalList valuation letters =
        match affineShiftThreeFirstIdeal valuation letters with
        | none =>
            affineShiftThreeUnitResidue
              (affineShiftThreeResidueSum
                (affineShiftThreeUnitPart valuation) letters)
        | some (selected, idealResidue) =>
            affineShiftThreeIdealResidue
              (affineShiftThreeResidueSum
                  (affineShiftThreeUnitPart valuation)
                  (affineShiftThreePrefixBeforeFirst selected letters) +
                idealResidue)
  | [] => rfl
  | letter :: rest => by
      cases classified : affineShiftThreeClassify (valuation letter) with
      | unit unitResidue =>
          have valueEq :=
            affineShiftThreeValuation_eq_unit_of_classify
              valuation letter unitResidue classified
          cases firstRest : affineShiftThreeFirstIdeal valuation rest with
          | none =>
              rw [affineShiftThreeEvalList_cons, valueEq,
                affineShiftThreeEvalList_firstIdeal_formula valuation rest,
                firstRest, affineShiftThreeMul_unitResidues]
              simp [affineShiftThreeFirstIdeal, classified, firstRest,
                affineShiftThreeResidueSum, affineShiftThreeUnitPart]
          | some hit =>
              rcases hit with ⟨selected, idealResidue⟩
              have selectedClassified :=
                affineShiftThreeFirstIdeal_some_classify
                  valuation rest firstRest
              have different : letter ≠ selected := by
                intro equal
                subst selected
                rw [classified] at selectedClassified
                cases selectedClassified
              rw [affineShiftThreeEvalList_cons, valueEq,
                affineShiftThreeEvalList_firstIdeal_formula valuation rest,
                firstRest, affineShiftThreeMul_unit_ideal]
              simpa only [affineShiftThreeFirstIdeal, classified, firstRest,
                affineShiftThreePrefixBeforeFirst, if_neg different,
                affineShiftThreeResidueSum, affineShiftThreeUnitPart] using
                congrArg affineShiftThreeIdealResidue
                  (affineShiftThreeAdd_assoc unitResidue
                    (affineShiftThreeResidueSum
                      (affineShiftThreeUnitPart valuation)
                      (affineShiftThreePrefixBeforeFirst selected rest))
                    idealResidue)
      | ideal idealResidue =>
          have valueEq :=
            affineShiftThreeValuation_eq_ideal_of_classify
              valuation letter idealResidue classified
          rw [affineShiftThreeEvalList_cons, valueEq,
            affineShiftThreeMul_ideal_left]
          simp [affineShiftThreeFirstIdeal, classified,
            affineShiftThreePrefixBeforeFirst,
            affineShiftThreeResidueSum]

private theorem affineShiftThreeFirstIdeal_firstOccurrencesFrom
    (valuation : Nat → Fin 6) :
    ∀ (seen letters : List Nat),
      (∀ letter, letter ∈ seen →
        ∃ residue,
          affineShiftThreeClassify (valuation letter) =
            AffineShiftThreeValue.unit residue) →
      affineShiftThreeFirstIdeal valuation
          (affineShiftThreeFirstOccurrencesFrom seen letters) =
        affineShiftThreeFirstIdeal valuation letters
  | seen, [], _ => rfl
  | seen, letter :: rest, seenUnits => by
      by_cases present : letter ∈ seen
      · obtain ⟨residue, classified⟩ := seenUnits letter present
        rw [affineShiftThreeFirstOccurrencesFrom, if_pos present]
        simp only [affineShiftThreeFirstIdeal, classified]
        exact affineShiftThreeFirstIdeal_firstOccurrencesFrom
          valuation seen rest seenUnits
      · cases classified : affineShiftThreeClassify (valuation letter) with
        | ideal residue =>
            simp [affineShiftThreeFirstOccurrencesFrom, present,
              affineShiftThreeFirstIdeal, classified]
        | unit residue =>
            rw [affineShiftThreeFirstOccurrencesFrom, if_neg present]
            simp only [affineShiftThreeFirstIdeal, classified]
            apply affineShiftThreeFirstIdeal_firstOccurrencesFrom
              valuation (seen ++ [letter]) rest
            intro tested testedMember
            rcases List.mem_append.mp testedMember with oldMember | newMember
            · exact seenUnits tested oldMember
            · simp only [List.mem_singleton] at newMember
              subst tested
              exact ⟨residue, classified⟩

theorem affineShiftThreeFirstIdeal_firstOccurrenceOrder
    (valuation : Nat → Fin 6) (letters : List Nat) :
    affineShiftThreeFirstIdeal valuation
        (affineShiftThreeFirstOccurrenceOrderList letters) =
      affineShiftThreeFirstIdeal valuation letters := by
  apply affineShiftThreeFirstIdeal_firstOccurrencesFrom valuation [] letters
  intro letter member
  simp at member

/-- The complete first-order/prefix/total invariant determines evaluation for
every valuation, not only for the separating valuations. -/
theorem affineShiftThreeEvalList_eq_of_invariants
    (left right : List Nat)
    (sameOrder :
      affineShiftThreeFirstOccurrenceOrderList left =
        affineShiftThreeFirstOccurrenceOrderList right)
    (sameTotal : ∀ tested,
      affineShiftThreeCountResidue tested left =
        affineShiftThreeCountResidue tested right)
    (samePrefix : ∀ selected tested,
      affineShiftThreeCountResidue tested
          (affineShiftThreePrefixBeforeFirst selected left) =
        affineShiftThreeCountResidue tested
          (affineShiftThreePrefixBeforeFirst selected right))
    (valuation : Nat → Fin 6) :
    affineShiftThreeEvalList valuation left =
      affineShiftThreeEvalList valuation right := by
  have sameFirstIdeal :
      affineShiftThreeFirstIdeal valuation left =
        affineShiftThreeFirstIdeal valuation right := by
    calc
      affineShiftThreeFirstIdeal valuation left =
          affineShiftThreeFirstIdeal valuation
            (affineShiftThreeFirstOccurrenceOrderList left) :=
        (affineShiftThreeFirstIdeal_firstOccurrenceOrder
          valuation left).symm
      _ = affineShiftThreeFirstIdeal valuation
            (affineShiftThreeFirstOccurrenceOrderList right) := by
        rw [sameOrder]
      _ = affineShiftThreeFirstIdeal valuation right :=
        affineShiftThreeFirstIdeal_firstOccurrenceOrder valuation right
  cases first : affineShiftThreeFirstIdeal valuation left with
  | none =>
      have second : affineShiftThreeFirstIdeal valuation right = none := by
        rw [← sameFirstIdeal, first]
      rw [affineShiftThreeEvalList_firstIdeal_formula,
        affineShiftThreeEvalList_firstIdeal_formula, first, second]
      exact congrArg affineShiftThreeUnitResidue <|
        affineShiftThreeResidueSum_eq_of_countResidue_eq
          (affineShiftThreeUnitPart valuation) left right sameTotal
  | some hit =>
      rcases hit with ⟨selected, idealResidue⟩
      have second :
          affineShiftThreeFirstIdeal valuation right =
            some (selected, idealResidue) := by
        rw [← sameFirstIdeal, first]
      rw [affineShiftThreeEvalList_firstIdeal_formula,
        affineShiftThreeEvalList_firstIdeal_formula, first, second]
      exact congrArg
        (fun residue =>
          affineShiftThreeIdealResidue (residue + idealResidue)) <|
        affineShiftThreeResidueSum_eq_of_countResidue_eq
          (affineShiftThreeUnitPart valuation)
          (affineShiftThreePrefixBeforeFirst selected left)
          (affineShiftThreePrefixBeforeFirst selected right)
          (samePrefix selected)

theorem affineShiftThreeEval_eq_of_invariants
    (left right : Word Nat)
    (sameOrder :
      affineShiftThreeFirstOccurrenceOrder left =
        affineShiftThreeFirstOccurrenceOrder right)
    (sameTotal : ∀ tested,
      affineShiftThreeWordTotalResidue tested left =
        affineShiftThreeWordTotalResidue tested right)
    (samePrefix : ∀ selected tested,
      affineShiftThreeWordPrefixResidue selected tested left =
        affineShiftThreeWordPrefixResidue selected tested right)
    (valuation : Nat → Fin 6) :
    affineShiftThree.semigroup.eval valuation left =
      affineShiftThree.semigroup.eval valuation right := by
  rw [affineShiftThreeEval_eq_evalList,
    affineShiftThreeEval_eq_evalList]
  apply affineShiftThreeEvalList_eq_of_invariants
    left.toList right.toList sameOrder sameTotal samePrefix valuation

/-- All variables are units; only the tested variable contributes the cyclic
generator. -/
def affineShiftThreeTotalValuation (tested : Nat) : Nat → Fin 6 :=
  fun letter =>
    affineShiftThreeUnitResidue
      (if letter = tested then 1 else 0)

/-- The selected variable is ideal-valued, the tested variable contributes
one unit residue, and every other variable is the identity. -/
def affineShiftThreePrefixValuation
    (selected tested : Nat) : Nat → Fin 6 :=
  fun letter =>
    if letter = selected then affineShiftThreeIdealResidue 0
    else
      affineShiftThreeUnitResidue
        (if letter = tested then 1 else 0)

theorem affineShiftThreeEvalList_totalValuation
    (tested : Nat) (letters : List Nat) :
    affineShiftThreeEvalList
        (affineShiftThreeTotalValuation tested) letters =
      affineShiftThreeUnitResidue
        (affineShiftThreeCountResidue tested letters) := by
  simpa [affineShiftThreeTotalValuation,
    affineShiftThreeCountResidue] using
      affineShiftThreeEvalList_allUnits
        (fun letter : Nat => if letter = tested then 1 else 0) letters

theorem affineShiftThreeEvalList_prefixValuation_of_mem
    (selected tested : Nat) {letters : List Nat}
    (member : selected ∈ letters) :
    affineShiftThreeEvalList
        (affineShiftThreePrefixValuation selected tested) letters =
      affineShiftThreeIdealResidue
        (affineShiftThreeCountResidue tested
          (affineShiftThreePrefixBeforeFirst selected letters)) := by
  obtain ⟨suffix, split⟩ :=
    affineShiftThreePrefixBeforeFirst_split selected member
  have evaluated :=
    affineShiftThreeEvalList_firstIdeal
      (affineShiftThreePrefixValuation selected tested)
      (fun letter : Nat => if letter = tested then 1 else 0)
      (affineShiftThreePrefixBeforeFirst selected letters)
      selected suffix 0 (by
        intro letter prefixMember
        have different : letter ≠ selected := by
          intro equal
          subst letter
          exact
            (affineShiftThreePrefixBeforeFirst_avoids selected letters)
              prefixMember
        simp [affineShiftThreePrefixValuation, different]) (by
          simp [affineShiftThreePrefixValuation])
  calc
    affineShiftThreeEvalList
        (affineShiftThreePrefixValuation selected tested) letters =
        affineShiftThreeEvalList
          (affineShiftThreePrefixValuation selected tested)
          (affineShiftThreePrefixBeforeFirst selected letters ++
            selected :: suffix) :=
      congrArg
        (affineShiftThreeEvalList
          (affineShiftThreePrefixValuation selected tested)) split
    _ = affineShiftThreeIdealResidue
          (affineShiftThreeCountResidue tested
            (affineShiftThreePrefixBeforeFirst selected letters)) := by
      simpa [affineShiftThreeCountResidue] using evaluated

theorem affineShiftThreeEvalList_prefixValuation_of_not_mem
    (selected tested : Nat) {letters : List Nat}
    (absent : selected ∉ letters) :
    affineShiftThreeEvalList
        (affineShiftThreePrefixValuation selected tested) letters =
      affineShiftThreeUnitResidue
        (affineShiftThreeCountResidue tested letters) := by
  simpa [affineShiftThreeCountResidue] using
    affineShiftThreeEvalList_allUnits_of
      (affineShiftThreePrefixValuation selected tested)
      (fun letter : Nat => if letter = tested then 1 else 0)
      letters (by
        intro letter member
        have different : letter ≠ selected := by
          intro equal
          subst letter
          exact absent member
        simp [affineShiftThreePrefixValuation, different])

/-- The specialized first-hit valuation exposes the prefix residue when the
selected variable occurs, and stays in the unit group otherwise. -/
theorem affineShiftThreeEvalList_prefixValuation
    (selected tested : Nat) (letters : List Nat) :
    affineShiftThreeEvalList
        (affineShiftThreePrefixValuation selected tested) letters =
      if selected ∈ letters then
        affineShiftThreeIdealResidue
          (affineShiftThreeCountResidue tested
            (affineShiftThreePrefixBeforeFirst selected letters))
      else
        affineShiftThreeUnitResidue
          (affineShiftThreeCountResidue tested letters) := by
  by_cases member : selected ∈ letters
  · simp [member,
      affineShiftThreeEvalList_prefixValuation_of_mem
        selected tested member]
  · simp [member,
      affineShiftThreeEvalList_prefixValuation_of_not_mem
        selected tested member]

/-- Equal term functions have equal total occurrence residues for every
variable. -/
theorem affineShiftThreeEqualEval_wordTotalResidue
    (left right : Word Nat)
    (equalEval :
      ∀ valuation : Nat → Fin 6,
        affineShiftThree.semigroup.eval valuation left =
          affineShiftThree.semigroup.eval valuation right)
    (tested : Nat) :
    affineShiftThreeWordTotalResidue tested left =
      affineShiftThreeWordTotalResidue tested right := by
  have evaluated := equalEval (affineShiftThreeTotalValuation tested)
  rw [affineShiftThreeEval_eq_evalList,
    affineShiftThreeEval_eq_evalList,
    affineShiftThreeEvalList_totalValuation,
    affineShiftThreeEvalList_totalValuation] at evaluated
  exact affineShiftThreeUnitResidue_injective evaluated

/-- Equal term functions have the same variable support. -/
theorem affineShiftThreeEqualEval_mem_iff
    (left right : Word Nat)
    (equalEval :
      ∀ valuation : Nat → Fin 6,
        affineShiftThree.semigroup.eval valuation left =
          affineShiftThree.semigroup.eval valuation right)
    (selected : Nat) :
    selected ∈ left.toList ↔ selected ∈ right.toList := by
  constructor
  · intro leftMember
    by_cases rightMember : selected ∈ right.toList
    · exact rightMember
    · exact False.elim <| by
        have evaluated :=
          equalEval (affineShiftThreePrefixValuation selected selected)
        rw [affineShiftThreeEval_eq_evalList,
          affineShiftThreeEval_eq_evalList,
          affineShiftThreeEvalList_prefixValuation_of_mem
            selected selected leftMember,
          affineShiftThreeEvalList_prefixValuation_of_not_mem
            selected selected rightMember] at evaluated
        exact affineShiftThreeUnitResidue_ne_idealResidue _ _
          evaluated.symm
  · intro rightMember
    by_cases leftMember : selected ∈ left.toList
    · exact leftMember
    · exact False.elim <| by
        have evaluated :=
          equalEval (affineShiftThreePrefixValuation selected selected)
        rw [affineShiftThreeEval_eq_evalList,
          affineShiftThreeEval_eq_evalList,
          affineShiftThreeEvalList_prefixValuation_of_not_mem
            selected selected leftMember,
          affineShiftThreeEvalList_prefixValuation_of_mem
            selected selected rightMember] at evaluated
        exact affineShiftThreeUnitResidue_ne_idealResidue _ _ evaluated

/-- Equal term functions have equal first-hit prefix residues for every
ordered pair of variables. This also covers an absent selected variable, when
the prefix is the entire word. -/
theorem affineShiftThreeEqualEval_wordPrefixResidue
    (left right : Word Nat)
    (equalEval :
      ∀ valuation : Nat → Fin 6,
        affineShiftThree.semigroup.eval valuation left =
          affineShiftThree.semigroup.eval valuation right)
    (selected tested : Nat) :
    affineShiftThreeWordPrefixResidue selected tested left =
      affineShiftThreeWordPrefixResidue selected tested right := by
  have sameSupport :=
    affineShiftThreeEqualEval_mem_iff left right equalEval selected
  by_cases leftMember : selected ∈ left.toList
  · have rightMember : selected ∈ right.toList :=
      sameSupport.mp leftMember
    have evaluated :=
      equalEval (affineShiftThreePrefixValuation selected tested)
    rw [affineShiftThreeEval_eq_evalList,
      affineShiftThreeEval_eq_evalList,
      affineShiftThreeEvalList_prefixValuation_of_mem
        selected tested leftMember,
      affineShiftThreeEvalList_prefixValuation_of_mem
        selected tested rightMember] at evaluated
    exact affineShiftThreeIdealResidue_injective evaluated
  · have rightAbsent : selected ∉ right.toList := by
      intro rightMember
      exact leftMember (sameSupport.mpr rightMember)
    unfold affineShiftThreeWordPrefixResidue
    rw [affineShiftThreePrefixBeforeFirst_eq_self_of_not_mem
        selected left.toList leftMember,
      affineShiftThreePrefixBeforeFirst_eq_self_of_not_mem
        selected right.toList rightAbsent]
    exact
      affineShiftThreeEqualEval_wordTotalResidue
        left right equalEval tested

end SemigroupBasis.Examples
