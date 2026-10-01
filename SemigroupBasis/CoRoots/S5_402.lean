import SemigroupBasis.CoRoots.S5_107BlockCombinatorics
import SemigroupBasis.Examples.CommutativeExponentThree
import SemigroupBasis.Examples.LeftZeroTwo
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder5Part04
import SemigroupBasis.Opposite
import SemigroupBasis.Transfer

namespace SemigroupBasis.CoRoots.S5_402

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xyx : Word Nat := w 0 [1, 0]
def xxyx : Word Nat := w 0 [0, 1, 0]
def xyxx : Word Nat := w 0 [1, 0, 0]
def xxyy : Word Nat := w 0 [0, 1, 1]
def xyxy : Word Nat := w 0 [1, 0, 1]
def xyyx : Word Nat := w 0 [1, 1, 0]
def xxyzy : Word Nat := w 0 [0, 1, 2, 1]
def xxzyy : Word Nat := w 0 [0, 2, 1, 1]
def xyxzy : Word Nat := w 0 [1, 0, 2, 1]
def xyzyx : Word Nat := w 0 [1, 2, 1, 0]
def xzyxy : Word Nat := w 0 [2, 1, 0, 1]
def xzyyx : Word Nat := w 0 [2, 1, 1, 0]
def xyxzx : Word Nat := w 0 [1, 0, 2, 0]
def xzxyx : Word Nat := w 0 [2, 0, 1, 0]
def xyxzz : Word Nat := w 0 [1, 0, 2, 2]
def xzyxz : Word Nat := w 0 [2, 1, 0, 2]
def xzzyx : Word Nat := w 0 [2, 2, 1, 0]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def leftDuplicationLaw : Identity Nat := ⟨xyx, xxyx⟩
def rightDuplicationLaw : Identity Nat := ⟨xyx, xyxx⟩
def squareAlternationLaw : Identity Nat := ⟨xxyy, xyxy⟩
def squareCrossingLaw : Identity Nat := ⟨xxyy, xyyx⟩
def factorLeftLaw : Identity Nat := ⟨xxyzy, xxzyy⟩
def factorMiddleLeftLaw : Identity Nat := ⟨xxyzy, xyxzy⟩
def factorMiddleRightLaw : Identity Nat := ⟨xxyzy, xyzyx⟩
def factorSwapLaw : Identity Nat := ⟨xxyzy, xzyxy⟩
def factorRightLaw : Identity Nat := ⟨xxyzy, xzyyx⟩
def simpleBlockSwapLaw : Identity Nat := ⟨xyxzx, xzxyx⟩
def successorShiftLaw : Identity Nat := ⟨xyxzz, xzyxz⟩
def successorReverseLaw : Identity Nat := ⟨xyxzz, xzzyx⟩

/-- The exact ordered thirteen-law basis recorded for catalogue class
`S5_402`. This foundation source asserts necessary invariants and finite
derivations only. -/
def basis : List (Identity Nat) :=
  [powerLaw, leftDuplicationLaw, rightDuplicationLaw,
    squareAlternationLaw, squareCrossingLaw, factorLeftLaw,
    factorMiddleLeftLaw, factorMiddleRightLaw, factorSwapLaw,
    factorRightLaw, simpleBlockSwapLaw, successorShiftLaw,
    successorReverseLaw]

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

def finiteBasis : List (Identity (Fin 3)) :=
  basis.map fun identity => identity.map toFinThree

private theorem basis_roundTrip_checked :
    basis.all (fun identity =>
      decide ((identity.map toFinThree).map Fin.val = identity)) = true := by
  decide

private theorem basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ basis) :
    (identity.map toFinThree).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basis_roundTrip_checked) identity member

/-- Exhaustive checks on the three displayed variables lift to
natural-number variables. This theorem does not assert completeness. -/
theorem models_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteBasis.all candidate.checkIdentity = true) :
    Models candidate.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinThree ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityNat_sound (identity.map toFinThree)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [basis_roundTrip identity member] at finiteValid
  exact finiteValid

abbrev table : FiniteTable :=
  Generated.Catalogue.S5_402.table

set_option maxRecDepth 100000 in
/-- The direct Smallsemi representative satisfies the thirteen recorded
laws. -/
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide)

/-- The opposite representative satisfies the literal reversed laws. -/
theorem oppositeModels :
    Models table.semigroup.opposite oppositeBasis :=
  models.oppositeReversed

/-- The copy on one-based target elements `[1,3,4]` is `S3_8`, the
commutative exponent-three factor that detects multiplicity capped at two. -/
def multiplicityEmbedding :
    Embedding Examples.commutativeExponentThree.semigroup table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨2, by decide⟩ else ⟨3, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

/-- The copy on one-based target elements `[4,5]` is the two-element
left-zero semigroup and therefore detects the exact head variable. -/
def headEmbedding :
    Embedding Examples.leftZeroTwo.semigroup table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨3, by decide⟩ else ⟨4, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

theorem valid_exponentThree (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy Examples.commutativeExponentThree.semigroup :=
  multiplicityEmbedding.pullback_identity identity valid

theorem valid_leftZeroTwo (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy Examples.leftZeroTwo.semigroup :=
  headEmbedding.pullback_identity identity valid

abbrev cappedMultiplicity := S5_107.cappedMultiplicity

/-- Extensional support agreement. -/
def SameSupport (left right : Word Nat) : Prop :=
  ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList

abbrev GloballySimple := S5_107.SimpleIn

/-- A globally simple source followed immediately by `target`. The explicit
inequality makes the impossible self-successor case structural. -/
def ImmediateSuccessor
    (word : Word Nat) (source target : Nat) : Prop :=
  source ≠ target ∧ GloballySimple word source ∧
    (source, target) ∈ word.adjacentPairs

def SameGloballySimpleVariables (left right : Word Nat) : Prop :=
  ∀ letter, GloballySimple left letter ↔ GloballySimple right letter

def SameImmediateSuccessors (left right : Word Nat) : Prop :=
  ∀ source target,
    ImmediateSuccessor left source target ↔
      ImmediateSuccessor right source target

/-- The necessary S5_402 signature. No theorem below asserts that this
signature is sufficient for derivability. -/
structure SameSimpleSuccessorSignature
    (left right : Word Nat) : Prop where
  capped :
    ∀ letter,
      cappedMultiplicity left letter = cappedMultiplicity right letter
  support : SameSupport left right
  head : left.head = right.head
  globallySimple : SameGloballySimpleVariables left right
  successor : SameImmediateSuccessors left right

theorem valid_cappedMultiplicity
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ letter,
      cappedMultiplicity identity.lhs letter =
        cappedMultiplicity identity.rhs letter := by
  intro letter
  simpa [cappedMultiplicity, S5_107.cappedMultiplicity, Nat.min_comm] using
    Examples.exponentValid_capped_count_eq identity
      (valid_exponentThree identity valid) letter

private theorem sameSupport_of_capped
    (left right : Word Nat)
    (capped :
      ∀ letter,
        cappedMultiplicity left letter = cappedMultiplicity right letter) :
    SameSupport left right := by
  intro letter
  have cappedEq :
      S5_107.cappedMultiplicity left letter =
        S5_107.cappedMultiplicity right letter :=
    capped letter
  have absent : letter ∉ left.toList ↔ letter ∉ right.toList := by
    rw [← List.count_eq_zero, ← List.count_eq_zero,
      ← S5_107.cappedMultiplicity_eq_zero_iff,
      ← S5_107.cappedMultiplicity_eq_zero_iff, cappedEq]
  simpa using not_congr absent

private theorem sameGloballySimple_of_capped
    (left right : Word Nat)
    (capped :
      ∀ letter,
        cappedMultiplicity left letter = cappedMultiplicity right letter) :
    SameGloballySimpleVariables left right := by
  intro letter
  have cappedEq :
      S5_107.cappedMultiplicity left letter =
        S5_107.cappedMultiplicity right letter :=
    capped letter
  constructor
  · intro leftSimple
    apply (S5_107.cappedMultiplicity_eq_one_iff right letter).1
    rw [← cappedEq]
    exact
      (S5_107.cappedMultiplicity_eq_one_iff left letter).2 leftSimple
  · intro rightSimple
    apply (S5_107.cappedMultiplicity_eq_one_iff left letter).1
    rw [cappedEq]
    exact
      (S5_107.cappedMultiplicity_eq_one_iff right letter).2 rightSimple

theorem valid_head (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  have pulled := valid_leftZeroTwo identity valid
  apply Decidable.byContradiction
  intro headsNe
  let valuation : Nat → Fin 2 :=
    fun letter => if letter = identity.lhs.head then 0 else 1
  have evaluated := pulled valuation
  rw [Examples.leftZeroTwo_eval, Examples.leftZeroTwo_eval] at evaluated
  simp [valuation, Ne.symm headsNe] at evaluated

/-- Send the simple source to one-based element `2`, the tested successor to
one-based element `4`, and every other variable to one-based element `5`. -/
def successorMarker (source target : Nat) : Nat → Fin 5 :=
  fun letter =>
    if letter = source then 1
    else if letter = target then 3
    else 4

@[simp]
private theorem successorMarker_source (source target : Nat) :
    successorMarker source target source = 1 := by
  simp [successorMarker]

private theorem successorMarker_target
    {source target : Nat} (different : source ≠ target) :
    successorMarker source target target = 3 := by
  simp [successorMarker, Ne.symm different]

private def listEvalStep
    (G : Semigroup (Fin 5)) :
    Option (Fin 5) → Fin 5 → Option (Fin 5)
  | none, next => some next
  | some current, next => some (G.mul current next)

private def listEvalFrom
    (G : Semigroup (Fin 5))
    (initial : Option (Fin 5)) (valuation : Nat → Fin 5)
    (letters : List Nat) : Option (Fin 5) :=
  letters.foldl
    (fun current letter =>
      listEvalStep G current (valuation letter))
    initial

@[simp]
private theorem listEvalFrom_nil
    (G : Semigroup (Fin 5))
    (initial : Option (Fin 5)) (valuation : Nat → Fin 5) :
    listEvalFrom G initial valuation [] = initial :=
  rfl

@[simp]
private theorem listEvalFrom_cons
    (G : Semigroup (Fin 5))
    (initial : Option (Fin 5)) (valuation : Nat → Fin 5)
    (first : Nat) (rest : List Nat) :
    listEvalFrom G initial valuation (first :: rest) =
      listEvalFrom G
        (listEvalStep G initial (valuation first)) valuation rest :=
  rfl

private theorem listEvalFrom_append
    (G : Semigroup (Fin 5))
    (initial : Option (Fin 5)) (valuation : Nat → Fin 5)
    (left right : List Nat) :
    listEvalFrom G initial valuation (left ++ right) =
      listEvalFrom G
        (listEvalFrom G initial valuation left) valuation right := by
  simp [listEvalFrom, List.foldl_append]

private theorem listEvalFrom_some
    (G : Semigroup (Fin 5))
    (initial : Fin 5) (valuation : Nat → Fin 5)
    (letters : List Nat) :
    listEvalFrom G (some initial) valuation letters =
      some
        (letters.foldl
          (fun current letter => G.mul current (valuation letter))
          initial) := by
  induction letters generalizing initial with
  | nil => rfl
  | cons first rest ih =>
      rw [listEvalFrom_cons]
      simp only [listEvalStep, List.foldl_cons]
      exact ih (G.mul initial (valuation first))

private theorem listEvalFrom_toList
    (valuation : Nat → Fin 5) (word : Word Nat) :
    listEvalFrom table.semigroup none valuation word.toList =
      some (table.semigroup.eval valuation word) := by
  cases word with
  | mk head tail =>
      simp only [Word.toList, listEvalFrom_cons, listEvalStep,
        Semigroup.eval]
      exact listEvalFrom_some table.semigroup (valuation head) valuation tail

private theorem listEvalFrom_sourceFree_fixed
    {source target : Nat} (different : source ≠ target)
    (state : Fin 5)
    (stateThree : table.semigroup.mul state (3 : Fin 5) = state)
    (stateFour : table.semigroup.mul state (4 : Fin 5) = state)
    {letters : List Nat} (sourceFree : source ∉ letters) :
    listEvalFrom table.semigroup (some state)
        (successorMarker source target) letters = some state := by
  induction letters with
  | nil => rfl
  | cons first rest ih =>
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
        rw [successorMarker_target different]
        simp only [listEvalStep, stateThree]
        exact ih restFree
      · rw [show successorMarker source target first = 4 by
          simp [successorMarker, firstNe, firstTarget]]
        simp only [listEvalStep, stateFour]
        exact ih restFree

private theorem listEvalFrom_none_sourceFree_cons
    {source target first : Nat} (different : source ≠ target)
    {rest : List Nat} (sourceFree : source ∉ first :: rest) :
    listEvalFrom table.semigroup none
        (successorMarker source target) (first :: rest) =
      some (successorMarker source target first) := by
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
    rw [successorMarker_target different]
    exact listEvalFrom_sourceFree_fixed different 3 (by decide) (by decide)
      restFree
  · rw [show successorMarker source target first = 4 by
      simp [successorMarker, firstNe, firstTarget]]
    exact listEvalFrom_sourceFree_fixed different 4 (by decide) (by decide)
      restFree

private theorem listEval_prefix_source
    {source target : Nat} (different : source ≠ target)
    (before after : List Nat) (beforeFree : source ∉ before) :
    listEvalFrom table.semigroup none
        (successorMarker source target)
        (before ++ source :: after) =
      listEvalFrom table.semigroup (some 1)
        (successorMarker source target) after := by
  rw [listEvalFrom_append]
  cases before with
  | nil =>
      simp [listEvalStep]
  | cons first rest =>
      have fullFree : source ∉ first :: rest := beforeFree
      rw [listEvalFrom_none_sourceFree_cons different fullFree]
      rw [listEvalFrom_cons, successorMarker_source]
      by_cases firstTarget : first = target
      · subst first
        rw [successorMarker_target different]
        simp only [listEvalStep]
        rw [show table.semigroup.mul (3 : Fin 5) (1 : Fin 5) =
            (1 : Fin 5) by decide]
      · have firstNe : first ≠ source := by
          intro equal
          apply fullFree
          simp [equal]
        rw [show successorMarker source target first = 4 by
          simp [successorMarker, firstNe, firstTarget]]
        simp only [listEvalStep]
        rw [show table.semigroup.mul (4 : Fin 5) (1 : Fin 5) =
            (1 : Fin 5) by decide]

private theorem table_zero_left (right : Fin 5) :
    table.semigroup.mul (0 : Fin 5) right = (0 : Fin 5) := by
  change Generated.Catalogue.S5_402.mul (0 : Fin 5) right = (0 : Fin 5)
  revert right
  decide

private theorem listEvalFrom_zero
    (source target : Nat) (letters : List Nat) :
    listEvalFrom table.semigroup (some 0)
        (successorMarker source target) letters = some 0 := by
  induction letters with
  | nil => rfl
  | cons first rest ih =>
      rw [listEvalFrom_cons]
      simp only [listEvalStep]
      rw [table_zero_left]
      exact ih

private theorem listEval_adjacent
    {source target : Nat} (different : source ≠ target)
    (before after : List Nat) (beforeFree : source ∉ before) :
    listEvalFrom table.semigroup none
        (successorMarker source target)
        (before ++ source :: target :: after) = some 0 := by
  rw [listEval_prefix_source different before (target :: after) beforeFree]
  rw [listEvalFrom_cons, successorMarker_target different]
  simp only [listEvalStep]
  rw [show table.semigroup.mul (1 : Fin 5) (3 : Fin 5) =
      (0 : Fin 5) by decide]
  exact listEvalFrom_zero source target after

private theorem listEval_nonadjacent
    {source target next : Nat} (different : source ≠ target)
    (nextNeSource : next ≠ source) (nextNeTarget : next ≠ target)
    (before rest : List Nat) (beforeFree : source ∉ before)
    (restFree : source ∉ rest) :
    listEvalFrom table.semigroup none
        (successorMarker source target)
        (before ++ source :: next :: rest) = some 2 := by
  rw [listEval_prefix_source different before (next :: rest) beforeFree]
  rw [listEvalFrom_cons]
  rw [show successorMarker source target next = 4 by
    simp [successorMarker, nextNeSource, nextNeTarget]]
  simp only [listEvalStep]
  rw [show table.semigroup.mul (1 : Fin 5) (4 : Fin 5) =
      (2 : Fin 5) by decide]
  exact listEvalFrom_sourceFree_fixed different 2 (by decide) (by decide)
    restFree

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

/-- The direct target valuation returns zero exactly when the globally simple
source is immediately followed by the tested successor. -/
theorem successorMarker_eval_eq_zero_iff
    (source target : Nat) (word : Word Nat)
    (different : source ≠ target)
    (sourceSimple : GloballySimple word source) :
    table.semigroup.eval (successorMarker source target) word =
        (0 : Fin 5) ↔
      (source, target) ∈ word.adjacentPairs := by
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
    have evaluated :
        listEvalFrom table.semigroup none
            (successorMarker source target) word.toList = some 0 := by
      rw [split]
      exact listEval_adjacent different before after free.1
    rw [listEvalFrom_toList] at evaluated
    constructor
    · intro _
      exact adjacent
    · intro _
      exact Option.some.inj evaluated
  · have countOne : word.toList.count source = 1 := sourceSimple
    have sourceMember : source ∈ word.toList :=
      List.count_pos_iff.mp
        (show 0 < word.toList.count source by omega)
    obtain ⟨before, after, split⟩ :=
      List.mem_iff_append.mp sourceMember
    have free :=
      sourceFree_parts_of_count_one split sourceSimple
    cases after with
    | nil =>
        have evaluated :
            listEvalFrom table.semigroup none
                (successorMarker source target) word.toList = some 1 := by
          rw [split]
          exact listEval_prefix_source different before [] free.1
        rw [listEvalFrom_toList] at evaluated
        rw [Option.some.inj evaluated]
        simp [adjacent]
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
            listEvalFrom table.semigroup none
                (successorMarker source target) word.toList = some 2 := by
          rw [split]
          exact listEval_nonadjacent different nextNeSource nextNeTarget
            before rest free.1 restFree
        rw [listEvalFrom_toList] at evaluated
        rw [Option.some.inj evaluated]
        simp [adjacent]

theorem valid_immediateSuccessor
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SameImmediateSuccessors identity.lhs identity.rhs := by
  have capped := valid_cappedMultiplicity identity valid
  have simple :=
    sameGloballySimple_of_capped identity.lhs identity.rhs capped
  intro source target
  constructor
  · rintro ⟨different, lhsSimple, lhsSuccessor⟩
    have rhsSimple := (simple source).mp lhsSimple
    have evaluated := valid (successorMarker source target)
    have lhsZero :=
      (successorMarker_eval_eq_zero_iff source target identity.lhs
        different lhsSimple).2 lhsSuccessor
    have rhsZero := evaluated.symm.trans lhsZero
    exact ⟨different, rhsSimple,
      (successorMarker_eval_eq_zero_iff source target identity.rhs
        different rhsSimple).1 rhsZero⟩
  · rintro ⟨different, rhsSimple, rhsSuccessor⟩
    have lhsSimple := (simple source).mpr rhsSimple
    have evaluated := valid (successorMarker source target)
    have rhsZero :=
      (successorMarker_eval_eq_zero_iff source target identity.rhs
        different rhsSimple).2 rhsSuccessor
    have lhsZero := evaluated.trans rhsZero
    exact ⟨different, lhsSimple,
      (successorMarker_eval_eq_zero_iff source target identity.lhs
        different lhsSimple).1 lhsZero⟩

/-- Every valid target identity carries the necessary capped-support,
head, simple-variable, and simple-successor signature. -/
theorem sameSignature_of_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SameSimpleSuccessorSignature identity.lhs identity.rhs := by
  have capped := valid_cappedMultiplicity identity valid
  exact
    { capped := capped
      support := sameSupport_of_capped identity.lhs identity.rhs capped
      head := valid_head identity valid
      globallySimple :=
        sameGloballySimple_of_capped identity.lhs identity.rhs capped
      successor := valid_immediateSuccessor identity valid }

/-- Every finite derivation preserves the necessary signature. -/
theorem derives_sameSignature {left right : Word Nat}
    (derivation : Derives basis left right) :
    SameSimpleSuccessorSignature left right :=
  sameSignature_of_valid ⟨left, right⟩
    (fun valuation => derivation.sound models valuation)

private def instantiateThreeWords
    (u v z : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private theorem basisPower : Derives basis xx xxx :=
  Derives.fromBasis (e := powerLaw) <| by simp [basis]

private theorem basisLeftDuplication : Derives basis xyx xxyx :=
  Derives.fromBasis (e := leftDuplicationLaw) <| by simp [basis]

private theorem basisRightDuplication : Derives basis xyx xyxx :=
  Derives.fromBasis (e := rightDuplicationLaw) <| by simp [basis]

private theorem basisSquareAlternation : Derives basis xxyy xyxy :=
  Derives.fromBasis (e := squareAlternationLaw) <| by simp [basis]

private theorem basisSquareCrossing : Derives basis xxyy xyyx :=
  Derives.fromBasis (e := squareCrossingLaw) <| by simp [basis]

private theorem basisFactorLeft : Derives basis xxyzy xxzyy :=
  Derives.fromBasis (e := factorLeftLaw) <| by simp [basis]

private theorem basisFactorMiddleLeft : Derives basis xxyzy xyxzy :=
  Derives.fromBasis (e := factorMiddleLeftLaw) <| by simp [basis]

private theorem basisFactorMiddleRight : Derives basis xxyzy xyzyx :=
  Derives.fromBasis (e := factorMiddleRightLaw) <| by simp [basis]

private theorem basisFactorSwap : Derives basis xxyzy xzyxy :=
  Derives.fromBasis (e := factorSwapLaw) <| by simp [basis]

private theorem basisFactorRight : Derives basis xxyzy xzyyx :=
  Derives.fromBasis (e := factorRightLaw) <| by simp [basis]

private theorem basisSimpleBlockSwap : Derives basis xyxzx xzxyx :=
  Derives.fromBasis (e := simpleBlockSwapLaw) <| by simp [basis]

private theorem basisSuccessorShift : Derives basis xyxzz xzyxz :=
  Derives.fromBasis (e := successorShiftLaw) <| by simp [basis]

private theorem basisSuccessorReverse : Derives basis xyxzz xzzyx :=
  Derives.fromBasis (e := successorReverseLaw) <| by simp [basis]

theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisPower (instantiateThreeWords u u u)
  simpa [xx, xxx, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesLeftDuplication (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ u) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisLeftDuplication (instantiateThreeWords u v v)
  simpa [xyx, xxyx, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesRightDuplication (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ v) ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisRightDuplication (instantiateThreeWords u v v)
  simpa [xyx, xyxx, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesSquareAlternation (u v : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ v)
      (((u ++ v) ++ u) ++ v) := by
  have substituted :=
    Derives.subst basisSquareAlternation (instantiateThreeWords u v v)
  simpa [xxyy, xyxy, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesSquareCrossing (u v : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ v)
      (((u ++ v) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisSquareCrossing (instantiateThreeWords u v v)
  simpa [xxyy, xyyx, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesFactorLeft (u v z : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ z) ++ v)
      ((((u ++ u) ++ z) ++ v) ++ v) := by
  have substituted :=
    Derives.subst basisFactorLeft (instantiateThreeWords u v z)
  simpa [xxyzy, xxzyy, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesFactorMiddleLeft (u v z : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ z) ++ v)
      ((((u ++ v) ++ u) ++ z) ++ v) := by
  have substituted :=
    Derives.subst basisFactorMiddleLeft (instantiateThreeWords u v z)
  simpa [xxyzy, xyxzy, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesFactorMiddleRight (u v z : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ z) ++ v)
      ((((u ++ v) ++ z) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisFactorMiddleRight (instantiateThreeWords u v z)
  simpa [xxyzy, xyzyx, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesFactorSwap (u v z : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ z) ++ v)
      ((((u ++ z) ++ v) ++ u) ++ v) := by
  have substituted :=
    Derives.subst basisFactorSwap (instantiateThreeWords u v z)
  simpa [xxyzy, xzyxy, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesFactorRight (u v z : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ z) ++ v)
      ((((u ++ z) ++ v) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisFactorRight (instantiateThreeWords u v z)
  simpa [xxyzy, xzyyx, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesSimpleBlockSwap (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ z) ++ u)
      ((((u ++ z) ++ u) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisSimpleBlockSwap (instantiateThreeWords u v z)
  simpa [xyxzx, xzxyx, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesSuccessorShift (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ z) ++ z)
      ((((u ++ z) ++ v) ++ u) ++ z) := by
  have substituted :=
    Derives.subst basisSuccessorShift (instantiateThreeWords u v z)
  simpa [xyxzz, xzyxz, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesSuccessorReverse (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ z) ++ z)
      ((((u ++ z) ++ z) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisSuccessorReverse (instantiateThreeWords u v z)
  simpa [xyxzz, xzzyx, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- The recorded chain `x^4 -> x^3 -> x^2`. -/
theorem derivesLeePowerFourToTwo (u : Word Nat) :
    Derives basis (((u ++ u) ++ u) ++ u) (u ++ u) := by
  have first := Derives.prepend u (derivesPowerExpansion u).symm
  have fourToThree :
      Derives basis (((u ++ u) ++ u) ++ u) ((u ++ u) ++ u) := by
    simpa [Word.append_assoc] using first
  exact fourToThree.trans (derivesPowerExpansion u).symm

/-- The recorded chain `x^3yx -> x^2yx -> xyx`. -/
theorem derivesLeeLeadingPowerReduction (u v : Word Nat) :
    Derives basis ((((u ++ u) ++ u) ++ v) ++ u)
      ((u ++ v) ++ u) := by
  have first := Derives.prepend u (derivesLeftDuplication u v).symm
  have threeToTwo :
      Derives basis ((((u ++ u) ++ u) ++ v) ++ u)
        (((u ++ u) ++ v) ++ u) := by
    simpa [Word.append_assoc] using first
  exact threeToTwo.trans (derivesLeftDuplication u v).symm

/-- The recorded chain `x^2yx -> xyx -> xyx^2`. -/
theorem derivesLeeDuplicationBridge (u v : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ u)
      (((u ++ v) ++ u) ++ u) :=
  (derivesLeftDuplication u v).symm.trans
    (derivesRightDuplication u v)

/-- The recorded chain `x^2yz^2 -> x^2zyz -> xyz^2x`. -/
theorem derivesLeeSquareTailMove (u v z : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ z) ++ z)
      ((((u ++ v) ++ z) ++ z) ++ u) :=
  (derivesFactorLeft u z v).symm.trans
    (derivesFactorRight u z v)

/-- The fifth Lee-system law is one displayed primitive law. -/
theorem derivesLeeSimpleBlockSwap (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ z) ++ u)
      ((((u ++ z) ++ u) ++ v) ++ u) :=
  derivesSimpleBlockSwap u v z

/-- The five exact Lee-system chains pinned by the structural certificate. -/
def recordedFiniteChains : List (List (Word Nat)) :=
  [
    [w 0 [0, 0, 0], w 0 [0, 0], w 0 [0]],
    [w 0 [0, 0, 1, 0], w 0 [0, 1, 0], w 0 [1, 0]],
    [w 0 [0, 1, 0], w 0 [1, 0], w 0 [1, 0, 0]],
    [w 0 [0, 1, 2, 2], w 0 [0, 2, 1, 2], w 0 [1, 2, 2, 0]],
    [w 0 [1, 0, 2, 0], w 0 [2, 0, 1, 0]]
  ]

/- Unrestricted grouped-tail normalization, scanner factorization, canonical
square-inventory normalization, and signature sufficiency are developed in the
subsequent `S5_402*` modules. -/

end SemigroupBasis.CoRoots.S5_402
