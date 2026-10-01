import SemigroupBasis.CoRoots.S5_851Normalization
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder5Part07
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_851

open SemigroupBasis
open SemigroupBasis.Examples

abbrev table : FiniteTable :=
  Generated.Catalogue.S5_851.table

def finiteRightDuplicationLaw : Identity (Fin 3) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 1]⟩⟩

def finiteInteriorExpansionLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1, 2]⟩⟩

def finiteInitialMoveLaw : Identity (Fin 3) :=
  ⟨⟨0, [0, 1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

theorem finiteRightDuplicationLaw_map :
    finiteRightDuplicationLaw.map Fin.val =
      rightDuplicationLaw := rfl

theorem finiteInteriorExpansionLaw_map :
    finiteInteriorExpansionLaw.map Fin.val =
      interiorExpansionLaw := rfl

theorem finiteInitialMoveLaw_map :
    finiteInitialMoveLaw.map Fin.val =
      initialMoveLaw := rfl

/-- The exact stored `S5_851` table satisfies all three ordered laws. -/
theorem catalogueModels : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl
  · rw [← finiteRightDuplicationLaw_map]
    exact table.checkIdentityNat_sound
      finiteRightDuplicationLaw (by decide)
  · rw [← finiteInteriorExpansionLaw_map]
    exact table.checkIdentityNat_sound
      finiteInteriorExpansionLaw (by decide)
  · rw [← finiteInitialMoveLaw_map]
    exact table.checkIdentityNat_sound
      finiteInitialMoveLaw (by decide)

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

def yx : Word Nat := ⟨1, [0]⟩
def yyx : Word Nat := ⟨1, [1, 0]⟩
def zyx : Word Nat := ⟨2, [1, 0]⟩
def zyzx : Word Nat := ⟨2, [1, 2, 0]⟩
def zyxx : Word Nat := ⟨2, [1, 0, 0]⟩
def zxyx : Word Nat := ⟨2, [0, 1, 0]⟩

def expectedOppositeBasis : List (Identity Nat) :=
  [⟨yx, yyx⟩, ⟨zyx, zyzx⟩, ⟨zyxx, zxyx⟩]

theorem oppositeBasis_eq_expected :
    oppositeBasis = expectedOppositeBasis := by
  rfl

/-- Left-zero states `1` and `3` in one-based notation separate the first
variable independently of later occurrences. -/
def headSeparator (tested : Nat) : Nat → Fin 5 :=
  fun letter => if letter = tested then 0 else 2

/-- One-based state `3` marks content while one-based state `4` passes. -/
def supportSeparator (tested : Nat) : Nat → Fin 5 :=
  fun letter => if letter = tested then 2 else 3

/-- One-based states `4` and `5` form a right-zero pair and expose the
final variable. -/
def finalSeparator (tested : Nat) : Nat → Fin 5 :=
  fun letter => if letter = tested then 4 else 3

/-- One-based state `2` survives pass states and collapses after a repeated
tested initial variable. -/
def initialMultiplicitySeparator (tested : Nat) : Nat → Fin 5 :=
  fun letter => if letter = tested then 1 else 3

namespace SeparatorBridge

theorem head_eq
    (semigroup : Semigroup (Fin 5))
    (evalSeparator :
      ∀ (tested : Nat) (word : Word Nat),
        semigroup.eval (headSeparator tested) word =
          headSeparator tested word.head)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy semigroup) :
    identity.lhs.head = identity.rhs.head := by
  let tested := identity.lhs.head
  have evaluated := valid (headSeparator tested)
  rw [evalSeparator, evalSeparator] at evaluated
  apply Decidable.byContradiction
  intro different
  have reverseDifferent :
      identity.rhs.head ≠ tested := by
    intro equal
    exact different <| by
      simpa [tested] using equal.symm
  simpa [tested, headSeparator, reverseDifferent] using evaluated

theorem support_eq
    (semigroup : Semigroup (Fin 5))
    (evalPass :
      ∀ (tested : Nat) (word : Word Nat),
        semigroup.eval (supportSeparator tested) word = 3 ↔
          tested ∉ word.toList)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy semigroup) :
    ∀ letter,
      letter ∈ identity.lhs.toList ↔
        letter ∈ identity.rhs.toList := by
  intro letter
  have evaluated := valid (supportSeparator letter)
  constructor
  · intro leftMember
    apply Decidable.byContradiction
    intro rightAbsent
    have rightPass :=
      (evalPass letter identity.rhs).2 rightAbsent
    have leftNotPass :
        semigroup.eval (supportSeparator letter)
            identity.lhs ≠ 3 := by
      intro leftPass
      exact ((evalPass letter identity.lhs).1 leftPass)
        leftMember
    exact leftNotPass <| evaluated.trans rightPass
  · intro rightMember
    apply Decidable.byContradiction
    intro leftAbsent
    have leftPass :=
      (evalPass letter identity.lhs).2 leftAbsent
    have rightNotPass :
        semigroup.eval (supportSeparator letter)
            identity.rhs ≠ 3 := by
      intro rightPass
      exact ((evalPass letter identity.rhs).1 rightPass)
        rightMember
    exact rightNotPass <| evaluated.symm.trans leftPass

private theorem final_wordOfPrefixFinal
    (pre : List Nat) (final : Nat) :
    (wordOfPrefixFinal pre final).final = final := by
  induction pre with
  | nil => rfl
  | cons letter rest induction =>
      rw [wordOfPrefixFinal_cons, Word.final_append]
      exact induction

theorem final_eq
    (semigroup : Semigroup (Fin 5))
    (evalSeparator :
      ∀ (tested : Nat) (pre : List Nat) (final : Nat),
        semigroup.eval (finalSeparator tested)
            (wordOfPrefixFinal pre final) =
          finalSeparator tested final)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy semigroup) :
    identity.lhs.final = identity.rhs.final := by
  have splitFinalEq :
      (splitPrefixFinal identity.lhs).2 =
        (splitPrefixFinal identity.rhs).2 := by
    let tested := (splitPrefixFinal identity.lhs).2
    have evaluated := valid (finalSeparator tested)
    rw [← wordOfPrefixFinal_split identity.lhs,
      ← wordOfPrefixFinal_split identity.rhs,
      evalSeparator, evalSeparator] at evaluated
    apply Decidable.byContradiction
    intro different
    have reversed :
        (splitPrefixFinal identity.rhs).2 =
          (splitPrefixFinal identity.lhs).2 := by
      simpa [tested, finalSeparator, different] using evaluated
    exact different reversed.symm
  have leftFinal :
      (splitPrefixFinal identity.lhs).2 =
        identity.lhs.final := by
    have reconstructed :=
      congrArg Word.final (wordOfPrefixFinal_split identity.lhs)
    rw [final_wordOfPrefixFinal] at reconstructed
    exact reconstructed
  have rightFinal :
      (splitPrefixFinal identity.rhs).2 =
        identity.rhs.final := by
    have reconstructed :=
      congrArg Word.final (wordOfPrefixFinal_split identity.rhs)
    rw [final_wordOfPrefixFinal] at reconstructed
    exact reconstructed
  exact leftFinal.symm.trans <| splitFinalEq.trans rightFinal

theorem repeatedInitial_eq
    (semigroup : Semigroup (Fin 5))
    (evalSeparator :
      ∀ (tested : Nat) (tail : List Nat),
        semigroup.eval (initialMultiplicitySeparator tested)
            ⟨tested, tail⟩ =
          if tested ∈ tail then 0 else 1)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy semigroup)
    (heads : identity.lhs.head = identity.rhs.head) :
    S5_855.repeatedInitial identity.lhs =
      S5_855.repeatedInitial identity.rhs := by
  rcases identity with
    ⟨⟨leftHead, leftTail⟩, ⟨rightHead, rightTail⟩⟩
  let tested := leftHead
  have evaluated := valid (initialMultiplicitySeparator tested)
  change leftHead = rightHead at heads
  subst rightHead
  change
    semigroup.eval
        (initialMultiplicitySeparator leftHead)
        ⟨leftHead, leftTail⟩ =
      semigroup.eval
        (initialMultiplicitySeparator leftHead)
        ⟨leftHead, rightTail⟩ at evaluated
  rw [evalSeparator, evalSeparator] at evaluated
  unfold S5_855.repeatedInitial
  by_cases leftMember : leftHead ∈ leftTail
  · by_cases rightMember : leftHead ∈ rightTail
    · simp [leftMember, rightMember]
    · simp [leftMember, rightMember] at evaluated
  · by_cases rightMember : leftHead ∈ rightTail
    · simp [leftMember, rightMember] at evaluated
    · simp [leftMember, rightMember]

end SeparatorBridge

private theorem headSeparator_mul
    (tested leftLetter rightLetter : Nat) :
    Generated.Catalogue.S5_851.mul
        (headSeparator tested leftLetter)
        (headSeparator tested rightLetter) =
      headSeparator tested leftLetter := by
  by_cases leftEqual : leftLetter = tested
  · subst leftLetter
    by_cases rightEqual : rightLetter = tested
    · subst rightLetter
      simp [headSeparator, Generated.Catalogue.S5_851.mul]
    · simp [headSeparator, rightEqual, eq_comm,
        Generated.Catalogue.S5_851.mul]
  · by_cases rightEqual : rightLetter = tested
    · subst rightLetter
      simp [headSeparator, leftEqual, eq_comm,
        Generated.Catalogue.S5_851.mul]
    · simp [headSeparator, leftEqual, rightEqual, eq_comm,
        Generated.Catalogue.S5_851.mul]

private theorem headSeparatorFold
    (tested initial : Nat) :
    ∀ letters : List Nat,
      letters.foldl
          (fun current letter =>
            Generated.Catalogue.S5_851.mul current
              (headSeparator tested letter))
          (headSeparator tested initial) =
        headSeparator tested initial
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      rw [headSeparator_mul]
      exact headSeparatorFold tested initial rest

theorem headSeparator_eval
    (tested : Nat) (word : Word Nat) :
    table.semigroup.eval (headSeparator tested) word =
      headSeparator tested word.head := by
  cases word with
  | mk head tail =>
      change
        tail.foldl
            (fun current letter =>
              Generated.Catalogue.S5_851.mul current
                (headSeparator tested letter))
            (headSeparator tested head) =
          headSeparator tested head
      exact headSeparatorFold tested head tail

private theorem supportZeroFold
    (tested : Nat) :
    ∀ letters : List Nat,
      letters.foldl
          (fun current letter =>
            Generated.Catalogue.S5_851.mul current
              (supportSeparator tested letter))
          0 = 0
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      rw [show
        Generated.Catalogue.S5_851.mul 0
            (supportSeparator tested letter) = 0 by
          by_cases equal : letter = tested
          · subst letter
            simp [supportSeparator,
              Generated.Catalogue.S5_851.mul]
          · have value :
                supportSeparator tested letter = (3 : Fin 5) := by
              simp [supportSeparator, equal, eq_comm]
            rw [value]
            decide]
      exact supportZeroFold tested rest

private theorem supportTwoFold
    (tested : Nat) :
    ∀ letters : List Nat,
      letters.foldl
          (fun current letter =>
            Generated.Catalogue.S5_851.mul current
              (supportSeparator tested letter))
          2 = 2
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      rw [show
        Generated.Catalogue.S5_851.mul 2
            (supportSeparator tested letter) = 2 by
          by_cases equal : letter = tested
          · subst letter
            simp [supportSeparator,
              Generated.Catalogue.S5_851.mul]
          · have value :
                supportSeparator tested letter = (3 : Fin 5) := by
              simp [supportSeparator, equal, eq_comm]
            rw [value]
            decide]
      exact supportTwoFold tested rest

private theorem supportPassFold
    (tested : Nat) :
    ∀ letters : List Nat,
      letters.foldl
          (fun current letter =>
            Generated.Catalogue.S5_851.mul current
              (supportSeparator tested letter))
          3 =
        if tested ∈ letters then 0 else 3
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      by_cases equal : letter = tested
      · subst letter
        rw [show supportSeparator tested tested = (2 : Fin 5) by
          simp [supportSeparator]]
        rw [show Generated.Catalogue.S5_851.mul 3 2 =
            (0 : Fin 5) by decide]
        rw [supportZeroFold]
        simp
      · rw [show supportSeparator tested letter = (3 : Fin 5) by
          simp [supportSeparator, equal, eq_comm]]
        rw [show Generated.Catalogue.S5_851.mul 3 3 =
            (3 : Fin 5) by decide]
        rw [supportPassFold]
        have reverse : tested ≠ letter := Ne.symm equal
        simp [equal, reverse]

theorem supportSeparator_eval_eq_pass_iff
    (tested : Nat) (word : Word Nat) :
    table.semigroup.eval (supportSeparator tested) word =
        (3 : Fin 5) ↔
      tested ∉ word.toList := by
  cases word with
  | mk head tail =>
      change
        tail.foldl
            (fun current letter =>
              Generated.Catalogue.S5_851.mul current
                (supportSeparator tested letter))
            (supportSeparator tested head) = 3 ↔
          tested ∉ head :: tail
      by_cases equal : head = tested
      · subst head
        rw [show supportSeparator tested tested = (2 : Fin 5) by
          simp [supportSeparator]]
        rw [supportTwoFold]
        simp
      · rw [show supportSeparator tested head = (3 : Fin 5) by
          simp [supportSeparator, equal, eq_comm]]
        rw [supportPassFold]
        have reverse : tested ≠ head := Ne.symm equal
        simp [equal, reverse]

private theorem finalSeparator_mul
    (tested leftLetter rightLetter : Nat) :
    Generated.Catalogue.S5_851.mul
        (finalSeparator tested leftLetter)
        (finalSeparator tested rightLetter) =
      finalSeparator tested rightLetter := by
  by_cases leftEqual : leftLetter = tested
  · subst leftLetter
    by_cases rightEqual : rightLetter = tested
    · subst rightLetter
      simp [finalSeparator, Generated.Catalogue.S5_851.mul]
    · simp [finalSeparator, rightEqual, eq_comm,
        Generated.Catalogue.S5_851.mul]
  · by_cases rightEqual : rightLetter = tested
    · subst rightLetter
      simp [finalSeparator, leftEqual, eq_comm,
        Generated.Catalogue.S5_851.mul]
    · simp [finalSeparator, leftEqual, rightEqual, eq_comm,
        Generated.Catalogue.S5_851.mul]

theorem finalSeparator_eval
    (tested : Nat) (pre : List Nat) (final : Nat) :
    table.semigroup.eval (finalSeparator tested)
        (wordOfPrefixFinal pre final) =
      finalSeparator tested final := by
  induction pre with
  | nil => rfl
  | cons letter rest induction =>
      rw [wordOfPrefixFinal_cons, Semigroup.eval_append,
        Semigroup.eval_singleton, induction]
      exact finalSeparator_mul tested letter final

private theorem zeroFold
    (tested : Nat) :
    ∀ letters : List Nat,
      letters.foldl
          (fun current letter =>
            Generated.Catalogue.S5_851.mul current
              (initialMultiplicitySeparator tested letter))
          0 = 0
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      rw [show
        Generated.Catalogue.S5_851.mul 0
            (initialMultiplicitySeparator tested letter) = 0 by
          by_cases equal : letter = tested
          · subst letter
            simp [initialMultiplicitySeparator,
              Generated.Catalogue.S5_851.mul]
          · have value :
                initialMultiplicitySeparator tested letter =
                  (3 : Fin 5) := by
              simp [initialMultiplicitySeparator, equal, eq_comm]
            rw [value]
            decide]
      exact zeroFold tested rest

private theorem initialMultiplicityFold
    (tested : Nat) :
    ∀ letters : List Nat,
      letters.foldl
          (fun current letter =>
            Generated.Catalogue.S5_851.mul current
              (initialMultiplicitySeparator tested letter))
          1 =
        if tested ∈ letters then 0 else 1
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      by_cases equal : letter = tested
      · subst letter
        rw [show initialMultiplicitySeparator tested tested =
            (1 : Fin 5) by
          simp [initialMultiplicitySeparator]]
        rw [show Generated.Catalogue.S5_851.mul 1 1 =
            (0 : Fin 5) by decide]
        rw [zeroFold]
        simp
      · rw [show initialMultiplicitySeparator tested letter =
            (3 : Fin 5) by
          simp [initialMultiplicitySeparator, equal, eq_comm]]
        rw [show Generated.Catalogue.S5_851.mul 1 3 =
            (1 : Fin 5) by decide]
        rw [initialMultiplicityFold]
        have reverse : tested ≠ letter := Ne.symm equal
        simp [equal, reverse]

theorem initialMultiplicitySeparator_eval
    (tested : Nat) (tail : List Nat) :
    table.semigroup.eval (initialMultiplicitySeparator tested)
        ⟨tested, tail⟩ =
      if tested ∈ tail then (0 : Fin 5) else (1 : Fin 5) := by
  change
    tail.foldl
        (fun current letter =>
          Generated.Catalogue.S5_851.mul current
            (initialMultiplicitySeparator tested letter))
        (initialMultiplicitySeparator tested tested) =
      if tested ∈ tail then 0 else 1
  rw [show initialMultiplicitySeparator tested tested =
      (1 : Fin 5) by
    simp [initialMultiplicitySeparator]]
  exact initialMultiplicityFold tested tail

theorem valid_signature
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SameHeadSupportFinalSignature identity.lhs identity.rhs := by
  have heads :=
    SeparatorBridge.head_eq table.semigroup headSeparator_eval
      identity valid
  exact
    ⟨heads,
      SeparatorBridge.support_eq table.semigroup
        supportSeparator_eval_eq_pass_iff identity valid,
      SeparatorBridge.final_eq table.semigroup finalSeparator_eval
        identity valid,
      SeparatorBridge.repeatedInitial_eq table.semigroup
        initialMultiplicitySeparator_eval identity valid heads⟩

/-- Conditional representative endpoint. The hypothesis is the named
unrestricted derivational obstruction, not an admitted theorem. -/
theorem representative_basis_of_headSupportFinalDerivationalCompleteness
    (complete : HeadSupportFinalDerivationalCompleteness) :
    BasisFor table.semigroup basis := by
  refine ⟨catalogueModels, ?_⟩
  intro identity valid
  exact complete identity.lhs identity.rhs
    (valid_signature identity valid)

/-- Conditional opposite endpoint for the non-self-dual `S5_851`
anti-isomorphism class. -/
theorem opposite_basis_of_headSupportFinalDerivationalCompleteness
    (complete : HeadSupportFinalDerivationalCompleteness) :
    BasisFor table.semigroup.opposite expectedOppositeBasis := by
  rw [← oppositeBasis_eq_expected]
  exact
    (representative_basis_of_headSupportFinalDerivationalCompleteness
      complete).oppositeReversed

end SemigroupBasis.CoRoots.S5_851

namespace SemigroupBasis.CoRoots.S5_867

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_851

abbrev table : FiniteTable :=
  Generated.Catalogue.S5_867.table

/-- The second stored frontier member satisfies the same exact basis. -/
theorem catalogueModels : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl
  · rw [← finiteRightDuplicationLaw_map]
    exact table.checkIdentityNat_sound
      finiteRightDuplicationLaw (by decide)
  · rw [← finiteInteriorExpansionLaw_map]
    exact table.checkIdentityNat_sound
      finiteInteriorExpansionLaw (by decide)
  · rw [← finiteInitialMoveLaw_map]
    exact table.checkIdentityNat_sound
      finiteInitialMoveLaw (by decide)

private theorem headSeparator_mul
    (tested leftLetter rightLetter : Nat) :
    Generated.Catalogue.S5_867.mul
        (headSeparator tested leftLetter)
        (headSeparator tested rightLetter) =
      headSeparator tested leftLetter := by
  by_cases leftEqual : leftLetter = tested
  · subst leftLetter
    by_cases rightEqual : rightLetter = tested
    · subst rightLetter
      simp [headSeparator, Generated.Catalogue.S5_867.mul]
    · simp [headSeparator, rightEqual, eq_comm,
        Generated.Catalogue.S5_867.mul]
  · by_cases rightEqual : rightLetter = tested
    · subst rightLetter
      simp [headSeparator, leftEqual, eq_comm,
        Generated.Catalogue.S5_867.mul]
    · simp [headSeparator, leftEqual, rightEqual, eq_comm,
        Generated.Catalogue.S5_867.mul]

private theorem headSeparatorFold
    (tested initial : Nat) :
    ∀ letters : List Nat,
      letters.foldl
          (fun current letter =>
            Generated.Catalogue.S5_867.mul current
              (headSeparator tested letter))
          (headSeparator tested initial) =
        headSeparator tested initial
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      rw [headSeparator_mul]
      exact headSeparatorFold tested initial rest

theorem headSeparator_eval
    (tested : Nat) (word : Word Nat) :
    table.semigroup.eval (headSeparator tested) word =
      headSeparator tested word.head := by
  cases word with
  | mk head tail =>
      change
        tail.foldl
            (fun current letter =>
              Generated.Catalogue.S5_867.mul current
                (headSeparator tested letter))
            (headSeparator tested head) =
          headSeparator tested head
      exact headSeparatorFold tested head tail

private theorem supportTwoFold
    (tested : Nat) :
    ∀ letters : List Nat,
      letters.foldl
          (fun current letter =>
            Generated.Catalogue.S5_867.mul current
              (supportSeparator tested letter))
          2 = 2
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      rw [show
        Generated.Catalogue.S5_867.mul 2
            (supportSeparator tested letter) = 2 by
          by_cases equal : letter = tested
          · subst letter
            simp [supportSeparator,
              Generated.Catalogue.S5_867.mul]
          · have value :
                supportSeparator tested letter = (3 : Fin 5) := by
              simp [supportSeparator, equal, eq_comm]
            rw [value]
            decide]
      exact supportTwoFold tested rest

private theorem supportPassFold
    (tested : Nat) :
    ∀ letters : List Nat,
      letters.foldl
          (fun current letter =>
            Generated.Catalogue.S5_867.mul current
              (supportSeparator tested letter))
          3 =
        if tested ∈ letters then 2 else 3
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      by_cases equal : letter = tested
      · subst letter
        rw [show supportSeparator tested tested = (2 : Fin 5) by
          simp [supportSeparator]]
        rw [show Generated.Catalogue.S5_867.mul 3 2 =
            (2 : Fin 5) by decide]
        rw [supportTwoFold]
        simp
      · rw [show supportSeparator tested letter = (3 : Fin 5) by
          simp [supportSeparator, equal, eq_comm]]
        rw [show Generated.Catalogue.S5_867.mul 3 3 =
            (3 : Fin 5) by decide]
        rw [supportPassFold]
        have reverse : tested ≠ letter := Ne.symm equal
        simp [equal, reverse]

theorem supportSeparator_eval_eq_pass_iff
    (tested : Nat) (word : Word Nat) :
    table.semigroup.eval (supportSeparator tested) word =
        (3 : Fin 5) ↔
      tested ∉ word.toList := by
  cases word with
  | mk head tail =>
      change
        tail.foldl
            (fun current letter =>
              Generated.Catalogue.S5_867.mul current
                (supportSeparator tested letter))
            (supportSeparator tested head) = 3 ↔
          tested ∉ head :: tail
      by_cases equal : head = tested
      · subst head
        rw [show supportSeparator tested tested = (2 : Fin 5) by
          simp [supportSeparator]]
        rw [supportTwoFold]
        simp
      · rw [show supportSeparator tested head = (3 : Fin 5) by
          simp [supportSeparator, equal, eq_comm]]
        rw [supportPassFold]
        have reverse : tested ≠ head := Ne.symm equal
        simp [equal, reverse]

private theorem finalSeparator_mul
    (tested leftLetter rightLetter : Nat) :
    Generated.Catalogue.S5_867.mul
        (finalSeparator tested leftLetter)
        (finalSeparator tested rightLetter) =
      finalSeparator tested rightLetter := by
  by_cases leftEqual : leftLetter = tested
  · subst leftLetter
    by_cases rightEqual : rightLetter = tested
    · subst rightLetter
      simp [finalSeparator, Generated.Catalogue.S5_867.mul]
    · simp [finalSeparator, rightEqual, eq_comm,
        Generated.Catalogue.S5_867.mul]
  · by_cases rightEqual : rightLetter = tested
    · subst rightLetter
      simp [finalSeparator, leftEqual, eq_comm,
        Generated.Catalogue.S5_867.mul]
    · simp [finalSeparator, leftEqual, rightEqual, eq_comm,
        Generated.Catalogue.S5_867.mul]

theorem finalSeparator_eval
    (tested : Nat) (pre : List Nat) (final : Nat) :
    table.semigroup.eval (finalSeparator tested)
        (wordOfPrefixFinal pre final) =
      finalSeparator tested final := by
  induction pre with
  | nil => rfl
  | cons letter rest induction =>
      rw [wordOfPrefixFinal_cons, Semigroup.eval_append,
        Semigroup.eval_singleton, induction]
      exact finalSeparator_mul tested letter final

private theorem zeroFold
    (tested : Nat) :
    ∀ letters : List Nat,
      letters.foldl
          (fun current letter =>
            Generated.Catalogue.S5_867.mul current
              (initialMultiplicitySeparator tested letter))
          0 = 0
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      rw [show
        Generated.Catalogue.S5_867.mul 0
            (initialMultiplicitySeparator tested letter) = 0 by
          by_cases equal : letter = tested
          · subst letter
            simp [initialMultiplicitySeparator,
              Generated.Catalogue.S5_867.mul]
          · have value :
                initialMultiplicitySeparator tested letter =
                  (3 : Fin 5) := by
              simp [initialMultiplicitySeparator, equal, eq_comm]
            rw [value]
            decide]
      exact zeroFold tested rest

private theorem initialMultiplicityFold
    (tested : Nat) :
    ∀ letters : List Nat,
      letters.foldl
          (fun current letter =>
            Generated.Catalogue.S5_867.mul current
              (initialMultiplicitySeparator tested letter))
          1 =
        if tested ∈ letters then 0 else 1
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      by_cases equal : letter = tested
      · subst letter
        rw [show initialMultiplicitySeparator tested tested =
            (1 : Fin 5) by
          simp [initialMultiplicitySeparator]]
        rw [show Generated.Catalogue.S5_867.mul 1 1 =
            (0 : Fin 5) by decide]
        rw [zeroFold]
        simp
      · rw [show initialMultiplicitySeparator tested letter =
            (3 : Fin 5) by
          simp [initialMultiplicitySeparator, equal, eq_comm]]
        rw [show Generated.Catalogue.S5_867.mul 1 3 =
            (1 : Fin 5) by decide]
        rw [initialMultiplicityFold]
        have reverse : tested ≠ letter := Ne.symm equal
        simp [equal, reverse]

theorem initialMultiplicitySeparator_eval
    (tested : Nat) (tail : List Nat) :
    table.semigroup.eval (initialMultiplicitySeparator tested)
        ⟨tested, tail⟩ =
      if tested ∈ tail then (0 : Fin 5) else (1 : Fin 5) := by
  change
    tail.foldl
        (fun current letter =>
          Generated.Catalogue.S5_867.mul current
            (initialMultiplicitySeparator tested letter))
        (initialMultiplicitySeparator tested tested) =
      if tested ∈ tail then 0 else 1
  rw [show initialMultiplicitySeparator tested tested =
      (1 : Fin 5) by
    simp [initialMultiplicitySeparator]]
  exact initialMultiplicityFold tested tail

theorem valid_signature
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SameHeadSupportFinalSignature identity.lhs identity.rhs := by
  have heads :=
    SeparatorBridge.head_eq table.semigroup headSeparator_eval
      identity valid
  exact
    ⟨heads,
      SeparatorBridge.support_eq table.semigroup
        supportSeparator_eval_eq_pass_iff identity valid,
      SeparatorBridge.final_eq table.semigroup finalSeparator_eval
        identity valid,
      SeparatorBridge.repeatedInitial_eq table.semigroup
        initialMultiplicitySeparator_eval identity valid heads⟩

/-- Conditional representative endpoint for the second stored table. -/
theorem representative_basis_of_headSupportFinalDerivationalCompleteness
    (complete : HeadSupportFinalDerivationalCompleteness) :
    BasisFor table.semigroup basis := by
  refine ⟨catalogueModels, ?_⟩
  intro identity valid
  exact complete identity.lhs identity.rhs
    (valid_signature identity valid)

/-- Conditional opposite endpoint for the separate non-self-dual
`S5_867` anti-isomorphism class. -/
theorem opposite_basis_of_headSupportFinalDerivationalCompleteness
    (complete : HeadSupportFinalDerivationalCompleteness) :
    BasisFor table.semigroup.opposite expectedOppositeBasis := by
  rw [← oppositeBasis_eq_expected]
  exact
    (representative_basis_of_headSupportFinalDerivationalCompleteness
      complete).oppositeReversed

end SemigroupBasis.CoRoots.S5_867
