import SemigroupBasis.Nonfinite.LeeL.Context
import SemigroupBasis.Nonfinite.LeeL.BlockCombinatorics
import SemigroupBasis.Nonfinite.LeeL.OrderedSplit

namespace SemigroupBasis.Examples.LeeL

open SemigroupBasis

/-!
This file isolates the remaining source-level obligations in Zhang--Luo's
proof that Lee's semigroup is nonfinitely based. The finite table, the
identities `p(n) ≈ q(n)`, their validity, and the generic derivation invariant
are proved in `LeeLNonfinite`.

Lemma 2 is reconstructed in `Nonfinite/LeeL/OrderedSplit.lean`, so the
connected-basis reduction of Lemma 3 is unconditional. The remaining
certificate contains exactly Lemma 5 and the orientation-exclusion core of
Lemma 6.
-/

/-- Reverse the two sides of an identity, without reversing either word. -/
def swapIdentity (identity : Identity Nat) : Identity Nat :=
  ⟨identity.rhs, identity.lhs⟩

@[simp]
theorem swapIdentity_lhs (identity : Identity Nat) :
    (swapIdentity identity).lhs = identity.rhs := rfl

@[simp]
theorem swapIdentity_rhs (identity : Identity Nat) :
    (swapIdentity identity).rhs = identity.lhs := rfl

theorem swapIdentity_satisfiedBy {identity : Identity Nat}
    (valid : identity.SatisfiedBy table.semigroup) :
    (swapIdentity identity).SatisfiedBy table.semigroup := by
  intro valuation
  exact (valid valuation).symm

theorem swapIdentity_usesAtMost {identity : Identity Nat} {bound : Nat}
    (uses : identity.UsesAtMost bound) :
    (swapIdentity identity).UsesAtMost bound := by
  rcases uses with ⟨variables, lengthBound, leftOnly, rightOnly⟩
  exact ⟨variables, lengthBound, rightOnly, leftOnly⟩

theorem swapIdentity_connected {identity : Identity Nat}
    (connected : SourceWords.ConnectedIdentity identity) :
    SourceWords.ConnectedIdentity (swapIdentity identity) :=
  ⟨connected.2, connected.1⟩

/-- Lemma 1, simple-letter formulation. -/
theorem valid_identity_simple_iff {identity : Identity Nat}
    (valid : identity.SatisfiedBy table.semigroup) (letter : Nat) :
    SourceWords.SimpleIn letter identity.lhs ↔
      SourceWords.SimpleIn letter identity.rhs :=
  valid_identity_preserves_simplicity valid letter

/-- Lemma 1, nonsimple-letter formulation. -/
theorem valid_identity_nonsimple_iff {identity : Identity Nat}
    (valid : identity.SatisfiedBy table.semigroup) (letter : Nat) :
    SourceWords.NonsimpleIn letter identity.lhs ↔
      SourceWords.NonsimpleIn letter identity.rhs := by
  have content := valid_identity_sameContent valid letter
  have simple := valid_identity_simple_iff valid letter
  constructor
  · rintro ⟨member, notSimple⟩
    exact ⟨content.mp member, fun rhsSimple => notSimple (simple.mpr rhsSimple)⟩
  · rintro ⟨member, notSimple⟩
    exact ⟨content.mpr member, fun lhsSimple => notSimple (simple.mp lhsSimple)⟩

/-! ## Exact source obligations -/

/-- The direct ordered-splitting statement used as Zhang--Luo Lemma 2. -/
abbrev PaperLemma2 : Prop :=
  OrderedSplit.Property

/-- Lemma 2 is unconditional: `OrderedSplit.property` proves the `A₀`
ordered-cut argument and the idempotent-separability cancellation. -/
theorem paperLemma2 : PaperLemma2 :=
  OrderedSplit.property

/-- The finite, variable-bound-preserving form of Zhang--Luo Lemma 3 needed
by Theorem 8.  Lemmas 1 and 2 yield this by repeatedly splitting every
disconnected basis identity and discarding trivial singleton identities.

The theorem `paperLemma3FiniteReduction_of_paperLemma2` below proves this
obligation from `PaperLemma2`. -/
def PaperLemma3FiniteReduction : Prop :=
  ∀ basis : List (Identity Nat),
    BasisFor table.semigroup basis →
    ∃ connectedBasis : List (Identity Nat),
      BasisFor table.semigroup connectedBasis ∧
      (∀ identity, identity ∈ connectedBasis →
        SourceWords.ConnectedIdentity identity) ∧
      BasisUsesAtMost connectedBasis (basisVariables basis).length

private theorem word_length_pos (word : Word Nat) :
    0 < word.toList.length := by
  cases word
  simp [Word.toList]

private theorem valid_eq_of_lhs_length_one
    {identity : Identity Nat}
    (valid : identity.SatisfiedBy table.semigroup)
    (lengthOne : identity.lhs.toList.length = 1) :
    identity.lhs = identity.rhs := by
  cases identity with
  | mk lhs rhs =>
      cases lhs with
      | mk x xs =>
          simp only [Word.toList, List.length_cons] at lengthOne
          have xsEmpty : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
          subst xs
          have content :=
            valid_identity_sameContent
              (identity := Identity.mk (Word.mk x []) rhs) valid
          have simple :=
            valid_identity_simple_iff
              (identity := Identity.mk (Word.mk x []) rhs) valid x
          have rightSimple : rhs.toList.count x = 1 := by
            apply simple.mp
            simp [SourceWords.SimpleIn, Word.toList]
          cases rhs with
          | mk y ys =>
              have yMemRight : y ∈ (Word.mk y ys : Word Nat).toList := by
                exact List.Mem.head ys
              have yMemLeft := (content y).mpr yMemRight
              have yEq : y = x := by
                simpa [Word.toList] using yMemLeft
              subst y
              cases ys with
              | nil => rfl
              | cons z zs =>
                  have zMemRight :
                      z ∈ (Word.mk x (z :: zs) : Word Nat).toList := by
                    simp [Word.toList]
                  have zMemLeft := (content z).mpr zMemRight
                  have zEq : z = x := by
                    simpa [Word.toList] using zMemLeft
                  subst z
                  simp [Word.toList] at rightSimple

private theorem connected_rhs_of_connected_lhs
    (lemma2 : PaperLemma2)
    {identity : Identity Nat}
    (valid : identity.SatisfiedBy table.semigroup)
    (leftConnected : SourceWords.Connected identity.lhs) :
    SourceWords.Connected identity.rhs := by
  constructor
  · by_cases long : 2 ≤ identity.rhs.toList.length
    · exact long
    · have rhsLengthOne : identity.rhs.toList.length = 1 := by
        have := word_length_pos identity.rhs
        omega
      have swappedEquality :=
        valid_eq_of_lhs_length_one
          (identity := swapIdentity identity)
          (swapIdentity_satisfiedBy valid) rhsLengthOne
      have rhsEqLhs : identity.rhs = identity.lhs := swappedEquality
      rw [rhsEqLhs]
      exact leftConnected.1
  · rintro ⟨rightLeft, rightRight, rightSplit, rightDisjoint⟩
    rcases lemma2 (swapIdentity identity) rightLeft rightRight
        (swapIdentity_satisfiedBy valid) rightSplit rightDisjoint with
      ⟨leftLeft, leftRight, leftSplit, leftDisjoint, _⟩
    apply leftConnected.2
    exact ⟨leftLeft, leftRight, leftSplit, leftDisjoint⟩

private theorem word_usesOnly_of_append_left
    {whole left right : Word Nat} {variables : List Nat}
    (split : whole = left ++ right)
    (uses : whole.UsesOnly variables) :
    left.UsesOnly variables := by
  intro letter member
  apply uses letter
  rw [split, Word.toList_append]
  exact List.mem_append.mpr (Or.inl member)

private theorem word_usesOnly_of_append_right
    {whole left right : Word Nat} {variables : List Nat}
    (split : whole = left ++ right)
    (uses : whole.UsesOnly variables) :
    right.UsesOnly variables := by
  intro letter member
  apply uses letter
  rw [split, Word.toList_append]
  exact List.mem_append.mpr (Or.inr member)

private theorem word_usesOnly_of_sameContent
    {left right : Word Nat} {variables : List Nat}
    (same : SourceWords.SameContent left right)
    (uses : left.UsesOnly variables) :
    right.UsesOnly variables := by
  intro letter member
  exact uses letter ((same letter).mpr member)

private structure ConnectedDecomposition
    (variables : List Nat) (identity : Identity Nat)
    (pieces : List (Identity Nat)) : Prop where
  models : Models table.semigroup pieces
  connected :
    ∀ piece, piece ∈ pieces → SourceWords.ConnectedIdentity piece
  usesOnly : BasisUsesOnly pieces variables
  derives : Derives pieces identity.lhs identity.rhs

private theorem derives_mono
    {source target : List (Identity Nat)} {left right : Word Nat}
    (subset : ∀ identity, identity ∈ source → identity ∈ target)
    (derivation : Derives source left right) :
    Derives target left right :=
  derivation.transport fun identity member =>
    Derives.fromBasis (subset identity member)

private theorem exists_connected_decomposition
    (lemma2 : PaperLemma2)
    (identity : Identity Nat) (variables : List Nat)
    (valid : identity.SatisfiedBy table.semigroup)
    (uses : identity.UsesOnly variables) :
    ∃ pieces, ConnectedDecomposition variables identity pieces := by
  classical
  let targetLength := identity.lhs.toList.length
  have inductionStatement :
      ∀ length,
        (∀ smaller < length,
          ∀ (current : Identity Nat),
            current.lhs.toList.length = smaller →
            current.SatisfiedBy table.semigroup →
            current.UsesOnly variables →
            ∃ pieces,
              ConnectedDecomposition variables current pieces) →
        ∀ (current : Identity Nat),
          current.lhs.toList.length = length →
          current.SatisfiedBy table.semigroup →
          current.UsesOnly variables →
          ∃ pieces,
            ConnectedDecomposition variables current pieces := by
    intro length smaller current lengthEq currentValid currentUses
    by_cases lengthOne : length = 1
    · have currentLengthOne : current.lhs.toList.length = 1 := by
        omega
      have currentEq :=
        valid_eq_of_lhs_length_one currentValid currentLengthOne
      refine ⟨[], ?_⟩
      refine
        { models := ?_,
          connected := ?_,
          usesOnly := ?_,
          derives := ?_ }
      · intro piece member
        simp at member
      · intro piece member
        simp at member
      · intro piece member
        simp at member
      · rw [currentEq]
        exact Derives.refl current.rhs
    · by_cases leftConnected : SourceWords.Connected current.lhs
      · have rightConnected :=
          connected_rhs_of_connected_lhs lemma2 currentValid leftConnected
        refine ⟨[current], ?_⟩
        refine
          { models := ?_,
            connected := ?_,
            usesOnly := ?_,
            derives := ?_ }
        · intro piece member
          simp only [List.mem_singleton] at member
          subst piece
          exact currentValid
        · intro piece member
          simp only [List.mem_singleton] at member
          subst piece
          exact ⟨leftConnected, rightConnected⟩
        · intro piece member
          simp only [List.mem_singleton] at member
          subst piece
          exact currentUses
        · exact Derives.fromBasis (by simp)
      · have currentLong : 2 ≤ current.lhs.toList.length := by
          have := word_length_pos current.lhs
          omega
        have disconnected : SourceWords.Disconnected current.lhs := by
          by_cases split : SourceWords.Disconnected current.lhs
          · exact split
          · exact False.elim (leftConnected ⟨currentLong, split⟩)
        rcases disconnected with
          ⟨left, right, leftSplit, leftDisjoint⟩
        rcases lemma2 current left right currentValid leftSplit leftDisjoint with
          ⟨left', right', rightSplit, rightDisjoint, leftContent,
            rightContent, leftValid, rightValid⟩
        let leftIdentity : Identity Nat := ⟨left, left'⟩
        let rightIdentity : Identity Nat := ⟨right, right'⟩
        have leftLength :
            left.toList.length < current.lhs.toList.length := by
          rw [leftSplit, Word.toList_append, List.length_append]
          have := word_length_pos right
          omega
        have rightLength :
            right.toList.length < current.lhs.toList.length := by
          rw [leftSplit, Word.toList_append, List.length_append]
          have := word_length_pos left
          omega
        have leftUses : leftIdentity.UsesOnly variables := by
          constructor
          · exact word_usesOnly_of_append_left leftSplit currentUses.1
          · exact word_usesOnly_of_sameContent leftContent
              (word_usesOnly_of_append_left leftSplit currentUses.1)
        have rightUses : rightIdentity.UsesOnly variables := by
          constructor
          · exact word_usesOnly_of_append_right leftSplit currentUses.1
          · exact word_usesOnly_of_sameContent rightContent
              (word_usesOnly_of_append_right leftSplit currentUses.1)
        have leftLengthEq :
            leftIdentity.lhs.toList.length = left.toList.length := rfl
        have rightLengthEq :
            rightIdentity.lhs.toList.length = right.toList.length := rfl
        rcases smaller left.toList.length (by omega) leftIdentity
            leftLengthEq leftValid leftUses with
          ⟨leftPieces, leftDecomposition⟩
        rcases smaller right.toList.length (by omega) rightIdentity
            rightLengthEq rightValid rightUses with
          ⟨rightPieces, rightDecomposition⟩
        refine ⟨leftPieces ++ rightPieces, ?_⟩
        refine
          { models := ?_,
            connected := ?_,
            usesOnly := ?_,
            derives := ?_ }
        · intro piece member
          rcases List.mem_append.mp member with member | member
          · exact leftDecomposition.models piece member
          · exact rightDecomposition.models piece member
        · intro piece member
          rcases List.mem_append.mp member with member | member
          · exact leftDecomposition.connected piece member
          · exact rightDecomposition.connected piece member
        · intro piece member
          rcases List.mem_append.mp member with member | member
          · exact leftDecomposition.usesOnly piece member
          · exact rightDecomposition.usesOnly piece member
        · have leftDerives :
              Derives (leftPieces ++ rightPieces) left left' :=
            derives_mono
              (fun piece member =>
                List.mem_append.mpr (Or.inl member))
              leftDecomposition.derives
          have rightDerives :
              Derives (leftPieces ++ rightPieces) right right' :=
            derives_mono
              (fun piece member =>
                List.mem_append.mpr (Or.inr member))
              rightDecomposition.derives
          rw [leftSplit, rightSplit]
          exact Derives.trans
            (Derives.appendRight leftDerives right)
            (Derives.prepend left' rightDerives)
  exact
    Nat.strongRecOn
      (motive := fun length =>
        ∀ (current : Identity Nat),
          current.lhs.toList.length = length →
          current.SatisfiedBy table.semigroup →
          current.UsesOnly variables →
          ∃ pieces,
            ConnectedDecomposition variables current pieces)
      targetLength inductionStatement identity rfl valid uses

private theorem replace_finite_models_by_connected
    (lemma2 : PaperLemma2)
    (basis : List (Identity Nat)) (variables : List Nat)
    (models : Models table.semigroup basis)
    (uses : BasisUsesOnly basis variables) :
    ∃ connectedBasis : List (Identity Nat),
      Models table.semigroup connectedBasis ∧
      (∀ identity, identity ∈ connectedBasis →
        SourceWords.ConnectedIdentity identity) ∧
      BasisUsesOnly connectedBasis variables ∧
      (∀ identity, identity ∈ basis →
        Derives connectedBasis identity.lhs identity.rhs) := by
  classical
  induction basis with
  | nil =>
      exact ⟨[], by simp [Models], by simp, by simp [BasisUsesOnly], by simp⟩
  | cons identity rest ih =>
      have identityValid : identity.SatisfiedBy table.semigroup :=
        models identity (by simp)
      have identityUses : identity.UsesOnly variables :=
        uses identity (by simp)
      have restModels : Models table.semigroup rest := by
        intro current member
        exact models current (by simp [member])
      have restUses : BasisUsesOnly rest variables := by
        intro current member
        exact uses current (by simp [member])
      rcases exists_connected_decomposition lemma2 identity variables
          identityValid identityUses with
        ⟨identityPieces, identityDecomposition⟩
      rcases ih restModels restUses with
        ⟨restPieces, restModels', restConnected, restUses', restDerives⟩
      refine ⟨identityPieces ++ restPieces, ?_, ?_, ?_, ?_⟩
      · intro current member
        rcases List.mem_append.mp member with member | member
        · exact identityDecomposition.models current member
        · exact restModels' current member
      · intro current member
        rcases List.mem_append.mp member with member | member
        · exact identityDecomposition.connected current member
        · exact restConnected current member
      · intro current member
        rcases List.mem_append.mp member with member | member
        · exact identityDecomposition.usesOnly current member
        · exact restUses' current member
      · intro current member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact derives_mono
            (fun piece pieceMember =>
              List.mem_append.mpr (Or.inl pieceMember))
            identityDecomposition.derives
        · exact derives_mono
            (fun piece pieceMember =>
              List.mem_append.mpr (Or.inr pieceMember))
            (restDerives current member)

/-- The paper's Lemma 3, including the finite variable bound required in
Theorem 8, follows from the ordered splitting property of Lemma 2. -/
theorem paperLemma3FiniteReduction_of_paperLemma2
    (lemma2 : PaperLemma2) :
    PaperLemma3FiniteReduction := by
  intro basis basisFor
  let variables := basisVariables basis
  rcases replace_finite_models_by_connected lemma2 basis variables
      basisFor.1 (basis_usesOnly_basisVariables basis) with
    ⟨connectedBasis, connectedModels, connected, connectedUses,
      sourceDerives⟩
  have connectedBasisFor : BasisFor table.semigroup connectedBasis :=
    basisFor.replace connectedModels sourceDerives
  refine ⟨connectedBasis, connectedBasisFor, connected, ?_⟩
  intro identity member
  exact (connectedUses identity member).usesAtMost

/-- Lemma 3 is now unconditional because Lemma 2 is proved in
`Nonfinite/LeeL/OrderedSplit.lean`. -/
theorem paperLemma3FiniteReduction :
    PaperLemma3FiniteReduction :=
  paperLemma3FiniteReduction_of_paperLemma2 paperLemma2

/-! ## Zhang--Luo Lemma 4 -/

def lemma4Left : Word Nat := ⟨0, [1, 1, 0]⟩

def lemma4Right₁ : Word Nat := ⟨0, [1, 0, 1, 0]⟩

def lemma4Right₂ : Word Nat := ⟨0, [1, 0, 1]⟩

def lemma4Right₃ : Word Nat := ⟨1, [0, 1, 0]⟩

def lemma4Right₄ : Word Nat := ⟨0, [0, 1, 1]⟩

def lemma4Right₅ : Word Nat := ⟨1, [1, 0, 0]⟩

private def lemma4Valuation (letter : Nat) : Fin 6 :=
  if letter = 0 then 5 else if letter = 1 then 4 else 0

theorem eval_lemma4Left :
    table.semigroup.eval lemma4Valuation lemma4Left = (1 : Fin 6) := by
  decide

theorem eval_lemma4Right₁ :
    table.semigroup.eval lemma4Valuation lemma4Right₁ = (0 : Fin 6) := by
  decide

theorem eval_lemma4Right₂ :
    table.semigroup.eval lemma4Valuation lemma4Right₂ = (0 : Fin 6) := by
  decide

theorem eval_lemma4Right₃ :
    table.semigroup.eval lemma4Valuation lemma4Right₃ = (0 : Fin 6) := by
  decide

theorem eval_lemma4Right₄ :
    table.semigroup.eval lemma4Valuation lemma4Right₄ = (3 : Fin 6) := by
  decide

theorem eval_lemma4Right₅ :
    table.semigroup.eval lemma4Valuation lemma4Right₅ = (2 : Fin 6) := by
  decide

theorem paperLemma4_right₁ :
    ¬(Identity.mk lemma4Left lemma4Right₁).SatisfiedBy table.semigroup := by
  intro valid
  have equality := valid lemma4Valuation
  change table.semigroup.eval lemma4Valuation lemma4Left =
    table.semigroup.eval lemma4Valuation lemma4Right₁ at equality
  rw [eval_lemma4Left, eval_lemma4Right₁] at equality
  have distinct : (1 : Fin 6) ≠ 0 := by decide
  exact distinct equality

theorem paperLemma4_right₂ :
    ¬(Identity.mk lemma4Left lemma4Right₂).SatisfiedBy table.semigroup := by
  intro valid
  have equality := valid lemma4Valuation
  change table.semigroup.eval lemma4Valuation lemma4Left =
    table.semigroup.eval lemma4Valuation lemma4Right₂ at equality
  rw [eval_lemma4Left, eval_lemma4Right₂] at equality
  have distinct : (1 : Fin 6) ≠ 0 := by decide
  exact distinct equality

theorem paperLemma4_right₃ :
    ¬(Identity.mk lemma4Left lemma4Right₃).SatisfiedBy table.semigroup := by
  intro valid
  have equality := valid lemma4Valuation
  change table.semigroup.eval lemma4Valuation lemma4Left =
    table.semigroup.eval lemma4Valuation lemma4Right₃ at equality
  rw [eval_lemma4Left, eval_lemma4Right₃] at equality
  have distinct : (1 : Fin 6) ≠ 0 := by decide
  exact distinct equality

theorem paperLemma4_right₄ :
    ¬(Identity.mk lemma4Left lemma4Right₄).SatisfiedBy table.semigroup := by
  intro valid
  have equality := valid lemma4Valuation
  change table.semigroup.eval lemma4Valuation lemma4Left =
    table.semigroup.eval lemma4Valuation lemma4Right₄ at equality
  rw [eval_lemma4Left, eval_lemma4Right₄] at equality
  have distinct : (1 : Fin 6) ≠ 3 := by decide
  exact distinct equality

theorem paperLemma4_right₅ :
    ¬(Identity.mk lemma4Left lemma4Right₅).SatisfiedBy table.semigroup := by
  intro valid
  have equality := valid lemma4Valuation
  change table.semigroup.eval lemma4Valuation lemma4Left =
    table.semigroup.eval lemma4Valuation lemma4Right₅ at equality
  rw [eval_lemma4Left, eval_lemma4Right₅] at equality
  have distinct : (1 : Fin 6) ≠ 2 := by decide
  exact distinct equality

def InPOrQ (n : Nat) (word : Word Nat) : Prop :=
  InP n word ∨ InQ n word

/-- Zhang--Luo Lemma 5 in the fixed alphabet used by `p`, `q`, `P`, and `Q`.
It is stated separately because the paper's proof of Lemma 6 uses it.

This is the first remaining completion obligation. -/
def PaperLemma5 : Prop :=
  ∀ (n : Nat) (identity : Identity Nat),
    2 ≤ n →
    identity.SatisfiedBy table.semigroup →
    InP n identity.lhs →
    InPOrQ n identity.rhs

private theorem valid_projection_equivalent
    {n : Nat} {identity : Identity Nat}
    (valid : identity.SatisfiedBy table.semigroup) :
    BlockCombinatorics.ProjectionEquivalent n
      identity.lhs.toList identity.rhs.toList := by
  refine ⟨?_, ?_, ?_⟩
  · have equality :=
      valid (fun letter =>
        BlockCombinatorics.colorValue (decide (letter ≠ 0)))
    rw [BlockCombinatorics.eval_projection,
      BlockCombinatorics.eval_projection] at equality
    exact equality
  · intro i _
    have equality :=
      valid (fun letter =>
        BlockCombinatorics.colorValue (decide (letter = i + 1)))
    rw [BlockCombinatorics.eval_projection,
      BlockCombinatorics.eval_projection] at equality
    exact equality
  · intro i _
    have equality :=
      valid (fun letter =>
        BlockCombinatorics.colorValue
          (decide (letter = i + 1 ∨ letter = i + 2)))
    rw [BlockCombinatorics.eval_projection,
      BlockCombinatorics.eval_projection] at equality
    exact equality

/-- All semigroup-specific work in Lemma 5 reduces to the explicit finite
projection kernel `BlockCombinatorics.Lemma5Combinatorics`. -/
theorem paperLemma5_of_combinatorics
    (combinatorics : BlockCombinatorics.Lemma5Combinatorics) :
    PaperLemma5 := by
  intro n identity atLeastTwo valid leftInP
  have absence :
      ∀ letter,
        identity.lhs.toList.count letter = 0 ↔
          identity.rhs.toList.count letter = 0 :=
    fun letter => valid_identity_preserves_absence valid letter
  have simplicity :
      ∀ letter,
        identity.lhs.toList.count letter = 1 ↔
          identity.rhs.toList.count letter = 1 :=
    fun letter => valid_identity_preserves_simplicity valid letter
  have result :=
    combinatorics n identity.lhs.toList identity.rhs.toList
      atLeastTwo leftInP absence simplicity
      (valid_projection_equivalent valid)
  rcases result with rightInP | rightInQ
  · exact Or.inl rightInP
  · exact Or.inr (by
      simpa [InQ, InP, ListInQ, Word.toList_reverse] using rightInQ)

theorem paperLemma5_of_mateRigidity
    (rigidity : BlockCombinatorics.MateRigidity) :
    PaperLemma5 :=
  paperLemma5_of_combinatorics
    (BlockCombinatorics.lemma5Combinatorics_of_mateRigidity rigidity)

theorem paperLemma5 : PaperLemma5 :=
  paperLemma5_of_mateRigidity BlockCombinatorics.mateRigidity

/-- The only orientation-specific combinatorial assertion needed after
Lemma 5. It is the core of Zhang--Luo Lemma 6: a connected rewrite using at
most `n` variables cannot turn a contextual `P_n` word into a `Q_n` word.

All contextual-substitution bookkeeping and the deduction from Lemma 5 are
proved below. -/
def ConnectedOrientationExclusion : Prop :=
  ∀ (n : Nat) (identity : Identity Nat)
      (pre post : List Nat) (substitution : Nat → Word Nat),
    2 ≤ n →
    SourceWords.ConnectedIdentity identity →
    identity.SatisfiedBy table.semigroup →
    identity.UsesAtMost n →
    ListInP n
      (pre ++ (identity.lhs.bind substitution).toList ++ post) →
    ¬ListInQ n
      (pre ++ (identity.rhs.bind substitution).toList ++ post)

/-- All semigroup-specific content of the orientation exclusion is discharged
by Lemma 1. The remaining obligation is exactly the pure contextual word
statement `BlockCombinatorics.OrientationCombinatorics`. -/
theorem connectedOrientationExclusion_of_combinatorics
    (combinatorics : BlockCombinatorics.OrientationCombinatorics) :
    ConnectedOrientationExclusion := by
  intro n identity pre post substitution atLeastTwo connected valid uses
    sourceInP targetInQ
  exact combinatorics n identity pre post substitution atLeastTwo connected
    (valid_identity_sameContent valid)
    (fun letter => valid_identity_simple_iff valid letter)
    uses sourceInP targetInQ

/-- Zhang--Luo Lemma 6, with empty external contexts represented by lists and
endomorphisms represented by nonempty-word substitutions.  `UsesAtMost n`
implies the source hypothesis that each side has at most `n` content letters.

This direct statement is retained as a source-faithful interface. Below it is
derived from Lemma 5 plus the smaller orientation-exclusion obligation. -/
def PaperLemma6 : Prop :=
  ∀ (n : Nat) (identity : Identity Nat)
      (pre post : List Nat) (substitution : Nat → Word Nat),
    2 ≤ n →
    SourceWords.ConnectedIdentity identity →
    identity.SatisfiedBy table.semigroup →
    identity.UsesAtMost n →
    ListInP n
      (pre ++ (identity.lhs.bind substitution).toList ++ post) →
    ListInP n
      (pre ++ (identity.rhs.bind substitution).toList ++ post)

/-- Lemma 6 follows from the `P_n ∪ Q_n` rigidity of Lemma 5 and the sharply
isolated connected-orientation exclusion. -/
theorem paperLemma6_of_lemma5_and_orientationExclusion
    (lemma5 : PaperLemma5)
    (orientation : ConnectedOrientationExclusion) :
    PaperLemma6 := by
  intro n identity pre post substitution atLeastTwo connected valid uses
    sourceInP
  let contextual :=
    ContextWords.identity identity pre post substitution
  have contextualValid :
      contextual.SatisfiedBy table.semigroup :=
    ContextWords.identity_valid valid pre post substitution
  have contextualLhsInP : InP n contextual.lhs :=
    (ContextWords.lhs_inP_iff n identity pre post substitution).mpr
      sourceInP
  rcases lemma5 n contextual atLeastTwo contextualValid contextualLhsInP with
    targetInP | targetInQ
  · exact
      (ContextWords.rhs_inP_iff n identity pre post substitution).mp
        targetInP
  · have targetListInQ :=
      (ContextWords.rhs_inQ_iff n identity pre post substitution).mp
        targetInQ
    exact False.elim
      (orientation n identity pre post substitution atLeastTwo connected
        valid uses sourceInP targetListInQ)

theorem paperLemma6_of_orientationCombinatorics
    (combinatorics : BlockCombinatorics.OrientationCombinatorics) :
    PaperLemma6 :=
  paperLemma6_of_lemma5_and_orientationExclusion paperLemma5
    (connectedOrientationExclusion_of_combinatorics combinatorics)

theorem paperLemma6_of_orientationTransitionKernel
    (kernel : BlockCombinatorics.OrientationTransitionKernel) :
    PaperLemma6 :=
  paperLemma6_of_orientationCombinatorics
    (BlockCombinatorics.orientationCombinatorics_of_transitionKernel kernel)

theorem paperLemma6_contextuallyEquivalent
    (lemma6 : PaperLemma6)
    {n : Nat} {identity : Identity Nat}
    (atLeastTwo : 2 ≤ n)
    (connected : SourceWords.ConnectedIdentity identity)
    (valid : identity.SatisfiedBy table.semigroup)
    (uses : identity.UsesAtMost n) :
    ContextuallyEquivalentInP n identity.lhs identity.rhs := by
  intro pre post substitution
  constructor
  · exact lemma6 n identity pre post substitution atLeastTwo connected
      valid uses
  · exact lemma6 n (swapIdentity identity) pre post substitution atLeastTwo
      (swapIdentity_connected connected) (swapIdentity_satisfiedBy valid)
      (swapIdentity_usesAtMost uses)

private theorem bind_singleton_identity (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  rw [Word.toList_bind]
  induction word.toList with
  | nil =>
      cases word with
      | mk head tail =>
          simp [Word.toList] at *
  | cons head tail ih =>
      simp only [List.flatMap_cons, Word.toList_singleton,
        List.singleton_append]
      change List.flatMap (fun x => [x]) tail = tail at ih
      exact congrArg (List.cons head) ih

/-- The deduction-sequence induction in Theorem 8, now using the exact
connected-identity hypothesis of Lemma 6 instead of the stronger placeholder
from `LeeLNonfinite`. -/
theorem obstruction_underivable_of_paperLemma6
    (lemma6 : PaperLemma6)
    (bound : Nat) (basis : List (Identity Nat))
    (models : Models table.semigroup basis)
    (bounded : BasisUsesAtMost basis bound)
    (connected :
      ∀ identity, identity ∈ basis →
        SourceWords.ConnectedIdentity identity) :
    ¬Derives basis (obstruction bound).lhs (obstruction bound).rhs := by
  let n := max 2 bound
  have nAtLeastTwo : 2 ≤ n := Nat.le_max_left 2 bound
  have boundLeN : bound ≤ n := Nat.le_max_right 2 bound
  intro derivation
  have axiomPreserves :
      ∀ identity, identity ∈ basis →
        ContextuallyEquivalentInP n identity.lhs identity.rhs := by
    intro identity member
    exact paperLemma6_contextuallyEquivalent lemma6 nAtLeastTwo
      (connected identity member) (models identity member)
      (Identity.UsesAtMost.mono (bounded identity member) boundLeN)
  have invariant :=
    SemigroupBasis.Examples.LeeL.Derives.contextuallyEquivalentInP
      axiomPreserves derivation
      ([] : List Nat) ([] : List Nat) Word.singleton
  have invariant' : InP n (p n) ↔ InP n (q n) := by
    simpa [obstruction, n, InP, bind_singleton_identity] using invariant
  exact q_not_inP nAtLeastTwo (invariant'.mp (p_inP (by omega)))

/-- Formal Zhang--Luo Theorem 8 from the two exact terminal obligations.

This theorem is intentionally conditional: it records that all finite-basis
and deduction-sequence bookkeeping is complete. Lemma 3 is now proved; this
generic entry point still accepts it explicitly for reuse and comparison with
the source proof. -/
theorem nonfinitelyBased_of_paperLemmas
    (lemma3 : PaperLemma3FiniteReduction)
    (lemma6 : PaperLemma6) :
    NonfinitelyBased table.semigroup := by
  rintro ⟨basis, basisFor⟩
  let bound := (basisVariables basis).length
  rcases lemma3 basis basisFor with
    ⟨connectedBasis, connectedBasisFor, connected, bounded⟩
  have underivable :=
    obstruction_underivable_of_paperLemma6 lemma6 bound connectedBasis
      connectedBasisFor.1 bounded connected
  exact underivable
    (connectedBasisFor.2 (obstruction bound) (obstruction_valid bound))

/-- Source-faithful compatibility theorem: Zhang--Luo Theorem 8 follows from
the exact statements of Lemmas 2 and 6. Lemma 2 is now supplied
unconditionally by `paperLemma2`. -/
theorem nonfinitelyBased_of_paperLemma2_and_paperLemma6
    (lemma2 : PaperLemma2)
    (lemma6 : PaperLemma6) :
    NonfinitelyBased table.semigroup :=
  nonfinitelyBased_of_paperLemmas
    (paperLemma3FiniteReduction_of_paperLemma2 lemma2) lemma6

/-- With ordered splitting discharged, a proof of Lemma 6 alone closes the
nonfinite-basis theorem. -/
theorem nonfinitelyBased_of_paperLemma6
    (lemma6 : PaperLemma6) :
    NonfinitelyBased table.semigroup :=
  nonfinitelyBased_of_paperLemmas paperLemma3FiniteReduction lemma6

/-- Minimal machine-checkable completion certificate.

The first field is exactly Zhang--Luo Lemma 5. The second is the
orientation-exclusion core of Lemma 6. No finite-table, quotient,
idempotent-separation, connected-basis reduction, contextual-substitution,
or deduction-sequence obligation remains in this record. -/
structure CompletionCertificate : Prop where
  pOrQRigidity : PaperLemma5
  connectedOrientation : ConnectedOrientationExclusion

def completionCertificate_of_combinatorialCore
    (core : BlockCombinatorics.CombinatorialCore) :
    CompletionCertificate where
  pOrQRigidity := paperLemma5_of_mateRigidity core.mateRigidity
  connectedOrientation :=
    connectedOrientationExclusion_of_combinatorics core.orientation

/-- The ordered-splitting half is now unconditional. The exact remaining
source frontier is Lemma 5 plus connected orientation exclusion. -/
theorem nonfinitelyBased_of_lemma5_and_orientationExclusion
    (lemma5 : PaperLemma5)
    (orientation : ConnectedOrientationExclusion) :
    NonfinitelyBased table.semigroup :=
  nonfinitelyBased_of_paperLemma2_and_paperLemma6 paperLemma2
    (paperLemma6_of_lemma5_and_orientationExclusion lemma5 orientation)

theorem nonfinitelyBased_of_completionCertificate
    (certificate : CompletionCertificate) :
    NonfinitelyBased table.semigroup :=
  nonfinitelyBased_of_lemma5_and_orientationExclusion
    certificate.pOrQRigidity certificate.connectedOrientation

/-- The complete formal proof now depends on one semantics-free word
certificate. No finite-table or equational-logic assumption remains. -/
theorem nonfinitelyBased_of_combinatorialCore
    (core : BlockCombinatorics.CombinatorialCore) :
    NonfinitelyBased table.semigroup :=
  nonfinitelyBased_of_completionCertificate
    (completionCertificate_of_combinatorialCore core)

theorem nonfinitelyBased_of_orientationCombinatorics
    (combinatorics : BlockCombinatorics.OrientationCombinatorics) :
    NonfinitelyBased table.semigroup :=
  nonfinitelyBased_of_paperLemma6
    (paperLemma6_of_orientationCombinatorics combinatorics)

theorem nonfinitelyBased_of_orientationTransitionKernel
    (kernel : BlockCombinatorics.OrientationTransitionKernel) :
    NonfinitelyBased table.semigroup :=
  nonfinitelyBased_of_paperLemma6
    (paperLemma6_of_orientationTransitionKernel kernel)

/-- The connected orientation exclusion for Lee's semigroup, with the
semantics-free transition kernel discharged in `BlockCombinatorics`. -/
theorem connectedOrientationExclusion : ConnectedOrientationExclusion :=
  connectedOrientationExclusion_of_combinatorics
    BlockCombinatorics.orientationCombinatorics

/-- Unconditional Zhang--Luo Lemma 6 for Lee's semigroup. -/
theorem paperLemma6 : PaperLemma6 :=
  paperLemma6_of_orientationCombinatorics
    BlockCombinatorics.orientationCombinatorics

/-- Lee's six-element semigroup is nonfinitely based. -/
theorem nonfinitelyBased : NonfinitelyBased table.semigroup :=
  nonfinitelyBased_of_paperLemma6 paperLemma6

/-- Nonfinite basability of the exact zero-based Smallsemi catalogue
representative `S6_3843`. -/
theorem s6_3843_nonfinitelyBased : NonfinitelyBased table.semigroup :=
  nonfinitelyBased

end SemigroupBasis.Examples.LeeL
