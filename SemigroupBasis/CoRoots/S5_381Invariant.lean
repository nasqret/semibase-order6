import SemigroupBasis.CoRoots.S5_381Factors
import SemigroupBasis.CoRoots.S5_793Invariant
import SemigroupBasis.Examples.FinalMarkerThree

namespace SemigroupBasis.CoRoots

open SemigroupBasis
open SemigroupBasis.Examples

namespace S5_381Invariant

def oppositeFinalMarkerThree : FiniteTable where
  order := 3
  mul := fun a b => finalMarkerThreeMul b a
  assoc := by decide

private def initialMarkerSeparator (z : Nat) : Nat → Fin 3 :=
  fun letter => if letter = z then 1 else 2

private theorem initialMarkerFold (z : Nat) :
    ∀ (letters : List Nat) (initial : Fin 3),
      letters.foldl
          (fun value letter =>
            finalMarkerThree.semigroup.opposite.mul value
              (initialMarkerSeparator z letter))
          initial =
        if z ∈ letters then 0 else initial
  | [], initial => by simp
  | letter :: rest, initial => by
      simp only [List.foldl_cons]
      rw [initialMarkerFold z rest]
      by_cases letterEq : letter = z
      · subst letter
        simp [initialMarkerSeparator, finalMarkerThree,
          FiniteTable.semigroup, Semigroup.opposite,
          finalMarkerThreeMul]
      · by_cases restMem : z ∈ rest
        · simp [initialMarkerSeparator, letterEq, restMem,
            finalMarkerThree, FiniteTable.semigroup,
            Semigroup.opposite, finalMarkerThreeMul]
        · have zNeLetter : z ≠ letter :=
            fun equality => letterEq equality.symm
          simp only [List.mem_cons, restMem, or_false, zNeLetter, if_false]
          simp [initialMarkerSeparator, letterEq,
            finalMarkerThree, FiniteTable.semigroup,
            Semigroup.opposite, finalMarkerThreeMul]

private theorem initialMarkerEval
    (word : Word Nat) (z : Nat) :
    finalMarkerThree.semigroup.opposite.eval
        (initialMarkerSeparator z) word =
      if z ∈ word.tail then (0 : Fin 3)
      else if word.head = z then (1 : Fin 3) else (2 : Fin 3) := by
  cases word with
  | mk head tail =>
      simp only [Semigroup.eval]
      rw [initialMarkerFold z tail]
      by_cases tailMem : z ∈ tail
      · simp [tailMem]
      · by_cases headEq : head = z
        · subst head
          simp [tailMem, initialMarkerSeparator]
        · simp [tailMem, headEq, initialMarkerSeparator]

private theorem simpleInitial_iff_head_tail
    (word : Word Nat) (z : Nat) :
    S5_107.SimpleInitial word z ↔
      word.head = z ∧ z ∉ word.tail := by
  cases word with
  | mk head tail =>
      by_cases headEq : head = z
      · subst head
        simp [S5_107.SimpleInitial, S5_107.SimpleIn, Word.toList,
          List.count_eq_zero]
      · simp [S5_107.SimpleInitial, headEq]

theorem initialMarkerEval_eq_one_iff
    (word : Word Nat) (z : Nat) :
    finalMarkerThree.semigroup.opposite.eval
        (initialMarkerSeparator z) word = (1 : Fin 3) ↔
      S5_107.SimpleInitial word z := by
  rw [initialMarkerEval, simpleInitial_iff_head_tail]
  by_cases tailMem : z ∈ word.tail
  · simp [tailMem]
  · by_cases headEq : word.head = z
    · simp [tailMem, headEq]
    · simp [tailMem, headEq]

/-- The opposite final-marker factor preserves exactly the optional
globally simple initial variable. -/
theorem oppositeFinalMarkerValid_simpleInitial_iff
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy finalMarkerThree.semigroup.opposite)
    (z : Nat) :
    S5_107.SimpleInitial identity.lhs z ↔
      S5_107.SimpleInitial identity.rhs z := by
  have evaluated := valid (initialMarkerSeparator z)
  constructor
  · intro leftSimple
    have leftOne :
        finalMarkerThree.semigroup.opposite.eval
            (initialMarkerSeparator z) identity.lhs = (1 : Fin 3) :=
      (initialMarkerEval_eq_one_iff identity.lhs z).2 leftSimple
    have rightOne :
        finalMarkerThree.semigroup.opposite.eval
            (initialMarkerSeparator z) identity.rhs = (1 : Fin 3) :=
      evaluated.symm.trans leftOne
    exact
      (initialMarkerEval_eq_one_iff identity.rhs z).1 rightOne
  · intro rightSimple
    have rightOne :
        finalMarkerThree.semigroup.opposite.eval
            (initialMarkerSeparator z) identity.rhs = (1 : Fin 3) :=
      (initialMarkerEval_eq_one_iff identity.rhs z).2 rightSimple
    have leftOne :
        finalMarkerThree.semigroup.opposite.eval
            (initialMarkerSeparator z) identity.lhs = (1 : Fin 3) :=
      evaluated.trans rightOne
    exact
      (initialMarkerEval_eq_one_iff identity.lhs z).1 leftOne

/-- The exact invariant of the `S5_381/S5_610` family. The block component
is the established `S4_71` simple-sequence/last-gap signature; `initial`
records `some head` exactly when that head is globally simple. -/
structure SameSimpleSequenceLastGapInitialSignature
    (left right : Word Nat) : Prop where
  blockTheory :
    (Identity.mk left right).SatisfiedBy
      Generated.S4_71.table.semigroup
  capped :
    ∀ letter,
      S5_107.cappedMultiplicity left letter =
        S5_107.cappedMultiplicity right letter
  simpleSequence :
    ∀ x y,
      S5_793Invariant.SimplePrecedes left x y ↔
        S5_793Invariant.SimplePrecedes right x y
  lastGap :
    ∀ x y,
      S5_793Invariant.MultipleLastBeforeSimple left x y ↔
        S5_793Invariant.MultipleLastBeforeSimple right x y
  initial :
    ∀ letter,
      S5_107.SimpleInitial left letter ↔
        S5_107.SimpleInitial right letter

abbrev sameSignature (left right : Word Nat) : Prop :=
  SameSimpleSequenceLastGapInitialSignature left right

theorem sameSignature_of_factor_valid
    (identity : Identity Nat)
    (blockValid :
      identity.SatisfiedBy Generated.S4_71.table.semigroup)
    (initialValid :
      identity.SatisfiedBy finalMarkerThree.semigroup.opposite) :
    SameSimpleSequenceLastGapInitialSignature
      identity.lhs identity.rhs := by
  have capped :
      ∀ letter,
        S5_107.cappedMultiplicity identity.lhs letter =
          S5_107.cappedMultiplicity identity.rhs letter :=
    fun letter =>
      S5_793Invariant.s4_71Valid_cappedMultiplicity
        identity blockValid letter
  exact
    ⟨blockValid, capped,
      fun x y =>
        S5_793Invariant.s4_71Valid_simplePrecedes
          identity blockValid capped x y,
      fun x y =>
        S5_793Invariant.s4_71Valid_multipleLastBeforeSimple
          identity blockValid capped x y,
      fun letter =>
        oppositeFinalMarkerValid_simpleInitial_iff
          identity initialValid letter⟩

namespace SameSimpleSequenceLastGapInitialSignature

theorem refl (word : Word Nat) :
    SameSimpleSequenceLastGapInitialSignature word word :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ => Iff.rfl,
    fun _ _ => Iff.rfl, fun _ => Iff.rfl⟩

theorem symm {left right : Word Nat}
    (same :
      SameSimpleSequenceLastGapInitialSignature left right) :
    SameSimpleSequenceLastGapInitialSignature right left :=
  ⟨fun valuation => (same.blockTheory valuation).symm,
    fun letter => (same.capped letter).symm,
    fun x y => (same.simpleSequence x y).symm,
    fun x y => (same.lastGap x y).symm,
    fun letter => (same.initial letter).symm⟩

theorem trans {left middle right : Word Nat}
    (first :
      SameSimpleSequenceLastGapInitialSignature left middle)
    (second :
      SameSimpleSequenceLastGapInitialSignature middle right) :
    SameSimpleSequenceLastGapInitialSignature left right :=
  ⟨fun valuation =>
      (first.blockTheory valuation).trans
        (second.blockTheory valuation),
    fun letter =>
      (first.capped letter).trans (second.capped letter),
    fun x y =>
      (first.simpleSequence x y).trans
        (second.simpleSequence x y),
    fun x y =>
      (first.lastGap x y).trans (second.lastGap x y),
    fun letter =>
      (first.initial letter).trans (second.initial letter)⟩

theorem absent {left right : Word Nat}
    (same :
      SameSimpleSequenceLastGapInitialSignature left right)
    (letter : Nat) :
    letter ∉ left.toList ↔ letter ∉ right.toList := by
  rw [← List.count_eq_zero, ← List.count_eq_zero,
    ← S5_107.cappedMultiplicity_eq_zero_iff,
    ← S5_107.cappedMultiplicity_eq_zero_iff,
    same.capped letter]

theorem support {left right : Word Nat}
    (same :
      SameSimpleSequenceLastGapInitialSignature left right)
    (letter : Nat) :
    letter ∈ left.toList ↔ letter ∈ right.toList := by
  simpa using not_congr (same.absent letter)

theorem simple {left right : Word Nat}
    (same :
      SameSimpleSequenceLastGapInitialSignature left right)
    (letter : Nat) :
    S5_107.SimpleIn left letter ↔
      S5_107.SimpleIn right letter := by
  unfold S5_107.SimpleIn
  rw [← S5_107.cappedMultiplicity_eq_one_iff,
    ← S5_107.cappedMultiplicity_eq_one_iff,
    same.capped letter]

theorem toSameFirst {left right : Word Nat}
    (same :
      SameSimpleSequenceLastGapInitialSignature left right)
    (heads : left.head = right.head) :
    S5_793Invariant.SameFirstSimpleLastGapSignature left right :=
  ⟨same.blockTheory, heads, same.capped,
    same.simpleSequence, same.lastGap⟩

end SameSimpleSequenceLastGapInitialSignature

end S5_381Invariant

namespace S5_381

/-- Every derivation from the exact basis preserves the advertised
simple-sequence/last-gap/optional-initial signature. -/
theorem derives_sameSignature
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    S5_381Invariant.SameSimpleSequenceLastGapInitialSignature
      left right := by
  have blockModels :
      Models Generated.S4_71.table.semigroup basis :=
    models_of_finite_checks Generated.S4_71.table (by decide)
  have initialModels :
      Models finalMarkerThree.semigroup.opposite basis :=
    by
      have checked :=
        models_of_finite_checks
          S5_381Invariant.oppositeFinalMarkerThree (by decide)
      simpa [S5_381Invariant.oppositeFinalMarkerThree, finalMarkerThree,
        FiniteTable.semigroup, Semigroup.opposite] using checked
  exact S5_381Invariant.sameSignature_of_factor_valid
    ⟨left, right⟩
    (fun valuation => derivation.sound blockModels valuation)
    (fun valuation => derivation.sound initialModels valuation)

end S5_381

namespace S5_381FamilyInvariant

namespace S5_381

theorem valid_sameSignature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_381.table.semigroup) :
    S5_381Invariant.SameSimpleSequenceLastGapInitialSignature
      identity.lhs identity.rhs :=
  S5_381Invariant.sameSignature_of_factor_valid identity
    (S5_381Factors.S5_381.valid_s4_71 identity valid)
    (S5_381Factors.S5_381.valid_initialMarker identity valid)

end S5_381

namespace S5_610

theorem valid_sameSignature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_610.table.semigroup) :
    S5_381Invariant.SameSimpleSequenceLastGapInitialSignature
      identity.lhs identity.rhs :=
  S5_381Invariant.sameSignature_of_factor_valid identity
    (S5_381Factors.S5_610.valid_s4_71 identity valid)
    (S5_381Factors.S5_610.valid_initialMarker identity valid)

end S5_610

end S5_381FamilyInvariant

end SemigroupBasis.CoRoots
