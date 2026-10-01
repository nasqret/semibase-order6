import SemigroupBasis.CoRoots.Order6Day7.S2_2.SeedS5_415ClosedReturnReplay
import SemigroupBasis.DerivationQuotient
import SemigroupBasis.Regular

/-!
# Rank040: genuine cut rotation, regular-cut product closure, and exchange

This implements parts of msg-0358's exposure-indexed invariant. A cut is
an actual factorization, and rotation MOVES the cut. Product closure at a
regular cut is proved using its two explicit inverse witnesses; it is not
obtained by canceling a prefix from an arbitrary derivation.

The frozen triangle exchange xyxzyz = x²y²z² absorbs every product of its
three nonempty blocks, including the specified odd loop z. All statements
are unrestricted within their stated domains. The general all-exposures
ClosedReturnDerivation theorem is NOT assumed or asserted here.

The term quotient is used only to reify equalities proved from the frozen
laws back into Derives. No factor-separation or completeness field occurs.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.ExposureReplay

open SemigroupBasis
open ClosedReturnReplay

section Models

variable {S : Type u} (G : Semigroup S) (models : Models G Rank040.basis)

include models

theorem modelSquareIdempotent (value : S) :
    G.IsIdempotent (G.mul value value) := by
  have expansion := Derives.sound models
    (BrandtParityBridge.derivesPairExpansion (Word.singleton 0)) (fun _ => value)
  change G.mul value value = G.mul (G.mul (G.mul value value) value) value at expansion
  simpa only [Semigroup.IsIdempotent, G.assoc] using expansion.symm

theorem modelSquaresCommute (first second : S) :
    G.mul (G.mul first first) (G.mul second second) =
      G.mul (G.mul second second) (G.mul first first) := by
  have commute := Derives.sound models
    (BrandtParityBridge.derivesSquareCommutation (Word.singleton 0) (Word.singleton 1))
    (fun letter => if letter = 0 then first else second)
  simpa only [Semigroup.eval_append, Semigroup.eval_singleton] using commute

theorem modelIdempotentsCommute : G.IdempotentsCommute := by
  intro first second firstIdempotent secondIdempotent
  change G.mul first first = first at firstIdempotent
  change G.mul second second = second at secondIdempotent
  have commute := modelSquaresCommute G models first second
  simpa only [firstIdempotent, secondIdempotent] using commute

theorem modelGuardedProductSquare (first second : S) :
    G.mul (G.mul first first) (G.mul second second) =
      G.mul (G.mul (G.mul first second) (G.mul first second))
        (G.mul (G.mul first first) (G.mul second second)) := by
  have inserted := Derives.sound models
    (derivesGuardedProductSquare (Word.singleton 0) (Word.singleton 1))
    (fun letter => if letter = 0 then first else second)
  simpa only [Semigroup.eval_append, Semigroup.eval_singleton] using inserted

/-- The exact idempotent corner test. Both flanking factors have actual
inverse witnesses, and no cancellativity is being assumed. -/
theorem regularSandwichInsertionIff
    {left leftInverse right rightInverse inserted : S}
    (leftRegular : G.IsInverse left leftInverse)
    (rightRegular : G.IsInverse right rightInverse)
    (insertedIdempotent : G.IsIdempotent inserted) :
    G.mul left right = G.mul (G.mul left inserted) right ↔
      G.mul (G.mul leftInverse left) (G.mul right rightInverse) =
        G.mul (G.mul (G.mul leftInverse left) (G.mul right rightInverse)) inserted := by
  let source := G.mul leftInverse left
  let range := G.mul right rightInverse
  have leftSource : G.mul left source = left := by
    simpa only [source, G.assoc] using leftRegular.1
  have rangeRight : G.mul range right = right := rightRegular.1
  have moveRange : G.mul inserted range = G.mul range inserted :=
    modelIdempotentsCommute G models insertedIdempotent rightRegular.mul_idempotent
  change G.mul left right = G.mul (G.mul left inserted) right ↔
    G.mul source range = G.mul (G.mul source range) inserted
  constructor
  · intro absorbs
    calc
      G.mul source range =
          G.mul (G.mul leftInverse (G.mul left right)) rightInverse := by
            simp only [source, range, G.assoc]
      _ = G.mul (G.mul leftInverse (G.mul (G.mul left inserted) right)) rightInverse :=
        congrArg (fun middle => G.mul (G.mul leftInverse middle) rightInverse) absorbs
      _ = G.mul source (G.mul inserted range) := by
        simp only [source, range, G.assoc]
      _ = G.mul source (G.mul range inserted) := congrArg (G.mul source) moveRange
      _ = G.mul (G.mul source range) inserted := (G.assoc source range inserted).symm
  · intro corner
    calc
      G.mul left right = G.mul (G.mul left (G.mul source range)) right := by
        rw [← G.assoc left source range, leftSource, G.assoc left range right, rangeRight]
      _ = G.mul (G.mul left (G.mul (G.mul source range) inserted)) right :=
        congrArg (fun middle => G.mul (G.mul left middle) right) corner
      _ = G.mul (G.mul left (G.mul source (G.mul range inserted))) right := by
        rw [G.assoc source range inserted]
      _ = G.mul (G.mul left (G.mul source (G.mul inserted range))) right :=
        congrArg (fun middle => G.mul (G.mul left (G.mul source middle)) right) moveRange.symm
      _ = G.mul (G.mul (G.mul left source) inserted) (G.mul range right) := by
        simp only [G.assoc]
      _ = G.mul (G.mul left inserted) right := by rw [leftSource, rangeRight]

/-- Product closure at a regular exposed cut, obtained by commuting the
three actual square idempotents in its inverse-witness corner. -/
theorem regularSandwichProduct
    {left leftInverse right rightInverse first second : S}
    (leftRegular : G.IsInverse left leftInverse)
    (rightRegular : G.IsInverse right rightInverse)
    (firstAbsorbs : G.mul left right = G.mul (G.mul left (G.mul first first)) right)
    (secondAbsorbs : G.mul left right = G.mul (G.mul left (G.mul second second)) right) :
    G.mul left right =
      G.mul (G.mul left (G.mul (G.mul first second) (G.mul first second))) right := by
  let corner := G.mul (G.mul leftInverse left) (G.mul right rightInverse)
  let firstSquare := G.mul first first
  let secondSquare := G.mul second second
  let productSquare := G.mul (G.mul first second) (G.mul first second)
  have firstCorner : corner = G.mul corner firstSquare :=
    (regularSandwichInsertionIff G models leftRegular rightRegular
      (modelSquareIdempotent G models first)).mp firstAbsorbs
  have secondCorner : corner = G.mul corner secondSquare :=
    (regularSandwichInsertionIff G models leftRegular rightRegular
      (modelSquareIdempotent G models second)).mp secondAbsorbs
  have bank : corner = G.mul corner (G.mul firstSquare secondSquare) := by
    calc
      corner = G.mul corner secondSquare := secondCorner
      _ = G.mul (G.mul corner firstSquare) secondSquare :=
        congrArg (fun value => G.mul value secondSquare) firstCorner
      _ = G.mul corner (G.mul firstSquare secondSquare) := G.assoc _ _ _
  have moveBank :
      G.mul productSquare (G.mul firstSquare secondSquare) =
        G.mul (G.mul firstSquare secondSquare) productSquare := by
    calc
      G.mul productSquare (G.mul firstSquare secondSquare) =
          G.mul (G.mul productSquare firstSquare) secondSquare := (G.assoc _ _ _).symm
      _ = G.mul (G.mul firstSquare productSquare) secondSquare :=
        congrArg (fun value => G.mul value secondSquare)
          (modelSquaresCommute G models (G.mul first second) first)
      _ = G.mul firstSquare (G.mul productSquare secondSquare) := G.assoc _ _ _
      _ = G.mul firstSquare (G.mul secondSquare productSquare) :=
        congrArg (G.mul firstSquare)
          (modelSquaresCommute G models (G.mul first second) second)
      _ = G.mul (G.mul firstSquare secondSquare) productSquare := (G.assoc _ _ _).symm
  apply (regularSandwichInsertionIff G models leftRegular rightRegular
    (modelSquareIdempotent G models (G.mul first second))).mpr
  change corner = G.mul corner productSquare
  calc
    corner = G.mul corner (G.mul firstSquare secondSquare) := bank
    _ = G.mul corner (G.mul productSquare (G.mul firstSquare secondSquare)) :=
      congrArg (G.mul corner) (modelGuardedProductSquare G models first second)
    _ = G.mul corner (G.mul (G.mul firstSquare secondSquare) productSquare) :=
      congrArg (G.mul corner) moveBank
    _ = G.mul (G.mul corner (G.mul firstSquare secondSquare)) productSquare :=
      (G.assoc _ _ _).symm
    _ = G.mul corner productSquare :=
      congrArg (fun value => G.mul value productSquare) bank.symm

end Models

/-- Proof-relevant regularity FROM the frozen rank040 laws. -/
structure InverseWitness (word : Word Nat) where
  inverse : Word Nat
  word_inverse_word : Derives Rank040.basis ((word ++ inverse) ++ word) word
  inverse_word_inverse : Derives Rank040.basis ((inverse ++ word) ++ inverse) inverse

theorem InverseWitness.model {word : Word Nat} (witness : InverseWitness word)
    {S : Type u} (G : Semigroup S) (models : Models G Rank040.basis)
    (valuation : Nat → S) :
    G.IsInverse (G.eval valuation word) (G.eval valuation witness.inverse) := by
  constructor
  · simpa only [Semigroup.eval_append] using Derives.sound models witness.word_inverse_word valuation
  · simpa only [Semigroup.eval_append] using Derives.sound models witness.inverse_word_inverse valuation

/-- A genuine inner inverse gives a two-sided inverse by the standard
`inverse word inverse` construction, using only contextual derivations. -/
def inverseWitnessOfInner (word inner : Word Nat)
    (reduces : Derives Rank040.basis ((word ++ inner) ++ word) word) :
    InverseWitness word where
  inverse := (inner ++ word) ++ inner
  word_inverse_word := by
    have first : Derives Rank040.basis
        ((word ++ ((inner ++ word) ++ inner)) ++ word) ((word ++ inner) ++ word) := by
      simpa only [Word.append_assoc] using Derives.appendRight reduces (inner ++ word)
    exact first.trans reduces
  inverse_word_inverse := by
    have second := Derives.appendRight (Derives.prepend inner reduces) inner
    have first : Derives Rank040.basis
        ((((inner ++ word) ++ inner) ++ word) ++ ((inner ++ word) ++ inner))
        ((inner ++ ((word ++ inner) ++ word)) ++ inner) := by
      simpa only [Word.append_assoc] using
        Derives.appendRight (Derives.prepend inner reduces) ((inner ++ word) ++ inner)
    exact first.trans second

def squareInverseWitness (word : Word Nat) : InverseWitness (word ++ word) := by
  have contract : Derives Rank040.basis ((word ++ word) ++ (word ++ word)) (word ++ word) := by
    simpa only [Word.append_assoc] using (BrandtParityBridge.derivesPairExpansion word).symm
  have inverse := (Derives.appendRight contract (word ++ word)).trans contract
  exact ⟨word ++ word, inverse, inverse⟩

def sandwichInverseWitness (first second : Word Nat) :
    InverseWitness ((first ++ second) ++ first) :=
  inverseWitnessOfInner ((first ++ second) ++ first) second (by
    simpa only [Word.append_assoc] using
      (BrandtParityBridge.derivesJointSandwichExpansion first second).symm)

theorem InverseWitness.termInverse {word : Word Nat} (witness : InverseWitness word) :
    (termSemigroup Rank040.basis).IsInverse
      (termClass Rank040.basis word) (termClass Rank040.basis witness.inverse) := by
  simpa only [termSemigroup_eval_singletonClass] using
    witness.model (termSemigroup Rank040.basis) (termSemigroup_models Rank040.basis)
      (fun letter => termClass Rank040.basis (Word.singleton letter))

/-- Products of explicit regular blocks remain regular. -/
def InverseWitness.append {first second : Word Nat}
    (firstWitness : InverseWitness first) (secondWitness : InverseWitness second) :
    InverseWitness (first ++ second) where
  inverse := secondWitness.inverse ++ firstWitness.inverse
  word_inverse_word := by
    have inverse := Semigroup.IdempotentsCommute.mul_inverse
      (modelIdempotentsCommute (termSemigroup Rank040.basis) (termSemigroup_models Rank040.basis))
      firstWitness.termInverse secondWitness.termInverse
    apply (termClass_eq_iff_derives Rank040.basis).mp
    simpa only [termSemigroup_mul_termClass] using inverse.1
  inverse_word_inverse := by
    have inverse := Semigroup.IdempotentsCommute.mul_inverse
      (modelIdempotentsCommute (termSemigroup Rank040.basis) (termSemigroup_models Rank040.basis))
      firstWitness.termInverse secondWitness.termInverse
    apply (termClass_eq_iff_derives Rank040.basis).mp
    simpa only [termSemigroup_mul_termClass] using inverse.2

def CutAbsorbs (left right loop : Word Nat) : Prop :=
  Derives Rank040.basis (left ++ right) ((left ++ (loop ++ loop)) ++ right)

/-- Actual Derives product closure at ANY cut with two explicit regular
flanks. This does not assert that all graph cuts have such witnesses. -/
theorem cutAbsorbsProduct
    {left right first second : Word Nat}
    (leftWitness : InverseWitness left) (rightWitness : InverseWitness right)
    (firstAbsorbs : CutAbsorbs left right first)
    (secondAbsorbs : CutAbsorbs left right second) :
    CutAbsorbs left right (first ++ second) := by
  apply (derives_iff_valid_in_all_models Rank040.basis _ _).mpr
  intro S G models valuation
  have firstEquality := Derives.sound models firstAbsorbs valuation
  have secondEquality := Derives.sound models secondAbsorbs valuation
  simp only [Semigroup.eval_append] at firstEquality secondEquality ⊢
  exact regularSandwichProduct G models (leftWitness.model G models valuation)
    (rightWitness.model G models valuation) firstEquality secondEquality

/-- Actual cut data, including the empty-prefix and empty-suffix boundaries. -/
structure Exposure (word : Word Nat) where
  before : List Nat
  after : List Nat
  partition : word.toList = before ++ after

def Exposure.insert {word : Word Nat} (cut : Exposure word) (loop : Word Nat) : Word Nat :=
  ChainReplay.Context.wrap cut.before (loop ++ loop) cut.after

def Exposure.Absorbs {word : Word Nat} (cut : Exposure word) (loop : Word Nat) : Prop :=
  Derives Rank040.basis word (cut.insert loop)

def Exposure.advance {word : Word Nat} (cut : Exposure word)
    (segment : Word Nat) (rest : List Nat) (split : cut.after = segment.toList ++ rest) :
    Exposure word where
  before := cut.before ++ segment.toList
  after := rest
  partition := by rw [cut.partition, split, List.append_assoc]

/-- Rotation is the exact identity (pq)²p = p(qp)² at the exposed word
segment p. It changes the cut, not just the spelling of the loop. -/
theorem Exposure.rotatedInsert_eq
    {word : Word Nat} (cut : Exposure word) (first second : Word Nat)
    (rest : List Nat) (split : cut.after = first.toList ++ rest) :
    cut.insert (first ++ second) =
      (cut.advance first rest split).insert (second ++ first) := by
  apply Word.toList_injective
  simp only [Exposure.insert, ChainReplay.Context.wrap_toList, Word.toList_append,
    Exposure.advance, split, List.append_assoc]

theorem Exposure.absorbsRotation_iff
    {word : Word Nat} (cut : Exposure word) (first second : Word Nat)
    (rest : List Nat) (split : cut.after = first.toList ++ rest) :
    cut.Absorbs (first ++ second) ↔
      (cut.advance first rest split).Absorbs (second ++ first) := by
  unfold Exposure.Absorbs
  rw [cut.rotatedInsert_eq first second rest split]

theorem headRotation_iff (first second after : Word Nat) :
    SquareAbsorbs (first ++ after) (first ++ second) ↔
      CutAbsorbs first after (second ++ first) := by
  simp only [SquareAbsorbs, CutAbsorbs, Word.append_assoc]

/-- The sandwich law supplies a genuine non-head cut generator. -/
theorem sandwichRotatedAbsorbs (first second : Word Nat) :
    CutAbsorbs first (second ++ first) (second ++ first) :=
  (headRotation_iff first second (second ++ first)).mp
    (by simpa only [Word.append_assoc] using sandwichSquareAbsorbs first second)

private def instantiateThree (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

def triangleWord (first second third : Word Nat) : Word Nat :=
  ((((first ++ second) ++ first) ++ third) ++ second) ++ third

def threeSquareBank (first second third : Word Nat) : Word Nat :=
  ((first ++ first) ++ (second ++ second)) ++ (third ++ third)

theorem derivesTriangleExchange (first second third : Word Nat) :
    Derives Rank040.basis (triangleWord first second third) (threeSquareBank first second third) := by
  have primitive : Derives Rank040.basis
      (Word.mk 0 [1, 0, 2, 1, 2]) (Word.mk 0 [0, 1, 1, 2, 2]) :=
    Derives.fromBasis (e := law14) (by simp [Rank040.basis])
  have substituted := Derives.subst primitive (instantiateThree first second third)
  simpa [triangleWord, threeSquareBank, instantiateThree,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Pure finite-product syntax over a list of nonempty block generators. -/
inductive GeneratedBlockWord (blocks : List (Word Nat)) : Word Nat → Prop
  | generator (block : Word Nat) (member : block ∈ blocks) : GeneratedBlockWord blocks block
  | product {first second : Word Nat} :
      GeneratedBlockWord blocks first → GeneratedBlockWord blocks second →
        GeneratedBlockWord blocks (first ++ second)

theorem threeSquareBankAbsorbsGenerator (first second third block : Word Nat)
    (member : block ∈ [first, second, third]) :
    SquareAbsorbs (threeSquareBank first second third) block := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same
  · subst block
    exact ((SquareAbsorbs.square first).appendRight (second ++ second)).appendRight (third ++ third)
  · subst block
    exact ((SquareAbsorbs.square second).prependSquare first).appendRight (third ++ third)
  · subst block
    simpa only [threeSquareBank, Word.append_assoc] using
      ((SquareAbsorbs.square third).prependSquare second).prependSquare first

/-- All products of all three blocks are absorbed by the triangle's bank. -/
theorem threeSquareBankAbsorbsGenerated
    (first second third loop : Word Nat)
    (generated : GeneratedBlockWord [first, second, third] loop) :
    SquareAbsorbs (threeSquareBank first second third) loop := by
  induction generated with
  | generator block member => exact threeSquareBankAbsorbsGenerator first second third block member
  | product _ _ firstIH secondIH => exact firstIH.product secondIH

/-- The full unrestricted triangle-exchange family: arbitrary nonempty
blocks, arbitrary products of those blocks, and no word-length bound. -/
theorem triangleAbsorbsGenerated (first second third loop : Word Nat)
    (generated : GeneratedBlockWord [first, second, third] loop) :
    SquareAbsorbs (triangleWord first second third) loop :=
  SquareAbsorbs.ofDerives (derivesTriangleExchange first second third)
    (threeSquareBankAbsorbsGenerated first second third loop generated)

theorem triangleAbsorbsThird (first second third : Word Nat) :
    SquareAbsorbs (triangleWord first second third) third :=
  triangleAbsorbsGenerated first second third third (.generator third (by simp))

/-- Fable's exact odd-loop example has an actual frozen-basis derivation. -/
theorem oddLoopExampleDerives :
    Derives Rank040.basis (Word.mk 0 [1, 0, 2, 1, 2]) (Word.mk 2 [2, 0, 1, 0, 2, 1, 2]) :=
  triangleAbsorbsThird (Word.singleton 0) (Word.singleton 1) (Word.singleton 2)

theorem oddLoopExampleClosed :
    HeadRetargetBoundary.ClosedReturnWord (Word.mk 0 [1, 0, 2, 1, 2]) (Word.singleton 2) :=
  (triangleAbsorbsThird (Word.singleton 0) (Word.singleton 1) (Word.singleton 2)).closedReturnWord

end SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.ExposureReplay
