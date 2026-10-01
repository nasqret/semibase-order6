import SemigroupBasis.CoRoots.S5_626Completeness
import SemigroupBasis.CoRoots.S5_870GapBlocks
import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.Examples.CommutativeExponentThree
import SemigroupBasis.Examples.CyclicTwo
import SemigroupBasis.FiniteReflection

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeLiCondition9

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots

universe u

/-!
This module formalizes the common Lee--Li Section 7.3, Condition 9 case.
The source orientation below is the ten-law expansion of

* `xyx^2 = x^3y`;
* `x^2yx^2 = x^2y`;
* `(xyx^2zx)^* = xyzx`;
* `(xhytxy)^* = xhytyx`.

The packet stores the word-reversed orientation as its direct basis.  Keeping
the source orientation explicit lets the normal-form proof use the
left-to-right first-occurrence decomposition of Section 7.3; the public basis
endpoint is transported back by `BasisFor.oppositeReversed`.
-/

def leeLiCondition9ProofRoute : String :=
  "lee-li-constructive-condition-branch"

def leeLiCondition9PacketSHA256 : String :=
  "54d7c44d876c04e41eadf640c4c47e93c83d2062b0d22680f74d578e7a1ca5f2"

def leeLiCondition9BasisSHA256 : String :=
  "573195da5e5af08d142cc7b7f4f3ffe5116d04aa71198973ce81db249720a7ec"

def leeLiCondition9ReversedBasisSHA256 : String :=
  "eaa85f26867885f28159b43a83f3bdca5f630c537e8425e59c778f7bf0b5a54d"

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

private def xxxx : Word Nat := w 0 [0, 0, 0]
private def xxxy : Word Nat := w 0 [0, 0, 2]
private def xyxx : Word Nat := w 0 [2, 0, 0]
private def xxxzx : Word Nat := w 0 [0, 0, 4, 0]
private def xzx : Word Nat := w 0 [4, 0]
private def xxy : Word Nat := w 0 [0, 2]
private def xxyxx : Word Nat := w 0 [0, 2, 0, 0]
private def xyx : Word Nat := w 0 [2, 0]
private def xyxxx : Word Nat := w 0 [2, 0, 0, 0]
private def xyxxzx : Word Nat := w 0 [2, 0, 0, 4, 0]
private def xyzx : Word Nat := w 0 [2, 4, 0]

private def powerLaw : Identity Nat :=
  ⟨S5_870.xx, xxxx⟩

private def gatherPairLaw : Identity Nat :=
  ⟨xxxy, xyxx⟩

private def initialPairCapLaw : Identity Nat :=
  ⟨xxxzx, xzx⟩

private def protectedPairLaw : Identity Nat :=
  ⟨xxy, xxyxx⟩

private def rightPeriodLaw : Identity Nat :=
  ⟨xyx, xyxxx⟩

private def generalPairCapLaw : Identity Nat :=
  ⟨xyxxzx, xyzx⟩

/-- Lee--Li's displayed Section 7.3 orientation, with both stars expanded.
Its ledger hash is `eaa85f26...`. -/
def leeLiCondition9ReversedBasis : List (Identity Nat) :=
  [S5_870.sortGeneralLaw, S5_870.sortFinalGapEmptyLaw,
    powerLaw, gatherPairLaw, initialPairCapLaw, protectedPairLaw,
    S5_870.sortInitialGapEmptyLaw, rightPeriodLaw,
    generalPairCapLaw, S5_870.sortBothEmptyLaw]

/-- The exact direct ten-law packet basis with hash `573195da...`. -/
def leeLiCondition9Basis : List (Identity Nat) :=
  reversedBasis leeLiCondition9ReversedBasis

@[simp]
theorem reversedBasis_leeLiCondition9Basis :
    reversedBasis leeLiCondition9Basis =
      leeLiCondition9ReversedBasis := by
  simp [leeLiCondition9Basis]

/-! ## The common six-element representative -/

/-- The zero-based multiplication table opposite to the stored `S6_9937`
orientation. The public semigroup below applies the opposite operation again
and therefore has the stored representative table. -/
def leeLiCondition9Mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then 0
  else if a = 1 then if b.val < 4 then 0 else 1
  else if a = 2 then 2
  else if a = 3 then if b.val < 4 then 2 else 3
  else if a = 4 then b
  else if b = 0 then 2
  else if b = 1 then 3
  else if b = 2 then 0
  else if b = 3 then 1
  else if b = 4 then 5
  else 4

def leeLiCondition9Table : FiniteTable where
  order := 6
  mul := leeLiCondition9Mul
  assoc := by decide

/-- The representative orientation attached to direct hash `573195da...`. -/
def leeLiCondition9Semigroup : Semigroup (Fin 6) :=
  leeLiCondition9Table.semigroup.opposite

private def finiteSortGeneralLaw : Identity (Fin 4) :=
  ⟨⟨0, [1, 2, 3, 0, 2]⟩, ⟨0, [1, 2, 3, 2, 0]⟩⟩

private def finiteSortFinalGapEmptyLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0, 2]⟩, ⟨0, [1, 2, 2, 0]⟩⟩

private def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

private def finiteGatherPairLaw : Identity (Fin 3) :=
  ⟨⟨0, [0, 0, 2]⟩, ⟨0, [2, 0, 0]⟩⟩

private def finiteInitialPairCapLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 0, 1, 0]⟩, ⟨0, [1, 0]⟩⟩

private def finiteProtectedPairLaw : Identity (Fin 3) :=
  ⟨⟨0, [0, 2]⟩, ⟨0, [0, 2, 0, 0]⟩⟩

private def finiteSortInitialGapEmptyLaw : Identity (Fin 4) :=
  ⟨⟨0, [2, 3, 0, 2]⟩, ⟨0, [2, 3, 2, 0]⟩⟩

private def finiteRightPeriodLaw : Identity (Fin 3) :=
  ⟨⟨0, [2, 0]⟩, ⟨0, [2, 0, 0, 0]⟩⟩

private def finiteGeneralPairCapLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 0, 2, 0]⟩, ⟨0, [1, 2, 0]⟩⟩

private def finiteSortBothEmptyLaw : Identity (Fin 3) :=
  ⟨⟨0, [2, 0, 2]⟩, ⟨0, [2, 2, 0]⟩⟩

private theorem finiteSortGeneralLaw_map :
    finiteSortGeneralLaw.map Fin.val = S5_870.sortGeneralLaw := rfl

private theorem finiteSortFinalGapEmptyLaw_map :
    finiteSortFinalGapEmptyLaw.map Fin.val =
      S5_870.sortFinalGapEmptyLaw := rfl

private theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = powerLaw := rfl

private theorem finiteGatherPairLaw_map :
    finiteGatherPairLaw.map Fin.val = gatherPairLaw := rfl

private def renameXZ : Nat → Nat
  | 0 => 0
  | _ => 4

private theorem finiteInitialPairCapLaw_map :
    (finiteInitialPairCapLaw.map Fin.val).map renameXZ =
      initialPairCapLaw := rfl

private theorem finiteProtectedPairLaw_map :
    finiteProtectedPairLaw.map Fin.val = protectedPairLaw := rfl

private theorem finiteSortInitialGapEmptyLaw_map :
    finiteSortInitialGapEmptyLaw.map Fin.val =
      S5_870.sortInitialGapEmptyLaw := rfl

private theorem finiteRightPeriodLaw_map :
    finiteRightPeriodLaw.map Fin.val = rightPeriodLaw := rfl

private def renameXYZ : Nat → Nat
  | 0 => 0
  | 1 => 2
  | _ => 4

private theorem finiteGeneralPairCapLaw_map :
    (finiteGeneralPairCapLaw.map Fin.val).map renameXYZ =
      generalPairCapLaw := rfl

private theorem finiteSortBothEmptyLaw_map :
    finiteSortBothEmptyLaw.map Fin.val = S5_870.sortBothEmptyLaw := rfl

/-- Exact finite check for the ten Condition 9 laws.  Each law is evaluated at
its actual variable arity, avoiding the proof-term blowup caused by checking
the whole list in a shared five-variable domain. -/
def checkLeeLiCondition9ReversedBasis (T : FiniteTable) : Bool :=
  T.checkIdentity finiteSortGeneralLaw &&
  T.checkIdentity finiteSortFinalGapEmptyLaw &&
  T.checkIdentity finitePowerLaw &&
  T.checkIdentity finiteGatherPairLaw &&
  T.checkIdentity finiteInitialPairCapLaw &&
  T.checkIdentity finiteProtectedPairLaw &&
  T.checkIdentity finiteSortInitialGapEmptyLaw &&
  T.checkIdentity finiteRightPeriodLaw &&
  T.checkIdentity finiteGeneralPairCapLaw &&
  T.checkIdentity finiteSortBothEmptyLaw

/-- Soundness of the arity-minimal finite Condition 9 check. -/
theorem modelsLeeLiCondition9ReversedBasisOfCheck (T : FiniteTable)
    (checked : checkLeeLiCondition9ReversedBasis T = true) :
    Models T.semigroup leeLiCondition9ReversedBasis := by
  simp only [checkLeeLiCondition9ReversedBasis, Bool.and_eq_true] at checked
  rcases checked with ⟨checks, checkSortBothEmpty⟩
  rcases checks with ⟨checks, checkGeneralPairCap⟩
  rcases checks with ⟨checks, checkRightPeriod⟩
  rcases checks with ⟨checks, checkSortInitialGapEmpty⟩
  rcases checks with ⟨checks, checkProtectedPair⟩
  rcases checks with ⟨checks, checkInitialPairCap⟩
  rcases checks with ⟨checks, checkGatherPair⟩
  rcases checks with ⟨checks, checkPower⟩
  rcases checks with ⟨checkSortGeneral, checkSortFinalGapEmpty⟩
  intro identity member
  simp only [leeLiCondition9ReversedBasis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · rw [← finiteSortGeneralLaw_map]
    exact T.checkIdentityNat_sound
      finiteSortGeneralLaw checkSortGeneral
  · rw [← finiteSortFinalGapEmptyLaw_map]
    exact T.checkIdentityNat_sound
      finiteSortFinalGapEmptyLaw checkSortFinalGapEmpty
  · rw [← finitePowerLaw_map]
    exact T.checkIdentityNat_sound finitePowerLaw checkPower
  · rw [← finiteGatherPairLaw_map]
    exact T.checkIdentityNat_sound finiteGatherPairLaw checkGatherPair
  · rw [← finiteInitialPairCapLaw_map]
    exact (finiteInitialPairCapLaw.map Fin.val).satisfiedBy_map
      renameXZ T.semigroup
      (T.checkIdentityNat_sound
        finiteInitialPairCapLaw checkInitialPairCap)
  · rw [← finiteProtectedPairLaw_map]
    exact T.checkIdentityNat_sound
      finiteProtectedPairLaw checkProtectedPair
  · rw [← finiteSortInitialGapEmptyLaw_map]
    exact T.checkIdentityNat_sound
      finiteSortInitialGapEmptyLaw checkSortInitialGapEmpty
  · rw [← finiteRightPeriodLaw_map]
    exact T.checkIdentityNat_sound finiteRightPeriodLaw checkRightPeriod
  · rw [← finiteGeneralPairCapLaw_map]
    exact (finiteGeneralPairCapLaw.map Fin.val).satisfiedBy_map
      renameXYZ T.semigroup
      (T.checkIdentityNat_sound
        finiteGeneralPairCapLaw checkGeneralPairCap)
  · rw [← finiteSortBothEmptyLaw_map]
    exact T.checkIdentityNat_sound
      finiteSortBothEmptyLaw checkSortBothEmpty

set_option maxHeartbeats 3000000 in
private theorem leeLiCondition9ReversedModels :
    Models leeLiCondition9Table.semigroup
      leeLiCondition9ReversedBasis :=
  modelsLeeLiCondition9ReversedBasisOfCheck
    leeLiCondition9Table (by decide)

theorem leeLiCondition9Models :
    Models leeLiCondition9Semigroup leeLiCondition9Basis := by
  simpa [leeLiCondition9Semigroup, leeLiCondition9Basis] using
    leeLiCondition9ReversedModels.oppositeReversed

/-! ## Lee--Li's two separating factors -/

/-- The affine parity factor `S4_96^op` occurs on the literal subset
`{5,6,1,3}` (one-based) of the source representative.  It records first
occurrences, parity before every first occurrence, and final parity. -/
def affineParityEmbedding :
    Embedding affineParityFour.semigroup.opposite
      leeLiCondition9Table.semigroup where
  toFun := fun value : Fin 4 =>
    if value.val = 0 then (⟨4, by decide⟩ : Fin 6)
    else if value.val = 1 then (⟨5, by decide⟩ : Fin 6)
    else if value.val = 2 then (⟨0, by decide⟩ : Fin 6)
    else (⟨2, by decide⟩ : Fin 6)
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

/-- The capped-multiplicity factor `S3_8` occurs on the literal subset
`{1,2,5}` (one-based).  Its three states distinguish absent, simple, and
repeated variables. -/
def cappedMultiplicityEmbedding :
    Embedding commutativeExponentThree.semigroup
      leeLiCondition9Table.semigroup where
  toFun := fun value : Fin 3 =>
    if value.val = 0 then (⟨0, by decide⟩ : Fin 6)
    else if value.val = 1 then (⟨1, by decide⟩ : Fin 6)
    else (⟨4, by decide⟩ : Fin 6)
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

/-- The exact semantic input used by the Condition 9 normal-form argument.
Concrete catalogue roots may supply the two factor consequences by embeddings,
quotients, or any other fully proved transport. -/
structure SemanticWitness {S : Type u} (G : Semigroup S) where
  models : Models G leeLiCondition9ReversedBasis
  affineConsequence :
    ∀ identity : Identity Nat, identity.SatisfiedBy G →
      identity.SatisfiedBy affineParityFour.semigroup.opposite
  cappedConsequence :
    ∀ identity : Identity Nat, identity.SatisfiedBy G →
      identity.SatisfiedBy commutativeExponentThree.semigroup

private def sourceSemanticWitness :
    SemanticWitness leeLiCondition9Table.semigroup where
  models := leeLiCondition9ReversedModels
  affineConsequence := fun identity valid =>
    affineParityEmbedding.pullback_identity identity valid
  cappedConsequence := fun identity valid =>
    cappedMultiplicityEmbedding.pullback_identity identity valid

private theorem sameAffineCombinatorics_of_valid
    {S : Type u} {G : Semigroup S} (semantic : SemanticWitness G)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy G) :
    S5_626.SameAffineOppositeCombinatorics
      identity.lhs identity.rhs :=
  S5_626.sameAffineOppositeCombinatorics_of_valid identity
    (semantic.affineConsequence identity valid)

private theorem sameCappedCounts_of_valid
    {S : Type u} {G : Semigroup S} (semantic : SemanticWitness G)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy G) :
    ∀ letter,
      min (identity.lhs.toList.count letter) 2 =
        min (identity.rhs.toList.count letter) 2 :=
  exponentValid_capped_count_eq identity
    (semantic.cappedConsequence identity valid)

/-! ## Generic substitutions for the six non-sorting laws -/

private def instantiateFiveWords
    (x h y t z : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => h
  | 2 => y
  | 3 => t
  | 4 => z
  | n + 5 => Word.singleton (n + 5)

private theorem basisPower :
    Derives leeLiCondition9ReversedBasis S5_870.xx xxxx :=
  Derives.fromBasis (e := powerLaw) (by
    simp [leeLiCondition9ReversedBasis])

private theorem basisGatherPair :
    Derives leeLiCondition9ReversedBasis xyxx xxxy :=
  (Derives.fromBasis (e := gatherPairLaw) (by
    simp [leeLiCondition9ReversedBasis])).symm

private theorem basisInitialPairCap :
    Derives leeLiCondition9ReversedBasis xxxzx xzx :=
  Derives.fromBasis (e := initialPairCapLaw) (by
    simp [leeLiCondition9ReversedBasis])

private theorem basisProtectedPair :
    Derives leeLiCondition9ReversedBasis xxyxx xxy :=
  (Derives.fromBasis (e := protectedPairLaw) (by
    simp [leeLiCondition9ReversedBasis])).symm

private theorem basisRightPeriod :
    Derives leeLiCondition9ReversedBasis xyx xyxxx :=
  Derives.fromBasis (e := rightPeriodLaw) (by
    simp [leeLiCondition9ReversedBasis])

private theorem basisGeneralPairCap :
    Derives leeLiCondition9ReversedBasis xyxxzx xyzx :=
  Derives.fromBasis (e := generalPairCapLaw) (by
    simp [leeLiCondition9ReversedBasis])

theorem derivesFourToTwo (x : Word Nat) :
    Derives leeLiCondition9ReversedBasis
      (((x ++ x) ++ x) ++ x) (x ++ x) := by
  have substituted :=
    Derives.subst basisPower (instantiateFiveWords x x x x x)
  simpa [powerLaw, S5_870.xx, xxxx, w, instantiateFiveWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted.symm

theorem derivesGatherPair (x middle : Word Nat) :
    Derives leeLiCondition9ReversedBasis
      (((x ++ middle) ++ x) ++ x) (((x ++ x) ++ x) ++ middle) := by
  have substituted :=
    Derives.subst basisGatherPair
      (instantiateFiveWords x x middle middle middle)
  simpa [gatherPairLaw, xyxx, xxxy, w, instantiateFiveWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

theorem derivesInitialPairCap (x middle : Word Nat) :
    Derives leeLiCondition9ReversedBasis
      ((((x ++ x) ++ x) ++ middle) ++ x)
      ((x ++ middle) ++ x) := by
  have substituted :=
    Derives.subst basisInitialPairCap
      (instantiateFiveWords x x x x middle)
  simpa [initialPairCapLaw, xxxzx, xzx, w, instantiateFiveWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

theorem derivesProtectedPairCap (x middle : Word Nat) :
    Derives leeLiCondition9ReversedBasis
      ((((x ++ x) ++ middle) ++ x) ++ x)
      ((x ++ x) ++ middle) := by
  have substituted :=
    Derives.subst basisProtectedPair
      (instantiateFiveWords x x middle middle middle)
  simpa [protectedPairLaw, xxyxx, xxy, w, instantiateFiveWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

theorem derivesRightPeriodContraction (x middle : Word Nat) :
    Derives leeLiCondition9ReversedBasis
      ((((x ++ middle) ++ x) ++ x) ++ x)
      ((x ++ middle) ++ x) := by
  have substituted :=
    Derives.subst basisRightPeriod
      (instantiateFiveWords x x middle middle middle)
  simpa [rightPeriodLaw, xyx, xyxxx, w, instantiateFiveWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted.symm

theorem derivesGeneralPairCap
    (x firstGap secondGap : Word Nat) :
    Derives leeLiCondition9ReversedBasis
      ((((((x ++ firstGap) ++ x) ++ x) ++ secondGap) ++ x))
      (((x ++ firstGap) ++ secondGap) ++ x) := by
  have substituted :=
    Derives.subst basisGeneralPairCap
      (instantiateFiveWords x x firstGap firstGap secondGap)
  simpa [generalPairCapLaw, xyxxzx, xyzx, w,
    instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-! ## S5_870 starred sorting under the Condition 9 basis -/

private theorem basisSortBothEmpty :
    Derives leeLiCondition9ReversedBasis
      S5_870.xyxy S5_870.xyyx :=
  Derives.fromBasis (e := S5_870.sortBothEmptyLaw) (by
    simp [leeLiCondition9ReversedBasis])

private theorem basisSortInitialGapEmpty :
    Derives leeLiCondition9ReversedBasis
      S5_870.xytxy S5_870.xytyx :=
  Derives.fromBasis (e := S5_870.sortInitialGapEmptyLaw) (by
    simp [leeLiCondition9ReversedBasis])

private theorem basisSortFinalGapEmpty :
    Derives leeLiCondition9ReversedBasis
      S5_870.xhyxy S5_870.xhyyx :=
  Derives.fromBasis (e := S5_870.sortFinalGapEmptyLaw) (by
    simp [leeLiCondition9ReversedBasis])

private theorem basisSortGeneral :
    Derives leeLiCondition9ReversedBasis
      S5_870.xhytxy S5_870.xhytyx :=
  Derives.fromBasis (e := S5_870.sortGeneralLaw) (by
    simp [leeLiCondition9ReversedBasis])

private theorem derivesSortBothEmpty (x y : Word Nat) :
    Derives leeLiCondition9ReversedBasis
      (((x ++ y) ++ x) ++ y) (((x ++ y) ++ y) ++ x) := by
  have substituted := Derives.subst basisSortBothEmpty
    (instantiateFiveWords x x y y y)
  change Derives leeLiCondition9ReversedBasis
    (((x ++ y) ++ x) ++ y) (((x ++ y) ++ y) ++ x) at substituted
  exact substituted

private theorem derivesSortInitialGapEmpty
    (x y gap : Word Nat) :
    Derives leeLiCondition9ReversedBasis
      ((((x ++ y) ++ gap) ++ x) ++ y)
      ((((x ++ y) ++ gap) ++ y) ++ x) := by
  have substituted := Derives.subst basisSortInitialGapEmpty
    (instantiateFiveWords x x y gap gap)
  change Derives leeLiCondition9ReversedBasis
    ((((x ++ y) ++ gap) ++ x) ++ y)
    ((((x ++ y) ++ gap) ++ y) ++ x) at substituted
  exact substituted

private theorem derivesSortFinalGapEmpty
    (x firstGap y : Word Nat) :
    Derives leeLiCondition9ReversedBasis
      ((((x ++ firstGap) ++ y) ++ x) ++ y)
      ((((x ++ firstGap) ++ y) ++ y) ++ x) := by
  have substituted := Derives.subst basisSortFinalGapEmpty
    (instantiateFiveWords x firstGap y y y)
  change Derives leeLiCondition9ReversedBasis
    ((((x ++ firstGap) ++ y) ++ x) ++ y)
    ((((x ++ firstGap) ++ y) ++ y) ++ x) at substituted
  exact substituted

private theorem derivesSortGeneral
    (x firstGap y secondGap : Word Nat) :
    Derives leeLiCondition9ReversedBasis
      (((((x ++ firstGap) ++ y) ++ secondGap) ++ x) ++ y)
      (((((x ++ firstGap) ++ y) ++ secondGap) ++ y) ++ x) := by
  have substituted := Derives.subst basisSortGeneral
    (instantiateFiveWords x firstGap y secondGap secondGap)
  change Derives leeLiCondition9ReversedBasis
    (((((x ++ firstGap) ++ y) ++ secondGap) ++ x) ++ y)
    (((((x ++ firstGap) ++ y) ++ secondGap) ++ y) ++ x) at substituted
  exact substituted

private abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives leeLiCondition9ReversedBasis

private abbrev listWordOfCons := S5_107.listWordOfCons

private theorem listDerivesSortBothEmpty (first second : Nat) :
    ListDerives [first, second, first, second]
      [first, second, second, first] := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc] using
      (S5_107.ListDerives.ofWord
        (basis := leeLiCondition9ReversedBasis)
        (derivesSortBothEmpty
          (Word.singleton first) (Word.singleton second)))

private theorem listDerivesSortInitialGapEmpty
    (first second gapHead : Nat) (gapTail : List Nat) :
    ListDerives
      ([first, second] ++ (gapHead :: gapTail) ++ [first, second])
      ([first, second] ++ (gapHead :: gapTail) ++ [second, first]) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc, List.append_assoc] using
      (S5_107.ListDerives.ofWord
        (basis := leeLiCondition9ReversedBasis)
        (derivesSortInitialGapEmpty
          (Word.singleton first) (Word.singleton second)
          (listWordOfCons gapHead gapTail)))

private theorem listDerivesSortFinalGapEmpty
    (first gapHead second : Nat) (gapTail : List Nat) :
    ListDerives
      ([first] ++ (gapHead :: gapTail) ++ [second, first, second])
      ([first] ++ (gapHead :: gapTail) ++ [second, second, first]) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc, List.append_assoc] using
      (S5_107.ListDerives.ofWord
        (basis := leeLiCondition9ReversedBasis)
        (derivesSortFinalGapEmpty
          (Word.singleton first) (listWordOfCons gapHead gapTail)
          (Word.singleton second)))

private theorem listDerivesSortGeneral
    (first firstGapHead second secondGapHead : Nat)
    (firstGapTail secondGapTail : List Nat) :
    ListDerives
      ([first] ++ (firstGapHead :: firstGapTail) ++ [second] ++
        (secondGapHead :: secondGapTail) ++ [first, second])
      ([first] ++ (firstGapHead :: firstGapTail) ++ [second] ++
        (secondGapHead :: secondGapTail) ++ [second, first]) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc, List.append_assoc] using
      (S5_107.ListDerives.ofWord
        (basis := leeLiCondition9ReversedBasis)
        (derivesSortGeneral
          (Word.singleton first) (listWordOfCons firstGapHead firstGapTail)
          (Word.singleton second)
          (listWordOfCons secondGapHead secondGapTail)))

/-- The four starred laws swap adjacent later occurrences in every possible
empty/nonempty placement. -/
theorem listDerivesSwapDisplayedSeconds
    (first second : Nat)
    (before firstGap secondGap after : List Nat) :
    ListDerives
      (before ++ [first] ++ firstGap ++ [second] ++ secondGap ++
        [first, second] ++ after)
      (before ++ [first] ++ firstGap ++ [second] ++ secondGap ++
        [second, first] ++ after) := by
  cases firstGap with
  | nil =>
      cases secondGap with
      | nil =>
          simpa [List.append_assoc] using
            S5_107.ListDerives.context before after
              (listDerivesSortBothEmpty first second)
      | cons secondGapHead secondGapTail =>
          simpa [List.append_assoc] using
            S5_107.ListDerives.context before after
              (listDerivesSortInitialGapEmpty
                first second secondGapHead secondGapTail)
  | cons firstGapHead firstGapTail =>
      cases secondGap with
      | nil =>
          simpa [List.append_assoc] using
            S5_107.ListDerives.context before after
              (listDerivesSortFinalGapEmpty
                first firstGapHead second firstGapTail)
      | cons secondGapHead secondGapTail =>
          simpa [List.append_assoc] using
            S5_107.ListDerives.context before after
              (listDerivesSortGeneral first firstGapHead second
                secondGapHead firstGapTail secondGapTail)

/-- Once both letters occur in the stem, their adjacent later occurrences
can be swapped. -/
theorem listDerivesSwapAfterSeen
    (stem suffix : List Nat) (left right : Nat)
    (leftSeen : left ∈ stem) (rightSeen : right ∈ stem) :
    ListDerives (stem ++ [left, right] ++ suffix)
      (stem ++ [right, left] ++ suffix) := by
  by_cases equal : left = right
  · subst right
    exact S5_107.ListDerives.refl _
  · obtain ⟨leftBefore, leftAfter, prefixSplit⟩ :=
      List.mem_iff_append.mp leftSeen
    have rightInSplit :
        right ∈ leftBefore ∨ right ∈ leftAfter := by
      rw [prefixSplit] at rightSeen
      rcases List.mem_append.mp rightSeen with beforeMember | afterMember
      · exact Or.inl beforeMember
      · rcases List.mem_cons.mp afterMember with atLeft | inAfter
        · exact False.elim (equal atLeft.symm)
        · exact Or.inr inAfter
    rcases rightInSplit with rightBefore | rightAfter
    · obtain ⟨before, middle, beforeSplit⟩ :=
        List.mem_iff_append.mp rightBefore
      have displayed := listDerivesSwapDisplayedSeconds
        right left before middle leftAfter suffix
      simpa [prefixSplit, beforeSplit, List.append_assoc] using
        displayed.symm
    · obtain ⟨middle, tail, afterSplit⟩ :=
        List.mem_iff_append.mp rightAfter
      simpa [prefixSplit, afterSplit, List.append_assoc] using
        listDerivesSwapDisplayedSeconds
          left right leftBefore middle tail suffix

/-- S5_870 starred sorting permits every permutation of a later block whose
letters already occur in the fixed stem. -/
theorem listDerivesPermuteAfterSeen
    (stem suffix : List Nat) {source target : List Nat}
    (sourceSeen : ∀ letter, letter ∈ source → letter ∈ stem)
    (permutation : source.Perm target) :
    ListDerives (stem ++ source ++ suffix)
      (stem ++ target ++ suffix) := by
  induction permutation generalizing stem with
  | nil =>
      exact S5_107.ListDerives.refl _
  | cons head _ induction =>
      have derivation := induction (stem ++ [head]) (by
        intro letter member
        exact List.mem_append.mpr <| Or.inl <|
          sourceSeen letter (List.Mem.tail head member))
      simpa [List.append_assoc] using derivation
  | swap first second rest =>
      have firstSeen : first ∈ stem := sourceSeen first (by simp)
      have secondSeen : second ∈ stem := sourceSeen second (by simp)
      simpa [List.append_assoc] using
        listDerivesSwapAfterSeen stem (rest ++ suffix)
          second first secondSeen firstSeen
  | trans firstPermutation _ firstInduction secondInduction =>
      have firstDerivation := firstInduction stem sourceSeen
      have secondDerivation := secondInduction stem (by
        intro letter member
        exact sourceSeen letter ((firstPermutation.mem_iff).mpr member))
      exact firstDerivation.trans secondDerivation

/-!
## Condition 9 normal form

Every globally repeated marker first receives a protected neutral pair.  Once
those pairs are present, the S5_870 starred laws sort each first-occurrence
gap and `xxyxx = xxy` removes every adjacent parity pair without changing a
simple variable into a repeated one.  The final pass removes a protected pair
exactly when a parity occurrence remains later.  Thus every marker has
exponent one, two, or three, and exponent three occurs only when that marker
is absent from all later gap residues.
-/

private abbrev GapBlock := S5_870.FirstOccurrenceGapBlock

private def parityBlock (letters : List Nat) : List Nat :=
  (parityReduce letters).mergeSort
    (fun left right : Nat => decide (left ≤ right))

private theorem source_mem_of_parityReduce_mem
    {letter : Nat} {letters : List Nat}
    (member : letter ∈ parityReduce letters) :
    letter ∈ letters := by
  have odd := (mem_parityReduce_iff letter letters).1 member
  apply List.count_pos_iff.mp
  omega

private theorem parityReduce_perm_parityBlock
    (letters : List Nat) :
    (parityReduce letters).Perm (parityBlock letters) := by
  exact (List.mergeSort_perm
    (parityReduce letters)
    (fun left right : Nat => decide (left ≤ right))).symm

private theorem parityBlock_nodup (letters : List Nat) :
    (parityBlock letters).Nodup := by
  exact (parityReduce_perm_parityBlock letters).nodup_iff.mp
    (parityReduce_nodup letters)

private theorem mem_of_mem_parityBlock
    {letter : Nat} {letters : List Nat}
    (member : letter ∈ parityBlock letters) :
    letter ∈ letters := by
  apply source_mem_of_parityReduce_mem
  exact (parityReduce_perm_parityBlock letters).mem_iff.mpr member

private def renderParityGapBlocks : List GapBlock → List Nat
  | [] => []
  | block :: rest =>
      block.marker ::
        (parityBlock block.seconds ++ renderParityGapBlocks rest)

private def markerRepeated
    (block : GapBlock) (rest : List GapBlock) : Prop :=
  block.marker ∈ S5_870.gapBlockSeconds (block :: rest)

private instance markerRepeatedDecidable
    (block : GapBlock) (rest : List GapBlock) :
    Decidable (markerRepeated block rest) := by
  unfold markerRepeated
  infer_instance

private def protectedMarker
    (block : GapBlock) (rest : List GapBlock) : List Nat :=
  if markerRepeated block rest then
    [block.marker, block.marker, block.marker]
  else [block.marker]

private def renderProtectedGapBlocks : List GapBlock → List Nat
  | [] => []
  | block :: rest =>
      protectedMarker block rest ++ block.seconds ++
        renderProtectedGapBlocks rest

private def renderProtectedParityGapBlocks : List GapBlock → List Nat
  | [] => []
  | block :: rest =>
      protectedMarker block rest ++ parityBlock block.seconds ++
        renderProtectedParityGapBlocks rest

private def renderCondition9GapBlocks : List GapBlock → List Nat
  | [] => []
  | block :: rest =>
      let parityTail :=
        parityBlock block.seconds ++ renderParityGapBlocks rest
      let markerPrefix :=
        if markerRepeated block rest ∧ block.marker ∉ parityTail then
          [block.marker, block.marker, block.marker]
        else [block.marker]
      markerPrefix ++ parityBlock block.seconds ++
        renderCondition9GapBlocks rest

/-- The executable Lee--Li Section 7.3, Condition 9 normal list. -/
def leeLiCondition9NormalList (word : Word Nat) : List Nat :=
  renderCondition9GapBlocks (S5_870.gapBlocksList word.toList)

/-! ### Installing all protected pairs -/

private theorem listDerivesInstallProtection
    (before tail : List Nat) (letter : Nat)
    (repeated : letter ∈ tail) :
    ListDerives
      (before ++ letter :: tail)
      (before ++ [letter, letter, letter] ++ tail) := by
  obtain ⟨middle, after, split⟩ :=
    List.mem_iff_append.mp repeated
  rw [split]
  cases middle with
  | nil =>
      have core :=
        S5_107.ListDerives.ofWord
          (derivesFourToTwo (Word.singleton letter)).symm
      simpa [Word.singleton, Word.append,
        List.append_assoc] using
          S5_107.ListDerives.context before after core
  | cons middleHead middleTail =>
      let middleWord := listWordOfCons middleHead middleTail
      have expanded :=
        (derivesRightPeriodContraction
          (Word.singleton letter) middleWord).symm
      have gathered :=
        derivesGatherPair (Word.singleton letter)
          (middleWord ++ Word.singleton letter)
      have core := S5_107.ListDerives.ofWord
        (expanded.trans gathered)
      simpa [middleWord, listWordOfCons, Word.singleton,
        Word.append, Word.append_assoc, List.append_assoc] using
          S5_107.ListDerives.context before after core

private theorem mem_renderGapBlocks_of_mem_seconds
    {tested : Nat} {blocks : List GapBlock}
    (member : tested ∈ S5_870.gapBlockSeconds blocks) :
    tested ∈ S5_870.renderGapBlocks blocks := by
  induction blocks with
  | nil => simp [S5_870.gapBlockSeconds] at member
  | cons block rest induction =>
      simp only [S5_870.gapBlockSeconds, List.flatMap_cons,
        List.mem_append] at member
      simp only [S5_870.renderGapBlocks, List.mem_cons,
        List.mem_append]
      rcases member with current | later
      · exact Or.inr (Or.inl current)
      · exact Or.inr (Or.inr (induction later))

private theorem marker_mem_tail_of_repeated
    (block : GapBlock) (rest : List GapBlock)
    (repeated : markerRepeated block rest) :
    block.marker ∈
      block.seconds ++ S5_870.renderGapBlocks rest := by
  change block.marker ∈
    block.seconds ++ S5_870.gapBlockSeconds rest at repeated
  rcases List.mem_append.mp repeated with current | later
  · exact List.mem_append.mpr (Or.inl current)
  · exact List.mem_append.mpr (Or.inr
      (mem_renderGapBlocks_of_mem_seconds later))

private theorem listDerivesProtectGapBlocks :
    ∀ blocks : List GapBlock,
      ListDerives
        (S5_870.renderGapBlocks blocks)
        (renderProtectedGapBlocks blocks)
  | [] => S5_107.ListDerives.refl []
  | block :: rest => by
      have recurse := listDerivesProtectGapBlocks rest
      by_cases repeated : markerRepeated block rest
      · have installed :=
          listDerivesInstallProtection []
            (block.seconds ++ S5_870.renderGapBlocks rest)
            block.marker
            (marker_mem_tail_of_repeated block rest repeated)
        have underPrefix := recurse.prepend
          ([block.marker, block.marker, block.marker] ++ block.seconds)
        simpa [S5_870.renderGapBlocks, renderProtectedGapBlocks,
          protectedMarker, repeated, List.append_assoc] using
            installed.trans underPrefix
      · have underPrefix := recurse.prepend
          ([block.marker] ++ block.seconds)
        simpa [S5_870.renderGapBlocks, renderProtectedGapBlocks,
          protectedMarker, repeated, List.append_assoc] using underPrefix

/-! ### Parity reduction behind protected markers -/

private def HasProtectedPair (stem : List Nat) (letter : Nat) : Prop :=
  ∃ before after,
    stem = before ++ [letter, letter] ++ after

private theorem HasProtectedPair.mem
    {stem : List Nat} {letter : Nat}
    (hasPair : HasProtectedPair stem letter) :
    letter ∈ stem := by
  obtain ⟨before, after, rfl⟩ := hasPair
  simp

private theorem HasProtectedPair.append
    {stem : List Nat} {letter : Nat}
    (hasPair : HasProtectedPair stem letter)
    (suffix : List Nat) :
    HasProtectedPair (stem ++ suffix) letter := by
  obtain ⟨before, after, rfl⟩ := hasPair
  exact ⟨before, after ++ suffix, by simp [List.append_assoc]⟩

private theorem listDerivesDeletePairAfterProtected
    (stem suffix : List Nat) (letter : Nat)
    (hasPair : HasProtectedPair stem letter) :
    ListDerives
      (stem ++ [letter, letter] ++ suffix)
      (stem ++ suffix) := by
  obtain ⟨before, gap, stemShape⟩ := hasPair
  rw [stemShape]
  cases gap with
  | nil =>
      have core := S5_107.ListDerives.ofWord
        (derivesFourToTwo (Word.singleton letter))
      simpa [Word.singleton, Word.append,
        List.append_assoc] using
          S5_107.ListDerives.context before suffix core
  | cons gapHead gapTail =>
      let gapWord := listWordOfCons gapHead gapTail
      have core := S5_107.ListDerives.ofWord
        (derivesProtectedPairCap
          (Word.singleton letter) gapWord)
      simpa [gapWord, listWordOfCons, Word.singleton, Word.append,
        List.append_assoc] using
          S5_107.ListDerives.context before suffix core

private theorem listDerivesParityReduceAfterProtected :
    ∀ (stem letters suffix : List Nat),
      (∀ letter, letter ∈ letters →
        HasProtectedPair stem letter) →
      ListDerives
        (stem ++ letters ++ suffix)
        (stem ++ parityReduce letters ++ suffix)
  | stem, [], suffix, _ => by
      simpa [parityReduce] using
        (S5_107.ListDerives.refl
          (basis := leeLiCondition9ReversedBasis) (stem ++ suffix))
  | stem, head :: tail, suffix, pairs => by
      have tailProtected :
          ∀ letter, letter ∈ tail →
            HasProtectedPair (stem ++ [head]) letter := by
        intro letter member
        exact (pairs letter (List.Mem.tail head member)).append [head]
      have tailDerivation :=
        listDerivesParityReduceAfterProtected
          (stem ++ [head]) tail suffix tailProtected
      by_cases member : head ∈ parityReduce tail
      · have headProtected := pairs head (List.Mem.head tail)
        have reducedProtected :
            ∀ letter, letter ∈ parityReduce tail →
              HasProtectedPair stem letter := by
          intro letter reducedMember
          exact pairs letter (List.Mem.tail head
            (source_mem_of_parityReduce_mem reducedMember))
        have blockSeen :
            ∀ letter, letter ∈ head :: parityReduce tail →
              letter ∈ stem := by
          intro letter blockMember
          rcases List.mem_cons.mp blockMember with equal | reducedMember
          · subst letter
            exact headProtected.mem
          · exact (reducedProtected letter reducedMember).mem
        have expose :
            (head :: parityReduce tail).Perm
              (head :: head :: (parityReduce tail).erase head) :=
          List.Perm.cons head (List.perm_cons_erase member)
        have arranged :=
          listDerivesPermuteAfterSeen stem suffix blockSeen expose
        have arranged' :
            ListDerives
              ((stem ++ [head]) ++ parityReduce tail ++ suffix)
              (stem ++ (head :: head ::
                (parityReduce tail).erase head) ++ suffix) := by
          simpa [List.append_assoc] using arranged
        have deleted :=
          listDerivesDeletePairAfterProtected stem
            ((parityReduce tail).erase head ++ suffix)
            head headProtected
        have deleted' :
            ListDerives
              (stem ++ (head :: head ::
                (parityReduce tail).erase head) ++ suffix)
              (stem ++ (parityReduce tail).erase head ++ suffix) := by
          simpa [List.append_assoc] using deleted
        exact by
          simpa [parityReduce, member, List.append_assoc] using
            tailDerivation.trans (arranged'.trans deleted')
      · simpa [parityReduce, member, List.append_assoc] using
          tailDerivation

private theorem listDerivesParityBlockAfterProtected
    (stem letters suffix : List Nat)
    (pairs : ∀ letter, letter ∈ letters →
      HasProtectedPair stem letter) :
    ListDerives
      (stem ++ letters ++ suffix)
      (stem ++ parityBlock letters ++ suffix) := by
  have reduced :=
    listDerivesParityReduceAfterProtected
      stem letters suffix pairs
  have reducedSeen :
      ∀ letter, letter ∈ parityReduce letters → letter ∈ stem := by
    intro letter member
    exact (pairs letter
      (source_mem_of_parityReduce_mem member)).mem
  have sorted :=
    listDerivesPermuteAfterSeen stem suffix reducedSeen
      (parityReduce_perm_parityBlock letters)
  exact reduced.trans sorted

private theorem mem_render_iff_markers_or_seconds
    (tested : Nat) :
    ∀ blocks : List GapBlock,
      tested ∈ S5_870.renderGapBlocks blocks ↔
        tested ∈ S5_870.gapBlockMarkers blocks ∨
          tested ∈ S5_870.gapBlockSeconds blocks
  | [] => by simp [S5_870.renderGapBlocks,
      S5_870.gapBlockMarkers, S5_870.gapBlockSeconds]
  | block :: rest => by
      simp only [S5_870.renderGapBlocks, S5_870.gapBlockMarkers,
        S5_870.gapBlockSeconds, List.map_cons, List.flatMap_cons,
        List.mem_cons, List.mem_append,
        mem_render_iff_markers_or_seconds tested rest]
      constructor
      · intro member
        rcases member with atMarker | inCurrent | inRestMarker | inRestSecond
        · exact Or.inl (Or.inl atMarker)
        · exact Or.inr (Or.inl inCurrent)
        · exact Or.inl (Or.inr inRestMarker)
        · exact Or.inr (Or.inr inRestSecond)
      · intro member
        rcases member with (atMarker | inRestMarker) |
          inCurrent | inRestSecond
        · exact Or.inl atMarker
        · exact Or.inr (Or.inr (Or.inl inRestMarker))
        · exact Or.inr (Or.inl inCurrent)
        · exact Or.inr (Or.inr (Or.inr inRestSecond))

private theorem listDerivesNormalizeProtectedGapBlocks :
    ∀ {seen : List Nat} {blocks : List GapBlock},
      S5_870.GapBlocksWellFormed seen blocks →
      ∀ stem : List Nat,
        (∀ letter, letter ∈ seen →
          letter ∈ S5_870.renderGapBlocks blocks →
            HasProtectedPair stem letter) →
        ListDerives
          (stem ++ renderProtectedGapBlocks blocks)
          (stem ++ renderProtectedParityGapBlocks blocks)
  | seen, [], formed, stem, pairs => by
      simpa [renderProtectedGapBlocks,
        renderProtectedParityGapBlocks] using
          (S5_107.ListDerives.refl
            (basis := leeLiCondition9ReversedBasis) stem)
  | seen, block :: rest, formed, stem, pairs => by
      cases formed with
      | cons _ _ _ markerFresh secondsSeen tailFormed =>
          let currentStem :=
            stem ++ protectedMarker block rest
          have currentProtected :
              ∀ letter, letter ∈ block.seconds →
                HasProtectedPair currentStem letter := by
            intro letter member
            rcases List.mem_cons.mp (secondsSeen letter member) with
              atMarker | inSeen
            · subst letter
              have repeated : markerRepeated block rest := by
                change block.marker ∈
                  block.seconds ++ S5_870.gapBlockSeconds rest
                exact List.mem_append.mpr (Or.inl member)
              exact ⟨stem, [block.marker], by
                simp [currentStem, protectedMarker, repeated,
                  List.append_assoc]⟩
            · have inCurrent :
                  letter ∈ S5_870.renderGapBlocks (block :: rest) := by
                simp [S5_870.renderGapBlocks, member]
              exact (pairs letter inSeen inCurrent).append
                (protectedMarker block rest)
          have current :=
            listDerivesParityBlockAfterProtected currentStem
              block.seconds (renderProtectedGapBlocks rest)
              currentProtected
          let nextStem := currentStem ++ parityBlock block.seconds
          have nextProtected :
              ∀ letter, letter ∈ block.marker :: seen →
                letter ∈ S5_870.renderGapBlocks rest →
                  HasProtectedPair nextStem letter := by
            intro letter inNextSeen inRest
            rcases List.mem_cons.mp inNextSeen with atMarker | inSeen
            · subst letter
              have markerNotInRestMarkers :
                  block.marker ∉ S5_870.gapBlockMarkers rest :=
                tailFormed.markersAvoidSeen block.marker
                  (List.Mem.head seen)
              have inRestSeconds :
                  block.marker ∈ S5_870.gapBlockSeconds rest :=
                ((mem_render_iff_markers_or_seconds
                  block.marker rest).mp inRest).resolve_left
                    markerNotInRestMarkers
              have repeated : markerRepeated block rest := by
                change block.marker ∈
                  block.seconds ++ S5_870.gapBlockSeconds rest
                exact List.mem_append.mpr (Or.inr inRestSeconds)
              have pairInCurrent :
                  HasProtectedPair currentStem block.marker :=
                ⟨stem, [block.marker], by
                  simp [currentStem, protectedMarker, repeated,
                    List.append_assoc]⟩
              exact pairInCurrent.append (parityBlock block.seconds)
            · have inCurrent :
                  letter ∈ S5_870.renderGapBlocks (block :: rest) := by
                simp [S5_870.renderGapBlocks, inRest]
              have pairInStem := pairs letter inSeen inCurrent
              exact (pairInStem.append
                (protectedMarker block rest)).append
                  (parityBlock block.seconds)
          have recurse :=
            listDerivesNormalizeProtectedGapBlocks tailFormed
              nextStem nextProtected
          simpa [currentStem, nextStem, renderProtectedGapBlocks,
            renderProtectedParityGapBlocks, List.append_assoc] using
              current.trans recurse

/-! ### Removing unnecessary protected pairs -/

private theorem listDerivesRemoveProtectionWithLater
    (before tail : List Nat) (letter : Nat)
    (later : letter ∈ tail) :
    ListDerives
      (before ++ [letter, letter, letter] ++ tail)
      (before ++ [letter] ++ tail) := by
  obtain ⟨middle, after, split⟩ :=
    List.mem_iff_append.mp later
  rw [split]
  cases middle with
  | nil =>
      have core := S5_107.ListDerives.ofWord
        (derivesFourToTwo (Word.singleton letter))
      simpa [Word.singleton, Word.append,
        List.append_assoc] using
          S5_107.ListDerives.context before after core
  | cons middleHead middleTail =>
      let middleWord := listWordOfCons middleHead middleTail
      have core := S5_107.ListDerives.ofWord
        (derivesInitialPairCap
          (Word.singleton letter) middleWord)
      simpa [middleWord, listWordOfCons, Word.singleton,
        Word.append, List.append_assoc] using
          S5_107.ListDerives.context before after core

private theorem mem_renderProtectedParity_of_mem_renderParity
    {tested : Nat} :
    ∀ {blocks : List GapBlock},
      tested ∈ renderParityGapBlocks blocks →
        tested ∈ renderProtectedParityGapBlocks blocks
  | [], member => by simp [renderParityGapBlocks] at member
  | block :: rest, member => by
      simp only [renderParityGapBlocks, List.mem_cons,
        List.mem_append] at member
      simp only [renderProtectedParityGapBlocks, List.mem_append]
      rcases member with atMarker | inCurrent | inRest
      · left
        unfold protectedMarker
        split <;> simp [atMarker]
      · exact Or.inl (Or.inr inCurrent)
      · exact Or.inr
          (mem_renderProtectedParity_of_mem_renderParity inRest)

private theorem listDerivesCleanupGapBlocks :
    ∀ blocks : List GapBlock,
      ListDerives
        (renderProtectedParityGapBlocks blocks)
        (renderCondition9GapBlocks blocks)
  | [] => S5_107.ListDerives.refl []
  | block :: rest => by
      let parityTail :=
        parityBlock block.seconds ++ renderParityGapBlocks rest
      have recurse := listDerivesCleanupGapBlocks rest
      by_cases repeated : markerRepeated block rest
      · by_cases retained : block.marker ∈ parityTail
        · have retainedProtected :
              block.marker ∈
                parityBlock block.seconds ++
                  renderProtectedParityGapBlocks rest := by
            rcases List.mem_append.mp retained with current | later
            · exact List.mem_append.mpr (Or.inl current)
            · exact List.mem_append.mpr (Or.inr
                (mem_renderProtectedParity_of_mem_renderParity later))
          have removed :=
            listDerivesRemoveProtectionWithLater []
              (parityBlock block.seconds ++
                renderProtectedParityGapBlocks rest)
              block.marker retainedProtected
          have underPrefix := recurse.prepend
            ([block.marker] ++ parityBlock block.seconds)
          simpa [renderProtectedParityGapBlocks,
            renderCondition9GapBlocks, protectedMarker, repeated,
            parityTail, retained, List.append_assoc] using
              removed.trans underPrefix
        · have underPrefix := recurse.prepend
            ([block.marker, block.marker, block.marker] ++
              parityBlock block.seconds)
          simpa [renderProtectedParityGapBlocks,
            renderCondition9GapBlocks, protectedMarker, repeated,
            parityTail, retained, List.append_assoc] using underPrefix
      · have underPrefix := recurse.prepend
          ([block.marker] ++ parityBlock block.seconds)
        simpa [renderProtectedParityGapBlocks,
          renderCondition9GapBlocks, protectedMarker, repeated,
          parityTail, List.append_assoc] using underPrefix

theorem listDerivesLeeLiCondition9Normal (word : Word Nat) :
    ListDerives word.toList (leeLiCondition9NormalList word) := by
  let blocks := S5_870.gapBlocksList word.toList
  have installed := listDerivesProtectGapBlocks blocks
  have normalized :=
    listDerivesNormalizeProtectedGapBlocks
      (S5_870.gapBlocksList_wellFormed word.toList) [] (by simp)
  have cleaned := listDerivesCleanupGapBlocks blocks
  rw [S5_870.render_gapBlocksList word.toList] at installed
  simpa [blocks, leeLiCondition9NormalList] using
    installed.trans (normalized.trans cleaned)

private def wordOfListOr (fallback : Nat) : List Nat → Word Nat
  | [] => Word.singleton fallback
  | head :: tail => ⟨head, tail⟩

private theorem gapBlocksList_ne_nil (word : Word Nat) :
    S5_870.gapBlocksList word.toList ≠ [] := by
  intro empty
  have rendered := S5_870.render_gapBlocksList word.toList
  rw [empty] at rendered
  cases word with
  | mk head tail => simp [Word.toList, S5_870.renderGapBlocks] at rendered

private theorem renderCondition9GapBlocks_ne_nil
    {blocks : List GapBlock} (nonempty : blocks ≠ []) :
    renderCondition9GapBlocks blocks ≠ [] := by
  cases blocks with
  | nil => contradiction
  | cons block rest =>
      simp only [renderCondition9GapBlocks]
      split <;> simp

theorem leeLiCondition9NormalList_ne_nil (word : Word Nat) :
    leeLiCondition9NormalList word ≠ [] := by
  exact renderCondition9GapBlocks_ne_nil
    (gapBlocksList_ne_nil word)

/-- Lee--Li's Condition 9 normal word. -/
def leeLiCondition9NormalWord (word : Word Nat) : Word Nat :=
  wordOfListOr word.head (leeLiCondition9NormalList word)

@[simp]
theorem leeLiCondition9NormalWord_toList (word : Word Nat) :
    (leeLiCondition9NormalWord word).toList =
      leeLiCondition9NormalList word := by
  unfold leeLiCondition9NormalWord
  cases shape : leeLiCondition9NormalList word with
  | nil => exact False.elim (leeLiCondition9NormalList_ne_nil word shape)
  | cons head tail => rfl

private theorem derives_of_listDerives_toList
    (left right : Word Nat)
    (derivation : ListDerives left.toList right.toList) :
    Derives leeLiCondition9ReversedBasis left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simpa [Word.toList, listWordOfCons] using
            S5_107.ListDerives.toWord derivation

theorem derivesLeeLiCondition9Normal (word : Word Nat) :
    Derives leeLiCondition9ReversedBasis word
      (leeLiCondition9NormalWord word) := by
  apply derives_of_listDerives_toList
  rw [leeLiCondition9NormalWord_toList]
  exact listDerivesLeeLiCondition9Normal word

/-! ## Affine parity skeleton -/

private def leeLiCondition9ParityList (word : Word Nat) : List Nat :=
  renderParityGapBlocks (S5_870.gapBlocksList word.toList)

private theorem renderParityGapBlocks_ne_nil
    {blocks : List GapBlock} (nonempty : blocks ≠ []) :
    renderParityGapBlocks blocks ≠ [] := by
  cases blocks with
  | nil => contradiction
  | cons block rest => simp [renderParityGapBlocks]

private theorem leeLiCondition9ParityList_ne_nil (word : Word Nat) :
    leeLiCondition9ParityList word ≠ [] := by
  exact renderParityGapBlocks_ne_nil (gapBlocksList_ne_nil word)

private def leeLiCondition9ParityWord (word : Word Nat) : Word Nat :=
  wordOfListOr word.head (leeLiCondition9ParityList word)

@[simp]
private theorem leeLiCondition9ParityWord_toList (word : Word Nat) :
    (leeLiCondition9ParityWord word).toList =
      leeLiCondition9ParityList word := by
  unfold leeLiCondition9ParityWord
  cases shape : leeLiCondition9ParityList word with
  | nil => exact False.elim (leeLiCondition9ParityList_ne_nil word shape)
  | cons head tail => rfl

private abbrev AffineListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives affineParityFourOppositeBasis

private theorem affineOppositeDerivesTripleContraction (x : Word Nat) :
    Derives affineParityFourOppositeBasis
      ((x ++ x) ++ x) x := by
  have direct := affineParityDerivesTripleContraction x.reverse
  have opposite := direct.reverse
  simpa [affineParityFourOppositeBasis, Word.append_assoc] using opposite

private theorem affineListDerivesContractTriple
    (before after : List Nat) (letter : Nat) :
    AffineListDerives
      (before ++ [letter, letter, letter] ++ after)
      (before ++ [letter] ++ after) := by
  have core := S5_107.ListDerives.ofWord
    (affineOppositeDerivesTripleContraction
      (Word.singleton letter))
  simpa [Word.singleton, Word.append, List.append_assoc] using
    S5_107.ListDerives.context before after core

private theorem affineListDerivesCondition9ToParity :
    ∀ blocks : List GapBlock,
      AffineListDerives
        (renderCondition9GapBlocks blocks)
        (renderParityGapBlocks blocks)
  | [] => S5_107.ListDerives.refl []
  | block :: rest => by
      let parityTail :=
        parityBlock block.seconds ++ renderParityGapBlocks rest
      have recurse := affineListDerivesCondition9ToParity rest
      by_cases retained :
          markerRepeated block rest ∧ block.marker ∉ parityTail
      · have contracted := affineListDerivesContractTriple []
          (parityBlock block.seconds ++
            renderCondition9GapBlocks rest) block.marker
        have underPrefix := recurse.prepend
          ([block.marker] ++ parityBlock block.seconds)
        simpa [renderCondition9GapBlocks, renderParityGapBlocks,
          parityTail, retained, List.append_assoc] using
            contracted.trans underPrefix
      · have underPrefix := recurse.prepend
          ([block.marker] ++ parityBlock block.seconds)
        have retained' :
            ¬(markerRepeated block rest ∧
              block.marker ∉ parityBlock block.seconds ∧
              block.marker ∉ renderParityGapBlocks rest) := by
          intro expanded
          exact retained ⟨expanded.1, by
            simp [parityTail, expanded.2.1, expanded.2.2]⟩
        simpa [renderCondition9GapBlocks, renderParityGapBlocks,
          retained', List.append_assoc] using underPrefix

private theorem affineDerives_of_listDerives_toList
    (left right : Word Nat)
    (derivation : AffineListDerives left.toList right.toList) :
    Derives affineParityFourOppositeBasis left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simpa [Word.toList, listWordOfCons] using
            S5_107.ListDerives.toWord derivation

private theorem affineDerivesCondition9ToParity (word : Word Nat) :
    Derives affineParityFourOppositeBasis
      (leeLiCondition9NormalWord word)
      (leeLiCondition9ParityWord word) := by
  apply affineDerives_of_listDerives_toList
  rw [leeLiCondition9NormalWord_toList,
    leeLiCondition9ParityWord_toList]
  exact affineListDerivesCondition9ToParity
    (S5_870.gapBlocksList word.toList)

private theorem affineModelsReversedBasis :
    Models affineParityFour.semigroup.opposite
      leeLiCondition9ReversedBasis := by
  intro identity member
  exact affineParityEmbedding.pullback_identity identity
    (leeLiCondition9ReversedModels identity member)

private theorem sourceParityAffineValid (word : Word Nat) :
    (Identity.mk word
      (leeLiCondition9ParityWord word)).SatisfiedBy
        affineParityFour.semigroup.opposite := by
  intro valuation
  exact
    ((derivesLeeLiCondition9Normal word).sound
      affineModelsReversedBasis valuation).trans
        ((affineDerivesCondition9ToParity word).sound
          affineParityFourOppositeBasis_complete.1 valuation)

private theorem parityIdentityAffineValid
    {S : Type u} {G : Semigroup S} (semantic : SemanticWitness G)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy G) :
    (Identity.mk
      (leeLiCondition9ParityWord identity.lhs)
      (leeLiCondition9ParityWord identity.rhs)).SatisfiedBy
        affineParityFour.semigroup.opposite := by
  intro valuation
  have sourceValid :=
    semantic.affineConsequence identity valid valuation
  exact (sourceParityAffineValid identity.lhs valuation).symm.trans <|
    sourceValid.trans (sourceParityAffineValid identity.rhs valuation)

/-! ### Reversed affine segments -/

private def paritySegment (block : GapBlock) : AffineParitySegment :=
  ⟨(parityBlock block.seconds).reverse, block.marker⟩

private def reverseParitySegments
    (blocks : List GapBlock) : List AffineParitySegment :=
  blocks.reverse.map paritySegment

@[simp]
private theorem reverseParitySegments_cons
    (block : GapBlock) (rest : List GapBlock) :
    reverseParitySegments (block :: rest) =
      reverseParitySegments rest ++ [paritySegment block] := by
  simp [reverseParitySegments]

private theorem affineParityRender_append
    (left right : List AffineParitySegment) :
    affineParityRender (left ++ right) =
      affineParityRender left ++ affineParityRender right := by
  induction left with
  | nil => rfl
  | cons segment rest induction =>
      simp [affineParityRender, induction, List.append_assoc]

private theorem affineParityMarkers_append
    (left right : List AffineParitySegment) :
    affineParityMarkers (left ++ right) =
      affineParityMarkers left ++ affineParityMarkers right := by
  induction left with
  | nil => rfl
  | cons segment rest induction =>
      simp [affineParityMarkers, induction]

private theorem render_reverseParitySegments (blocks : List GapBlock) :
    affineParityRender (reverseParitySegments blocks) =
      (renderParityGapBlocks blocks).reverse := by
  induction blocks with
  | nil => rfl
  | cons block rest induction =>
      rw [reverseParitySegments_cons, affineParityRender_append,
        induction]
      simp [paritySegment, affineParityRender, renderParityGapBlocks,
        List.reverse_append, List.append_assoc]

private theorem markers_reverseParitySegments (blocks : List GapBlock) :
    affineParityMarkers (reverseParitySegments blocks) =
      (S5_870.gapBlockMarkers blocks).reverse := by
  induction blocks with
  | nil => rfl
  | cons block rest induction =>
      rw [reverseParitySegments_cons, affineParityMarkers_append,
        induction]
      simp [paritySegment, affineParityMarkers,
        S5_870.gapBlockMarkers]

private theorem parityBlock_pairwise (letters : List Nat) :
    (parityBlock letters).Pairwise (· ≤ ·) := by
  have transitive :
      ∀ left middle right : Nat,
        decide (left ≤ middle) = true →
        decide (middle ≤ right) = true →
        decide (left ≤ right) = true := by
    intro left middle right first second
    exact decide_eq_true
      (Nat.le_trans (of_decide_eq_true first)
        (of_decide_eq_true second))
  have total :
      ∀ left right : Nat,
        (decide (left ≤ right) || decide (right ≤ left)) = true := by
    intro left right
    rcases Nat.le_total left right with first | second
    · simp [first]
    · simp [second]
  exact (List.pairwise_mergeSort transitive total
    (parityReduce letters)).imp fun relation =>
      of_decide_eq_true relation

private theorem reverseParitySegments_acc_normal
    {seen : List Nat} {blocks : List GapBlock}
    {tailSegments : List AffineParitySegment}
    (formed : S5_870.GapBlocksWellFormed seen blocks)
    (tailNormal : AffineParitySegmentsNormal tailSegments)
    (tailMarkers : affineParityMarkers tailSegments = seen) :
    AffineParitySegmentsNormal
      (reverseParitySegments blocks ++ tailSegments) := by
  induction formed generalizing tailSegments with
  | nil => simpa [reverseParitySegments] using tailNormal
  | cons seen block rest markerFresh secondsSeen tailFormed induction =>
      have blockNodup : (paritySegment block).parity.Nodup := by
        change List.Pairwise (fun left right : Nat => left ≠ right)
          (parityBlock block.seconds).reverse
        rw [List.pairwise_reverse]
        exact (parityBlock_nodup block.seconds).imp fun different =>
          Ne.symm different
      have markerFreshInTail :
          block.marker ∉ affineParityMarkers tailSegments := by
        simpa [tailMarkers] using markerFresh
      have blockGuard :
          ∀ selected, selected ∈ (paritySegment block).parity →
            selected = block.marker ∨
              selected ∈ affineParityMarkers tailSegments := by
        intro selected member
        have inParityBlock : selected ∈ parityBlock block.seconds := by
          simpa [paritySegment] using member
        rcases List.mem_cons.mp
            (secondsSeen selected
              (mem_of_mem_parityBlock inParityBlock)) with
          atMarker | inSeen
        · exact Or.inl atMarker
        · exact Or.inr <| by simpa [tailMarkers] using inSeen
      have currentNormal :
          AffineParitySegmentsNormal
            (paritySegment block :: tailSegments) :=
        AffineParitySegmentsNormal.cons blockNodup
          markerFreshInTail blockGuard tailNormal
      have currentMarkers :
          affineParityMarkers
              (paritySegment block :: tailSegments) =
            block.marker :: seen := by
        simp [affineParityMarkers, paritySegment, tailMarkers]
      have restNormal := induction currentNormal currentMarkers
      simpa [List.append_assoc] using restNormal

private theorem reverseParitySegments_normal
    {blocks : List GapBlock}
    (formed : S5_870.GapBlocksWellFormed [] blocks) :
    AffineParitySegmentsNormal (reverseParitySegments blocks) := by
  simpa using reverseParitySegments_acc_normal formed
    AffineParitySegmentsNormal.nil rfl

private theorem reverseParitySegments_reverse_sorted
    (blocks : List GapBlock) :
    ∀ segment, segment ∈ reverseParitySegments blocks →
      segment.parity.reverse.Pairwise (· ≤ ·) := by
  intro segment member
  unfold reverseParitySegments at member
  obtain ⟨block, _, rfl⟩ := List.mem_map.mp member
  simpa [paritySegment] using parityBlock_pairwise block.seconds

private theorem reverse_perm
    {left right : List Nat} (permutation : left.Perm right) :
    left.reverse.Perm right.reverse := by
  rw [List.perm_iff_count] at permutation ⊢
  intro selected
  simpa using permutation selected

private theorem affineParitySegments_eq_of_perm_and_reverse_sorted
    {left right : List AffineParitySegment}
    (permutation : AffineParitySegmentsPerm left right)
    (leftSorted : ∀ segment, segment ∈ left →
      segment.parity.reverse.Pairwise (· ≤ ·))
    (rightSorted : ∀ segment, segment ∈ right →
      segment.parity.reverse.Pairwise (· ≤ ·)) :
    left = right := by
  induction permutation with
  | nil => rfl
  | @cons leftBlock rightBlock marker leftRest rightRest
      blockPermutation restPermutation induction =>
      have leftBlockSorted :
          leftBlock.reverse.Pairwise (· ≤ ·) := by
        simpa using leftSorted ⟨leftBlock, marker⟩ (by simp)
      have rightBlockSorted :
          rightBlock.reverse.Pairwise (· ≤ ·) := by
        simpa using rightSorted ⟨rightBlock, marker⟩ (by simp)
      have reversedEqual : leftBlock.reverse = rightBlock.reverse :=
        List.Perm.eq_of_pairwise
          (fun _ _ _ _ leftLe rightLe =>
            Nat.le_antisymm leftLe rightLe)
          leftBlockSorted rightBlockSorted
          (reverse_perm blockPermutation)
      have blockEqual : leftBlock = rightBlock :=
        List.reverse_inj.mp reversedEqual
      have restEqual : leftRest = rightRest :=
        induction
          (fun segment member =>
            leftSorted segment (List.Mem.tail _ member))
          (fun segment member =>
            rightSorted segment (List.Mem.tail _ member))
      subst rightBlock
      rw [restEqual]

private theorem leeLiCondition9ParityList_eq_of_valid
    {S : Type u} {G : Semigroup S} (semantic : SemanticWitness G)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy G) :
    leeLiCondition9ParityList identity.lhs =
      leeLiCondition9ParityList identity.rhs := by
  let leftBlocks := S5_870.gapBlocksList identity.lhs.toList
  let rightBlocks := S5_870.gapBlocksList identity.rhs.toList
  let leftSegments := reverseParitySegments leftBlocks
  let rightSegments := reverseParitySegments rightBlocks
  have leftNormal : AffineParitySegmentsNormal leftSegments := by
    exact reverseParitySegments_normal
      (S5_870.gapBlocksList_wellFormed identity.lhs.toList)
  have rightNormal : AffineParitySegmentsNormal rightSegments := by
    exact reverseParitySegments_normal
      (S5_870.gapBlocksList_wellFormed identity.rhs.toList)
  have leftRender :
      affineParityRender leftSegments =
        (leeLiCondition9ParityList identity.lhs).reverse := by
    simpa [leftSegments, leftBlocks, leeLiCondition9ParityList] using
      render_reverseParitySegments
        (S5_870.gapBlocksList identity.lhs.toList)
  have rightRender :
      affineParityRender rightSegments =
        (leeLiCondition9ParityList identity.rhs).reverse := by
    simpa [rightSegments, rightBlocks, leeLiCondition9ParityList] using
      render_reverseParitySegments
        (S5_870.gapBlocksList identity.rhs.toList)
  let parityIdentity : Identity Nat :=
    ⟨leeLiCondition9ParityWord identity.lhs,
      leeLiCondition9ParityWord identity.rhs⟩
  have oppositeValid :
      parityIdentity.SatisfiedBy
        affineParityFour.semigroup.opposite := by
    exact parityIdentityAffineValid semantic identity valid
  have directValid :
      parityIdentity.reversed.SatisfiedBy
        affineParityFour.semigroup :=
    (Identity.satisfiedBy_opposite_iff_reversed
      parityIdentity affineParityFour.semigroup).1 oppositeValid
  have equalEval :
      ∀ valuation : Nat → Fin 4,
        affineParityListEval valuation
            (affineParityRender leftSegments) =
          affineParityListEval valuation
            (affineParityRender rightSegments) := by
    intro valuation
    rw [leftRender, rightRender]
    have evaluated := directValid valuation
    change
      affineParityFour.semigroup.eval valuation
          (leeLiCondition9ParityWord identity.lhs).reverse =
        affineParityFour.semigroup.eval valuation
          (leeLiCondition9ParityWord identity.rhs).reverse at evaluated
    rw [affineParityEval_eq_listEval,
      affineParityEval_eq_listEval, Word.toList_reverse,
      Word.toList_reverse, leeLiCondition9ParityWord_toList,
      leeLiCondition9ParityWord_toList] at evaluated
    exact evaluated
  have segmentMarkers :
      affineParityMarkers leftSegments =
        affineParityMarkers rightSegments :=
    affineParityMarkers_eq_of_eval_eq leftNormal rightNormal equalEval
  have totalParity : ∀ tested,
      (affineParityRender leftSegments).count tested % 2 =
        (affineParityRender rightSegments).count tested % 2 := by
    intro tested
    rw [leftRender, rightRender]
    have parity :=
      affineParityValid_totalParity
        parityIdentity.reversed directValid tested
    change
      (leeLiCondition9ParityWord identity.lhs).reverse.toList.count
          tested % 2 =
        (leeLiCondition9ParityWord identity.rhs).reverse.toList.count
          tested % 2 at parity
    rw [Word.toList_reverse, Word.toList_reverse,
      leeLiCondition9ParityWord_toList,
      leeLiCondition9ParityWord_toList] at parity
    exact parity
  have suffixParity : ∀ tested marker, tested ≠ marker →
      affineParitySuffixParity tested marker
          (affineParityRender leftSegments) =
        affineParitySuffixParity tested marker
          (affineParityRender rightSegments) := by
    intro tested marker different
    rw [leftRender, rightRender]
    have parity :=
      affineParityValid_suffixParity
        parityIdentity.reversed directValid tested marker different
    change
      affineParitySuffixParity tested marker
          (leeLiCondition9ParityWord identity.lhs).reverse.toList =
        affineParitySuffixParity tested marker
          (leeLiCondition9ParityWord identity.rhs).reverse.toList at parity
    rw [Word.toList_reverse, Word.toList_reverse,
      leeLiCondition9ParityWord_toList,
      leeLiCondition9ParityWord_toList] at parity
    exact parity
  have segmentPermutation :=
    affineParitySegmentsPerm_of_invariants
      leftNormal rightNormal segmentMarkers totalParity suffixParity
  have segmentEqual : leftSegments = rightSegments :=
    affineParitySegments_eq_of_perm_and_reverse_sorted
      segmentPermutation
      (reverseParitySegments_reverse_sorted leftBlocks)
      (reverseParitySegments_reverse_sorted rightBlocks)
  have renderedEqual := congrArg affineParityRender segmentEqual
  rw [leftRender, rightRender] at renderedEqual
  exact List.reverse_inj.mp renderedEqual

/-! ## Capped multiplicity and the Condition 9 exponents -/

private def condition9Enhance
    (repeated seen : List Nat) : List Nat → List Nat
  | [] => []
  | letter :: rest =>
      if letter ∈ seen then
        letter :: condition9Enhance repeated seen rest
      else
        let markerPrefix :=
          if letter ∈ repeated ∧ letter ∉ rest then
            [letter, letter, letter]
          else [letter]
        markerPrefix ++
          condition9Enhance repeated (letter :: seen) rest

private theorem condition9Enhance_append_known
    (repeated seen knownLetters suffix : List Nat)
    (known : ∀ letter, letter ∈ knownLetters → letter ∈ seen) :
    condition9Enhance repeated seen (knownLetters ++ suffix) =
      knownLetters ++ condition9Enhance repeated seen suffix := by
  induction knownLetters with
  | nil => rfl
  | cons head tail induction =>
      have headSeen := known head (List.Mem.head tail)
      have tailKnown :
          ∀ letter, letter ∈ tail → letter ∈ seen := by
        intro letter member
        exact known letter (List.Mem.tail head member)
      simp [condition9Enhance, headSeen, induction tailKnown]

private theorem condition9Enhance_renderParity :
    ∀ {seen blocks repeated},
      S5_870.GapBlocksWellFormed seen blocks →
      (∀ letter, letter ∈ S5_870.gapBlockMarkers blocks →
        (letter ∈ repeated ↔
          letter ∈ S5_870.gapBlockSeconds blocks)) →
      condition9Enhance repeated seen
          (renderParityGapBlocks blocks) =
        renderCondition9GapBlocks blocks
  | seen, [], repeated, formed, agreement => rfl
  | seen, block :: rest, repeated, formed, agreement => by
      cases formed with
      | cons _ _ _ markerFresh secondsSeen tailFormed =>
          have repeatedIff :
              block.marker ∈ repeated ↔ markerRepeated block rest := by
            change block.marker ∈ repeated ↔
              block.marker ∈
                S5_870.gapBlockSeconds (block :: rest)
            exact agreement block.marker (by
              simp [S5_870.gapBlockMarkers])
          have currentKnown :
              ∀ letter, letter ∈ parityBlock block.seconds →
                letter ∈ block.marker :: seen := by
            intro letter member
            exact secondsSeen letter (mem_of_mem_parityBlock member)
          have passCurrent := condition9Enhance_append_known
            repeated (block.marker :: seen)
            (parityBlock block.seconds)
            (renderParityGapBlocks rest) currentKnown
          have tailAgreement :
              ∀ letter,
                letter ∈ S5_870.gapBlockMarkers rest →
                  (letter ∈ repeated ↔
                    letter ∈ S5_870.gapBlockSeconds rest) := by
            intro letter tailMarker
            have currentAbsent : letter ∉ block.seconds := by
              intro current
              have inNextSeen := secondsSeen letter current
              exact (tailFormed.markersAvoidSeen letter inNextSeen)
                tailMarker
            have fullMarker :
                letter ∈ S5_870.gapBlockMarkers (block :: rest) := by
              change letter ∈
                block.marker :: S5_870.gapBlockMarkers rest
              exact List.Mem.tail block.marker tailMarker
            have full := agreement letter fullMarker
            simpa [S5_870.gapBlockSeconds, currentAbsent] using full
          have recurse := condition9Enhance_renderParity
            tailFormed tailAgreement
          simp [condition9Enhance, renderParityGapBlocks,
            renderCondition9GapBlocks, markerFresh, repeatedIff,
            passCurrent, recurse]

private theorem renderCondition9GapBlocks_eq_enhance
    {blocks : List GapBlock}
    (formed : S5_870.GapBlocksWellFormed [] blocks) :
    renderCondition9GapBlocks blocks =
      condition9Enhance (S5_870.gapBlockSeconds blocks) []
        (renderParityGapBlocks blocks) := by
  symm
  exact condition9Enhance_renderParity formed
    (fun _ _ => Iff.rfl)

private theorem condition9Enhance_eq_of_mem_iff
    {leftRepeated rightRepeated : List Nat}
    (same : ∀ letter,
      letter ∈ leftRepeated ↔ letter ∈ rightRepeated) :
    ∀ seen letters,
      condition9Enhance leftRepeated seen letters =
        condition9Enhance rightRepeated seen letters := by
  intro seen letters
  induction letters generalizing seen with
  | nil => rfl
  | cons head tail induction =>
      simp [condition9Enhance, same head, induction]

private theorem mem_gapBlockSeconds_iff_two_le_count
    {blocks : List GapBlock}
    (formed : S5_870.GapBlocksWellFormed [] blocks)
    (tested : Nat) :
    tested ∈ S5_870.gapBlockSeconds blocks ↔
      2 ≤ (S5_870.renderGapBlocks blocks).count tested := by
  rw [S5_870.count_renderGapBlocks]
  have markersNodup := formed.markersNodup
  have markerCountLe :
      (S5_870.gapBlockMarkers blocks).count tested ≤ 1 := by
    rw [markersNodup.count]
    split <;> omega
  constructor
  · intro inSeconds
    have inMarkers : tested ∈ S5_870.gapBlockMarkers blocks :=
      (formed.secondsInSeenOrMarkers tested inSeconds).resolve_left
        (by simp)
    have markerCount :
        (S5_870.gapBlockMarkers blocks).count tested = 1 := by
      rw [markersNodup.count]
      simp [inMarkers]
    have secondsPositive :
        0 < (S5_870.gapBlockSeconds blocks).count tested :=
      List.count_pos_iff.mpr inSeconds
    rw [markerCount]
    omega
  · intro total
    have secondsPositive :
        0 < (S5_870.gapBlockSeconds blocks).count tested := by
      omega
    exact List.count_pos_iff.mp secondsPositive

private theorem two_le_iff_of_min_two_eq
    {left right : Nat} (same : min left 2 = min right 2) :
    (2 ≤ left ↔ 2 ≤ right) := by
  omega

private theorem leeLiCondition9NormalList_eq_of_valid
    {S : Type u} {G : Semigroup S} (semantic : SemanticWitness G)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy G) :
    leeLiCondition9NormalList identity.lhs =
      leeLiCondition9NormalList identity.rhs := by
  let leftBlocks := S5_870.gapBlocksList identity.lhs.toList
  let rightBlocks := S5_870.gapBlocksList identity.rhs.toList
  have leftFormed : S5_870.GapBlocksWellFormed [] leftBlocks :=
    S5_870.gapBlocksList_wellFormed identity.lhs.toList
  have rightFormed : S5_870.GapBlocksWellFormed [] rightBlocks :=
    S5_870.gapBlocksList_wellFormed identity.rhs.toList
  have parityEqual :=
    leeLiCondition9ParityList_eq_of_valid semantic identity valid
  change renderParityGapBlocks leftBlocks =
    renderParityGapBlocks rightBlocks at parityEqual
  have cappedCounts := sameCappedCounts_of_valid semantic identity valid
  have repeatedEqual : ∀ tested,
      tested ∈ S5_870.gapBlockSeconds leftBlocks ↔
        tested ∈ S5_870.gapBlockSeconds rightBlocks := by
    intro tested
    rw [mem_gapBlockSeconds_iff_two_le_count leftFormed tested,
      mem_gapBlockSeconds_iff_two_le_count rightFormed tested]
    have threshold := two_le_iff_of_min_two_eq (cappedCounts tested)
    simpa [leftBlocks, rightBlocks,
      S5_870.render_gapBlocksList] using threshold
  have leftEnhance := renderCondition9GapBlocks_eq_enhance leftFormed
  have rightEnhance := renderCondition9GapBlocks_eq_enhance rightFormed
  change renderCondition9GapBlocks leftBlocks =
    renderCondition9GapBlocks rightBlocks
  calc
    renderCondition9GapBlocks leftBlocks =
        condition9Enhance (S5_870.gapBlockSeconds leftBlocks) []
          (renderParityGapBlocks leftBlocks) := leftEnhance
    _ = condition9Enhance (S5_870.gapBlockSeconds rightBlocks) []
          (renderParityGapBlocks leftBlocks) :=
      condition9Enhance_eq_of_mem_iff repeatedEqual [] _
    _ = condition9Enhance (S5_870.gapBlockSeconds rightBlocks) []
          (renderParityGapBlocks rightBlocks) :=
      congrArg
        (condition9Enhance
          (S5_870.gapBlockSeconds rightBlocks) []) parityEqual
    _ = renderCondition9GapBlocks rightBlocks := rightEnhance.symm

private theorem leeLiCondition9NormalWord_eq_of_valid
    {S : Type u} {G : Semigroup S} (semantic : SemanticWitness G)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy G) :
    leeLiCondition9NormalWord identity.lhs =
      leeLiCondition9NormalWord identity.rhs := by
  apply Word.toList_injective
  rw [leeLiCondition9NormalWord_toList,
    leeLiCondition9NormalWord_toList]
  exact leeLiCondition9NormalList_eq_of_valid semantic identity valid

/-- The shared Condition 9 completeness theorem.  A catalogue endpoint must
provide actual semantic transports from its table to the two separating
factors; table IDs, hashes, and bounded-signature membership are not inputs. -/
theorem reversedBasisForOfSemanticWitness
    {S : Type u} {G : Semigroup S} (semantic : SemanticWitness G) :
    BasisFor G leeLiCondition9ReversedBasis := by
  refine ⟨semantic.models, ?_⟩
  intro identity valid
  have normalEqual :=
    leeLiCondition9NormalWord_eq_of_valid semantic identity valid
  exact (derivesLeeLiCondition9Normal identity.lhs).trans <| by
    rw [normalEqual]
    exact (derivesLeeLiCondition9Normal identity.rhs).symm

private theorem leeLiCondition9ReversedBasisFor :
    BasisFor leeLiCondition9Table.semigroup
      leeLiCondition9ReversedBasis :=
  reversedBasisForOfSemanticWitness sourceSemanticWitness

/-- Unconditional Condition 9 source-table theorem for the exact direct
ten-law basis with hash `573195da...`. The catalogue-facing bindings and
transports are supplied by `Order6LeeLiCondition9Roots`; this theorem does not
close the other nine recorded order-six rows by itself. -/
theorem leeLiCondition9BasisFor :
    BasisFor leeLiCondition9Semigroup leeLiCondition9Basis := by
  simpa [leeLiCondition9Semigroup, leeLiCondition9Basis] using
    leeLiCondition9ReversedBasisFor.oppositeReversed

end SemigroupBasis.CoRoots.Order6LeeLiCondition9
