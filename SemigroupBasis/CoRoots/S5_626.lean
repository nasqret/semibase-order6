import SemigroupBasis.Examples.FinalMarkerThree
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder4
import SemigroupBasis.Generated.CatalogueOrder5Part05
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

namespace SemigroupBasis.CoRoots.S5_626

open SemigroupBasis
open SemigroupBasis.Examples

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxxx : Word Nat := w 0 [0, 0, 0]
def xy : Word Nat := w 0 [1]
def xyyy : Word Nat := w 0 [1, 1, 1]
def xxy : Word Nat := w 0 [0, 1]
def xxyxx : Word Nat := w 0 [0, 1, 0, 0]
def xyx : Word Nat := w 0 [1, 0]
def xxxyx : Word Nat := w 0 [0, 0, 1, 0]
def xyxyy : Word Nat := w 0 [1, 0, 1, 1]
def xyyxy : Word Nat := w 0 [1, 1, 0, 1]
def xyz : Word Nat := w 0 [1, 2]
def xyzyy : Word Nat := w 0 [1, 2, 1, 1]
def xxxy : Word Nat := w 0 [0, 0, 1]
def xyxx : Word Nat := w 0 [1, 0, 0]
def xyxy : Word Nat := w 0 [1, 0, 1]
def xyyx : Word Nat := w 0 [1, 1, 0]
def xyzxy : Word Nat := w 0 [1, 2, 0, 1]
def xyzyx : Word Nat := w 0 [1, 2, 1, 0]
def xyzxz : Word Nat := w 0 [1, 2, 0, 2]
def xyzzx : Word Nat := w 0 [1, 2, 2, 0]

def squareExpansionLaw : Identity Nat := ⟨xx, xxxx⟩
def tailCubeLaw : Identity Nat := ⟨xy, xyyy⟩
def prefixSquareLiftLaw : Identity Nat := ⟨xxy, xxyxx⟩
def initialTripleLiftLaw : Identity Nat := ⟨xyx, xxxyx⟩
def trailingSquareLiftLaw : Identity Nat := ⟨xyx, xyxyy⟩
def middleSquareLiftLaw : Identity Nat := ⟨xyx, xyyxy⟩
def markerSquareLiftLaw : Identity Nat := ⟨xyz, xyzyy⟩
def systemThreeBalanceLaw : Identity Nat := ⟨xxxy, xyxx⟩
def systemThreeSwapLaw : Identity Nat := ⟨xyxy, xyyx⟩
def ternarySwapYLaw : Identity Nat := ⟨xyzxy, xyzyx⟩
def ternarySwapZLaw : Identity Nat := ⟨xyzxz, xyzzx⟩

/-- The exact ordered eleven-law basis recorded for `S5_626`.
This foundation source asserts finite semantics and finite derivations only. -/
def basis : List (Identity Nat) :=
  [squareExpansionLaw, tailCubeLaw, prefixSquareLiftLaw,
    initialTripleLiftLaw, trailingSquareLiftLaw, middleSquareLiftLaw,
    markerSquareLiftLaw, systemThreeBalanceLaw, systemThreeSwapLaw,
    ternarySwapYLaw, ternarySwapZLaw]

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

/-- Exhaustive checks on the three displayed variables lift to natural-number
variables. This theorem does not assert completeness. -/
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
  Generated.Catalogue.S5_626.table

abbrev affineParityFactorTable : FiniteTable :=
  Generated.Catalogue.S4_96.table

abbrev initialMarkerFactorTable : FiniteTable :=
  finalMarkerThree

set_option maxRecDepth 100000 in
/-- The direct Smallsemi representative satisfies the eleven recorded laws. -/
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide)

/-- Anti-isomorphism replay: the opposite representative satisfies the
literal reversed basis. -/
theorem oppositeModels :
    Models table.semigroup.opposite oppositeBasis :=
  models.oppositeReversed

private theorem satisfiedBy_of_joint_homs
    {A : Type u} {B : Type v} {C : Type w} {α : Type z}
    {G : Semigroup A} {H : Semigroup B} {K : Semigroup C}
    (left : Hom G H) (right : Hom G K)
    (joint :
      Function.Injective fun value =>
        (left.toFun value, right.toFun value))
    (identity : Identity α)
    (leftValid : identity.SatisfiedBy H)
    (rightValid : identity.SatisfiedBy K) :
    identity.SatisfiedBy G := by
  intro valuation
  apply joint
  apply Prod.ext
  · change
      left.toFun (G.eval valuation identity.lhs) =
        left.toFun (G.eval valuation identity.rhs)
    rw [left.map_eval, left.map_eval]
    exact leftValid (fun x => left.toFun (valuation x))
  · change
      right.toFun (G.eval valuation identity.lhs) =
        right.toFun (G.eval valuation identity.rhs)
    rw [right.map_eval, right.map_eval]
    exact rightValid (fun x => right.toFun (valuation x))

/-- The zero-based section `[2,3,0,4]` embeds `S4_96` opposite in
`S5_626`. -/
def affineParityEmbedding :
    Embedding affineParityFactorTable.semigroup.opposite table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨2, by decide⟩ else
      if a.val = 1 then ⟨3, by decide⟩ else
        if a.val = 2 then ⟨0, by decide⟩ else ⟨4, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

/-- The zero-based quotient `[2,2,0,1,3]` split-surjects onto `S4_96`
opposite. -/
def affineParityQuotient :
    SplitSurjection table.semigroup
      affineParityFactorTable.semigroup.opposite where
  toFun := fun a =>
    if a.val = 0 then ⟨2, by decide⟩ else
      if a.val = 1 then ⟨2, by decide⟩ else
        if a.val = 2 then ⟨0, by decide⟩ else
          if a.val = 3 then ⟨1, by decide⟩ else ⟨3, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := affineParityEmbedding.toFun
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

/-- The zero-based section `[0,1,2]` embeds `S3_6` opposite in `S5_626`. -/
def initialMarkerEmbedding :
    Embedding initialMarkerFactorTable.semigroup.opposite table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨1, by decide⟩ else ⟨2, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

/-- The zero-based quotient `[0,1,2,2,0]` split-surjects onto `S3_6`
opposite. -/
def initialMarkerQuotient :
    SplitSurjection table.semigroup
      initialMarkerFactorTable.semigroup.opposite where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨1, by decide⟩ else
        if a.val = 2 then ⟨2, by decide⟩ else
          if a.val = 3 then ⟨2, by decide⟩ else ⟨0, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := initialMarkerEmbedding.toFun
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

/-- The five recorded factor-product images are pairwise distinct. -/
theorem factorPair_injective :
    Function.Injective fun a =>
      (affineParityQuotient.toFun a, initialMarkerQuotient.toFun a) := by
  intro a b
  revert a b
  decide

theorem valid_s4_96_opposite (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy affineParityFactorTable.semigroup.opposite :=
  affineParityQuotient.pushforwardIdentity identity valid

theorem valid_s3_6_opposite (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy initialMarkerFactorTable.semigroup.opposite :=
  initialMarkerQuotient.pushforwardIdentity identity valid

/-- The two quotient term functions jointly determine the target term
function. This is a semantic identity sandwich, not a basis transfer. -/
theorem valid_iff_factors (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔
      identity.SatisfiedBy affineParityFactorTable.semigroup.opposite ∧
        identity.SatisfiedBy initialMarkerFactorTable.semigroup.opposite := by
  constructor
  · intro valid
    exact ⟨valid_s4_96_opposite identity valid,
      valid_s3_6_opposite identity valid⟩
  · rintro ⟨affineValid, initialValid⟩
    exact satisfiedBy_of_joint_homs
      affineParityQuotient.toHom initialMarkerQuotient.toHom
      factorPair_injective identity affineValid initialValid

/-- Keep first occurrences in their original left-to-right order. -/
def firstOccurrenceSequenceList : List Nat → List Nat
  | [] => []
  | letter :: rest =>
      letter :: (firstOccurrenceSequenceList rest).filter
        (fun old => decide (old ≠ letter))

def parityVector (letters variables : List Nat) : List Nat :=
  variables.map fun letter => letters.count letter % 2

private def firstOccurrenceParityProfileAux
    (seen stem : List Nat) : List Nat → List (Nat × List Nat)
  | [] => []
  | letter :: rest =>
      let nextPrefix := stem ++ [letter]
      if letter ∈ seen then
        firstOccurrenceParityProfileAux seen nextPrefix rest
      else
        (letter, parityVector stem seen) ::
          firstOccurrenceParityProfileAux
            (seen ++ [letter]) nextPrefix rest

/-- At each new first occurrence, record the parity vector of the variables
already seen. -/
def FirstOccurrenceParityProfile
    (word : Word Nat) : List (Nat × List Nat) :=
  firstOccurrenceParityProfileAux [] [] word.toList

def FirstOccurrenceSequence (word : Word Nat) : List Nat :=
  firstOccurrenceSequenceList word.toList

def FinalParityVector (word : Word Nat) : List Nat :=
  parityVector word.toList (FirstOccurrenceSequence word)

/-- Since a word is nonempty, its initial variable occurs exactly once iff it
does not occur in the tail. -/
def InitialOccursExactlyOnce (word : Word Nat) : Prop :=
  word.head ∉ word.tail

def GloballySimpleInitial (word : Word Nat) (letter : Nat) : Prop :=
  word.head = letter ∧ InitialOccursExactlyOnce word

def SameGloballySimpleInitial (left right : Word Nat) : Prop :=
  ∀ letter, GloballySimpleInitial left letter ↔
    GloballySimpleInitial right letter

/-- The intended four-component syntax signature. No semantic completeness or
derivability theorem for this relation is asserted here. -/
structure SameS5_626Signature (left right : Word Nat) : Prop where
  firstOccurrences :
    FirstOccurrenceSequence left = FirstOccurrenceSequence right
  parityBeforeFirstOccurrences :
    FirstOccurrenceParityProfile left = FirstOccurrenceParityProfile right
  finalParity : FinalParityVector left = FinalParityVector right
  initialOccursExactlyOnce :
    InitialOccursExactlyOnce left ↔ InitialOccursExactlyOnce right

/-- The factor-level signature established by the exact split quotients. -/
structure SameFactorSignature (left right : Word Nat) : Prop where
  affineTermFunction :
    (Identity.mk left right).SatisfiedBy
      affineParityFactorTable.semigroup.opposite
  initialOccursExactlyOnce :
    InitialOccursExactlyOnce left ↔ InitialOccursExactlyOnce right

private def initialMarkerSeparator (letter : Nat) : Nat → Fin 3 :=
  fun tested => if tested = letter then 1 else 2

private theorem initialMarkerFold (letter : Nat) :
    ∀ (letters : List Nat) (initial : Fin 3),
      letters.foldl
          (fun value tested =>
            finalMarkerThree.semigroup.opposite.mul value
              (initialMarkerSeparator letter tested))
          initial =
        if letter ∈ letters then 0 else initial
  | [], initial => by simp
  | tested :: rest, initial => by
      simp only [List.foldl_cons]
      rw [initialMarkerFold letter rest]
      by_cases testedEq : tested = letter
      · subst tested
        simp [initialMarkerSeparator, finalMarkerThree,
          FiniteTable.semigroup, Semigroup.opposite,
          finalMarkerThreeMul]
      · by_cases restMem : letter ∈ rest
        · simp [initialMarkerSeparator, testedEq, restMem,
            finalMarkerThree, FiniteTable.semigroup,
            Semigroup.opposite, finalMarkerThreeMul]
        · have letterNeTested : letter ≠ tested :=
            fun equality => testedEq equality.symm
          simp only [List.mem_cons, restMem, or_false, letterNeTested,
            if_false]
          simp [initialMarkerSeparator, testedEq,
            finalMarkerThree, FiniteTable.semigroup,
            Semigroup.opposite, finalMarkerThreeMul]

private theorem initialMarkerEval
    (word : Word Nat) (letter : Nat) :
    finalMarkerThree.semigroup.opposite.eval
        (initialMarkerSeparator letter) word =
      if letter ∈ word.tail then (0 : Fin 3)
      else if word.head = letter then (1 : Fin 3) else (2 : Fin 3) := by
  cases word with
  | mk head tail =>
      simp only [Semigroup.eval]
      rw [initialMarkerFold letter tail]
      by_cases tailMem : letter ∈ tail
      · simp [tailMem]
      · by_cases headEq : head = letter
        · subst head
          simp [tailMem, initialMarkerSeparator]
        · simp [tailMem, headEq, initialMarkerSeparator]

private theorem initialMarkerEval_eq_one_iff
    (word : Word Nat) (letter : Nat) :
    finalMarkerThree.semigroup.opposite.eval
        (initialMarkerSeparator letter) word = (1 : Fin 3) ↔
      GloballySimpleInitial word letter := by
  rw [initialMarkerEval]
  by_cases tailMem : letter ∈ word.tail
  · by_cases headEq : word.head = letter
    · subst letter
      simp [tailMem, GloballySimpleInitial,
        InitialOccursExactlyOnce]
    · simp [tailMem, headEq, GloballySimpleInitial,
        InitialOccursExactlyOnce]
  · by_cases headEq : word.head = letter
    · simp [tailMem, headEq, GloballySimpleInitial,
        InitialOccursExactlyOnce]
    · simp [tailMem, headEq, GloballySimpleInitial,
        InitialOccursExactlyOnce]

theorem oppositeFinalMarkerValid_simpleInitial_iff
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy initialMarkerFactorTable.semigroup.opposite)
    (letter : Nat) :
    GloballySimpleInitial identity.lhs letter ↔
      GloballySimpleInitial identity.rhs letter := by
  have evaluated := valid (initialMarkerSeparator letter)
  constructor
  · intro leftSimple
    have leftOne :
        finalMarkerThree.semigroup.opposite.eval
            (initialMarkerSeparator letter) identity.lhs = (1 : Fin 3) :=
      (initialMarkerEval_eq_one_iff identity.lhs letter).2 leftSimple
    have rightOne :
        finalMarkerThree.semigroup.opposite.eval
            (initialMarkerSeparator letter) identity.rhs = (1 : Fin 3) :=
      evaluated.symm.trans leftOne
    exact (initialMarkerEval_eq_one_iff identity.rhs letter).1 rightOne
  · intro rightSimple
    have rightOne :
        finalMarkerThree.semigroup.opposite.eval
            (initialMarkerSeparator letter) identity.rhs = (1 : Fin 3) :=
      (initialMarkerEval_eq_one_iff identity.rhs letter).2 rightSimple
    have leftOne :
        finalMarkerThree.semigroup.opposite.eval
            (initialMarkerSeparator letter) identity.lhs = (1 : Fin 3) :=
      evaluated.trans rightOne
    exact (initialMarkerEval_eq_one_iff identity.lhs letter).1 leftOne

theorem sameInitialOccursExactlyOnce_of_valid_s3_6_opposite
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy initialMarkerFactorTable.semigroup.opposite) :
    InitialOccursExactlyOnce identity.lhs ↔
      InitialOccursExactlyOnce identity.rhs := by
  have same := oppositeFinalMarkerValid_simpleInitial_iff identity valid
  constructor
  · intro leftSimple
    have leftGlobal :
        GloballySimpleInitial identity.lhs identity.lhs.head :=
      ⟨rfl, leftSimple⟩
    exact ((same identity.lhs.head).1 leftGlobal).2
  · intro rightSimple
    have rightGlobal :
        GloballySimpleInitial identity.rhs identity.rhs.head :=
      ⟨rfl, rightSimple⟩
    exact ((same identity.rhs.head).2 rightGlobal).2

theorem sameFactorSignature_of_factors
    (identity : Identity Nat)
    (affineValid :
      identity.SatisfiedBy affineParityFactorTable.semigroup.opposite)
    (initialValid :
      identity.SatisfiedBy initialMarkerFactorTable.semigroup.opposite) :
    SameFactorSignature identity.lhs identity.rhs :=
  ⟨affineValid,
    sameInitialOccursExactlyOnce_of_valid_s3_6_opposite
      identity initialValid⟩

theorem valid_factorSignature
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SameFactorSignature identity.lhs identity.rhs :=
  sameFactorSignature_of_factors identity
    (valid_s4_96_opposite identity valid)
    (valid_s3_6_opposite identity valid)

private theorem affineParityFactorModels :
    Models affineParityFactorTable.semigroup.opposite basis := by
  intro identity member
  exact valid_s4_96_opposite identity (models identity member)

private theorem initialMarkerFactorModels :
    Models initialMarkerFactorTable.semigroup.opposite basis := by
  intro identity member
  exact valid_s3_6_opposite identity (models identity member)

/-- Every finite derivation preserves the established factor-level
signature. The bridge to the four-component syntax signature remains open. -/
theorem derives_factorSignature {left right : Word Nat}
    (derivation : Derives basis left right) :
    SameFactorSignature left right :=
  sameFactorSignature_of_factors ⟨left, right⟩
    (fun valuation =>
      derivation.sound affineParityFactorModels valuation)
    (fun valuation =>
      derivation.sound initialMarkerFactorModels valuation)

private def instantiateThreeWords
    (u v z : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private theorem basisSquareExpansion : Derives basis xx xxxx :=
  Derives.fromBasis (e := squareExpansionLaw) <| by simp [basis]

private theorem basisTailCube : Derives basis xy xyyy :=
  Derives.fromBasis (e := tailCubeLaw) <| by simp [basis]

private theorem basisPrefixSquareLift : Derives basis xxy xxyxx :=
  Derives.fromBasis (e := prefixSquareLiftLaw) <| by simp [basis]

private theorem basisInitialTripleLift : Derives basis xyx xxxyx :=
  Derives.fromBasis (e := initialTripleLiftLaw) <| by simp [basis]

private theorem basisTrailingSquareLift : Derives basis xyx xyxyy :=
  Derives.fromBasis (e := trailingSquareLiftLaw) <| by simp [basis]

private theorem basisMiddleSquareLift : Derives basis xyx xyyxy :=
  Derives.fromBasis (e := middleSquareLiftLaw) <| by simp [basis]

private theorem basisMarkerSquareLift : Derives basis xyz xyzyy :=
  Derives.fromBasis (e := markerSquareLiftLaw) <| by simp [basis]

private theorem basisSystemThreeBalance : Derives basis xxxy xyxx :=
  Derives.fromBasis (e := systemThreeBalanceLaw) <| by simp [basis]

private theorem basisSystemThreeSwap : Derives basis xyxy xyyx :=
  Derives.fromBasis (e := systemThreeSwapLaw) <| by simp [basis]

private theorem basisTernarySwapY : Derives basis xyzxy xyzyx :=
  Derives.fromBasis (e := ternarySwapYLaw) <| by simp [basis]

private theorem basisTernarySwapZ : Derives basis xyzxz xyzzx :=
  Derives.fromBasis (e := ternarySwapZLaw) <| by simp [basis]

theorem derivesSquareExpansion (u : Word Nat) :
    Derives basis (u ++ u) (((u ++ u) ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisSquareExpansion (instantiateThreeWords u u u)
  simpa [xx, xxxx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesTailCube (u v : Word Nat) :
    Derives basis (u ++ v) (((u ++ v) ++ v) ++ v) := by
  have substituted :=
    Derives.subst basisTailCube (instantiateThreeWords u v v)
  simpa [xy, xyyy, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesPrefixSquareLift (u v : Word Nat) :
    Derives basis ((u ++ u) ++ v)
      ((((u ++ u) ++ v) ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisPrefixSquareLift (instantiateThreeWords u v v)
  simpa [xxy, xxyxx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesInitialTripleLift (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u)
      ((((u ++ u) ++ u) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisInitialTripleLift (instantiateThreeWords u v v)
  simpa [xyx, xxxyx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesTrailingSquareLift (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u)
      ((((u ++ v) ++ u) ++ v) ++ v) := by
  have substituted :=
    Derives.subst basisTrailingSquareLift (instantiateThreeWords u v v)
  simpa [xyx, xyxyy, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesMiddleSquareLift (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u)
      ((((u ++ v) ++ v) ++ u) ++ v) := by
  have substituted :=
    Derives.subst basisMiddleSquareLift (instantiateThreeWords u v v)
  simpa [xyx, xyyxy, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesMarkerSquareLift (u v z : Word Nat) :
    Derives basis ((u ++ v) ++ z)
      ((((u ++ v) ++ z) ++ v) ++ v) := by
  have substituted :=
    Derives.subst basisMarkerSquareLift (instantiateThreeWords u v z)
  simpa [xyz, xyzyy, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesSystemThreeBalance (u v : Word Nat) :
    Derives basis (((u ++ u) ++ u) ++ v)
      (((u ++ v) ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisSystemThreeBalance (instantiateThreeWords u v v)
  simpa [xxxy, xyxx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesSystemThreeSwap (u v : Word Nat) :
    Derives basis (((u ++ v) ++ u) ++ v)
      (((u ++ v) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisSystemThreeSwap (instantiateThreeWords u v v)
  simpa [xyxy, xyyx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesTernarySwapY (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ z) ++ u) ++ v)
      ((((u ++ v) ++ z) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisTernarySwapY (instantiateThreeWords u v z)
  simpa [xyzxy, xyzyx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesTernarySwapZ (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ z) ++ u) ++ z)
      ((((u ++ v) ++ z) ++ z) ++ u) := by
  have substituted :=
    Derives.subst basisTernarySwapZ (instantiateThreeWords u v z)
  simpa [xyzxz, xyzzx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- A concrete neutral pair can be appended once three copies are already
present. This does not repair an arbitrary segmented word. -/
theorem derivesOddNeutralPairExpansion (u : Word Nat) :
    Derives basis ((u ++ u) ++ u)
      ((((u ++ u) ++ u) ++ u) ++ u) := by
  have extended := Derives.appendRight (derivesSquareExpansion u) u
  simpa [Word.append_assoc] using extended

/-- Exact bounded chains replayed by the metadata-only packet. -/
def recordedFiniteChains : List (List (Word Nat)) :=
  [
    [w 0 [0], w 0 [0, 0, 0]],
    [w 0 [1], w 0 [1, 1, 1]],
    [w 0 [0, 1], w 0 [0, 1, 0, 0]],
    [w 0 [1, 0], w 0 [0, 0, 1, 0]],
    [w 0 [1, 0], w 0 [1, 0, 1, 1]],
    [w 0 [1, 0], w 0 [1, 1, 0, 1]],
    [w 0 [1, 2], w 0 [1, 2, 1, 1]],
    [w 0 [0, 0, 1], w 0 [1, 0, 0]],
    [w 0 [1, 0, 1], w 0 [1, 1, 0]],
    [w 0 [1, 2, 0, 1], w 0 [1, 2, 1, 0]],
    [w 0 [1, 2, 0, 2], w 0 [1, 2, 2, 0]],
    [w 0 [0, 0], w 0 [0, 0, 0, 0]]
  ]

/- The unrestricted target normalizer is intentionally absent. The missing
argument must segment at first occurrences, reduce and sort each parity block
without crossing the next marker, and then repair a globally repeated odd
initial variable with a neutral pair. The source does not assert invariant
completeness, signature sufficiency, a completeness endpoint, compilation,
proof-object acceptance, or release. -/

end SemigroupBasis.CoRoots.S5_626
