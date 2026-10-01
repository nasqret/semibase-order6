import SemigroupBasis.Examples.FinalMarkerThree
import SemigroupBasis.Examples.ParityInitialFourSyntax
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder4
import SemigroupBasis.Generated.CatalogueOrder5Part05
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

namespace SemigroupBasis.CoRoots.S5_579

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xxxy : Word Nat := w 0 [0, 0, 1]
def xy : Word Nat := w 0 [1]
def xyx : Word Nat := w 0 [1, 0]
def xxyyy : Word Nat := w 0 [0, 1, 1, 1]

def powerTailLaw : Identity Nat := ⟨xxxy, xy⟩
def repeatedFinalLaw : Identity Nat := ⟨xyx, xxyyy⟩

/-- The exact ordered Lee-system-(2) basis recorded for `S5_579`.
This foundation source asserts finite semantics and finite derivations only. -/
def basis : List (Identity Nat) :=
  [powerTailLaw, repeatedFinalLaw]

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

private def toFinTwo : Nat → Fin 2
  | 0 => 0
  | _ => 1

def finiteBasis : List (Identity (Fin 2)) :=
  basis.map fun identity => identity.map toFinTwo

private theorem basis_roundTrip_checked :
    basis.all (fun identity =>
      decide ((identity.map toFinTwo).map Fin.val = identity)) = true := by
  decide

private theorem basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ basis) :
    (identity.map toFinTwo).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basis_roundTrip_checked) identity member

/-- Exhaustive checks on the two displayed variables lift to natural-number
variables. This theorem does not assert completeness. -/
theorem models_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteBasis.all candidate.checkIdentity = true) :
    Models candidate.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinTwo ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityNat_sound (identity.map toFinTwo)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [basis_roundTrip identity member] at finiteValid
  exact finiteValid

abbrev table : FiniteTable :=
  Generated.Catalogue.S5_579.table

abbrev parityFactorTable : FiniteTable :=
  Generated.Catalogue.S4_95.table

abbrev finalMarkerFactorTable : FiniteTable :=
  Examples.finalMarkerThree

set_option maxRecDepth 100000 in
/-- The direct Smallsemi representative satisfies the two recorded laws. -/
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide)

/-- The opposite representative satisfies the literal reversed laws. -/
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

/-- The recorded section `[3,4,1,5]` embeds `S4_95` in `S5_579`. -/
def parityEmbedding :
    Embedding parityFactorTable.semigroup table.semigroup where
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

/-- The recorded quotient `[3,3,1,2,4]` split-surjects onto `S4_95`. -/
def parityQuotient :
    SplitSurjection table.semigroup parityFactorTable.semigroup where
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
  preimage := parityEmbedding.toFun
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

/-- The recorded section `[1,2,3]` embeds `S3_6` in `S5_579`. -/
def finalMarkerEmbedding :
    Embedding finalMarkerFactorTable.semigroup table.semigroup where
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

/-- The recorded quotient `[1,2,3,3,1]` split-surjects onto `S3_6`. -/
def finalMarkerQuotient :
    SplitSurjection table.semigroup finalMarkerFactorTable.semigroup where
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
  preimage := finalMarkerEmbedding.toFun
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

/-- The five recorded product images are pairwise distinct. -/
theorem factorPair_injective :
    Function.Injective fun a =>
      (parityQuotient.toFun a, finalMarkerQuotient.toFun a) := by
  intro a b
  revert a b
  decide

theorem valid_s4_95 (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy parityFactorTable.semigroup :=
  parityQuotient.pushforwardIdentity identity valid

theorem valid_s3_6 (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy finalMarkerFactorTable.semigroup :=
  finalMarkerQuotient.pushforwardIdentity identity valid

/-- The two quotient term functions jointly determine the target term
function. This is a semantic identity sandwich, not a completeness endpoint. -/
theorem valid_iff_factors (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔
      identity.SatisfiedBy parityFactorTable.semigroup ∧
        identity.SatisfiedBy finalMarkerFactorTable.semigroup := by
  constructor
  · intro valid
    exact ⟨valid_s4_95 identity valid, valid_s3_6 identity valid⟩
  · rintro ⟨parityValid, finalValid⟩
    exact satisfiedBy_of_joint_homs
      parityQuotient.toHom finalMarkerQuotient.toHom
      factorPair_injective identity parityValid finalValid

/-- The syntax-only profile supplied by `ParityInitialFourSyntax`. It records
variables in first-occurrence order and one or two copies according to their
total multiplicity parity. -/
def FirstOccurrenceParityProfile (word : Word Nat) : List Nat :=
  Examples.parityInitialNormalList word.toList

def SameFirstOccurrenceParity (left right : Word Nat) : Prop :=
  FirstOccurrenceParityProfile left = FirstOccurrenceParityProfile right

/-- The final letter occurs globally exactly once. -/
def GloballySimpleFinal (word : Word Nat) (letter : Nat) : Prop :=
  (Examples.splitPrefixFinal word).2 = letter ∧
    letter ∉ (Examples.splitPrefixFinal word).1

def SameGloballySimpleFinal (left right : Word Nat) : Prop :=
  ∀ letter, GloballySimpleFinal left letter ↔
    GloballySimpleFinal right letter

/-- The intended combinatorial signature. Its necessity bridge from the
`S4_95` term function is deliberately not asserted in this foundation. -/
structure SameS5_579Signature (left right : Word Nat) : Prop where
  firstOccurrenceParity : SameFirstOccurrenceParity left right
  globallySimpleFinal : SameGloballySimpleFinal left right

/-- The factor-level signature already justified by the two quotients. -/
structure SameFactorSignature (left right : Word Nat) : Prop where
  parityTermFunction :
    (Identity.mk left right).SatisfiedBy parityFactorTable.semigroup
  globallySimpleFinal : SameGloballySimpleFinal left right

/-- The syntax profile is always in parity-block normal shape. This is a
shape fact only, not a derivability or uniqueness claim for the target basis. -/
theorem firstOccurrenceParityProfile_normal (word : Word Nat) :
    Examples.ParityInitialNormal (FirstOccurrenceParityProfile word) :=
  Examples.parityInitialNormalList_normal word.toList

theorem sameGloballySimpleFinal_of_valid_s3_6
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy finalMarkerFactorTable.semigroup) :
    SameGloballySimpleFinal identity.lhs identity.rhs := by
  intro letter
  exact Examples.finalMarkerValid_splitSimpleFinal_iff
    identity valid letter

theorem sameFactorSignature_of_factors
    (identity : Identity Nat)
    (parityValid :
      identity.SatisfiedBy parityFactorTable.semigroup)
    (finalValid :
      identity.SatisfiedBy finalMarkerFactorTable.semigroup) :
    SameFactorSignature identity.lhs identity.rhs :=
  ⟨parityValid,
    sameGloballySimpleFinal_of_valid_s3_6 identity finalValid⟩

theorem valid_factorSignature
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SameFactorSignature identity.lhs identity.rhs :=
  sameFactorSignature_of_factors identity
    (valid_s4_95 identity valid) (valid_s3_6 identity valid)

private theorem s4_95Models :
    Models parityFactorTable.semigroup basis :=
  models_of_finite_checks parityFactorTable (by decide)

private theorem s3_6Models :
    Models finalMarkerFactorTable.semigroup basis :=
  models_of_finite_checks finalMarkerFactorTable (by decide)

/-- Every finite derivation preserves the established factor-level
signature. The combinatorial first-occurrence/parity bridge remains open. -/
theorem derives_factorSignature {left right : Word Nat}
    (derivation : Derives basis left right) :
    SameFactorSignature left right :=
  sameFactorSignature_of_factors ⟨left, right⟩
    (fun valuation => derivation.sound s4_95Models valuation)
    (fun valuation => derivation.sound s3_6Models valuation)

private def instantiateTwoWords
    (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

private theorem basisPowerTail : Derives basis xxxy xy :=
  Derives.fromBasis (e := powerTailLaw) <| by simp [basis]

private theorem basisRepeatedFinal : Derives basis xyx xxyyy :=
  Derives.fromBasis (e := repeatedFinalLaw) <| by simp [basis]

theorem derivesTriplePrefixReduction (u v : Word Nat) :
    Derives basis (((u ++ u) ++ u) ++ v) (u ++ v) := by
  have substituted :=
    Derives.subst basisPowerTail (instantiateTwoWords u v)
  simpa [xxxy, xy, w, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesRepeatedFinalBridge (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u)
      ((((u ++ u) ++ v) ++ v) ++ v) := by
  have substituted :=
    Derives.subst basisRepeatedFinal (instantiateTwoWords u v)
  simpa [xyx, xxyyy, w, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- The terminal even block contracts from four copies to two. -/
theorem derivesTerminalEvenReduction (u : Word Nat) :
    Derives basis (((u ++ u) ++ u) ++ u) (u ++ u) :=
  derivesTriplePrefixReduction u u

/-- The terminal odd block contracts from five copies to three. -/
theorem derivesTerminalOddReduction (u : Word Nat) :
    Derives basis ((((u ++ u) ++ u) ++ u) ++ u)
      ((u ++ u) ++ u) := by
  have extended :=
    Derives.appendRight (derivesTerminalEvenReduction u) u
  simpa [Word.append_assoc] using extended

/-- The minimal repeated-final branch moves `xyx` to the parity blocks
`x^2 y^3`. -/
theorem derivesMinimalRepeatedFinalRepair (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u)
      ((((u ++ u) ++ v) ++ v) ++ v) :=
  derivesRepeatedFinalBridge u v

/-- Exact finite chains pinned by this foundation packet. -/
def recordedFiniteChains : List (List (Word Nat)) :=
  [
    [w 0 [0, 0, 0], w 0 [0]],
    [w 0 [0, 0, 0, 0], w 0 [0, 0]],
    [w 0 [1, 0], w 0 [0, 1, 1, 1]]
  ]

/- The unrestricted target normalizer is intentionally absent. The open
branch has no globally simple final marker; in particular, a repeated final
variable may precede another variable in first-occurrence order. Its terminal
block must be reduced to two copies for even multiplicity or three copies for
odd multiplicity without disturbing earlier parity blocks. -/

end SemigroupBasis.CoRoots.S5_579
