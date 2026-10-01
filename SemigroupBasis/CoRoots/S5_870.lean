import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder3
import SemigroupBasis.Generated.CatalogueOrder5Part07
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_870

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xxtx : Word Nat := w 0 [0, 3, 0]
def xxt : Word Nat := w 0 [0, 3]
def xhxx : Word Nat := w 0 [1, 0, 0]
def xhx : Word Nat := w 0 [1, 0]
def xhxtx : Word Nat := w 0 [1, 0, 3, 0]
def xhxt : Word Nat := w 0 [1, 0, 3]
def xyxy : Word Nat := w 0 [2, 0, 2]
def xyyx : Word Nat := w 0 [2, 2, 0]
def xytxy : Word Nat := w 0 [2, 3, 0, 2]
def xytyx : Word Nat := w 0 [2, 3, 2, 0]
def xhyxy : Word Nat := w 0 [1, 2, 0, 2]
def xhyyx : Word Nat := w 0 [1, 2, 2, 0]
def xhytxy : Word Nat := w 0 [1, 2, 3, 0, 2]
def xhytyx : Word Nat := w 0 [1, 2, 3, 2, 0]

def capBothEmptyLaw : Identity Nat := ⟨xxx, xx⟩
def capInitialGapEmptyLaw : Identity Nat := ⟨xxtx, xxt⟩
def capFinalGapEmptyLaw : Identity Nat := ⟨xhxx, xhx⟩
def capGeneralLaw : Identity Nat := ⟨xhxtx, xhxt⟩
def sortBothEmptyLaw : Identity Nat := ⟨xyxy, xyyx⟩
def sortInitialGapEmptyLaw : Identity Nat := ⟨xytxy, xytyx⟩
def sortFinalGapEmptyLaw : Identity Nat := ⟨xhyxy, xhyyx⟩
def sortGeneralLaw : Identity Nat := ⟨xhytxy, xhytyx⟩

/- The exact ordered eight-law system recorded for the representative
`S5_870`. This definition records the laws, not their completeness. -/
def basis : List (Identity Nat) :=
  [capBothEmptyLaw, capInitialGapEmptyLaw, capFinalGapEmptyLaw,
    capGeneralLaw, sortBothEmptyLaw, sortInitialGapEmptyLaw,
    sortFinalGapEmptyLaw, sortGeneralLaw]

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

private def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

def finiteBasis : List (Identity (Fin 4)) :=
  basis.map fun identity => identity.map toFinFour

private theorem basis_roundTrip_checked :
    basis.all (fun identity =>
      decide ((identity.map toFinFour).map Fin.val = identity)) = true := by
  decide

private theorem basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ basis) :
    (identity.map toFinFour).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basis_roundTrip_checked) identity member

/- Exhaustive checks on the four displayed variables lift to natural-number
variables. This theorem establishes soundness only. -/
theorem models_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteBasis.all candidate.checkIdentity = true) :
    Models candidate.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinFour ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityNat_sound (identity.map toFinFour)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [basis_roundTrip identity member] at finiteValid
  exact finiteValid

/-! ## Exact catalogue and quotient maps -/

abbrev table : FiniteTable :=
  Generated.Catalogue.S5_870.table

abbrev leftRegularBandTable : FiniteTable :=
  Generated.Catalogue.S3_16.table

abbrev cappedExponentTable : FiniteTable :=
  Generated.Catalogue.S3_8.table

/- The one-based quotient `[1,1,1,2,3]` onto the three-element
left-regular-band monoid `S3_16`, with section `[1,4,5]`. -/
def leftRegularBandQuotient :
    SplitSurjection table.semigroup leftRegularBandTable.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩
    else if value.val = 1 then ⟨0, by decide⟩
    else if value.val = 2 then ⟨0, by decide⟩
    else if value.val = 3 then ⟨1, by decide⟩
    else ⟨2, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  preimage := fun value =>
    if value.val = 0 then ⟨0, by decide⟩
    else if value.val = 1 then ⟨3, by decide⟩
    else ⟨4, by decide⟩
  right_inverse := by
    intro value
    apply Fin.ext
    revert value
    decide

/- The one-based quotient `[1,2,1,3,1]` onto the capped-exponent monoid
`S3_8`, with section `[1,2,4]`. -/
def cappedExponentQuotient :
    SplitSurjection table.semigroup cappedExponentTable.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩
    else if value.val = 1 then ⟨1, by decide⟩
    else if value.val = 2 then ⟨0, by decide⟩
    else if value.val = 3 then ⟨2, by decide⟩
    else ⟨0, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  preimage := fun value =>
    if value.val = 0 then ⟨0, by decide⟩
    else if value.val = 1 then ⟨1, by decide⟩
    else ⟨3, by decide⟩
  right_inverse := by
    intro value
    apply Fin.ext
    revert value
    decide

def leftRegularBandQuotientValuesOneBased : List Nat :=
  List.ofFn fun value : Fin 5 =>
    (leftRegularBandQuotient.toFun value).val + 1

def cappedExponentQuotientValuesOneBased : List Nat :=
  List.ofFn fun value : Fin 5 =>
    (cappedExponentQuotient.toFun value).val + 1

theorem leftRegularBandQuotientValuesOneBased_certificate :
    leftRegularBandQuotientValuesOneBased = [1, 1, 1, 2, 3] := by
  decide

theorem cappedExponentQuotientValuesOneBased_certificate :
    cappedExponentQuotientValuesOneBased = [1, 2, 1, 3, 1] := by
  decide

/- Assign the tested `x` to one-based element `2`, the comparator `y` to
`5`, and every other variable to `4`. The five outputs distinguish absence,
one or two `x` occurrences, first-occurrence order, and whether the second
`x` occurs before the first `y`. -/
def markerValuation (x y : Nat) : Nat → Fin 5 :=
  fun letter =>
    if letter = x then ⟨1, by decide⟩
    else if letter = y then ⟨4, by decide⟩
    else ⟨3, by decide⟩

def markerValuation012OneBased : List Nat :=
  List.ofFn fun letter : Fin 4 =>
    (markerValuation 0 1 letter.val).val + 1

theorem markerValuation012OneBased_certificate :
    markerValuation012OneBased = [2, 5, 4, 4] := by
  decide

set_option maxRecDepth 100000 in
/- Direct finite verification on the exact catalogue table. -/
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide)

/- The opposite semigroup satisfies the literal reversed system. The
catalogue representative is not asserted to be self-dual. -/
theorem oppositeModels :
    Models table.semigroup.opposite oppositeBasis :=
  models.oppositeReversed

/-! ## Bounded normal-form signature -/

/-- State-parametrized first-occurrence scan used by the cap proof. -/
def firstOccurrenceSequenceAux
    (seen : List Nat) : List Nat → List Nat
  | [] => []
  | letter :: rest =>
      if letter ∈ seen then
        firstOccurrenceSequenceAux seen rest
      else
        letter :: firstOccurrenceSequenceAux (letter :: seen) rest

def firstOccurrenceSequenceList (letters : List Nat) : List Nat :=
  firstOccurrenceSequenceAux [] letters

def repeatFlagsList (letters : List Nat) : List Bool :=
  (firstOccurrenceSequenceList letters).map fun letter =>
    decide (2 ≤ letters.count letter)

/-- State-parametrized second-occurrence-gap scan used by the cap proof. -/
def secondOccurrenceGapAux
    (selected : Nat) (seenSelected : Bool) (firsts : List Nat) :
    List Nat → Option Nat
  | [] => none
  | letter :: rest =>
      let nextFirsts :=
        if letter ∈ firsts then firsts else letter :: firsts
      if letter = selected then
        if seenSelected then some firsts.length
        else secondOccurrenceGapAux selected true nextFirsts rest
      else
        secondOccurrenceGapAux selected seenSelected nextFirsts rest

def secondOccurrenceGapList
    (letters : List Nat) (selected : Nat) : Option Nat :=
  secondOccurrenceGapAux selected false [] letters

def secondOccurrenceGapsList
    (letters : List Nat) : List (Option Nat) :=
  (firstOccurrenceSequenceList letters).map fun letter =>
    secondOccurrenceGapList letters letter

structure GapSignature where
  firstOccurrences : List Nat
  repeatFlags : List Bool
  secondOccurrenceGaps : List (Option Nat)
deriving DecidableEq, Repr

def gapSignatureList (letters : List Nat) : GapSignature where
  firstOccurrences := firstOccurrenceSequenceList letters
  repeatFlags := repeatFlagsList letters
  secondOccurrenceGaps := secondOccurrenceGapsList letters

def gapSignature (word : Word Nat) : GapSignature :=
  gapSignatureList word.toList

/- This is only the finite computation on the eight literal law pairs. -/
theorem literalBasisSignaturesAgree :
    basis.all (fun identity =>
      decide (gapSignature identity.lhs = gapSignature identity.rhs)) = true := by
  decide

/-! ## Primitive cap and sort substitutions -/

private def instantiateFourWords
    (u h v t : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => h
  | 2 => v
  | 3 => t
  | n + 4 => Word.singleton (n + 4)

private theorem basisCapBothEmpty : Derives basis xxx xx :=
  Derives.fromBasis (e := capBothEmptyLaw) <| by simp [basis]

private theorem basisCapInitialGapEmpty : Derives basis xxtx xxt :=
  Derives.fromBasis (e := capInitialGapEmptyLaw) <| by simp [basis]

private theorem basisCapFinalGapEmpty : Derives basis xhxx xhx :=
  Derives.fromBasis (e := capFinalGapEmptyLaw) <| by simp [basis]

private theorem basisCapGeneral : Derives basis xhxtx xhxt :=
  Derives.fromBasis (e := capGeneralLaw) <| by simp [basis]

private theorem basisSortBothEmpty : Derives basis xyxy xyyx :=
  Derives.fromBasis (e := sortBothEmptyLaw) <| by simp [basis]

private theorem basisSortInitialGapEmpty : Derives basis xytxy xytyx :=
  Derives.fromBasis (e := sortInitialGapEmptyLaw) <| by simp [basis]

private theorem basisSortFinalGapEmpty : Derives basis xhyxy xhyyx :=
  Derives.fromBasis (e := sortFinalGapEmptyLaw) <| by simp [basis]

private theorem basisSortGeneral : Derives basis xhytxy xhytyx :=
  Derives.fromBasis (e := sortGeneralLaw) <| by simp [basis]

theorem derivesCapBothEmpty (u : Word Nat) :
    Derives basis ((u ++ u) ++ u) (u ++ u) := by
  have substituted :=
    Derives.subst basisCapBothEmpty (instantiateFourWords u u u u)
  simpa [xxx, xx, w, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesCapInitialGapEmpty (u t : Word Nat) :
    Derives basis (((u ++ u) ++ t) ++ u) ((u ++ u) ++ t) := by
  have substituted :=
    Derives.subst basisCapInitialGapEmpty (instantiateFourWords u u u t)
  simpa [xxtx, xxt, w, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesCapFinalGapEmpty (u h : Word Nat) :
    Derives basis (((u ++ h) ++ u) ++ u) ((u ++ h) ++ u) := by
  have substituted :=
    Derives.subst basisCapFinalGapEmpty (instantiateFourWords u h u u)
  simpa [xhxx, xhx, w, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesCapGeneral (u h t : Word Nat) :
    Derives basis ((((u ++ h) ++ u) ++ t) ++ u)
      (((u ++ h) ++ u) ++ t) := by
  have substituted :=
    Derives.subst basisCapGeneral (instantiateFourWords u h u t)
  simpa [xhxtx, xhxt, w, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesSortBothEmpty (u v : Word Nat) :
    Derives basis (((u ++ v) ++ u) ++ v)
      (((u ++ v) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisSortBothEmpty (instantiateFourWords u u v v)
  simpa [xyxy, xyyx, w, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesSortInitialGapEmpty (u v t : Word Nat) :
    Derives basis ((((u ++ v) ++ t) ++ u) ++ v)
      ((((u ++ v) ++ t) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisSortInitialGapEmpty (instantiateFourWords u u v t)
  simpa [xytxy, xytyx, w, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesSortFinalGapEmpty (u h v : Word Nat) :
    Derives basis ((((u ++ h) ++ v) ++ u) ++ v)
      ((((u ++ h) ++ v) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisSortFinalGapEmpty (instantiateFourWords u h v v)
  simpa [xhyxy, xhyyx, w, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesSortGeneral (u h v t : Word Nat) :
    Derives basis (((((u ++ h) ++ v) ++ t) ++ u) ++ v)
      (((((u ++ h) ++ v) ++ t) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisSortGeneral (instantiateFourWords u h v t)
  simpa [xhytxy, xhytyx, w, instantiateFourWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-! ## Unwitnessed completeness obligations -/

def IsTwoLimited (word : Word Nat) : Prop :=
  ∀ letter, word.toList.count letter ≤ 2

/- The first honest blocker. No inhabitant is asserted: the four cap
substitutions above do not yet provide a correct global choice of which
occurrence to delete. -/
structure TwoLimitedReductionObligation : Prop where
  reduce :
    ∀ word : Word Nat,
      ∃ reduced : Word Nat,
        IsTwoLimited reduced ∧
        gapSignature word = gapSignature reduced ∧
        Derives basis word reduced

/- The next blocker after a two-limited reduction witness. Its missing proof
must decompose first-occurrence gaps, dispatch the four empty/nonempty swap
placements, and terminate by a decreasing inversion measure. -/
structure GapBlockSortObligation
    (_reduction : TwoLimitedReductionObligation) : Prop where
  sort :
    ∀ left right : Word Nat,
      IsTwoLimited left →
      IsTwoLimited right →
      gapSignature left = gapSignature right →
      Derives basis left right

/- Exact one-step chains replayed by the metadata-only packet. -/
def recordedFiniteChains : List (List (Word Nat)) :=
  [
    [w 0 [0, 0], w 0 [0]],
    [w 0 [0, 3, 0], w 0 [0, 3]],
    [w 0 [1, 0, 0], w 0 [1, 0]],
    [w 0 [1, 0, 3, 0], w 0 [1, 0, 3]],
    [w 0 [2, 0, 2], w 0 [2, 2, 0]],
    [w 0 [2, 3, 0, 2], w 0 [2, 3, 2, 0]],
    [w 0 [1, 2, 0, 2], w 0 [1, 2, 2, 0]],
    [w 0 [1, 2, 3, 0, 2], w 0 [1, 2, 3, 2, 0]]
  ]

/- The source intentionally stops with two unwitnessed obligations. It does
not assert a general two-limited reduction, gap-block sorting, unrestricted
completeness, or any basis endpoint. -/

end SemigroupBasis.CoRoots.S5_870
