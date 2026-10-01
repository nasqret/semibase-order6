import SemigroupBasis.CoRoots.S5_196
import SemigroupBasis.CoRoots.S5_830
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S3_6
import SemigroupBasis.Subdirect

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6FinalMarkerSquareHead

open SemigroupBasis
open SemigroupBasis.Examples

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xyx : Word Nat := w 0 [1, 0]
def xyy : Word Nat := w 0 [1, 1]
def xyz : Word Nat := w 0 [1, 2]
def xyxz : Word Nat := w 0 [1, 0, 2]
def xxyzx : Word Nat := w 0 [0, 1, 2, 0]
def xxyzy : Word Nat := w 0 [0, 1, 2, 1]
def xxzyx : Word Nat := w 0 [0, 2, 1, 0]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def repeatedFinalWitnessLaw : Identity Nat := ⟨xxyzx, xxyzy⟩
def doubledHeadTailSwapLaw : Identity Nat := ⟨xxyzx, xxzyx⟩
def copyLaw : Identity Nat := ⟨xyx, xyy⟩
def interiorDeletionLaw : Identity Nat := ⟨xyxz, xyz⟩

/-- The exact O6F_0046 final-marker/square-head intersection basis. -/
def basis : List (Identity Nat) :=
  [powerLaw, repeatedFinalWitnessLaw, doubledHeadTailSwapLaw,
    copyLaw, interiorDeletionLaw]

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

private def instantiateThreeWords
    (u v z : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private theorem bind_append
    (u v : Word Nat) (substitution : Nat → Word Nat) :
    (u ++ v).bind substitution =
      u.bind substitution ++ v.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (word : Word Nat)
    (first second : Nat → Word Nat) :
    (word.bind first).bind second =
      word.bind (fun x => (first x).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have base : Derives basis xx xxx :=
    Derives.fromBasis (e := powerLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateThreeWords u u u)
  simpa [powerLaw, xx, xxx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

theorem derivesCopy (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) ((u ++ v) ++ v) := by
  have base : Derives basis xyx xyy :=
    Derives.fromBasis (e := copyLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [copyLaw, xyx, xyy, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

theorem derivesInteriorDeletion (u v suffix : Word Nat) :
    Derives basis (((u ++ v) ++ u) ++ suffix)
      ((u ++ v) ++ suffix) := by
  have base : Derives basis xyxz xyz :=
    Derives.fromBasis (e := interiorDeletionLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateThreeWords u v suffix)
  simpa [interiorDeletionLaw, xyxz, xyz, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesDoubledHeadTailSwap (head left right : Word Nat) :
    Derives basis
      (((((head ++ head) ++ left) ++ right) ++ head))
      (((((head ++ head) ++ right) ++ left) ++ head)) := by
  have base : Derives basis xxyzx xxzyx :=
    Derives.fromBasis (e := doubledHeadTailSwapLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateThreeWords head left right)
  simpa [doubledHeadTailSwapLaw, xxyzx, xxzyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Duplicate the second protected block while retaining a nonempty suffix. -/
theorem derivesDuplicateSecond
    (first second suffix : Word Nat) :
    Derives basis ((first ++ second) ++ suffix)
      (((first ++ second) ++ second) ++ suffix) := by
  have insertFirst :=
    Derives.symm (derivesInteriorDeletion first second suffix)
  have copyFirst :=
    Derives.appendRight (derivesCopy first second) suffix
  exact insertFirst.trans <| by
    simpa [Word.append_assoc] using copyFirst

/-- Duplicate a block immediately after an arbitrary protected prefix. -/
theorem derivesDuplicateAfterPrefix
    (stemPrefix block suffix : Word Nat) :
    Derives basis ((stemPrefix ++ block) ++ suffix)
      (((stemPrefix ++ block) ++ block) ++ suffix) := by
  have insertPrefix :=
    Derives.symm (derivesInteriorDeletion stemPrefix block suffix)
  have copyPrefix :=
    Derives.appendRight (derivesCopy stemPrefix block) suffix
  exact insertPrefix.trans <| by
    simpa [Word.append_assoc] using copyPrefix

/-- Swap two interior blocks after two protected nonempty blocks and before
a protected nonempty suffix. This is the load-bearing square-head move used
to replay the final-marker rotation law without changing the first two
letters. -/
theorem derivesInteriorSwap
    (first second left right suffix : Word Nat) :
    Derives basis
      ((((first ++ second) ++ left) ++ right) ++ suffix)
      ((((first ++ second) ++ right) ++ left) ++ suffix) := by
  have duplicateSecond :=
    derivesDuplicateSecond first second ((left ++ right) ++ suffix)
  have insertSecond :=
    Derives.prepend first <|
      Derives.symm <|
        derivesInteriorDeletion second ((second ++ left) ++ right) suffix
  have swapCore :=
    Derives.appendRight
      (Derives.prepend first
        (derivesDoubledHeadTailSwap second left right))
      suffix
  have deleteSecond :=
    Derives.prepend first <|
      derivesInteriorDeletion second ((second ++ right) ++ left) suffix
  have contractSecond :=
    Derives.symm <|
      derivesDuplicateSecond first second ((right ++ left) ++ suffix)
  have step1 :
      Derives basis
        ((((first ++ second) ++ left) ++ right) ++ suffix)
        (((((first ++ second) ++ second) ++ left) ++ right) ++ suffix) := by
    simpa [Word.append_assoc] using duplicateSecond
  have step2 :
      Derives basis
        (((((first ++ second) ++ second) ++ left) ++ right) ++ suffix)
        ((((((first ++ second) ++ second) ++ left) ++ right) ++ second) ++
          suffix) := by
    simpa [Word.append_assoc] using insertSecond
  have step3 :
      Derives basis
        ((((((first ++ second) ++ second) ++ left) ++ right) ++ second) ++
          suffix)
        ((((((first ++ second) ++ second) ++ right) ++ left) ++ second) ++
          suffix) := by
    simpa [Word.append_assoc] using swapCore
  have step4 :
      Derives basis
        ((((((first ++ second) ++ second) ++ right) ++ left) ++ second) ++
          suffix)
        (((((first ++ second) ++ second) ++ right) ++ left) ++ suffix) := by
    simpa [Word.append_assoc] using deleteSecond
  have step5 :
      Derives basis
        (((((first ++ second) ++ second) ++ right) ++ left) ++ suffix)
        ((((first ++ second) ++ right) ++ left) ++ suffix) := by
    simpa [Word.append_assoc] using contractSecond
  exact step1.trans <| step2.trans <| step3.trans <| step4.trans step5

/-- Replay every derivation in the complete `S3_6` final-marker basis behind
two protected nonempty blocks. The two protected blocks are allowed to grow
in the induction, so the result is stable under arbitrary derivation
contexts and substitutions. -/
theorem liftFinalMarker
    {u v : Word Nat}
    (derivation : Derives finalMarkerThreeBasis u v)
    (first second : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis
      ((first ++ second) ++ u.bind substitution)
      ((first ++ second) ++ v.bind substitution) := by
  induction derivation generalizing first second substitution with
  | fromBasis member =>
      simp only [finalMarkerThreeBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · simpa [finalMarkerPowerLaw, finalMarkerXX, finalMarkerXXX,
          Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          Derives.prepend (first ++ second)
            (derivesPowerExpansion (substitution 0))
      · simpa [finalMarkerPrefixDuplicationLaw, finalMarkerXY,
          finalMarkerXXY, Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesDuplicateAfterPrefix
            (first ++ second) (substitution 0) (substitution 1)
      · simpa [finalMarkerCopyLaw, finalMarkerXYX, finalMarkerXYY,
          Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          Derives.prepend (first ++ second)
            (derivesCopy (substitution 0) (substitution 1))
      · simpa [finalMarkerRotateLaw, finalMarkerXYX, finalMarkerYXX,
          Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          derivesInteriorSwap first second
            (substitution 0) (substitution 1) (substitution 0)
  | refl =>
      exact Derives.refl _
  | symm _ ih =>
      exact Derives.symm (ih first second substitution)
  | trans _ _ firstDerivation secondDerivation =>
      exact (firstDerivation first second substitution).trans
        (secondDerivation first second substitution)
  | prepend stem _ ih =>
      simpa [bind_append, Word.append_assoc] using
        ih first (second ++ stem.bind substitution) substitution
  | appendRight _ suffix ih =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight
          (ih first second substitution) (suffix.bind substitution)
  | subst _ firstSubstitution ih =>
      simpa [bind_bind] using
        ih first second
          (fun x => (firstSubstitution x).bind substitution)

/-- A word with at least three letters may be saturated by a second copy of
its first-two prefix. -/
private theorem derivesSaturateLong
    (first second third : Nat) (rest : List Nat) :
    Derives basis (w first (second :: third :: rest))
      ((Word.singleton first ++ Word.singleton second) ++
        w first (second :: third :: rest)) := by
  let suffix : Word Nat := w third rest
  have insertFirst :=
    Derives.symm <|
      derivesInteriorDeletion
        (Word.singleton first) (Word.singleton second) suffix
  have insertSecond :=
    Derives.prepend (Word.singleton first) <|
      Derives.symm <|
        derivesInteriorDeletion
          (Word.singleton second) (Word.singleton first) suffix
  have step1 :
      Derives basis
        (w first (second :: third :: rest))
        (((Word.singleton first ++ Word.singleton second) ++
          Word.singleton first) ++ suffix) := by
    simpa [suffix, w, Word.singleton, Word.append,
      Word.append_assoc] using insertFirst
  have step2 :
      Derives basis
        (((Word.singleton first ++ Word.singleton second) ++
          Word.singleton first) ++ suffix)
        ((Word.singleton first ++ Word.singleton second) ++
          w first (second :: third :: rest)) := by
    simpa [suffix, w, Word.singleton, Word.append,
      Word.append_assoc] using insertSecond
  exact step1.trans step2

/-- The only two-letter word that can share its final-marker theory with a
longer word having the same first-two prefix is a square. Squares admit the
same saturation as long words. -/
private theorem derivesSaturateSquare (letter : Nat) :
    Derives basis (w letter [letter])
      ((Word.singleton letter ++ Word.singleton letter) ++
        w letter [letter]) := by
  have firstStep := derivesPowerExpansion (Word.singleton letter)
  have secondStep :=
    Derives.appendRight firstStep (Word.singleton letter)
  exact firstStep.trans <| by
    simpa [w, Word.singleton, Word.append, Word.append_assoc] using
      secondStep

private theorem finalMarkerFoldZero
    (valuation : Nat → Fin 3) (letters : List Nat) :
    letters.foldl
        (fun current x => finalMarkerThreeMul current (valuation x))
        0 = 0 := by
  induction letters with
  | nil => rfl
  | cons next rest ih =>
      simp only [List.foldl_cons]
      simpa [finalMarkerThreeMul] using ih

/-- A two-letter word with distinct letters is separated in `S3_6` from
every longer word with the same first two letters. -/
private theorem shortLongNotFinalMarkerValid
    (first second third : Nat) (rest : List Nat)
    (distinct : first ≠ second) :
    ¬(Identity.mk (w first [second])
        (w first (second :: third :: rest))).SatisfiedBy
      finalMarkerThree.semigroup := by
  intro valid
  let valuation : Nat → Fin 3 :=
    fun x => if x = second then 1 else 2
  have evaluated := valid valuation
  have firstValue : valuation first = (2 : Fin 3) := by
    simp [valuation, distinct]
  have secondValue : valuation second = (1 : Fin 3) := by
    simp [valuation]
  change
    finalMarkerThreeMul (valuation first) (valuation second) =
      rest.foldl
        (fun current x => finalMarkerThreeMul current (valuation x))
        (finalMarkerThreeMul
          (finalMarkerThreeMul (valuation first) (valuation second))
          (valuation third))
    at evaluated
  rw [firstValue, secondValue] at evaluated
  simp [finalMarkerThreeMul] at evaluated
  have folded := finalMarkerFoldZero valuation rest
  have folded' :
      rest.foldl
          (fun current x =>
            if current = 2 then valuation x else 0)
          0 = 0 := by
    simpa [finalMarkerThreeMul] using folded
  rw [folded'] at evaluated
  exact (by decide : (1 : Fin 3) ≠ 0) evaluated

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem markerModels :
    Models SemigroupBasis.Generated.S3_6.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S3_6.table basis toFinThree (by decide)

theorem squareHeadModels :
    Models SemigroupBasis.Generated.Catalogue.S5_830.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.Catalogue.S5_830.table basis toFinThree (by decide)

private theorem satisfiedBy_of_table_eq
    {source target : FiniteTable} (tableEq : source = target)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy source.semigroup) :
    identity.SatisfiedBy target.semigroup := by
  cases tableEq
  exact valid

/-- Unrestricted `Nat`-level completeness of the five displayed laws for
`Id(S3_6) ∩ Id(S5_830)`. No finite-alphabet completeness premise occurs:
the complete `S3_6` derivation is replayed behind the first-two prefix
recovered semantically from `S5_830`. -/
theorem derives_of_factor_valid
    (identity : Identity Nat)
    (markerValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_6.table.semigroup)
    (squareHeadValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_830.table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have markerValidCanonical :
      identity.SatisfiedBy finalMarkerThree.semigroup := by
    exact
      satisfiedBy_of_table_eq
        SemigroupBasis.Generated.S3_6.table_eq_catalogue_model
        identity markerValid
  have squareHeadDerivation :=
    SemigroupBasis.CoRoots.S5_830.basis_complete.2
      identity squareHeadValid
  have squareHeadClass :=
    SemigroupBasis.CoRoots.S5_830.derives_iff_exactBasisClass.mp
      squareHeadDerivation
  rcases squareHeadClass with equal |
      ⟨leftTwo, rightTwo, firstTwoEqual, _⟩
  · rw [equal]
    exact Derives.refl _
  · rcases identity with
      ⟨⟨leftHead, leftTail⟩, ⟨rightHead, rightTail⟩⟩
    cases leftTail with
    | nil =>
        simp [Word.toList] at leftTwo
    | cons leftSecond leftRest =>
        cases rightTail with
        | nil =>
            simp [Word.toList] at rightTwo
        | cons rightSecond rightRest =>
            simp only [SemigroupBasis.CoRoots.S5_830.FirstTwo,
              Word.toList] at firstTwoEqual
            have heads : leftHead = rightHead :=
              (List.cons.inj firstTwoEqual).1
            have tailHeads :
                leftSecond :: [] = rightSecond :: [] :=
              (List.cons.inj firstTwoEqual).2
            have seconds : leftSecond = rightSecond :=
              (List.cons.inj tailHeads).1
            subst rightHead
            subst rightSecond
            have finalMarkerDerivation :
                Derives finalMarkerThreeBasis
                  (w leftHead (leftSecond :: leftRest))
                  (w leftHead (leftSecond :: rightRest)) :=
              finalMarkerThreeBasis_complete.2
                (Identity.mk
                  (w leftHead (leftSecond :: leftRest))
                  (w leftHead (leftSecond :: rightRest)))
                (by simpa [w] using markerValidCanonical)
            have lifted :=
              liftFinalMarker finalMarkerDerivation
                (Word.singleton leftHead)
                (Word.singleton leftSecond) Word.singleton
            rw [bind_singleton, bind_singleton] at lifted
            cases leftRest with
            | nil =>
                cases rightRest with
                | nil =>
                    exact Derives.refl _
                | cons rightThird rightMore =>
                    by_cases square : leftHead = leftSecond
                    · subst leftSecond
                      exact
                        (derivesSaturateSquare leftHead).trans <|
                          lifted.trans <|
                            (derivesSaturateLong
                              leftHead leftHead rightThird rightMore).symm
                    · exact False.elim <|
                        shortLongNotFinalMarkerValid
                          leftHead leftSecond rightThird rightMore square
                          (by simpa [w] using markerValidCanonical)
            | cons leftThird leftMore =>
                cases rightRest with
                | nil =>
                    by_cases square : leftHead = leftSecond
                    · subst leftSecond
                      exact
                        (derivesSaturateLong
                          leftHead leftHead leftThird leftMore).trans <|
                            lifted.trans <|
                              (derivesSaturateSquare leftHead).symm
                    · have reversedValid :
                          (Identity.mk
                            (w leftHead [leftSecond])
                            (w leftHead
                              (leftSecond :: leftThird :: leftMore))).SatisfiedBy
                            finalMarkerThree.semigroup := by
                        intro valuation
                        exact (markerValidCanonical valuation).symm
                      exact False.elim <|
                        shortLongNotFinalMarkerValid
                          leftHead leftSecond leftThird leftMore square
                          reversedValid
                | cons rightThird rightMore =>
                    exact
                      (derivesSaturateLong
                        leftHead leftSecond leftThird leftMore).trans <|
                          lifted.trans <|
                            (derivesSaturateLong
                              leftHead leftSecond rightThird rightMore).symm

def canonicalIntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_830.table.semigroup
      basis where
  leftModels := markerModels
  rightModels := squareHeadModels
  complete := derives_of_factor_valid

/-- Any semigroup with the complete `S5_830` basis can replace the canonical
square-head factor. This is the reusable bridge for the `S5_904` and
`S5_943` quotient orientations recorded in the order-six certificate. -/
def intersectionOfSquareHeadBasis
    {S : Type u} {G : Semigroup S}
    (squareHeadBasis :
      BasisFor G SemigroupBasis.CoRoots.S5_830.basis) :
    IntersectionBasis
      SemigroupBasis.Generated.S3_6.table.semigroup G basis where
  leftModels := markerModels
  rightModels := by
    intro identity member
    have canonicalValid := squareHeadModels identity member
    have derivation :=
      SemigroupBasis.CoRoots.S5_830.basis_complete.2
        identity canonicalValid
    exact fun valuation =>
      derivation.sound squareHeadBasis.1 valuation
  complete := by
    intro identity markerValid squareHeadValid
    have squareHeadDerivation :=
      squareHeadBasis.2 identity squareHeadValid
    have canonicalValid :
        identity.SatisfiedBy
          SemigroupBasis.Generated.Catalogue.S5_830.table.semigroup :=
      fun valuation =>
        squareHeadDerivation.sound
          SemigroupBasis.CoRoots.S5_830.models valuation
    exact derives_of_factor_valid identity markerValid canonicalValid

end SemigroupBasis.CoRoots.Order6FinalMarkerSquareHead
