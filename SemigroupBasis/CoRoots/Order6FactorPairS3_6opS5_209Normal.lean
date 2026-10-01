import SemigroupBasis.FiniteReflection
import SemigroupBasis.Examples.CommutativeExponentFour
import SemigroupBasis.Examples.SimpleEndpointsFour
import SemigroupBasis.Generated.S3_6
import SemigroupBasis.Generated.S5_209
import SemigroupBasis.Subdirect

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_6opS5_209Normal

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

/-- The exact twelve-law candidate recorded for family
`o6fp-26c708eeb801b5c8`. -/
def recordedBasis : List (Identity Nat) :=
  [ Identity.mk (w 0 [0, 0])       (w 0 [0, 0, 0]),
    Identity.mk (w 0 [0, 0, 1, 0]) (w 0 [0, 1, 0]),
    Identity.mk (w 0 [0, 0, 1, 1]) (w 1 [0, 0, 0, 1]),
    Identity.mk (w 0 [0, 1, 0])    (w 0 [1, 0, 0]),
    Identity.mk (w 0 [0, 1, 1])    (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1, 1])    (w 0 [1, 1, 0]),
    Identity.mk (w 0 [0, 1, 1])    (w 1 [0, 0, 1]),
    Identity.mk (w 0 [0, 1, 2])    (w 0 [1, 0, 2]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 1, 2, 0]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 1 [0, 0, 2, 1]),
    Identity.mk (w 0 [1, 2, 0])    (w 0 [2, 1, 0]),
    Identity.mk (w 0 [1, 2, 1])    (w 0 [2, 1, 1]) ]

/-- The square-free open-interior transposition omitted by `recordedBasis`. -/
def missingOpenInteriorSwap : Identity Nat :=
  Identity.mk (w 0 [1, 2, 3]) (w 0 [2, 1, 3])

/-- The repaired thirteen-law candidate. -/
def correctedBasis : List (Identity Nat) :=
  recordedBasis ++ [missingOpenInteriorSwap]

private def missingOpenInteriorSwapFin : Identity (Fin 4) :=
  Identity.mk (Word.mk 0 [1, 2, 3]) (Word.mk 0 [2, 1, 3])

private theorem missingOpenInteriorSwapFin_map :
    missingOpenInteriorSwapFin.map Fin.val =
      missingOpenInteriorSwap := rfl

private theorem missingOpenInteriorSwapFin_reversed_map :
    missingOpenInteriorSwapFin.reversed.map Fin.val =
      missingOpenInteriorSwap.reversed := rfl

/-- The omitted square-free identity holds in the opposite `S3_6` factor. -/
theorem missingOpenInteriorSwap_valid_s3_6_opposite :
    missingOpenInteriorSwap.SatisfiedBy
      SemigroupBasis.Generated.S3_6.table.semigroup.opposite := by
  rw [Identity.satisfiedBy_opposite_iff_reversed]
  rw [← missingOpenInteriorSwapFin_reversed_map]
  exact
    SemigroupBasis.Generated.S3_6.table.checkIdentityNat_sound
      missingOpenInteriorSwapFin.reversed (by decide)

/-- The omitted square-free identity holds in the stored `S5_209` factor. -/
theorem missingOpenInteriorSwap_valid_s5_209 :
    missingOpenInteriorSwap.SatisfiedBy
      SemigroupBasis.Generated.S5_209.table.semigroup := by
  rw [← missingOpenInteriorSwapFin_map]
  exact
    SemigroupBasis.Generated.S5_209.table.checkIdentityNat_sound
      missingOpenInteriorSwapFin (by decide)

private theorem nodup_of_flatMap_nodup
    (source : List Nat) (images : Nat → List Nat)
    (imageNonempty : ∀ letter, images letter ≠ [])
    (mappedNodup : (source.flatMap images).Nodup) :
    source.Nodup := by
  induction source with
  | nil =>
      simp
  | cons head tail ih =>
      rw [List.flatMap_cons] at mappedNodup
      have split := List.nodup_append.mp mappedNodup
      apply List.nodup_cons.mpr
      constructor
      · intro headMember
        obtain ⟨marker, markerMember⟩ :=
          List.exists_mem_of_ne_nil
            (images head) (imageNonempty head)
        have markerInTail : marker ∈ tail.flatMap images := by
          simp only [List.mem_flatMap]
          exact ⟨head, headMember, markerMember⟩
        exact split.2.2 marker markerMember marker markerInTail rfl
      · exact ih split.2.1

private theorem source_nodup_of_bind_nodup
    (source : Word Nat) (substitution : Nat → Word Nat)
    (bound : (source.bind substitution).toList.Nodup) :
    source.toList.Nodup := by
  rw [Word.toList_bind] at bound
  apply nodup_of_flatMap_nodup source.toList
    (fun letter => (substitution letter).toList)
  · intro letter
    cases substitution letter
    simp [Word.toList]
  · exact bound

private theorem recordedBasis_has_repetition :
    ∀ identity ∈ recordedBasis,
      ¬ identity.lhs.toList.Nodup ∧
        ¬ identity.rhs.toList.Nodup := by
  decide

/-- Every side of every recorded law repeats a variable. Since substitutions
map variables to nonempty words, a derivation from the twelve laws cannot move
a square-free word. -/
private theorem recordedDerives_nodup_rigid
    {left right : Word Nat}
    (derivation : Derives recordedBasis left right) :
    (left.toList.Nodup → left = right) ∧
      (right.toList.Nodup → left = right) := by
  induction derivation with
  | fromBasis member =>
      have repeated := recordedBasis_has_repetition _ member
      exact
        ⟨fun nodup => False.elim (repeated.1 nodup),
          fun nodup => False.elim (repeated.2 nodup)⟩
  | refl =>
      exact ⟨fun _ => rfl, fun _ => rfl⟩
  | symm nestedDerivation ih =>
      exact
        ⟨fun nodup => (ih.2 nodup).symm,
          fun nodup => (ih.1 nodup).symm⟩
  | trans firstDerivation secondDerivation first second =>
      constructor
      · intro nodup
        have equalFirst := first.1 nodup
        subst_vars
        exact second.1 nodup
      · intro nodup
        have equalSecond := second.2 nodup
        subst_vars
        exact first.2 nodup
  | prepend p nestedDerivation ih =>
      constructor
      · intro nodup
        have suffixNodup : _ := (List.nodup_append.mp <| by
          simpa [Word.toList_append] using nodup).2.1
        rw [ih.1 suffixNodup]
      · intro nodup
        have suffixNodup : _ := (List.nodup_append.mp <| by
          simpa [Word.toList_append] using nodup).2.1
        rw [ih.2 suffixNodup]
  | appendRight nestedDerivation suffix ih =>
      constructor
      · intro nodup
        have prefixNodup : _ := (List.nodup_append.mp <| by
          simpa [Word.toList_append] using nodup).1
        rw [ih.1 prefixNodup]
      · intro nodup
        have prefixNodup : _ := (List.nodup_append.mp <| by
          simpa [Word.toList_append] using nodup).1
        rw [ih.2 prefixNodup]
  | subst nestedDerivation substitution ih =>
      constructor
      · intro nodup
        have sourceNodup :=
          source_nodup_of_bind_nodup _ substitution nodup
        rw [ih.1 sourceNodup]
      · intro nodup
        have targetNodup :=
          source_nodup_of_bind_nodup _ substitution nodup
        rw [ih.2 targetNodup]

/-- The common square-free identity cannot be derived from the recorded
twelve-law candidate. -/
theorem missingOpenInteriorSwap_not_derivable :
    ¬ Derives recordedBasis
      missingOpenInteriorSwap.lhs missingOpenInteriorSwap.rhs := by
  intro derivation
  have literal :=
    (recordedDerives_nodup_rigid derivation).1 (by decide)
  exact
    (by decide :
      missingOpenInteriorSwap.lhs ≠ missingOpenInteriorSwap.rhs) literal

/-- The unrestricted joint-completeness obligation requested for the recorded
twelve laws is false. -/
theorem recordedJointCompleteness_isFalse :
    ¬ (∀ identity : Identity Nat,
        identity.SatisfiedBy
            SemigroupBasis.Generated.S3_6.table.semigroup.opposite →
          identity.SatisfiedBy
              SemigroupBasis.Generated.S5_209.table.semigroup →
            Derives recordedBasis identity.lhs identity.rhs) := by
  intro complete
  exact missingOpenInteriorSwap_not_derivable
    (complete missingOpenInteriorSwap
      missingOpenInteriorSwap_valid_s3_6_opposite
      missingOpenInteriorSwap_valid_s5_209)

/-- Consequently no unconditional `IntersectionBasis` endpoint exists for
the exact twelve-law candidate. -/
theorem recordedIntersectionBasis_isFalse :
    ¬ IntersectionBasis
        SemigroupBasis.Generated.S3_6.table.semigroup.opposite
        SemigroupBasis.Generated.S5_209.table.semigroup
        recordedBasis := by
  intro intersection
  exact missingOpenInteriorSwap_not_derivable
    (intersection.complete missingOpenInteriorSwap
      missingOpenInteriorSwap_valid_s3_6_opposite
      missingOpenInteriorSwap_valid_s5_209)

/-! ## Soundness of the repaired candidate -/

private def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

private def finiteCorrectedBasis : List (Identity (Fin 4)) :=
  correctedBasis.map fun identity => identity.map toFinFour

private theorem correctedBasis_roundTrip_checked :
    correctedBasis.all (fun identity =>
      decide ((identity.map toFinFour).map Fin.val = identity)) = true := by
  decide

private theorem correctedBasis_roundTrip
    (identity : Identity Nat) (member : identity ∈ correctedBasis) :
    (identity.map toFinFour).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp correctedBasis_roundTrip_checked) identity member

private theorem correctedModels_of_finite_checks
    (table : FiniteTable)
    (checked : finiteCorrectedBasis.all table.checkIdentity = true) :
    Models table.semigroup correctedBasis := by
  intro identity member
  have finiteMember :
      identity.map toFinFour ∈ finiteCorrectedBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    table.checkIdentityNat_sound (identity.map toFinFour)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [correctedBasis_roundTrip identity member] at finiteValid
  exact finiteValid

/-- All thirteen repaired laws hold in the stored `S5_209` factor. -/
theorem correctedModels_s5_209 :
    Models SemigroupBasis.Generated.S5_209.table.semigroup
      correctedBasis :=
  correctedModels_of_finite_checks
    SemigroupBasis.Generated.S5_209.table (by decide)

private def finiteReversedCorrectedBasis :
    List (Identity (Fin 4)) :=
  correctedBasis.map fun identity =>
    identity.reversed.map toFinFour

private theorem reversedCorrectedBasis_roundTrip_checked :
    correctedBasis.all (fun identity =>
      decide
        ((identity.reversed.map toFinFour).map Fin.val =
          identity.reversed)) = true := by
  decide

private theorem reversedCorrectedBasis_roundTrip
    (identity : Identity Nat) (member : identity ∈ correctedBasis) :
    (identity.reversed.map toFinFour).map Fin.val =
      identity.reversed := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp reversedCorrectedBasis_roundTrip_checked)
      identity member

/-- All thirteen repaired laws hold in the opposite `S3_6` factor. -/
theorem correctedModels_s3_6_opposite :
    Models SemigroupBasis.Generated.S3_6.table.semigroup.opposite
      correctedBasis := by
  intro identity member
  have finiteMember :
      identity.reversed.map toFinFour ∈
        finiteReversedCorrectedBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    SemigroupBasis.Generated.S3_6.table.checkIdentityNat_sound
      (identity.reversed.map toFinFour)
      ((List.all_eq_true.mp (by decide :
        finiteReversedCorrectedBasis.all
          SemigroupBasis.Generated.S3_6.table.checkIdentity = true))
        _ finiteMember)
  rw [reversedCorrectedBasis_roundTrip identity member] at finiteValid
  exact
    (Identity.satisfiedBy_opposite_iff_reversed identity
      SemigroupBasis.Generated.S3_6.table.semigroup).2 finiteValid

/-! ## Constructive syntax supplied by the repaired law -/

private def instantiateFourWords
    (first second third fourth : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | 3 => fourth
  | n + 4 => Word.singleton (n + 4)

/-- Substitute arbitrary nonempty words into a repaired basis law. -/
theorem derivesCorrectedSubstitution
    (identity : Identity Nat) (member : identity ∈ correctedBasis)
    (substitution : Nat → Word Nat) :
    Derives correctedBasis
      (identity.lhs.bind substitution)
      (identity.rhs.bind substitution) :=
  Derives.subst (Derives.fromBasis member) substitution

/-- Contract four consecutive copies of any nonempty block to three. -/
theorem derivesFourToThree (block : Word Nat) :
    Derives correctedBasis
      (((block ++ block) ++ block) ++ block)
      ((block ++ block) ++ block) := by
  have base :
      Derives correctedBasis (w 0 [0, 0, 0]) (w 0 [0, 0]) :=
    Derives.symm <|
      Derives.fromBasis
        (e := Identity.mk (w 0 [0, 0]) (w 0 [0, 0, 0]))
        (by simp [correctedBasis, recordedBasis])
  have substituted :=
    Derives.subst base
      (instantiateFourWords block block block block)
  simpa [w, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Adjacent nonempty blocks can be transposed strictly between nonempty
left and right contexts. -/
theorem derivesOpenInteriorSwap
    (left first second right : Word Nat) :
    Derives correctedBasis
      (((left ++ first) ++ second) ++ right)
      (((left ++ second) ++ first) ++ right) := by
  have substituted :=
    derivesCorrectedSubstitution missingOpenInteriorSwap
      (by simp [correctedBasis])
      (instantiateFourWords left first second right)
  simpa [missingOpenInteriorSwap, w, instantiateFourWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

private def endpointWord
    (initial : Nat) (middle : List Nat) (final : Nat) : Word Nat :=
  Word.mk initial (middle ++ [final])

private def prefixFinalWord : List Nat → Nat → Word Nat
  | [], final => Word.singleton final
  | head :: tail, final => Word.singleton head ++ prefixFinalWord tail final

@[simp]
private theorem toList_prefixFinalWord
    (middle : List Nat) (final : Nat) :
    (prefixFinalWord middle final).toList = middle ++ [final] := by
  induction middle with
  | nil =>
      rfl
  | cons head tail ih =>
      change head :: (prefixFinalWord tail final).toList =
        head :: (tail ++ [final])
      rw [ih]

private theorem endpointWord_eq
    (initial : Nat) (middle : List Nat) (final : Nat) :
    endpointWord initial middle final =
      Word.singleton initial ++ prefixFinalWord middle final := by
  apply Word.toList_injective
  rw [Word.toList_append, Word.toList_singleton,
    toList_prefixFinalWord]
  rfl

/-- The repaired squarefree law gives every permutation of an arbitrary
interior while preserving both endpoint occurrences. -/
theorem derivesMiddlePermutation
    (initial final : Nat) {left right : List Nat}
    (permutation : left.Perm right) :
    Derives correctedBasis
      (endpointWord initial left final)
      (endpointWord initial right final) := by
  induction permutation generalizing initial with
  | nil =>
      exact Derives.refl _
  | cons letter _ ih =>
      simpa [endpointWord_eq, Word.append_assoc] using
        Derives.prepend (Word.singleton initial) (ih letter)
  | swap first second suffix =>
      simpa [endpointWord_eq, Word.append_assoc] using
        derivesOpenInteriorSwap
          (Word.singleton initial)
          (Word.singleton second) (Word.singleton first)
          (prefixFinalWord suffix final)
  | trans _ _ first second =>
      exact Derives.trans (first initial) (second initial)

/-! ## Reduction to lower-order normal-form theories -/

private def markerProduct :
    Semigroup (Fin 3 × Fin 3) where
  mul := fun left right =>
    (SemigroupBasis.Generated.S3_6.table.semigroup.opposite.mul
        left.1 right.1,
      SemigroupBasis.Generated.S3_6.table.semigroup.mul
        left.2 right.2)
  assoc := by
    intro left middle right
    apply Prod.ext
    · exact
        SemigroupBasis.Generated.S3_6.table.semigroup.opposite.assoc
          left.1 middle.1 right.1
    · exact
        SemigroupBasis.Generated.S3_6.table.semigroup.assoc
          left.2 middle.2 right.2

private def markerProductLeft :
    Hom markerProduct
      SemigroupBasis.Generated.S3_6.table.semigroup.opposite where
  toFun := Prod.fst
  map_mul := by
    intro left right
    rfl

private def markerProductRight :
    Hom markerProduct
      SemigroupBasis.Generated.S3_6.table.semigroup where
  toFun := Prod.snd
  map_mul := by
    intro left right
    rfl

private def simpleEndpointsToMarkers (value : Fin 4) :
    Fin 3 × Fin 3 :=
  if value = 0 then (0, 0)
  else if value = 1 then (0, 1)
  else if value = 2 then (1, 0)
  else (2, 2)

/-- The endpoint separator is the four-element subsemigroup of the two
opposite marker coordinates. -/
private def simpleEndpointsMarkerEmbedding :
    Embedding SemigroupBasis.Examples.simpleEndpointsFour.semigroup
      markerProduct where
  toFun := simpleEndpointsToMarkers
  map_mul := by
    intro left right
    apply Prod.ext
    · apply Fin.ext
      revert left right
      decide
    · apply Fin.ext
      revert left right
      decide
  injective := by
    intro left right equal
    apply Fin.ext
    revert left right
    decide

private def s5_209ToFinalMarker (value : Fin 5) : Fin 3 :=
  if value = 2 then 1 else if value = 4 then 2 else 0

private def finalMarkerToS5_209 (value : Fin 3) : Fin 5 :=
  if value = 0 then 0 else if value = 1 then 2 else 4

/-- The stored `S5_209` orientation has `S3_6` as its final-marker
quotient. -/
private def s5_209FinalMarkerQuotient :
    SplitSurjection
      SemigroupBasis.Generated.S5_209.table.semigroup
      SemigroupBasis.Generated.S3_6.table.semigroup where
  toFun := s5_209ToFinalMarker
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  preimage := finalMarkerToS5_209
  right_inverse := by
    intro value
    apply Fin.ext
    revert value
    decide

/-- Joint validity in the original factors implies validity in the existing
four-element simple-endpoints separator. -/
theorem valid_simpleEndpoints_of_factors
    (identity : Identity Nat)
    (s3Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_6.table.semigroup.opposite)
    (s5Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S5_209.table.semigroup) :
    identity.SatisfiedBy
      SemigroupBasis.Examples.simpleEndpointsFour.semigroup := by
  have finalMarkerValid :=
    s5_209FinalMarkerQuotient.pushforwardIdentity identity s5Valid
  apply simpleEndpointsMarkerEmbedding.pullback_identity identity
  intro valuation
  apply Prod.ext
  · change
      markerProductLeft.toFun
          (markerProduct.eval valuation identity.lhs) =
        markerProductLeft.toFun
          (markerProduct.eval valuation identity.rhs)
    rw [markerProductLeft.map_eval, markerProductLeft.map_eval]
    exact s3Valid (fun letter => (valuation letter).1)
  · change
      markerProductRight.toFun
          (markerProduct.eval valuation identity.lhs) =
        markerProductRight.toFun
          (markerProduct.eval valuation identity.rhs)
    rw [markerProductRight.map_eval, markerProductRight.map_eval]
    exact finalMarkerValid (fun letter => (valuation letter).2)

private def exponentFourToS5_209 (value : Fin 4) : Fin 5 :=
  if value = 0 then 0
  else if value = 1 then 1
  else if value = 2 then 3
  else 4

/-- The four exponent states `0,1,2,≥3` form a subsemigroup of the stored
`S5_209` table. -/
private def exponentFourEmbedding :
    Embedding
      SemigroupBasis.Examples.commutativeExponentFour.semigroup
      SemigroupBasis.Generated.S5_209.table.semigroup where
  toFun := exponentFourToS5_209
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right equal
    apply Fin.ext
    revert left right
    decide

/-- `S5_209` validity therefore preserves every multiplicity after capping
at three. -/
theorem valid_exponentFour_of_s5_209
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S5_209.table.semigroup) :
    identity.SatisfiedBy
      SemigroupBasis.Examples.commutativeExponentFour.semigroup :=
  exponentFourEmbedding.pullback_identity identity valid

/-- The smallest remaining syntactic lemma. The hypotheses are exactly the
complete lower-order invariants: simple endpoints and every multiplicity
capped at three. -/
def EndpointCapThreeCompleteness : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy
        SemigroupBasis.Examples.simpleEndpointsFour.semigroup →
      (∀ letter,
        min (identity.lhs.toList.count letter) 3 =
          min (identity.rhs.toList.count letter) 3) →
        Derives correctedBasis identity.lhs identity.rhs

/-- The exact residual normal-form theorem. It contains no support bound:
the corrected laws must join the established simple-endpoint and cap-three
theories for arbitrary identities over `Nat`. -/
def ReducedCompleteness : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy
        SemigroupBasis.Examples.simpleEndpointsFour.semigroup →
      identity.SatisfiedBy
          SemigroupBasis.Examples.commutativeExponentFour.semigroup →
        Derives correctedBasis identity.lhs identity.rhs

/-- The cap-three separator API reduces `ReducedCompleteness` to the smaller
endpoint-and-count statement above. -/
theorem reducedCompleteness_of_endpointCapThree
    (complete : EndpointCapThreeCompleteness) :
    ReducedCompleteness := by
  intro identity simpleValid exponentValid
  exact complete identity simpleValid
    (SemigroupBasis.Examples.exponentFourValid_capped_count_eq
      identity exponentValid)

/-- The lower-order reduction turns the residual normal-form theorem into
the requested unrestricted joint completeness statement. -/
theorem correctedJointCompleteness_of_reduced
    (reduced : ReducedCompleteness)
    (identity : Identity Nat)
    (s3Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_6.table.semigroup.opposite)
    (s5Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S5_209.table.semigroup) :
    Derives correctedBasis identity.lhs identity.rhs :=
  reduced identity
    (valid_simpleEndpoints_of_factors identity s3Valid s5Valid)
    (valid_exponentFour_of_s5_209 identity s5Valid)

/-- No endpoint is asserted unconditionally: this constructor records
precisely that `ReducedCompleteness` is the remaining input. -/
def correctedIntersectionBasis_of_reduced
    (reduced : ReducedCompleteness) :
    IntersectionBasis
      SemigroupBasis.Generated.S3_6.table.semigroup.opposite
      SemigroupBasis.Generated.S5_209.table.semigroup
      correctedBasis where
  leftModels := correctedModels_s3_6_opposite
  rightModels := correctedModels_s5_209
  complete := correctedJointCompleteness_of_reduced reduced

end SemigroupBasis.CoRoots.Order6FactorPairS3_6opS5_209Normal
