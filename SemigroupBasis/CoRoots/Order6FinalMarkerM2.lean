import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.S5_213Family
import SemigroupBasis.CoRoots.S5_213Normalization
import SemigroupBasis.Examples.FinalMarkerThree
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S3_6
import SemigroupBasis.Subdirect

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6FinalMarkerM2

open SemigroupBasis
open SemigroupBasis.Examples

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xxx : Word Nat := w 0 [0, 0]
def xxxx : Word Nat := w 0 [0, 0, 0]
def xxyy : Word Nat := w 0 [0, 1, 1]
def xyyx : Word Nat := w 0 [1, 1, 0]
def xxyz : Word Nat := w 0 [0, 1, 2]
def xyxz : Word Nat := w 0 [1, 0, 2]
def xyx : Word Nat := w 0 [1, 0]
def yxx : Word Nat := w 1 [0, 0]

def powerLaw : Identity Nat := ⟨xxx, xxxx⟩
def repeatedFinalLaw : Identity Nat := ⟨xxyy, xyyx⟩
def doubledInitialMoveLaw : Identity Nat := ⟨xxyz, xyxz⟩
def rightGatherLaw : Identity Nat := ⟨xyx, yxx⟩

/-- The exact four-law final-marker/M2 intersection basis. -/
def basis : List (Identity Nat) :=
  [powerLaw, repeatedFinalLaw, doubledInitialMoveLaw, rightGatherLaw]

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

def candidateBasisUpToOppositeSHA256 : String :=
  "50e92e62a303710a203641117aa82fe638e54e5c97e74ce59a246afa6d38fd3b"

private def instantiateThreeWords
    (u v suffix : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => suffix
  | n + 3 => Word.singleton (n + 3)

private theorem bind_append
    (left right : Word Nat) (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution =
      left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (word : Word Nat)
    (first second : Nat → Word Nat) :
    (word.bind first).bind second =
      word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis ((u ++ u) ++ u) (((u ++ u) ++ u) ++ u) := by
  have base : Derives basis xxx xxxx :=
    Derives.fromBasis (e := powerLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateThreeWords u u u)
  simpa [powerLaw, xxx, xxxx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

theorem derivesPowerContraction (u : Word Nat) :
    Derives basis (((u ++ u) ++ u) ++ u) ((u ++ u) ++ u) :=
  (derivesPowerExpansion u).symm

theorem derivesRepeatedFinalSwitch (u v : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ v)
      (((u ++ v) ++ v) ++ u) := by
  have base : Derives basis xxyy xyyx :=
    Derives.fromBasis (e := repeatedFinalLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [repeatedFinalLaw, xxyy, xyyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesDoubledInitialMove (u v suffix : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ suffix)
      (((u ++ v) ++ u) ++ suffix) := by
  have base : Derives basis xxyz xyxz :=
    Derives.fromBasis (e := doubledInitialMoveLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateThreeWords u v suffix)
  simpa [doubledInitialMoveLaw, xxyz, xyxz, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesRightGather (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) ((v ++ u) ++ u) := by
  have base : Derives basis xyx yxx :=
    Derives.fromBasis (e := rightGatherLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [rightGatherLaw, xyx, yxx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

private theorem s5_213_xxx_eq :
    SemigroupBasis.CoRoots.S5_213.xxx =
      (⟨0, [0, 0]⟩ : Word Nat) :=
  rfl

private theorem s5_213_xxxx_eq :
    SemigroupBasis.CoRoots.S5_213.xxxx =
      (⟨0, [0, 0, 0]⟩ : Word Nat) :=
  rfl

private theorem s5_213_xyx_eq :
    SemigroupBasis.CoRoots.S5_213.xyx =
      (⟨0, [1, 0]⟩ : Word Nat) :=
  rfl

private theorem s5_213_xxy_eq :
    SemigroupBasis.CoRoots.S5_213.xxy =
      (⟨0, [0, 1]⟩ : Word Nat) :=
  rfl

private theorem s5_213_yxx_eq :
    SemigroupBasis.CoRoots.S5_213.yxx =
      (⟨1, [0, 0]⟩ : Word Nat) :=
  rfl

/-- Replay an arbitrary `S5_213` derivation while retaining a protected
nonempty suffix.  The missing uncontextualized left-gather law is supplied
by `xxyz = xyxz`; every other source axiom is already present. -/
theorem liftS5_213Derivation
    {left right : Word Nat}
    (derivation :
      Derives SemigroupBasis.CoRoots.S5_213.basis left right)
    (suffix : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis
      (left.bind substitution ++ suffix)
      (right.bind substitution ++ suffix) := by
  induction derivation generalizing suffix substitution with
  | fromBasis member =>
      simp only [SemigroupBasis.CoRoots.S5_213.basis,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · simpa [SemigroupBasis.CoRoots.S5_213.powerLaw,
          s5_213_xxx_eq, s5_213_xxxx_eq,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
            Derives.appendRight
              (derivesPowerExpansion (substitution 0)) suffix
      · simpa [SemigroupBasis.CoRoots.S5_213.leftGatherLaw,
          s5_213_xyx_eq, s5_213_xxy_eq,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
            (derivesDoubledInitialMove
              (substitution 0) (substitution 1) suffix).symm
      · simpa [SemigroupBasis.CoRoots.S5_213.rightGatherLaw,
          s5_213_xyx_eq, s5_213_yxx_eq,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
            Derives.appendRight
              (derivesRightGather
                (substitution 0) (substitution 1)) suffix
  | refl =>
      exact Derives.refl _
  | symm _ induction =>
      exact Derives.symm (induction suffix substitution)
  | trans _ _ first second =>
      exact (first suffix substitution).trans
        (second suffix substitution)
  | prepend stem _ induction =>
      simpa [bind_append, Word.append_assoc] using
        Derives.prepend (stem.bind substitution)
          (induction suffix substitution)
  | appendRight _ appended induction =>
      simpa [bind_append, Word.append_assoc] using
        induction (appended.bind substitution ++ suffix) substitution
  | subst _ firstSubstitution induction =>
      simpa [bind_bind] using
        induction suffix
          (fun letter =>
            (firstSubstitution letter).bind substitution)

theorem liftS5_213DerivationWithSuffix
    {left right : Word Nat}
    (derivation :
      Derives SemigroupBasis.CoRoots.S5_213.basis left right)
    (suffix : Word Nat) :
    Derives basis (left ++ suffix) (right ++ suffix) := by
  simpa [bind_singleton] using
    liftS5_213Derivation derivation suffix Word.singleton

def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem markerModels :
    Models SemigroupBasis.Generated.S3_6.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S3_6.table basis toFinThree (by decide)

theorem s5_213Models :
    Models SemigroupBasis.Generated.Catalogue.S5_213.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.Catalogue.S5_213.table
    basis toFinThree (by decide)

theorem s5_498Models :
    Models SemigroupBasis.Generated.Catalogue.S5_498.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.Catalogue.S5_498.table
    basis toFinThree (by decide)

private def s5_213OppositeTable : FiniteTable where
  order := SemigroupBasis.Generated.Catalogue.S5_213.table.order
  mul := fun left right =>
    SemigroupBasis.Generated.Catalogue.S5_213.table.mul right left
  assoc := fun left middle right =>
    (SemigroupBasis.Generated.Catalogue.S5_213.table.assoc
      right middle left).symm

private theorem s5_213OppositeTable_semigroup :
    s5_213OppositeTable.semigroup =
      SemigroupBasis.Generated.Catalogue.S5_213.table.semigroup.opposite :=
  rfl

theorem s5_213OppositeModels :
    Models
      SemigroupBasis.Generated.Catalogue.S5_213.table.semigroup.opposite
      basis := by
  have checked :=
    FiniteCertificate.checkModels_sound
      s5_213OppositeTable basis toFinThree (by decide)
  rw [s5_213OppositeTable_semigroup] at checked
  exact checked

/-- The exact portion of the M2 signature used by the intersection:
multiplicities capped at three and the literal order of globally singleton
variables. -/
structure M2Data (left right : Word Nat) : Prop where
  capped :
    ∀ letter,
      SemigroupBasis.CoRoots.S5_213Syntax.cappedMultiplicity left letter =
        SemigroupBasis.CoRoots.S5_213Syntax.cappedMultiplicity right letter
  singletons :
    SemigroupBasis.CoRoots.S5_213Syntax.singletonSequence left =
      SemigroupBasis.CoRoots.S5_213Syntax.singletonSequence right

namespace M2Data

theorem refl (word : Word Nat) : M2Data word word :=
  ⟨fun _ => rfl, rfl⟩

theorem symm {left right : Word Nat}
    (data : M2Data left right) : M2Data right left :=
  ⟨fun letter => (data.capped letter).symm,
    data.singletons.symm⟩

theorem trans {left middle right : Word Nat}
    (first : M2Data left middle) (second : M2Data middle right) :
    M2Data left right :=
  ⟨fun letter =>
      (first.capped letter).trans (second.capped letter),
    first.singletons.trans second.singletons⟩

end M2Data

theorem m2Data_of_s5_213_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_213.table.semigroup) :
    M2Data identity.lhs identity.rhs := by
  have same :=
    SemigroupBasis.CoRoots.S5_213Invariant.sameSignature_of_s5_213_valid
      identity valid
  exact ⟨same.capped, same.singletonSequence_eq⟩

theorem m2Data_of_s5_498_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_498.table.semigroup) :
    M2Data identity.lhs identity.rhs := by
  have same :=
    SemigroupBasis.CoRoots.S5_213Invariant.sameSignature_of_s5_498_valid
      identity valid
  exact ⟨same.capped, same.singletonSequence_eq⟩

theorem m2Data_of_s5_213_opposite_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_213.table.semigroup.opposite) :
    M2Data identity.lhs identity.rhs := by
  have reversedValid :
      identity.reversed.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_213.table.semigroup :=
    (Identity.satisfiedBy_opposite_iff_reversed identity
      SemigroupBasis.Generated.Catalogue.S5_213.table.semigroup).mp valid
  have same :=
    SemigroupBasis.CoRoots.S5_213Invariant.sameSignature_of_s5_213_valid
      identity.reversed reversedValid
  constructor
  · intro letter
    simpa [Identity.reversed,
      SemigroupBasis.CoRoots.S5_213Syntax.cappedMultiplicity,
      Word.toList_reverse, List.count_reverse] using
        same.capped letter
  · have reversedSingletons := same.singletonSequence_eq
    change
      SemigroupBasis.CoRoots.S5_213Syntax.singletonSequence
          identity.lhs.reverse =
        SemigroupBasis.CoRoots.S5_213Syntax.singletonSequence
          identity.rhs.reverse
      at reversedSingletons
    rw [SemigroupBasis.CoRoots.S5_213Syntax.singletonSequence_reverse,
      SemigroupBasis.CoRoots.S5_213Syntax.singletonSequence_reverse]
      at reversedSingletons
    simpa using congrArg List.reverse reversedSingletons

private abbrev ListDerives :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

def removeLetter (selected : Nat) (letters : List Nat) : List Nat :=
  letters.filter (fun letter => decide (letter ≠ selected))

private theorem removeLetter_append
    (selected : Nat) (left right : List Nat) :
    removeLetter selected (left ++ right) =
      removeLetter selected left ++ removeLetter selected right := by
  simp [removeLetter, List.filter_append]

private theorem removeLetter_idempotent
    (selected : Nat) (letters : List Nat) :
    removeLetter selected (removeLetter selected letters) =
      removeLetter selected letters := by
  simp [removeLetter, List.filter_filter]

private theorem removeLetter_replicate_self
    (selected copies : Nat) :
    removeLetter selected (List.replicate copies selected) = [] := by
  simp [removeLetter]

def finalCopies (stem : List Nat) (final : Nat) : Nat :=
  Nat.min 3 (stem.count final + 1)

theorem finalCopies_positive (stem : List Nat) (final : Nat) :
    0 < finalCopies stem final := by
  unfold finalCopies
  simp only [Nat.min_def]
  split <;> omega

theorem finalCopies_le_three (stem : List Nat) (final : Nat) :
    finalCopies stem final ≤ 3 :=
  Nat.min_le_left _ _

private theorem replicate_sub_one_append_singleton
    (letter copies : Nat) (positive : 0 < copies) :
    List.replicate (copies - 1) letter ++ [letter] =
      List.replicate copies letter := by
  cases copies with
  | zero => omega
  | succ copies =>
      induction copies with
      | zero => simp
      | succ copies ih =>
          simpa [List.replicate_succ, List.cons_append] using
            congrArg (List.cons letter) (ih (by omega))

private theorem finalCopies_cons_self
    (stem : List Nat) (final : Nat) :
    finalCopies (final :: stem) final =
      if finalCopies stem final < 3 then
        finalCopies stem final + 1
      else
        3 := by
  unfold finalCopies
  simp only [List.count_cons_self]
  simp only [Nat.min_def]
  split <;> split <;> split <;> omega

def finalNormalList (stem : List Nat) (final : Nat) : List Nat :=
  removeLetter final stem ++
    List.replicate (finalCopies stem final) final

private theorem listDerivesGatherOne
    (final : Nat) (middle : List Nat) (copies : Nat)
    (positive : 0 < copies) :
    ListDerives
      (final :: middle ++ List.replicate copies final)
      (middle ++ List.replicate (copies + 1) final) := by
  cases middle with
  | nil =>
      simpa [List.replicate_succ, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis)
          (List.replicate (copies + 1) final))
  | cons head tail =>
      cases copies with
      | zero => omega
      | succ extra =>
          have core :=
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
              derivesRightGather
                (Word.singleton final)
                (SemigroupBasis.CoRoots.S5_107.listWordOfCons
                  head tail)
          have extended :=
            core.append (List.replicate extra final)
          simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
            Word.toList_append, Word.toList_singleton,
            List.replicate_succ, List.append_assoc] using extended

private theorem listDerivesContractFour
    (stem : List Nat) (letter : Nat) :
    ListDerives
      (stem ++ List.replicate 4 letter)
      (stem ++ List.replicate 3 letter) := by
  have core :=
    SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
      derivesPowerContraction (Word.singleton letter)
  simpa [Word.toList_append, Word.toList_singleton,
    List.replicate_succ, List.append_assoc] using
      core.prepend stem

/-- Gather every occurrence of the displayed final variable at the right
edge, preserve the order of all other letters, and cap the resulting final
block at three. -/
theorem listDerivesFinalNormal :
    ∀ (stem : List Nat) (final : Nat),
      ListDerives
        (stem ++ [final])
        (finalNormalList stem final)
  | [], final => by
      simpa [finalNormalList, finalCopies, removeLetter] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis) [final])
  | head :: tail, final => by
      have tailNormal := listDerivesFinalNormal tail final
      have prefixed := tailNormal.prepend [head]
      by_cases same : head = final
      · subst head
        have gathered :=
          listDerivesGatherOne final (removeLetter final tail)
            (finalCopies tail final)
            (finalCopies_positive tail final)
        have start :
            ListDerives
              ((final :: tail) ++ [final])
              (final ::
                removeLetter final tail ++
                  List.replicate (finalCopies tail final) final) := by
          simpa [finalNormalList, List.append_assoc] using prefixed
        by_cases saturated : finalCopies tail final = 3
        · have contracted :=
            listDerivesContractFour
              (removeLetter final tail) final
          have finish :
              ListDerives
                (removeLetter final tail ++
                  List.replicate
                    (finalCopies tail final + 1) final)
                (finalNormalList (final :: tail) final) := by
            rw [saturated]
            simpa [finalNormalList, removeLetter,
              finalCopies_cons_self, saturated,
              List.append_assoc] using contracted
          exact start.trans <| gathered.trans finish
        · have below : finalCopies tail final < 3 := by
            have upper := finalCopies_le_three tail final
            omega
          have finish :
              removeLetter final tail ++
                    List.replicate
                      (finalCopies tail final + 1) final =
                finalNormalList (final :: tail) final := by
            simp [finalNormalList, removeLetter,
              finalCopies_cons_self, below]
          rw [← finish]
          exact start.trans gathered
      · have target :
          finalNormalList (head :: tail) final =
            head :: finalNormalList tail final := by
          simp [finalNormalList, finalCopies, removeLetter, same]
        rw [target]
        simpa [List.append_assoc] using prefixed
termination_by
  stem final => stem.length

def finalNormalWord (stem : List Nat) (final : Nat) : Word Nat :=
  wordOfPrefixFinal
    (removeLetter final stem ++
      List.replicate (finalCopies stem final - 1) final)
    final

theorem toList_finalNormalWord
    (stem : List Nat) (final : Nat) :
    (finalNormalWord stem final).toList =
      finalNormalList stem final := by
  unfold finalNormalWord finalNormalList
  rw [toList_wordOfPrefixFinal, List.append_assoc,
    replicate_sub_one_append_singleton final
      (finalCopies stem final)
      (finalCopies_positive stem final)]

private theorem derives_of_listDerives_toList
    {left right : Word Nat}
    (derivation : ListDerives left.toList right.toList) :
    Derives basis left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          exact
            SemigroupBasis.CoRoots.S5_107.ListDerives.toWord derivation

theorem derivesFinalNormal (stem : List Nat) (final : Nat) :
    Derives basis
      (wordOfPrefixFinal stem final)
      (finalNormalWord stem final) := by
  apply derives_of_listDerives_toList
  rw [toList_wordOfPrefixFinal, toList_finalNormalWord]
  exact listDerivesFinalNormal stem final

private theorem count_removeLetter_self
    (selected : Nat) (letters : List Nat) :
    (removeLetter selected letters).count selected = 0 := by
  apply List.count_eq_zero.mpr
  simp [removeLetter]

private theorem count_removeLetter_of_ne
    {selected letter : Nat} (different : letter ≠ selected) :
    ∀ letters : List Nat,
      (removeLetter selected letters).count letter =
        letters.count letter
  | [] => rfl
  | head :: tail => by
      by_cases headSelected : head = selected
      · subst head
        simpa [removeLetter, different, Ne.symm different] using
          count_removeLetter_of_ne different tail
      · by_cases headLetter : head = letter
        · subst head
          simp [removeLetter, different,
            count_removeLetter_of_ne different tail]
        · simpa [removeLetter, headSelected, headLetter,
            Ne.symm headLetter] using
              count_removeLetter_of_ne different tail

private theorem count_replicate_of_ne
    {tested repeated : Nat} (different : tested ≠ repeated) :
    ∀ copies : Nat,
      (List.replicate copies repeated).count tested = 0
  | 0 => rfl
  | copies + 1 => by
      rw [List.replicate_succ,
        List.count_cons_of_ne (Ne.symm different),
        count_replicate_of_ne different copies]

private theorem singletonSequence_removedWord
    (source : Word Nat) (selected head : Nat) (tail : List Nat)
    (shape :
      removeLetter selected source.toList = head :: tail) :
    SemigroupBasis.CoRoots.S5_213Syntax.singletonSequence
        (SemigroupBasis.CoRoots.S5_107.listWordOfCons head tail) =
      (SemigroupBasis.CoRoots.S5_213Syntax.singletonSequence source).filter
        (fun letter => decide (letter ≠ selected)) := by
  unfold SemigroupBasis.CoRoots.S5_213Syntax.singletonSequence
  simp only [SemigroupBasis.CoRoots.S5_107.listWordOfCons, Word.toList]
  simp only [← shape]
  unfold removeLetter
  rw [List.filter_filter, List.filter_filter]
  apply List.filter_congr
  intro letter _
  by_cases same : letter = selected
  · subst letter
    simp
  · simp [same, Bool.and_comm, Word.toList]

private theorem removed_canonicalWord_eq
    {left right : Word Nat} (data : M2Data left right)
    (selected : Nat)
    {leftHead rightHead : Nat} {leftTail rightTail : List Nat}
    (leftShape :
      removeLetter selected left.toList = leftHead :: leftTail)
    (rightShape :
      removeLetter selected right.toList = rightHead :: rightTail) :
    SemigroupBasis.CoRoots.S5_213Syntax.canonicalWord
        (SemigroupBasis.CoRoots.S5_107.listWordOfCons
          leftHead leftTail) =
      SemigroupBasis.CoRoots.S5_213Syntax.canonicalWord
        (SemigroupBasis.CoRoots.S5_107.listWordOfCons
          rightHead rightTail) := by
  apply
    SemigroupBasis.CoRoots.S5_213Syntax.canonicalWord_eq_of_capped_singletonSequence
  · intro letter
    unfold SemigroupBasis.CoRoots.S5_213Syntax.cappedMultiplicity
    simp only [SemigroupBasis.CoRoots.S5_107.listWordOfCons, Word.toList]
    rw [← leftShape, ← rightShape]
    by_cases same : letter = selected
    · subst letter
      rw [count_removeLetter_self, count_removeLetter_self]
    · rw [count_removeLetter_of_ne same,
        count_removeLetter_of_ne same]
      exact data.capped letter
  · rw [singletonSequence_removedWord left selected
        leftHead leftTail leftShape,
      singletonSequence_removedWord right selected
        rightHead rightTail rightShape,
      data.singletons]

private theorem removeLetter_nil_transfer
    {left right : Word Nat} (data : M2Data left right)
    (selected : Nat)
    (leftEmpty : removeLetter selected left.toList = []) :
    removeLetter selected right.toList = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro letter member
  have filtered := List.mem_filter.mp member
  have different : letter ≠ selected := by
    simpa using filtered.2
  have rightPositive : 0 < right.toList.count letter :=
    List.count_pos_iff.mpr filtered.1
  have leftNonzero : left.toList.count letter ≠ 0 := by
    intro leftZero
    have leftCappedZero :
        SemigroupBasis.CoRoots.S5_213Syntax.cappedMultiplicity
            left letter = 0 :=
      (SemigroupBasis.CoRoots.S5_213Syntax.cappedMultiplicity_eq_zero_iff
        left letter).2 leftZero
    have rightCappedZero :
        SemigroupBasis.CoRoots.S5_213Syntax.cappedMultiplicity
            right letter = 0 := by
      rw [← data.capped letter]
      exact leftCappedZero
    have rightZero :=
      (SemigroupBasis.CoRoots.S5_213Syntax.cappedMultiplicity_eq_zero_iff
        right letter).1 rightCappedZero
    exact (Nat.ne_of_gt rightPositive) rightZero
  have leftPositive : 0 < left.toList.count letter :=
    Nat.pos_of_ne_zero leftNonzero
  have leftMember : letter ∈ left.toList :=
    List.count_pos_iff.mp leftPositive
  have kept :
      letter ∈ removeLetter selected left.toList := by
    apply List.mem_filter.mpr
    exact ⟨leftMember, by simpa [different]⟩
  rw [leftEmpty] at kept
  exact List.not_mem_nil kept

private def finalBlockWord (final copies : Nat) : Word Nat :=
  ⟨final, List.replicate (copies - 1) final⟩

private theorem toList_finalBlockWord
    (final copies : Nat) (positive : 0 < copies) :
    (finalBlockWord final copies).toList =
      List.replicate copies final := by
  cases copies with
  | zero => omega
  | succ copies =>
      simp [finalBlockWord, Word.toList, List.replicate_succ]

private theorem finalNormalWord_eq_body_append
    (stem : List Nat) (final copies : Nat)
    (copiesEq : finalCopies stem final = copies)
    {head : Nat} {tail : List Nat}
    (bodyShape : removeLetter final stem = head :: tail) :
    finalNormalWord stem final =
      SemigroupBasis.CoRoots.S5_107.listWordOfCons head tail ++
        finalBlockWord final copies := by
  apply Word.toList_injective
  rw [toList_finalNormalWord,
    SemigroupBasis.Word.toList_append,
    toList_finalBlockWord final copies (by
      rw [← copiesEq]
      exact finalCopies_positive stem final)]
  simp only [SemigroupBasis.CoRoots.S5_107.listWordOfCons, Word.toList]
  rw [finalNormalList, bodyShape, copiesEq]

/-- Once the final variable agrees, the two terminal normal forms differ
only in their M2 bodies.  The existing unrestricted `S5_213` normalizer is
replayed behind the common nonempty final block. -/
theorem derivesSameFinal
    (leftPrefix rightPrefix : List Nat) (final : Nat)
    (data :
      M2Data
        (wordOfPrefixFinal leftPrefix final)
        (wordOfPrefixFinal rightPrefix final)) :
    Derives basis
      (wordOfPrefixFinal leftPrefix final)
      (wordOfPrefixFinal rightPrefix final) := by
  have leftNormal := derivesFinalNormal leftPrefix final
  have rightNormal := derivesFinalNormal rightPrefix final
  have copiesEq :
      finalCopies leftPrefix final =
        finalCopies rightPrefix final := by
    have equality := data.capped final
    simpa [SemigroupBasis.CoRoots.S5_213Syntax.cappedMultiplicity,
      toList_wordOfPrefixFinal, finalCopies,
      List.count_append] using equality
  cases leftBody :
      removeLetter final
        (wordOfPrefixFinal leftPrefix final).toList with
  | nil =>
      have rightBody :
          removeLetter final
              (wordOfPrefixFinal rightPrefix final).toList = [] :=
        removeLetter_nil_transfer data final leftBody
      have leftPrefixEmpty :
          removeLetter final leftPrefix = [] := by
        simpa [toList_wordOfPrefixFinal, removeLetter,
          List.filter_append] using leftBody
      have rightPrefixEmpty :
          removeLetter final rightPrefix = [] := by
        simpa [toList_wordOfPrefixFinal, removeLetter,
          List.filter_append] using rightBody
      have normalEq :
          finalNormalWord leftPrefix final =
            finalNormalWord rightPrefix final := by
        apply Word.toList_injective
        rw [toList_finalNormalWord, toList_finalNormalWord]
        simp [finalNormalList, leftPrefixEmpty,
          rightPrefixEmpty, copiesEq]
      rw [normalEq] at leftNormal
      exact leftNormal.trans rightNormal.symm
  | cons leftHead leftTail =>
      cases rightBody :
          removeLetter final
            (wordOfPrefixFinal rightPrefix final).toList with
      | nil =>
          have impossible :=
            removeLetter_nil_transfer (M2Data.symm data) final rightBody
          rw [leftBody] at impossible
          contradiction
      | cons rightHead rightTail =>
          have leftPrefixBody :
              removeLetter final leftPrefix =
                leftHead :: leftTail := by
            simpa [toList_wordOfPrefixFinal, removeLetter,
              List.filter_append] using leftBody
          have rightPrefixBody :
              removeLetter final rightPrefix =
                rightHead :: rightTail := by
            simpa [toList_wordOfPrefixFinal, removeLetter,
              List.filter_append] using rightBody
          let copies := finalCopies leftPrefix final
          have copiesPositive : 0 < copies :=
            finalCopies_positive leftPrefix final
          have leftAsAppend :=
            finalNormalWord_eq_body_append
              leftPrefix final copies rfl leftPrefixBody
          have rightAsAppend :=
            finalNormalWord_eq_body_append
              rightPrefix final copies copiesEq.symm rightPrefixBody
          have canonicalEq :=
            removed_canonicalWord_eq data final leftBody rightBody
          have leftBodyNormal :=
            liftS5_213DerivationWithSuffix
              (SemigroupBasis.CoRoots.S5_213Normalization.derivesCanonical
                (SemigroupBasis.CoRoots.S5_107.listWordOfCons
                  leftHead leftTail))
              (finalBlockWord final copies)
          have rightBodyNormal :=
            liftS5_213DerivationWithSuffix
              (SemigroupBasis.CoRoots.S5_213Normalization.derivesCanonical
                (SemigroupBasis.CoRoots.S5_107.listWordOfCons
                  rightHead rightTail))
              (finalBlockWord final copies)
          rw [canonicalEq] at leftBodyNormal
          rw [leftAsAppend] at leftNormal
          rw [rightAsAppend] at rightNormal
          exact leftNormal.trans <|
            leftBodyNormal.trans <|
              rightBodyNormal.symm.trans rightNormal.symm

theorem m2Data_of_derivation
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    M2Data left right := by
  have valid :
      (⟨left, right⟩ : Identity Nat).SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_213.table.semigroup :=
    fun valuation => derivation.sound s5_213Models valuation
  exact m2Data_of_s5_213_valid ⟨left, right⟩ valid

def gatheredRepeatedWord
    (source : Word Nat) (selected : Nat) : Word Nat :=
  wordOfPrefixFinal
    (removeLetter selected source.toList ++
      List.replicate
        (SemigroupBasis.CoRoots.S5_213Syntax.cappedMultiplicity
          source selected - 1)
        selected)
    selected

theorem toList_gatheredRepeatedWord
    (source : Word Nat) (selected : Nat)
    (multiple : 2 ≤ source.toList.count selected) :
    (gatheredRepeatedWord source selected).toList =
      removeLetter selected source.toList ++
        List.replicate
          (SemigroupBasis.CoRoots.S5_213Syntax.cappedMultiplicity
            source selected)
          selected := by
  have cappedPositive :
      0 <
        SemigroupBasis.CoRoots.S5_213Syntax.cappedMultiplicity
          source selected := by
    have cappedAtLeast :
        2 ≤
          SemigroupBasis.CoRoots.S5_213Syntax.cappedMultiplicity
            source selected :=
      (SemigroupBasis.CoRoots.S5_213Syntax.two_le_cappedMultiplicity_iff
        source selected).2 multiple
    omega
  unfold gatheredRepeatedWord
  rw [toList_wordOfPrefixFinal, List.append_assoc,
    replicate_sub_one_append_singleton selected
      (SemigroupBasis.CoRoots.S5_213Syntax.cappedMultiplicity
        source selected) cappedPositive]

private theorem selected_not_mem_singletonSequence
    (word : Word Nat) (selected : Nat)
    (multiple : 2 ≤ word.toList.count selected) :
    selected ∉
      SemigroupBasis.CoRoots.S5_213Syntax.singletonSequence word := by
  intro member
  have one :=
    (SemigroupBasis.CoRoots.S5_213Syntax.mem_singletonSequence_iff
      word selected).1 member
  omega

private theorem singletonSequence_gatheredRepeatedWord
    (source : Word Nat) (selected : Nat)
    (multiple : 2 ≤ source.toList.count selected) :
    SemigroupBasis.CoRoots.S5_213Syntax.singletonSequence
        (gatheredRepeatedWord source selected) =
      SemigroupBasis.CoRoots.S5_213Syntax.singletonSequence source := by
  cases bodyShape :
      removeLetter selected source.toList with
  | nil =>
      have onlySelected :
          ∀ letter, letter ∈ source.toList → letter = selected := by
        intro letter member
        by_cases equal : letter = selected
        · exact equal
        · have kept :
              letter ∈ removeLetter selected source.toList := by
            apply List.mem_filter.mpr
            exact ⟨member, by simpa using equal⟩
          rw [bodyShape] at kept
          exact False.elim (List.not_mem_nil kept)
      have sourceSingletons :
          SemigroupBasis.CoRoots.S5_213Syntax.singletonSequence source =
            [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro letter member
        have one :=
          (SemigroupBasis.CoRoots.S5_213Syntax.mem_singletonSequence_iff
            source letter).1 member
        have occurrence :
            letter ∈ source.toList :=
          List.count_pos_iff.mp (by omega)
        have equal : letter = selected :=
          onlySelected letter occurrence
        subst letter
        omega
      have gatheredSingletons :
          SemigroupBasis.CoRoots.S5_213Syntax.singletonSequence
              (gatheredRepeatedWord source selected) = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro letter member
        have one :=
          (SemigroupBasis.CoRoots.S5_213Syntax.mem_singletonSequence_iff
              (gatheredRepeatedWord source selected) letter).1 member
        rw [toList_gatheredRepeatedWord source selected multiple,
          bodyShape] at one
        have cappedAtLeast :
            2 ≤
              SemigroupBasis.CoRoots.S5_213Syntax.cappedMultiplicity
                source selected := by
          exact
            (SemigroupBasis.CoRoots.S5_213Syntax.two_le_cappedMultiplicity_iff
              source selected).2 multiple
        simp only [List.nil_append] at one
        have occurrence :
            letter = selected := by
          have member :
              letter ∈ List.replicate
                (SemigroupBasis.CoRoots.S5_213Syntax.cappedMultiplicity
                  source selected) selected :=
            List.count_pos_iff.mp (by omega)
          simpa using List.eq_of_mem_replicate member
        subst letter
        simp at one
        omega
      rw [sourceSingletons, gatheredSingletons]
  | cons bodyHead bodyTail =>
      have sourceBody :=
        singletonSequence_removedWord source selected
          bodyHead bodyTail bodyShape
      have gatheredBodyShape :
          removeLetter selected
              (gatheredRepeatedWord source selected).toList =
            bodyHead :: bodyTail := by
        rw [toList_gatheredRepeatedWord source selected multiple,
          removeLetter_append, removeLetter_idempotent,
          removeLetter_replicate_self, bodyShape]
        simp
      have gatheredBody :=
        singletonSequence_removedWord
          (gatheredRepeatedWord source selected) selected
          bodyHead bodyTail gatheredBodyShape
      have sourceFilter :
          List.filter (fun letter => decide (letter ≠ selected))
              (SemigroupBasis.CoRoots.S5_213Syntax.singletonSequence source) =
            SemigroupBasis.CoRoots.S5_213Syntax.singletonSequence source :=
        List.filter_eq_self.mpr <| by
          intro letter member
          exact decide_eq_true <| by
            intro equal
            subst letter
            exact selected_not_mem_singletonSequence
              source selected multiple member
      have gatheredMultiple :
          2 ≤
            (gatheredRepeatedWord source selected).toList.count
              selected := by
        rw [toList_gatheredRepeatedWord source selected multiple,
          List.count_append, count_removeLetter_self,
          List.count_replicate_self, Nat.zero_add]
        exact
          (SemigroupBasis.CoRoots.S5_213Syntax.two_le_cappedMultiplicity_iff
            source selected).2 multiple
      have gatheredFilter :
          List.filter (fun letter => decide (letter ≠ selected))
              (SemigroupBasis.CoRoots.S5_213Syntax.singletonSequence
                (gatheredRepeatedWord source selected)) =
            SemigroupBasis.CoRoots.S5_213Syntax.singletonSequence
              (gatheredRepeatedWord source selected) :=
        List.filter_eq_self.mpr <| by
          intro letter member
          exact decide_eq_true <| by
            intro equal
            subst letter
            exact selected_not_mem_singletonSequence
              (gatheredRepeatedWord source selected) selected
              gatheredMultiple member
      rw [sourceFilter] at sourceBody
      rw [gatheredFilter] at gatheredBody
      exact gatheredBody.symm.trans sourceBody

private theorem canonicalWord_eq_gatheredRepeatedWord
    (source : Word Nat) (selected : Nat)
    (multiple : 2 ≤ source.toList.count selected) :
    SemigroupBasis.CoRoots.S5_213Syntax.canonicalWord source =
      SemigroupBasis.CoRoots.S5_213Syntax.canonicalWord
        (gatheredRepeatedWord source selected) := by
  apply
    SemigroupBasis.CoRoots.S5_213Syntax.canonicalWord_eq_of_capped_singletonSequence
  · intro letter
    unfold SemigroupBasis.CoRoots.S5_213Syntax.cappedMultiplicity
    rw [toList_gatheredRepeatedWord source selected multiple]
    by_cases same : letter = selected
    · subst letter
      rw [List.count_append, count_removeLetter_self,
        List.count_replicate_self, Nat.zero_add]
      unfold SemigroupBasis.CoRoots.S5_213Syntax.cappedMultiplicity
      simp [Nat.min_assoc]
    · rw [List.count_append,
        count_removeLetter_of_ne same,
        count_replicate_of_ne same,
        Nat.add_zero]
  · exact (singletonSequence_gatheredRepeatedWord
      source selected multiple).symm

theorem derivesGatheredRepeatedWithSuffix
    (source : Word Nat) (selected : Nat)
    (multiple : 2 ≤ source.toList.count selected)
    (suffix : Word Nat) :
    Derives basis
      (source ++ suffix)
      (gatheredRepeatedWord source selected ++ suffix) := by
  have left :=
    liftS5_213DerivationWithSuffix
      (SemigroupBasis.CoRoots.S5_213Normalization.derivesCanonical source)
      suffix
  have right :=
    liftS5_213DerivationWithSuffix
      (SemigroupBasis.CoRoots.S5_213Normalization.derivesCanonical
        (gatheredRepeatedWord source selected))
      suffix
  rw [canonicalWord_eq_gatheredRepeatedWord source selected multiple]
    at left
  exact left.trans right.symm

private theorem listDerivesTwoTwoSwitch
    (oldFinal newFinal : Nat) :
    ListDerives
      [newFinal, newFinal, oldFinal, oldFinal]
      [newFinal, oldFinal, oldFinal, newFinal] :=
  SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <| by
    simpa [Word.toList_append, Word.toList_singleton] using
      derivesRepeatedFinalSwitch
        (Word.singleton newFinal) (Word.singleton oldFinal)

private theorem listDerivesTwoThreeSwitch
    (oldFinal newFinal : Nat) :
    ListDerives
      [newFinal, newFinal, oldFinal, oldFinal, oldFinal]
      [oldFinal, newFinal, oldFinal, oldFinal, newFinal] := by
  have first :=
    (listDerivesTwoTwoSwitch oldFinal newFinal).append [oldFinal]
  have secondCore :=
    SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
      derivesRightGather
        (Word.singleton newFinal)
        (Word.singleton oldFinal ++ Word.singleton oldFinal)
  have second :=
    secondCore.append [oldFinal]
  have third :=
    (listDerivesTwoTwoSwitch newFinal oldFinal).append [oldFinal]
  have fourth :=
    (listDerivesTwoTwoSwitch oldFinal newFinal).prepend [oldFinal]
  exact first.trans <| by
    simpa [Word.toList_append, Word.toList_singleton,
      List.append_assoc] using
        second.trans <| third.trans fourth

private theorem listDerivesCappedBlockSwitch
    (stem : List Nat) (oldFinal newFinal oldCopies newCopies : Nat)
    (oldBounds : 2 ≤ oldCopies ∧ oldCopies ≤ 3)
    (newBounds : 2 ≤ newCopies ∧ newCopies ≤ 3) :
    ∃ switchedPrefix,
      ListDerives
        (stem ++ List.replicate newCopies newFinal ++
          List.replicate oldCopies oldFinal)
        (switchedPrefix ++ [newFinal]) := by
  rcases oldBounds with ⟨oldLow, oldHigh⟩
  rcases newBounds with ⟨newLow, newHigh⟩
  have oldCases : oldCopies = 2 ∨ oldCopies = 3 := by omega
  have newCases : newCopies = 2 ∨ newCopies = 3 := by omega
  rcases oldCases with rfl | rfl <;>
    rcases newCases with rfl | rfl
  · refine
      ⟨stem ++ [newFinal, oldFinal, oldFinal],
        ?_⟩
    simpa [List.replicate_succ, List.append_assoc] using
      (listDerivesTwoTwoSwitch oldFinal newFinal).prepend stem
  · refine
      ⟨stem ++ [newFinal, newFinal, oldFinal, oldFinal],
        ?_⟩
    simpa [List.replicate_succ, List.append_assoc] using
      ((listDerivesTwoTwoSwitch oldFinal newFinal).prepend
        (stem ++ [newFinal]))
  · refine
      ⟨stem ++ [oldFinal, newFinal, oldFinal, oldFinal],
        ?_⟩
    simpa [List.replicate_succ, List.append_assoc] using
      (listDerivesTwoThreeSwitch oldFinal newFinal).prepend stem
  · refine
      ⟨stem ++
          [newFinal, oldFinal, newFinal, oldFinal, oldFinal],
        ?_⟩
    simpa [List.replicate_succ, List.append_assoc] using
      ((listDerivesTwoThreeSwitch oldFinal newFinal).prepend
        (stem ++ [newFinal]))

/-- Change one repeated final variable to another repeated variable.  The
body is first normalized by the M2 normalizer; the remaining block switch
has only four double/triple cases. -/
theorem derivesChangeRepeatedFinal
    (stem : List Nat) (oldFinal newFinal : Nat)
    (different : oldFinal ≠ newFinal)
    (oldRepeated : oldFinal ∈ stem)
    (newRepeated :
      2 ≤ (stem ++ [oldFinal]).count newFinal) :
    ∃ switchedPrefix,
      Derives basis
        (wordOfPrefixFinal stem oldFinal)
        (wordOfPrefixFinal switchedPrefix newFinal) := by
  have leftNormal := derivesFinalNormal stem oldFinal
  let body := removeLetter oldFinal stem
  have newBodyCount :
      2 ≤ body.count newFinal := by
    change 2 ≤ (removeLetter oldFinal stem).count newFinal
    rw [count_removeLetter_of_ne (Ne.symm different)]
    rw [List.count_append] at newRepeated
    simpa [different] using newRepeated
  have bodyNonempty : body ≠ [] := by
    intro empty
    rw [empty] at newBodyCount
    simp at newBodyCount
  cases bodyShape : body with
  | nil => exact False.elim (bodyNonempty bodyShape)
  | cons bodyHead bodyTail =>
      let bodyWord :=
        SemigroupBasis.CoRoots.S5_107.listWordOfCons bodyHead bodyTail
      have bodyCount :
          2 ≤ bodyWord.toList.count newFinal := by
        simpa [bodyWord, bodyShape,
          SemigroupBasis.CoRoots.S5_107.listWordOfCons] using
            newBodyCount
      let oldCopies := finalCopies stem oldFinal
      let newCopies :=
        SemigroupBasis.CoRoots.S5_213Syntax.cappedMultiplicity
          bodyWord newFinal
      have oldBounds : 2 ≤ oldCopies ∧ oldCopies ≤ 3 := by
        constructor
        · unfold oldCopies finalCopies
          have positive := List.count_pos_iff.mpr oldRepeated
          simp only [Nat.min_def]
          split <;> omega
        · exact finalCopies_le_three stem oldFinal
      have newBounds : 2 ≤ newCopies ∧ newCopies ≤ 3 := by
        constructor
        · unfold newCopies
          exact
            (SemigroupBasis.CoRoots.S5_213Syntax.two_le_cappedMultiplicity_iff
              bodyWord newFinal).2 bodyCount
        · unfold newCopies
          unfold SemigroupBasis.CoRoots.S5_213Syntax.cappedMultiplicity
          exact Nat.min_le_left _ _
      have leftAsAppend :
          finalNormalWord stem oldFinal =
            bodyWord ++ finalBlockWord oldFinal oldCopies := by
        apply finalNormalWord_eq_body_append
          stem oldFinal oldCopies rfl
        simpa [body] using bodyShape
      have gathered :=
        derivesGatheredRepeatedWithSuffix
          bodyWord newFinal bodyCount
          (finalBlockWord oldFinal oldCopies)
      have gatheredList :
          (gatheredRepeatedWord bodyWord newFinal).toList =
            removeLetter newFinal bodyWord.toList ++
              List.replicate newCopies newFinal := by
        simpa [newCopies] using
          toList_gatheredRepeatedWord bodyWord newFinal bodyCount
      obtain ⟨switchedPrefix, switchedList⟩ :=
        listDerivesCappedBlockSwitch
          (removeLetter newFinal bodyWord.toList)
          oldFinal newFinal oldCopies newCopies
          oldBounds newBounds
      have switchedWords :
          Derives basis
            (gatheredRepeatedWord bodyWord newFinal ++
              finalBlockWord oldFinal oldCopies)
            (wordOfPrefixFinal switchedPrefix newFinal) := by
        apply derives_of_listDerives_toList
        rw [Word.toList_append, gatheredList,
          toList_finalBlockWord oldFinal oldCopies (by omega),
          toList_wordOfPrefixFinal]
        exact switchedList
      rw [leftAsAppend] at leftNormal
      exact
        ⟨switchedPrefix,
          leftNormal.trans <| gathered.trans switchedWords⟩

/-- Unrestricted derivational completeness from exactly the two semantic
descriptors used by this lane: the final-marker invariant and the M2 capped
multiplicity/singleton-sequence invariant. -/
theorem derives_of_marker_m2Data
    (identity : Identity Nat)
    (markerValid :
      identity.SatisfiedBy finalMarkerThree.semigroup)
    (data : M2Data identity.lhs identity.rhs) :
    Derives basis identity.lhs identity.rhs := by
  let leftSplit := splitPrefixFinal identity.lhs
  let rightSplit := splitPrefixFinal identity.rhs
  have leftReconstruct :
      wordOfPrefixFinal leftSplit.1 leftSplit.2 = identity.lhs :=
    wordOfPrefixFinal_split identity.lhs
  have rightReconstruct :
      wordOfPrefixFinal rightSplit.1 rightSplit.2 = identity.rhs :=
    wordOfPrefixFinal_split identity.rhs
  by_cases sameFinal : leftSplit.2 = rightSplit.2
  · have rightReconstructSame :
        wordOfPrefixFinal rightSplit.1 leftSplit.2 =
          identity.rhs := by
      rw [sameFinal]
      exact rightReconstruct
    have alignedData :
        M2Data
          (wordOfPrefixFinal leftSplit.1 leftSplit.2)
          (wordOfPrefixFinal rightSplit.1 leftSplit.2) := by
      simpa only [leftReconstruct, rightReconstructSame] using data
    rw [← leftReconstruct, ← rightReconstructSame]
    exact
      derivesSameFinal leftSplit.1 rightSplit.1 leftSplit.2
        alignedData
  · have oldRepeated : leftSplit.2 ∈ leftSplit.1 := by
      apply Decidable.byContradiction
      intro oldSimple
      have transported :=
        (finalMarkerValid_splitSimpleFinal_iff
          identity markerValid leftSplit.2).mp
            ⟨rfl, oldSimple⟩
      exact sameFinal transported.1.symm
    have newRepeated : rightSplit.2 ∈ rightSplit.1 := by
      apply Decidable.byContradiction
      intro newSimple
      have transported :=
        (finalMarkerValid_splitSimpleFinal_iff
          identity markerValid rightSplit.2).mpr
            ⟨rfl, newSimple⟩
      exact sameFinal transported.1
    have rightAtLeast :
        2 ≤ identity.rhs.toList.count rightSplit.2 := by
      rw [← rightReconstruct, toList_wordOfPrefixFinal,
        List.count_append]
      have positive := List.count_pos_iff.mpr newRepeated
      simp
      omega
    have leftAtLeast :
        2 ≤ identity.lhs.toList.count rightSplit.2 := by
      have rightCapped :
          2 ≤
            SemigroupBasis.CoRoots.S5_213Syntax.cappedMultiplicity
              identity.rhs rightSplit.2 :=
        (SemigroupBasis.CoRoots.S5_213Syntax.two_le_cappedMultiplicity_iff
          identity.rhs rightSplit.2).2 rightAtLeast
      rw [← data.capped rightSplit.2] at rightCapped
      exact
        (SemigroupBasis.CoRoots.S5_213Syntax.two_le_cappedMultiplicity_iff
          identity.lhs rightSplit.2).1 rightCapped
    rw [← leftReconstruct, toList_wordOfPrefixFinal] at leftAtLeast
    obtain ⟨switchedPrefix, switchDerivation⟩ :=
      derivesChangeRepeatedFinal leftSplit.1 leftSplit.2 rightSplit.2
        sameFinal oldRepeated leftAtLeast
    have reconstructedData :
        M2Data
          (wordOfPrefixFinal leftSplit.1 leftSplit.2)
          (wordOfPrefixFinal rightSplit.1 rightSplit.2) := by
      simpa only [leftReconstruct, rightReconstruct] using data
    have switchedData :
        M2Data
          (wordOfPrefixFinal switchedPrefix rightSplit.2)
          (wordOfPrefixFinal rightSplit.1 rightSplit.2) :=
      M2Data.trans
        (M2Data.symm (m2Data_of_derivation switchDerivation))
        reconstructedData
    have aligned :=
      derivesSameFinal switchedPrefix rightSplit.1 rightSplit.2
        switchedData
    rw [← leftReconstruct, ← rightReconstruct]
    exact switchDerivation.trans aligned

theorem derives_of_s3_6_s5_213_valid
    (identity : Identity Nat)
    (markerValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_6.table.semigroup)
    (m2Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_213.table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  rw [SemigroupBasis.Generated.S3_6.table_eq_catalogue_model]
    at markerValid
  exact derives_of_marker_m2Data identity markerValid
    (m2Data_of_s5_213_valid identity m2Valid)

theorem derives_of_s3_6_s5_498_valid
    (identity : Identity Nat)
    (markerValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_6.table.semigroup)
    (m2Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_498.table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  rw [SemigroupBasis.Generated.S3_6.table_eq_catalogue_model]
    at markerValid
  exact derives_of_marker_m2Data identity markerValid
    (m2Data_of_s5_498_valid identity m2Valid)

theorem derives_of_s3_6_s5_213_opposite_valid
    (identity : Identity Nat)
    (markerValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_6.table.semigroup)
    (m2Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_213.table.semigroup.opposite) :
    Derives basis identity.lhs identity.rhs := by
  rw [SemigroupBasis.Generated.S3_6.table_eq_catalogue_model]
    at markerValid
  exact derives_of_marker_m2Data identity markerValid
    (m2Data_of_s5_213_opposite_valid identity m2Valid)

def s3_6_s5_213IntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_213.table.semigroup
      basis where
  leftModels := markerModels
  rightModels := s5_213Models
  complete := derives_of_s3_6_s5_213_valid

def s3_6_s5_498IntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_498.table.semigroup
      basis where
  leftModels := markerModels
  rightModels := s5_498Models
  complete := derives_of_s3_6_s5_498_valid

def s3_6_s5_213OppositeIntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_213.table.semigroup.opposite
      basis where
  leftModels := markerModels
  rightModels := s5_213OppositeModels
  complete := derives_of_s3_6_s5_213_opposite_valid

end SemigroupBasis.CoRoots.Order6FinalMarkerM2
