import SemigroupBasis.CoRoots.Order6FactorPairS4_116opS5_841Prelude
import SemigroupBasis.CoRoots.S5_1089Normalization
import SemigroupBasis.CoRoots.S5_345Factors
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Subdirect

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6FactorPairS4_116opS5_841

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_1089
open SemigroupBasis.CoRoots.S5_841

private abbrev ListDerives : List Nat -> List Nat -> Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

private def xx : Word Nat := w 0 [0]
private def xxx : Word Nat := w 0 [0, 0]
private def xxyx : Word Nat := w 0 [0, 1, 0]
private def xzx : Word Nat := w 0 [2, 0]
private def xyx : Word Nat := w 0 [1, 0]
private def xyxx : Word Nat := w 0 [1, 0, 0]
private def xyxzy : Word Nat := w 0 [1, 0, 2, 1]
private def yxxzy : Word Nat := w 1 [0, 0, 2, 1]
private def xyxy : Word Nat := w 0 [1, 0, 1]
private def yxxy : Word Nat := w 1 [0, 0, 1]
private def xyxzx : Word Nat := w 0 [1, 0, 2, 0]
private def xyzx : Word Nat := w 0 [1, 2, 0]
private def xyzxy : Word Nat := w 0 [1, 2, 0, 1]
private def yxzxy : Word Nat := w 1 [0, 2, 0, 1]

private def powerLaw : Identity Nat := Identity.mk xx xxx
private def leftDeletionLaw : Identity Nat := Identity.mk xxyx xyx
private def rightExpansionLaw : Identity Nat := Identity.mk xyx xyxx
private def rightContextSwapLaw : Identity Nat := Identity.mk xyxzy yxxzy
private def shortSwapLaw : Identity Nat := Identity.mk xyxy yxxy
private def middleDeletionLaw : Identity Nat := Identity.mk xyxzx xyzx
private def terminalContextSwapLaw : Identity Nat := Identity.mk xyzxy yxzxy

private theorem basisPower : Derives basis xx xxx :=
  Derives.fromBasis (e := powerLaw) (by decide)

private theorem basisLeftDeletion : Derives basis xxyx xyx :=
  Derives.fromBasis (e := leftDeletionLaw) (by decide)

private theorem basisRightExpansion : Derives basis xyx xyxx :=
  Derives.fromBasis (e := rightExpansionLaw) (by decide)

private theorem basisRightContextSwap :
    Derives basis xyxzy yxxzy :=
  Derives.fromBasis (e := rightContextSwapLaw) (by decide)

private theorem basisShortSwap : Derives basis xyxy yxxy :=
  Derives.fromBasis (e := shortSwapLaw) (by decide)

private theorem basisMiddleDeletion : Derives basis xyxzx xyzx :=
  Derives.fromBasis (e := middleDeletionLaw) (by decide)

private theorem basisTerminalContextSwap :
    Derives basis xyzxy yxzxy :=
  Derives.fromBasis (e := terminalContextSwapLaw) (by decide)

private def instantiateFourWords
    (u v z q : Word Nat) : Nat -> Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | 3 => q
  | n + 4 => Word.singleton (n + 4)

private theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisPower (instantiateFourWords u u u u)
  simpa [xx, xxx, w, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesLeftDuplication (u z : Word Nat) :
    Derives basis ((u ++ z) ++ u) (((u ++ u) ++ z) ++ u) := by
  have substituted :=
    Derives.subst basisLeftDeletion (instantiateFourWords u z z z)
  simpa [xxyx, xyx, w, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted.symm

private theorem derivesRightDuplication (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ v) ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisRightExpansion (instantiateFourWords u v v v)
  simpa [xyx, xyxx, w, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesRightContextSwap (u v q : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ q) ++ v)
      ((((v ++ u) ++ u) ++ q) ++ v) := by
  have substituted :=
    Derives.subst basisRightContextSwap
      (instantiateFourWords u v q q)
  simpa [xyxzy, yxxzy, w, instantiateFourWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

private theorem derivesShortSwap (u v : Word Nat) :
    Derives basis (((u ++ v) ++ u) ++ v)
      (((v ++ u) ++ u) ++ v) := by
  have substituted :=
    Derives.subst basisShortSwap (instantiateFourWords u v v v)
  simpa [xyxy, yxxy, w, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesThirdOccurrenceDeletion (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ z) ++ u)
      (((u ++ v) ++ z) ++ u) := by
  have substituted :=
    Derives.subst basisMiddleDeletion (instantiateFourWords u v z z)
  simpa [xyxzx, xyzx, w, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesTerminalContextSwap (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ z) ++ u) ++ v)
      ((((v ++ u) ++ z) ++ u) ++ v) := by
  have substituted :=
    Derives.subst basisTerminalContextSwap
      (instantiateFourWords u v z z)
  simpa [xyzxy, yxzxy, w, instantiateFourWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- The long-gap L6 swap follows from the three candidate context laws:
insert a third `u`, swap the initial pair, then contract the extra `u`. -/
private theorem derivesLongContextSwap (u v z q : Word Nat) :
    Derives basis (((((u ++ v) ++ z) ++ u) ++ q) ++ v)
      (((((v ++ u) ++ z) ++ u) ++ q) ++ v) := by
  have insert :
      Derives basis (((((u ++ v) ++ z) ++ u) ++ q) ++ v)
        ((((((u ++ v) ++ u) ++ z) ++ u) ++ q) ++ v) := by
    simpa [Word.append_assoc] using
      ((derivesThirdOccurrenceDeletion u v z).symm.appendRight q).appendRight v
  have swap :
      Derives basis ((((((u ++ v) ++ u) ++ z) ++ u) ++ q) ++ v)
        ((((((v ++ u) ++ u) ++ z) ++ u) ++ q) ++ v) := by
    simpa [Word.append_assoc] using
      derivesRightContextSwap u v ((z ++ u) ++ q)
  have contract :
      Derives basis ((((((v ++ u) ++ u) ++ z) ++ u) ++ q) ++ v)
        (((((v ++ u) ++ z) ++ u) ++ q) ++ v) := by
    simpa [Word.append_assoc] using
      (((Derives.prepend v (derivesLeftDuplication u z).symm).appendRight q).appendRight v)
  exact insert.trans (swap.trans contract)

/-! ## Semantic invariants of the two factors -/

private def toFinThree : Nat -> Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private theorem candidateModelsM20 :
    Models
      SemigroupBasis.CoRoots.S5_841.publishedM20Table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.CoRoots.S5_841.publishedM20Table basis toFinThree
      (by decide)

private theorem candidateModelsRightRegularBand :
    Models leftRegularBandThree.semigroup.opposite basis :=
  FiniteCertificate.checkModels_sound
    { order := 3
      mul := fun left right =>
        leftRegularBandThree.semigroup.opposite.mul left right
      assoc := leftRegularBandThree.semigroup.opposite.assoc }
    basis toFinThree (by decide)

theorem modelsS5_841 :
    Models SemigroupBasis.CoRoots.S5_841.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.CoRoots.S5_841.table basis toFinThree (by decide)

theorem modelsS4_116Opposite :
    Models
      SemigroupBasis.Generated.Catalogue.S4_116.table.semigroup.opposite
      basis := by
  intro identity member
  have rightRegularValid := candidateModelsRightRegularBand identity member
  have derivation :=
    leftRegularBandThreeOppositeBasis_complete.2
      identity rightRegularValid
  exact fun valuation =>
    derivation.sound
      SemigroupBasis.Generated.BandEmbeddingTransfers.S4_116.opposite_basis.1
      valuation

private theorem rightRegularBandValid_lastOccurrenceSequence_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftRegularBandThree.semigroup.opposite) :
    lastOccurrenceSequence identity.lhs.toList =
      lastOccurrenceSequence identity.rhs.toList := by
  have validReversed :
      identity.reversed.SatisfiedBy leftRegularBandThree.semigroup :=
    (Identity.satisfiedBy_opposite_iff_reversed
      identity leftRegularBandThree.semigroup).mp valid
  have firstReversed :=
    SemigroupBasis.CoRoots.S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
        identity.reversed validReversed
  have reversedEquality := congrArg List.reverse firstReversed
  simpa [Identity.reversed,
    lastOccurrenceSequence_eq_reverse_firstOccurrenceSequence] using
      reversedEquality

private theorem s4Valid_lastOccurrenceSequence_eq
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S4_116.table.semigroup.opposite) :
    lastOccurrenceSequence identity.lhs.toList =
      lastOccurrenceSequence identity.rhs.toList := by
  have reversedValid :
      identity.reversed.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S4_116.table.semigroup :=
    (Identity.satisfiedBy_opposite_iff_reversed identity
      SemigroupBasis.Generated.Catalogue.S4_116.table.semigroup).mp valid
  have lrbValid :
      identity.reversed.SatisfiedBy leftRegularBandThree.semigroup :=
    SemigroupBasis.Generated.BandEmbeddingTransfers.S4_116.embedding.pullback_identity
      identity.reversed reversedValid
  have firstReversed :=
    SemigroupBasis.CoRoots.S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
        identity.reversed lrbValid
  have reversedEquality := congrArg List.reverse firstReversed
  simpa [Identity.reversed,
    lastOccurrenceSequence_eq_reverse_firstOccurrenceSequence] using
      reversedEquality

private theorem m20ListEquivalent_of_derives
    {left right : List Nat} (derivation : ListDerives left right) :
    M20ListEquivalent left right := by
  cases derivation with
  | empty => exact fun _ => rfl
  | @words leftHead rightHead leftTail rightTail wordDerivation =>
      have valid :
          (Identity.mk
            (SemigroupBasis.CoRoots.S5_107.listWordOfCons
              leftHead leftTail)
            (SemigroupBasis.CoRoots.S5_107.listWordOfCons
              rightHead rightTail)).SatisfiedBy
            SemigroupBasis.CoRoots.S5_841.publishedM20Table.semigroup :=
        fun valuation => wordDerivation.sound candidateModelsM20 valuation
      simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons, Word.toList] using
        M20ListEquivalent.of_valid _ valid

private theorem lastOccurrenceSequence_eq_of_derives
    {left right : List Nat} (derivation : ListDerives left right) :
    lastOccurrenceSequence left = lastOccurrenceSequence right := by
  cases derivation with
  | empty => rfl
  | @words leftHead rightHead leftTail rightTail wordDerivation =>
      have valid :
          (Identity.mk
            (SemigroupBasis.CoRoots.S5_107.listWordOfCons
              leftHead leftTail)
            (SemigroupBasis.CoRoots.S5_107.listWordOfCons
              rightHead rightTail)).SatisfiedBy
            leftRegularBandThree.semigroup.opposite :=
        fun valuation =>
          wordDerivation.sound candidateModelsRightRegularBand valuation
      simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons, Word.toList] using
        rightRegularBandValid_lastOccurrenceSequence_eq _ valid

/-! ## Candidate-only endpoint cap -/

private theorem listDerivesDeleteMiddleCore
    (x : Nat) (left right : List Nat) :
    ListDerives
      ([x] ++ left ++ [x] ++ right ++ [x])
      ([x] ++ left ++ right ++ [x]) := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          exact SemigroupBasis.CoRoots.S5_107.ListDerives.words <| by
            simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
              Word.singleton, Word.append, Word.append_assoc,
              List.append_assoc] using
              (derivesPowerExpansion (Word.singleton x)).symm
      | cons y ys =>
          exact SemigroupBasis.CoRoots.S5_107.ListDerives.words <| by
            simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
              Word.singleton, Word.append, Word.append_assoc,
              List.append_assoc] using
              (derivesLeftDuplication
                (Word.singleton x)
                (SemigroupBasis.CoRoots.S5_107.listWordOfCons y ys)).symm
  | cons y ys =>
      cases right with
      | nil =>
          exact SemigroupBasis.CoRoots.S5_107.ListDerives.words <| by
            simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
              Word.singleton, Word.append, Word.append_assoc,
              List.append_assoc] using
              (derivesRightDuplication
                (Word.singleton x)
                (SemigroupBasis.CoRoots.S5_107.listWordOfCons y ys)).symm
      | cons z zs =>
          exact SemigroupBasis.CoRoots.S5_107.ListDerives.words <| by
            simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
              Word.singleton, Word.append, Word.append_assoc,
              List.append_assoc] using
              derivesThirdOccurrenceDeletion
                (Word.singleton x)
                (SemigroupBasis.CoRoots.S5_107.listWordOfCons y ys)
                (SemigroupBasis.CoRoots.S5_107.listWordOfCons z zs)

private theorem listDerivesDeleteCurrent
    (pre suffix : List Nat) (x : Nat)
    (past : x ∈ pre) (future : x ∈ suffix) :
    ListDerives (pre ++ x :: suffix) (pre ++ suffix) := by
  rcases List.append_of_mem past with ⟨before, left, preShape⟩
  rcases List.append_of_mem future with ⟨right, after, suffixShape⟩
  rw [preShape, suffixShape]
  simpa [List.append_assoc] using
    (listDerivesDeleteMiddleCore x left right).context before after

private theorem listDerivesEndpointCapAux
    (pre seen : List Nat)
    (seenInPre : ∀ z ∈ seen, z ∈ pre) :
    ∀ suffix : List Nat,
      ListDerives
        (pre ++ suffix)
        (pre ++ uniqueSeparatorEndpointCapAux seen suffix)
  | [] => by
      simpa using
        SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis) pre
  | x :: xs => by
      by_cases middle : x ∈ seen ∧ x ∈ xs
      · have xInPre : x ∈ pre := seenInPre x middle.1
        have deleteCurrent :
            ListDerives (pre ++ x :: xs) (pre ++ xs) :=
          listDerivesDeleteCurrent pre xs x xInPre middle.2
        have nextSeenInPre : ∀ z ∈ x :: seen, z ∈ pre := by
          intro z member
          rcases List.mem_cons.mp member with rfl | member
          · exact xInPre
          · exact seenInPre z member
        have recurse :=
          listDerivesEndpointCapAux pre (x :: seen) nextSeenInPre xs
        rw [uniqueSeparatorEndpointCapAux, if_pos middle]
        exact deleteCurrent.trans recurse
      · have nextSeenInPre :
            ∀ z ∈ x :: seen, z ∈ pre ++ [x] := by
          intro z member
          rcases List.mem_cons.mp member with rfl | member
          · exact List.mem_append_right pre (List.Mem.head [])
          · exact List.mem_append_left [x] (seenInPre z member)
        have recurse :=
          listDerivesEndpointCapAux
            (pre ++ [x]) (x :: seen) nextSeenInPre xs
        rw [uniqueSeparatorEndpointCapAux, if_neg middle]
        simpa [List.append_assoc] using recurse

private theorem listDerivesTwoLimitedReduction (letters : List Nat) :
    ListDerives letters (uniqueSeparatorEndpointCap letters) := by
  simpa [uniqueSeparatorEndpointCap] using
    listDerivesEndpointCapAux [] [] (by simp) letters

/-! ## The L6 swaps retained by the seven-law basis -/

private theorem listDerivesL6
    (x y : Nat) (middle tail : List Nat) :
    ListDerives
      ([x, y] ++ middle ++ [x] ++ tail ++ [y])
      ([y, x] ++ middle ++ [x] ++ tail ++ [y]) := by
  cases middle with
  | nil =>
      cases tail with
      | nil =>
          exact SemigroupBasis.CoRoots.S5_107.ListDerives.words <| by
            simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
              Word.singleton, Word.append, Word.append_assoc,
              List.append_assoc] using
              derivesShortSwap (Word.singleton x) (Word.singleton y)
      | cons t ts =>
          exact SemigroupBasis.CoRoots.S5_107.ListDerives.words <| by
            simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
              Word.singleton, Word.append, Word.append_assoc,
              List.append_assoc] using
              derivesRightContextSwap
                (Word.singleton x) (Word.singleton y)
                (SemigroupBasis.CoRoots.S5_107.listWordOfCons t ts)
  | cons m ms =>
      cases tail with
      | nil =>
          exact SemigroupBasis.CoRoots.S5_107.ListDerives.words <| by
            simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
              Word.singleton, Word.append, Word.append_assoc,
              List.append_assoc] using
              derivesTerminalContextSwap
                (Word.singleton x) (Word.singleton y)
                (SemigroupBasis.CoRoots.S5_107.listWordOfCons m ms)
      | cons t ts =>
          exact SemigroupBasis.CoRoots.S5_107.ListDerives.words <| by
            simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
              Word.singleton, Word.append, Word.append_assoc,
              List.append_assoc] using
              derivesLongContextSwap
                (Word.singleton x) (Word.singleton y)
                (SemigroupBasis.CoRoots.S5_107.listWordOfCons m ms)
                (SemigroupBasis.CoRoots.S5_107.listWordOfCons t ts)


/-! ## Last-occurrence pair projections -/

private def pairKeep (x y value : Nat) : Bool :=
  decide (value = x ∨ value = y)

private theorem pairFilter_eq_nil_of_absent
    {x y : Nat} (letters : List Nat)
    (xAbsent : x ∉ letters) (yAbsent : y ∉ letters) :
    letters.filter (pairKeep x y) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro letter member
  have letterNeX : letter ≠ x := by
    intro equal
    subst letter
    exact xAbsent member
  have letterNeY : letter ≠ y := by
    intro equal
    subst letter
    exact yAbsent member
  simp [pairKeep, letterNeX, letterNeY]

private theorem lastOccurrenceSequence_filter
    (keep : Nat -> Bool) :
    ∀ letters : List Nat,
      lastOccurrenceSequence (letters.filter keep) =
        (lastOccurrenceSequence letters).filter keep
  | [] => rfl
  | letter :: rest => by
      have induction := lastOccurrenceSequence_filter keep rest
      by_cases kept : keep letter
      · by_cases member : letter ∈ rest
        · have filteredMember : letter ∈ rest.filter keep := by
            simp [member, kept]
          simp [lastOccurrenceSequence, kept, member, filteredMember,
            induction]
        · have filteredAbsent : letter ∉ rest.filter keep := by
            simp [member]
          simp [lastOccurrenceSequence, kept, member, filteredAbsent,
            induction]
      · by_cases member : letter ∈ rest
        · simp [lastOccurrenceSequence, kept, member, induction]
        · simp [lastOccurrenceSequence, kept, member, induction]

private theorem lastOccurrenceSequence_drop_pair_prefix
    {x y : Nat} :
    ∀ (front suffix : List Nat),
      (∀ letter, letter ∈ front -> letter = x ∨ letter = y) ->
      x ∈ suffix ->
      y ∈ suffix ->
      lastOccurrenceSequence (front ++ suffix) =
        lastOccurrenceSequence suffix
  | [], _, _, _, _ => rfl
  | letter :: rest, suffix, onlyPair, xMember, yMember => by
      have letterPair :=
        onlyPair letter (List.Mem.head rest)
      have restOnlyPair :
          ∀ next, next ∈ rest -> next = x ∨ next = y := by
        intro next member
        exact onlyPair next (List.Mem.tail letter member)
      have letterLater : letter ∈ rest ++ suffix := by
        rcases letterPair with rfl | rfl
        · exact List.mem_append_right rest xMember
        · exact List.mem_append_right rest yMember
      rw [List.cons_append, lastOccurrenceSequence, if_pos letterLater]
      exact
        lastOccurrenceSequence_drop_pair_prefix rest suffix
          restOnlyPair xMember yMember

private theorem lastOccurrenceSequence_constant
    (x : Nat) :
    ∀ letters : List Nat,
      letters ≠ [] ->
      (∀ letter, letter ∈ letters -> letter = x) ->
      lastOccurrenceSequence letters = [x]
  | [], nonempty, _ => False.elim (nonempty rfl)
  | letter :: rest, _, allEqual => by
      have letterEqual :=
        allEqual letter (List.Mem.head rest)
      subst letter
      cases rest with
      | nil =>
          simp [lastOccurrenceSequence]
      | cons next tail =>
          have nextEqual :
              next = x :=
            allEqual next (List.Mem.tail x (List.Mem.head tail))
          have xLater : x ∈ next :: tail := by
            simpa [nextEqual]
          rw [lastOccurrenceSequence, if_pos xLater]
          exact
            lastOccurrenceSequence_constant x (next :: tail)
              (by simp)
              (fun value member =>
                allEqual value (List.Mem.tail x member))

private theorem lastOccurrencePairProjection_terminal
    {x y : Nat} (different : x ≠ y)
    (before after : List Nat)
    (xAbsent : x ∉ after) (yAbsent : y ∉ after) :
    (lastOccurrenceSequence (before ++ x :: y :: after)).filter
        (pairKeep x y) =
      [x, y] := by
  rw [← lastOccurrenceSequence_filter]
  have afterFilter :
      after.filter (pairKeep x y) = [] :=
    pairFilter_eq_nil_of_absent after xAbsent yAbsent
  have filteredShape :
      (before ++ x :: y :: after).filter (pairKeep x y) =
        before.filter (pairKeep x y) ++ [x, y] := by
    simp [List.filter_append, pairKeep, different, Ne.symm different,
      afterFilter]
  rw [filteredShape]
  have prefixOnlyPair :
      ∀ letter, letter ∈ before.filter (pairKeep x y) ->
        letter = x ∨ letter = y := by
    intro letter member
    have kept := (List.mem_filter.mp member).2
    simpa [pairKeep] using kept
  calc
    lastOccurrenceSequence
        (before.filter (pairKeep x y) ++ [x, y]) =
        lastOccurrenceSequence [x, y] :=
      lastOccurrenceSequence_drop_pair_prefix
        (before.filter (pairKeep x y)) [x, y]
        prefixOnlyPair (by simp) (by simp)
    _ = [x, y] := by
      simp [lastOccurrenceSequence, different]

private theorem lastOccurrencePairProjection_crossed
    {x y : Nat} (different : x ≠ y)
    (before after : List Nat)
    (yAbsent : y ∉ after) (xMember : x ∈ after) :
    (lastOccurrenceSequence (before ++ y :: after)).filter
        (pairKeep x y) =
      [y, x] := by
  rw [← lastOccurrenceSequence_filter]
  have xKept : x ∈ after.filter (pairKeep x y) := by
    simp [xMember, pairKeep]
  have yFilteredAbsent : y ∉ after.filter (pairKeep x y) := by
    simp [yAbsent]
  have afterOnlyX :
      ∀ letter, letter ∈ after.filter (pairKeep x y) -> letter = x := by
    intro letter member
    have data := List.mem_filter.mp member
    have pair : letter = x ∨ letter = y := by
      simpa [pairKeep] using data.2
    exact pair.resolve_right (fun equal => yAbsent (equal ▸ data.1))
  have prefixOnlyPair :
      ∀ letter, letter ∈ before.filter (pairKeep x y) ->
        letter = x ∨ letter = y := by
    intro letter member
    have kept := (List.mem_filter.mp member).2
    simpa [pairKeep] using kept
  have filteredShape :
      (before ++ y :: after).filter (pairKeep x y) =
        before.filter (pairKeep x y) ++
          y :: after.filter (pairKeep x y) := by
    simp [List.filter_append, pairKeep]
  rw [filteredShape]
  have dropPrefix :
      lastOccurrenceSequence
          (before.filter (pairKeep x y) ++
            y :: after.filter (pairKeep x y)) =
        lastOccurrenceSequence
          (y :: after.filter (pairKeep x y)) :=
    lastOccurrenceSequence_drop_pair_prefix
      (before.filter (pairKeep x y))
      (y :: after.filter (pairKeep x y))
      prefixOnlyPair (List.mem_cons_of_mem y xKept) (List.Mem.head _)
  rw [dropPrefix, lastOccurrenceSequence, if_neg yFilteredAbsent]
  rw [lastOccurrenceSequence_constant x
    (after.filter (pairKeep x y)) (List.ne_nil_of_mem xKept)
    afterOnlyX]

/-! ## Last-occurrence-restricted quadratic block permutations -/


/-! ## Target-directed quadratic block permutations -/

private def blockPrecedenceStep
    (x y : Nat) (state : PrecedenceState) (letter : Nat) :
    PrecedenceState :=
  if letter = x then
    match state with
    | .neither => .onlyX
    | .onlyX => .onlyX
    | .onlyY | .ordered | .violated => .violated
  else if letter = y then
    match state with
    | .neither => .onlyY
    | .onlyX => .ordered
    | .onlyY => .onlyY
    | .ordered => .ordered
    | .violated => .violated
  else state

private theorem precedenceScanList_eq_blockFold
    (letters : List Nat) (x y : Nat) :
    precedenceScanList letters x y =
      letters.foldl (blockPrecedenceStep x y) .neither := by
  rfl

private def blockPairFree
    (x y : Nat) (letters : List Nat) : Prop :=
  x ∉ letters ∧ y ∉ letters

private theorem blockPrecedenceFold_pairFree
    (x y : Nat) :
    ∀ (letters : List Nat) (state : PrecedenceState),
      blockPairFree x y letters →
      letters.foldl (blockPrecedenceStep x y) state = state
  | [], _, _ => rfl
  | letter :: rest, state, free => by
      have letterNeX : letter ≠ x := by
        intro equal
        subst letter
        exact free.1 (List.Mem.head rest)
      have letterNeY : letter ≠ y := by
        intro equal
        subst letter
        exact free.2 (List.Mem.head rest)
      have restFree : blockPairFree x y rest :=
        ⟨fun member => free.1 (List.Mem.tail letter member),
          fun member => free.2 (List.Mem.tail letter member)⟩
      simp only [List.foldl_cons]
      rw [show blockPrecedenceStep x y state letter = state by
        simp [blockPrecedenceStep, letterNeX, letterNeY]]
      exact blockPrecedenceFold_pairFree x y rest state restFree

private theorem blockPrecedenceFold_onlyX_of_y_absent
    (x y : Nat) :
    ∀ letters : List Nat,
      y ∉ letters →
      letters.foldl (blockPrecedenceStep x y) .onlyX = .onlyX
  | [], _ => rfl
  | letter :: rest, absent => by
      have letterNeY : letter ≠ y := by
        intro equal
        subst letter
        exact absent (List.Mem.head rest)
      have restAbsent : y ∉ rest :=
        fun member => absent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      rw [show blockPrecedenceStep x y .onlyX letter = .onlyX by
        by_cases isX : letter = x
        · simp [blockPrecedenceStep, isX]
        · simp [blockPrecedenceStep, isX, letterNeY]]
      exact blockPrecedenceFold_onlyX_of_y_absent x y rest restAbsent

private theorem blockPrecedenceFold_ordered_of_x_absent
    (x y : Nat) :
    ∀ letters : List Nat,
      x ∉ letters →
      letters.foldl (blockPrecedenceStep x y) .ordered = .ordered
  | [], _ => rfl
  | letter :: rest, absent => by
      have letterNeX : letter ≠ x := by
        intro equal
        subst letter
        exact absent (List.Mem.head rest)
      have restAbsent : x ∉ rest :=
        fun member => absent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      rw [show blockPrecedenceStep x y .ordered letter = .ordered by
        simp [blockPrecedenceStep, letterNeX]]
      exact blockPrecedenceFold_ordered_of_x_absent x y rest restAbsent

private theorem blockPrecedenceFold_violated
    (x y : Nat) :
    ∀ letters : List Nat,
      letters.foldl (blockPrecedenceStep x y) .violated = .violated
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      rw [show blockPrecedenceStep x y .violated letter = .violated by
        simp [blockPrecedenceStep]]
      exact blockPrecedenceFold_violated x y rest

private theorem blockPrecedenceFold_onlyX_of_x_mem_y_absent
    (x y : Nat) :
    ∀ letters : List Nat,
      x ∈ letters →
      y ∉ letters →
      letters.foldl (blockPrecedenceStep x y) .neither = .onlyX
  | [], member, _ => by simp at member
  | letter :: rest, xMember, yAbsent => by
      have letterNeY : letter ≠ y := by
        intro equal
        subst letter
        exact yAbsent (List.Mem.head rest)
      have restYAbsent : y ∉ rest :=
        fun member => yAbsent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      by_cases isX : letter = x
      · rw [show blockPrecedenceStep x y .neither letter = .onlyX by
          simp [blockPrecedenceStep, isX]]
        exact
          blockPrecedenceFold_onlyX_of_y_absent
            x y rest restYAbsent
      · have restXMember : x ∈ rest := by
          exact
            (List.mem_cons.mp xMember).resolve_left (Ne.symm isX)
        rw [show blockPrecedenceStep x y .neither letter = .neither by
          simp [blockPrecedenceStep, isX, letterNeY]]
        exact
          blockPrecedenceFold_onlyX_of_x_mem_y_absent
            x y rest restXMember restYAbsent

private theorem blockPrecedenceFold_ordered_of_x_absent_y_mem
    (x y : Nat) :
    ∀ letters : List Nat,
      x ∉ letters →
      y ∈ letters →
      letters.foldl (blockPrecedenceStep x y) .onlyX = .ordered
  | [], _, member => by simp at member
  | letter :: rest, xAbsent, yMember => by
      have letterNeX : letter ≠ x := by
        intro equal
        subst letter
        exact xAbsent (List.Mem.head rest)
      have restXAbsent : x ∉ rest :=
        fun member => xAbsent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      by_cases isY : letter = y
      · rw [show blockPrecedenceStep x y .onlyX letter = .ordered by
          have yNeX : y ≠ x := fun equal =>
            letterNeX (isY.trans equal)
          simp [blockPrecedenceStep, isY, yNeX]]
        exact
          blockPrecedenceFold_ordered_of_x_absent
            x y rest restXAbsent
      · have restYMember : y ∈ rest := by
          exact
            (List.mem_cons.mp yMember).resolve_left (Ne.symm isY)
        rw [show blockPrecedenceStep x y .onlyX letter = .onlyX by
          simp [blockPrecedenceStep, letterNeX, isY]]
        exact
          blockPrecedenceFold_ordered_of_x_absent_y_mem
            x y rest restXAbsent restYMember

private theorem blockPrecedenceFold_violated_of_x_mem_from_onlyY
    (x y : Nat) :
    ∀ letters : List Nat,
      x ∈ letters →
      letters.foldl (blockPrecedenceStep x y) .onlyY = .violated
  | [], member => by simp at member
  | letter :: rest, member => by
      simp only [List.foldl_cons]
      by_cases isX : letter = x
      · rw [show blockPrecedenceStep x y .onlyY letter = .violated by
          simp [blockPrecedenceStep, isX]]
        exact blockPrecedenceFold_violated x y rest
      · have restMember : x ∈ rest := by
          exact
            (List.mem_cons.mp member).resolve_left (Ne.symm isX)
        rw [show blockPrecedenceStep x y .onlyY letter = .onlyY by
          simp [blockPrecedenceStep, isX]]
        exact
          blockPrecedenceFold_violated_of_x_mem_from_onlyY
            x y rest restMember

private theorem blockPrecedenceFold_violated_of_x_mem_from_ordered
    (x y : Nat) :
    ∀ letters : List Nat,
      x ∈ letters →
      letters.foldl (blockPrecedenceStep x y) .ordered = .violated
  | [], member => by simp at member
  | letter :: rest, member => by
      simp only [List.foldl_cons]
      by_cases isX : letter = x
      · rw [show blockPrecedenceStep x y .ordered letter = .violated by
          simp [blockPrecedenceStep, isX]]
        exact blockPrecedenceFold_violated x y rest
      · have restMember : x ∈ rest := by
          exact
            (List.mem_cons.mp member).resolve_left (Ne.symm isX)
        rw [show blockPrecedenceStep x y .ordered letter = .ordered by
          simp [blockPrecedenceStep, isX]]
        exact
          blockPrecedenceFold_violated_of_x_mem_from_ordered
            x y rest restMember

private theorem precedenceScan_ordered_of_split
    {x y : Nat} (different : x ≠ y)
    (before after : List Nat)
    (xInBefore : x ∈ before)
    (yAbsentBefore : y ∉ before)
    (xAbsentAfter : x ∉ after)
    (yInAfter : y ∈ after) :
    precedenceScanList (before ++ x :: after) x y = .ordered := by
  rw [precedenceScanList_eq_blockFold]
  rw [List.foldl_append]
  rw [blockPrecedenceFold_onlyX_of_x_mem_y_absent
    x y before xInBefore yAbsentBefore]
  simp only [List.foldl_cons]
  rw [show blockPrecedenceStep x y .onlyX x = .onlyX by
    simp [blockPrecedenceStep]]
  exact
    blockPrecedenceFold_ordered_of_x_absent_y_mem
      x y after xAbsentAfter yInAfter

private theorem precedenceScan_violated_of_inversion
    {x y : Nat} (different : x ≠ y)
    (before after : List Nat)
    (yAbsentBefore : y ∉ before)
    (xInAfter : x ∈ after) :
    precedenceScanList (before ++ y :: after) x y = .violated := by
  rw [precedenceScanList_eq_blockFold]
  rw [List.foldl_append]
  by_cases xInBefore : x ∈ before
  · rw [blockPrecedenceFold_onlyX_of_x_mem_y_absent
      x y before xInBefore yAbsentBefore]
    simp only [List.foldl_cons]
    rw [show blockPrecedenceStep x y .onlyX y = .ordered by
      simp [blockPrecedenceStep, Ne.symm different]]
    exact
      blockPrecedenceFold_violated_of_x_mem_from_ordered
        x y after xInAfter
  · have free : blockPairFree x y before :=
      ⟨xInBefore, yAbsentBefore⟩
    rw [blockPrecedenceFold_pairFree x y before .neither free]
    simp only [List.foldl_cons]
    rw [show blockPrecedenceStep x y .neither y = .onlyY by
      simp [blockPrecedenceStep, Ne.symm different]]
    exact
      blockPrecedenceFold_violated_of_x_mem_from_onlyY
        x y after xInAfter

private theorem precedenceState_violated_ne_ordered :
    (PrecedenceState.violated : PrecedenceState) ≠ .ordered := by
  decide

private theorem listDerivesMoveMemberToFront
    (fixedPrefix targetTail sourcePost targetPost : List Nat)
    (selected : Nat) :
    ∀ (crossed source : List Nat),
      selected ∉ crossed →
      (crossed ++ source).Perm (selected :: targetTail) →
      (∀ letter, letter ∈ crossed ++ source →
        (fixedPrefix ++ crossed ++ source ++ sourcePost).count letter = 2) →
      (∀ letter, letter ∈ selected :: targetTail →
        (fixedPrefix ++ (selected :: targetTail) ++ targetPost).count letter =
          2) →
      M20ListEquivalent
        (fixedPrefix ++ crossed ++ source ++ sourcePost)
        (fixedPrefix ++ (selected :: targetTail) ++ targetPost) →
      lastOccurrenceSequence
          (fixedPrefix ++ crossed ++ source ++ sourcePost) =
        lastOccurrenceSequence
          (fixedPrefix ++ (selected :: targetTail) ++ targetPost) →
      S5_107.ListDerives basis
        (fixedPrefix ++ crossed ++ source ++ sourcePost)
        (fixedPrefix ++ crossed ++
          (selected :: source.erase selected) ++ sourcePost)
  | crossed, [], selectedAbsent, permutation, _, _, _, _ => by
      have selectedInCrossed : selected ∈ crossed :=
        by simpa using
          permutation.mem_iff.mpr (List.Mem.head targetTail)
      exact False.elim (selectedAbsent selectedInCrossed)
  | crossed, head :: tail, selectedAbsent, permutation,
      sourceQuadratic, targetQuadratic, equivalent, lastEqual => by
      by_cases equal : head = selected
      · subst head
        simpa [List.append_assoc] using
          S5_107.ListDerives.refl (basis := basis)
            (fixedPrefix ++ crossed ++ (selected :: tail) ++ sourcePost)
      · have selectedInBlock :
            selected ∈ crossed ++ head :: tail :=
          permutation.mem_iff.mpr (List.Mem.head targetTail)
        have selectedInSource : selected ∈ head :: tail :=
          (List.mem_append.mp selectedInBlock).resolve_left selectedAbsent
        have selectedInTail : selected ∈ tail := by
          simpa [Ne.symm equal] using selectedInSource
        have nextSelectedAbsent : selected ∉ crossed ++ [head] := by
          simp [selectedAbsent, Ne.symm equal]
        have nextPermutation :
            ((crossed ++ [head]) ++ tail).Perm
              (selected :: targetTail) := by
          simpa [List.append_assoc] using permutation
        have nextSourceQuadratic :
            ∀ letter, letter ∈ (crossed ++ [head]) ++ tail →
              (fixedPrefix ++ (crossed ++ [head]) ++ tail ++ sourcePost).count
                  letter =
                2 := by
          intro letter member
          have oldMember : letter ∈ crossed ++ head :: tail := by
            simpa [List.append_assoc] using member
          simpa [List.append_assoc] using
            sourceQuadratic letter oldMember
        have nextEquivalent :
            M20ListEquivalent
              (fixedPrefix ++ (crossed ++ [head]) ++ tail ++ sourcePost)
              (fixedPrefix ++ (selected :: targetTail) ++ targetPost) := by
          simpa [List.append_assoc] using equivalent
        have nextLastEqual :
            lastOccurrenceSequence
                (fixedPrefix ++ (crossed ++ [head]) ++ tail ++ sourcePost) =
              lastOccurrenceSequence
                (fixedPrefix ++ (selected :: targetTail) ++ targetPost) := by
          simpa [List.append_assoc] using lastEqual
        have moveTail :=
          listDerivesMoveMemberToFront
            fixedPrefix targetTail sourcePost targetPost selected
            (crossed ++ [head]) tail nextSelectedAbsent
            nextPermutation nextSourceQuadratic targetQuadratic
            nextEquivalent nextLastEqual
        have movedEquivalent :
            M20ListEquivalent
              ((fixedPrefix ++ crossed) ++
                (head :: selected ::
                  (tail.erase selected ++ sourcePost)))
              (fixedPrefix ++ (selected :: targetTail) ++ targetPost) := by
          have moveSound := m20ListEquivalent_of_derives moveTail
          exact (by
            simpa [List.append_assoc] using
              moveSound.symm.trans nextEquivalent)
        have movedLastEqual :
            lastOccurrenceSequence
                ((fixedPrefix ++ crossed) ++
                  (head :: selected ::
                    (tail.erase selected ++ sourcePost))) =
              lastOccurrenceSequence
                (fixedPrefix ++ (selected :: targetTail) ++ targetPost) := by
          have movePreservesLast :=
            lastOccurrenceSequence_eq_of_derives moveTail
          exact (by
            simpa [List.append_assoc] using
              movePreservesLast.symm.trans nextLastEqual)
        have tailExpose :
            tail.Perm (selected :: tail.erase selected) :=
          List.perm_cons_erase selectedInTail
        have sourceExpose :
            (head :: tail).Perm
              (head :: selected :: tail.erase selected) :=
          List.Perm.cons head tailExpose
        have fullExpose :
            (fixedPrefix ++ crossed ++ (head :: tail) ++ sourcePost).Perm
              ((fixedPrefix ++ crossed) ++
                (head :: selected ::
                  (tail.erase selected ++ sourcePost))) := by
          simpa [List.append_assoc] using
            List.Perm.append
              (List.Perm.append
                (List.Perm.refl (fixedPrefix ++ crossed)) sourceExpose)
              (List.Perm.refl sourcePost)
        have headQuadratic :
            (((fixedPrefix ++ crossed) ++
              (head :: selected ::
                (tail.erase selected ++ sourcePost))).count
                head) =
              2 := by
          calc
            (((fixedPrefix ++ crossed) ++
                (head :: selected ::
                  (tail.erase selected ++ sourcePost))).count
                  head) =
                (((fixedPrefix ++ crossed) ++
                  (head :: tail) ++ sourcePost).count head) := by
              exact (fullExpose.count head).symm
            _ = 2 := by
              simpa [List.append_assoc] using
                sourceQuadratic head (by simp)
        have selectedQuadratic :
            (((fixedPrefix ++ crossed) ++
              (head :: selected ::
                (tail.erase selected ++ sourcePost))).count
                selected) =
              2 := by
          calc
            (((fixedPrefix ++ crossed) ++
                (head :: selected ::
                  (tail.erase selected ++ sourcePost))).count
                  selected) =
                (((fixedPrefix ++ crossed) ++
                  (head :: tail) ++ sourcePost).count selected) := by
              exact (fullExpose.count selected).symm
            _ = 2 := by
              simpa [List.append_assoc] using
                sourceQuadratic selected (by
                  simp [selectedInTail])
        have headInTargetTail : head ∈ targetTail := by
          have headInTarget : head ∈ selected :: targetTail :=
            permutation.mem_iff.mp (by simp)
          simpa [equal] using headInTarget
        have position :
            QuadraticSwapPosition head selected
              (fixedPrefix ++ crossed)
              (tail.erase selected ++ sourcePost) :=
          uniqueSeparatorAdjacentQuadraticPosition_of_counts
            equal headQuadratic selectedQuadratic
        have swap :
            S5_107.ListDerives basis
              ((fixedPrefix ++ crossed) ++
                (head :: selected ::
                  (tail.erase selected ++ sourcePost)))
              ((fixedPrefix ++ crossed) ++
                (selected :: head ::
                  (tail.erase selected ++ sourcePost))) := by
          cases position with
          | futureXY middle between after postShape =>
              rw [postShape]
              simpa [List.append_assoc] using
                (listDerivesL6 head selected middle between).context
                  (fixedPrefix ++ crossed) after
          | futureYX middle between after postShape =>
              rw [postShape]
              simpa [List.append_assoc] using
                (listDerivesL6 selected head middle between).symm.context
                  (fixedPrefix ++ crossed) after
          | straddleXY before left right after preShape postShape =>
              have headCount := headQuadratic
              have selectedCount := selectedQuadratic
              rw [preShape, postShape] at headCount selectedCount
              simp only [List.count_append, List.count_cons] at headCount selectedCount
              simp [equal, Ne.symm equal] at headCount selectedCount
              have headInCurrentPrefix :
                  head ∈ fixedPrefix ++ crossed := by
                rw [preShape]
                simp
              have selectedPrefixCount :
                  (fixedPrefix ++ crossed).count selected = 0 := by
                rw [preShape]
                simp only [List.count_append, List.count_cons]
                simp [equal, Ne.symm equal]
                omega
              have selectedAbsentCurrentPrefix :
                  selected ∉ fixedPrefix ++ crossed :=
                List.count_eq_zero.mp selectedPrefixCount
              have headRestCount :
                  (tail.erase selected ++ sourcePost).count head = 0 := by
                rw [postShape]
                simp only [List.count_append, List.count_cons]
                simp [equal, Ne.symm equal]
                omega
              have headAbsentRest :
                  head ∉ tail.erase selected ++ sourcePost :=
                List.count_eq_zero.mp headRestCount
              have headAbsentSourceAfter :
                  head ∉ selected ::
                    (tail.erase selected ++ sourcePost) := by
                simp [equal, headAbsentRest]
              have selectedAbsentFixedPrefix :
                  selected ∉ fixedPrefix := by
                intro member
                exact selectedAbsentCurrentPrefix
                  (List.mem_append_left crossed member)
              have headInTargetAfter :
                  head ∈ targetTail ++ targetPost :=
                List.mem_append_left targetPost headInTargetTail
              have sourcePrecedence :
                  CompletePrecedenceList
                    ((fixedPrefix ++ crossed) ++
                      (head :: selected ::
                        (tail.erase selected ++ sourcePost)))
                    head selected :=
                ⟨equal, by
                  exact
                    precedenceScan_ordered_of_split equal
                      (fixedPrefix ++ crossed)
                      (selected ::
                        (tail.erase selected ++ sourcePost))
                      headInCurrentPrefix selectedAbsentCurrentPrefix
                      headAbsentSourceAfter (by simp)⟩
              have targetNotPrecedence :
                  ¬ CompletePrecedenceList
                    (fixedPrefix ++ (selected :: targetTail) ++ targetPost)
                    head selected := by
                intro targetPrecedence
                have targetScan :
                    precedenceScanList
                        (fixedPrefix ++ (selected :: targetTail) ++ targetPost)
                        head selected =
                      .violated := by
                  simpa [List.append_assoc] using
                    precedenceScan_violated_of_inversion equal
                      fixedPrefix (targetTail ++ targetPost)
                      selectedAbsentFixedPrefix headInTargetAfter
                exact precedenceState_violated_ne_ordered
                  (targetScan.symm.trans targetPrecedence.2)
              have preserved :=
                m20ListEquivalent_completePrecedenceList
                  movedEquivalent head selected
              exact False.elim
                (targetNotPrecedence (preserved.mp sourcePrecedence))
          | straddleYX before left right after preShape postShape =>
              have headCount := headQuadratic
              have selectedCount := selectedQuadratic
              rw [preShape, postShape] at headCount selectedCount
              simp only [List.count_append, List.count_cons] at headCount selectedCount
              simp [equal, Ne.symm equal] at headCount selectedCount
              have headPrefixCount :
                  (fixedPrefix ++ crossed).count head = 0 := by
                rw [preShape]
                simp only [List.count_append, List.count_cons]
                simp [equal, Ne.symm equal]
                omega
              have headAbsentCurrentPrefix :
                  head ∉ fixedPrefix ++ crossed :=
                List.count_eq_zero.mp headPrefixCount
              have headAbsentFixedPrefix : head ∉ fixedPrefix := by
                intro member
                exact headAbsentCurrentPrefix
                  (List.mem_append_left crossed member)
              have selectedInCurrentPrefix :
                  selected ∈ fixedPrefix ++ crossed := by
                rw [preShape]
                simp
              have selectedInFixedPrefix : selected ∈ fixedPrefix := by
                rcases List.mem_append.mp selectedInCurrentPrefix with
                  inFixed | inCrossed
                · exact inFixed
                · exact False.elim (selectedAbsent inCrossed)
              have fixedSelectedPositive :
                  1 ≤ fixedPrefix.count selected :=
                List.one_le_count_iff.mpr selectedInFixedPrefix
              have targetSelectedCount :=
                targetQuadratic selected (by simp)
              simp only [List.count_append, List.count_cons_self] at targetSelectedCount
              have selectedTargetAfterCount :
                  (targetTail ++ targetPost).count selected = 0 := by
                simp only [List.count_append]
                omega
              have selectedAbsentTargetAfter :
                  selected ∉ targetTail ++ targetPost :=
                List.count_eq_zero.mp selectedTargetAfterCount
              have headInTargetAfter :
                  head ∈ targetTail ++ targetPost :=
                List.mem_append_left targetPost headInTargetTail
              have sourceNotPrecedence :
                  ¬ CompletePrecedenceList
                    ((fixedPrefix ++ crossed) ++
                      (head :: selected ::
                        (tail.erase selected ++ sourcePost)))
                    selected head := by
                intro sourcePrecedence
                have sourceScan :
                    precedenceScanList
                        ((fixedPrefix ++ crossed) ++
                          (head :: selected ::
                            (tail.erase selected ++ sourcePost)))
                        selected head =
                      .violated := by
                  exact
                    precedenceScan_violated_of_inversion
                      (Ne.symm equal) (fixedPrefix ++ crossed)
                      (selected ::
                        (tail.erase selected ++ sourcePost))
                      headAbsentCurrentPrefix (by simp)
                exact precedenceState_violated_ne_ordered
                  (sourceScan.symm.trans sourcePrecedence.2)
              have targetPrecedence :
                  CompletePrecedenceList
                    (fixedPrefix ++ (selected :: targetTail) ++ targetPost)
                    selected head :=
                ⟨Ne.symm equal, by
                  simpa [List.append_assoc] using
                    precedenceScan_ordered_of_split
                      (Ne.symm equal) fixedPrefix
                      (targetTail ++ targetPost)
                      selectedInFixedPrefix headAbsentFixedPrefix
                      selectedAbsentTargetAfter headInTargetAfter⟩
              have preserved :=
                m20ListEquivalent_completePrecedenceList
                  movedEquivalent selected head
              exact False.elim
                (sourceNotPrecedence (preserved.mpr targetPrecedence))
          | pastXY before left middle preShape =>
              have headCount := headQuadratic
              have selectedCount := selectedQuadratic
              rw [preShape] at headCount selectedCount
              simp only [List.count_append, List.count_cons] at headCount selectedCount
              simp [equal, Ne.symm equal] at headCount selectedCount
              have headTailCount : tail.count head = 0 := by
                omega
              have headSourcePostCount : sourcePost.count head = 0 := by
                omega
              have headAfterCount :
                  (tail.erase selected ++ sourcePost).count head = 0 := by
                simp [List.count_append, List.count_erase_of_ne equal,
                  headTailCount, headSourcePostCount]
              have selectedTailCount : tail.count selected = 1 := by
                have positive :=
                  List.one_le_count_iff.mpr selectedInTail
                omega
              have selectedSourcePostCount :
                  sourcePost.count selected = 0 := by
                omega
              have selectedAfterCount :
                  (tail.erase selected ++ sourcePost).count selected = 0 := by
                simp [List.count_append, List.count_erase_self,
                  selectedTailCount, selectedSourcePostCount]
              have headAbsentAfter :
                  head ∉ tail.erase selected ++ sourcePost :=
                List.count_eq_zero.mp headAfterCount
              have selectedAbsentAfter :
                  selected ∉ tail.erase selected ++ sourcePost :=
                List.count_eq_zero.mp selectedAfterCount
              have selectedInCurrentPrefix :
                  selected ∈ fixedPrefix ++ crossed := by
                rw [preShape]
                simp
              have selectedInFixedPrefix : selected ∈ fixedPrefix := by
                rcases List.mem_append.mp selectedInCurrentPrefix with
                  inFixed | inCrossed
                · exact inFixed
                · exact False.elim (selectedAbsent inCrossed)
              have fixedSelectedPositive :
                  1 ≤ fixedPrefix.count selected :=
                List.one_le_count_iff.mpr selectedInFixedPrefix
              have targetSelectedCount :=
                targetQuadratic selected (by simp)
              simp only [List.count_append, List.count_cons_self] at targetSelectedCount
              have selectedTargetAfterCount :
                  (targetTail ++ targetPost).count selected = 0 := by
                simp only [List.count_append]
                omega
              have selectedAbsentTargetAfter :
                  selected ∉ targetTail ++ targetPost :=
                List.count_eq_zero.mp selectedTargetAfterCount
              have headInTargetAfter :
                  head ∈ targetTail ++ targetPost :=
                List.mem_append_left targetPost headInTargetTail
              have sourceProjection :=
                lastOccurrencePairProjection_terminal equal
                  (fixedPrefix ++ crossed)
                  (tail.erase selected ++ sourcePost)
                  headAbsentAfter selectedAbsentAfter
              have targetProjection :=
                lastOccurrencePairProjection_crossed equal
                  fixedPrefix (targetTail ++ targetPost)
                  selectedAbsentTargetAfter headInTargetAfter
              have projected :=
                congrArg (List.filter (pairKeep head selected))
                  movedLastEqual
              rw [sourceProjection] at projected
              have targetProjection' :
                  (lastOccurrenceSequence
                    (fixedPrefix ++ selected :: targetTail ++ targetPost)).filter
                      (pairKeep head selected) =
                    [selected, head] := by
                simpa [List.append_assoc] using targetProjection
              rw [targetProjection'] at projected
              have headEqual : head = selected := by
                have heads := congrArg List.head? projected
                simpa using heads
              exact False.elim (equal headEqual)
          | pastYX before left middle preShape =>
              have headCount := headQuadratic
              have selectedCount := selectedQuadratic
              rw [preShape] at headCount selectedCount
              simp only [List.count_append, List.count_cons] at headCount selectedCount
              simp [equal, Ne.symm equal] at headCount selectedCount
              have headTailCount : tail.count head = 0 := by
                omega
              have headSourcePostCount : sourcePost.count head = 0 := by
                omega
              have headAfterCount :
                  (tail.erase selected ++ sourcePost).count head = 0 := by
                simp [List.count_append, List.count_erase_of_ne equal,
                  headTailCount, headSourcePostCount]
              have selectedTailCount : tail.count selected = 1 := by
                have positive :=
                  List.one_le_count_iff.mpr selectedInTail
                omega
              have selectedSourcePostCount :
                  sourcePost.count selected = 0 := by
                omega
              have selectedAfterCount :
                  (tail.erase selected ++ sourcePost).count selected = 0 := by
                simp [List.count_append, List.count_erase_self,
                  selectedTailCount, selectedSourcePostCount]
              have headAbsentAfter :
                  head ∉ tail.erase selected ++ sourcePost :=
                List.count_eq_zero.mp headAfterCount
              have selectedAbsentAfter :
                  selected ∉ tail.erase selected ++ sourcePost :=
                List.count_eq_zero.mp selectedAfterCount
              have selectedInCurrentPrefix :
                  selected ∈ fixedPrefix ++ crossed := by
                rw [preShape]
                simp
              have selectedInFixedPrefix : selected ∈ fixedPrefix := by
                rcases List.mem_append.mp selectedInCurrentPrefix with
                  inFixed | inCrossed
                · exact inFixed
                · exact False.elim (selectedAbsent inCrossed)
              have fixedSelectedPositive :
                  1 ≤ fixedPrefix.count selected :=
                List.one_le_count_iff.mpr selectedInFixedPrefix
              have targetSelectedCount :=
                targetQuadratic selected (by simp)
              simp only [List.count_append, List.count_cons_self] at targetSelectedCount
              have selectedTargetAfterCount :
                  (targetTail ++ targetPost).count selected = 0 := by
                simp only [List.count_append]
                omega
              have selectedAbsentTargetAfter :
                  selected ∉ targetTail ++ targetPost :=
                List.count_eq_zero.mp selectedTargetAfterCount
              have headInTargetAfter :
                  head ∈ targetTail ++ targetPost :=
                List.mem_append_left targetPost headInTargetTail
              have sourceProjection :=
                lastOccurrencePairProjection_terminal equal
                  (fixedPrefix ++ crossed)
                  (tail.erase selected ++ sourcePost)
                  headAbsentAfter selectedAbsentAfter
              have targetProjection :=
                lastOccurrencePairProjection_crossed equal
                  fixedPrefix (targetTail ++ targetPost)
                  selectedAbsentTargetAfter headInTargetAfter
              have projected :=
                congrArg (List.filter (pairKeep head selected))
                  movedLastEqual
              rw [sourceProjection] at projected
              have targetProjection' :
                  (lastOccurrenceSequence
                    (fixedPrefix ++ selected :: targetTail ++ targetPost)).filter
                      (pairKeep head selected) =
                    [selected, head] := by
                simpa [List.append_assoc] using targetProjection
              rw [targetProjection'] at projected
              have headEqual : head = selected := by
                have heads := congrArg List.head? projected
                simpa using heads
              exact False.elim (equal headEqual)
        have complete := moveTail.trans <| by
          simpa [List.append_assoc] using swap
        simpa only [List.append_assoc, List.erase,
          beq_eq_false_iff_ne.mpr equal] using complete
termination_by
  _ source => source.length

/-- Target-directed quadratic block permutation. The semantic target may
have a different suffix; the derivation changes only the source block and
retains `sourcePost`. Exact quadratic counts are required in both complete
contexts so repeated labels remain controlled during target selection. -/
theorem listDerivesQuadraticBlockPermutationAgainst :
    ∀ (target source pre sourcePost targetPost : List Nat),
      source.Perm target →
      (∀ letter, letter ∈ source →
        (pre ++ source ++ sourcePost).count letter = 2) →
      (∀ letter, letter ∈ target →
        (pre ++ target ++ targetPost).count letter = 2) →
      M20ListEquivalent
        (pre ++ source ++ sourcePost)
        (pre ++ target ++ targetPost) →
      lastOccurrenceSequence (pre ++ source ++ sourcePost) =
        lastOccurrenceSequence (pre ++ target ++ targetPost) →
      S5_107.ListDerives basis
        (pre ++ source ++ sourcePost)
        (pre ++ target ++ sourcePost)
  | [], source, pre, sourcePost, _, permutation, _, _, _, _ => by
      have sourceEmpty : source = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa using permutation.length_eq
      subst source
      simpa [List.append_assoc] using
        S5_107.ListDerives.refl (basis := basis) (pre ++ sourcePost)
  | selected :: targetTail, source, pre, sourcePost, targetPost,
      permutation, sourceQuadratic, targetQuadratic, equivalent,
      lastEqual => by
      have moveRaw :=
        listDerivesMoveMemberToFront
          pre targetTail sourcePost targetPost selected [] source
          (by simp) (by simpa using permutation)
          (by simpa [List.append_assoc] using sourceQuadratic)
          targetQuadratic (by simpa [List.append_assoc] using equivalent)
          (by simpa [List.append_assoc] using lastEqual)
      have move :
          S5_107.ListDerives basis
            (pre ++ source ++ sourcePost)
            ((pre ++ [selected]) ++ source.erase selected ++ sourcePost) := by
        simpa [List.append_assoc] using moveRaw
      have selectedInSource : selected ∈ source :=
        permutation.mem_iff.mpr (by simp)
      have sourceExpose :
          source.Perm (selected :: source.erase selected) :=
        List.perm_cons_erase selectedInSource
      have erasedPermutation :
          (source.erase selected).Perm targetTail := by
        simpa using permutation.erase selected
      have fullExpose :
          (pre ++ source ++ sourcePost).Perm
            ((pre ++ [selected]) ++ source.erase selected ++ sourcePost) := by
        simpa [List.append_assoc] using
          List.Perm.append
            (List.Perm.append (List.Perm.refl pre) sourceExpose)
            (List.Perm.refl sourcePost)
      have erasedSourceQuadratic :
          ∀ letter, letter ∈ source.erase selected →
            ((pre ++ [selected]) ++ source.erase selected ++ sourcePost).count
                letter =
              2 := by
        intro letter erasedMember
        have sourceMember : letter ∈ source :=
          List.mem_of_mem_erase erasedMember
        calc
          ((pre ++ [selected]) ++ source.erase selected ++ sourcePost).count
              letter =
              (pre ++ source ++ sourcePost).count letter := by
            exact (fullExpose.count letter).symm
          _ = 2 := sourceQuadratic letter sourceMember
      have erasedTargetQuadratic :
          ∀ letter, letter ∈ targetTail →
            ((pre ++ [selected]) ++ targetTail ++ targetPost).count letter =
              2 := by
        intro letter member
        simpa [List.append_assoc] using
          targetQuadratic letter (List.Mem.tail selected member)
      have exposedEquivalent :
          M20ListEquivalent
            ((pre ++ [selected]) ++ source.erase selected ++ sourcePost)
            ((pre ++ [selected]) ++ targetTail ++ targetPost) := by
        have moveSound := m20ListEquivalent_of_derives move
        have exposedToTarget := moveSound.symm.trans equivalent
        simpa [List.append_assoc] using exposedToTarget
      have exposedLastEqual :
          lastOccurrenceSequence
              ((pre ++ [selected]) ++ source.erase selected ++ sourcePost) =
            lastOccurrenceSequence
              ((pre ++ [selected]) ++ targetTail ++ targetPost) := by
        have movePreservesLast :=
          lastOccurrenceSequence_eq_of_derives move
        have exposedToTarget := movePreservesLast.symm.trans lastEqual
        simpa [List.append_assoc] using exposedToTarget
      have rest :=
        listDerivesQuadraticBlockPermutationAgainst
          targetTail (source.erase selected) (pre ++ [selected])
          sourcePost targetPost erasedPermutation
          erasedSourceQuadratic erasedTargetQuadratic exposedEquivalent
          exposedLastEqual
      exact move.trans <| by
        simpa [List.append_assoc] using rest
termination_by
  target _ _ _ _ => target.length

/-- Same-suffix form used by the six-case block-permutation obligation. -/
theorem listDerivesQuadraticBlockPermutation
    (target source pre post : List Nat)
    (permutation : source.Perm target)
    (quadratic :
      ∀ letter, letter ∈ source →
        (pre ++ source ++ post).count letter = 2)
    (equivalent :
      M20ListEquivalent
        (pre ++ source ++ post)
        (pre ++ target ++ post))
    (lastEqual :
      lastOccurrenceSequence (pre ++ source ++ post) =
        lastOccurrenceSequence (pre ++ target ++ post)) :
    S5_107.ListDerives basis
      (pre ++ source ++ post)
      (pre ++ target ++ post) := by
  have contextPermutation :
      (pre ++ source ++ post).Perm (pre ++ target ++ post) :=
    List.Perm.append
      (List.Perm.append (List.Perm.refl pre) permutation)
      (List.Perm.refl post)
  have targetQuadratic :
      ∀ letter, letter ∈ target →
        (pre ++ target ++ post).count letter = 2 := by
    intro letter targetMember
    have sourceMember : letter ∈ source :=
      permutation.mem_iff.mpr targetMember
    calc
      (pre ++ target ++ post).count letter =
          (pre ++ source ++ post).count letter :=
        (contextPermutation.count letter).symm
      _ = 2 := quadratic letter sourceMember
  exact
    listDerivesQuadraticBlockPermutationAgainst
      target source pre post post permutation quadratic targetQuadratic
      equivalent lastEqual




/-! ## Last-occurrence-restricted segmentation -/


/-! ## Globally singleton projections -/

/-- Retain the letters of `letters` that are globally singleton in `whole`. -/
private def simpleProjection
    (whole letters : List Nat) : List Nat :=
  letters.filter fun letter => decide (whole.count letter = 1)

private theorem filter_filter_ne_comm
    (keep : Nat → Bool) (selected : Nat)
    (letters : List Nat) :
    (letters.filter keep).filter
        (fun letter => decide (letter ≠ selected)) =
      (letters.filter
        (fun letter => decide (letter ≠ selected))).filter keep := by
  rw [List.filter_filter, List.filter_filter]
  apply List.filter_congr
  intro letter _
  exact Bool.and_comm _ _

private theorem filter_ne_then_keep_of_drop
    (keep : Nat → Bool) (selected : Nat)
    (dropped : ¬keep selected)
    (letters : List Nat) :
    (letters.filter
        (fun letter => decide (letter ≠ selected))).filter keep =
      letters.filter keep := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro letter _
  by_cases equal : letter = selected
  · subst letter
    simp [dropped]
  · simp [equal]

private theorem firstOccurrenceSequence_filter
    (keep : Nat → Bool) :
    ∀ letters : List Nat,
      firstOccurrenceSequence (letters.filter keep) =
        (firstOccurrenceSequence letters).filter keep
  | [] => rfl
  | letter :: rest => by
      by_cases kept : keep letter
      · rw [List.filter_cons, if_pos kept,
          firstOccurrenceSequence, firstOccurrenceSequence,
          firstOccurrenceSequence_filter keep rest,
          List.filter_cons, if_pos kept]
        exact congrArg (List.cons letter) <|
          filter_filter_ne_comm keep letter
            (firstOccurrenceSequence rest)
      · rw [List.filter_cons, if_neg kept,
          firstOccurrenceSequence_filter keep rest,
          firstOccurrenceSequence,
          List.filter_cons, if_neg kept]
        exact
          (filter_ne_then_keep_of_drop
            keep letter kept (firstOccurrenceSequence rest)).symm

private theorem firstOccurrenceSequence_eq_self_of_nodup
    {letters : List Nat} (nodup : letters.Nodup) :
    firstOccurrenceSequence letters = letters := by
  induction letters with
  | nil => rfl
  | cons letter rest induction =>
      have data := List.nodup_cons.mp nodup
      rw [firstOccurrenceSequence, induction data.2]
      congr 1
      apply List.filter_eq_self.mpr
      intro next member
      exact decide_eq_true <| by
        intro equal
        subst next
        exact data.1 member

private theorem nodup_of_count_le_one
    {letters : List Nat}
    (bounded : ∀ letter, letters.count letter ≤ 1) :
    letters.Nodup := by
  induction letters with
  | nil => simp
  | cons first rest induction =>
      simp only [List.nodup_cons]
      constructor
      · intro member
        have positive : 1 ≤ rest.count first :=
          List.count_pos_iff.mpr member
        have bound := bounded first
        simp only [List.count_cons_self] at bound
        omega
      · apply induction
        intro letter
        have bound := bounded letter
        by_cases equal : first = letter
        · subst first
          simp only [List.count_cons_self] at bound
          omega
        · simpa [equal] using bound

private theorem simpleProjection_self_nodup (letters : List Nat) :
    (simpleProjection letters letters).Nodup := by
  apply nodup_of_count_le_one
  intro letter
  by_cases simple : letters.count letter = 1
  · exact Nat.le_trans
      (List.filter_sublist.count_le letter) (by omega)
  · have absent : letter ∉ simpleProjection letters letters := by
      intro member
      have kept := (List.mem_filter.mp member).2
      simp [simpleProjection, simple] at kept
    rw [List.count_eq_zero.mpr absent]
    omega

private theorem simpleProjection_self_eq_firstOccurrenceFilter
    (letters : List Nat) :
    simpleProjection letters letters =
      (firstOccurrenceSequence letters).filter
        (fun letter => decide (letters.count letter = 1)) := by
  calc
    simpleProjection letters letters =
        firstOccurrenceSequence (simpleProjection letters letters) :=
      (firstOccurrenceSequence_eq_self_of_nodup
        (simpleProjection_self_nodup letters)).symm
    _ = _ := by
      simpa [simpleProjection] using
        firstOccurrenceSequence_filter
          (fun letter => decide (letters.count letter = 1)) letters

private theorem simpleProjection_congr
    {leftWhole rightWhole : List Nat}
    (counts : ∀ letter, leftWhole.count letter = rightWhole.count letter)
    (letters : List Nat) :
    simpleProjection leftWhole letters =
      simpleProjection rightWhole letters := by
  unfold simpleProjection
  apply List.filter_congr
  intro letter _
  simp [counts letter]

private theorem simpleProjection_cons_split
    (pre tail : List Nat) (separator : Nat) (remaining : List Nat)
    (projection :
      simpleProjection (pre ++ tail) tail = separator :: remaining) :
    ∃ before after,
      tail = before ++ separator :: after ∧
      (∀ letter, letter ∈ before →
        (pre ++ tail).count letter ≠ 1) ∧
      simpleProjection (pre ++ tail) after = remaining ∧
      (pre ++ tail).count separator = 1 := by
  have separatorProjected :
      separator ∈ simpleProjection (pre ++ tail) tail := by
    rw [projection]
    simp
  have separatorData := List.mem_filter.mp separatorProjected
  have separatorInTail : separator ∈ tail := separatorData.1
  have separatorSimple : (pre ++ tail).count separator = 1 := by
    simpa [simpleProjection] using separatorData.2
  obtain ⟨before, after, tailShape⟩ :=
    List.append_of_mem separatorInTail
  have separatorSimpleShaped :
      (pre ++ (before ++ separator :: after)).count separator = 1 := by
    simpa [tailShape] using separatorSimple
  have separatorNotBefore : separator ∉ before := by
    intro member
    have positive : 1 ≤ before.count separator :=
      List.one_le_count_iff.mpr member
    simp only [List.count_append, List.count_cons_self] at separatorSimpleShaped
    omega
  have expanded :
      simpleProjection (pre ++ tail) before ++
        separator :: simpleProjection (pre ++ tail) after =
      separator :: remaining := by
    have expandedProjection := projection
    rw [tailShape] at expandedProjection
    unfold simpleProjection at expandedProjection
    rw [List.filter_append] at expandedProjection
    have separatorKept :
        decide
            ((pre ++ (before ++ separator :: after)).count separator = 1) =
          true := by
      simp [separatorSimpleShaped]
    rw [List.filter_cons, if_pos separatorKept] at expandedProjection
    simpa [simpleProjection, tailShape, List.append_assoc] using
      expandedProjection
  have beforeEmpty :
      simpleProjection (pre ++ tail) before = [] := by
    cases beforeProjection : simpleProjection (pre ++ tail) before with
    | nil => rfl
    | cons first rest =>
        rw [beforeProjection] at expanded
        simp only [List.cons_append] at expanded
        have firstEqual : first = separator := by
          injection expanded
        subst first
        have separatorProjectedBefore :
            separator ∈ simpleProjection (pre ++ tail) before := by
          rw [beforeProjection]
          simp
        have separatorBefore : separator ∈ before :=
          (List.mem_filter.mp separatorProjectedBefore).1
        exact False.elim (separatorNotBefore separatorBefore)
  have afterProjection :
      simpleProjection (pre ++ tail) after = remaining := by
    rw [beforeEmpty] at expanded
    simpa using expanded
  have beforeNonlinear :
      ∀ letter, letter ∈ before →
        (pre ++ tail).count letter ≠ 1 := by
    intro letter member countOne
    have projected :
        letter ∈ simpleProjection (pre ++ tail) before :=
      List.mem_filter.mpr ⟨member, by simp [countOne]⟩
    rw [beforeEmpty] at projected
    simp at projected
  exact
    ⟨before, after, tailShape, beforeNonlinear,
      afterProjection, separatorSimple⟩

private theorem nonlinear_of_simpleProjection_nil
    (whole letters : List Nat)
    (projection : simpleProjection whole letters = []) :
    ∀ letter, letter ∈ letters → whole.count letter ≠ 1 := by
  intro letter member countOne
  have projected : letter ∈ simpleProjection whole letters :=
    List.mem_filter.mpr ⟨member, by simp [countOne]⟩
  rw [projection] at projected
  simp at projected

/-! ## Complete precedence orders the singleton projection -/

private def segmentationPairKeep (x y value : Nat) : Bool :=
  value == x || value == y

private def pairProjection
    (letters : List Nat) (x y : Nat) : List Nat :=
  letters.filter (segmentationPairKeep x y)

private theorem count_filter_of_kept
    (letters : List Nat) (keep : Nat → Bool) (letter : Nat)
    (kept : keep letter = true) :
    (letters.filter keep).count letter = letters.count letter := by
  induction letters with
  | nil => simp
  | cons first rest induction =>
      by_cases equality : first = letter
      · subst first
        simp [kept, induction]
      · by_cases firstKept : keep first
        · simp [firstKept, equality, induction]
        · simp [firstKept, equality, induction]

private theorem segmentationPairKeep_member
    {letters : List Nat} {x y value : Nat}
    (member : value ∈ letters.filter (segmentationPairKeep x y)) :
    value = x ∨ value = y := by
  have kept := (List.mem_filter.mp member).2
  simpa [segmentationPairKeep] using kept

private theorem length_eq_pair_counts
    {x y : Nat} (different : x ≠ y) :
    ∀ letters : List Nat,
      (∀ value, value ∈ letters → value = x ∨ value = y) →
      letters.length = letters.count x + letters.count y
  | [], _ => by simp
  | value :: rest, onlyPair => by
      have headPair := onlyPair value (by simp)
      have restPair :
          ∀ selected, selected ∈ rest →
            selected = x ∨ selected = y := by
        intro selected member
        exact onlyPair selected (by simp [member])
      have induction :=
        length_eq_pair_counts different rest restPair
      rcases headPair with rfl | rfl
      · simp [different, induction]
        omega
      · simp [Ne.symm different, induction]
        omega

private theorem pairList_shape_of_counts_one
    (letters : List Nat) {x y : Nat}
    (different : x ≠ y)
    (xCount : letters.count x = 1)
    (yCount : letters.count y = 1)
    (onlyPair :
      ∀ value, value ∈ letters → value = x ∨ value = y) :
    letters = [x, y] ∨ letters = [y, x] := by
  have lengthTwo : letters.length = 2 := by
    rw [length_eq_pair_counts different letters onlyPair,
      xCount, yCount]
  rcases letters with _ | ⟨head, rest⟩
  · simp at lengthTwo
  rcases rest with _ | ⟨next, rest⟩
  · simp at lengthTwo
  have restEmpty : rest = [] := by
    apply List.eq_nil_of_length_eq_zero
    simpa using lengthTwo
  subst rest
  have headPair := onlyPair head (by simp)
  have nextPair := onlyPair next (by simp)
  rcases headPair with rfl | rfl
  · rcases nextPair with rfl | rfl
    · simp at xCount
    · exact Or.inl rfl
  · rcases nextPair with rfl | rfl
    · exact Or.inr rfl
    · simp at yCount

private theorem pairProjection_shape
    (letters : List Nat) {x y : Nat}
    (different : x ≠ y)
    (xSimple : letters.count x = 1)
    (ySimple : letters.count y = 1) :
    pairProjection letters x y = [x, y] ∨
      pairProjection letters x y = [y, x] := by
  apply pairList_shape_of_counts_one
  · exact different
  · unfold pairProjection
    rw [count_filter_of_kept letters (segmentationPairKeep x y) x]
    · exact xSimple
    · simp [segmentationPairKeep]
  · unfold pairProjection
    rw [count_filter_of_kept letters (segmentationPairKeep x y) y]
    · exact ySimple
    · simp [segmentationPairKeep]
  · intro value member
    exact segmentationPairKeep_member member

private def segmentationPrecedenceStep
    (x y : Nat) (state : PrecedenceState) (letter : Nat) :
    PrecedenceState :=
  if letter = x then
    match state with
    | .neither => .onlyX
    | .onlyX => .onlyX
    | .onlyY | .ordered | .violated => .violated
  else if letter = y then
    match state with
    | .neither => .onlyY
    | .onlyX => .ordered
    | .onlyY => .onlyY
    | .ordered => .ordered
    | .violated => .violated
  else state

private theorem precedenceScanList_eq_segmentationFold
    (letters : List Nat) (x y : Nat) :
    precedenceScanList letters x y =
      letters.foldl (segmentationPrecedenceStep x y) .neither := by
  rfl

private theorem segmentationPrecedenceFold_filter
    (x y : Nat) :
    ∀ (letters : List Nat) (initial : PrecedenceState),
      letters.foldl (segmentationPrecedenceStep x y) initial =
        (letters.filter (segmentationPairKeep x y)).foldl
          (segmentationPrecedenceStep x y) initial
  | [], _ => rfl
  | value :: rest, initial => by
      by_cases isX : value = x
      · subst value
        have induction :=
          segmentationPrecedenceFold_filter x y rest
            (segmentationPrecedenceStep x y initial x)
        simpa [segmentationPairKeep] using induction
      · by_cases isY : value = y
        · subst value
          have induction :=
            segmentationPrecedenceFold_filter x y rest
              (segmentationPrecedenceStep x y initial y)
          simpa [segmentationPairKeep, isX] using induction
        · have induction :=
            segmentationPrecedenceFold_filter x y rest initial
          simpa [segmentationPairKeep, segmentationPrecedenceStep, isX, isY]
            using induction

private theorem precedenceScanList_eq_pairProjectionFold
    (letters : List Nat) (x y : Nat) :
    precedenceScanList letters x y =
      (pairProjection letters x y).foldl
        (segmentationPrecedenceStep x y) .neither := by
  rw [precedenceScanList_eq_segmentationFold]
  unfold pairProjection
  exact segmentationPrecedenceFold_filter x y letters .neither

private theorem completePrecedence_iff_pairProjection_head
    (letters : List Nat) {x y : Nat}
    (different : x ≠ y)
    (xSimple : letters.count x = 1)
    (ySimple : letters.count y = 1) :
    CompletePrecedenceList letters x y ↔
      (pairProjection letters x y).head? = some x := by
  unfold CompletePrecedenceList
  rw [precedenceScanList_eq_pairProjectionFold]
  rcases pairProjection_shape letters different xSimple ySimple with
      shape | shape <;>
    rw [shape] <;>
    simp [segmentationPrecedenceStep, different, Ne.symm different]

private theorem simpleProjection_pairProjection
    (letters : List Nat) {x y : Nat}
    (different : x ≠ y)
    (xSimple : letters.count x = 1)
    (ySimple : letters.count y = 1) :
    (simpleProjection letters letters).filter (segmentationPairKeep x y) =
      pairProjection letters x y := by
  unfold simpleProjection pairProjection
  rw [List.filter_filter]
  apply List.filter_congr
  intro value _
  by_cases isX : value = x
  · subst value
    simp [segmentationPairKeep, xSimple]
  · by_cases isY : value = y
    · subst value
      simp [segmentationPairKeep, isX, ySimple]
    · simp [segmentationPairKeep, isX, isY]

private theorem nodup_eq_of_pairProjection_head :
    ∀ {left right : List Nat},
      left.Nodup →
      right.Nodup →
      (∀ value, value ∈ left ↔ value ∈ right) →
      (∀ x y,
        x ≠ y →
        x ∈ left →
        y ∈ left →
        (left.filter (segmentationPairKeep x y)).head? =
          (right.filter (segmentationPairKeep x y)).head?) →
      left = right
  | [], [], _, _, _, _ => rfl
  | [], head :: tail, _, _, sameMembers, _ => by
      have : head ∈ ([] : List Nat) :=
        (sameMembers head).mpr (by simp)
      simp at this
  | head :: tail, [], _, _, sameMembers, _ => by
      have : head ∈ ([] : List Nat) :=
        (sameMembers head).mp (by simp)
      simp at this
  | leftHead :: leftTail, rightHead :: rightTail,
      leftNodup, rightNodup, sameMembers, sameHeads => by
      simp only [List.nodup_cons] at leftNodup rightNodup
      have headsEqual : leftHead = rightHead := by
        apply Decidable.byContradiction
        intro different
        have leftHeadMember :
            leftHead ∈ leftHead :: leftTail := by simp
        have rightHeadMember :
            rightHead ∈ leftHead :: leftTail :=
          (sameMembers rightHead).mpr (by simp)
        have pairHeads :=
          sameHeads leftHead rightHead different
            leftHeadMember rightHeadMember
        simp [segmentationPairKeep, different] at pairHeads
      subst rightHead
      have tailMembers :
          ∀ value, value ∈ leftTail ↔ value ∈ rightTail := by
        intro value
        constructor
        · intro member
          have inRight :
              value ∈ leftHead :: rightTail :=
            (sameMembers value).mp (by simp [member])
          rcases List.mem_cons.mp inRight with equality | tailMember
          · subst value
            exact False.elim (leftNodup.1 member)
          · exact tailMember
        · intro member
          have inLeft :
              value ∈ leftHead :: leftTail :=
            (sameMembers value).mpr (by simp [member])
          rcases List.mem_cons.mp inLeft with equality | tailMember
          · subst value
            exact False.elim (rightNodup.1 member)
          · exact tailMember
      have tailHeads :
          ∀ x y,
            x ≠ y →
            x ∈ leftTail →
            y ∈ leftTail →
            (leftTail.filter (segmentationPairKeep x y)).head? =
              (rightTail.filter (segmentationPairKeep x y)).head? := by
        intro x y different xMember yMember
        have xNotHead : x ≠ leftHead := by
          intro equality
          subst x
          exact leftNodup.1 xMember
        have yNotHead : y ≠ leftHead := by
          intro equality
          subst y
          exact leftNodup.1 yMember
        have inherited :=
          sameHeads x y different
            (by simp [xMember]) (by simp [yMember])
        simpa [segmentationPairKeep, Ne.symm xNotHead,
          Ne.symm yNotHead] using inherited
      have tailEqual :=
        nodup_eq_of_pairProjection_head
          leftNodup.2 rightNodup.2 tailMembers tailHeads
      rw [tailEqual]

private theorem simpleProjection_eq_of_counts_precedence
    {left right : List Nat}
    (counts : ∀ letter, left.count letter = right.count letter)
    (precedence :
      ∀ x y,
        CompletePrecedenceList left x y ↔
          CompletePrecedenceList right x y) :
    simpleProjection left left = simpleProjection right right := by
  apply nodup_eq_of_pairProjection_head
  · exact simpleProjection_self_nodup left
  · exact simpleProjection_self_nodup right
  · intro letter
    simp only [simpleProjection, List.mem_filter]
    constructor
    · rintro ⟨member, simple⟩
      refine ⟨?_, ?_⟩
      · exact List.count_pos_iff.mp <| by
          rw [← counts letter]
          exact List.count_pos_iff.mpr member
      · simpa [counts letter] using simple
    · rintro ⟨member, simple⟩
      refine ⟨?_, ?_⟩
      · exact List.count_pos_iff.mp <| by
          rw [counts letter]
          exact List.count_pos_iff.mpr member
      · simpa [counts letter] using simple
  · intro x y different xMember yMember
    have leftX : left.count x = 1 := by
      have kept := (List.mem_filter.mp xMember).2
      simpa [simpleProjection] using kept
    have leftY : left.count y = 1 := by
      have kept := (List.mem_filter.mp yMember).2
      simpa [simpleProjection] using kept
    have rightX : right.count x = 1 := by
      rw [← counts x]
      exact leftX
    have rightY : right.count y = 1 := by
      rw [← counts y]
      exact leftY
    rw [simpleProjection_pairProjection left different leftX leftY,
      simpleProjection_pairProjection right different rightX rightY]
    rcases pairProjection_shape left different leftX leftY with
        leftXY | leftYX <;>
      rcases pairProjection_shape right different rightX rightY with
        rightXY | rightYX
    · simp [leftXY, rightXY]
    · have leftPrecedes : CompletePrecedenceList left x y :=
        (completePrecedence_iff_pairProjection_head
          left different leftX leftY).2 <| by
            simp [leftXY]
      have rightPrecedes := (precedence x y).1 leftPrecedes
      have rightHead :=
        (completePrecedence_iff_pairProjection_head
          right different rightX rightY).1 rightPrecedes
      rw [rightYX] at rightHead
      have equal : y = x := Option.some.inj rightHead
      exact False.elim (different equal.symm)
    · have rightPrecedes : CompletePrecedenceList right x y :=
        (completePrecedence_iff_pairProjection_head
          right different rightX rightY).2 <| by
            simp [rightXY]
      have leftPrecedes := (precedence x y).2 rightPrecedes
      have leftHead :=
        (completePrecedence_iff_pairProjection_head
          left different leftX leftY).1 leftPrecedes
      rw [leftYX] at leftHead
      have equal : y = x := Option.some.inj leftHead
      exact False.elim (different equal.symm)
    · simp [leftYX, rightYX]

/-! ## Prefix counts at a singleton separator -/

private def segmentationPairFree
    (x y : Nat) (letters : List Nat) : Prop :=
  x ∉ letters ∧ y ∉ letters

private theorem segmentationPrecedenceFold_pairFree
    (x y : Nat) :
    ∀ (letters : List Nat) (state : PrecedenceState),
      segmentationPairFree x y letters →
      letters.foldl (segmentationPrecedenceStep x y) state = state
  | [], _, _ => rfl
  | letter :: rest, state, free => by
      have letterNeX : letter ≠ x := by
        intro equal
        subst letter
        exact free.1 (List.Mem.head rest)
      have letterNeY : letter ≠ y := by
        intro equal
        subst letter
        exact free.2 (List.Mem.head rest)
      have restFree : segmentationPairFree x y rest :=
        ⟨fun member => free.1 (List.Mem.tail letter member),
          fun member => free.2 (List.Mem.tail letter member)⟩
      simp only [List.foldl_cons]
      rw [show segmentationPrecedenceStep x y state letter = state by
        simp [segmentationPrecedenceStep, letterNeX, letterNeY]]
      exact
        segmentationPrecedenceFold_pairFree x y rest state restFree

private theorem segmentationPrecedenceFold_onlyX_of_y_absent
    (x y : Nat) :
    ∀ letters : List Nat,
      y ∉ letters →
      letters.foldl (segmentationPrecedenceStep x y) .onlyX = .onlyX
  | [], _ => rfl
  | letter :: rest, absent => by
      have letterNeY : letter ≠ y := by
        intro equal
        subst letter
        exact absent (List.Mem.head rest)
      have restAbsent : y ∉ rest :=
        fun member => absent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      rw [show segmentationPrecedenceStep x y .onlyX letter = .onlyX by
        by_cases isX : letter = x
        · simp [segmentationPrecedenceStep, isX]
        · simp [segmentationPrecedenceStep, isX, letterNeY]]
      exact
        segmentationPrecedenceFold_onlyX_of_y_absent
          x y rest restAbsent

private theorem segmentationPrecedenceFold_onlyY_of_x_absent
    (x y : Nat) :
    ∀ letters : List Nat,
      x ∉ letters →
      letters.foldl (segmentationPrecedenceStep x y) .onlyY = .onlyY
  | [], _ => rfl
  | letter :: rest, absent => by
      have letterNeX : letter ≠ x := by
        intro equal
        subst letter
        exact absent (List.Mem.head rest)
      have restAbsent : x ∉ rest :=
        fun member => absent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      rw [show segmentationPrecedenceStep x y .onlyY letter = .onlyY by
        simp [segmentationPrecedenceStep, letterNeX]]
      exact
        segmentationPrecedenceFold_onlyY_of_x_absent
          x y rest restAbsent

private theorem segmentationPrecedenceFold_ordered_of_x_absent
    (x y : Nat) :
    ∀ letters : List Nat,
      x ∉ letters →
      letters.foldl (segmentationPrecedenceStep x y) .ordered = .ordered
  | [], _ => rfl
  | letter :: rest, absent => by
      have letterNeX : letter ≠ x := by
        intro equal
        subst letter
        exact absent (List.Mem.head rest)
      have restAbsent : x ∉ rest :=
        fun member => absent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      rw [show segmentationPrecedenceStep x y .ordered letter = .ordered by
        simp [segmentationPrecedenceStep, letterNeX]]
      exact
        segmentationPrecedenceFold_ordered_of_x_absent
          x y rest restAbsent

private theorem segmentationPrecedenceFold_violated
    (x y : Nat) :
    ∀ letters : List Nat,
      letters.foldl (segmentationPrecedenceStep x y) .violated = .violated
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      rw [show segmentationPrecedenceStep x y .violated letter = .violated by
        simp [segmentationPrecedenceStep]]
      exact segmentationPrecedenceFold_violated x y rest

private theorem
    segmentationPrecedenceFold_violated_of_x_mem_from_onlyY
    (x y : Nat) :
    ∀ letters : List Nat,
      x ∈ letters →
      letters.foldl (segmentationPrecedenceStep x y) .onlyY = .violated
  | [], member => by simp at member
  | letter :: rest, member => by
      simp only [List.foldl_cons]
      by_cases isX : letter = x
      · rw [show segmentationPrecedenceStep x y .onlyY letter =
            .violated by
          simp [segmentationPrecedenceStep, isX]]
        exact segmentationPrecedenceFold_violated x y rest
      · have restMember : x ∈ rest := by
          exact
            (List.mem_cons.mp member).resolve_left (Ne.symm isX)
        rw [show segmentationPrecedenceStep x y .onlyY letter = .onlyY by
          simp [segmentationPrecedenceStep, isX]]
        exact
          segmentationPrecedenceFold_violated_of_x_mem_from_onlyY
            x y rest restMember

private theorem
    segmentationPrecedenceFold_violated_of_x_mem_from_ordered
    (x y : Nat) :
    ∀ letters : List Nat,
      x ∈ letters →
      letters.foldl (segmentationPrecedenceStep x y) .ordered = .violated
  | [], member => by simp at member
  | letter :: rest, member => by
      simp only [List.foldl_cons]
      by_cases isX : letter = x
      · rw [show segmentationPrecedenceStep x y .ordered letter =
            .violated by
          simp [segmentationPrecedenceStep, isX]]
        exact segmentationPrecedenceFold_violated x y rest
      · have restMember : x ∈ rest := by
          exact
            (List.mem_cons.mp member).resolve_left (Ne.symm isX)
        rw [show segmentationPrecedenceStep x y .ordered letter = .ordered by
          simp [segmentationPrecedenceStep, isX]]
        exact
          segmentationPrecedenceFold_violated_of_x_mem_from_ordered
            x y rest restMember

private theorem segmentationPrecedenceFold_onlyX_of_x_mem_y_absent
    (x y : Nat) :
    ∀ letters : List Nat,
      x ∈ letters →
      y ∉ letters →
      letters.foldl (segmentationPrecedenceStep x y) .neither = .onlyX
  | [], member, _ => by simp at member
  | letter :: rest, xMember, yAbsent => by
      have letterNeY : letter ≠ y := by
        intro equal
        subst letter
        exact yAbsent (List.Mem.head rest)
      have restYAbsent : y ∉ rest :=
        fun member => yAbsent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      by_cases isX : letter = x
      · rw [show segmentationPrecedenceStep x y .neither letter = .onlyX by
          simp [segmentationPrecedenceStep, isX]]
        exact
          segmentationPrecedenceFold_onlyX_of_y_absent
            x y rest restYAbsent
      · have restXMember : x ∈ rest := by
          exact
            (List.mem_cons.mp xMember).resolve_left (Ne.symm isX)
        rw [show segmentationPrecedenceStep x y .neither letter = .neither by
          simp [segmentationPrecedenceStep, isX, letterNeY]]
        exact
          segmentationPrecedenceFold_onlyX_of_x_mem_y_absent
            x y rest restXMember restYAbsent

private theorem segmentationPrecedenceFold_onlyY_of_x_absent_y_mem
    (x y : Nat) :
    ∀ letters : List Nat,
      x ∉ letters →
      y ∈ letters →
      letters.foldl (segmentationPrecedenceStep x y) .neither = .onlyY
  | [], _, member => by simp at member
  | letter :: rest, xAbsent, yMember => by
      have letterNeX : letter ≠ x := by
        intro equal
        subst letter
        exact xAbsent (List.Mem.head rest)
      have restXAbsent : x ∉ rest :=
        fun member => xAbsent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      by_cases isY : letter = y
      · have yNeX : y ≠ x := by
          intro equal
          exact letterNeX (isY.trans equal)
        rw [show segmentationPrecedenceStep x y .neither letter = .onlyY by
          simp [segmentationPrecedenceStep, isY, yNeX]]
        exact
          segmentationPrecedenceFold_onlyY_of_x_absent
            x y rest restXAbsent
      · have restYMember : y ∈ rest := by
          exact
            (List.mem_cons.mp yMember).resolve_left (Ne.symm isY)
        rw [show segmentationPrecedenceStep x y .neither letter = .neither by
          simp [segmentationPrecedenceStep, letterNeX, isY]]
        exact
          segmentationPrecedenceFold_onlyY_of_x_absent_y_mem
            x y rest restXAbsent restYMember

private theorem segmentationPrecedenceFold_ordered_of_x_absent_y_mem
    (x y : Nat) :
    ∀ letters : List Nat,
      x ∉ letters →
      y ∈ letters →
      letters.foldl (segmentationPrecedenceStep x y) .onlyX = .ordered
  | [], _, member => by simp at member
  | letter :: rest, xAbsent, yMember => by
      have letterNeX : letter ≠ x := by
        intro equal
        subst letter
        exact xAbsent (List.Mem.head rest)
      have restXAbsent : x ∉ rest :=
        fun member => xAbsent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      by_cases isY : letter = y
      · have yNeX : y ≠ x := by
          intro equal
          exact letterNeX (isY.trans equal)
        rw [show segmentationPrecedenceStep x y .onlyX letter = .ordered by
          simp [segmentationPrecedenceStep, isY, yNeX]]
        exact
          segmentationPrecedenceFold_ordered_of_x_absent
            x y rest restXAbsent
      · have restYMember : y ∈ rest := by
          exact
            (List.mem_cons.mp yMember).resolve_left (Ne.symm isY)
        rw [show segmentationPrecedenceStep x y .onlyX letter = .onlyX by
          simp [segmentationPrecedenceStep, letterNeX, isY]]
        exact
          segmentationPrecedenceFold_ordered_of_x_absent_y_mem
            x y rest restXAbsent restYMember

private theorem precedenceScan_ordered_before_separator
    {x separator : Nat} (different : x ≠ separator)
    (before after : List Nat)
    (xInBefore : x ∈ before)
    (separatorAbsentBefore : separator ∉ before)
    (xAbsentAfter : x ∉ after) :
    precedenceScanList (before ++ separator :: after) x separator =
      .ordered := by
  rw [precedenceScanList_eq_segmentationFold]
  rw [List.foldl_append]
  rw [segmentationPrecedenceFold_onlyX_of_x_mem_y_absent
    x separator before xInBefore separatorAbsentBefore]
  simp only [List.foldl_cons]
  rw [show segmentationPrecedenceStep x separator .onlyX separator =
      .ordered by
    simp [segmentationPrecedenceStep, Ne.symm different]]
  exact
    segmentationPrecedenceFold_ordered_of_x_absent
      x separator after xAbsentAfter

private theorem precedenceScan_ordered_after_separator
    {x separator : Nat} (different : x ≠ separator)
    (before after : List Nat)
    (xAbsentBefore : x ∉ before)
    (separatorAbsentBefore : separator ∉ before)
    (xInAfter : x ∈ after)
    (separatorAbsentAfter : separator ∉ after) :
    precedenceScanList (before ++ separator :: after) separator x =
      .ordered := by
  rw [precedenceScanList_eq_segmentationFold]
  rw [List.foldl_append]
  rw [segmentationPrecedenceFold_pairFree separator x before .neither
    ⟨separatorAbsentBefore, xAbsentBefore⟩]
  simp only [List.foldl_cons]
  rw [show segmentationPrecedenceStep separator x .neither separator =
      .onlyX by
    simp [segmentationPrecedenceStep]]
  exact
    segmentationPrecedenceFold_ordered_of_x_absent_y_mem
      separator x after separatorAbsentAfter xInAfter

private theorem precedenceScan_violated_after_inversion
    {x separator : Nat} (different : x ≠ separator)
    (before after : List Nat)
    (separatorAbsentBefore : separator ∉ before)
    (xInAfter : x ∈ after) :
    precedenceScanList (before ++ separator :: after) x separator =
      .violated := by
  rw [precedenceScanList_eq_segmentationFold]
  rw [List.foldl_append]
  by_cases xInBefore : x ∈ before
  · rw [segmentationPrecedenceFold_onlyX_of_x_mem_y_absent
      x separator before xInBefore separatorAbsentBefore]
    simp only [List.foldl_cons]
    rw [show segmentationPrecedenceStep x separator .onlyX separator =
        .ordered by
      simp [segmentationPrecedenceStep, Ne.symm different]]
    exact
      segmentationPrecedenceFold_violated_of_x_mem_from_ordered
        x separator after xInAfter
  · rw [segmentationPrecedenceFold_pairFree x separator before .neither
      ⟨xInBefore, separatorAbsentBefore⟩]
    simp only [List.foldl_cons]
    rw [show segmentationPrecedenceStep x separator .neither separator =
        .onlyY by
      simp [segmentationPrecedenceStep, Ne.symm different]]
    exact
      segmentationPrecedenceFold_violated_of_x_mem_from_onlyY
        x separator after xInAfter

private theorem precedenceScan_violated_before_separator
    {x separator : Nat} (different : x ≠ separator)
    (before after : List Nat)
    (xInBefore : x ∈ before)
    (separatorAbsentBefore : separator ∉ before) :
    precedenceScanList (before ++ separator :: after) separator x =
      .violated := by
  rw [precedenceScanList_eq_segmentationFold]
  rw [List.foldl_append]
  rw [segmentationPrecedenceFold_onlyY_of_x_absent_y_mem
    separator x before separatorAbsentBefore xInBefore]
  simp only [List.foldl_cons]
  rw [show segmentationPrecedenceStep separator x .onlyY separator =
      .violated by
    simp [segmentationPrecedenceStep]]
  exact segmentationPrecedenceFold_violated separator x after

private theorem segmentationPrecedenceState_violated_ne_ordered :
    (PrecedenceState.violated : PrecedenceState) ≠ .ordered := by
  decide

private theorem completePrecedence_before_separator_iff
    {x separator : Nat} (different : x ≠ separator)
    (before after : List Nat)
    (xQuadratic : (before ++ separator :: after).count x = 2)
    (separatorSimple :
      (before ++ separator :: after).count separator = 1) :
    CompletePrecedenceList
        (before ++ separator :: after) x separator ↔
      before.count x = 2 := by
  have xSplit := xQuadratic
  simp only [List.count_append, List.count_cons] at xSplit
  simp [Ne.symm different] at xSplit
  have separatorSplit := separatorSimple
  simp only [List.count_append, List.count_cons_self] at separatorSplit
  have separatorBeforeZero : before.count separator = 0 := by omega
  have separatorAfterZero : after.count separator = 0 := by omega
  have separatorAbsentBefore : separator ∉ before :=
    List.count_eq_zero.mp separatorBeforeZero
  constructor
  · intro complete
    have xAfterZero : after.count x = 0 := by
      apply Decidable.byContradiction
      intro nonzero
      have xInAfter : x ∈ after :=
        List.one_le_count_iff.mp (by omega)
      have violated :=
        precedenceScan_violated_after_inversion
          different before after separatorAbsentBefore xInAfter
      exact segmentationPrecedenceState_violated_ne_ordered
        (violated.symm.trans complete.2)
    omega
  · intro beforeTwo
    have xInBefore : x ∈ before :=
      List.one_le_count_iff.mp (by omega)
    have xAfterZero : after.count x = 0 := by omega
    have xAbsentAfter : x ∉ after :=
      List.count_eq_zero.mp xAfterZero
    exact
      ⟨different,
        precedenceScan_ordered_before_separator
          different before after xInBefore separatorAbsentBefore
            xAbsentAfter⟩

private theorem completePrecedence_after_separator_iff
    {x separator : Nat} (different : x ≠ separator)
    (before after : List Nat)
    (xQuadratic : (before ++ separator :: after).count x = 2)
    (separatorSimple :
      (before ++ separator :: after).count separator = 1) :
    CompletePrecedenceList
        (before ++ separator :: after) separator x ↔
      before.count x = 0 := by
  have xSplit := xQuadratic
  simp only [List.count_append, List.count_cons] at xSplit
  simp [Ne.symm different] at xSplit
  have separatorSplit := separatorSimple
  simp only [List.count_append, List.count_cons_self] at separatorSplit
  have separatorBeforeZero : before.count separator = 0 := by omega
  have separatorAfterZero : after.count separator = 0 := by omega
  have separatorAbsentBefore : separator ∉ before :=
    List.count_eq_zero.mp separatorBeforeZero
  have separatorAbsentAfter : separator ∉ after :=
    List.count_eq_zero.mp separatorAfterZero
  constructor
  · intro complete
    apply Decidable.byContradiction
    intro nonzero
    have xInBefore : x ∈ before :=
      List.one_le_count_iff.mp (by omega)
    have violated :=
      precedenceScan_violated_before_separator
        different before after xInBefore separatorAbsentBefore
    exact segmentationPrecedenceState_violated_ne_ordered
      (violated.symm.trans complete.2)
  · intro beforeZero
    have xAfterTwo : after.count x = 2 := by omega
    have xInAfter : x ∈ after :=
      List.one_le_count_iff.mp (by omega)
    have xAbsentBefore : x ∉ before :=
      List.count_eq_zero.mp beforeZero
    exact
      ⟨Ne.symm different,
        precedenceScan_ordered_after_separator
          different before after xAbsentBefore separatorAbsentBefore
            xInAfter separatorAbsentAfter⟩

private theorem prefixCount_eq_of_completePrecedence
    {x separator : Nat} (different : x ≠ separator)
    (leftPrefix leftRest rightPrefix rightRest : List Nat)
    (leftQuadratic :
      (leftPrefix ++ separator :: leftRest).count x = 2)
    (rightQuadratic :
      (rightPrefix ++ separator :: rightRest).count x = 2)
    (leftSeparator :
      (leftPrefix ++ separator :: leftRest).count separator = 1)
    (rightSeparator :
      (rightPrefix ++ separator :: rightRest).count separator = 1)
    (precedence :
      ∀ a b,
        CompletePrecedenceList
            (leftPrefix ++ separator :: leftRest) a b ↔
          CompletePrecedenceList
            (rightPrefix ++ separator :: rightRest) a b) :
    leftPrefix.count x = rightPrefix.count x := by
  have leftBefore :=
    completePrecedence_before_separator_iff
      different leftPrefix leftRest leftQuadratic leftSeparator
  have rightBefore :=
    completePrecedence_before_separator_iff
      different rightPrefix rightRest rightQuadratic rightSeparator
  have leftAfter :=
    completePrecedence_after_separator_iff
      different leftPrefix leftRest leftQuadratic leftSeparator
  have rightAfter :=
    completePrecedence_after_separator_iff
      different rightPrefix rightRest rightQuadratic rightSeparator
  by_cases before :
      CompletePrecedenceList
        (leftPrefix ++ separator :: leftRest) x separator
  · have rightValue := (precedence x separator).1 before
    rw [leftBefore.mp before, rightBefore.mp rightValue]
  · have rightNotBefore :
        ¬ CompletePrecedenceList
          (rightPrefix ++ separator :: rightRest) x separator := by
      intro rightValue
      exact before ((precedence x separator).2 rightValue)
    by_cases after :
        CompletePrecedenceList
          (leftPrefix ++ separator :: leftRest) separator x
    · have rightValue := (precedence separator x).1 after
      rw [leftAfter.mp after, rightAfter.mp rightValue]
    · have rightNotAfter :
          ¬ CompletePrecedenceList
            (rightPrefix ++ separator :: rightRest) separator x := by
        intro rightValue
        exact after ((precedence separator x).2 rightValue)
      have leftNotTwo : leftPrefix.count x ≠ 2 :=
        fun equal => before (leftBefore.mpr equal)
      have rightNotTwo : rightPrefix.count x ≠ 2 :=
        fun equal => rightNotBefore (rightBefore.mpr equal)
      have leftNotZero : leftPrefix.count x ≠ 0 :=
        fun equal => after (leftAfter.mpr equal)
      have rightNotZero : rightPrefix.count x ≠ 0 :=
        fun equal => rightNotAfter (rightAfter.mpr equal)
      have leftSplit := leftQuadratic
      have rightSplit := rightQuadratic
      simp only [List.count_append, List.count_cons] at leftSplit rightSplit
      simp [Ne.symm different] at leftSplit rightSplit
      omega

/-! ## Recursive segmentation -/

/-- On two-limited lists the capped multiplicity equality is exact. -/
theorem twoLimited_count_eq_of_capped
    {left right : List Nat}
    (leftLimited : UniqueSeparatorTwoLimited left)
    (rightLimited : UniqueSeparatorTwoLimited right)
    (capped :
      ∀ letter,
        Nat.min (left.count letter) 2 =
          Nat.min (right.count letter) 2) :
    ∀ letter, left.count letter = right.count letter := by
  intro letter
  have leftBound := leftLimited letter
  have rightBound := rightLimited letter
  have equal := capped letter
  simpa [Nat.min_eq_left leftBound,
    Nat.min_eq_left rightBound] using equal

private theorem listDerivesSegmented
    (sourceTail targetTail pre : List Nat)
    (sourceLimited :
      UniqueSeparatorTwoLimited (pre ++ sourceTail))
    (targetLimited :
      UniqueSeparatorTwoLimited (pre ++ targetTail))
    (counts :
      ∀ letter,
        (pre ++ sourceTail).count letter =
          (pre ++ targetTail).count letter)
    (simpleEqual :
      simpleProjection (pre ++ sourceTail) sourceTail =
        simpleProjection (pre ++ targetTail) targetTail)
    (precedence :
      ∀ x y,
        CompletePrecedenceList (pre ++ sourceTail) x y ↔
          CompletePrecedenceList (pre ++ targetTail) x y)
    (equivalent :
      M20ListEquivalent
        (pre ++ sourceTail) (pre ++ targetTail))
    (lastEqual :
      lastOccurrenceSequence (pre ++ sourceTail) =
        lastOccurrenceSequence (pre ++ targetTail)) :
    S5_107.ListDerives basis
      (pre ++ sourceTail) (pre ++ targetTail) := by
  cases sourceProjection :
      simpleProjection (pre ++ sourceTail) sourceTail with
  | nil =>
      have targetProjection :
          simpleProjection (pre ++ targetTail) targetTail = [] := by
        rw [← simpleEqual, sourceProjection]
      have sourceNonlinear :=
        nonlinear_of_simpleProjection_nil
          (pre ++ sourceTail) sourceTail sourceProjection
      have targetNonlinear :=
        nonlinear_of_simpleProjection_nil
          (pre ++ targetTail) targetTail targetProjection
      have permutation : sourceTail.Perm targetTail := by
        rw [List.perm_iff_count]
        intro letter
        have total := counts letter
        simp only [List.count_append] at total
        omega
      have sourceQuadratic :
          ∀ letter, letter ∈ sourceTail →
            (pre ++ sourceTail ++ []).count letter = 2 := by
        intro letter member
        have positive : 1 ≤ (pre ++ sourceTail).count letter :=
          List.one_le_count_iff.mpr <| by simp [member]
        have bound := sourceLimited letter
        have notOne := sourceNonlinear letter member
        simpa using
          (show (pre ++ sourceTail).count letter = 2 by omega)
      have targetQuadratic :
          ∀ letter, letter ∈ targetTail →
            (pre ++ targetTail ++ []).count letter = 2 := by
        intro letter member
        have positive : 1 ≤ (pre ++ targetTail).count letter :=
          List.one_le_count_iff.mpr <| by simp [member]
        have bound := targetLimited letter
        have notOne := targetNonlinear letter member
        simpa using
          (show (pre ++ targetTail).count letter = 2 by omega)
      simpa using
        listDerivesQuadraticBlockPermutationAgainst
          targetTail sourceTail pre [] [] permutation
          sourceQuadratic targetQuadratic (by simpa using equivalent)
          (by simpa using lastEqual)
  | cons separator remaining =>
      have targetProjection :
          simpleProjection (pre ++ targetTail) targetTail =
            separator :: remaining := by
        rw [← simpleEqual, sourceProjection]
      obtain
        ⟨sourceBlock, sourceRest, sourceShape,
          sourceBlockNonlinear, sourceRestProjection,
          sourceSeparator⟩ :=
        simpleProjection_cons_split
          pre sourceTail separator remaining sourceProjection
      obtain
        ⟨targetBlock, targetRest, targetShape,
          targetBlockNonlinear, targetRestProjection,
          targetSeparator⟩ :=
        simpleProjection_cons_split
          pre targetTail separator remaining targetProjection
      have sourceRestShorter : sourceRest.length < sourceTail.length := by
        rw [sourceShape]
        simp only [List.length_append, List.length_cons]
        omega
      have sourceLimitedNorm :
          UniqueSeparatorTwoLimited
            (pre ++ sourceBlock ++ separator :: sourceRest) := by
        simpa [sourceShape, List.append_assoc] using sourceLimited
      have targetLimitedNorm :
          UniqueSeparatorTwoLimited
            (pre ++ targetBlock ++ separator :: targetRest) := by
        simpa [targetShape, List.append_assoc] using targetLimited
      have countsNorm :
          ∀ letter,
            (pre ++ sourceBlock ++ separator :: sourceRest).count letter =
              (pre ++ targetBlock ++ separator :: targetRest).count
                letter := by
        intro letter
        simpa [sourceShape, targetShape, List.append_assoc] using
          counts letter
      have precedenceNorm :
          ∀ x y,
            CompletePrecedenceList
                (pre ++ sourceBlock ++ separator :: sourceRest) x y ↔
              CompletePrecedenceList
                (pre ++ targetBlock ++ separator :: targetRest) x y := by
        intro x y
        simpa [sourceShape, targetShape, List.append_assoc] using
          precedence x y
      have equivalentNorm :
          M20ListEquivalent
            (pre ++ sourceBlock ++ separator :: sourceRest)
            (pre ++ targetBlock ++ separator :: targetRest) := by
        simpa [sourceShape, targetShape, List.append_assoc] using equivalent
      have lastEqualNorm :
          lastOccurrenceSequence
              (pre ++ sourceBlock ++ separator :: sourceRest) =
            lastOccurrenceSequence
              (pre ++ targetBlock ++ separator :: targetRest) := by
        simpa [sourceShape, targetShape, List.append_assoc] using lastEqual
      have sourceSeparatorNorm :
          (pre ++ sourceBlock ++ separator :: sourceRest).count
              separator = 1 := by
        simpa [sourceShape, List.append_assoc] using sourceSeparator
      have targetSeparatorNorm :
          (pre ++ targetBlock ++ separator :: targetRest).count
              separator = 1 := by
        simpa [targetShape, List.append_assoc] using targetSeparator
      have blockPermutation : sourceBlock.Perm targetBlock := by
        rw [List.perm_iff_count]
        intro letter
        by_cases sourceMember : letter ∈ sourceBlock
        · have sourcePositive :
              1 ≤
                (pre ++ sourceBlock ++ separator :: sourceRest).count
                  letter :=
            List.one_le_count_iff.mpr <| by simp [sourceMember]
          have sourceBound := sourceLimitedNorm letter
          have sourceNotOne :
              (pre ++ sourceBlock ++ separator :: sourceRest).count
                  letter ≠ 1 := by
            simpa [sourceShape, List.append_assoc] using
              sourceBlockNonlinear letter sourceMember
          have sourceTwo :
              (pre ++ sourceBlock ++ separator :: sourceRest).count
                  letter = 2 := by
            omega
          have targetTwo :
              (pre ++ targetBlock ++ separator :: targetRest).count
                  letter = 2 := by
            rw [← countsNorm letter]
            exact sourceTwo
          have different : letter ≠ separator := by
            intro equal
            subst letter
            omega
          have cut :=
            prefixCount_eq_of_completePrecedence
              different (pre ++ sourceBlock) sourceRest
              (pre ++ targetBlock) targetRest
              (by simpa [List.append_assoc] using sourceTwo)
              (by simpa [List.append_assoc] using targetTwo)
              (by simpa [List.append_assoc] using sourceSeparatorNorm)
              (by simpa [List.append_assoc] using targetSeparatorNorm)
              (by
                intro x y
                simpa [List.append_assoc] using precedenceNorm x y)
          simp only [List.count_append] at cut
          omega
        · by_cases targetMember : letter ∈ targetBlock
          · have targetPositive :
                1 ≤
                  (pre ++ targetBlock ++ separator :: targetRest).count
                    letter :=
              List.one_le_count_iff.mpr <| by simp [targetMember]
            have targetBound := targetLimitedNorm letter
            have targetNotOne :
                (pre ++ targetBlock ++ separator :: targetRest).count
                    letter ≠ 1 := by
              simpa [targetShape, List.append_assoc] using
                targetBlockNonlinear letter targetMember
            have targetTwo :
                (pre ++ targetBlock ++ separator :: targetRest).count
                    letter = 2 := by
              omega
            have sourceTwo :
                (pre ++ sourceBlock ++ separator :: sourceRest).count
                    letter = 2 := by
              rw [countsNorm letter]
              exact targetTwo
            have different : letter ≠ separator := by
              intro equal
              subst letter
              omega
            have cut :=
              prefixCount_eq_of_completePrecedence
                different (pre ++ sourceBlock) sourceRest
                (pre ++ targetBlock) targetRest
                (by simpa [List.append_assoc] using sourceTwo)
                (by simpa [List.append_assoc] using targetTwo)
                (by simpa [List.append_assoc] using sourceSeparatorNorm)
                (by simpa [List.append_assoc] using targetSeparatorNorm)
                (by
                  intro x y
                  simpa [List.append_assoc] using precedenceNorm x y)
            simp only [List.count_append] at cut
            omega
          · rw [List.count_eq_zero.mpr sourceMember,
              List.count_eq_zero.mpr targetMember]
      have sourceQuadratic :
          ∀ letter, letter ∈ sourceBlock →
            (pre ++ sourceBlock ++ separator :: sourceRest).count
                letter = 2 := by
        intro letter member
        have positive :
            1 ≤
              (pre ++ sourceBlock ++ separator :: sourceRest).count
                letter :=
          List.one_le_count_iff.mpr <| by simp [member]
        have bound := sourceLimitedNorm letter
        have notOne :
            (pre ++ sourceBlock ++ separator :: sourceRest).count
                letter ≠ 1 := by
          simpa [sourceShape, List.append_assoc] using
            sourceBlockNonlinear letter member
        omega
      have targetQuadratic :
          ∀ letter, letter ∈ targetBlock →
            (pre ++ targetBlock ++ separator :: targetRest).count
                letter = 2 := by
        intro letter member
        have positive :
            1 ≤
              (pre ++ targetBlock ++ separator :: targetRest).count
                letter :=
          List.one_le_count_iff.mpr <| by simp [member]
        have bound := targetLimitedNorm letter
        have notOne :
            (pre ++ targetBlock ++ separator :: targetRest).count
                letter ≠ 1 := by
          simpa [targetShape, List.append_assoc] using
            targetBlockNonlinear letter member
        omega
      have move :=
        listDerivesQuadraticBlockPermutationAgainst
          targetBlock sourceBlock pre
          (separator :: sourceRest) (separator :: targetRest)
          blockPermutation sourceQuadratic targetQuadratic equivalentNorm
          lastEqualNorm
      have fullPermutation :
          (pre ++ sourceBlock ++ separator :: sourceRest).Perm
            (pre ++ targetBlock ++ separator :: sourceRest) := by
        simpa [List.append_assoc] using
          List.Perm.append
            (List.Perm.append (List.Perm.refl pre) blockPermutation)
            (List.Perm.refl (separator :: sourceRest))
      let nextPre := pre ++ targetBlock ++ [separator]
      have nextEquivalent :
          M20ListEquivalent
            (nextPre ++ sourceRest) (nextPre ++ targetRest) := by
        have moved :=
          (m20ListEquivalent_of_derives move).symm.trans equivalentNorm
        simpa [nextPre, List.append_assoc] using moved
      have nextLastEqual :
          lastOccurrenceSequence (nextPre ++ sourceRest) =
            lastOccurrenceSequence (nextPre ++ targetRest) := by
        have moved :=
          (lastOccurrenceSequence_eq_of_derives move).symm.trans
            lastEqualNorm
        simpa [nextPre, List.append_assoc] using moved
      have nextCounts :
          ∀ letter,
            (nextPre ++ sourceRest).count letter =
              (nextPre ++ targetRest).count letter := by
        intro letter
        calc
          (nextPre ++ sourceRest).count letter =
              (pre ++ sourceBlock ++ separator :: sourceRest).count
                letter := by
            simpa [nextPre, List.append_assoc] using
              (fullPermutation.count letter).symm
          _ =
              (pre ++ targetBlock ++ separator :: targetRest).count
                letter := countsNorm letter
          _ = (nextPre ++ targetRest).count letter := by
            simp [nextPre, List.append_assoc]
      have nextSourceLimited :
          UniqueSeparatorTwoLimited (nextPre ++ sourceRest) := by
        intro letter
        calc
          (nextPre ++ sourceRest).count letter =
              (pre ++ sourceBlock ++ separator :: sourceRest).count
                letter := by
            simpa [nextPre, List.append_assoc] using
              (fullPermutation.count letter).symm
          _ ≤ 2 := sourceLimitedNorm letter
      have nextTargetLimited :
          UniqueSeparatorTwoLimited (nextPre ++ targetRest) := by
        intro letter
        simpa [nextPre, List.append_assoc] using targetLimitedNorm letter
      have nextSimpleEqual :
          simpleProjection (nextPre ++ sourceRest) sourceRest =
            simpleProjection (nextPre ++ targetRest) targetRest := by
        calc
          simpleProjection (nextPre ++ sourceRest) sourceRest =
              simpleProjection
                (pre ++ sourceBlock ++ separator :: sourceRest)
                sourceRest := by
            apply simpleProjection_congr
            intro letter
            simpa [nextPre, List.append_assoc] using
              (fullPermutation.count letter).symm
          _ = remaining := by
            simpa [sourceShape, List.append_assoc] using
              sourceRestProjection
          _ =
              simpleProjection
                (pre ++ targetBlock ++ separator :: targetRest)
                targetRest := by
            simpa [targetShape, List.append_assoc] using
              targetRestProjection.symm
          _ = simpleProjection (nextPre ++ targetRest) targetRest := by
            simp [nextPre, List.append_assoc]
      have nextPrecedence :
          ∀ x y,
            CompletePrecedenceList (nextPre ++ sourceRest) x y ↔
              CompletePrecedenceList (nextPre ++ targetRest) x y := by
        intro x y
        exact
          m20ListEquivalent_completePrecedenceList nextEquivalent x y
      have recurse :=
        listDerivesSegmented sourceRest targetRest nextPre
          nextSourceLimited nextTargetLimited nextCounts
          nextSimpleEqual nextPrecedence nextEquivalent nextLastEqual
      simpa [sourceShape, targetShape, List.append_assoc] using
        move.trans (by
          simpa [nextPre, List.append_assoc] using recurse)
termination_by sourceTail.length
decreasing_by
  exact sourceRestShorter



private theorem restrictedSegmentationCompleteness
    {left right : List Nat}
    (leftLimited : UniqueSeparatorTwoLimited left)
    (rightLimited : UniqueSeparatorTwoLimited right)
    (equivalent : M20ListEquivalent left right)
    (capped :
      ∀ letter,
        Nat.min (left.count letter) 2 =
          Nat.min (right.count letter) 2)
    (precedence :
      ∀ x y,
        CompletePrecedenceList left x y ↔
          CompletePrecedenceList right x y)
    (lastEqual :
      lastOccurrenceSequence left = lastOccurrenceSequence right) :
    ListDerives left right := by
  have counts : ∀ letter, left.count letter = right.count letter :=
    twoLimited_count_eq_of_capped leftLimited rightLimited capped
  have simpleEqual :
      simpleProjection left left = simpleProjection right right :=
    simpleProjection_eq_of_counts_precedence counts precedence
  simpa using
    listDerivesSegmented left right []
      leftLimited rightLimited counts simpleEqual precedence equivalent
      lastEqual

/-! ## Unrestricted joint completeness -/

theorem derivesOfFactorValid
    (identity : Identity Nat)
    (s4Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S4_116.table.semigroup.opposite)
    (s5Valid :
      identity.SatisfiedBy SemigroupBasis.CoRoots.S5_841.table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have signature : SameM20Signature identity.lhs identity.rhs :=
    catalogueValid_sameM20Signature identity s5Valid
  have originalLastEqual :
      lastOccurrenceSequence identity.lhs.toList =
        lastOccurrenceSequence identity.rhs.toList :=
    s4Valid_lastOccurrenceSequence_eq identity s4Valid
  have leftListDerivation :=
    listDerivesTwoLimitedReduction identity.lhs.toList
  have rightListDerivation :=
    listDerivesTwoLimitedReduction identity.rhs.toList
  cases lhsEq : identity.lhs with
  | mk leftHead leftTail =>
      cases rhsEq : identity.rhs with
      | mk rightHead rightTail =>
          obtain
            ⟨leftCapHead, leftCapTail, leftCapShape,
              leftCapDerivation⟩ :=
            leftListDerivation.from_cons
          obtain
            ⟨rightCapHead, rightCapTail, rightCapShape,
              rightCapDerivation⟩ :=
            rightListDerivation.from_cons
          let leftCap : Word Nat :=
            SemigroupBasis.CoRoots.S5_107.listWordOfCons
              leftCapHead leftCapTail
          let rightCap : Word Nat :=
            SemigroupBasis.CoRoots.S5_107.listWordOfCons
              rightCapHead rightCapTail
          have leftCapToList :
              leftCap.toList =
                uniqueSeparatorEndpointCap
                  (Word.mk leftHead leftTail).toList := by
            simpa [lhsEq, leftCap,
              SemigroupBasis.CoRoots.S5_107.listWordOfCons,
              Word.toList] using leftCapShape.symm
          have rightCapToList :
              rightCap.toList =
                uniqueSeparatorEndpointCap
                  (Word.mk rightHead rightTail).toList := by
            simpa [rhsEq, rightCap,
              SemigroupBasis.CoRoots.S5_107.listWordOfCons,
              Word.toList] using rightCapShape.symm
          have capRawCounts :
              ∀ letter,
                leftCap.toList.count letter =
                  rightCap.toList.count letter := by
            intro letter
            rw [leftCapToList, rightCapToList,
              uniqueSeparatorEndpointCap_count,
              uniqueSeparatorEndpointCap_count]
            simpa [lhsEq, rhsEq, CappedMultiplicity, Nat.min_comm] using
              signature.cappedMultiplicity letter
          have capCounts :
              ∀ letter,
                Nat.min (leftCap.toList.count letter) 2 =
                  Nat.min (rightCap.toList.count letter) 2 := by
            intro letter
            exact congrArg (fun count => Nat.min count 2)
              (capRawCounts letter)
          have leftLimited :
              UniqueSeparatorTwoLimited leftCap.toList := by
            rw [leftCapToList]
            exact
              uniqueSeparatorEndpointCap_twoLimited
                (Word.mk leftHead leftTail).toList
          have rightLimited :
              UniqueSeparatorTwoLimited rightCap.toList := by
            rw [rightCapToList]
            exact
              uniqueSeparatorEndpointCap_twoLimited
                (Word.mk rightHead rightTail).toList
          have capPrecedence :
              ∀ x y,
                CompletePrecedenceList leftCap.toList x y ↔
                  CompletePrecedenceList rightCap.toList x y := by
            intro x y
            have leftPreserved :
                CompletePrecedenceList
                    (Word.mk leftHead leftTail).toList x y ↔
                  CompletePrecedenceList leftCap.toList x y := by
              rw [leftCapToList]
              simpa [lhsEq] using
                m20ListEquivalent_completePrecedenceList
                  (m20ListEquivalent_of_derives leftListDerivation) x y
            have rightPreserved :
                CompletePrecedenceList
                    (Word.mk rightHead rightTail).toList x y ↔
                  CompletePrecedenceList rightCap.toList x y := by
              rw [rightCapToList]
              simpa [rhsEq] using
                m20ListEquivalent_completePrecedenceList
                  (m20ListEquivalent_of_derives rightListDerivation) x y
            have originalPreserved :
                CompletePrecedenceList
                    (Word.mk leftHead leftTail).toList x y ↔
                  CompletePrecedenceList
                    (Word.mk rightHead rightTail).toList x y := by
              simpa [lhsEq, rhsEq, CompletePrecedence] using
                signature.completePrecedence x y
            exact
              leftPreserved.symm.trans
                (originalPreserved.trans rightPreserved)
          have originalEquivalent :
              M20ListEquivalent
                (Word.mk leftHead leftTail).toList
                (Word.mk rightHead rightTail).toList :=
            by
              simpa [lhsEq, rhsEq] using
                M20ListEquivalent.of_valid identity
                  (publishedM20ToCatalogue.pullback_identity identity s5Valid)
          have capEquivalent :
              M20ListEquivalent leftCap.toList rightCap.toList := by
            rw [leftCapToList, rightCapToList]
            have leftCapEquivalent :
                M20ListEquivalent
                  (uniqueSeparatorEndpointCap
                    (Word.mk leftHead leftTail).toList)
                  (Word.mk leftHead leftTail).toList := by
              simpa [lhsEq] using
                (m20ListEquivalent_of_derives leftListDerivation).symm
            have rightCapEquivalent :
                M20ListEquivalent
                  (Word.mk rightHead rightTail).toList
                  (uniqueSeparatorEndpointCap
                    (Word.mk rightHead rightTail).toList) := by
              simpa [rhsEq] using
                m20ListEquivalent_of_derives rightListDerivation
            exact
              leftCapEquivalent.trans
                (originalEquivalent.trans rightCapEquivalent)
          have capLastEqual :
              lastOccurrenceSequence leftCap.toList =
                lastOccurrenceSequence rightCap.toList := by
            rw [leftCapToList, rightCapToList]
            simpa [lhsEq, rhsEq] using
              (lastOccurrenceSequence_eq_of_derives
                leftListDerivation).symm.trans
                (originalLastEqual.trans
                  (lastOccurrenceSequence_eq_of_derives
                    rightListDerivation))
          have capListDerivation :=
            restrictedSegmentationCompleteness
              leftLimited rightLimited capEquivalent capCounts
              capPrecedence capLastEqual
          have capWordDerivation :
              Derives basis leftCap rightCap := by
            have represented :
                ListDerives
                  (leftCapHead :: leftCapTail)
                  (rightCapHead :: rightCapTail) := by
              simpa [leftCap, rightCap,
                SemigroupBasis.CoRoots.S5_107.listWordOfCons,
                Word.toList] using capListDerivation
            simpa [leftCap, rightCap] using represented.toWord
          simpa [lhsEq, rhsEq,
            SemigroupBasis.CoRoots.S5_107.listWordOfCons] using
            leftCapDerivation.trans
              (capWordDerivation.trans rightCapDerivation.symm)

/-- The seven displayed laws are the exact basis of the two factor theories'
intersection. -/
def intersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.Catalogue.S4_116.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_841.table.semigroup basis where
  leftModels := modelsS4_116Opposite
  rightModels := modelsS5_841
  complete := derivesOfFactorValid


end SemigroupBasis.CoRoots.Order6FactorPairS4_116opS5_841
