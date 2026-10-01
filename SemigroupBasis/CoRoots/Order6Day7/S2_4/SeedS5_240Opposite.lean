import SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank051
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer
import SemigroupBasis.CoRoots.S5_240Completeness

/-!
# An unrestricted `S2_4 × S5_240ᵒᵖ` family seed

Independent direct `S5_240` completeness certifies the exact reversed-word
support, singleton, globally unique terminal variable, and simple penultimate
pair. In the original orientation the actual left-zero factor fixes the first
variable, while a distinct globally unique second variable is detected even
when the first variable repeats.

The authenticated rank-051 laws make the suffix after the first two variables
a commutative idempotent support. Unique second variables remain fixed;
repeated second variables switch only through genuine displayed-law marker
derivations; and the square law saturates repeated-initial classes. These
branches prove unrestricted completeness before quotient packaging.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank051.Seed

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_83

universe u v

private def instantiateThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

private def pairWord
    (initial marker : Nat) (tail : List Nat) : Word Nat :=
  ⟨initial, marker :: tail⟩

private def appendLetters
    (word : Word Nat) (tail : List Nat) : Word Nat :=
  ⟨word.head, word.tail ++ tail⟩

private theorem appendLetters_derives
    {left right : Word Nat}
    (derivation : Derives basis left right)
    (tail : List Nat) :
    Derives basis
      (appendLetters left tail)
      (appendLetters right tail) := by
  cases tail with
  | nil =>
      simpa [appendLetters] using derivation
  | cons first rest =>
      simpa [appendLetters, Word.append] using
        Derives.appendRight derivation (Word.mk first rest)

/-- The authenticated `xx = xxx` expands a nonempty square. -/
theorem derivesPowerExpansion
    (first : Word Nat) :
    Derives basis
      (first ++ first)
      ((first ++ first) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [0]) (Word.mk 0 [0, 0]) :=
    Derives.fromBasis (e := law00) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first first first)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The authenticated `xxy = xxyx` returns the repeated initial block. -/
theorem derivesRepeatedReturn
    (first second : Word Nat) :
    Derives basis
      ((first ++ first) ++ second)
      (((first ++ first) ++ second) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 1]) (Word.mk 0 [0, 1, 0]) :=
    Derives.fromBasis (e := law01) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first second second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The authenticated `xyyz = xzyz` switches a repeated interior marker. -/
theorem derivesMarkerCopy
    (initial repeated replacement : Word Nat) :
    Derives basis
      (((initial ++ repeated) ++ repeated) ++ replacement)
      (((initial ++ replacement) ++ repeated) ++ replacement) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 1, 2]) (Word.mk 0 [2, 1, 2]) :=
    Derives.fromBasis (e := law12) (by simp [basis])
  have substituted :=
    Derives.subst primitive
      (instantiateThree initial repeated replacement)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The authenticated `xyz = xyzz` duplicates any suffix block. -/
theorem derivesSuffixDuplication
    (initial marker repeated : Word Nat) :
    Derives basis
      ((initial ++ marker) ++ repeated)
      (((initial ++ marker) ++ repeated) ++ repeated) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 2]) (Word.mk 0 [1, 2, 2]) :=
    Derives.fromBasis (e := law13) (by simp [basis])
  have substituted :=
    Derives.subst primitive
      (instantiateThree initial marker repeated)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Swap arbitrary suffix blocks after two fixed nonempty contexts:
`PABC → PABCBC → PACCB C → PACCB → PACB`. -/
theorem derivesSuffixSwap
    (initial marker first second : Word Nat) :
    Derives basis
      (((initial ++ marker) ++ first) ++ second)
      (((initial ++ marker) ++ second) ++ first) := by
  have duplicate :=
    derivesSuffixDuplication initial marker (first ++ second)
  have switched :=
    Derives.prepend initial <|
      Derives.appendRight
        (derivesMarkerCopy marker second first).symm second
  have contractedReturn :=
    Derives.prepend (initial ++ marker)
      (derivesRepeatedReturn second first).symm
  have contractedSquare :=
    Derives.appendRight
      (derivesSuffixDuplication initial marker second).symm first
  have firstStep :
      Derives basis
        (((initial ++ marker) ++ first) ++ second)
        (((((initial ++ marker) ++ first) ++ second) ++ first) ++ second) := by
    simpa [Word.append_assoc] using duplicate
  have secondStep :
      Derives basis
        (((((initial ++ marker) ++ first) ++ second) ++ first) ++ second)
        (((((initial ++ marker) ++ second) ++ second) ++ first) ++ second) := by
    simpa [Word.append_assoc] using switched
  have thirdStep :
      Derives basis
        (((((initial ++ marker) ++ second) ++ second) ++ first) ++ second)
        ((((initial ++ marker) ++ second) ++ second) ++ first) := by
    simpa [Word.append_assoc] using contractedReturn
  have fourthStep :
      Derives basis
        ((((initial ++ marker) ++ second) ++ second) ++ first)
        (((initial ++ marker) ++ second) ++ first) := by
    simpa [Word.append_assoc] using contractedSquare
  exact firstStep.trans <|
    secondStep.trans (thirdStep.trans fourthStep)

/-- Every suffix permutation retains both initial variables. -/
theorem derivesTailPermutation
    {left right : List Nat}
    (permutation : left.Perm right)
    (initial marker : Nat) :
    Derives basis
      (pairWord initial marker left)
      (pairWord initial marker right) := by
  induction permutation generalizing initial marker with
  | nil =>
      exact Derives.refl _
  | cons letter _ induction =>
      simpa [pairWord, Word.append, Word.singleton] using
        Derives.prepend
          (Word.singleton initial) (induction marker letter)
  | swap first second rest =>
      have swapped :=
        derivesSuffixSwap
          (Word.singleton initial)
          (Word.singleton marker)
          (Word.singleton second)
          (Word.singleton first)
      simpa [pairWord, appendLetters, Word.append,
        Word.singleton, List.append_assoc] using
        appendLetters_derives swapped rest
  | trans _ _ first second =>
      exact (first initial marker).trans (second initial marker)

private theorem derivesDeleteLeadingTail
    (initial marker letter : Nat) (tail : List Nat)
    (present : letter ∈ tail) :
    Derives basis
      (pairWord initial marker (letter :: tail))
      (pairWord initial marker tail) := by
  have expose : tail.Perm (letter :: tail.erase letter) :=
    List.perm_cons_erase present
  have sourcePermutation :
      (letter :: tail).Perm
        (letter :: letter :: tail.erase letter) :=
    List.Perm.cons letter expose
  have contraction :
      Derives basis
        (pairWord initial marker
          (letter :: letter :: tail.erase letter))
        (pairWord initial marker
          (letter :: tail.erase letter)) := by
    have primitive :=
      (derivesSuffixDuplication
        (Word.singleton initial)
        (Word.singleton marker)
        (Word.singleton letter)).symm
    simpa [pairWord, appendLetters, Word.append,
      Word.singleton, List.append_assoc] using
      appendLetters_derives primitive (tail.erase letter)
  exact
    (derivesTailPermutation sourcePermutation initial marker).trans <|
      contraction.trans
        (derivesTailPermutation expose.symm initial marker)

/-- Reduce the suffix to one representative of each support variable. -/
theorem derivesNormalizeTail :
    ∀ (initial marker : Nat) (tail : List Nat),
      Derives basis
        (pairWord initial marker tail)
        (pairWord initial marker (finalMarkerPrefixReduce tail))
  | initial, marker, [] =>
      Derives.refl _
  | initial, marker, letter :: rest => by
      have suffixNormal :=
        derivesNormalizeTail marker letter rest
      have prefixed :
          Derives basis
            (pairWord initial marker (letter :: rest))
            (pairWord initial marker
              (letter :: finalMarkerPrefixReduce rest)) := by
        simpa [pairWord, Word.append, Word.singleton] using
          Derives.prepend (Word.singleton initial) suffixNormal
      by_cases present : letter ∈ finalMarkerPrefixReduce rest
      · have reduceEq :
            finalMarkerPrefixReduce (letter :: rest) =
              finalMarkerPrefixReduce rest := by
          simp [finalMarkerPrefixReduce, present]
        rw [reduceEq]
        exact prefixed.trans <|
          derivesDeleteLeadingTail
            initial marker letter
            (finalMarkerPrefixReduce rest) present
      · have reduceEq :
            finalMarkerPrefixReduce (letter :: rest) =
              letter :: finalMarkerPrefixReduce rest := by
          simp [finalMarkerPrefixReduce, present]
        rw [reduceEq]
        exact prefixed

/-- Equal suffix supports are complete when the first pair agrees. -/
theorem derivesOfTailSupport
    (initial marker : Nat) (left right : List Nat)
    (support : ∀ letter, letter ∈ left ↔ letter ∈ right) :
    Derives basis
      (pairWord initial marker left)
      (pairWord initial marker right) := by
  have permutation :
      (finalMarkerPrefixReduce left).Perm
        (finalMarkerPrefixReduce right) := by
    rw [List.perm_iff_count]
    intro letter
    rw [(finalMarkerPrefixReduce_nodup left).count,
      (finalMarkerPrefixReduce_nodup right).count]
    simp only [finalMarkerPrefixReduce_mem, support letter]
  exact
    (derivesNormalizeTail initial marker left).trans <|
      (derivesTailPermutation permutation initial marker).trans
        (derivesNormalizeTail initial marker right).symm

/-- Switch a repeated second variable only when both markers occur in the
actual suffix. -/
theorem derivesRepeatedMarkerSwitch
    (initial oldMarker newMarker : Nat) (tail : List Nat)
    (oldPresent : oldMarker ∈ tail)
    (newPresent : newMarker ∈ tail) :
    Derives basis
      (pairWord initial oldMarker tail)
      (pairWord initial newMarker tail) := by
  by_cases equal : oldMarker = newMarker
  · subst newMarker
    exact Derives.refl _
  · have newInErase :
        newMarker ∈ tail.erase oldMarker := by
      exact (List.mem_erase_of_ne (Ne.symm equal)).mpr newPresent
    let remainder := (tail.erase oldMarker).erase newMarker
    have arrange :
        tail.Perm (oldMarker :: newMarker :: remainder) := by
      exact (List.perm_cons_erase oldPresent).trans <|
        List.Perm.cons oldMarker <| by
          simpa [remainder] using List.perm_cons_erase newInErase
    have switched :
        Derives basis
          (pairWord initial oldMarker
            (oldMarker :: newMarker :: remainder))
          (pairWord initial newMarker
            (oldMarker :: newMarker :: remainder)) := by
      have primitive :=
        derivesMarkerCopy
          (Word.singleton initial)
          (Word.singleton oldMarker)
          (Word.singleton newMarker)
      simpa [pairWord, appendLetters, Word.append,
        Word.singleton, List.append_assoc] using
        appendLetters_derives primitive remainder
    exact
      (derivesTailPermutation arrange initial oldMarker).trans <|
        switched.trans
          (derivesTailPermutation arrange.symm initial newMarker)

/-- A nonsimple second marker in a nonunique-initial class normalizes to the
initial marker; the displayed square law preserves the old marker support. -/
theorem derivesNonsimpleInitialCanonical
    (initial marker : Nat) (tail : List Nat)
    (notSimple : ¬(marker ≠ initial ∧ marker ∉ tail))
    (notUnique : ¬(initial ≠ marker ∧ initial ∉ tail)) :
    Derives basis
      (pairWord initial marker tail)
      (pairWord initial initial (marker :: tail)) := by
  by_cases equal : marker = initial
  · subst marker
    have power := derivesPowerExpansion (Word.singleton initial)
    simpa [pairWord, appendLetters, Word.append,
      Word.singleton, List.append_assoc] using
      appendLetters_derives power tail
  · have markerPresent : marker ∈ tail := by
      apply Decidable.byContradiction
      intro absent
      exact notSimple ⟨equal, absent⟩
    have initialPresent : initial ∈ tail := by
      apply Decidable.byContradiction
      intro absent
      exact notUnique ⟨Ne.symm equal, absent⟩
    have switched :=
      derivesRepeatedMarkerSwitch
        initial marker initial tail markerPresent initialPresent
    have support :
        ∀ letter, letter ∈ tail ↔ letter ∈ marker :: tail := by
      intro letter
      constructor
      · exact List.Mem.tail marker
      · intro member
        rcases List.mem_cons.mp member with markerEq | present
        · simpa [markerEq] using markerPresent
        · exact present
    exact switched.trans <|
      derivesOfTailSupport initial initial tail (marker :: tail) support

/-- An explicit initial pair reverses to the expected terminal split. -/
private theorem reversePair_split
    (initial marker : Nat) (tail : List Nat) :
    terminalSplit (pairWord initial marker tail).reverse =
      .pair tail.reverse marker initial := by
  have rendered :
      (pairWord initial marker tail).reverse =
        (TerminalSplit.pair tail.reverse marker initial).renderWord := by
    apply Word.toList_injective
    rw [Word.toList_reverse, TerminalSplit.toList_renderWord]
    simp [pairWord, Word.toList, TerminalSplit.renderList,
      List.reverse_cons, List.append_assoc]
  rw [rendered, terminalSplit_renderWord_inverse]

/-- The exact lower-factor endpoint signature plus a common initial variable
constructively derives the actual displayed rank-051 identity. -/
theorem derivesPairOfReversedSignature
    (initial leftMarker rightMarker : Nat)
    (leftTail rightTail : List Nat)
    (same :
      SemigroupBasis.CoRoots.S5_240.SameEndpointSuffixSignature
        (pairWord initial leftMarker leftTail).reverse
        (pairWord initial rightMarker rightTail).reverse) :
    Derives basis
      (pairWord initial leftMarker leftTail)
      (pairWord initial rightMarker rightTail) := by
  have leftSplit := reversePair_split initial leftMarker leftTail
  have rightSplit := reversePair_split initial rightMarker rightTail
  have support :
      ∀ letter,
        (letter = initial ∨ letter = leftMarker ∨ letter ∈ leftTail) ↔
          (letter = initial ∨ letter = rightMarker ∨
            letter ∈ rightTail) := by
    intro letter
    have compared := same.support letter
    rw [Word.toList_reverse, Word.toList_reverse] at compared
    rw [List.mem_reverse, List.mem_reverse] at compared
    simpa only [pairWord, Word.toList, List.mem_cons] using compared
  have uniqueIff :
      (initial ≠ leftMarker ∧ initial ∉ leftTail) ↔
        (initial ≠ rightMarker ∧ initial ∉ rightTail) := by
    simpa [UniqueFinal, leftSplit, rightSplit] using
      same.uniqueFinal initial
  by_cases leftSimple :
      leftMarker ≠ initial ∧ leftMarker ∉ leftTail
  · have leftPair :
        SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair
          (pairWord initial leftMarker leftTail).reverse
          leftMarker initial := by
      simpa [SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair,
        leftSplit] using
        ⟨leftSimple.2, Ne.symm leftSimple.1⟩
    have rightPair :=
      (same.simplePenultimatePair leftMarker initial).mp leftPair
    have rightParts :
        rightMarker = leftMarker ∧
          leftMarker ∉ rightTail ∧
          initial ≠ leftMarker := by
      simpa [SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair,
        rightSplit] using rightPair
    have markers := rightParts.1
    subst rightMarker
    have headAbsence :
        initial ∉ leftTail ↔ initial ∉ rightTail := by
      constructor
      · intro absent
        exact (uniqueIff.mp ⟨Ne.symm leftSimple.1, absent⟩).2
      · intro absent
        exact (uniqueIff.mpr ⟨Ne.symm leftSimple.1, absent⟩).2
    have tailSupport :
        ∀ letter, letter ∈ leftTail ↔ letter ∈ rightTail := by
      intro letter
      by_cases head : letter = initial
      · subst letter
        by_cases present : initial ∈ leftTail
        · have rightPresent : initial ∈ rightTail := by
            apply Decidable.byContradiction
            intro absent
            exact (headAbsence.mpr absent) present
          exact iff_of_true present rightPresent
        · exact iff_of_false present (headAbsence.mp present)
      · by_cases marker : letter = leftMarker
        · subst letter
          exact iff_of_false leftSimple.2 rightParts.2.1
        · simpa [head, marker] using support letter
    exact derivesOfTailSupport
      initial leftMarker leftTail rightTail tailSupport
  · have rightNotSimple :
        ¬(rightMarker ≠ initial ∧ rightMarker ∉ rightTail) := by
      intro rightSimple
      have rightPair :
          SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair
            (pairWord initial rightMarker rightTail).reverse
            rightMarker initial := by
        simpa [SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair,
          rightSplit] using
          ⟨rightSimple.2, Ne.symm rightSimple.1⟩
      have leftPair :=
        (same.simplePenultimatePair rightMarker initial).mpr rightPair
      have leftParts :
          leftMarker = rightMarker ∧
            rightMarker ∉ leftTail ∧
            initial ≠ rightMarker := by
        simpa [SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair,
          leftSplit] using leftPair
      apply leftSimple
      constructor
      · intro equal
        exact leftParts.2.2 (equal.symm.trans leftParts.1)
      · intro present
        exact leftParts.2.1 <| by
          simpa [← leftParts.1] using present
    by_cases leftUnique :
        initial ≠ leftMarker ∧ initial ∉ leftTail
    · have rightUnique := uniqueIff.mp leftUnique
      have oldRepeated : leftMarker ∈ leftTail := by
        apply Decidable.byContradiction
        intro absent
        exact leftSimple ⟨Ne.symm leftUnique.1, absent⟩
      have newRepeated : rightMarker ∈ rightTail := by
        apply Decidable.byContradiction
        intro absent
        exact rightNotSimple ⟨Ne.symm rightUnique.1, absent⟩
      have tailSupport :
          ∀ letter, letter ∈ leftTail ↔ letter ∈ rightTail := by
        intro letter
        constructor
        · intro member
          rcases (support letter).mp (Or.inr (Or.inr member)) with
            head | marker | target
          · subst letter
            exact False.elim (leftUnique.2 member)
          · subst letter
            exact newRepeated
          · exact target
        · intro member
          rcases (support letter).mpr (Or.inr (Or.inr member)) with
            head | marker | target
          · subst letter
            exact False.elim (rightUnique.2 member)
          · subst letter
            exact oldRepeated
          · exact target
      have newInLeft : rightMarker ∈ leftTail :=
        (tailSupport rightMarker).mpr newRepeated
      exact
        (derivesRepeatedMarkerSwitch
          initial leftMarker rightMarker leftTail
          oldRepeated newInLeft).trans
          (derivesOfTailSupport
            initial rightMarker leftTail rightTail tailSupport)
    · have rightNotUnique :
          ¬(initial ≠ rightMarker ∧ initial ∉ rightTail) := by
        intro unique
        exact leftUnique (uniqueIff.mpr unique)
      have headInLeft : initial ∈ leftMarker :: leftTail := by
        by_cases equal : leftMarker = initial
        · exact List.mem_cons.mpr (Or.inl equal.symm)
        · have present : initial ∈ leftTail := by
            apply Decidable.byContradiction
            intro absent
            exact leftUnique ⟨Ne.symm equal, absent⟩
          exact List.Mem.tail _ present
      have headInRight : initial ∈ rightMarker :: rightTail := by
        by_cases equal : rightMarker = initial
        · exact List.mem_cons.mpr (Or.inl equal.symm)
        · have present : initial ∈ rightTail := by
            apply Decidable.byContradiction
            intro absent
            exact rightNotUnique ⟨Ne.symm equal, absent⟩
          exact List.Mem.tail _ present
      have tailSupport :
          ∀ letter,
            letter ∈ leftMarker :: leftTail ↔
              letter ∈ rightMarker :: rightTail := by
        intro letter
        constructor
        · intro member
          have source :
              letter = initial ∨
                letter = leftMarker ∨ letter ∈ leftTail := by
            rcases List.mem_cons.mp member with marker | tail
            · exact Or.inr (Or.inl marker)
            · exact Or.inr (Or.inr tail)
          rcases (support letter).mp source with
            head | marker | tail
          · subst letter
            exact headInRight
          · exact List.mem_cons.mpr (Or.inl marker)
          · exact List.mem_cons.mpr (Or.inr tail)
        · intro member
          have source :
              letter = initial ∨
                letter = rightMarker ∨ letter ∈ rightTail := by
            rcases List.mem_cons.mp member with marker | tail
            · exact Or.inr (Or.inl marker)
            · exact Or.inr (Or.inr tail)
          rcases (support letter).mpr source with
            head | marker | tail
          · subst letter
            exact headInLeft
          · exact List.mem_cons.mpr (Or.inl marker)
          · exact List.mem_cons.mpr (Or.inr tail)
      exact
        (derivesNonsimpleInitialCanonical
          initial leftMarker leftTail leftSimple leftUnique).trans <|
          (derivesOfTailSupport
            initial initial
            (leftMarker :: leftTail)
            (rightMarker :: rightTail) tailSupport).trans
            (derivesNonsimpleInitialCanonical
              initial rightMarker rightTail
              rightNotSimple rightNotUnique).symm

/-- Validity in the actual left-zero factor fixes the initial variable. -/
theorem leftValid_head
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftTable.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  change identity.SatisfiedBy leftZeroTwo.semigroup at valid
  apply Decidable.byContradiction
  intro different
  let valuation : Nat → Fin 2 :=
    fun letter => if letter = identity.lhs.head then 0 else 1
  have evaluated := valid valuation
  rw [leftZeroTwo_eval, leftZeroTwo_eval] at evaluated
  simp [valuation, Ne.symm different] at evaluated

/-- Exact opposite-factor validity is independent direct-factor validity of
the reversed identity. -/
theorem rightValid_reversed
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    identity.reversed.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_240.table.semigroup := by
  change
    identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_240.table.semigroup.opposite
    at valid
  exact
    (Identity.satisfiedBy_opposite_iff_reversed identity
      SemigroupBasis.Generated.Catalogue.S5_240.table.semigroup).mp valid

/-- Genuine unrestricted completeness obtained from the independent lower
endpoint, exact semantic signature, and displayed-law suffix normalization. -/
theorem derives_of_factor_valid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have reversedValid := rightValid_reversed identity rightValid
  have lower :=
    SemigroupBasis.CoRoots.S5_240.basis_complete.2
      identity.reversed reversedValid
  have certifiedValid :
      identity.reversed.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_240.table.semigroup :=
    fun valuation =>
      lower.sound SemigroupBasis.CoRoots.S5_240.models valuation
  have same :=
    SemigroupBasis.CoRoots.S5_240.valid_signature
      identity.reversed certifiedValid
  have heads := leftValid_head identity leftValid
  cases identity with
  | mk left right =>
      cases left with
      | mk initial leftLetters =>
          cases right with
          | mk rightInitial rightLetters =>
              change initial = rightInitial at heads
              subst rightInitial
              cases leftLetters with
              | nil =>
                  cases rightLetters with
                  | nil =>
                      exact Derives.refl _
                  | cons rightMarker rightTail =>
                      have leftSingleton :
                          IsSingletonWord
                            (Word.mk initial []).reverse := by
                        change True
                        trivial
                      have rightSingleton :=
                        same.singleton.mp leftSingleton
                      change
                        IsSingletonWord
                          (pairWord initial rightMarker rightTail).reverse
                        at rightSingleton
                      have rightSplit :=
                        reversePair_split
                          initial rightMarker rightTail
                      simp [IsSingletonWord, rightSplit] at rightSingleton
              | cons leftMarker leftTail =>
                  cases rightLetters with
                  | nil =>
                      have rightSingleton :
                          IsSingletonWord
                            (Word.mk initial []).reverse := by
                        change True
                        trivial
                      have leftSingleton :=
                        same.singleton.mpr rightSingleton
                      change
                        IsSingletonWord
                          (pairWord initial leftMarker leftTail).reverse
                        at leftSingleton
                      have leftSplit :=
                        reversePair_split
                          initial leftMarker leftTail
                      simp [IsSingletonWord, leftSplit] at leftSingleton
                  | cons rightMarker rightTail =>
                      exact
                        derivesPairOfReversedSignature
                          initial leftMarker rightMarker
                          leftTail rightTail same

/-- Assemble the factor pair only after unrestricted completeness. -/
def intersectionBasis :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := derives_of_factor_valid

/-- Independently certified reusable rank-051 family seed. -/
noncomputable def normalizer :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

theorem s6_6510_representative_basis :
    BasisFor S6_6510.table.semigroup basis :=
  S6_6510.representative_basis_of_normalizer normalizer

theorem s6_6510_opposite_basis :
    BasisFor S6_6510.table.semigroup.opposite (reversedBasis basis) :=
  S6_6510.opposite_basis_of_normalizer normalizer

theorem s6_9924_representative_basis :
    BasisFor S6_9924.table.semigroup basis :=
  S6_9924.representative_basis_of_normalizer normalizer

theorem s6_9924_opposite_basis :
    BasisFor S6_9924.table.semigroup.opposite (reversedBasis basis) :=
  S6_9924.opposite_basis_of_normalizer normalizer

/-- Reviewed transport retains explicit law derivations and independent
unrestricted validity implications for both target factors. -/
noncomputable def transportedNormalizer
    {A : Type u} {B : Type v}
    {targetLeft : Semigroup A} {targetRight : Semigroup B}
    {targetBasis : List (Identity Nat)}
    (lawDerivations :
      ∀ law : Identity Nat,
        law ∈ basis → Derives targetBasis law.lhs law.rhs)
    (leftTheory :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy targetLeft →
          identity.SatisfiedBy leftTable.semigroup)
    (rightTheory :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy targetRight →
          identity.SatisfiedBy rightTable.semigroup) :
    IntersectionNormalizer targetLeft targetRight targetBasis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.transportNormalizer
    normalizer lawDerivations leftTheory rightTheory

end SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank051.Seed
