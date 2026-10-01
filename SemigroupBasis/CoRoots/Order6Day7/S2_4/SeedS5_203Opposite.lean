import SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank046
import SemigroupBasis.CoRoots.Order6Day7.S2_4.SeedS5_203

/-!
# An unrestricted `S2_4 × S5_203ᵒᵖ` family seed

The independent direct `S5_203` endpoint certifies the exact reversed-word
signature: support, singleton, globally unique terminal variable, terminal
doubleton, and the conditioned unique terminal pair. The actual left-zero
factor additionally fixes the unreversed initial variable.

Five authenticated rank-046 laws make the suffix after two fixed initial
variables a commutative idempotent support. The conditioned unique pair fixes
a genuinely unique second variable; repeated second variables can be switched
using `xyyz = xzyz`; and a repeated initial variable can be normalized to the
initial-marker class using `xxxy = xyx`. The initial-doubleton branch stays
separate throughout. No temporary initial variable is cancelled, and no
factor validity is inferred from a finite table.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank046.Seed

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

/-- Append a possibly empty list of singleton variables to both endpoints. -/
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

/-- The authenticated `xxxy = xyx` exchanges a triple prefix for a return. -/
theorem derivesTripleReturn
    (first second : Word Nat) :
    Derives basis
      (((first ++ first) ++ first) ++ second)
      ((first ++ second) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 0, 1]) (Word.mk 0 [1, 0]) :=
    Derives.fromBasis (e := law01) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first second second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The authenticated `xyy = xyyy` expands a repeated second block. -/
theorem derivesSecondCube
    (first second : Word Nat) :
    Derives basis
      ((first ++ second) ++ second)
      (((first ++ second) ++ second) ++ second) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 1]) (Word.mk 0 [1, 1, 1]) :=
    Derives.fromBasis (e := law15) (by simp [basis])
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
    Derives.fromBasis (e := law16) (by simp [basis])
  have substituted :=
    Derives.subst primitive
      (instantiateThree initial repeated replacement)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The authenticated `xyz = xyzz` duplicates any block after two contexts. -/
theorem derivesSuffixDuplication
    (initial marker repeated : Word Nat) :
    Derives basis
      ((initial ++ marker) ++ repeated)
      (((initial ++ marker) ++ repeated) ++ repeated) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 2]) (Word.mk 0 [1, 2, 2]) :=
    Derives.fromBasis (e := law17) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree initial marker repeated)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Swap arbitrary suffix blocks after two fixed nonempty contexts:
`PABC → PABBC → PABBBC → PABCB → PACCB → PACB`. -/
theorem derivesSuffixSwap
    (initial marker first second : Word Nat) :
    Derives basis
      (((initial ++ marker) ++ first) ++ second)
      (((initial ++ marker) ++ second) ++ first) := by
  have duplicate :=
    Derives.appendRight
      (derivesSuffixDuplication initial marker first) second
  have triple :=
    Derives.appendRight
      (derivesSecondCube (initial ++ marker) first) second
  have returning :=
    Derives.prepend (initial ++ marker)
      (derivesTripleReturn first second)
  have switch :=
    Derives.prepend initial
      (derivesMarkerCopy marker second first).symm
  have contract :=
    Derives.appendRight
      (derivesSuffixDuplication initial marker second).symm first
  have firstStep :
      Derives basis
        (((initial ++ marker) ++ first) ++ second)
        ((((initial ++ marker) ++ first) ++ first) ++ second) := by
    simpa [Word.append_assoc] using duplicate
  have secondStep :
      Derives basis
        ((((initial ++ marker) ++ first) ++ first) ++ second)
        (((((initial ++ marker) ++ first) ++ first) ++ first) ++ second) := by
    simpa [Word.append_assoc] using triple
  have thirdStep :
      Derives basis
        (((((initial ++ marker) ++ first) ++ first) ++ first) ++ second)
        ((((initial ++ marker) ++ first) ++ second) ++ first) := by
    simpa [Word.append_assoc] using returning
  have fourthStep :
      Derives basis
        ((((initial ++ marker) ++ first) ++ second) ++ first)
        ((((initial ++ marker) ++ second) ++ second) ++ first) := by
    simpa [Word.append_assoc] using switch
  have fifthStep :
      Derives basis
        ((((initial ++ marker) ++ second) ++ second) ++ first)
        (((initial ++ marker) ++ second) ++ first) := by
    simpa [Word.append_assoc] using contract
  exact firstStep.trans <|
    secondStep.trans <|
      thirdStep.trans (fourthStep.trans fifthStep)

/-- Every suffix permutation preserves the first two variables literally. -/
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

/-- Delete a repeated suffix letter after exposing its duplicate. -/
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

/-- Normalize the suffix to one representative of each variable. -/
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

/-- With fixed first and second variables, suffix support is complete. -/
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

/-- A repeated second variable can be replaced by any other suffix marker
without changing the suffix support. -/
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

/-- When the initial variable occurs in the suffix, normalize the second
marker to that initial variable without losing the old marker's support. -/
theorem derivesRepeatedInitialCanonical
    (initial marker : Nat) (tail : List Nat)
    (initialPresent : initial ∈ tail) :
    Derives basis
      (pairWord initial marker tail)
      (pairWord initial initial (marker :: tail)) := by
  let remainder := tail.erase initial
  have arrange : tail.Perm (initial :: remainder) := by
    simpa [remainder] using List.perm_cons_erase initialPresent
  have expanded :
      Derives basis
        (pairWord initial marker (initial :: remainder))
        (pairWord initial initial
          (initial :: marker :: remainder)) := by
    have primitive :=
      (derivesTripleReturn
        (Word.singleton initial)
        (Word.singleton marker)).symm
    simpa [pairWord, appendLetters, Word.append,
      Word.singleton, List.append_assoc] using
      appendLetters_derives primitive remainder
  have tailSupport :
      ∀ letter,
        letter ∈ initial :: marker :: remainder ↔
          letter ∈ marker :: tail := by
    intro letter
    have membership :
        letter ∈ tail ↔ letter ∈ initial :: remainder :=
      arrange.mem_iff
    simp only [List.mem_cons] at membership ⊢
    constructor
    · rintro (head | old | rest)
      · exact Or.inr (membership.mpr (Or.inl head))
      · exact Or.inl old
      · exact Or.inr (membership.mpr (Or.inr rest))
    · rintro (old | source)
      · exact Or.inr (Or.inl old)
      · rcases membership.mp source with head | rest
        · exact Or.inl head
        · exact Or.inr (Or.inr rest)
  exact
    (derivesTailPermutation arrange initial marker).trans <|
      expanded.trans
        (derivesOfTailSupport
          initial initial
          (initial :: marker :: remainder)
          (marker :: tail) tailSupport)

/-- Reversing an explicit initial pair gives its exact terminal split. -/
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

/-- Exact reversed lower-factor semantics plus a common initial variable
produce an unrestricted rank-046 derivation. -/
theorem derivesPairOfReversedSignature
    (initial leftMarker rightMarker : Nat)
    (leftTail rightTail : List Nat)
    (same :
      SemigroupBasis.CoRoots.S5_203.DirectCompletenessArchitecture.SameSupportTerminalStateSignature
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
  have doubletonIff :
      (leftMarker = initial ∧ initial ∉ leftTail) ↔
        (rightMarker = initial ∧ initial ∉ rightTail) := by
    simpa [SemigroupBasis.CoRoots.S5_203.DirectCompletenessArchitecture.TerminalDoubleton,
      leftSplit, rightSplit] using
      same.terminalDoubleton initial
  by_cases leftUnique :
      initial ≠ leftMarker ∧ initial ∉ leftTail
  · have rightUnique := uniqueIff.mp leftUnique
    have leftUniqueFinal :
        UniqueFinal
          (pairWord initial leftMarker leftTail).reverse initial := by
      simpa [UniqueFinal, leftSplit] using leftUnique
    by_cases oldRepeated : leftMarker ∈ leftTail
    · have newRepeated : rightMarker ∈ rightTail := by
        apply Decidable.byContradiction
        intro newAbsent
        have rightPair :
            UniqueTerminalPair
              (pairWord initial rightMarker rightTail).reverse
              rightMarker initial := by
          simp [UniqueTerminalPair, rightSplit,
            newAbsent, rightUnique.1, rightUnique.2]
        have leftPair :=
          (same.uniqueTerminalPairOfUniqueFinal
            rightMarker initial leftUniqueFinal).mpr rightPair
        have leftParts :
            leftMarker = rightMarker ∧
              rightMarker ∉ leftTail ∧
              initial ≠ rightMarker ∧
              initial ∉ leftTail := by
          simpa [UniqueTerminalPair, leftSplit] using leftPair
        exact leftParts.2.1 <| by
          simpa [← leftParts.1] using oldRepeated
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
    · have leftPair :
          UniqueTerminalPair
            (pairWord initial leftMarker leftTail).reverse
            leftMarker initial := by
        simp [UniqueTerminalPair, leftSplit,
          oldRepeated, leftUnique.1, leftUnique.2]
      have rightPair :=
        (same.uniqueTerminalPairOfUniqueFinal
          leftMarker initial leftUniqueFinal).mp leftPair
      have rightParts :
          rightMarker = leftMarker ∧
            leftMarker ∉ rightTail ∧
            initial ≠ leftMarker ∧
            initial ∉ rightTail := by
        simpa [UniqueTerminalPair, rightSplit] using rightPair
      have markers := rightParts.1
      subst rightMarker
      have tailSupport :
          ∀ letter, letter ∈ leftTail ↔ letter ∈ rightTail := by
        intro letter
        by_cases head : letter = initial
        · subst letter
          exact iff_of_false leftUnique.2 rightParts.2.2.2
        · by_cases marker : letter = leftMarker
          · subst letter
            exact iff_of_false oldRepeated rightParts.2.1
          · simpa [head, marker] using support letter
      exact derivesOfTailSupport
        initial leftMarker leftTail rightTail tailSupport
  · by_cases leftDoubleton :
        leftMarker = initial ∧ initial ∉ leftTail
    · have rightDoubleton := doubletonIff.mp leftDoubleton
      have leftMarkerEq := leftDoubleton.1
      have rightMarkerEq := rightDoubleton.1
      subst leftMarker
      subst rightMarker
      have tailSupport :
          ∀ letter, letter ∈ leftTail ↔ letter ∈ rightTail := by
        intro letter
        by_cases head : letter = initial
        · subst letter
          exact iff_of_false leftDoubleton.2 rightDoubleton.2
        · simpa [head] using support letter
      exact derivesOfTailSupport
        initial initial leftTail rightTail tailSupport
    · have rightNotUnique :
          ¬(initial ≠ rightMarker ∧ initial ∉ rightTail) := by
        intro unique
        exact leftUnique (uniqueIff.mpr unique)
      have rightNotDoubleton :
          ¬(rightMarker = initial ∧ initial ∉ rightTail) := by
        intro doubleton
        exact leftDoubleton (doubletonIff.mpr doubleton)
      have initialInLeft : initial ∈ leftTail := by
        apply Decidable.byContradiction
        intro absent
        have markerEq : leftMarker = initial := by
          apply Decidable.byContradiction
          intro different
          exact leftUnique ⟨Ne.symm different, absent⟩
        exact leftDoubleton ⟨markerEq, absent⟩
      have initialInRight : initial ∈ rightTail := by
        apply Decidable.byContradiction
        intro absent
        have markerEq : rightMarker = initial := by
          apply Decidable.byContradiction
          intro different
          exact rightNotUnique ⟨Ne.symm different, absent⟩
        exact rightNotDoubleton ⟨markerEq, absent⟩
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
            exact List.Mem.tail _ initialInRight
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
            exact List.Mem.tail _ initialInLeft
          · exact List.mem_cons.mpr (Or.inl marker)
          · exact List.mem_cons.mpr (Or.inr tail)
      exact
        (derivesRepeatedInitialCanonical
          initial leftMarker leftTail initialInLeft).trans <|
          (derivesOfTailSupport
            initial initial
            (leftMarker :: leftTail)
            (rightMarker :: rightTail) tailSupport).trans
            (derivesRepeatedInitialCanonical
              initial rightMarker rightTail initialInRight).symm

/-- Actual left-zero validity, rather than finite-table separation, fixes the
unreversed initial variable. -/
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

/-- Opposite-table validity is independent validity of the reversed words in
the reviewed direct `S5_203` factor. -/
theorem rightValid_reversed
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    identity.reversed.SatisfiedBy
      SemigroupBasis.CoRoots.S5_203.table.semigroup := by
  change
    identity.SatisfiedBy
      SemigroupBasis.CoRoots.S5_203.table.semigroup.opposite at valid
  exact
    (Identity.satisfiedBy_opposite_iff_reversed identity
      SemigroupBasis.CoRoots.S5_203.table.semigroup).mp valid

/-- Genuine unrestricted pair completeness with the initial-doubleton branch
kept separate and no temporary-head cancellation. -/
theorem derives_of_factor_valid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have reversedValid := rightValid_reversed identity rightValid
  have lower :=
    SemigroupBasis.CoRoots.S5_203Family.S5_203.basisFor.2
      identity.reversed reversedValid
  have same :=
    SemigroupBasis.CoRoots.S5_203.derives_sameSupportTerminalStateSignature
      lower
  rcases
      SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank044.Seed.lowerDerivation_shortOrLong
        lower with equal | ⟨leftReversedLong, rightReversedLong⟩
  · have unreversed := congrArg Word.reverse equal
    have actualEqual : identity.lhs = identity.rhs := by
      simpa [Identity.reversed] using unreversed
    rw [actualEqual]
    exact Derives.refl _
  · have leftLong : 3 ≤ identity.lhs.toList.length := by
      simpa [Identity.reversed, Word.toList_reverse] using leftReversedLong
    have rightLong : 3 ≤ identity.rhs.toList.length := by
      simpa [Identity.reversed, Word.toList_reverse] using rightReversedLong
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
                    simp [Word.toList] at leftLong
                | cons leftMarker leftTail =>
                    cases rightLetters with
                    | nil =>
                        simp [Word.toList] at rightLong
                    | cons rightMarker rightTail =>
                        exact
                          derivesPairOfReversedSignature
                            initial leftMarker rightMarker
                            leftTail rightTail same

/-- Package the pair only after the unrestricted factor proof. -/
def intersectionBasis :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := derives_of_factor_valid

/-- Genuine reusable rank-046 family seed. -/
noncomputable def normalizer :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

theorem s6_5635_representative_basis :
    BasisFor S6_5635.table.semigroup basis :=
  S6_5635.representative_basis_of_normalizer normalizer

theorem s6_5635_opposite_basis :
    BasisFor S6_5635.table.semigroup.opposite (reversedBasis basis) :=
  S6_5635.opposite_basis_of_normalizer normalizer

theorem s6_5637_representative_basis :
    BasisFor S6_5637.table.semigroup basis :=
  S6_5637.representative_basis_of_normalizer normalizer

theorem s6_5637_opposite_basis :
    BasisFor S6_5637.table.semigroup.opposite (reversedBasis basis) :=
  S6_5637.opposite_basis_of_normalizer normalizer

/-- Reviewed transport retains all explicit displayed-law derivations and
independent unrestricted target-factor theory implications. -/
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

end SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank046.Seed
