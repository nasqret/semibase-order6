import SemigroupBasis.CoRoots.S5_196
import SemigroupBasis.CoRoots.Order6FactorIntersectionSpecialRoots
import SemigroupBasis.Examples.CommutativeParityThree

namespace SemigroupBasis
namespace CoRoots
namespace Order6FactorPairS2S5196

open SemigroupBasis.Examples
open Order6FactorIntersectionSpecialRoots.Common

private abbrev candidateBasis : List (Identity Nat) :=
  [ Identity.mk (Word.mk 0 [0, 0]) (Word.mk 0 [0, 0, 0, 0]),
    Identity.mk (Word.mk 0 [0, 0, 0, 1]) (Word.mk 0 [0, 1]),
    Identity.mk (Word.mk 0 [0, 0, 1, 0]) (Word.mk 0 [1, 0]),
    Identity.mk (Word.mk 0 [0, 0, 1, 2]) (Word.mk 0 [1, 2]),
    Identity.mk (Word.mk 0 [0, 1, 0]) (Word.mk 0 [1, 1, 1]),
    Identity.mk (Word.mk 0 [0, 1, 1]) (Word.mk 0 [1, 1, 0]),
    Identity.mk (Word.mk 0 [0, 1, 1, 1]) (Word.mk 0 [1, 0]),
    Identity.mk (Word.mk 0 [1, 0]) (Word.mk 0 [1, 1, 1, 0]),
    Identity.mk (Word.mk 0 [1, 0]) (Word.mk 1 [0, 0]),
    Identity.mk (Word.mk 0 [1, 2]) (Word.mk 1 [0, 2]) ]

private theorem prefixSwap (u v q : Word Nat) :
    Derives candidateBasis ((u ++ v) ++ q) ((v ++ u) ++ q) := by
  apply Order6FactorIntersectionSpecialRoots.Common.derivesPrefixSwap (basis := candidateBasis)
      (xyz := Word.mk 0 [1, 2]) (yxz := Word.mk 1 [0, 2]) rfl rfl
  simp [candidateBasis]

private theorem terminalSwitch (u v : Word Nat) :
    Derives candidateBasis (((u ++ u) ++ v) ++ v)
      (((u ++ v) ++ v) ++ u) := by
  apply Order6FactorIntersectionSpecialRoots.Common.derivesRepeatedFinalSwitch (basis := candidateBasis)
      (xxyy := Word.mk 0 [0, 1, 1])
      (xyyx := Word.mk 0 [1, 1, 0]) rfl rfl
  simp [candidateBasis]

private def instantiateThree
    (u v q : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => q
  | n + 3 => Word.singleton (n + 3)

private theorem insertTwoCopies
    (u v q : Word Nat) :
    Derives candidateBasis ((u ++ v) ++ q)
      ((((u ++ u) ++ u) ++ v) ++ q) := by
  have base : Derives candidateBasis
      (Word.mk 0 [0, 0, 1, 2]) (Word.mk 0 [1, 2]) :=
    Derives.fromBasis (e := Identity.mk (Word.mk 0 [0, 0, 1, 2])
      (Word.mk 0 [1, 2])) (by simp [candidateBasis])
  have h := Derives.subst base (instantiateThree u v q)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h.symm

private theorem insertProtectedPair
    (letters : List Nat) (final marker : Nat)
    (prefixLong : 2 ≤ letters.length)
    (markerIn : marker ∈ letters) :
    Derives candidateBasis
      (wordOfPrefixFinal letters final)
      (wordOfPrefixFinal (marker :: marker :: letters) final) := by
  have restNonempty : letters.erase marker ≠ [] := by
    intro h
    have len := List.length_erase_of_mem markerIn
    rw [h] at len
    simp at len
    omega
  obtain ⟨next, tail, restEq⟩ := List.exists_cons_of_ne_nil restNonempty
  have expose : letters.Perm (marker :: letters.erase marker) :=
    List.perm_cons_erase markerIn
  have first :=
    Order6FactorIntersectionSpecialRoots.Common.derivesPrefixPermutation
      prefixSwap expose final
  have middle : Derives candidateBasis
      (wordOfPrefixFinal (marker :: next :: tail) final)
      (wordOfPrefixFinal (marker :: marker :: marker :: next :: tail) final) := by
    simpa [wordOfPrefixFinal, Word.singleton, Word.append,
      Word.append_assoc] using
      insertTwoCopies (Word.singleton marker) (Word.singleton next)
        (wordOfPrefixFinal tail final)
  have restorePerm :
      (marker :: marker :: marker :: next :: tail).Perm
        (marker :: marker :: letters) := by
    apply List.Perm.cons marker
    apply List.Perm.cons marker
    simpa [restEq] using expose.symm
  have last :=
    Order6FactorIntersectionSpecialRoots.Common.derivesPrefixPermutation
      prefixSwap restorePerm final
  exact first.trans (by simpa [restEq] using middle.trans last)

private theorem contractThreeInPrefix
    (x marker final : Nat) (remainder : List Nat) :
    Derives candidateBasis
      (wordOfPrefixFinal
        (marker :: marker :: x :: x :: x :: remainder) final)
      (wordOfPrefixFinal (marker :: marker :: x :: remainder) final) := by
  have p1 : (marker :: marker :: x :: x :: x :: remainder).Perm
      (x :: x :: x :: marker :: marker :: remainder) := by
    grind
  have first := Order6FactorIntersectionSpecialRoots.Common.derivesPrefixPermutation
    prefixSwap p1 final
  have middle : Derives candidateBasis
      (wordOfPrefixFinal (x :: x :: x :: marker :: marker :: remainder) final)
      (wordOfPrefixFinal (x :: marker :: marker :: remainder) final) := by
    simpa [wordOfPrefixFinal, Word.singleton, Word.append,
      Word.append_assoc] using
      (insertTwoCopies (Word.singleton x) (Word.singleton marker)
        (wordOfPrefixFinal (marker :: remainder) final)).symm
  have p2 : (x :: marker :: marker :: remainder).Perm
      (marker :: marker :: x :: remainder) := by
    grind
  have last := Order6FactorIntersectionSpecialRoots.Common.derivesPrefixPermutation
    prefixSwap p2 final
  exact first.trans (middle.trans last)

private theorem normalizeHeadBehindPair
    (x : Nat) (reduced : List Nat) (final marker : Nat)
    (countLe : reduced.count x ≤ 2) :
    Derives candidateBasis
      (wordOfPrefixFinal (marker :: marker :: x :: reduced) final)
      (wordOfPrefixFinal
        (marker :: marker ::
          (if reduced.count x < 2 then x :: reduced else reduced.erase x))
        final) := by
  by_cases hcount : reduced.count x < 2
  · simp only [if_pos hcount]
    exact Derives.refl _
  · simp only [if_neg hcount]
    have countEq : reduced.count x = 2 := by omega
    let remainder := (reduced.erase x).erase x
    have extracted : reduced.Perm (x :: x :: remainder) := by
      simpa [remainder, List.replicate_succ] using
        Order6FactorIntersectionSpecialRoots.Common.perm_extractCopies x 2 reduced countEq
    have arrangePerm :
        (marker :: marker :: x :: reduced).Perm
          (marker :: marker :: x :: x :: x :: remainder) :=
      List.Perm.cons marker (List.Perm.cons marker (List.Perm.cons x extracted))
    have arranged := Order6FactorIntersectionSpecialRoots.Common.derivesPrefixPermutation prefixSwap arrangePerm final
    have contracted := contractThreeInPrefix x marker final remainder
    have eraseCount : (reduced.erase x).count x = 1 := by
      rw [List.count_erase_self, countEq]
    have eraseHasX : x ∈ reduced.erase x :=
      List.count_pos_iff.mp (by omega)
    have restorePerm :
        (marker :: marker :: x :: remainder).Perm
          (marker :: marker :: reduced.erase x) := by
      apply List.Perm.cons
      apply List.Perm.cons
      simpa [remainder] using (List.perm_cons_erase eraseHasX).symm
    have restored := Order6FactorIntersectionSpecialRoots.Common.derivesPrefixPermutation prefixSwap restorePerm final
    exact arranged.trans (contracted.trans restored)

private theorem normalizeBehindPair
    (letters : List Nat) (final marker : Nat) :
    Derives candidateBasis
      (wordOfPrefixFinal (marker :: marker :: letters) final)
      (wordOfPrefixFinal
        (marker :: marker :: positiveParityReduce letters) final) := by
  induction letters with
  | nil =>
      simpa [positiveParityReduce] using
        (Derives.refl (basis := candidateBasis)
          (wordOfPrefixFinal [marker, marker] final))
  | cons head tail ih =>
      have p1 : (marker :: marker :: head :: tail).Perm
          (head :: marker :: marker :: tail) := by grind
      have first := Order6FactorIntersectionSpecialRoots.Common.derivesPrefixPermutation
        prefixSwap p1 final
      have contextual : Derives candidateBasis
          (wordOfPrefixFinal (head :: marker :: marker :: tail) final)
          (wordOfPrefixFinal
            (head :: marker :: marker :: positiveParityReduce tail) final) := by
        simpa [wordOfPrefixFinal, Word.singleton, Word.append_assoc] using
          Derives.prepend (Word.singleton head) ih
      have p2 : (head :: marker :: marker :: positiveParityReduce tail).Perm
          (marker :: marker :: head :: positiveParityReduce tail) := by grind
      have second := Order6FactorIntersectionSpecialRoots.Common.derivesPrefixPermutation
        prefixSwap p2 final
      have finish := normalizeHeadBehindPair head (positiveParityReduce tail)
        final marker (positiveParityReduce_count_le_two head tail)
      simpa only [positiveParityReduce] using
        first.trans (contextual.trans (second.trans finish))

private theorem derivesProtectedParityNormal
    (letters : List Nat) (final marker : Nat)
    (prefixLong : 2 ≤ letters.length)
    (markerIn : marker ∈ letters) :
    Derives candidateBasis
      (wordOfPrefixFinal letters final)
      (wordOfPrefixFinal
        (marker :: marker :: positiveParityReduce letters) final) := by
  exact (insertProtectedPair letters final marker prefixLong markerIn).trans
    (normalizeBehindPair letters final marker)

private theorem derivesSameFinal
    (leftPrefix rightPrefix : List Nat) (final : Nat)
    (leftLong : 2 ≤ leftPrefix.length)
    (rightLong : 2 ≤ rightPrefix.length)
    (support : ∀ z, z ∈ leftPrefix ↔ z ∈ rightPrefix)
    (parity : ∀ z,
      (leftPrefix ++ [final]).count z % 2 =
      (rightPrefix ++ [final]).count z % 2) :
    Derives candidateBasis
      (wordOfPrefixFinal leftPrefix final)
      (wordOfPrefixFinal rightPrefix final) := by
  obtain ⟨marker, markerIn⟩ : ∃ marker, marker ∈ leftPrefix := by
    apply List.length_pos_iff_exists_mem.mp
    omega
  have leftNorm := derivesProtectedParityNormal leftPrefix final marker
    leftLong markerIn
  have markerRight : marker ∈ rightPrefix := (support marker).mp markerIn
  have rightNorm := derivesProtectedParityNormal rightPrefix final marker
    rightLong markerRight
  have prefixParity : ∀ z, leftPrefix.count z % 2 = rightPrefix.count z % 2 := by
    intro z
    have hp := parity z
    simp only [List.count_append, List.count_cons, List.count_nil,
      Nat.add_zero] at hp
    by_cases hz : final = z
    · subst z
      simp at hp
      omega
    · simp [hz] at hp
      exact hp
  have reducedPerm := positiveParityReduce_perm support prefixParity
  have protectedPerm :
      (marker :: marker :: positiveParityReduce leftPrefix).Perm
        (marker :: marker :: positiveParityReduce rightPrefix) :=
    List.Perm.cons marker (List.Perm.cons marker reducedPerm)
  have middle := Order6FactorIntersectionSpecialRoots.Common.derivesPrefixPermutation
    prefixSwap protectedPerm final
  exact leftNorm.trans (middle.trans rightNorm.symm)

private theorem splitPrefix_length (word : Word Nat) :
    (splitPrefixFinal word).1.length + 1 = word.toList.length := by
  have h := congrArg (fun w => w.toList.length) (wordOfPrefixFinal_split word)
  simpa [toList_wordOfPrefixFinal] using h

private theorem prefixSignature
    {leftPrefix rightPrefix : List Nat}
    {leftFinal rightFinal : Nat}
    (support : ∀ z,
      (z ∈ leftPrefix ∨ z = leftFinal) ↔
        (z ∈ rightPrefix ∨ z = rightFinal))
    (simple : ∀ z,
      (leftFinal = z ∧ z ∉ leftPrefix) ↔
        (rightFinal = z ∧ z ∉ rightPrefix)) :
    (∀ z, z ∈ leftPrefix ↔ z ∈ rightPrefix) ∧
      ((leftFinal = rightFinal ∧ leftFinal ∉ leftPrefix ∧
          rightFinal ∉ rightPrefix) ∨
        (leftFinal ∈ leftPrefix ∧ rightFinal ∈ rightPrefix)) := by
  grind

private theorem splitSignature
    (left right : Word Nat)
    (support : S5_196.SameSupport left right)
    (simple : S5_196.SameSimpleFinal left right) :
    (∀ z, z ∈ (splitPrefixFinal left).1 ↔
      z ∈ (splitPrefixFinal right).1) ∧
    (((splitPrefixFinal left).2 = (splitPrefixFinal right).2 ∧
       (splitPrefixFinal left).2 ∉ (splitPrefixFinal left).1 ∧
       (splitPrefixFinal right).2 ∉ (splitPrefixFinal right).1) ∨
     ((splitPrefixFinal left).2 ∈ (splitPrefixFinal left).1 ∧
       (splitPrefixFinal right).2 ∈ (splitPrefixFinal right).1)) := by
  apply prefixSignature
  · intro z
    have same := support z
    rw [← wordOfPrefixFinal_split left, ← wordOfPrefixFinal_split right,
      toList_wordOfPrefixFinal, toList_wordOfPrefixFinal] at same
    simpa using same
  · exact simple

private theorem alignRepeatedFinal
    (letters : List Nat) (oldFinal newFinal : Nat)
    (prefixLong : 2 ≤ letters.length)
    (oldIn : oldFinal ∈ letters)
    (newIn : newFinal ∈ letters) :
    ∃ alignedPrefix,
      Derives candidateBasis
        (wordOfPrefixFinal letters oldFinal)
        (wordOfPrefixFinal alignedPrefix newFinal) ∧
      (∀ z, z ∈ letters ++ [oldFinal] ↔
        z ∈ alignedPrefix ++ [newFinal]) ∧
      (∀ z, (letters ++ [oldFinal]).count z % 2 =
        (alignedPrefix ++ [newFinal]).count z % 2) ∧
      newFinal ∈ alignedPrefix ∧ 2 ≤ alignedPrefix.length := by
  have inserted := insertProtectedPair letters oldFinal newFinal prefixLong newIn
  have oldExpanded : oldFinal ∈ newFinal :: newFinal :: letters := by simp [oldIn]
  have twoNew : 2 ≤ (newFinal :: newFinal :: letters).count newFinal := by simp
  obtain ⟨switched, switchedDeriv, switchedPerm, switchedIn⟩ :=
    Order6FactorIntersectionSpecialRoots.Common.switchRepeatedFinal
      prefixSwap terminalSwitch (newFinal :: newFinal :: letters)
      oldFinal newFinal oldExpanded twoNew
  refine ⟨switched, inserted.trans switchedDeriv, ?_, ?_, switchedIn, ?_⟩
  · intro z
    have hp : z ∈ (newFinal :: newFinal :: letters) ++ [oldFinal] ↔
        z ∈ switched ++ [newFinal] := switchedPerm.mem_iff
    simp only [List.mem_append, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at hp ⊢
    grind
  · intro z
    have hc := switchedPerm.count_eq z
    simp only [List.count_append, List.count_cons, List.count_nil,
      Nat.add_zero] at hc ⊢
    omega
  · have newCount := switchedPerm.count_eq newFinal
    simp only [List.count_append, List.count_cons, List.count_nil,
      Nat.add_zero] at newCount
    have positive := List.count_pos_iff.mpr newIn
    have bound : switched.count newFinal ≤ switched.length :=
      List.count_le_length
    by_cases same : oldFinal = newFinal <;> simp [same] at newCount
    · omega
    · omega

theorem derivesLongOfSignatureParity
    (left right : Word Nat)
    (leftLong : 3 <= left.toList.length)
    (rightLong : 3 <= right.toList.length)
    (support : S5_196.SameSupport left right)
    (simple : S5_196.SameSimpleFinal left right)
    (parity : forall z : Nat,
      left.toList.count z % 2 = right.toList.count z % 2) :
    Derives
      ([
        Identity.mk (Word.mk 0 [0, 0]) (Word.mk 0 [0, 0, 0, 0]),
        Identity.mk (Word.mk 0 [0, 0, 0, 1]) (Word.mk 0 [0, 1]),
        Identity.mk (Word.mk 0 [0, 0, 1, 0]) (Word.mk 0 [1, 0]),
        Identity.mk (Word.mk 0 [0, 0, 1, 2]) (Word.mk 0 [1, 2]),
        Identity.mk (Word.mk 0 [0, 1, 0]) (Word.mk 0 [1, 1, 1]),
        Identity.mk (Word.mk 0 [0, 1, 1]) (Word.mk 0 [1, 1, 0]),
        Identity.mk (Word.mk 0 [0, 1, 1, 1]) (Word.mk 0 [1, 0]),
        Identity.mk (Word.mk 0 [1, 0]) (Word.mk 0 [1, 1, 1, 0]),
        Identity.mk (Word.mk 0 [1, 0]) (Word.mk 1 [0, 0]),
        Identity.mk (Word.mk 0 [1, 2]) (Word.mk 1 [0, 2])
      ] : List (Identity Nat)) left right := by
  have sig := splitSignature left right support simple
  have leftPrefixLong : 2 ≤ (splitPrefixFinal left).1.length := by
    have h := splitPrefix_length left
    omega
  have rightPrefixLong : 2 ≤ (splitPrefixFinal right).1.length := by
    have h := splitPrefix_length right
    omega
  rcases sig.2 with simpleFinal | repeatedFinal
  · have fullParity : ∀ z,
        ((splitPrefixFinal left).1 ++ [(splitPrefixFinal left).2]).count z % 2 =
        ((splitPrefixFinal right).1 ++ [(splitPrefixFinal left).2]).count z % 2 := by
      intro z
      have hp := parity z
      rw [← wordOfPrefixFinal_split left,
        ← wordOfPrefixFinal_split right] at hp
      simp only [toList_wordOfPrefixFinal] at hp
      simpa [simpleFinal.1] using hp
    have d := derivesSameFinal
      (splitPrefixFinal left).1 (splitPrefixFinal right).1
      (splitPrefixFinal left).2 leftPrefixLong rightPrefixLong sig.1 fullParity
    rw [wordOfPrefixFinal_split left] at d
    have rightEq :
        wordOfPrefixFinal (splitPrefixFinal right).1
          (splitPrefixFinal left).2 = right := by
      rw [simpleFinal.1, wordOfPrefixFinal_split]
    rw [rightEq] at d
    exact d
  · have newInLeft :
        (splitPrefixFinal right).2 ∈ (splitPrefixFinal left).1 :=
      (sig.1 _).mpr repeatedFinal.2
    obtain ⟨aligned, alignDeriv, alignSupport, alignParity,
        alignedRepeated, alignedLong⟩ :=
      alignRepeatedFinal (splitPrefixFinal left).1
        (splitPrefixFinal left).2 (splitPrefixFinal right).2
        leftPrefixLong repeatedFinal.1 newInLeft
    have alignedSupport : ∀ z,
        z ∈ aligned ↔ z ∈ (splitPrefixFinal right).1 := by
      intro z
      have ha := alignSupport z
      simp only [List.mem_append, List.mem_singleton] at ha
      constructor
      · intro hz
        have leftFull :
            z ∈ (splitPrefixFinal left).1 ∨
              z = (splitPrefixFinal left).2 := ha.mpr (Or.inl hz)
        rcases leftFull with hp | hf
        · exact (sig.1 z).mp hp
        · subst z
          exact (sig.1 _).mp repeatedFinal.1
      · intro hz
        have leftPrefix : z ∈ (splitPrefixFinal left).1 :=
          (sig.1 z).mpr hz
        exact (ha.mp (Or.inl leftPrefix)).elim id
          (fun eq => eq ▸ alignedRepeated)
    have alignedToRightParity : ∀ z,
        (aligned ++ [(splitPrefixFinal right).2]).count z % 2 =
        ((splitPrefixFinal right).1 ++ [(splitPrefixFinal right).2]).count z % 2 := by
      intro z
      have hp := parity z
      rw [← wordOfPrefixFinal_split left,
        ← wordOfPrefixFinal_split right] at hp
      simp only [toList_wordOfPrefixFinal] at hp
      exact (alignParity z).symm.trans hp
    have finish := derivesSameFinal aligned (splitPrefixFinal right).1
      (splitPrefixFinal right).2 alignedLong rightPrefixLong
      alignedSupport alignedToRightParity
    have total := alignDeriv.trans finish
    rw [wordOfPrefixFinal_split left, wordOfPrefixFinal_split right] at total
    exact total

end Order6FactorPairS2S5196
end CoRoots
end SemigroupBasis