import SemigroupBasis.CoRoots.S5_441ParityEnvelopeReplay

namespace SemigroupBasis.CoRoots.S5_441

open SemigroupBasis
open SemigroupBasis.Examples

private theorem listDerivesRightEnvelopePowerWithOptionalInterior
    (endpoint : Nat) (interior : List Nat) :
    ListDerives
      ([endpoint] ++ interior ++ [endpoint])
      ([endpoint] ++ interior ++ [endpoint, endpoint, endpoint]) := by
  cases interior with
  | nil =>
      simpa [Word.toList_append, List.append_assoc] using
        (ListDerives.ofWord
          (derivesBlockSquarePower (Word.singleton endpoint)))
  | cons interiorHead interiorTail =>
      let interiorWord :=
        S5_107.listWordOfCons interiorHead interiorTail
      simpa [interiorWord, S5_107.listWordOfCons, Word.toList,
        Word.toList_append, List.append_assoc] using
          (ListDerives.ofWord
            (derivesRightEnvelopePower
              (Word.singleton endpoint) interiorWord))

private theorem listDerivesAttachmentXYYZXWithOptionalMiddle
    (x y : Nat) (middle : List Nat) :
    ListDerives
      ([x, x, y] ++ middle ++ [y])
      ([x, y, y] ++ middle ++ [x]) := by
  cases middle with
  | nil =>
      simpa [Word.toList_append, List.append_assoc] using
        (ListDerives.ofWord
          (derivesSquareFinalSwitch
            (Word.singleton x) (Word.singleton y)))
  | cons middleHead middleTail =>
      let middleWord :=
        S5_107.listWordOfCons middleHead middleTail
      simpa [middleWord, S5_107.listWordOfCons, Word.toList,
        Word.toList_append, List.append_assoc] using
          (ListDerives.ofWord
            (derivesAttachmentXYYZX
              (Word.singleton x) (Word.singleton y) middleWord))

private theorem listDerivesLeftEnvelopePowerContraction
    (endpoint : Nat) (middle : List Nat)
    (middleNonempty : middle ≠ []) :
    ListDerives
      ([endpoint, endpoint, endpoint] ++ middle ++ [endpoint])
      ([endpoint] ++ middle ++ [endpoint]) := by
  obtain ⟨middleHead, middleTail, rfl⟩ :=
    List.exists_cons_of_ne_nil middleNonempty
  let middleWord :=
    S5_107.listWordOfCons middleHead middleTail
  simpa [middleWord, S5_107.listWordOfCons, Word.toList,
    Word.toList_append, List.append_assoc] using
      ListDerives.symm
        (ListDerives.ofWord
          (derivesLeftEnvelopePower
            (Word.singleton endpoint) middleWord))

/-- Unconditionally combine two adjacent closed parity envelopes:

`a p a b q b -> a p b b q a`.

The first envelope is expanded by two endpoint copies. One expanded copy is
retained before an attachment rewrite on `a a b q b`; the resulting outer
`a`-envelope is permuted so that its three leading endpoint copies can be
contracted back to one. -/
theorem listDerivesAdjacentParityEnvelopeCombine
    (a b : Nat) (p q : List Nat) :
    ListDerives
      ([a] ++ p ++ [a] ++ [b] ++ q ++ [b])
      ([a] ++ p ++ [b, b] ++ q ++ [a]) := by
  have expand :
      ListDerives
        ([a] ++ p ++ [a] ++ [b] ++ q ++ [b])
        ([a] ++ p ++ [a, a, a] ++ [b] ++ q ++ [b]) := by
    simpa [List.append_assoc] using
      ListDerives.append
        (listDerivesRightEnvelopePowerWithOptionalInterior a p)
        ([b] ++ q ++ [b])
  have attach :
      ListDerives
        ([a] ++ p ++ [a, a, a] ++ [b] ++ q ++ [b])
        ([a] ++ p ++ [a, a] ++ [b, b] ++ q ++ [a]) := by
    simpa [List.append_assoc] using
      ListDerives.prepend
        ([a] ++ p ++ [a])
        (listDerivesAttachmentXYYZXWithOptionalMiddle a b q)
  have interiorPermutation :
      (p ++ [a, a] ++ [b, b] ++ q).Perm
        ([a, a] ++ p ++ [b, b] ++ q) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append, List.count_cons, List.count_nil]
    omega
  have arrange :
      ListDerives
        ([a] ++ p ++ [a, a] ++ [b, b] ++ q ++ [a])
        ([a, a, a] ++ p ++ [b, b] ++ q ++ [a]) := by
    simpa [parityEnvelopeRender, List.append_assoc] using
      listDerivesParityEnvelopeInteriorPermutation
        a [] interiorPermutation
  have contract :
      ListDerives
        ([a, a, a] ++ p ++ [b, b] ++ q ++ [a])
        ([a] ++ p ++ [b, b] ++ q ++ [a]) := by
    have middleNonempty :
        p ++ [b, b] ++ q ≠ [] := by
      simp
    simpa [List.append_assoc] using
      listDerivesLeftEnvelopePowerContraction
        a (p ++ [b, b] ++ q) middleNonempty
  exact
    ListDerives.trans expand
      (ListDerives.trans attach
        (ListDerives.trans arrange contract))

/-- Apply the unconditional adjacent-envelope combine under arbitrary list
contexts. -/
theorem listDerivesAdjacentParityEnvelopeCombineContext
    (pre suffix : List Nat)
    (a b : Nat) (p q : List Nat) :
    ListDerives
      (pre ++ [a] ++ p ++ [a] ++ [b] ++ q ++ [b] ++ suffix)
      (pre ++ [a] ++ p ++ [b, b] ++ q ++ [a] ++ suffix) := by
  simpa [List.append_assoc] using
    ListDerives.context pre suffix
      (listDerivesAdjacentParityEnvelopeCombine a b p q)

end SemigroupBasis.CoRoots.S5_441
