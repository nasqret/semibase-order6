import SemigroupBasis.CoRoots.Order6SporadicSection11Gather

namespace SemigroupBasis.CoRoots.Order6SporadicSection11

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_107

private abbrev ListDerives :=
  S5_107.ListDerives basis

/-- Change a pseudo-compact terminal owner from `oldTerminal` to a later
repeated `pivot`. The first rewrite peels one pivot copy from its block, the
second applies (11.1c), and the third gathers the old terminal copy back into
its first block. -/
theorem listDerivesChangeTerminalOwner
    (pre left right : List Nat) (oldTerminal pivot : Nat) :
    ListDerives
      (pre ++ [oldTerminal] ++ left ++ [pivot, pivot] ++ right ++
        [oldTerminal])
      (pre ++ [oldTerminal, oldTerminal] ++ left ++ [pivot] ++ right ++
        [pivot]) := by
  have peelPivot :
      ListDerives
        (pre ++ [oldTerminal] ++ left ++ [pivot, pivot] ++ right ++
          [oldTerminal])
        (pre ++ [oldTerminal] ++ left ++ [pivot] ++ right ++
          [pivot, oldTerminal]) := by
    simpa [List.append_assoc] using
      (listDerivesGatherNonfinal
        (pre ++ [oldTerminal] ++ left) [] pivot right
        [oldTerminal] (by simp)).symm
  have switchTerminal :
      ListDerives
        (pre ++ [oldTerminal] ++ left ++ [pivot] ++ right ++
          [pivot, oldTerminal])
        (pre ++ [oldTerminal] ++ left ++ [pivot] ++ right ++
          [oldTerminal, pivot]) := by
    simpa [List.append_assoc] using
      (listDerivesTerminalSwitch
        pre [] oldTerminal pivot left right).symm
  have regatherOld :
      ListDerives
        (pre ++ [oldTerminal] ++ left ++ [pivot] ++ right ++
          [oldTerminal, pivot])
        (pre ++ [oldTerminal, oldTerminal] ++ left ++ [pivot] ++ right ++
          [pivot]) := by
    simpa [List.append_assoc] using
      listDerivesGatherNonfinal
        pre [] oldTerminal (left ++ [pivot] ++ right)
        [pivot] (by simp)
  exact peelPivot.trans (switchTerminal.trans regatherOld)

end SemigroupBasis.CoRoots.Order6SporadicSection11
