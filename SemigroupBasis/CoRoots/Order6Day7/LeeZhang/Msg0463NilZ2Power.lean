import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0463NilZ2Basis
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0463TriplePowerCore
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0463CapThreeBank

/-! The actual B12 adapter to the proved three-law power core and generic
cap-three bank alignment. Every algebraic capability is discharged here;
none is stamped or imported from a stronger M18 power law. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0463NilZ2

open SemigroupBasis

theorem coreBasisDerivable : ∀ identity, identity ∈ TriplePowerCore.basis →
    Derives basis identity.lhs identity.rhs := by
  intro identity member
  simp only [TriplePowerCore.basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact Derives.fromBasis (e := TriplePowerCore.cubeLaw) (by decide)
  · exact Derives.fromBasis (e := TriplePowerCore.centralLaw) (by decide)
  · exact Derives.fromBasis (e := TriplePowerCore.separatedLaw) (by decide)

theorem transportCoreList {left right : List Nat}
    (derivation : S5_107.ListDerives TriplePowerCore.basis left right) :
    S5_107.ListDerives basis left right := by
  cases derivation with
  | empty => exact S5_107.ListDerives.empty
  | words wordDerivation => exact S5_107.ListDerives.words (wordDerivation.transport coreBasisDerivable)

theorem listDerivesAppendPairOfCountGeThree (letters : List Nat) (letter : Nat)
    (triple : 3 ≤ letters.count letter) :
    S5_107.ListDerives basis letters (letters ++ [letter, letter]) :=
  transportCoreList (TriplePowerCore.listDerivesAppendPairOfCountGeThree letters letter triple)

theorem listDerives_preserve_caps {left right : List Nat}
    (derivation : S5_107.ListDerives basis left right) : CapThreeBank.SameCaps left right := by
  cases derivation with
  | empty => exact fun _ => rfl
  | words wordDerivation =>
      exact fun letter => (derives_preserve_signature wordDerivation).counts letter

def bankRules : CapThreeBank.Rules basis where
  centralPair := fun letter payload => transportCoreList (TriplePowerCore.listDerivesPairAcross letter payload)
  appendPairAtThree := listDerivesAppendPairOfCountGeThree
  preservesCounts := listDerives_preserve_caps

theorem listDerivesAlignBanks (stem left right : List Nat)
    (same : CapThreeBank.SameCaps
      (stem ++ S5_254.renderSquareBank left) (stem ++ S5_254.renderSquareBank right)) :
    S5_107.ListDerives basis
      (stem ++ S5_254.renderSquareBank left) (stem ++ S5_254.renderSquareBank right) :=
  CapThreeBank.align bankRules stem left right same

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0463NilZ2
