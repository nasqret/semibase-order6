import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0446NilZ2Signature

/-! The exact eleven-law S6_9386 repair in Fable msg0455. These laws are
sound, but the separated-cube countermodel in the next module refutes their
completeness. The previous seven-law definition is preserved unchanged. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0455NilZ2

open SemigroupBasis

def swap00 : Identity Nat := ⟨⟨0, [1, 2, 3, 0, 2]⟩, ⟨0, [1, 2, 3, 2, 0]⟩⟩
def swap01 : Identity Nat := ⟨⟨0, [1, 0, 2, 3, 2]⟩, ⟨0, [1, 2, 0, 3, 2]⟩⟩
def swap02 : Identity Nat := ⟨⟨2, [1, 0, 2, 3, 0]⟩, ⟨2, [1, 2, 0, 3, 0]⟩⟩
def swap03 : Identity Nat := ⟨⟨0, [2, 1, 0, 3, 2]⟩, ⟨2, [0, 1, 0, 3, 2]⟩⟩
def swaps : List (Identity Nat) := [swap00, swap01, swap02, swap03]
def basis : List (Identity Nat) := Msg0446NilZ2.basis ++ swaps
def basisSHA256 : String := "3e035a150f407feea6d7f221b3d78826aeacdb91da97d02a7fa5dd21aec24186"
abbrev target := Msg0446NilZ2.table9386

theorem basis_length : basis.length = 11 := rfl

theorem old_basis_subset : ∀ identity, identity ∈ Msg0446NilZ2.basis → identity ∈ basis := by
  intro identity member
  exact List.mem_append_left swaps member

private def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

theorem swaps_models9386 : Models target.semigroup swaps :=
  FiniteCertificate.checkModels_sound target swaps toFinFour (by decide +kernel)

theorem models9386 : Models target.semigroup basis := by
  intro identity member
  rcases List.mem_append.mp member with old | added
  · exact Msg0446NilZ2.models9386 identity old
  · exact swaps_models9386 identity added

theorem oppositeModels9386 : Models target.semigroup.opposite (reversedBasis basis) :=
  models9386.oppositeReversed

/-- The four approved structural swaps support arbitrary NONEMPTY word
substitutions. This reusable algebra does not imply full reach or completeness. -/
theorem derivesSwapSubstitution (identity : Identity Nat) (member : identity ∈ swaps)
    (substitution : Nat → Word Nat) :
    Derives basis (identity.lhs.bind substitution) (identity.rhs.bind substitution) :=
  Derives.subst (Derives.fromBasis (List.mem_append_right _ member)) substitution

theorem derives_preserve_signature {left right : Word Nat}
    (derivation : Derives basis left right) : Msg0446NilZ2.SameSignature left right :=
  Msg0446NilZ2.sameSignature_of_valid9386 ⟨left, right⟩ (derivation.sound models9386)

/-- This valid identity is missing from the B11 derivation theory. -/
def separatedCube : Identity Nat := ⟨⟨0, [1, 0, 2, 0]⟩, ⟨0, [1, 0, 2, 0, 0, 0]⟩⟩

theorem separatedCube_valid9386 : separatedCube.SatisfiedBy target.semigroup := by
  have checked : Models target.semigroup [separatedCube] :=
    FiniteCertificate.checkModels_sound target [separatedCube] Msg0446NilZ2.toFinThree
      (by decide +kernel)
  exact checked separatedCube (by simp)

theorem separatedCube_sameSignature :
    Msg0446NilZ2.SameSignature separatedCube.lhs separatedCube.rhs :=
  Msg0446NilZ2.sameSignature_of_valid9386 separatedCube separatedCube_valid9386

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0455NilZ2
