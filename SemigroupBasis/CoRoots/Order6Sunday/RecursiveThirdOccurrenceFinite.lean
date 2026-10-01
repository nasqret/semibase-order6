import SemigroupBasis.CoRoots.Order6Sunday.RecursiveDepth7Delta

/-! The exact fixed third-occurrence input requested by S2 in msg0468.
Two uses of the original law xyxxz=xyxzx suffice; the approved B8 is unchanged.
Substitution into arbitrary contexts remains the consumer's responsibility. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.RecursiveThirdOccurrenceFinite

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Sunday.RecursivePublishedFinite.S6_9726

/-- The fixed pair x y x z x t = x y x z t x, with x=0, y=1, z=2, t=3. -/
theorem thirdOccurrenceTransportFromB8 :
    Derives RecursiveDepth7Delta.S6_9726.basis
      (⟨0, [1, 0, 2, 0, 3]⟩ : Word Nat)
      (⟨0, [1, 0, 2, 3, 0]⟩ : Word Nat) := by
  have law4 : Derives RecursiveDepth7Delta.S6_9726.basis
      basisLaw4.lhs basisLaw4.rhs := by
    apply Derives.fromBasis
    change basisLaw4 ∈ basis ++ RecursiveDepth7Delta.S6_9726.added
    exact List.mem_append_left _ (by simp [basis])
  have step0 : Derives RecursiveDepth7Delta.S6_9726.basis
      ⟨0, [1, 0, 2, 0, 3]⟩ ⟨0, [1, 0, 0, 2, 3]⟩ :=
    Derives.appendRight (Derives.symm law4) ⟨3, []⟩
  have step1 : Derives RecursiveDepth7Delta.S6_9726.basis
      ⟨0, [1, 0, 0, 2, 3]⟩ ⟨0, [1, 0, 2, 3, 0]⟩ := by
    let substitution : Nat → Word Nat := fun
      | 2 => ⟨2, [3]⟩
      | n => Word.singleton n
    exact Derives.subst law4 substitution
  exact Derives.trans step0 step1

end SemigroupBasis.CoRoots.Order6Sunday.RecursiveThirdOccurrenceFinite
