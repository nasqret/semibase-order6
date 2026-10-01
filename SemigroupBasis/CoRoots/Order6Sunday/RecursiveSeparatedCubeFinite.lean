import SemigroupBasis.CoRoots.Order6Sunday.RecursiveDepth7Delta

/-! One fixed separated-cube identity for the index-three, period-one table.
The original seven laws already derive this pair in four displayed-law edges.
The approved eight-law list and the two opposite lists inherit that fixed
witness. No arbitrary-word key, reachability or completeness field is supplied. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.RecursiveSeparatedCubeFinite

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Sunday.RecursivePublishedFinite.S6_9726

/-- x y x z x = x y x z x x, with x=0, y=1, z=2. -/
def separatedCube : Identity Nat :=
  ⟨⟨0, [1, 0, 2, 0]⟩, ⟨0, [1, 0, 2, 0, 0]⟩⟩

/-- A fixed four-edge derivation; no amended law is used. -/
theorem separatedCubeFromB7 :
    Derives basis separatedCube.lhs separatedCube.rhs := by
  have law2 : Derives basis basisLaw2.lhs basisLaw2.rhs :=
    Derives.fromBasis (by simp [basis])
  have law4 : Derives basis basisLaw4.lhs basisLaw4.rhs :=
    Derives.fromBasis (by simp [basis])
  have step0 : Derives basis ⟨0, [1, 0, 2, 0]⟩ ⟨0, [1, 0, 0, 2]⟩ :=
    Derives.symm law4
  have step1 : Derives basis ⟨0, [1, 0, 0, 2]⟩ ⟨0, [1, 0, 0, 0, 2]⟩ :=
    Derives.appendRight law2 ⟨2, []⟩
  have step2 : Derives basis ⟨0, [1, 0, 0, 0, 2]⟩ ⟨0, [1, 0, 0, 2, 0]⟩ := by
    let substitution : Nat → Word Nat := fun
      | 2 => ⟨0, [2]⟩
      | n => Word.singleton n
    exact Derives.subst law4 substitution
  have step3 : Derives basis ⟨0, [1, 0, 0, 2, 0]⟩ ⟨0, [1, 0, 2, 0, 0]⟩ :=
    Derives.appendRight law4 ⟨0, []⟩
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 step3))

theorem oppositeSeparatedCubeFromB7 :
    Derives (reversedBasis basis)
      separatedCube.reversed.lhs separatedCube.reversed.rhs :=
  separatedCubeFromB7.reverse

/-- Transport through inclusion in the unchanged approved B8. -/
theorem separatedCubeFromB8 :
    Derives RecursiveDepth7Delta.S6_9726.basis
      separatedCube.lhs separatedCube.rhs := by
  refine separatedCubeFromB7.transport ?_
  intro identity member
  apply Derives.fromBasis (e := identity)
  change identity ∈ basis ++ RecursiveDepth7Delta.S6_9726.added
  exact List.mem_append_left _ member

theorem oppositeSeparatedCubeFromB8 :
    Derives (reversedBasis RecursiveDepth7Delta.S6_9726.basis)
      separatedCube.reversed.lhs separatedCube.reversed.rhs :=
  separatedCubeFromB8.reverse

/-- Fixed table validity follows from the already recorded B7 models fact. -/
theorem separatedCubeValid : separatedCube.SatisfiedBy table.semigroup := by
  intro valuation
  exact Derives.sound tableModels separatedCubeFromB7 valuation

theorem oppositeSeparatedCubeValid :
    separatedCube.reversed.SatisfiedBy table.semigroup.opposite := by
  rw [Identity.satisfiedBy_opposite_iff_reversed, Identity.reversed_reversed]
  exact separatedCubeValid

end SemigroupBasis.CoRoots.Order6Sunday.RecursiveSeparatedCubeFinite
