import SemigroupBasis.CoRoots.Order6Sunday.RecursiveDepth7Delta

/-! The four exact finite inputs requested by S2 for S6_6447.
Only two fixed word pairs and two three-case table actions are proved here.
The approved B12 and the owner's arbitrary-word proof remain unchanged. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Recursive6447Fixed

open SemigroupBasis
open RecursivePublishedFinite.S6_6447 (basisLaw0 basisLaw1 basisLaw3 basisLaw4 basisLaw5)

/-- The fixed square commute x x y y = y y x x, using five displayed-law edges. -/
theorem squareCommuteFromB12 :
    Derives RecursiveDepth7Delta.S6_6447.basis
      (⟨0, [0, 1, 1]⟩ : Word Nat) (⟨1, [1, 0, 0]⟩ : Word Nat) := by
  have power : Derives RecursiveDepth7Delta.S6_6447.basis basisLaw0.lhs basisLaw0.rhs :=
    Derives.fromBasis (e := basisLaw0) (by decide)
  have sandwich : Derives RecursiveDepth7Delta.S6_6447.basis basisLaw1.lhs basisLaw1.rhs :=
    Derives.fromBasis (e := basisLaw1) (by decide)
  have alternate : Derives RecursiveDepth7Delta.S6_6447.basis basisLaw3.lhs basisLaw3.rhs :=
    Derives.fromBasis (e := basisLaw3) (by decide)
  have square : Derives RecursiveDepth7Delta.S6_6447.basis basisLaw4.lhs basisLaw4.rhs :=
    Derives.fromBasis (e := basisLaw4) (by decide)
  have insert : Derives RecursiveDepth7Delta.S6_6447.basis basisLaw5.lhs basisLaw5.rhs :=
    Derives.fromBasis (e := basisLaw5) (by decide)
  have step0 : Derives RecursiveDepth7Delta.S6_6447.basis
      ⟨0, [0, 1, 1]⟩ ⟨0, [1, 0, 1]⟩ := alternate
  have step1 : Derives RecursiveDepth7Delta.S6_6447.basis
      ⟨0, [1, 0, 1]⟩ ⟨0, [0, 1, 0, 1]⟩ :=
    Derives.appendRight sandwich ⟨1, []⟩
  have step2 : Derives RecursiveDepth7Delta.S6_6447.basis
      ⟨0, [0, 1, 0, 1]⟩ ⟨1, [0, 0, 0, 1]⟩ := by
    let substitution : Nat → Word Nat := fun
      | 2 => Word.singleton 0
      | n => Word.singleton n
    exact Derives.subst insert substitution
  have step3 : Derives RecursiveDepth7Delta.S6_6447.basis
      ⟨1, [0, 0, 0, 1]⟩ ⟨1, [0, 0, 1]⟩ :=
    Derives.appendRight (Derives.prepend ⟨1, []⟩ power.symm) ⟨1, []⟩
  have step4 : Derives RecursiveDepth7Delta.S6_6447.basis
      ⟨1, [0, 0, 1]⟩ ⟨1, [1, 0, 0]⟩ := by
    let substitution : Nat → Word Nat := fun
      | 0 => Word.singleton 1
      | 1 => Word.singleton 0
      | n => Word.singleton n
    exact (Derives.subst square substitution).symm
  exact step0.trans (step1.trans (step2.trans (step3.trans step4)))

/-- The fixed empty-prefix mixed pair x x y z y = x y x z y. -/
theorem mixedEmptyPrefixFromB12 :
    Derives RecursiveDepth7Delta.S6_6447.basis
      (⟨0, [0, 1, 2, 1]⟩ : Word Nat) (⟨0, [1, 0, 2, 1]⟩ : Word Nat) := by
  have power : Derives RecursiveDepth7Delta.S6_6447.basis basisLaw0.lhs basisLaw0.rhs :=
    Derives.fromBasis (e := basisLaw0) (by decide)
  have sandwich : Derives RecursiveDepth7Delta.S6_6447.basis basisLaw1.lhs basisLaw1.rhs :=
    Derives.fromBasis (e := basisLaw1) (by decide)
  have inner : Derives RecursiveDepth7Delta.S6_6447.basis
      RecursiveDepth7Delta.S6_6447.addedLaw0.lhs
      RecursiveDepth7Delta.S6_6447.addedLaw0.rhs :=
    Derives.fromBasis (e := RecursiveDepth7Delta.S6_6447.addedLaw0) (by decide)
  have step0 : Derives RecursiveDepth7Delta.S6_6447.basis
      ⟨0, [0, 1, 2, 1]⟩ ⟨0, [0, 0, 1, 2, 1]⟩ :=
    Derives.appendRight power ⟨1, [2, 1]⟩
  have step1 : Derives RecursiveDepth7Delta.S6_6447.basis
      ⟨0, [0, 0, 1, 2, 1]⟩ ⟨0, [0, 1, 0, 2, 1]⟩ := by
    let substitution : Nat → Word Nat := fun
      | 0 => Word.singleton 0
      | 1 => Word.singleton 0
      | 2 => Word.singleton 1
      | 3 => Word.singleton 2
      | n => Word.singleton n
    exact Derives.subst inner substitution
  have step2 : Derives RecursiveDepth7Delta.S6_6447.basis
      ⟨0, [0, 1, 0, 2, 1]⟩ ⟨0, [1, 0, 2, 1]⟩ :=
    Derives.appendRight sandwich.symm ⟨2, [1]⟩
  exact step0.trans (step1.trans step2)

theorem highStepControl (n : Fin 3) :
    RecursivePublishedFinite.S6_6447.mul
      (if n.val = 0 then (5 : Fin 6) else if n.val = 1 then 4 else 3) 4 =
      (if n.val = 0 then (4 : Fin 6) else 3) := by
  decide +revert

theorem lowStepControl (n : Fin 3) :
    RecursivePublishedFinite.S6_6447.mul
      (if n.val = 0 then (2 : Fin 6) else if n.val = 1 then 1 else 0) 4 =
      (if n.val = 0 then (1 : Fin 6) else 0) := by
  decide +revert

end SemigroupBasis.CoRoots.Order6Sunday.Recursive6447Fixed
