import SemigroupBasis.CoRoots.Order6Sunday.Msg0514RepairedSixteenLawFinite

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6Day15.B16.Reach

open SemigroupBasis.CoRoots.Order6Sunday.Msg0514RepairedSixteenLawFinite

theorem squareMove : Derives basis (Word.mk 0 [0, 1, 1]) (Word.mk 1 [1, 0, 0, 1, 1]) := by
  have h0 : Derives basis (Word.mk 0 [0, 1, 1]) (Word.mk 0 [0, 1, 1, 1]) := by
    have member : basisLaw0 ∈ basis := by decide
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 1 [1]) (Word.mk 1 [1, 1]) := base.subst (fun n => if n = 0 then (Word.mk 1 []) else Word.singleton 0)
    exact Derives.prepend (Word.mk 0 [0]) (inst)
  have h1 : Derives basis (Word.mk 0 [0, 1, 1, 1]) (Word.mk 0 [0, 1, 1, 1, 1]) := by
    have member : basisLaw0 ∈ basis := by decide
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 1 [1]) (Word.mk 1 [1, 1]) := base.subst (fun n => if n = 0 then (Word.mk 1 []) else Word.singleton 0)
    exact Derives.appendRight (Derives.prepend (Word.mk 0 [0]) (inst)) (Word.mk 1 [])
  have h2 : Derives basis (Word.mk 0 [0, 1, 1, 1, 1]) (Word.mk 1 [1, 0, 0, 1, 1]) := by
    have member : basisLaw4 ∈ basis := by decide
    have base : Derives basis basisLaw4.lhs basisLaw4.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 0 [0, 1, 1, 1, 1]) (Word.mk 1 [1, 0, 0, 1, 1]) := base.subst (fun n => if n = 0 then (Word.mk 0 []) else if n = 1 then (Word.mk 1 [1]) else Word.singleton 0)
    exact inst
  exact ((h0).trans h1).trans h2

theorem squareMoveQ : Derives basis (Word.mk 0 [0, 1, 3, 1]) (Word.mk 1 [1, 0, 0, 1, 3, 1]) := by
  have h0 : Derives basis (Word.mk 0 [0, 1, 3, 1]) (Word.mk 0 [0, 1, 1, 3, 1]) := by
    have member : basisLaw1 ∈ basis := by decide
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 1 [3, 1]) (Word.mk 1 [1, 3, 1]) := base.subst (fun n => if n = 0 then (Word.mk 1 []) else if n = 1 then (Word.mk 3 []) else Word.singleton 0)
    exact Derives.prepend (Word.mk 0 [0]) (inst)
  have h1 : Derives basis (Word.mk 0 [0, 1, 1, 3, 1]) (Word.mk 1 [0, 0, 1, 3, 1]) := by
    have member : basisLaw4 ∈ basis := by decide
    have base : Derives basis basisLaw4.lhs basisLaw4.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 0 [0, 1, 1]) (Word.mk 1 [0, 0, 1]) := base.subst (fun n => if n = 0 then (Word.mk 0 []) else if n = 1 then (Word.mk 1 []) else Word.singleton 0)
    exact Derives.appendRight (inst) (Word.mk 3 [1])
  have h2 : Derives basis (Word.mk 1 [0, 0, 1, 3, 1]) (Word.mk 1 [1, 0, 0, 1, 3, 1]) := by
    have member : basisLaw1 ∈ basis := by decide
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 1 [0, 0, 1]) (Word.mk 1 [1, 0, 0, 1]) := base.subst (fun n => if n = 0 then (Word.mk 1 []) else if n = 1 then (Word.mk 0 [0]) else Word.singleton 0)
    exact Derives.appendRight (inst) (Word.mk 3 [1])
  exact ((h0).trans h1).trans h2

theorem squareMoveP : Derives basis (Word.mk 0 [0, 2, 1, 1]) (Word.mk 1 [1, 0, 0, 2, 1, 1]) := by
  have h0 : Derives basis (Word.mk 0 [0, 2, 1, 1]) (Word.mk 0 [0, 1, 2, 1, 1]) := by
    have member : basisLaw9 ∈ basis := by decide
    have base : Derives basis basisLaw9.lhs basisLaw9.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 0 [0, 2, 1, 1]) (Word.mk 0 [0, 1, 2, 1, 1]) := base.subst (fun n => if n = 0 then (Word.mk 0 []) else if n = 1 then (Word.mk 2 []) else if n = 2 then (Word.mk 1 []) else Word.singleton 0)
    exact inst
  have h1 : Derives basis (Word.mk 0 [0, 1, 2, 1, 1]) (Word.mk 0 [0, 1, 1, 2, 1, 1]) := by
    have member : basisLaw1 ∈ basis := by decide
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 1 [2, 1]) (Word.mk 1 [1, 2, 1]) := base.subst (fun n => if n = 0 then (Word.mk 1 []) else if n = 1 then (Word.mk 2 []) else Word.singleton 0)
    exact Derives.appendRight (Derives.prepend (Word.mk 0 [0]) (inst)) (Word.mk 1 [])
  have h2 : Derives basis (Word.mk 0 [0, 1, 1, 2, 1, 1]) (Word.mk 0 [1, 1, 0, 2, 1, 1]) := by
    have member : basisLaw3 ∈ basis := by decide
    have base : Derives basis basisLaw3.lhs basisLaw3.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 0 [0, 1, 1]) (Word.mk 0 [1, 1, 0]) := base.subst (fun n => if n = 0 then (Word.mk 0 []) else if n = 1 then (Word.mk 1 []) else Word.singleton 0)
    exact Derives.appendRight (inst) (Word.mk 2 [1, 1])
  have h3 : Derives basis (Word.mk 0 [1, 1, 0, 2, 1, 1]) (Word.mk 1 [1, 0, 0, 2, 1, 1]) := by
    have member : basisLaw4 ∈ basis := by decide
    have base : Derives basis basisLaw4.lhs basisLaw4.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 1 [1, 0, 0]) (Word.mk 0 [1, 1, 0]) := base.subst (fun n => if n = 0 then (Word.mk 1 []) else if n = 1 then (Word.mk 0 []) else Word.singleton 0)
    exact Derives.appendRight (inst.symm) (Word.mk 2 [1, 1])
  exact (((h0).trans h1).trans h2).trans h3

theorem squareMovePQ : Derives basis (Word.mk 0 [0, 2, 1, 3, 1]) (Word.mk 1 [1, 0, 0, 2, 1, 3, 1]) := by
  have h0 : Derives basis (Word.mk 0 [0, 2, 1, 3, 1]) (Word.mk 0 [0, 2, 1, 1, 3, 1]) := by
    have member : basisLaw1 ∈ basis := by decide
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 1 [3, 1]) (Word.mk 1 [1, 3, 1]) := base.subst (fun n => if n = 0 then (Word.mk 1 []) else if n = 1 then (Word.mk 3 []) else Word.singleton 0)
    exact Derives.prepend (Word.mk 0 [0, 2]) (inst)
  have h1 : Derives basis (Word.mk 0 [0, 2, 1, 1, 3, 1]) (Word.mk 0 [0, 1, 2, 1, 1, 3, 1]) := by
    have member : basisLaw9 ∈ basis := by decide
    have base : Derives basis basisLaw9.lhs basisLaw9.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 0 [0, 2, 1, 1]) (Word.mk 0 [0, 1, 2, 1, 1]) := base.subst (fun n => if n = 0 then (Word.mk 0 []) else if n = 1 then (Word.mk 2 []) else if n = 2 then (Word.mk 1 []) else Word.singleton 0)
    exact Derives.appendRight (inst) (Word.mk 3 [1])
  have h2 : Derives basis (Word.mk 0 [0, 1, 2, 1, 1, 3, 1]) (Word.mk 0 [0, 1, 1, 2, 1, 3, 1]) := by
    have member : basisLaw10 ∈ basis := by decide
    have base : Derives basis basisLaw10.lhs basisLaw10.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 1 [2, 1, 1, 3, 1]) (Word.mk 1 [1, 2, 1, 3, 1]) := base.subst (fun n => if n = 0 then (Word.mk 1 []) else if n = 1 then (Word.mk 2 []) else if n = 2 then (Word.mk 1 []) else if n = 3 then (Word.mk 3 []) else Word.singleton 0)
    exact Derives.prepend (Word.mk 0 [0]) (inst)
  have h3 : Derives basis (Word.mk 0 [0, 1, 1, 2, 1, 3, 1]) (Word.mk 0 [1, 1, 0, 2, 1, 3, 1]) := by
    have member : basisLaw3 ∈ basis := by decide
    have base : Derives basis basisLaw3.lhs basisLaw3.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 0 [0, 1, 1]) (Word.mk 0 [1, 1, 0]) := base.subst (fun n => if n = 0 then (Word.mk 0 []) else if n = 1 then (Word.mk 1 []) else Word.singleton 0)
    exact Derives.appendRight (inst) (Word.mk 2 [1, 3, 1])
  have h4 : Derives basis (Word.mk 0 [1, 1, 0, 2, 1, 3, 1]) (Word.mk 1 [1, 0, 0, 2, 1, 3, 1]) := by
    have member : basisLaw4 ∈ basis := by decide
    have base : Derives basis basisLaw4.lhs basisLaw4.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 1 [1, 0, 0]) (Word.mk 0 [1, 1, 0]) := base.subst (fun n => if n = 0 then (Word.mk 1 []) else if n = 1 then (Word.mk 0 []) else Word.singleton 0)
    exact Derives.appendRight (inst.symm) (Word.mk 2 [1, 3, 1])
  exact ((((h0).trans h1).trans h2).trans h3).trans h4

theorem squareCommute : Derives basis (Word.mk 0 [0, 1, 1]) (Word.mk 1 [1, 0, 0]) := by
  have h0 : Derives basis (Word.mk 0 [0, 1, 1]) (Word.mk 1 [0, 0, 1]) := by
    have member : basisLaw4 ∈ basis := by decide
    have base : Derives basis basisLaw4.lhs basisLaw4.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 0 [0, 1, 1]) (Word.mk 1 [0, 0, 1]) := base.subst (fun n => if n = 0 then (Word.mk 0 []) else if n = 1 then (Word.mk 1 []) else Word.singleton 0)
    exact inst
  have h1 : Derives basis (Word.mk 1 [0, 0, 1]) (Word.mk 1 [1, 0, 0]) := by
    have member : basisLaw3 ∈ basis := by decide
    have base : Derives basis basisLaw3.lhs basisLaw3.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 1 [1, 0, 0]) (Word.mk 1 [0, 0, 1]) := base.subst (fun n => if n = 0 then (Word.mk 1 []) else if n = 1 then (Word.mk 0 []) else Word.singleton 0)
    exact inst.symm
  exact (h0).trans h1

theorem powerStep : Derives basis (Word.mk 0 [0]) (Word.mk 0 [0, 0]) :=
  Derives.fromBasis (by decide : basisLaw0 ∈ basis)

theorem repeatStep : Derives basis (Word.mk 0 [1, 0]) (Word.mk 0 [0, 1, 0]) :=
  Derives.fromBasis (by decide : basisLaw1 ∈ basis)

end SemigroupBasis.CoRoots.Order6Day15.B16.Reach

