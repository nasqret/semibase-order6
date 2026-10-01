import SemigroupBasis.CoRoots.Order6Sunday.Msg0514RepairedSixteenLawFinite

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6Day15.B16.Reach

open SemigroupBasis.CoRoots.Order6Sunday.Msg0514RepairedSixteenLawFinite

theorem thickenSeed : Derives basis (Word.mk 0 [1, 2, 0, 1]) (Word.mk 0 [1, 2, 0, 1, 1]) := by
  have h0 : Derives basis (Word.mk 0 [1, 2, 0, 1]) (Word.mk 0 [1, 1, 2, 0, 1]) := by
    have member : basisLaw1 ∈ basis := by decide
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 1 [2, 0, 1]) (Word.mk 1 [1, 2, 0, 1]) := base.subst (fun n => if n = 0 then (Word.mk 1 []) else if n = 1 then (Word.mk 2 [0]) else Word.singleton 0)
    exact Derives.prepend (Word.mk 0 []) (inst)
  have h1 : Derives basis (Word.mk 0 [1, 1, 2, 0, 1]) (Word.mk 1 [1, 0, 2, 0, 1]) := by
    have member : basisLaw14 ∈ basis := by decide
    have base : Derives basis basisLaw14.lhs basisLaw14.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 0 [1, 1, 2, 0, 1]) (Word.mk 1 [1, 0, 2, 0, 1]) := base.subst (fun n => if n = 0 then (Word.mk 0 []) else if n = 1 then (Word.mk 1 []) else if n = 2 then (Word.mk 1 []) else if n = 3 then (Word.mk 2 []) else Word.singleton 0)
    exact inst
  have h2 : Derives basis (Word.mk 1 [1, 0, 2, 0, 1]) (Word.mk 1 [1, 1, 0, 2, 0, 1]) := by
    have member : basisLaw0 ∈ basis := by decide
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 1 [1]) (Word.mk 1 [1, 1]) := base.subst (fun n => if n = 0 then (Word.mk 1 []) else Word.singleton 0)
    exact Derives.appendRight (inst) (Word.mk 0 [2, 0, 1])
  have h3 : Derives basis (Word.mk 1 [1, 1, 0, 2, 0, 1]) (Word.mk 1 [1, 0, 2, 0, 1, 1]) := by
    have member : basisLaw6 ∈ basis := by decide
    have base : Derives basis basisLaw6.lhs basisLaw6.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 0 [2, 0, 1, 1]) (Word.mk 1 [0, 2, 0, 1]) := base.subst (fun n => if n = 0 then (Word.mk 0 []) else if n = 1 then (Word.mk 2 []) else if n = 2 then (Word.mk 1 []) else Word.singleton 0)
    exact Derives.prepend (Word.mk 1 [1]) (inst.symm)
  have h4 : Derives basis (Word.mk 1 [1, 0, 2, 0, 1, 1]) (Word.mk 0 [1, 1, 2, 0, 1, 1]) := by
    have member : basisLaw14 ∈ basis := by decide
    have base : Derives basis basisLaw14.lhs basisLaw14.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 0 [1, 1, 2, 0, 1]) (Word.mk 1 [1, 0, 2, 0, 1]) := base.subst (fun n => if n = 0 then (Word.mk 0 []) else if n = 1 then (Word.mk 1 []) else if n = 2 then (Word.mk 1 []) else if n = 3 then (Word.mk 2 []) else Word.singleton 0)
    exact Derives.appendRight (inst.symm) (Word.mk 1 [])
  have h5 : Derives basis (Word.mk 0 [1, 1, 2, 0, 1, 1]) (Word.mk 0 [1, 2, 0, 1, 1]) := by
    have member : basisLaw1 ∈ basis := by decide
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 1 [2, 0, 1]) (Word.mk 1 [1, 2, 0, 1]) := base.subst (fun n => if n = 0 then (Word.mk 1 []) else if n = 1 then (Word.mk 2 [0]) else Word.singleton 0)
    exact Derives.appendRight (Derives.prepend (Word.mk 0 []) (inst.symm)) (Word.mk 1 [])
  exact (((((h0).trans h1).trans h2).trans h3).trans h4).trans h5

theorem thickenSeedEmpty : Derives basis (Word.mk 0 [1, 0, 1]) (Word.mk 0 [1, 0, 1, 1]) := by
  have h0 : Derives basis (Word.mk 0 [1, 0, 1]) (Word.mk 0 [0, 1, 1]) := by
    have member : basisLaw2 ∈ basis := by decide
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 0 [0, 1, 1]) (Word.mk 0 [1, 0, 1]) := base.subst (fun n => if n = 0 then (Word.mk 0 []) else if n = 1 then (Word.mk 1 []) else Word.singleton 0)
    exact inst.symm
  have h1 : Derives basis (Word.mk 0 [0, 1, 1]) (Word.mk 0 [0, 1, 1, 1]) := by
    have member : basisLaw0 ∈ basis := by decide
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 1 [1]) (Word.mk 1 [1, 1]) := base.subst (fun n => if n = 0 then (Word.mk 1 []) else Word.singleton 0)
    exact Derives.prepend (Word.mk 0 [0]) (inst)
  have h2 : Derives basis (Word.mk 0 [0, 1, 1, 1]) (Word.mk 0 [1, 0, 1, 1]) := by
    have member : basisLaw2 ∈ basis := by decide
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 0 [0, 1, 1]) (Word.mk 0 [1, 0, 1]) := base.subst (fun n => if n = 0 then (Word.mk 0 []) else if n = 1 then (Word.mk 1 []) else Word.singleton 0)
    exact Derives.appendRight (inst) (Word.mk 1 [])
  exact ((h0).trans h1).trans h2

theorem anchoredThicken : Derives basis (Word.mk 0 [0, 1, 1, 2, 0, 1]) (Word.mk 0 [0, 1, 1, 2, 0, 1, 1]) := by
  have h0 : Derives basis (Word.mk 0 [0, 1, 1, 2, 0, 1]) (Word.mk 0 [1, 0, 1, 2, 0, 1]) := by
    have member : basisLaw2 ∈ basis := by decide
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 0 [0, 1, 1]) (Word.mk 0 [1, 0, 1]) := base.subst (fun n => if n = 0 then (Word.mk 0 []) else if n = 1 then (Word.mk 1 []) else Word.singleton 0)
    exact Derives.appendRight (inst) (Word.mk 2 [0, 1])
  have h1 : Derives basis (Word.mk 0 [1, 0, 1, 2, 0, 1]) (Word.mk 0 [1, 2, 0, 1]) := by
    have member : basisLaw1 ∈ basis := by decide
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 0 [1, 2, 0, 1]) (Word.mk 0 [1, 0, 1, 2, 0, 1]) := base.subst (fun n => if n = 0 then (Word.mk 0 [1]) else if n = 1 then (Word.mk 2 []) else Word.singleton 0)
    exact inst.symm
  have h2 : Derives basis (Word.mk 0 [1, 2, 0, 1]) (Word.mk 0 [1, 1, 2, 0, 1]) := by
    have member : basisLaw1 ∈ basis := by decide
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 1 [2, 0, 1]) (Word.mk 1 [1, 2, 0, 1]) := base.subst (fun n => if n = 0 then (Word.mk 1 []) else if n = 1 then (Word.mk 2 [0]) else Word.singleton 0)
    exact Derives.prepend (Word.mk 0 []) (inst)
  have h3 : Derives basis (Word.mk 0 [1, 1, 2, 0, 1]) (Word.mk 1 [1, 0, 2, 0, 1]) := by
    have member : basisLaw14 ∈ basis := by decide
    have base : Derives basis basisLaw14.lhs basisLaw14.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 0 [1, 1, 2, 0, 1]) (Word.mk 1 [1, 0, 2, 0, 1]) := base.subst (fun n => if n = 0 then (Word.mk 0 []) else if n = 1 then (Word.mk 1 []) else if n = 2 then (Word.mk 1 []) else if n = 3 then (Word.mk 2 []) else Word.singleton 0)
    exact inst
  have h4 : Derives basis (Word.mk 1 [1, 0, 2, 0, 1]) (Word.mk 1 [1, 1, 0, 2, 0, 1]) := by
    have member : basisLaw0 ∈ basis := by decide
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 1 [1]) (Word.mk 1 [1, 1]) := base.subst (fun n => if n = 0 then (Word.mk 1 []) else Word.singleton 0)
    exact Derives.appendRight (inst) (Word.mk 0 [2, 0, 1])
  have h5 : Derives basis (Word.mk 1 [1, 1, 0, 2, 0, 1]) (Word.mk 1 [1, 0, 2, 0, 1, 1]) := by
    have member : basisLaw6 ∈ basis := by decide
    have base : Derives basis basisLaw6.lhs basisLaw6.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 0 [2, 0, 1, 1]) (Word.mk 1 [0, 2, 0, 1]) := base.subst (fun n => if n = 0 then (Word.mk 0 []) else if n = 1 then (Word.mk 2 []) else if n = 2 then (Word.mk 1 []) else Word.singleton 0)
    exact Derives.prepend (Word.mk 1 [1]) (inst.symm)
  have h6 : Derives basis (Word.mk 1 [1, 0, 2, 0, 1, 1]) (Word.mk 0 [1, 1, 2, 0, 1, 1]) := by
    have member : basisLaw14 ∈ basis := by decide
    have base : Derives basis basisLaw14.lhs basisLaw14.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 0 [1, 1, 2, 0, 1]) (Word.mk 1 [1, 0, 2, 0, 1]) := base.subst (fun n => if n = 0 then (Word.mk 0 []) else if n = 1 then (Word.mk 1 []) else if n = 2 then (Word.mk 1 []) else if n = 3 then (Word.mk 2 []) else Word.singleton 0)
    exact Derives.appendRight (inst.symm) (Word.mk 1 [])
  have h7 : Derives basis (Word.mk 0 [1, 1, 2, 0, 1, 1]) (Word.mk 0 [1, 2, 0, 1, 1]) := by
    have member : basisLaw1 ∈ basis := by decide
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 1 [2, 0, 1]) (Word.mk 1 [1, 2, 0, 1]) := base.subst (fun n => if n = 0 then (Word.mk 1 []) else if n = 1 then (Word.mk 2 [0]) else Word.singleton 0)
    exact Derives.appendRight (Derives.prepend (Word.mk 0 []) (inst.symm)) (Word.mk 1 [])
  have h8 : Derives basis (Word.mk 0 [1, 2, 0, 1, 1]) (Word.mk 0 [1, 0, 1, 2, 0, 1, 1]) := by
    have member : basisLaw1 ∈ basis := by decide
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 0 [1, 2, 0, 1]) (Word.mk 0 [1, 0, 1, 2, 0, 1]) := base.subst (fun n => if n = 0 then (Word.mk 0 [1]) else if n = 1 then (Word.mk 2 []) else Word.singleton 0)
    exact Derives.appendRight (inst) (Word.mk 1 [])
  have h9 : Derives basis (Word.mk 0 [1, 0, 1, 2, 0, 1, 1]) (Word.mk 0 [0, 1, 1, 2, 0, 1, 1]) := by
    have member : basisLaw2 ∈ basis := by decide
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 0 [0, 1, 1]) (Word.mk 0 [1, 0, 1]) := base.subst (fun n => if n = 0 then (Word.mk 0 []) else if n = 1 then (Word.mk 1 []) else Word.singleton 0)
    exact Derives.appendRight (inst.symm) (Word.mk 2 [0, 1, 1])
  exact (((((((((h0).trans h1).trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).trans h8).trans h9

end SemigroupBasis.CoRoots.Order6Day15.B16.Reach

