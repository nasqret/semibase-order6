import SemigroupBasis.CoRoots.Order6Sunday.Msg0514RepairedSixteenLawFinite

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6Day15.B16.Reach

open SemigroupBasis.CoRoots.Order6Sunday.Msg0514RepairedSixteenLawFinite

theorem anchoredDelete : Derives basis (Word.mk 0 [0, 1, 1, 2, 0, 1, 3, 1]) (Word.mk 0 [0, 1, 1, 2, 0, 3, 1]) := by
  have h0 : Derives basis (Word.mk 0 [0, 1, 1, 2, 0, 1, 3, 1]) (Word.mk 0 [0, 1, 1, 1, 2, 0, 3, 1]) := by
    have member : basisLaw10 ∈ basis := by decide
    have base : Derives basis basisLaw10.lhs basisLaw10.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 0 [1, 1, 2, 0, 1, 3, 1]) (Word.mk 0 [1, 1, 1, 2, 0, 3, 1]) := base.subst (fun n => if n = 0 then (Word.mk 0 []) else if n = 1 then (Word.mk 1 [1, 2]) else if n = 2 then (Word.mk 1 []) else if n = 3 then (Word.mk 3 []) else Word.singleton 0)
    exact Derives.prepend (Word.mk 0 []) (inst)
  have h1 : Derives basis (Word.mk 0 [0, 1, 1, 1, 2, 0, 3, 1]) (Word.mk 0 [0, 1, 1, 2, 0, 3, 1]) := by
    have member : basisLaw1 ∈ basis := by decide
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 1 [1, 2, 0, 3, 1]) (Word.mk 1 [1, 1, 2, 0, 3, 1]) := base.subst (fun n => if n = 0 then (Word.mk 1 []) else if n = 1 then (Word.mk 1 [2, 0, 3]) else Word.singleton 0)
    exact Derives.prepend (Word.mk 0 [0]) (inst.symm)
  exact (h0).trans h1

theorem headTransfer : Derives basis (Word.mk 0 [0, 1, 1, 2, 0, 0, 3, 1]) (Word.mk 0 [0, 2, 1, 0, 0, 3, 1]) := by
  have h0 : Derives basis (Word.mk 0 [0, 1, 1, 2, 0, 0, 3, 1]) (Word.mk 0 [0, 1, 1, 2, 0, 0, 0, 3, 1]) := by
    have member : basisLaw0 ∈ basis := by decide
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 0 [0]) (Word.mk 0 [0, 0]) := base.subst (fun n => if n = 0 then (Word.mk 0 []) else Word.singleton 0)
    exact Derives.appendRight (Derives.prepend (Word.mk 0 [0, 1, 1, 2]) (inst)) (Word.mk 3 [1])
  have h1 : Derives basis (Word.mk 0 [0, 1, 1, 2, 0, 0, 0, 3, 1]) (Word.mk 0 [0, 1, 2, 0, 0, 0, 3, 1]) := by
    have member : basisLaw1 ∈ basis := by decide
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 1 [2, 0, 0, 0, 3, 1]) (Word.mk 1 [1, 2, 0, 0, 0, 3, 1]) := base.subst (fun n => if n = 0 then (Word.mk 1 []) else if n = 1 then (Word.mk 2 [0, 0, 0, 3]) else Word.singleton 0)
    exact Derives.prepend (Word.mk 0 [0]) (inst.symm)
  have h2 : Derives basis (Word.mk 0 [0, 1, 2, 0, 0, 0, 3, 1]) (Word.mk 0 [0, 0, 2, 1, 0, 0, 3, 1]) := by
    have member : basisLaw13 ∈ basis := by decide
    have base : Derives basis basisLaw13.lhs basisLaw13.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 1 [2, 0, 0, 0, 3, 1]) (Word.mk 0 [2, 1, 0, 0, 3, 1]) := base.subst (fun n => if n = 0 then (Word.mk 1 []) else if n = 1 then (Word.mk 2 []) else if n = 2 then (Word.mk 0 []) else if n = 3 then (Word.mk 0 [3]) else Word.singleton 0)
    exact Derives.prepend (Word.mk 0 [0]) (inst)
  have h3 : Derives basis (Word.mk 0 [0, 0, 2, 1, 0, 0, 3, 1]) (Word.mk 0 [0, 2, 1, 0, 0, 3, 1]) := by
    have member : basisLaw0 ∈ basis := by decide
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 0 [0]) (Word.mk 0 [0, 0]) := base.subst (fun n => if n = 0 then (Word.mk 0 []) else Word.singleton 0)
    exact Derives.appendRight (inst.symm) (Word.mk 2 [1, 0, 0, 3, 1])
  exact (((h0).trans h1).trans h2).trans h3

theorem headTransferEmpty : Derives basis (Word.mk 0 [0, 1, 1, 2, 0, 0, 1]) (Word.mk 0 [0, 2, 1, 0, 0, 1]) := by
  have h0 : Derives basis (Word.mk 0 [0, 1, 1, 2, 0, 0, 1]) (Word.mk 0 [0, 1, 1, 2, 0, 0, 0, 1]) := by
    have member : basisLaw0 ∈ basis := by decide
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 0 [0]) (Word.mk 0 [0, 0]) := base.subst (fun n => if n = 0 then (Word.mk 0 []) else Word.singleton 0)
    exact Derives.appendRight (Derives.prepend (Word.mk 0 [0, 1, 1, 2]) (inst)) (Word.mk 1 [])
  have h1 : Derives basis (Word.mk 0 [0, 1, 1, 2, 0, 0, 0, 1]) (Word.mk 0 [0, 1, 2, 0, 0, 0, 1]) := by
    have member : basisLaw1 ∈ basis := by decide
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 1 [2, 0, 0, 0, 1]) (Word.mk 1 [1, 2, 0, 0, 0, 1]) := base.subst (fun n => if n = 0 then (Word.mk 1 []) else if n = 1 then (Word.mk 2 [0, 0, 0]) else Word.singleton 0)
    exact Derives.prepend (Word.mk 0 [0]) (inst.symm)
  have h2 : Derives basis (Word.mk 0 [0, 1, 2, 0, 0, 0, 1]) (Word.mk 0 [0, 0, 2, 1, 0, 0, 1]) := by
    have member : basisLaw13 ∈ basis := by decide
    have base : Derives basis basisLaw13.lhs basisLaw13.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 1 [2, 0, 0, 0, 1]) (Word.mk 0 [2, 1, 0, 0, 1]) := base.subst (fun n => if n = 0 then (Word.mk 1 []) else if n = 1 then (Word.mk 2 []) else if n = 2 then (Word.mk 0 []) else if n = 3 then (Word.mk 0 []) else Word.singleton 0)
    exact Derives.prepend (Word.mk 0 [0]) (inst)
  have h3 : Derives basis (Word.mk 0 [0, 0, 2, 1, 0, 0, 1]) (Word.mk 0 [0, 2, 1, 0, 0, 1]) := by
    have member : basisLaw0 ∈ basis := by decide
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs := Derives.fromBasis member
    have inst : Derives basis (Word.mk 0 [0]) (Word.mk 0 [0, 0]) := base.subst (fun n => if n = 0 then (Word.mk 0 []) else Word.singleton 0)
    exact Derives.appendRight (inst.symm) (Word.mk 2 [1, 0, 0, 1])
  exact (((h0).trans h1).trans h2).trans h3

end SemigroupBasis.CoRoots.Order6Day15.B16.Reach

