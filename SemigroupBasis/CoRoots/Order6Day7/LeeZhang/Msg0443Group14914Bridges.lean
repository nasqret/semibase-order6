import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0443Group14914Presentation

/-! Explicit equational transport from the newly approved list to the
already complete source-bound basis. Every finite trace is checked by Lean. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0443Group14914

open SemigroupBasis
open Msg0442Cyclic (substituteFour)

theorem oldBasis00 : Derives basis (Word.mk 0 [0]) (Word.mk 0 [0, 0, 0, 0]) := by
  have step0 : Derives basis (Word.mk 0 [0]) (Word.mk 0 [0, 0, 0, 0]) := by
    have primitive : Derives basis law04.lhs law04.rhs := Derives.fromBasis (e := law04) (by simp [basis])
    have substituted := Derives.subst primitive (substituteFour (Word.mk 0 []) (Word.mk 0 []) (Word.mk 0 []) (Word.mk 0 []))
    simpa [law04, substituteFour, Word.bind, Word.append, Word.singleton] using substituted
  exact step0

theorem oldBasis01 : Derives basis (Word.mk 0 [0, 0, 1, 0]) (Word.mk 1 [0, 1, 1, 1]) := by
  have step0 : Derives basis (Word.mk 0 [0, 0, 1, 0]) (Word.mk 1 [0, 1, 1, 1]) := by
    have primitive : Derives basis law06.lhs law06.rhs := Derives.fromBasis (e := law06) (by simp [basis])
    have substituted := Derives.subst primitive (substituteFour (Word.mk 0 []) (Word.mk 1 []) (Word.mk 0 []) (Word.mk 0 []))
    simpa [law06, substituteFour, Word.bind, Word.append, Word.singleton] using substituted
  exact step0

theorem oldBasis02 : Derives basis (Word.mk 0 [0, 0, 1, 1]) (Word.mk 1 [0, 0, 0, 1]) := by
  have step0 : Derives basis (Word.mk 0 [0, 0, 1, 1]) (Word.mk 1 [0, 0, 0, 1]) := by
    have primitive : Derives basis law07.lhs law07.rhs := Derives.fromBasis (e := law07) (by simp [basis])
    have substituted := Derives.subst primitive (substituteFour (Word.mk 0 []) (Word.mk 1 []) (Word.mk 0 []) (Word.mk 0 []))
    simpa [law07, substituteFour, Word.bind, Word.append, Word.singleton] using substituted
  exact step0

theorem oldBasis03 : Derives basis (Word.mk 0 [0, 1, 0]) (Word.mk 0 [1, 0, 0]) := by
  have step0 : Derives basis (Word.mk 0 [0, 1, 0]) (Word.mk 0 [1, 0, 0]) := by
    have primitive : Derives basis law00.lhs law00.rhs := Derives.fromBasis (e := law00) (by simp [basis])
    have substituted := Derives.subst primitive (substituteFour (Word.mk 0 []) (Word.mk 0 []) (Word.mk 1 []) (Word.mk 0 []))
    simpa [law00, substituteFour, Word.bind, Word.append, Word.singleton] using substituted
  exact step0

theorem oldBasis04 : Derives basis (Word.mk 0 [0, 1, 1]) (Word.mk 0 [1, 0, 1]) := by
  have step0 : Derives basis (Word.mk 0 [0, 1, 1]) (Word.mk 1 [1, 0, 0]) := by
    have primitive : Derives basis law01.lhs law01.rhs := Derives.fromBasis (e := law01) (by simp [basis])
    have substituted := Derives.subst primitive (substituteFour (Word.mk 0 []) (Word.mk 0 []) (Word.mk 0 []) (Word.mk 1 []))
    simpa [law01, substituteFour, Word.bind, Word.append, Word.singleton] using substituted
  have step1 : Derives basis (Word.mk 1 [1, 0, 0]) (Word.mk 0 [1, 0, 1]) := by
    have primitive : Derives basis law02.lhs law02.rhs := Derives.fromBasis (e := law02) (by simp [basis])
    have substituted := Derives.subst primitive (substituteFour (Word.mk 0 []) (Word.mk 0 []) (Word.mk 1 []) (Word.mk 0 []))
    simpa [law02, substituteFour, Word.bind, Word.append, Word.singleton] using substituted
  exact step0.trans (step1)

theorem oldBasis05 : Derives basis (Word.mk 0 [0, 1, 1]) (Word.mk 0 [1, 1, 0]) := by
  have step0 : Derives basis (Word.mk 0 [0, 1, 1]) (Word.mk 1 [1, 0, 0]) := by
    have primitive : Derives basis law01.lhs law01.rhs := Derives.fromBasis (e := law01) (by simp [basis])
    have substituted := Derives.subst primitive (substituteFour (Word.mk 0 []) (Word.mk 0 []) (Word.mk 0 []) (Word.mk 1 []))
    simpa [law01, substituteFour, Word.bind, Word.append, Word.singleton] using substituted
  have step1 : Derives basis (Word.mk 1 [1, 0, 0]) (Word.mk 0 [1, 1, 0]) := by
    have primitive : Derives basis law03.lhs law03.rhs := Derives.fromBasis (e := law03) (by simp [basis])
    have substituted := Derives.subst primitive (substituteFour (Word.mk 0 []) (Word.mk 0 []) (Word.mk 1 []) (Word.mk 0 []))
    simpa [law03, substituteFour, Word.bind, Word.append, Word.singleton] using substituted
  exact step0.trans (step1)

theorem oldBasis06 : Derives basis (Word.mk 0 [0, 1, 1]) (Word.mk 1 [0, 0, 1]) := by
  have step0 : Derives basis (Word.mk 0 [0, 1, 1]) (Word.mk 1 [0, 0, 1]) := by
    have primitive : Derives basis law03.lhs law03.rhs := Derives.fromBasis (e := law03) (by simp [basis])
    have substituted := Derives.subst primitive (substituteFour (Word.mk 0 []) (Word.mk 0 []) (Word.mk 0 []) (Word.mk 1 []))
    simpa [law03, substituteFour, Word.bind, Word.append, Word.singleton] using substituted
  exact step0

theorem oldBasis07 : Derives basis (Word.mk 0 [0, 1, 2, 1]) (Word.mk 0 [1, 0, 2, 1]) := by
  have step0 : Derives basis (Word.mk 0 [0, 1, 2, 1]) (Word.mk 0 [1, 0, 2, 1]) := by
    have primitive : Derives basis law08.lhs law08.rhs := Derives.fromBasis (e := law08) (by simp [basis])
    have substituted := Derives.subst primitive (substituteFour (Word.mk 0 []) (Word.mk 1 []) (Word.mk 2 []) (Word.mk 0 []))
    simpa [law08, substituteFour, Word.bind, Word.append, Word.singleton] using substituted
  exact step0

theorem oldBasis08 : Derives basis (Word.mk 0 [0, 1, 2, 1]) (Word.mk 0 [1, 1, 2, 0]) := by
  have step0 : Derives basis (Word.mk 0 [0, 1, 2, 1]) (Word.mk 0 [1, 1, 2, 0]) := by
    have primitive : Derives basis law09.lhs law09.rhs := Derives.fromBasis (e := law09) (by simp [basis])
    have substituted := Derives.subst primitive (substituteFour (Word.mk 0 []) (Word.mk 1 []) (Word.mk 2 []) (Word.mk 0 []))
    simpa [law09, substituteFour, Word.bind, Word.append, Word.singleton] using substituted
  exact step0

theorem oldBasis09 : Derives basis (Word.mk 0 [0, 1, 2, 1]) (Word.mk 0 [2, 0, 1, 1]) :=
  Derives.fromBasis (e := law10) (by simp [basis])

theorem oldBasis10 : Derives basis (Word.mk 0 [0, 1, 2, 1]) (Word.mk 1 [0, 0, 2, 1]) := by
  have step0 : Derives basis (Word.mk 0 [0, 1, 2, 1]) (Word.mk 1 [0, 0, 2, 1]) := by
    have primitive : Derives basis law11.lhs law11.rhs := Derives.fromBasis (e := law11) (by simp [basis])
    have substituted := Derives.subst primitive (substituteFour (Word.mk 0 []) (Word.mk 1 []) (Word.mk 2 []) (Word.mk 0 []))
    simpa [law11, substituteFour, Word.bind, Word.append, Word.singleton] using substituted
  exact step0

theorem oldBasis11 : Derives basis (Word.mk 0 [1, 2, 0]) (Word.mk 0 [2, 1, 0]) := by
  have step0 : Derives basis (Word.mk 0 [1, 2, 0]) (Word.mk 0 [2, 1, 0]) := by
    have primitive : Derives basis law00.lhs law00.rhs := Derives.fromBasis (e := law00) (by simp [basis])
    have substituted := Derives.subst primitive (substituteFour (Word.mk 0 []) (Word.mk 1 []) (Word.mk 2 []) (Word.mk 0 []))
    simpa [law00, substituteFour, Word.bind, Word.append, Word.singleton] using substituted
  exact step0

theorem oldBasis12 : Derives basis (Word.mk 0 [1, 0]) (Word.mk 0 [0, 0, 0, 1, 0]) := by
  have step0 : Derives basis (Word.mk 0 [1, 0]) (Word.mk 0 [0, 0, 0, 1, 0]) := by
    have primitive : Derives basis law05.lhs law05.rhs := Derives.fromBasis (e := law05) (by simp [basis])
    have substituted := Derives.subst primitive (substituteFour (Word.mk 0 []) (Word.mk 1 []) (Word.mk 0 []) (Word.mk 0 []))
    simpa [law05, substituteFour, Word.bind, Word.append, Word.singleton] using substituted
  exact step0

abbrev oldBasis := SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006SigmaPlus.sigmaPlus

theorem oldBasisExact : oldBasis =
    [(Identity.mk (Word.mk 0 [0]) (Word.mk 0 [0, 0, 0, 0])),
     (Identity.mk (Word.mk 0 [0, 0, 1, 0]) (Word.mk 1 [0, 1, 1, 1])),
     (Identity.mk (Word.mk 0 [0, 0, 1, 1]) (Word.mk 1 [0, 0, 0, 1])),
     (Identity.mk (Word.mk 0 [0, 1, 0]) (Word.mk 0 [1, 0, 0])),
     (Identity.mk (Word.mk 0 [0, 1, 1]) (Word.mk 0 [1, 0, 1])),
     (Identity.mk (Word.mk 0 [0, 1, 1]) (Word.mk 0 [1, 1, 0])),
     (Identity.mk (Word.mk 0 [0, 1, 1]) (Word.mk 1 [0, 0, 1])),
     (Identity.mk (Word.mk 0 [0, 1, 2, 1]) (Word.mk 0 [1, 0, 2, 1])),
     (Identity.mk (Word.mk 0 [0, 1, 2, 1]) (Word.mk 0 [1, 1, 2, 0])),
     (Identity.mk (Word.mk 0 [0, 1, 2, 1]) (Word.mk 0 [2, 0, 1, 1])),
     (Identity.mk (Word.mk 0 [0, 1, 2, 1]) (Word.mk 1 [0, 0, 2, 1])),
     (Identity.mk (Word.mk 0 [1, 2, 0]) (Word.mk 0 [2, 1, 0])),
     (Identity.mk (Word.mk 0 [1, 0]) (Word.mk 0 [0, 0, 0, 1, 0]))] := rfl

theorem oldBasisDerivable (identity : Identity Nat) (member : identity ∈ oldBasis) :
    Derives basis identity.lhs identity.rhs := by
  rw [oldBasisExact] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact oldBasis00
  · exact oldBasis01
  · exact oldBasis02
  · exact oldBasis03
  · exact oldBasis04
  · exact oldBasis05
  · exact oldBasis06
  · exact oldBasis07
  · exact oldBasis08
  · exact oldBasis09
  · exact oldBasis10
  · exact oldBasis11
  · exact oldBasis12

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0443Group14914
