import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0443Pair2675Presentation

/-! Concrete B10 derivations, then arbitrary substitution and a structural
induction through the complete S5_203 lower theory. No bounded premise. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0443Pair2675

open SemigroupBasis
open Msg0442Cyclic (substituteFour bindSingleton)

theorem guardedLower00 : Derives basis (Word.mk 3 [0, 0, 0]) (Word.mk 3 [0, 0, 0, 0]) := by
  have step0 : Derives basis (Word.mk 3 [0, 0, 0]) (Word.mk 3 [0, 0, 0, 0]) := by
    have primitive : Derives basis law01.lhs law01.rhs := Derives.fromBasis (e := law01) (by simp [basis])
    have substituted := Derives.subst primitive (substituteFour (Word.mk 0 []) (Word.mk 0 []) (Word.mk 0 []) (Word.mk 0 []))
    simpa [law01, substituteFour, Word.bind, Word.append, Word.singleton] using (Derives.prepend (Word.mk 3 []) substituted)
  exact step0

theorem guardedLower01 : Derives basis (Word.mk 3 [0, 0, 1]) (Word.mk 3 [0, 0, 0, 1]) := by
  have step0 : Derives basis (Word.mk 3 [0, 0, 1]) (Word.mk 3 [0, 0, 0, 1]) := by
    have primitive : Derives basis law01.lhs law01.rhs := Derives.fromBasis (e := law01) (by simp [basis])
    have substituted := Derives.subst primitive (substituteFour (Word.mk 0 []) (Word.mk 0 []) (Word.mk 1 []) (Word.mk 0 []))
    simpa [law01, substituteFour, Word.bind, Word.append, Word.singleton] using (Derives.prepend (Word.mk 3 []) substituted)
  exact step0

theorem guardedLower02 : Derives basis (Word.mk 3 [0, 1, 0]) (Word.mk 3 [1, 0, 1]) := by
  have step0 : Derives basis (Word.mk 3 [0, 1, 0]) (Word.mk 3 [1, 0, 1]) := by
    have primitive : Derives basis law00.lhs law00.rhs := Derives.fromBasis (e := law00) (by simp [basis])
    have substituted := Derives.subst primitive (substituteFour (Word.mk 0 []) (Word.mk 0 []) (Word.mk 0 []) (Word.mk 1 []))
    simpa [law00, substituteFour, Word.bind, Word.append, Word.singleton] using (Derives.prepend (Word.mk 3 []) substituted)
  exact step0

theorem guardedLower03 : Derives basis (Word.mk 3 [0, 1, 0]) (Word.mk 3 [0, 0, 1, 0]) := by
  have step0 : Derives basis (Word.mk 3 [0, 1, 0]) (Word.mk 3 [0, 0, 1, 0]) := by
    have primitive : Derives basis law05.lhs law05.rhs := Derives.fromBasis (e := law05) (by simp [basis])
    have substituted := Derives.subst primitive (substituteFour (Word.mk 3 []) (Word.mk 0 []) (Word.mk 1 []) (Word.mk 0 []))
    simpa [law05, substituteFour, Word.bind, Word.append, Word.singleton] using substituted
  exact step0

theorem guardedLower04 : Derives basis (Word.mk 3 [0, 1, 0]) (Word.mk 3 [0, 1, 1, 1]) := by
  have step0 : Derives basis (Word.mk 3 [0, 1, 0]) (Word.mk 3 [0, 0, 1, 1, 1]) := by
    have primitive : Derives basis law06.lhs law06.rhs := Derives.fromBasis (e := law06) (by simp [basis])
    have substituted := Derives.subst primitive (substituteFour (Word.mk 0 []) (Word.mk 1 []) (Word.mk 0 []) (Word.mk 0 []))
    simpa [law06, substituteFour, Word.bind, Word.append, Word.singleton] using (Derives.prepend (Word.mk 3 []) substituted)
  have step1 : Derives basis (Word.mk 3 [0, 0, 1, 1, 1]) (Word.mk 3 [0, 1, 1, 1]) := by
    have primitive : Derives basis law05.lhs law05.rhs := Derives.fromBasis (e := law05) (by simp [basis])
    have substituted := Derives.subst primitive (substituteFour (Word.mk 3 []) (Word.mk 0 []) (Word.mk 1 []) (Word.mk 1 []))
    simpa [law05, substituteFour, Word.bind, Word.append, Word.singleton] using (Derives.appendRight substituted.symm (Word.mk 1 []))
  exact step0.trans (step1)

theorem guardedLower05 : Derives basis (Word.mk 3 [0, 1, 0]) (Word.mk 3 [0, 1, 1, 0, 0]) := by
  have step0 : Derives basis (Word.mk 3 [0, 1, 0]) (Word.mk 3 [1, 1, 0, 1]) := by
    have primitive : Derives basis law02.lhs law02.rhs := Derives.fromBasis (e := law02) (by simp [basis])
    have substituted := Derives.subst primitive (substituteFour (Word.mk 0 []) (Word.mk 0 []) (Word.mk 0 []) (Word.mk 1 []))
    simpa [law02, substituteFour, Word.bind, Word.append, Word.singleton] using (Derives.prepend (Word.mk 3 []) substituted)
  have step1 : Derives basis (Word.mk 3 [1, 1, 0, 1]) (Word.mk 3 [1, 0, 1, 1, 0]) := by
    have primitive : Derives basis law00.lhs law00.rhs := Derives.fromBasis (e := law00) (by simp [basis])
    have substituted := Derives.subst primitive (substituteFour (Word.mk 0 []) (Word.mk 0 []) (Word.mk 1 []) (Word.mk 1 [0]))
    simpa [law00, substituteFour, Word.bind, Word.append, Word.singleton] using (Derives.prepend (Word.mk 3 []) substituted)
  have step2 : Derives basis (Word.mk 3 [1, 0, 1, 1, 0]) (Word.mk 3 [0, 1, 1, 0, 0]) := by
    have primitive : Derives basis law03.lhs law03.rhs := Derives.fromBasis (e := law03) (by simp [basis])
    have substituted := Derives.subst primitive (substituteFour (Word.mk 0 []) (Word.mk 0 []) (Word.mk 1 []) (Word.mk 1 []))
    simpa [law03, substituteFour, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend (Word.mk 3 []) substituted.symm) (Word.mk 0 []))
  exact step0.trans (step1.trans (step2))

theorem guardedLower06 : Derives basis (Word.mk 3 [0, 1, 1]) (Word.mk 3 [0, 0, 1, 1]) := by
  have step0 : Derives basis (Word.mk 3 [0, 1, 1]) (Word.mk 3 [0, 0, 1, 1]) := by
    have primitive : Derives basis law05.lhs law05.rhs := Derives.fromBasis (e := law05) (by simp [basis])
    have substituted := Derives.subst primitive (substituteFour (Word.mk 3 []) (Word.mk 0 []) (Word.mk 1 []) (Word.mk 1 []))
    simpa [law05, substituteFour, Word.bind, Word.append, Word.singleton] using substituted
  exact step0

theorem guardedLower07 : Derives basis (Word.mk 3 [0, 1, 2]) (Word.mk 3 [0, 0, 1, 2]) := by
  have step0 : Derives basis (Word.mk 3 [0, 1, 2]) (Word.mk 3 [0, 0, 1, 2]) := by
    have primitive : Derives basis law05.lhs law05.rhs := Derives.fromBasis (e := law05) (by simp [basis])
    have substituted := Derives.subst primitive (substituteFour (Word.mk 3 []) (Word.mk 0 []) (Word.mk 1 []) (Word.mk 2 []))
    simpa [law05, substituteFour, Word.bind, Word.append, Word.singleton] using substituted
  exact step0

theorem guardedLower08 : Derives basis (Word.mk 3 [0, 1, 2, 0]) (Word.mk 3 [0, 1, 2, 1]) := by
  have step0 : Derives basis (Word.mk 3 [0, 1, 2, 0]) (Word.mk 3 [0, 0, 1, 2, 1]) := by
    have primitive : Derives basis law07.lhs law07.rhs := Derives.fromBasis (e := law07) (by simp [basis])
    have substituted := Derives.subst primitive (substituteFour (Word.mk 0 []) (Word.mk 1 []) (Word.mk 2 []) (Word.mk 0 []))
    simpa [law07, substituteFour, Word.bind, Word.append, Word.singleton] using (Derives.prepend (Word.mk 3 []) substituted)
  have step1 : Derives basis (Word.mk 3 [0, 0, 1, 2, 1]) (Word.mk 3 [0, 1, 2, 1]) := by
    have primitive : Derives basis law05.lhs law05.rhs := Derives.fromBasis (e := law05) (by simp [basis])
    have substituted := Derives.subst primitive (substituteFour (Word.mk 3 []) (Word.mk 0 []) (Word.mk 1 []) (Word.mk 2 []))
    simpa [law05, substituteFour, Word.bind, Word.append, Word.singleton] using (Derives.appendRight substituted.symm (Word.mk 1 []))
  exact step0.trans (step1)

theorem guardedLower09 : Derives basis (Word.mk 3 [0, 1, 2, 2]) (Word.mk 3 [1, 0, 2, 2]) := by
  have step0 : Derives basis (Word.mk 3 [0, 1, 2, 2]) (Word.mk 3 [0, 0, 1, 2, 2]) := by
    have primitive : Derives basis law05.lhs law05.rhs := Derives.fromBasis (e := law05) (by simp [basis])
    have substituted := Derives.subst primitive (substituteFour (Word.mk 3 []) (Word.mk 0 []) (Word.mk 1 []) (Word.mk 2 []))
    simpa [law05, substituteFour, Word.bind, Word.append, Word.singleton] using (Derives.appendRight substituted (Word.mk 2 []))
  have step1 : Derives basis (Word.mk 3 [0, 0, 1, 2, 2]) (Word.mk 3 [0, 1, 0, 2, 2]) := by
    have primitive : Derives basis law08.lhs law08.rhs := Derives.fromBasis (e := law08) (by simp [basis])
    have substituted := Derives.subst primitive (substituteFour (Word.mk 0 []) (Word.mk 1 []) (Word.mk 2 []) (Word.mk 0 []))
    simpa [law08, substituteFour, Word.bind, Word.append, Word.singleton] using (Derives.prepend (Word.mk 3 []) substituted)
  have step2 : Derives basis (Word.mk 3 [0, 1, 0, 2, 2]) (Word.mk 3 [1, 0, 1, 2, 2]) := by
    have primitive : Derives basis law00.lhs law00.rhs := Derives.fromBasis (e := law00) (by simp [basis])
    have substituted := Derives.subst primitive (substituteFour (Word.mk 0 []) (Word.mk 0 []) (Word.mk 0 []) (Word.mk 1 []))
    simpa [law00, substituteFour, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend (Word.mk 3 []) substituted) (Word.mk 2 [2]))
  have step3 : Derives basis (Word.mk 3 [1, 0, 1, 2, 2]) (Word.mk 3 [1, 1, 0, 2, 2]) := by
    have primitive : Derives basis law08.lhs law08.rhs := Derives.fromBasis (e := law08) (by simp [basis])
    have substituted := Derives.subst primitive (substituteFour (Word.mk 1 []) (Word.mk 0 []) (Word.mk 2 []) (Word.mk 0 []))
    simpa [law08, substituteFour, Word.bind, Word.append, Word.singleton] using (Derives.prepend (Word.mk 3 []) substituted.symm)
  have step4 : Derives basis (Word.mk 3 [1, 1, 0, 2, 2]) (Word.mk 3 [1, 0, 2, 2]) := by
    have primitive : Derives basis law05.lhs law05.rhs := Derives.fromBasis (e := law05) (by simp [basis])
    have substituted := Derives.subst primitive (substituteFour (Word.mk 3 []) (Word.mk 1 []) (Word.mk 0 []) (Word.mk 2 []))
    simpa [law05, substituteFour, Word.bind, Word.append, Word.singleton] using (Derives.appendRight substituted.symm (Word.mk 2 []))
  exact step0.trans (step1.trans (step2.trans (step3.trans (step4))))

theorem squarePrefix (word suffix : Word Nat) :
    Derives basis ((word ++ word) ++ suffix) (((word ++ word) ++ word) ++ suffix) := by
  have primitive : Derives basis law01.lhs law01.rhs := Derives.fromBasis (e := law01) (by simp [basis])
  have substituted := Derives.subst primitive (substituteFour word word suffix word)
  simpa [law01, substituteFour, Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted

theorem sandwich (u v : Word Nat) : Derives basis ((u ++ v) ++ u) ((v ++ u) ++ v) := by
  have primitive : Derives basis law00.lhs law00.rhs := Derives.fromBasis (e := law00) (by simp [basis])
  have substituted := Derives.subst primitive (substituteFour u u u v)
  simpa [law00, substituteFour, Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted

theorem crossDuplicate (u v : Word Nat) : Derives basis ((u ++ v) ++ u) (((v ++ v) ++ u) ++ v) := by
  have primitive : Derives basis law02.lhs law02.rhs := Derives.fromBasis (e := law02) (by simp [basis])
  have substituted := Derives.subst primitive (substituteFour u u u v)
  simpa [law02, substituteFour, Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted

theorem headInside (u v : Word Nat) : Derives basis ((u ++ v) ++ u) (((u ++ u) ++ v) ++ u) :=
  (sandwich u v).trans (crossDuplicate v u)

theorem mix (a b word : Word Nat) :
    Derives basis ((((a ++ b) ++ a) ++ a) ++ word) ((((b ++ a) ++ a) ++ b) ++ word) := by
  have primitive : Derives basis law03.lhs law03.rhs := Derives.fromBasis (e := law03) (by simp [basis])
  have substituted := Derives.subst primitive (substituteFour a b a a)
  have rotated : Derives basis (((b ++ a) ++ a) ++ b) (((a ++ b) ++ a) ++ a) := by
    simpa [law03, substituteFour, Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted
  exact Derives.appendRight rotated.symm word

theorem guardedLowerAxioms (identity : Identity Nat) (member : identity ∈ S5_203.basis)
    (stem : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis (stem ++ identity.lhs.bind substitution) (stem ++ identity.rhs.bind substitution) := by
  simp only [S5_203.basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Derives basis (stem ++ (Word.mk 0 [0, 0]).bind substitution)
      (stem ++ (Word.mk 0 [0, 0, 0]).bind substitution)
    have substituted := Derives.subst guardedLower00 (substituteFour (substitution 0) (substitution 1) (substitution 2) stem)
    simpa [substituteFour, Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted
  · change Derives basis (stem ++ (Word.mk 0 [0, 1]).bind substitution)
      (stem ++ (Word.mk 0 [0, 0, 1]).bind substitution)
    have substituted := Derives.subst guardedLower01 (substituteFour (substitution 0) (substitution 1) (substitution 2) stem)
    simpa [substituteFour, Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted
  · change Derives basis (stem ++ (Word.mk 0 [1, 0]).bind substitution)
      (stem ++ (Word.mk 1 [0, 1]).bind substitution)
    have substituted := Derives.subst guardedLower02 (substituteFour (substitution 0) (substitution 1) (substitution 2) stem)
    simpa [substituteFour, Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted
  · change Derives basis (stem ++ (Word.mk 0 [1, 0]).bind substitution)
      (stem ++ (Word.mk 0 [0, 1, 0]).bind substitution)
    have substituted := Derives.subst guardedLower03 (substituteFour (substitution 0) (substitution 1) (substitution 2) stem)
    simpa [substituteFour, Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted
  · change Derives basis (stem ++ (Word.mk 0 [1, 0]).bind substitution)
      (stem ++ (Word.mk 0 [1, 1, 1]).bind substitution)
    have substituted := Derives.subst guardedLower04 (substituteFour (substitution 0) (substitution 1) (substitution 2) stem)
    simpa [substituteFour, Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted
  · change Derives basis (stem ++ (Word.mk 0 [1, 0]).bind substitution)
      (stem ++ (Word.mk 0 [1, 1, 0, 0]).bind substitution)
    have substituted := Derives.subst guardedLower05 (substituteFour (substitution 0) (substitution 1) (substitution 2) stem)
    simpa [substituteFour, Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted
  · change Derives basis (stem ++ (Word.mk 0 [1, 1]).bind substitution)
      (stem ++ (Word.mk 0 [0, 1, 1]).bind substitution)
    have substituted := Derives.subst guardedLower06 (substituteFour (substitution 0) (substitution 1) (substitution 2) stem)
    simpa [substituteFour, Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted
  · change Derives basis (stem ++ (Word.mk 0 [1, 2]).bind substitution)
      (stem ++ (Word.mk 0 [0, 1, 2]).bind substitution)
    have substituted := Derives.subst guardedLower07 (substituteFour (substitution 0) (substitution 1) (substitution 2) stem)
    simpa [substituteFour, Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted
  · change Derives basis (stem ++ (Word.mk 0 [1, 2, 0]).bind substitution)
      (stem ++ (Word.mk 0 [1, 2, 1]).bind substitution)
    have substituted := Derives.subst guardedLower08 (substituteFour (substitution 0) (substitution 1) (substitution 2) stem)
    simpa [substituteFour, Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted
  · change Derives basis (stem ++ (Word.mk 0 [1, 2, 2]).bind substitution)
      (stem ++ (Word.mk 1 [0, 2, 2]).bind substitution)
    have substituted := Derives.subst guardedLower09 (substituteFour (substitution 0) (substitution 1) (substitution 2) stem)
    simpa [substituteFour, Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted

theorem liftLower {left right : Word Nat} (derivation : Derives S5_203.basis left right) (stem : Word Nat) :
    Derives basis (stem ++ left) (stem ++ right) := by
  simpa only [bindSingleton] using Msg0442Initial.liftGuarded guardedLowerAxioms derivation stem Word.singleton

def rules : InitialMarkerLongJoin.Rules basis S5_203.basis where
  lift := liftLower
  squarePrefix := squarePrefix
  headInside := headInside
  mix := mix

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0443Pair2675
