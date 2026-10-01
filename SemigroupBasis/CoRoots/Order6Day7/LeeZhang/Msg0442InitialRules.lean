import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0442InitialPresentation

/-! All inputs to InitialMarkerJoin.Rules are derived from the exact approved
lists. The lower theories are replayed by induction on Derives, retaining
arbitrary substitutions and a genuine nonempty left context. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0442Initial

open SemigroupBasis
open Msg0442Cyclic (substituteFour bindAppend bindBind bindSingleton)

theorem liftGuarded {basis lowerBasis : List (Identity Nat)}
    (axioms : ∀ identity : Identity Nat, identity ∈ lowerBasis →
      ∀ stem : Word Nat, ∀ substitution : Nat → Word Nat,
        Derives basis (stem ++ identity.lhs.bind substitution) (stem ++ identity.rhs.bind substitution))
    {left right : Word Nat} (derivation : Derives lowerBasis left right)
    (stem : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis (stem ++ left.bind substitution) (stem ++ right.bind substitution) := by
  induction derivation generalizing stem substitution with
  | fromBasis member => exact axioms _ member stem substitution
  | refl => exact Derives.refl _
  | symm _ ih => exact (ih stem substitution).symm
  | trans _ _ first second => exact (first stem substitution).trans (second stem substitution)
  | prepend before _ ih =>
      simpa [bindAppend, Word.append_assoc] using ih (stem ++ before.bind substitution) substitution
  | appendRight _ after ih =>
      simpa [bindAppend, Word.append_assoc] using
        Derives.appendRight (ih stem substitution) (after.bind substitution)
  | subst _ next ih =>
      simpa [bindBind] using ih stem (fun x => (next x).bind substitution)

namespace Group1040

theorem power (word : Word Nat) : Derives basis (word ++ word) ((word ++ word) ++ word) := by
  have base : Derives basis law00.lhs law00.rhs := Derives.fromBasis (e := law00) (by simp [basis])
  have substituted := Derives.subst base (substituteFour word word word word)
  simpa [law00, substituteFour, Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted

theorem sandwich (u v : Word Nat) : Derives basis ((u ++ v) ++ u) ((v ++ u) ++ v) := by
  have base : Derives basis law01.lhs law01.rhs := Derives.fromBasis (e := law01) (by simp [basis])
  have substituted := Derives.subst base (substituteFour u u u v)
  simpa [law01, substituteFour, Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted

theorem crossDuplicate (u v : Word Nat) : Derives basis ((u ++ v) ++ u) (((v ++ v) ++ u) ++ v) := by
  have base : Derives basis law02.lhs law02.rhs := Derives.fromBasis (e := law02) (by simp [basis])
  have substituted := Derives.subst base (substituteFour u u u v)
  simpa [law02, substituteFour, Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted

theorem headInside (u v : Word Nat) : Derives basis ((u ++ v) ++ u) (((u ++ u) ++ v) ++ u) :=
  (sandwich u v).trans (crossDuplicate v u)

theorem guardedRotate (stem u v : Word Nat) :
    Derives basis (stem ++ ((u ++ v) ++ u)) (stem ++ ((v ++ u) ++ u)) := by
  have base : Derives basis law03.lhs law03.rhs := Derives.fromBasis (e := law03) (by simp [basis])
  have substituted := Derives.subst base (substituteFour stem u v stem)
  simpa [law03, substituteFour, Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted

theorem guardedCopy (stem u v : Word Nat) :
    Derives basis (stem ++ ((u ++ v) ++ u)) (stem ++ ((u ++ v) ++ v)) :=
  (Derives.prepend stem (sandwich u v)).trans (guardedRotate stem v u)

theorem guardedLongInsertion (stem u v w : Word Nat) :
    Derives basis (stem ++ ((u ++ v) ++ w)) (stem ++ (((u ++ u) ++ v) ++ w)) := by
  have base : Derives basis law06.lhs law06.rhs := Derives.fromBasis (e := law06) (by simp [basis])
  have substituted := Derives.subst base (substituteFour stem u v w)
  simpa [law06, Msg0442Cyclic.duplicationLaw, substituteFour, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

theorem mix (a b word : Word Nat) :
    Derives basis ((((a ++ b) ++ a) ++ a) ++ word) ((((b ++ a) ++ a) ++ b) ++ word) := by
  have base : Derives basis law04.lhs law04.rhs := Derives.fromBasis (e := law04) (by simp [basis])
  have substituted := Derives.subst base (substituteFour a b a a)
  have rotated : Derives basis (((b ++ a) ++ a) ++ b) (((a ++ b) ++ a) ++ a) := by
    simpa [law04, substituteFour, Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted
  exact Derives.appendRight rotated.symm word

theorem guardedLowerAxioms (identity : Identity Nat) (member : identity ∈ S5_83.basis)
    (stem : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis (stem ++ identity.lhs.bind substitution) (stem ++ identity.rhs.bind substitution) := by
  simp only [S5_83.basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · change Derives basis (stem ++ (Word.mk 0 [0]).bind substitution)
      (stem ++ (Word.mk 0 [0, 0]).bind substitution)
    simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      Derives.prepend stem (power (substitution 0))
  · change Derives basis (stem ++ (Word.mk 0 [1, 0]).bind substitution)
      (stem ++ (Word.mk 0 [1, 1]).bind substitution)
    simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      guardedCopy stem (substitution 0) (substitution 1)
  · change Derives basis (stem ++ (Word.mk 0 [1, 0]).bind substitution)
      (stem ++ (Word.mk 1 [0, 0]).bind substitution)
    simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      guardedRotate stem (substitution 0) (substitution 1)
  · change Derives basis (stem ++ (Word.mk 0 [1, 2]).bind substitution)
      (stem ++ (Word.mk 0 [0, 1, 2]).bind substitution)
    simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      guardedLongInsertion stem (substitution 0) (substitution 1) (substitution 2)

theorem liftLower {left right : Word Nat} (derivation : Derives S5_83.basis left right) (stem : Word Nat) :
    Derives basis (stem ++ left) (stem ++ right) := by
  simpa only [bindSingleton] using liftGuarded guardedLowerAxioms derivation stem Word.singleton

def rules : InitialMarkerJoin.Rules basis S5_83.basis where
  lift := liftLower
  power := power
  headInside := headInside
  mix := mix

end Group1040

namespace Single2979

theorem power (word : Word Nat) : Derives basis (word ++ word) ((word ++ word) ++ word) := by
  have base : Derives basis law00.lhs law00.rhs := Derives.fromBasis (e := law00) (by simp [basis])
  have substituted := Derives.subst base (substituteFour word word word word)
  simpa [law00, Group1040.law00, substituteFour, Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted

theorem headInside (u v : Word Nat) : Derives basis ((u ++ v) ++ u) (((u ++ u) ++ v) ++ u) := by
  have base : Derives basis law01.lhs law01.rhs := Derives.fromBasis (e := law01) (by simp [basis])
  have substituted := Derives.subst base (substituteFour u u v u)
  simpa [law01, substituteFour, Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted

theorem guardedMarkerSwitch (stem u v : Word Nat) :
    Derives basis (stem ++ ((u ++ v) ++ v)) (stem ++ ((v ++ u) ++ u)) := by
  have base : Derives basis law02.lhs law02.rhs := Derives.fromBasis (e := law02) (by simp [basis])
  have substituted := Derives.subst base (substituteFour stem u v stem)
  simpa [law02, substituteFour, Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted

theorem guardedLongInsertion (stem u v w : Word Nat) :
    Derives basis (stem ++ ((u ++ v) ++ w)) (stem ++ (((u ++ u) ++ v) ++ w)) := by
  have base : Derives basis law05.lhs law05.rhs := Derives.fromBasis (e := law05) (by simp [basis])
  have substituted := Derives.subst base (substituteFour stem u v w)
  simpa [law05, Msg0442Cyclic.duplicationLaw, substituteFour, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

theorem mix (a b word : Word Nat) :
    Derives basis ((((a ++ b) ++ a) ++ a) ++ word) ((((b ++ a) ++ a) ++ b) ++ word) := by
  have base : Derives basis law06.lhs law06.rhs := Derives.fromBasis (e := law06) (by simp [basis])
  have substituted := Derives.subst base (substituteFour a b a word)
  simpa [law06, substituteFour, Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted

theorem guardedLowerAxioms (identity : Identity Nat) (member : identity ∈ S5_240.basis)
    (stem : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis (stem ++ identity.lhs.bind substitution) (stem ++ identity.rhs.bind substitution) := by
  simp only [S5_240.basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · change Derives basis (stem ++ (Word.mk 0 [0]).bind substitution)
      (stem ++ (Word.mk 0 [0, 0]).bind substitution)
    simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      Derives.prepend stem (power (substitution 0))
  · change Derives basis (stem ++ (Word.mk 0 [1, 1]).bind substitution)
      (stem ++ (Word.mk 1 [0, 0]).bind substitution)
    simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      guardedMarkerSwitch stem (substitution 0) (substitution 1)
  · change Derives basis (stem ++ (Word.mk 0 [1, 2]).bind substitution)
      (stem ++ (Word.mk 0 [0, 1, 2]).bind substitution)
    simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      guardedLongInsertion stem (substitution 0) (substitution 1) (substitution 2)

theorem liftLower {left right : Word Nat} (derivation : Derives S5_240.basis left right) (stem : Word Nat) :
    Derives basis (stem ++ left) (stem ++ right) := by
  simpa only [bindSingleton] using liftGuarded guardedLowerAxioms derivation stem Word.singleton

def rules : InitialMarkerJoin.Rules basis S5_240.basis where
  lift := liftLower
  power := power
  headInside := headInside
  mix := mix

end Single2979
end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0442Initial
