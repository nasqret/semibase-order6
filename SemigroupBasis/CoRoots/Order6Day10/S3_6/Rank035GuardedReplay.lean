import SemigroupBasis.CoRoots.Order6Day10.S3_6.Rank035Shape

/-! Every concrete step below is a displayed-law substitution and context.
No bare M18 law is retargeted: all fifteen lower axioms retain a nonempty suffix.
The searched witnesses are only inputs; the Lean kernel checks every chain. -/

namespace SemigroupBasis.CoRoots.Order6Day10.S3_6.Rank035GuardedReplay

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Day10.S3_6.Rank035Shape

theorem lower_00 :
    Derives basis (Word.mk 0 [0, 4]) (Word.mk 0 [0, 0, 0, 4]) := by
  have step0 : Derives basis (Word.mk 0 [0, 4]) (Word.mk 0 [0, 0, 0, 4]) := by
    have primitive : Derives basis law00.lhs law00.rhs :=
      Derives.fromBasis (e := law00) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | _ => Word.singleton 0)
    simpa [law00, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.appendRight mapped (Word.mk 4 []))
  exact step0

theorem lower_01 :
    Derives basis (Word.mk 0 [0, 0, 1, 0, 4]) (Word.mk 0 [1, 0, 4]) := by
  have step0 : Derives basis (Word.mk 0 [0, 0, 1, 0, 4]) (Word.mk 0 [1, 0, 4]) := by
    have primitive : Derives basis law04.lhs law04.rhs :=
      Derives.fromBasis (e := law04) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | 1 => (Word.mk 1 [])
        | _ => Word.singleton 0)
    simpa [law04, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.appendRight mapped.symm (Word.mk 4 []))
  exact step0

theorem lower_02 :
    Derives basis (Word.mk 0 [0, 1, 4]) (Word.mk 1 [0, 0, 4]) := by
  have step0 : Derives basis (Word.mk 0 [0, 1, 4]) (Word.mk 1 [0, 0, 4]) := by
    have primitive : Derives basis law13.lhs law13.rhs :=
      Derives.fromBasis (e := law13) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | 1 => (Word.mk 1 [])
        | 2 => (Word.mk 4 [])
        | _ => Word.singleton 0)
    simpa [law13, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped.symm
  exact step0

theorem lower_03 :
    Derives basis (Word.mk 0 [0, 2, 3, 2, 4]) (Word.mk 0 [2, 0, 3, 2, 4]) := by
  have step0 : Derives basis (Word.mk 0 [0, 2, 3, 2, 4]) (Word.mk 0 [2, 0, 3, 2, 4]) := by
    have primitive : Derives basis law12.lhs law12.rhs :=
      Derives.fromBasis (e := law12) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | 1 => (Word.mk 2 [])
        | 2 => (Word.mk 3 [])
        | _ => Word.singleton 0)
    simpa [law12, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.appendRight mapped.symm (Word.mk 4 []))
  exact step0

theorem lower_04 :
    Derives basis (Word.mk 0 [0, 2, 2, 4]) (Word.mk 0 [2, 0, 2, 4]) := by
  have step0 : Derives basis (Word.mk 0 [0, 2, 2, 4]) (Word.mk 0 [2, 0, 2, 4]) := by
    have primitive : Derives basis law09.lhs law09.rhs :=
      Derives.fromBasis (e := law09) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | 1 => (Word.mk 2 [])
        | _ => Word.singleton 0)
    simpa [law09, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.appendRight mapped.symm (Word.mk 4 []))
  exact step0

theorem lower_05 :
    Derives basis (Word.mk 0 [1, 0, 3, 1, 4]) (Word.mk 1 [0, 0, 3, 1, 4]) := by
  have step0 : Derives basis (Word.mk 0 [1, 0, 3, 1, 4]) (Word.mk 0 [0, 1, 3, 1, 4]) := by
    have primitive : Derives basis law12.lhs law12.rhs :=
      Derives.fromBasis (e := law12) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | 1 => (Word.mk 1 [])
        | 2 => (Word.mk 3 [])
        | _ => Word.singleton 0)
    simpa [law12, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.appendRight mapped (Word.mk 4 []))
  have step1 : Derives basis (Word.mk 0 [0, 1, 3, 1, 4]) (Word.mk 1 [0, 0, 3, 1, 4]) := by
    have primitive : Derives basis law13.lhs law13.rhs :=
      Derives.fromBasis (e := law13) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | 1 => (Word.mk 1 [])
        | 2 => (Word.mk 3 [])
        | _ => Word.singleton 0)
    simpa [law13, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.appendRight mapped.symm (Word.mk 1 [4]))
  exact step0.trans (step1)

theorem lower_06 :
    Derives basis (Word.mk 0 [1, 0, 1, 4]) (Word.mk 1 [0, 0, 1, 4]) := by
  have step0 : Derives basis (Word.mk 0 [1, 0, 1, 4]) (Word.mk 0 [0, 1, 1, 4]) := by
    have primitive : Derives basis law09.lhs law09.rhs :=
      Derives.fromBasis (e := law09) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | 1 => (Word.mk 1 [])
        | _ => Word.singleton 0)
    simpa [law09, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.appendRight mapped (Word.mk 4 []))
  have step1 : Derives basis (Word.mk 0 [0, 1, 1, 4]) (Word.mk 1 [0, 0, 1, 4]) := by
    have primitive : Derives basis law08.lhs law08.rhs :=
      Derives.fromBasis (e := law08) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | 1 => (Word.mk 1 [])
        | _ => Word.singleton 0)
    simpa [law08, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.appendRight mapped.symm (Word.mk 4 []))
  exact step0.trans (step1)

theorem lower_07 :
    Derives basis (Word.mk 0 [1, 0, 2, 3, 2, 4]) (Word.mk 0 [1, 2, 0, 3, 2, 4]) := by
  have step0 : Derives basis (Word.mk 0 [1, 0, 2, 3, 2, 4]) (Word.mk 0 [1, 0, 0, 0, 2, 3, 2, 4]) := by
    have primitive : Derives basis law02.lhs law02.rhs :=
      Derives.fromBasis (e := law02) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | 1 => (Word.mk 1 [])
        | _ => Word.singleton 0)
    simpa [law02, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.appendRight mapped.symm (Word.mk 2 [3, 2, 4]))
  have step1 : Derives basis (Word.mk 0 [1, 0, 0, 0, 2, 3, 2, 4]) (Word.mk 0 [1, 0, 0, 2, 0, 3, 2, 4]) := by
    have primitive : Derives basis law12.lhs law12.rhs :=
      Derives.fromBasis (e := law12) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | 1 => (Word.mk 2 [])
        | 2 => (Word.mk 3 [])
        | _ => Word.singleton 0)
    simpa [law12, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.appendRight (Derives.prepend (Word.mk 0 [1, 0]) mapped.symm) (Word.mk 4 []))
  have step2 : Derives basis (Word.mk 0 [1, 0, 0, 2, 0, 3, 2, 4]) (Word.mk 0 [1, 2, 0, 0, 0, 3, 2, 4]) := by
    have primitive : Derives basis law01.lhs law01.rhs :=
      Derives.fromBasis (e := law01) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | 1 => (Word.mk 2 [])
        | _ => Word.singleton 0)
    simpa [law01, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.appendRight (Derives.prepend (Word.mk 0 [1]) mapped.symm) (Word.mk 3 [2, 4]))
  have step3 : Derives basis (Word.mk 0 [1, 2, 0, 0, 0, 3, 2, 4]) (Word.mk 0 [1, 2, 0, 3, 2, 4]) := by
    have primitive : Derives basis law02.lhs law02.rhs :=
      Derives.fromBasis (e := law02) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | 1 => (Word.mk 1 [2])
        | _ => Word.singleton 0)
    simpa [law02, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.appendRight mapped (Word.mk 3 [2, 4]))
  exact step0.trans (step1.trans (step2.trans (step3)))

theorem lower_08 :
    Derives basis (Word.mk 0 [1, 0, 2, 2, 4]) (Word.mk 0 [1, 2, 0, 2, 4]) := by
  have step0 : Derives basis (Word.mk 0 [1, 0, 2, 2, 4]) (Word.mk 2 [2, 0, 1, 0, 4]) := by
    have primitive : Derives basis law03.lhs law03.rhs :=
      Derives.fromBasis (e := law03) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 2 [])
        | 1 => (Word.mk 0 [])
        | 2 => (Word.mk 1 [])
        | _ => Word.singleton 0)
    simpa [law03, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.appendRight mapped (Word.mk 4 []))
  have step1 : Derives basis (Word.mk 2 [2, 0, 1, 0, 4]) (Word.mk 0 [1, 2, 0, 2, 4]) := by
    have primitive : Derives basis law05.lhs law05.rhs :=
      Derives.fromBasis (e := law05) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 2 [])
        | 1 => (Word.mk 0 [])
        | 2 => (Word.mk 1 [])
        | _ => Word.singleton 0)
    simpa [law05, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.appendRight mapped.symm (Word.mk 4 []))
  exact step0.trans (step1)

theorem lower_09 :
    Derives basis (Word.mk 0 [1, 2, 3, 0, 2, 4]) (Word.mk 0 [1, 2, 3, 2, 0, 4]) := by
  have step0 : Derives basis (Word.mk 0 [1, 2, 3, 0, 2, 4]) (Word.mk 0 [1, 2, 3, 0, 0, 0, 2, 4]) := by
    have primitive : Derives basis law02.lhs law02.rhs :=
      Derives.fromBasis (e := law02) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | 1 => (Word.mk 1 [2, 3])
        | _ => Word.singleton 0)
    simpa [law02, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.appendRight mapped.symm (Word.mk 2 [4]))
  have step1 : Derives basis (Word.mk 0 [1, 2, 3, 0, 0, 0, 2, 4]) (Word.mk 0 [1, 0, 0, 2, 3, 0, 2, 4]) := by
    have primitive : Derives basis law01.lhs law01.rhs :=
      Derives.fromBasis (e := law01) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | 1 => (Word.mk 2 [3])
        | _ => Word.singleton 0)
    simpa [law01, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.appendRight (Derives.prepend (Word.mk 0 [1]) mapped) (Word.mk 2 [4]))
  have step2 : Derives basis (Word.mk 0 [1, 0, 0, 2, 3, 0, 2, 4]) (Word.mk 0 [1, 2, 3, 0, 0, 2, 0, 4]) := by
    have primitive : Derives basis law05.lhs law05.rhs :=
      Derives.fromBasis (e := law05) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | 1 => (Word.mk 2 [])
        | 2 => (Word.mk 3 [0])
        | _ => Word.singleton 0)
    simpa [law05, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.appendRight (Derives.prepend (Word.mk 0 [1]) mapped.symm) (Word.mk 4 []))
  have step3 : Derives basis (Word.mk 0 [1, 2, 3, 0, 0, 2, 0, 4]) (Word.mk 0 [1, 2, 3, 2, 0, 0, 0, 4]) := by
    have primitive : Derives basis law01.lhs law01.rhs :=
      Derives.fromBasis (e := law01) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | 1 => (Word.mk 2 [])
        | _ => Word.singleton 0)
    simpa [law01, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.appendRight (Derives.prepend (Word.mk 0 [1, 2, 3]) mapped.symm) (Word.mk 4 []))
  have step4 : Derives basis (Word.mk 0 [1, 2, 3, 2, 0, 0, 0, 4]) (Word.mk 0 [1, 2, 3, 2, 0, 4]) := by
    have primitive : Derives basis law02.lhs law02.rhs :=
      Derives.fromBasis (e := law02) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | 1 => (Word.mk 1 [2, 3, 2])
        | _ => Word.singleton 0)
    simpa [law02, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.appendRight mapped (Word.mk 4 []))
  exact step0.trans (step1.trans (step2.trans (step3.trans (step4))))

theorem lower_10 :
    Derives basis (Word.mk 0 [1, 2, 0, 3, 1, 4]) (Word.mk 1 [0, 2, 0, 3, 1, 4]) := by
  have step0 : Derives basis (Word.mk 0 [1, 2, 0, 3, 1, 4]) (Word.mk 0 [1, 2, 0, 3, 1, 1, 1, 4]) := by
    have primitive : Derives basis law02.lhs law02.rhs :=
      Derives.fromBasis (e := law02) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 1 [])
        | 1 => (Word.mk 2 [0, 3])
        | _ => Word.singleton 0)
    simpa [law02, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.appendRight (Derives.prepend (Word.mk 0 []) mapped.symm) (Word.mk 4 []))
  have step1 : Derives basis (Word.mk 0 [1, 2, 0, 3, 1, 1, 1, 4]) (Word.mk 1 [1, 0, 1, 2, 0, 3, 1, 4]) := by
    have primitive : Derives basis law01.lhs law01.rhs :=
      Derives.fromBasis (e := law01) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 1 [])
        | 1 => (Word.mk 0 [1, 2, 0, 3])
        | _ => Word.singleton 0)
    simpa [law01, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.appendRight mapped (Word.mk 4 []))
  have step2 : Derives basis (Word.mk 1 [1, 0, 1, 2, 0, 3, 1, 4]) (Word.mk 1 [1, 1, 0, 2, 0, 3, 1, 4]) := by
    have primitive : Derives basis law12.lhs law12.rhs :=
      Derives.fromBasis (e := law12) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 1 [])
        | 1 => (Word.mk 0 [])
        | 2 => (Word.mk 2 [])
        | _ => Word.singleton 0)
    simpa [law12, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.appendRight (Derives.prepend (Word.mk 1 []) mapped) (Word.mk 3 [1, 4]))
  have step3 : Derives basis (Word.mk 1 [1, 1, 0, 2, 0, 3, 1, 4]) (Word.mk 1 [0, 2, 0, 3, 1, 4]) := by
    have primitive : Derives basis law04.lhs law04.rhs :=
      Derives.fromBasis (e := law04) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 1 [])
        | 1 => (Word.mk 0 [2, 0, 3])
        | _ => Word.singleton 0)
    simpa [law04, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.appendRight mapped.symm (Word.mk 4 []))
  exact step0.trans (step1.trans (step2.trans (step3)))

theorem lower_11 :
    Derives basis (Word.mk 0 [1, 2, 0, 1, 4]) (Word.mk 1 [0, 2, 0, 1, 4]) := by
  have step0 : Derives basis (Word.mk 0 [1, 2, 0, 1, 4]) (Word.mk 1 [0, 2, 0, 1, 4]) := by
    have primitive : Derives basis law10.lhs law10.rhs :=
      Derives.fromBasis (e := law10) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | 1 => (Word.mk 1 [])
        | 2 => (Word.mk 2 [])
        | _ => Word.singleton 0)
    simpa [law10, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.appendRight mapped.symm (Word.mk 4 []))
  exact step0

theorem lower_12 :
    Derives basis (Word.mk 0 [1, 2, 0, 2, 4]) (Word.mk 0 [1, 2, 2, 0, 4]) := by
  have step0 : Derives basis (Word.mk 0 [1, 2, 0, 2, 4]) (Word.mk 2 [2, 0, 1, 0, 4]) := by
    have primitive : Derives basis law05.lhs law05.rhs :=
      Derives.fromBasis (e := law05) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 2 [])
        | 1 => (Word.mk 0 [])
        | 2 => (Word.mk 1 [])
        | _ => Word.singleton 0)
    simpa [law05, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.appendRight mapped (Word.mk 4 []))
  have step1 : Derives basis (Word.mk 2 [2, 0, 1, 0, 4]) (Word.mk 0 [1, 2, 2, 0, 4]) := by
    have primitive : Derives basis law13.lhs law13.rhs :=
      Derives.fromBasis (e := law13) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 2 [])
        | 1 => (Word.mk 0 [1])
        | 2 => (Word.mk 0 [])
        | _ => Word.singleton 0)
    simpa [law13, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.appendRight mapped.symm (Word.mk 4 []))
  exact step0.trans (step1)

theorem lower_13 :
    Derives basis (Word.mk 0 [2, 3, 0, 2, 4]) (Word.mk 0 [2, 3, 2, 0, 4]) := by
  have step0 : Derives basis (Word.mk 0 [2, 3, 0, 2, 4]) (Word.mk 0 [2, 3, 2, 0, 4]) := by
    have primitive : Derives basis law07.lhs law07.rhs :=
      Derives.fromBasis (e := law07) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | 1 => (Word.mk 2 [])
        | 2 => (Word.mk 3 [])
        | _ => Word.singleton 0)
    simpa [law07, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.appendRight mapped.symm (Word.mk 4 []))
  exact step0

theorem lower_14 :
    Derives basis (Word.mk 0 [2, 0, 2, 4]) (Word.mk 0 [2, 2, 0, 4]) := by
  have step0 : Derives basis (Word.mk 0 [2, 0, 2, 4]) (Word.mk 0 [0, 2, 2, 4]) := by
    have primitive : Derives basis law09.lhs law09.rhs :=
      Derives.fromBasis (e := law09) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | 1 => (Word.mk 2 [])
        | _ => Word.singleton 0)
    simpa [law09, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.appendRight mapped (Word.mk 4 []))
  have step1 : Derives basis (Word.mk 0 [0, 2, 2, 4]) (Word.mk 0 [2, 2, 0, 4]) := by
    have primitive : Derives basis law06.lhs law06.rhs :=
      Derives.fromBasis (e := law06) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | 1 => (Word.mk 2 [])
        | _ => Word.singleton 0)
    simpa [law06, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.appendRight mapped.symm (Word.mk 4 []))
  exact step0.trans (step1)

theorem squares_commute_literal :
    Derives basis (Word.mk 0 [0, 1, 1]) (Word.mk 1 [1, 0, 0]) := by
  have step0 : Derives basis (Word.mk 0 [0, 1, 1]) (Word.mk 0 [1, 1, 0]) := by
    have primitive : Derives basis law06.lhs law06.rhs :=
      Derives.fromBasis (e := law06) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | 1 => (Word.mk 1 [])
        | _ => Word.singleton 0)
    simpa [law06, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped.symm
  have step1 : Derives basis (Word.mk 0 [1, 1, 0]) (Word.mk 1 [1, 0, 0]) := by
    have primitive : Derives basis law08.lhs law08.rhs :=
      Derives.fromBasis (e := law08) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 1 [])
        | 1 => (Word.mk 0 [])
        | _ => Word.singleton 0)
    simpa [law08, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped
  exact step0.trans (step1)

private def guardSubstitution (substitution : Nat → Word Nat) (suffix : Word Nat) : Nat → Word Nat
  | 0 => substitution 0
  | 1 => substitution 1
  | 2 => substitution 2
  | 3 => substitution 3
  | 4 => suffix
  | n + 5 => substitution (n + 5)

/-- Every exact lower axiom, under arbitrary nonempty substitution and suffix. -/
theorem guarded_lower_axiom (identity : Identity Nat) (member : identity ∈ lowerBasis)
    (substitution : Nat → Word Nat) (suffix : Word Nat) :
    Derives basis (identity.lhs.bind substitution ++ suffix)
      (identity.rhs.bind substitution ++ suffix) := by
  simp only [lowerBasis, SemigroupBasis.CoRoots.S5_254.basis,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Derives basis ((Word.mk 0 [0]).bind substitution ++ suffix)
      ((Word.mk 0 [0, 0, 0]).bind substitution ++ suffix)
    have step := Derives.subst lower_00 (guardSubstitution substitution suffix)
    simpa [guardSubstitution, Word.bind, Word.append, Word.singleton, Word.append_assoc] using step
  · change Derives basis ((Word.mk 0 [0, 0, 1, 0]).bind substitution ++ suffix)
      ((Word.mk 0 [1, 0]).bind substitution ++ suffix)
    have step := Derives.subst lower_01 (guardSubstitution substitution suffix)
    simpa [guardSubstitution, Word.bind, Word.append, Word.singleton, Word.append_assoc] using step
  · change Derives basis ((Word.mk 0 [0, 1]).bind substitution ++ suffix)
      ((Word.mk 1 [0, 0]).bind substitution ++ suffix)
    have step := Derives.subst lower_02 (guardSubstitution substitution suffix)
    simpa [guardSubstitution, Word.bind, Word.append, Word.singleton, Word.append_assoc] using step
  · change Derives basis ((Word.mk 0 [0, 2, 3, 2]).bind substitution ++ suffix)
      ((Word.mk 0 [2, 0, 3, 2]).bind substitution ++ suffix)
    have step := Derives.subst lower_03 (guardSubstitution substitution suffix)
    simpa [guardSubstitution, Word.bind, Word.append, Word.singleton, Word.append_assoc] using step
  · change Derives basis ((Word.mk 0 [0, 2, 2]).bind substitution ++ suffix)
      ((Word.mk 0 [2, 0, 2]).bind substitution ++ suffix)
    have step := Derives.subst lower_04 (guardSubstitution substitution suffix)
    simpa [guardSubstitution, Word.bind, Word.append, Word.singleton, Word.append_assoc] using step
  · change Derives basis ((Word.mk 0 [1, 0, 3, 1]).bind substitution ++ suffix)
      ((Word.mk 1 [0, 0, 3, 1]).bind substitution ++ suffix)
    have step := Derives.subst lower_05 (guardSubstitution substitution suffix)
    simpa [guardSubstitution, Word.bind, Word.append, Word.singleton, Word.append_assoc] using step
  · change Derives basis ((Word.mk 0 [1, 0, 1]).bind substitution ++ suffix)
      ((Word.mk 1 [0, 0, 1]).bind substitution ++ suffix)
    have step := Derives.subst lower_06 (guardSubstitution substitution suffix)
    simpa [guardSubstitution, Word.bind, Word.append, Word.singleton, Word.append_assoc] using step
  · change Derives basis ((Word.mk 0 [1, 0, 2, 3, 2]).bind substitution ++ suffix)
      ((Word.mk 0 [1, 2, 0, 3, 2]).bind substitution ++ suffix)
    have step := Derives.subst lower_07 (guardSubstitution substitution suffix)
    simpa [guardSubstitution, Word.bind, Word.append, Word.singleton, Word.append_assoc] using step
  · change Derives basis ((Word.mk 0 [1, 0, 2, 2]).bind substitution ++ suffix)
      ((Word.mk 0 [1, 2, 0, 2]).bind substitution ++ suffix)
    have step := Derives.subst lower_08 (guardSubstitution substitution suffix)
    simpa [guardSubstitution, Word.bind, Word.append, Word.singleton, Word.append_assoc] using step
  · change Derives basis ((Word.mk 0 [1, 2, 3, 0, 2]).bind substitution ++ suffix)
      ((Word.mk 0 [1, 2, 3, 2, 0]).bind substitution ++ suffix)
    have step := Derives.subst lower_09 (guardSubstitution substitution suffix)
    simpa [guardSubstitution, Word.bind, Word.append, Word.singleton, Word.append_assoc] using step
  · change Derives basis ((Word.mk 0 [1, 2, 0, 3, 1]).bind substitution ++ suffix)
      ((Word.mk 1 [0, 2, 0, 3, 1]).bind substitution ++ suffix)
    have step := Derives.subst lower_10 (guardSubstitution substitution suffix)
    simpa [guardSubstitution, Word.bind, Word.append, Word.singleton, Word.append_assoc] using step
  · change Derives basis ((Word.mk 0 [1, 2, 0, 1]).bind substitution ++ suffix)
      ((Word.mk 1 [0, 2, 0, 1]).bind substitution ++ suffix)
    have step := Derives.subst lower_11 (guardSubstitution substitution suffix)
    simpa [guardSubstitution, Word.bind, Word.append, Word.singleton, Word.append_assoc] using step
  · change Derives basis ((Word.mk 0 [1, 2, 0, 2]).bind substitution ++ suffix)
      ((Word.mk 0 [1, 2, 2, 0]).bind substitution ++ suffix)
    have step := Derives.subst lower_12 (guardSubstitution substitution suffix)
    simpa [guardSubstitution, Word.bind, Word.append, Word.singleton, Word.append_assoc] using step
  · change Derives basis ((Word.mk 0 [2, 3, 0, 2]).bind substitution ++ suffix)
      ((Word.mk 0 [2, 3, 2, 0]).bind substitution ++ suffix)
    have step := Derives.subst lower_13 (guardSubstitution substitution suffix)
    simpa [guardSubstitution, Word.bind, Word.append, Word.singleton, Word.append_assoc] using step
  · change Derives basis ((Word.mk 0 [2, 0, 2]).bind substitution ++ suffix)
      ((Word.mk 0 [2, 2, 0]).bind substitution ++ suffix)
    have step := Derives.subst lower_14 (guardSubstitution substitution suffix)
    simpa [guardSubstitution, Word.bind, Word.append, Word.singleton, Word.append_assoc] using step

private theorem bind_append
    (left right : Word Nat) (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution = left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (word : Word Nat) (first second : Nat → Word Nat) :
    (word.bind first).bind second = word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) : word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- Replay a complete M18 derivation only behind an unchanged nonempty suffix. -/
theorem liftLowerWithSuffix {left right : Word Nat}
    (derivation : Derives lowerBasis left right)
    (suffix : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis (left.bind substitution ++ suffix) (right.bind substitution ++ suffix) := by
  induction derivation generalizing suffix substitution with
  | fromBasis member => exact guarded_lower_axiom _ member substitution suffix
  | refl => exact Derives.refl _
  | symm _ induction => exact (induction suffix substitution).symm
  | trans _ _ first second => exact (first suffix substitution).trans (second suffix substitution)
  | prepend stem _ induction =>
      simpa [bind_append, Word.append_assoc] using
        Derives.prepend (stem.bind substitution) (induction suffix substitution)
  | appendRight _ final induction =>
      simpa [bind_append, Word.append_assoc] using
        induction (final.bind substitution ++ suffix) substitution
  | subst _ next induction =>
      simpa [bind_bind] using
        induction suffix (fun letter => (next letter).bind substitution)

private def twoWords (first second : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | n + 2 => Word.singleton (n + 2)

/-- Commutation is proved for squares, never assumed for arbitrary letters. -/
theorem derivesSquaresCommute (first second : Word Nat) :
    Derives basis ((first ++ first) ++ (second ++ second))
      ((second ++ second) ++ (first ++ first)) := by
  have step := Derives.subst squares_commute_literal (twoWords first second)
  simpa [twoWords, Word.bind, Word.append, Word.singleton, Word.append_assoc] using step

theorem derivesPower (block : Word Nat) :
    Derives basis (block ++ block) (((block ++ block) ++ block) ++ block) := by
  have primitive : Derives basis law00.lhs law00.rhs := Derives.fromBasis (e := law00) (by decide)
  have step := Derives.subst primitive (twoWords block block)
  simpa [law00, twoWords, Word.bind, Word.append, Word.singleton, Word.append_assoc] using step

theorem derivesFinalSelfPair (block gap : Word Nat) :
    Derives basis ((block ++ gap) ++ block)
      ((((block ++ gap) ++ block) ++ block) ++ block) := by
  have primitive : Derives basis law02.lhs law02.rhs := Derives.fromBasis (e := law02) (by decide)
  have step := (Derives.subst primitive (twoWords block gap)).symm
  simpa [law02, twoWords, Word.bind, Word.append, Word.singleton, Word.append_assoc] using step

/-- Actual-factor validity can be used through the already complete lower basis. -/
theorem derivesSameSuffixOfLowerValid (left right suffix : Word Nat)
    (valid : (Identity.mk left right).SatisfiedBy rightTable.semigroup) :
    Derives basis (left ++ suffix) (right ++ suffix) := by
  have lower := SemigroupBasis.CoRoots.S5_254.basisFor.2 (Identity.mk left right) valid
  simpa [bind_singleton] using liftLowerWithSuffix lower suffix Word.singleton

end SemigroupBasis.CoRoots.Order6Day10.S3_6.Rank035GuardedReplay
