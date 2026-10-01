import SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776Presentation
import SemigroupBasis.CoRoots.S5_520
import SemigroupBasis.Normalization.RightGuardedTransport

/-!
# Raw8 interpretation of the complete S5_534 factor basis after a last guard

Every source axiom is interpreted after an arbitrary nonempty suffix and
under arbitrary nonerasing substitution. The shared transport theorem then
inducts over the full Derives grammar; no finite-rank reduction is assumed.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776

open SemigroupBasis

private def substitute (a b c : Word Nat) : Nat → Word Nat
  | 0 => a
  | 1 => b
  | _ => c

theorem raw00 (a : Word Nat) :
    Derives basis ((a ++ a) ++ a) (((a ++ a) ++ a) ++ a) := by
  have seed : Derives basis law00.lhs law00.rhs :=
    Derives.fromBasis (e := law00) (by decide)
  have result := Derives.subst seed (substitute a a a)
  change Derives basis ((a ++ a) ++ a) (((a ++ a) ++ a) ++ a) at result
  exact result

theorem raw01 (a b : Word Nat) :
    Derives basis (((a ++ a) ++ a) ++ b) ((a ++ a) ++ b) := by
  have seed : Derives basis law01.lhs law01.rhs :=
    Derives.fromBasis (e := law01) (by decide)
  have result := Derives.subst seed (substitute a b b)
  change Derives basis (((a ++ a) ++ a) ++ b) ((a ++ a) ++ b) at result
  exact result

theorem raw02 (a b : Word Nat) :
    Derives basis ((a ++ a) ++ b) (((a ++ b) ++ a) ++ b) := by
  have seed : Derives basis law02.lhs law02.rhs :=
    Derives.fromBasis (e := law02) (by decide)
  have result := Derives.subst seed (substitute a b b)
  change Derives basis ((a ++ a) ++ b) (((a ++ b) ++ a) ++ b) at result
  exact result

theorem raw03 (a b : Word Nat) :
    Derives basis ((a ++ a) ++ b) ((a ++ b) ++ b) := by
  have seed : Derives basis law03.lhs law03.rhs :=
    Derives.fromBasis (e := law03) (by decide)
  have result := Derives.subst seed (substitute a b b)
  change Derives basis ((a ++ a) ++ b) ((a ++ b) ++ b) at result
  exact result

theorem raw04 (a b : Word Nat) :
    Derives basis (((a ++ a) ++ b) ++ a) ((a ++ b) ++ a) := by
  have seed : Derives basis law04.lhs law04.rhs :=
    Derives.fromBasis (e := law04) (by decide)
  have result := Derives.subst seed (substitute a b b)
  change Derives basis (((a ++ a) ++ b) ++ a) ((a ++ b) ++ a) at result
  exact result

theorem raw05 (a b c : Word Nat) :
    Derives basis (((a ++ a) ++ b) ++ c) ((a ++ b) ++ c) := by
  have seed : Derives basis law05.lhs law05.rhs :=
    Derives.fromBasis (e := law05) (by decide)
  have result := Derives.subst seed (substitute a b c)
  change Derives basis (((a ++ a) ++ b) ++ c) ((a ++ b) ++ c) at result
  exact result

theorem raw06 (a b c : Word Nat) :
    Derives basis (((a ++ b) ++ a) ++ c) ((a ++ b) ++ c) := by
  have seed : Derives basis law06.lhs law06.rhs :=
    Derives.fromBasis (e := law06) (by decide)
  have result := Derives.subst seed (substitute a b c)
  change Derives basis (((a ++ b) ++ a) ++ c) ((a ++ b) ++ c) at result
  exact result

theorem raw07 (a b c : Word Nat) :
    Derives basis ((a ++ b) ++ c) (((a ++ c) ++ b) ++ c) := by
  have seed : Derives basis law07.lhs law07.rhs :=
    Derives.fromBasis (e := law07) (by decide)
  have result := Derives.subst seed (substitute a b c)
  change Derives basis ((a ++ b) ++ c) (((a ++ c) ++ b) ++ c) at result
  exact result

/-- The four-letter interior swap is derived, not imported as a new law. -/
theorem interiorSwap (a b c d : Word Nat) :
    Derives basis (((a ++ b) ++ c) ++ d) (((a ++ c) ++ b) ++ d) := by
  have first : Derives basis (((a ++ b) ++ c) ++ d)
      (((((a ++ c) ++ d) ++ b) ++ c) ++ d) := by
    simpa only [Word.append_assoc] using raw07 a b (c ++ d)
  have middle : Derives basis (((((a ++ c) ++ d) ++ b) ++ c) ++ d)
      ((((a ++ c) ++ d) ++ b) ++ d) := by
    simpa only [Word.append_assoc] using
      Derives.prepend a (raw06 c (d ++ b) d)
  have last : Derives basis ((((a ++ c) ++ d) ++ b) ++ d)
      (((a ++ c) ++ b) ++ d) := by
    simpa only [Word.append_assoc] using
      Derives.prepend a (raw07 c b d).symm
  exact first.trans (middle.trans last)

theorem duplicateFinalBlock (a b c : Word Nat) :
    Derives basis ((a ++ b) ++ c) (((a ++ b) ++ c) ++ c) :=
  (raw07 a b c).trans (interiorSwap a c b c)

theorem lowerAxiomsAfterLast (identity : Identity Nat)
    (member : identity ∈ SemigroupBasis.CoRoots.S5_520.basis)
    (substitution : Nat → Word Nat) (suffix : Word Nat) :
    Derives basis (identity.lhs.bind substitution ++ suffix)
      (identity.rhs.bind substitution ++ suffix) := by
  simp only [SemigroupBasis.CoRoots.S5_520.basis,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · change Derives basis ((((substitution 0 ++ substitution 0) ++ substitution 0) ++ suffix))
      (((((substitution 0 ++ substitution 0) ++ substitution 0) ++ substitution 0) ++ suffix))
    exact Derives.appendRight (raw00 (substitution 0)) suffix
  · change Derives basis (((substitution 0 ++ substitution 0) ++ substitution 1) ++ suffix)
      (((substitution 0 ++ substitution 1) ++ substitution 0) ++ suffix)
    exact (raw05 (substitution 0) (substitution 1) suffix).trans
      (raw06 (substitution 0) (substitution 1) suffix).symm
  · change Derives basis (((substitution 0 ++ substitution 0) ++ substitution 1) ++ suffix)
      (((substitution 0 ++ substitution 1) ++ substitution 1) ++ suffix)
    exact Derives.appendRight (raw03 (substitution 0) (substitution 1)) suffix
  · change Derives basis (((substitution 0 ++ substitution 0) ++ substitution 1) ++ suffix)
      ((((substitution 0 ++ substitution 0) ++ substitution 0) ++ substitution 1) ++ suffix)
    exact Derives.appendRight (raw01 (substitution 0) (substitution 1)).symm suffix
  · change Derives basis (((substitution 0 ++ substitution 1) ++ substitution 2) ++ suffix)
      (((substitution 0 ++ substitution 2) ++ substitution 1) ++ suffix)
    exact interiorSwap (substitution 0) (substitution 1) (substitution 2) suffix
  · change Derives basis (((substitution 0 ++ substitution 1) ++ substitution 2) ++ suffix)
      ((((substitution 0 ++ substitution 0) ++ substitution 1) ++ substitution 2) ++ suffix)
    exact Derives.appendRight (raw05 (substitution 0) (substitution 1) (substitution 2)).symm suffix

theorem lowerDerivationAfterLast {left right : Word Nat}
    (derivation : Derives SemigroupBasis.CoRoots.S5_520.basis left right)
    (suffix : Word Nat) :
    Derives basis (left ++ suffix) (right ++ suffix) :=
  SemigroupBasis.RightGuardedTransport.transport lowerAxiomsAfterLast derivation suffix

private theorem appendLastLong (rest : List Nat) (a b c : Nat) :
    Derives basis (Word.mk a (b :: c :: rest))
      (Word.mk a (b :: c :: rest) ++
        Word.singleton (Word.mk a (b :: c :: rest)).reverse.head) := by
  induction rest generalizing a b c with
  | nil =>
      exact duplicateFinalBlock (Word.singleton a) (Word.singleton b) (Word.singleton c)
  | cons d rest ih =>
      have inside := ih b c d
      have lifted := Derives.prepend (Word.singleton a) inside
      simpa only [Word.append_assoc] using lifted

/-- A final LETTER can be duplicated in every word of length at least three. -/
theorem appendLast (word : Word Nat) (long : 3 ≤ word.toList.length) :
    Derives basis word (word ++ Word.singleton word.reverse.head) := by
  rcases word with ⟨a, tail⟩
  cases tail with
  | nil => simp only [Word.toList, List.length_cons, List.length_nil] at long; omega
  | cons b rest =>
      cases rest with
      | nil => simp only [Word.toList, List.length_cons, List.length_nil] at long; omega
      | cons c remaining => exact appendLastLong remaining a b c

#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.raw00
#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.raw01
#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.raw02
#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.raw03
#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.raw04
#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.raw05
#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.raw06
#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.raw07
#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.interiorSwap
#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.duplicateFinalBlock
#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.lowerAxiomsAfterLast
#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.lowerDerivationAfterLast
#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.appendLast

end SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776
