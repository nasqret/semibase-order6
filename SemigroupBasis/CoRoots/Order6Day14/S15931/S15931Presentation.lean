import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Opposite
import SemigroupBasis.Examples.HeadSortedPeriodThreeFromTwo

/-! The exact ordered S6_15931 B4. Primitive instances substitute only
nonempty words. Optional list suffixes are handled separately. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day14.S15931

open SemigroupBasis

def law00 : Identity Nat := ⟨Word.mk 0 [0], Word.mk 0 [0, 0, 0, 0]⟩
def law01 : Identity Nat := ⟨Word.mk 0 [1], Word.mk 0 [1, 1, 1, 1]⟩
def law02 : Identity Nat := ⟨Word.mk 0 [0, 1], Word.mk 0 [1, 0]⟩
def law03 : Identity Nat := ⟨Word.mk 0 [1, 2], Word.mk 0 [2, 1]⟩

def basis : List (Identity Nat) := [law00, law01, law02, law03]
abbrev dualBasis : List (Identity Nat) := reversedBasis basis
abbrev displayedBasisSHA256 : String :=
  "2a923a798463d727d519ccf784f4e13b31b7dbe1fc2e4c33d118830b34a5cdf8"

theorem basis_length : basis.length = 4 := by decide

theorem displayedBasis_exact :
    basis.map (fun identity => (identity.lhs.toList, identity.rhs.toList)) =
      [([0, 0], [0, 0, 0, 0, 0]), ([0, 1], [0, 1, 1, 1, 1]),
       ([0, 0, 1], [0, 1, 0]), ([0, 1, 2], [0, 2, 1])] := by decide

theorem rawLaw00 (u : Word Nat) :
    Derives basis (u ++ u) ((((u ++ u) ++ u) ++ u) ++ u) := by
  have primitive : Derives basis law00.lhs law00.rhs :=
    Derives.fromBasis (e := law00) (by decide)
  have mapped := primitive.subst (fun _ => u)
  simpa [law00, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw01 (u v : Word Nat) :
    Derives basis (u ++ v) ((((u ++ v) ++ v) ++ v) ++ v) := by
  have primitive : Derives basis law01.lhs law01.rhs :=
    Derives.fromBasis (e := law01) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law01, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw02 (u v : Word Nat) :
    Derives basis ((u ++ u) ++ v) ((u ++ v) ++ u) := by
  have primitive : Derives basis law02.lhs law02.rhs :=
    Derives.fromBasis (e := law02) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law02, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw03 (u v w : Word Nat) :
    Derives basis ((u ++ v) ++ w) ((u ++ w) ++ v) := by
  have primitive : Derives basis law03.lhs law03.rhs :=
    Derives.fromBasis (e := law03) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law03, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem normalizerBasis_exact :
    Examples.headSortedPeriodThreeFromTwoBasis = [law00, law02, law03] := by decide

theorem normalizerLawDerives (identity : Identity Nat)
    (member : identity ∈ Examples.headSortedPeriodThreeFromTwoBasis) :
    Derives basis identity.lhs identity.rhs := by
  rw [normalizerBasis_exact] at member
  rcases List.mem_cons.mp member with rfl | member
  · exact Derives.fromBasis (e := law00) (by decide)
  · rcases List.mem_cons.mp member with rfl | member
    · exact Derives.fromBasis (e := law02) (by decide)
    · have equal : identity = law03 := List.mem_singleton.mp member
      subst identity
      exact Derives.fromBasis (e := law03) (by decide)

theorem transportNormalizer {u v : Word Nat}
    (derivation : Derives Examples.headSortedPeriodThreeFromTwoBasis u v) :
    Derives basis u v :=
  derivation.transport normalizerLawDerives

def appendTail (pre : Word Nat) (tail : List Nat) : Word Nat :=
  ⟨pre.head, pre.tail ++ tail⟩

theorem appendTail_nil (pre : Word Nat) : appendTail pre [] = pre := by
  cases pre
  simp [appendTail]

theorem appendTail_cons_word (pre : Word Nat) (letter : Nat) (tail : List Nat) :
    appendTail pre (letter :: tail) = pre ++ Word.mk letter tail := rfl

theorem appendTail_cons_prefix (pre : Word Nat) (letter : Nat) (tail : List Nat) :
    appendTail pre (letter :: tail) = appendTail (pre ++ Word.singleton letter) tail := by
  apply Word.toList_injective
  simp [appendTail, Word.toList, Word.singleton, List.append_assoc]

theorem appendTail_append (pre : Word Nat) (first second : List Nat) :
    appendTail pre (first ++ second) = appendTail (appendTail pre first) second := by
  apply Word.toList_injective
  simp [appendTail, Word.toList, List.append_assoc]

theorem derivesAppendTail {u v : Word Nat} (derivation : Derives basis u v)
    (tail : List Nat) : Derives basis (appendTail u tail) (appendTail v tail) := by
  cases tail with
  | nil => simpa only [appendTail_nil] using derivation
  | cons letter rest =>
      simpa only [appendTail_cons_word] using derivation.appendRight (Word.mk letter rest)

end SemigroupBasis.CoRoots.Order6Day14.S15931
