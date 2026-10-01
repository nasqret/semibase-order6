import SemigroupBasis.Opposite
import SemigroupBasis.Examples.CommutativePositiveModFourFive

/-! Exact B3 presentation. Commutativity is transported only behind a
nonempty prefix; no global commutativity or unit premise is introduced. -/

namespace SemigroupBasis.CoRoots.Order6Day14.S9498

open SemigroupBasis

def law00 : Identity Nat := ⟨Word.mk 0 [], Word.mk 0 [0, 0, 0, 0]⟩
def law01 : Identity Nat := ⟨Word.mk 0 [0, 1], Word.mk 0 [1, 0]⟩
def law02 : Identity Nat := ⟨Word.mk 0 [1, 2], Word.mk 0 [2, 1]⟩
def basis : List (Identity Nat) := [law00, law01, law02]
abbrev dualBasis : List (Identity Nat) := reversedBasis basis
abbrev displayedBasisSHA256 : String :=
  "84a23fbfd777e7e94a09b5fe484c1a2f22e4564c15a76c291d7bda204b5dd474"

theorem basis_length : basis.length = 3 := by decide

theorem displayedBasis_exact :
    basis.map (fun e => (e.lhs.toList, e.rhs.toList)) =
      [([0], [0, 0, 0, 0, 0]), ([0, 0, 1], [0, 1, 0]),
       ([0, 1, 2], [0, 2, 1])] := by decide

theorem rawLaw00 (u : Word Nat) :
    Derives basis u ((((u ++ u) ++ u) ++ u) ++ u) := by
  have primitive : Derives basis law00.lhs law00.rhs :=
    Derives.fromBasis (e := law00) (by decide)
  have mapped := primitive.subst (fun _ => u)
  simpa [law00, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw01 (u v : Word Nat) :
    Derives basis ((u ++ u) ++ v) ((u ++ v) ++ u) := by
  have primitive : Derives basis law01.lhs law01.rhs :=
    Derives.fromBasis (e := law01) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law01, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw02 (pre u v : Word Nat) :
    Derives basis ((pre ++ u) ++ v) ((pre ++ v) ++ u) := by
  have primitive : Derives basis law02.lhs law02.rhs :=
    Derives.fromBasis (e := law02) (by decide)
  have mapped := primitive.subst (fun | 0 => pre | 1 => u | 2 => v | _ => Word.singleton 0)
  simpa [law02, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem bind_append (u v : Word Nat) (σ : Nat → Word Nat) :
    (u ++ v).bind σ = u.bind σ ++ v.bind σ := by
  apply Word.toList_injective
  simp [Word.toList_bind, Word.toList_append, List.flatMap_append]

theorem bind_bind (w : Word Nat) (σ τ : Nat → Word Nat) :
    (w.bind σ).bind τ = w.bind (fun z => (σ z).bind τ) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

theorem bind_singleton (w : Word Nat) : w.bind Word.singleton = w := by
  apply Word.toList_injective
  simp [Word.toList_bind, Word.toList_singleton]

theorem transportUnderPrefixSubst {u v : Word Nat}
    (derivation : Derives Examples.commutativePositiveModFourBasis u v) :
    ∀ (σ : Nat → Word Nat) (pre : Word Nat),
      Derives basis (pre ++ u.bind σ) (pre ++ v.bind σ) := by
  induction derivation with
  | @fromBasis e member =>
      intro σ pre
      change e ∈ [Examples.positiveModFourPowerLaw,
        Examples.positiveModFourCommutativityLaw] at member
      rcases List.mem_cons.mp member with equal | member
      · subst e
        have powered := (rawLaw00 (σ 0)).prepend pre
        simpa [Examples.positiveModFourPowerLaw, Examples.positiveModFourX,
          Examples.positiveModFourXXXXX, Word.bind, Word.singleton,
          Word.append_assoc] using powered
      · have equal := List.mem_singleton.mp member
        subst e
        have swapped := rawLaw02 pre (σ 0) (σ 1)
        simpa [Examples.positiveModFourCommutativityLaw, Examples.positiveModFourXY,
          Examples.positiveModFourYX, Word.bind, Word.append_assoc] using swapped
  | refl w =>
      intro σ pre
      exact Derives.refl (pre ++ w.bind σ)
  | symm _ ih =>
      intro σ pre
      exact (ih σ pre).symm
  | trans _ _ first second =>
      intro σ pre
      exact (first σ pre).trans (second σ pre)
  | prepend q _ ih =>
      intro σ pre
      have enlarged := ih σ (pre ++ q.bind σ)
      simpa only [bind_append, Word.append_assoc] using enlarged
  | appendRight _ q ih =>
      intro σ pre
      have extended := (ih σ pre).appendRight (q.bind σ)
      simpa only [bind_append, Word.append_assoc] using extended
  | subst _ τ ih =>
      intro σ pre
      have composed := ih (fun z => (τ z).bind σ) pre
      simpa only [bind_bind] using composed

theorem transportUnderPrefix {u v : Word Nat}
    (derivation : Derives Examples.commutativePositiveModFourBasis u v)
    (pre : Word Nat) : Derives basis (pre ++ u) (pre ++ v) := by
  have transported := transportUnderPrefixSubst derivation Word.singleton pre
  simpa only [bind_singleton] using transported

end SemigroupBasis.CoRoots.Order6Day14.S9498
