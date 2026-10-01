import SemigroupBasis.CoRoots.Order6Sunday.TwinTwoLawFinite
import SemigroupBasis.Examples.ParityInitialFour

namespace SemigroupBasis.CoRoots.Order6Day14.TwinsA

open SemigroupBasis

abbrev basis := Order6Sunday.TwinTwoLawFinite.A.basis

theorem basis_length : basis.length = 2 := by decide

theorem displayedBasis_exact :
    basis = [⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩,
      ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩] := rfl

def rightLaw0 : Identity Nat := ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩
def rightLaw1 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem rightBasis_exact :
    Examples.parityInitialOppositeBasis = [rightLaw0, rightLaw1] := by decide

theorem rawLaw0 (u : Word Nat) :
    Derives basis u (u ++ (u ++ u)) := by
  have primitive : Derives basis
      Order6Sunday.TwinTwoLawFinite.A.basisLaw0.lhs
      Order6Sunday.TwinTwoLawFinite.A.basisLaw0.rhs :=
    Derives.fromBasis (e := Order6Sunday.TwinTwoLawFinite.A.basisLaw0) (by decide)
  have mapped := primitive.subst (fun _ => u)
  simpa only [Order6Sunday.TwinTwoLawFinite.A.basisLaw0, Word.bind,
    List.foldl_cons, List.foldl_nil, Word.append_assoc] using mapped

theorem rawLaw1 (pre u v : Word Nat) :
    Derives basis (pre ++ (u ++ (v ++ u)))
      (pre ++ (v ++ (u ++ u))) := by
  have primitive : Derives basis
      Order6Sunday.TwinTwoLawFinite.A.basisLaw1.lhs
      Order6Sunday.TwinTwoLawFinite.A.basisLaw1.rhs :=
    Derives.fromBasis (e := Order6Sunday.TwinTwoLawFinite.A.basisLaw1) (by decide)
  have mapped := primitive.subst
    (fun | 0 => pre | 1 => u | 2 => v | _ => Word.singleton 0)
  simpa only [Order6Sunday.TwinTwoLawFinite.A.basisLaw1, Word.bind,
    List.foldl_cons, List.foldl_nil, Word.append_assoc] using mapped

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

/-- Right-factor derivations lift only under a nonempty prefix. -/
theorem transportUnderPrefixSubst {u v : Word Nat}
    (derivation : Derives Examples.parityInitialOppositeBasis u v) :
    ∀ (σ : Nat → Word Nat) (pre : Word Nat),
      Derives basis (pre ++ u.bind σ) (pre ++ v.bind σ) := by
  induction derivation with
  | @fromBasis e member =>
      intro σ pre
      rw [rightBasis_exact] at member
      rcases List.mem_cons.mp member with equal | member
      · subst e
        have powered := (rawLaw0 (σ 0)).prepend pre
        simpa only [rightLaw0, Word.bind, List.foldl_cons,
          List.foldl_nil, Word.append_assoc] using powered
      · have equal := List.mem_singleton.mp member
        subst e
        have gathered := rawLaw1 pre (σ 0) (σ 1)
        simpa only [rightLaw1, Word.bind, List.foldl_cons,
          List.foldl_nil, Word.append_assoc] using gathered
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
    (derivation : Derives Examples.parityInitialOppositeBasis u v)
    (pre : Word Nat) : Derives basis (pre ++ u) (pre ++ v) := by
  have transported := transportUnderPrefixSubst derivation Word.singleton pre
  simpa only [bind_singleton] using transported

end SemigroupBasis.CoRoots.Order6Day14.TwinsA
