import SemigroupBasis.CoRoots.S5_855Normalization

namespace SemigroupBasis.CoRoots.S5_851

open SemigroupBasis

def xy : Word Nat := ⟨0, [1]⟩
def xyy : Word Nat := ⟨0, [1, 1]⟩
def xyz : Word Nat := ⟨0, [1, 2]⟩
def xzyz : Word Nat := ⟨0, [2, 1, 2]⟩
def xxyz : Word Nat := ⟨0, [0, 1, 2]⟩
def xyxz : Word Nat := ⟨0, [1, 0, 2]⟩

def rightDuplicationLaw : Identity Nat := ⟨xy, xyy⟩
def interiorExpansionLaw : Identity Nat := ⟨xyz, xzyz⟩
def initialMoveLaw : Identity Nat := ⟨xxyz, xyxz⟩

/-- The exact ordered basis recorded for `S5_851` and `S5_867`. -/
def basis : List (Identity Nat) :=
  [rightDuplicationLaw, interiorExpansionLaw, initialMoveLaw]

private def instantiateThree
    (u v q : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => q
  | n + 3 => Word.singleton (n + 3)

/-- Delete an adjacent repeated nonempty block after a nonempty prefix. -/
theorem derivesRightContraction (u v : Word Nat) :
    Derives basis ((u ++ v) ++ v) (u ++ v) := by
  have base :
      Derives basis xyy xy :=
    Derives.symm <|
      Derives.fromBasis (e := rightDuplicationLaw) <|
        List.Mem.head _
  have substituted :=
    Derives.subst base (instantiateThree u v v)
  simpa [basis, rightDuplicationLaw, xyy, xy, instantiateThree,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Gather a later copy of `u` next to the initial copy while retaining a
nonempty suffix. -/
theorem derivesReturnGather (u v q : Word Nat) :
    Derives basis
      (((u ++ v) ++ u) ++ q)
      (((u ++ u) ++ v) ++ q) := by
  have base :
      Derives basis xyxz xxyz :=
    Derives.symm <|
      Derives.fromBasis (e := initialMoveLaw) <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _
  have substituted :=
    Derives.subst base (instantiateThree u v q)
  simpa [basis, initialMoveLaw, xyxz, xxyz, instantiateThree,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Move the second initial block across a nonempty middle while retaining
the nonempty suffix. -/
theorem derivesInitialMove (u v q : Word Nat) :
    Derives basis
      (((u ++ u) ++ v) ++ q)
      (((u ++ v) ++ u) ++ q) := by
  have base :
      Derives basis xxyz xyxz :=
    Derives.fromBasis (e := initialMoveLaw) <|
      List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _
  have substituted :=
    Derives.subst base (instantiateThree u v q)
  simpa [basis, initialMoveLaw, xxyz, xyxz, instantiateThree,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- The derived power contraction `uuu -> uu`. -/
theorem derivesPowerContraction (u : Word Nat) :
    Derives basis ((u ++ u) ++ u) (u ++ u) :=
  derivesRightContraction u u

/-- Instantiate the third basis law as `uvq -> uqvq`. -/
theorem derivesInteriorExpansion (u v q : Word Nat) :
    Derives basis
      ((u ++ v) ++ q)
      (((u ++ q) ++ v) ++ q) := by
  have base :
      Derives basis xyz xzyz :=
    Derives.fromBasis (e := interiorExpansionLaw) <|
      List.Mem.tail _ <| List.Mem.head _
  have substituted :=
    Derives.subst base (instantiateThree u v q)
  simpa [basis, interiorExpansionLaw, xyz, xzyz, instantiateThree,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- The authoritative derived law `uvqr = uqvr`: duplicate `v`, move the
second copy past `q`, then use `xyz = xzyz` in reverse. -/
theorem derivesInteriorSwap (u v q r : Word Nat) :
    Derives basis
      (((u ++ v) ++ q) ++ r)
      (((u ++ q) ++ v) ++ r) := by
  have duplicate :
      Derives basis
        (((u ++ v) ++ q) ++ r)
        ((((u ++ v) ++ v) ++ q) ++ r) := by
    have core :=
      Derives.symm (derivesRightContraction u v)
    have extended :=
      Derives.appendRight core (q ++ r)
    simpa [Word.append_assoc] using extended
  have move :
      Derives basis
        ((((u ++ v) ++ v) ++ q) ++ r)
        ((((u ++ v) ++ q) ++ v) ++ r) := by
    have core :=
      Derives.prepend u (derivesInitialMove v q r)
    simpa [Word.append_assoc] using core
  have contract :
      Derives basis
        ((((u ++ v) ++ q) ++ v) ++ r)
        (((u ++ q) ++ v) ++ r) := by
    have core :=
      Derives.symm (derivesInteriorExpansion u q v)
    have extended :=
      Derives.appendRight core r
    simpa [Word.append_assoc] using extended
  exact duplicate.trans <| move.trans contract

private theorem s5_855AxiomDerives
    (identity : Identity Nat)
    (member : identity ∈ S5_855.basis) :
    Derives basis identity.lhs identity.rhs := by
  simp only [S5_855.basis, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl
  · simpa [S5_855.rightDuplicationLaw, S5_855.xy, S5_855.xyy,
      rightDuplicationLaw, xy, xyy] using
      (Derives.fromBasis (basis := basis)
        (e := rightDuplicationLaw) (List.Mem.head _))
  · simpa [S5_855.initialMoveLaw, S5_855.xxyz, S5_855.xyxz,
      initialMoveLaw, xxyz, xyxz] using
      (Derives.fromBasis (basis := basis)
        (e := initialMoveLaw)
        (List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _))

/-- Every derivation in the two-law `S5_855` normalizer transports to the
exact three-law basis. -/
theorem liftS5_855Derivation
    {left right : Word Nat}
    (derivation : Derives S5_855.basis left right) :
    Derives basis left right :=
  derivation.transport s5_855AxiomDerives

/-- The established first-occurrence-order normalizer remains available
unchanged under the larger exact basis. -/
theorem derivesOfInitialFinalSignature
    {left right : Word Nat}
    (same : S5_855.SameInitialFinalSignature left right) :
    Derives basis left right :=
  liftS5_855Derivation (S5_855.derivesOfSignature same)

/-- The exact four-coordinate invariant recorded by the authoritative
head/support/final certificate. -/
structure SameHeadSupportFinalSignature
    (left right : Word Nat) : Prop where
  head : left.head = right.head
  support :
    ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList
  final : left.final = right.final
  repeatedInitial :
    S5_855.repeatedInitial left =
      S5_855.repeatedInitial right

namespace SameHeadSupportFinalSignature

theorem refl (word : Word Nat) :
    SameHeadSupportFinalSignature word word :=
  ⟨rfl, fun _ => Iff.rfl, rfl, rfl⟩

theorem symm {left right : Word Nat}
    (same : SameHeadSupportFinalSignature left right) :
    SameHeadSupportFinalSignature right left :=
  ⟨same.head.symm, fun letter => (same.support letter).symm,
    same.final.symm, same.repeatedInitial.symm⟩

theorem trans {left middle right : Word Nat}
    (first : SameHeadSupportFinalSignature left middle)
    (second : SameHeadSupportFinalSignature middle right) :
    SameHeadSupportFinalSignature left right :=
  ⟨first.head.trans second.head,
    fun letter => (first.support letter).trans (second.support letter),
    first.final.trans second.final,
    first.repeatedInitial.trans second.repeatedInitial⟩

end SameHeadSupportFinalSignature

/-- The one unrestricted derivational theorem not supplied by the existing
`S5_855` normalizer: equal head, support, final letter, and head uniqueness
must suffice for an explicit derivation in the exact three laws. -/
def HeadSupportFinalDerivationalCompleteness : Prop :=
  ∀ left right : Word Nat,
    SameHeadSupportFinalSignature left right →
      Derives basis left right

end SemigroupBasis.CoRoots.S5_851
