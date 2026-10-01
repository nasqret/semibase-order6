import SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrierPrelude
import SemigroupBasis.Opposite

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroup

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xyzx : Word Nat := w 0 [1, 2, 0]
def xyxxzx : Word Nat := w 0 [1, 0, 0, 2, 0]

def regularLaw : Identity Nat :=
  ⟨xyzx, xyxxzx⟩

/-- The regular-orthogroup candidate for `S6_14897`. -/
def basis : List (Identity Nat) :=
  [SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.powerLaw, regularLaw]

def finiteRegularLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 0, 2, 0]⟩⟩

theorem finiteRegularLaw_map :
    finiteRegularLaw.map Fin.val = regularLaw := rfl

theorem basis_models :
    Models
      SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.table.semigroup
      basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · rw [←
      SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.finitePowerLaw_map]
    exact
      (SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.table).checkIdentityNat_sound
        SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.finitePowerLaw
        (by decide)
  · rw [← finiteRegularLaw_map]
    exact
      (SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.table).checkIdentityNat_sound
        finiteRegularLaw (by decide)

private theorem powerLaw_mem :
    SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.powerLaw ∈ basis := by
  simp [basis]

private theorem regularLaw_mem :
    regularLaw ∈ basis := by
  simp [basis]

private def instantiateThreeWords
    (u v z : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis u ((u ++ u) ++ u) := by
  have base :
      Derives basis
        SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.powerLaw.lhs
        SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.powerLaw.rhs :=
    Derives.fromBasis powerLaw_mem
  have instantiated := Derives.subst base (fun _ => u)
  simpa [
    SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.powerLaw,
    SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.x,
    SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.xxx, Word.bind,
    Word.append] using instantiated

theorem derivesPowerContraction (u : Word Nat) :
    Derives basis ((u ++ u) ++ u) u :=
  (derivesPowerExpansion u).symm

theorem derivesRegularExpansion
    (u v z : Word Nat) :
    Derives basis
      (((u ++ v) ++ z) ++ u)
      (((((u ++ v) ++ u) ++ u) ++ z) ++ u) := by
  have base :
      Derives basis regularLaw.lhs regularLaw.rhs :=
    Derives.fromBasis regularLaw_mem
  have instantiated :=
    Derives.subst base (instantiateThreeWords u v z)
  simpa [regularLaw, xyzx, xyxxzx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      instantiated

private def swapSecondThird : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 2
  | 2 => Word.singleton 1
  | n + 3 => Word.singleton (n + 3)

theorem powerLaw_reversed :
    SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.powerLaw.reversed =
      SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.powerLaw := by
  decide

/-- Reversal of the regular law is its `y,z` renaming, so the basis is
closed under word reversal up to derivability. -/
theorem derivesReversedRegularLaw :
    Derives basis regularLaw.reversed.lhs regularLaw.reversed.rhs := by
  have base :
      Derives basis regularLaw.lhs regularLaw.rhs :=
    Derives.fromBasis regularLaw_mem
  have renamed := Derives.subst base swapSecondThird
  have leftEq :
      regularLaw.reversed.lhs =
        regularLaw.lhs.bind swapSecondThird := by
    decide
  have rightEq :
      regularLaw.reversed.rhs =
        regularLaw.rhs.bind swapSecondThird := by
    decide
  simpa only [leftEq, rightEq] using renamed

theorem reversedAxiomDerives
    (identity : Identity Nat)
    (member : identity ∈ reversedBasis basis) :
    Derives basis identity.lhs identity.rhs := by
  obtain ⟨source, sourceMember, rfl⟩ :=
    List.mem_map.mp member
  simp only [basis, List.mem_cons, List.not_mem_nil,
    or_false] at sourceMember
  rcases sourceMember with rfl | rfl
  · rw [powerLaw_reversed]
    exact Derives.fromBasis powerLaw_mem
  · exact derivesReversedRegularLaw

/-- Any derivation from the candidate basis may be reversed without changing
the basis. -/
theorem derivesReverse
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    Derives basis left.reverse right.reverse :=
  derivation.reverse.transport reversedAxiomDerives

theorem derivesRegularContraction
    (u v z : Word Nat) :
    Derives basis
      (((((u ++ v) ++ u) ++ u) ++ z) ++ u)
      (((u ++ v) ++ z) ++ u) :=
  (derivesRegularExpansion u v z).symm

/-- The mixed-orientation guarded affine middle-square kernel found by WMI
job 170568: `uvuvvu = uvvuvu`. -/
theorem derivesGuardedMiddleSquare
    (u v : Word Nat) :
    Derives basis
      (((((u ++ v) ++ u) ++ v) ++ v) ++ u)
      (((((u ++ v) ++ v) ++ u) ++ v) ++ u) := by
  have first :=
    Derives.prepend ((((u ++ v) ++ u) ++ v))
      (derivesPowerExpansion (v ++ u))
  have second :=
    Derives.appendRight
      (Derives.prepend u
        (derivesRegularContraction v u u))
      ((u ++ v) ++ u)
  have third :=
    Derives.appendRight
      (derivesRegularContraction u v v)
      (v ++ u)
  exact Derives.trans
    (by simpa [Word.append_assoc] using first) <|
      Derives.trans
        (by simpa [Word.append_assoc] using second)
        (by simpa [Word.append_assoc] using third)

/-- The same-orientation two-sided guarded swap kernel found by WMI job
170569: `uvuvuv = uvvuuv`. -/
theorem derivesGuardedSwapKernel
    (u v : Word Nat) :
    Derives basis
      (((((u ++ v) ++ u) ++ v) ++ u) ++ v)
      (((((u ++ v) ++ v) ++ u) ++ u) ++ v) := by
  have first :=
    Derives.appendRight
      (Derives.prepend ((((u ++ v) ++ u) ++ v))
        (derivesPowerExpansion u))
      v
  have second :=
    Derives.prepend (((u ++ v) ++ u))
      (derivesRegularExpansion v u (u ++ u))
  have third :=
    Derives.appendRight
      (derivesPowerContraction (u ++ v))
      (((v ++ u) ++ u) ++ v)
  exact Derives.trans
    (by simpa [Word.append_assoc] using first) <|
      Derives.trans
        (by simpa [Word.append_assoc] using second)
        (by simpa [Word.append_assoc] using third)

/-- The first nonadjacent left-guard kernel found by WMI job 170572:
`ugvuvuv = ugvvuuv`. The arbitrary word `gap` is retained unchanged. -/
theorem derivesLeftGapGuardedSwapKernel
    (u gap v : Word Nat) :
    Derives basis
      ((((((u ++ gap) ++ v) ++ u) ++ v) ++ u) ++ v)
      ((((((u ++ gap) ++ v) ++ v) ++ u) ++ u) ++ v) := by
  have first :=
    Derives.appendRight
      (Derives.prepend (((u ++ gap) ++ v))
        (derivesPowerExpansion u))
      ((v ++ u) ++ v)
  have second :=
    Derives.appendRight
      (Derives.prepend (u ++ gap)
        (derivesRegularExpansion v (u ++ u) u))
      (u ++ v)
  have third :=
    Derives.appendRight
      (Derives.prepend ((((u ++ gap) ++ v) ++ u))
        (derivesRegularExpansion u v v))
      ((v ++ u) ++ v)
  have fourth :=
    Derives.prepend ((((((u ++ gap) ++ v) ++ u) ++ u) ++ v) ++ u)
      (derivesPowerContraction (u ++ v))
  have fifth :=
    Derives.appendRight
      (derivesRegularContraction u (gap ++ v) v)
      (u ++ v)
  exact Derives.trans
    (by simpa [Word.append_assoc] using first) <|
      Derives.trans
        (by simpa [Word.append_assoc] using second) <|
          Derives.trans
            (by simpa [Word.append_assoc] using third) <|
              Derives.trans
                (by simpa [Word.append_assoc] using fourth)
                (by simpa [Word.append_assoc] using fifth)

end SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroup
