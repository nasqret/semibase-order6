import SemigroupBasis.CoRoots.S5_83Family
import SemigroupBasis.Generated.S2_4
import SemigroupBasis.Subdirect

namespace SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_83Opposite

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xxy : Word Nat := w 0 [0, 1]
def xxyy : Word Nat := w 0 [0, 1, 1]
def xyx : Word Nat := w 0 [1, 0]
def xxyz : Word Nat := w 0 [0, 1, 2]
def xxzy : Word Nat := w 0 [0, 2, 1]
def xyyz : Word Nat := w 0 [1, 1, 2]
def xzyz : Word Nat := w 0 [2, 1, 2]
def xyz : Word Nat := w 0 [1, 2]
def xyzz : Word Nat := w 0 [1, 2, 2]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def doubledFinalLaw : Identity Nat := ⟨xxy, xxyy⟩
def returnLaw : Identity Nat := ⟨xxy, xyx⟩
def doubledPrefixSwapLaw : Identity Nat := ⟨xxyz, xxzy⟩
def contextualCopyLaw : Identity Nat := ⟨xyyz, xzyz⟩
def longFinalInsertionLaw : Identity Nat := ⟨xyz, xyzz⟩

/-- The exact six-law basis authenticated by canonical packet hash
`33829fb6383259df1407d689c655ef9c3e268b07e7a94d8cd26e1a40f8c11a29`.
It is shared by the eight `S2_4` with `S5_83^op` or `S5_84^op`
factor-pair packets: `S6_3810`, `S6_3816`, `S6_3823`, `S6_3829`,
`S6_6433`, `S6_6438`, `S6_6440`, and `S6_6445`. -/
def basis : List (Identity Nat) :=
  [powerLaw, doubledFinalLaw, returnLaw, doubledPrefixSwapLaw,
    contextualCopyLaw, longFinalInsertionLaw]

def yxx : Word Nat := w 1 [0, 0]
def yyxx : Word Nat := w 1 [1, 0, 0]
def zyxx : Word Nat := w 2 [1, 0, 0]
def yzxx : Word Nat := w 1 [2, 0, 0]
def zyyx : Word Nat := w 2 [1, 1, 0]
def zyzx : Word Nat := w 2 [1, 2, 0]
def zyx : Word Nat := w 2 [1, 0]
def zzyx : Word Nat := w 2 [2, 1, 0]

def dualPowerLaw : Identity Nat := ⟨xx, xxx⟩
def dualDoubledFinalLaw : Identity Nat := ⟨yxx, yyxx⟩
def dualReturnLaw : Identity Nat := ⟨yxx, xyx⟩
def dualDoubledPrefixSwapLaw : Identity Nat := ⟨zyxx, yzxx⟩
def dualContextualCopyLaw : Identity Nat := ⟨zyyx, zyzx⟩
def dualLongFinalInsertionLaw : Identity Nat := ⟨zyx, zzyx⟩

/-- Literal reversed presentation. Every law preserves the final variable,
as required by the right-zero factor. -/
def dualBasis : List (Identity Nat) :=
  [dualPowerLaw, dualDoubledFinalLaw, dualReturnLaw,
    dualDoubledPrefixSwapLaw, dualContextualCopyLaw,
    dualLongFinalInsertionLaw]

theorem dualBasis_eq_reversedBasis :
    dualBasis = reversedBasis basis := by
  decide

theorem reversedDualBasis_eq_basis :
    reversedBasis dualBasis = basis := by
  rw [dualBasis_eq_reversedBasis, reversedBasis_reversedBasis]

private def instantiateThreeWords
    (x y z : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

theorem derivesDualPowerExpansion (u : Word Nat) :
    Derives dualBasis (u ++ u) ((u ++ u) ++ u) := by
  have base : Derives dualBasis xx xxx :=
    Derives.fromBasis (e := dualPowerLaw) (by simp [dualBasis])
  have substituted :=
    Derives.subst base (instantiateThreeWords u u u)
  simpa [dualPowerLaw, xx, xxx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

theorem derivesDualPowerContraction (u : Word Nat) :
    Derives dualBasis ((u ++ u) ++ u) (u ++ u) :=
  (derivesDualPowerExpansion u).symm

/-- Insert a second copy of the first block while retaining a nonempty
two-block suffix. -/
theorem derivesDualLongInsertion (u v z : Word Nat) :
    Derives dualBasis ((u ++ v) ++ z) (((u ++ u) ++ v) ++ z) := by
  have base : Derives dualBasis zyx zzyx :=
    Derives.fromBasis (e := dualLongFinalInsertionLaw) (by
      simp [dualBasis])
  have substituted :=
    Derives.subst base (instantiateThreeWords z v u)
  simpa [dualLongFinalInsertionLaw, zyx, zzyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesDualLongContraction (u v z : Word Nat) :
    Derives dualBasis (((u ++ u) ++ v) ++ z) ((u ++ v) ++ z) :=
  (derivesDualLongInsertion u v z).symm

/-- The final-preserving rotation `uvu = vuu`. -/
theorem derivesDualRotate (u v : Word Nat) :
    Derives dualBasis ((u ++ v) ++ u) ((v ++ u) ++ u) := by
  have base : Derives dualBasis yxx xyx :=
    Derives.fromBasis (e := dualReturnLaw) (by simp [dualBasis])
  have substituted :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [dualReturnLaw, yxx, xyx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted.symm

/-- The head-changing `uvu = uvv` move from the `S5_83` theory is valid in
the intersection only when a nonempty suffix retains the literal final
variable. -/
theorem derivesDualCopyWithSuffix (u v suffix : Word Nat) :
    Derives dualBasis (((u ++ v) ++ u) ++ suffix)
      (((u ++ v) ++ v) ++ suffix) := by
  have base : Derives dualBasis zyyx zyzx :=
    Derives.fromBasis (e := dualContextualCopyLaw) (by
      simp [dualBasis])
  have substituted :=
    Derives.subst base (instantiateThreeWords suffix v u)
  simpa [dualContextualCopyLaw, zyyx, zyzx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted.symm

theorem derivesDualTransferWithSuffix (u v suffix : Word Nat) :
    Derives dualBasis (((u ++ v) ++ v) ++ suffix)
      (((v ++ u) ++ u) ++ suffix) :=
  (derivesDualCopyWithSuffix u v suffix).symm.trans <| by
    simpa [Word.append_assoc] using
      Derives.appendRight (derivesDualRotate u v) suffix

/-- Adjacent nonempty prefix blocks may be swapped whenever two nonempty
suffix blocks remain. This is the unrestricted replacement for the packet's
bounded right-extension transition. -/
theorem derivesDualPrefixSwap (u v q r : Word Nat) :
    Derives dualBasis (((u ++ v) ++ q) ++ r)
      (((v ++ u) ++ q) ++ r) := by
  have duplicate :=
    Derives.prepend u (derivesDualLongInsertion v q r)
  have copyBack :=
    (derivesDualCopyWithSuffix u v (q ++ r)).symm
  have rotate :=
    Derives.appendRight (derivesDualRotate u v) (q ++ r)
  have contract :=
    Derives.prepend v (derivesDualLongContraction u q r)
  exact Derives.trans
    (by simpa [Word.append_assoc] using duplicate) <|
    Derives.trans
      (by simpa [Word.append_assoc] using copyBack) <|
    Derives.trans
      (by simpa [Word.append_assoc] using rotate)
      (by simpa [Word.append_assoc] using contract)

private theorem s5DerivesDualPower :
    Derives SemigroupBasis.CoRoots.S5_83.basis xx xxx := by
  simpa [xx, xxx, w] using
    SemigroupBasis.CoRoots.S5_83.derivesPowerExpansion
      (Word.singleton 0)

private theorem s5DerivesDualDoubledFinal :
    Derives SemigroupBasis.CoRoots.S5_83.basis yxx yyxx := by
  simpa [yxx, yyxx, w, Word.singleton, Word.append,
    Word.append_assoc] using
      SemigroupBasis.CoRoots.S5_83.derivesLongInsertion
        (Word.singleton 1) (Word.singleton 0) (Word.singleton 0)

private theorem s5DerivesDualReturn :
    Derives SemigroupBasis.CoRoots.S5_83.basis yxx xyx := by
  simpa [yxx, xyx, w, Word.singleton, Word.append,
    Word.append_assoc] using
      (SemigroupBasis.CoRoots.S5_83.derivesRotate
        (Word.singleton 0) (Word.singleton 1)).symm

private theorem s5DerivesDualDoubledPrefixSwap :
    Derives SemigroupBasis.CoRoots.S5_83.basis zyxx yzxx := by
  simpa [zyxx, yzxx, w, Word.singleton, Word.append,
    Word.append_assoc] using
      SemigroupBasis.CoRoots.S5_83.derivesPrefixSwap
        (Word.singleton 2) (Word.singleton 1)
        (Word.singleton 0) (Word.singleton 0)

private theorem s5DerivesDualContextualCopy :
    Derives SemigroupBasis.CoRoots.S5_83.basis zyyx zyzx := by
  have copied :=
    Derives.appendRight
      (SemigroupBasis.CoRoots.S5_83.derivesCopy
        (Word.singleton 2) (Word.singleton 1)).symm
      (Word.singleton 0)
  simpa [zyyx, zyzx, w, Word.singleton, Word.append,
    Word.append_assoc] using copied

private theorem s5DerivesDualLongFinalInsertion :
    Derives SemigroupBasis.CoRoots.S5_83.basis zyx zzyx := by
  simpa [zyx, zzyx, w, Word.singleton, Word.append,
    Word.append_assoc] using
      SemigroupBasis.CoRoots.S5_83.derivesLongInsertion
        (Word.singleton 2) (Word.singleton 1) (Word.singleton 0)

theorem s5_83BasisDerivesDualAxiom
    (identity : Identity Nat) (member : identity ∈ dualBasis) :
    Derives SemigroupBasis.CoRoots.S5_83.basis
      identity.lhs identity.rhs := by
  simp only [dualBasis, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact s5DerivesDualPower
  · exact s5DerivesDualDoubledFinal
  · exact s5DerivesDualReturn
  · exact s5DerivesDualDoubledPrefixSwap
  · exact s5DerivesDualContextualCopy
  · exact s5DerivesDualLongFinalInsertion

theorem modelsS5_83 :
    Models SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup
      dualBasis := by
  intro identity member valuation
  exact (s5_83BasisDerivesDualAxiom identity member).sound
    SemigroupBasis.CoRoots.S5_83Family.S5_83.models valuation

theorem modelsS5_84 :
    Models SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup
      dualBasis := by
  intro identity member valuation
  exact (s5_83BasisDerivesDualAxiom identity member).sound
    SemigroupBasis.CoRoots.S5_83Family.S5_84.models valuation

theorem modelsRightZero :
    Models SemigroupBasis.Generated.S2_4.table.semigroup.opposite
      dualBasis := by
  intro identity member
  simp only [dualBasis, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    intro valuation <;> rfl

end SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_83Opposite
