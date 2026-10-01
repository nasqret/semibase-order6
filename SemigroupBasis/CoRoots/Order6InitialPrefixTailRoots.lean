import SemigroupBasis.CoRoots.Order6BlockTraceRootEndpoints
import SemigroupBasis.Generated.Order6InitialPrefixTailTargets
import SemigroupBasis.Opposite

/-!
Reusable unrestricted derivations for the initial-prefix/tail basis, followed
by an explicitly conditional block-trace endpoint for the nine exact roots.

The missing object is a `TraceCertificate` for the shared normal form.  Finite
model checks below do not discharge that unrestricted completeness premise.
-/

namespace SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots

open SemigroupBasis

universe u

namespace Target

abbrev basis :=
  SemigroupBasis.Generated.Order6InitialPrefixTailTargets.basis

end Target

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xxy : Word Nat := w 0 [0, 1]
def xyx : Word Nat := w 0 [1, 0]
def yyxx : Word Nat := w 1 [1, 0, 0]
def xyyx : Word Nat := w 0 [1, 1, 0]
def uzyx : Word Nat := w 3 [2, 1, 0]
def uzxy : Word Nat := w 3 [2, 0, 1]
def xzyx : Word Nat := w 0 [2, 1, 0]
def xyzx : Word Nat := w 0 [1, 2, 0]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def squareRotationLaw : Identity Nat := ⟨yyxx, xyyx⟩
def gatherLaw : Identity Nat := ⟨xyx, xxy⟩
def tailSwapLaw : Identity Nat := ⟨uzyx, uzxy⟩
def anchoredTailLaw : Identity Nat := ⟨xzyx, xyzx⟩

/-- Literal reverse-word presentation used by the unrestricted proof lane. -/
def basis : List (Identity Nat) :=
  [powerLaw, squareRotationLaw, gatherLaw, tailSwapLaw,
    anchoredTailLaw]

theorem basis_eq_reversedTarget :
    basis = reversedBasis Target.basis := by
  decide

private def instantiateFourWords
    (a b c d : Word Nat) : Nat → Word Nat
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d
  | n + 4 => Word.singleton (n + 4)

theorem derivesPowerLaw : Derives basis xx xxx :=
  Derives.fromBasis (e := powerLaw) (by simp [basis])

theorem derivesSquareRotationLaw :
    Derives basis yyxx xyyx :=
  Derives.fromBasis (e := squareRotationLaw) (by simp [basis])

theorem derivesGatherLaw : Derives basis xyx xxy :=
  Derives.fromBasis (e := gatherLaw) (by simp [basis])

theorem derivesTailSwapLaw : Derives basis uzyx uzxy :=
  Derives.fromBasis (e := tailSwapLaw) (by simp [basis])

theorem derivesAnchoredTailLaw : Derives basis xzyx xyzx :=
  Derives.fromBasis (e := anchoredTailLaw) (by simp [basis])

/-- Contract three adjacent copies of any nonempty block to two. -/
theorem derivesThreeToTwo (block : Word Nat) :
    Derives basis ((block ++ block) ++ block) (block ++ block) := by
  have substituted :=
    Derives.subst derivesPowerLaw.symm
      (instantiateFourWords block block block block)
  simpa [powerLaw, xx, xxx, w, instantiateFourWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Gather a later occurrence next to the first copy of a block. -/
theorem derivesGather (block middle : Word Nat) :
    Derives basis ((block ++ middle) ++ block)
      ((block ++ block) ++ middle) := by
  have substituted :=
    Derives.subst derivesGatherLaw
      (instantiateFourWords block middle middle middle)
  simpa [gatherLaw, xyx, xxy, w, instantiateFourWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Adjacent square blocks commute. -/
theorem derivesSquareCommutation (left right : Word Nat) :
    Derives basis
      ((left ++ left) ++ (right ++ right))
      ((right ++ right) ++ (left ++ left)) := by
  have rotated :=
    Derives.subst derivesSquareRotationLaw
      (instantiateFourWords right left left left)
  have gathered := derivesGather right (left ++ left)
  exact Derives.trans
    (by
      simpa [squareRotationLaw, yyxx, xyyx, w,
        instantiateFourWords, Word.bind, Word.append,
        Word.singleton, Word.append_assoc] using rotated)
    (by simpa [Word.append_assoc] using gathered)

/-- Swap arbitrary adjacent nonempty blocks behind two nonempty prefixes. -/
theorem derivesTailSwap
    (first second left right : Word Nat) :
    Derives basis
      (((first ++ second) ++ left) ++ right)
      (((first ++ second) ++ right) ++ left) := by
  have substituted :=
    Derives.subst derivesTailSwapLaw
      (instantiateFourWords right left second first)
  simpa [tailSwapLaw, uzyx, uzxy, w, instantiateFourWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-! ## Explicitly conditional unrestricted endpoint -/

/-- The exact remaining completeness boundary for the shared lane. -/
abbrev CompletenessCertificate {S : Type u} (candidate : Semigroup S) :=
  SemigroupBasis.CoRoots.Order6BlockTraceRootEndpoints.TraceCertificate
    candidate basis

/-- A finite model plus an unrestricted trace certificate gives completeness.
The certificate is a genuine premise and is not supplied by finite projection. -/
theorem basisFor_of_traceCertificate
    {S : Type u} (candidate : Semigroup S)
    (models : Models candidate basis)
    (certificate : CompletenessCertificate candidate) :
    BasisFor candidate basis :=
  SemigroupBasis.CoRoots.Order6BlockTraceRootEndpoints.TraceCertificate.toBasisFor
    certificate models

/-! ## Nine exact table/model wrappers -/

namespace S6_1041

open SemigroupBasis.Generated.Order6InitialPrefixTailTargets.S6_1041

theorem opposite_models :
    Models table.semigroup.opposite basis := by
  rw [basis_eq_reversedTarget]
  exact models.oppositeReversed

theorem opposite_basis
    (certificate :
      CompletenessCertificate table.semigroup.opposite) :
    BasisFor table.semigroup.opposite basis :=
  basisFor_of_traceCertificate _ opposite_models certificate

theorem representative_basis
    (certificate :
      CompletenessCertificate table.semigroup.opposite) :
    BasisFor table.semigroup Target.basis := by
  have reversed := (opposite_basis certificate).oppositeReversed
  simpa [basis_eq_reversedTarget] using reversed

end S6_1041

namespace S6_1043

open SemigroupBasis.Generated.Order6InitialPrefixTailTargets.S6_1043

theorem opposite_models :
    Models table.semigroup.opposite basis := by
  rw [basis_eq_reversedTarget]
  exact models.oppositeReversed

theorem opposite_basis
    (certificate :
      CompletenessCertificate table.semigroup.opposite) :
    BasisFor table.semigroup.opposite basis :=
  basisFor_of_traceCertificate _ opposite_models certificate

theorem representative_basis
    (certificate :
      CompletenessCertificate table.semigroup.opposite) :
    BasisFor table.semigroup Target.basis := by
  have reversed := (opposite_basis certificate).oppositeReversed
  simpa [basis_eq_reversedTarget] using reversed

end S6_1043

namespace S6_1045

open SemigroupBasis.Generated.Order6InitialPrefixTailTargets.S6_1045

theorem opposite_models :
    Models table.semigroup.opposite basis := by
  rw [basis_eq_reversedTarget]
  exact models.oppositeReversed

theorem opposite_basis
    (certificate :
      CompletenessCertificate table.semigroup.opposite) :
    BasisFor table.semigroup.opposite basis :=
  basisFor_of_traceCertificate _ opposite_models certificate

theorem representative_basis
    (certificate :
      CompletenessCertificate table.semigroup.opposite) :
    BasisFor table.semigroup Target.basis := by
  have reversed := (opposite_basis certificate).oppositeReversed
  simpa [basis_eq_reversedTarget] using reversed

end S6_1045

namespace S6_1046

open SemigroupBasis.Generated.Order6InitialPrefixTailTargets.S6_1046

theorem opposite_models :
    Models table.semigroup.opposite basis := by
  rw [basis_eq_reversedTarget]
  exact models.oppositeReversed

theorem opposite_basis
    (certificate :
      CompletenessCertificate table.semigroup.opposite) :
    BasisFor table.semigroup.opposite basis :=
  basisFor_of_traceCertificate _ opposite_models certificate

theorem representative_basis
    (certificate :
      CompletenessCertificate table.semigroup.opposite) :
    BasisFor table.semigroup Target.basis := by
  have reversed := (opposite_basis certificate).oppositeReversed
  simpa [basis_eq_reversedTarget] using reversed

end S6_1046

namespace S6_1062

open SemigroupBasis.Generated.Order6InitialPrefixTailTargets.S6_1062

theorem opposite_models :
    Models table.semigroup.opposite basis := by
  rw [basis_eq_reversedTarget]
  exact models.oppositeReversed

theorem opposite_basis
    (certificate :
      CompletenessCertificate table.semigroup.opposite) :
    BasisFor table.semigroup.opposite basis :=
  basisFor_of_traceCertificate _ opposite_models certificate

theorem representative_basis
    (certificate :
      CompletenessCertificate table.semigroup.opposite) :
    BasisFor table.semigroup Target.basis := by
  have reversed := (opposite_basis certificate).oppositeReversed
  simpa [basis_eq_reversedTarget] using reversed

end S6_1062

namespace S6_1063

open SemigroupBasis.Generated.Order6InitialPrefixTailTargets.S6_1063

theorem opposite_models :
    Models table.semigroup.opposite basis := by
  rw [basis_eq_reversedTarget]
  exact models.oppositeReversed

theorem opposite_basis
    (certificate :
      CompletenessCertificate table.semigroup.opposite) :
    BasisFor table.semigroup.opposite basis :=
  basisFor_of_traceCertificate _ opposite_models certificate

theorem representative_basis
    (certificate :
      CompletenessCertificate table.semigroup.opposite) :
    BasisFor table.semigroup Target.basis := by
  have reversed := (opposite_basis certificate).oppositeReversed
  simpa [basis_eq_reversedTarget] using reversed

end S6_1063

namespace S6_1100

open SemigroupBasis.Generated.Order6InitialPrefixTailTargets.S6_1100

theorem opposite_models :
    Models table.semigroup.opposite basis := by
  rw [basis_eq_reversedTarget]
  exact models.oppositeReversed

theorem opposite_basis
    (certificate :
      CompletenessCertificate table.semigroup.opposite) :
    BasisFor table.semigroup.opposite basis :=
  basisFor_of_traceCertificate _ opposite_models certificate

theorem representative_basis
    (certificate :
      CompletenessCertificate table.semigroup.opposite) :
    BasisFor table.semigroup Target.basis := by
  have reversed := (opposite_basis certificate).oppositeReversed
  simpa [basis_eq_reversedTarget] using reversed

end S6_1100

namespace S6_1102

open SemigroupBasis.Generated.Order6InitialPrefixTailTargets.S6_1102

theorem opposite_models :
    Models table.semigroup.opposite basis := by
  rw [basis_eq_reversedTarget]
  exact models.oppositeReversed

theorem opposite_basis
    (certificate :
      CompletenessCertificate table.semigroup.opposite) :
    BasisFor table.semigroup.opposite basis :=
  basisFor_of_traceCertificate _ opposite_models certificate

theorem representative_basis
    (certificate :
      CompletenessCertificate table.semigroup.opposite) :
    BasisFor table.semigroup Target.basis := by
  have reversed := (opposite_basis certificate).oppositeReversed
  simpa [basis_eq_reversedTarget] using reversed

end S6_1102

namespace S6_1134

open SemigroupBasis.Generated.Order6InitialPrefixTailTargets.S6_1134

theorem opposite_models :
    Models table.semigroup.opposite basis := by
  rw [basis_eq_reversedTarget]
  exact models.oppositeReversed

theorem opposite_basis
    (certificate :
      CompletenessCertificate table.semigroup.opposite) :
    BasisFor table.semigroup.opposite basis :=
  basisFor_of_traceCertificate _ opposite_models certificate

theorem representative_basis
    (certificate :
      CompletenessCertificate table.semigroup.opposite) :
    BasisFor table.semigroup Target.basis := by
  have reversed := (opposite_basis certificate).oppositeReversed
  simpa [basis_eq_reversedTarget] using reversed

end S6_1134

end SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots
