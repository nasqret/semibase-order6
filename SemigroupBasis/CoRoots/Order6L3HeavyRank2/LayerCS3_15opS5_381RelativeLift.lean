import SemigroupBasis.CoRoots.S5_381
import SemigroupBasis.Generated.Order6OneLocalFordLast.DisplayedSigma

/-!
# Final-relative lift for the `S3_15^op x S5_381` ten-law basis

The exact ten-law system contains seven of the eight `S5_381` axioms
directly (up to orientation).  Its fifth displayed law is precisely the
missing square-final switch under a nonempty suffix:
`x^2 y^2 z = x y^2 x z`.  Consequently every unrestricted `S5_381`
derivation lifts immediately before the same fixed suffix.
-/

namespace SemigroupBasis.CoRoots.Order6L3HeavyRank2.S3_15opS5_381

open SemigroupBasis

private abbrev targetBasis : List (Identity Nat) :=
  SemigroupBasis.Generated.Order6OneLocalFordLast.DisplayedSigma.Sigma_17bbc703ba9dbee0.basis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

private def xx : Word Nat := w 0 [0]
private def xxx : Word Nat := w 0 [0, 0]
private def xyx : Word Nat := w 0 [1, 0]
private def xxyx : Word Nat := w 0 [0, 1, 0]
private def xyxx : Word Nat := w 0 [1, 0, 0]
private def xxyy : Word Nat := w 0 [0, 1, 1]
private def xyxy : Word Nat := w 0 [1, 0, 1]
private def yxxy : Word Nat := w 1 [0, 0, 1]
private def xyzx : Word Nat := w 0 [1, 2, 0]
private def xyxzx : Word Nat := w 0 [1, 0, 2, 0]
private def xyzy : Word Nat := w 0 [1, 2, 1]
private def xzyy : Word Nat := w 0 [2, 1, 1]
private def xxyyz : Word Nat := w 0 [0, 1, 1, 2]
private def xyyxz : Word Nat := w 0 [1, 1, 0, 2]

private theorem targetPower :
    Derives targetBasis xx xxx :=
  Derives.fromBasis (e := Identity.mk xx xxx) (by decide)

private theorem targetLeftDuplication :
    Derives targetBasis xxyx xyx :=
  Derives.fromBasis (e := Identity.mk xxyx xyx) (by decide)

private theorem targetRightDuplication :
    Derives targetBasis xyx xyxx :=
  Derives.fromBasis (e := Identity.mk xyx xyxx) (by decide)

private theorem targetSquareInterleave :
    Derives targetBasis xxyy xyxy :=
  Derives.fromBasis (e := Identity.mk xxyy xyxy) (by decide)

private theorem targetSquareInitialSwitch :
    Derives targetBasis xxyy yxxy :=
  Derives.fromBasis (e := Identity.mk xxyy yxxy) (by decide)

private theorem targetInteriorInsertion :
    Derives targetBasis xyxzx xyzx :=
  Derives.fromBasis (e := Identity.mk xyxzx xyzx) (by decide)

private theorem targetPrefixedGather :
    Derives targetBasis xyzy xzyy :=
  Derives.fromBasis (e := Identity.mk xyzy xzyy) (by decide)

private theorem targetSquareFinalRelativeLiteral :
    Derives targetBasis xxyyz xyyxz :=
  Derives.fromBasis (e := Identity.mk xxyyz xyyxz) (by decide)

private def instantiateThreeWords
    (first second third : Word Nat) : Nat -> Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

theorem derivesPower (word : Word Nat) :
    Derives targetBasis (word ++ word) ((word ++ word) ++ word) := by
  have substituted :=
    Derives.subst targetPower
      (instantiateThreeWords word word word)
  simpa [xx, xxx, w, instantiateThreeWords, Word.bind,
    Word.singleton, Word.append, Word.append_assoc] using substituted

theorem derivesRightDuplication (word middle : Word Nat) :
    Derives targetBasis
      ((word ++ middle) ++ word)
      (((word ++ middle) ++ word) ++ word) := by
  have substituted :=
    Derives.subst targetRightDuplication
      (instantiateThreeWords word middle middle)
  simpa [xyx, xyxx, w, instantiateThreeWords, Word.bind,
    Word.singleton, Word.append, Word.append_assoc] using substituted

/-- The only `S5_381` axiom absent unguarded from the target basis becomes
the fifth target axiom after substituting the whole suffix for `z`. -/
theorem derivesSquareFinalRelative
    (x y suffix : Word Nat) :
    Derives targetBasis
      (((x ++ x) ++ (y ++ y)) ++ suffix)
      ((((x ++ y) ++ y) ++ x) ++ suffix) := by
  have substituted :=
    Derives.subst targetSquareFinalRelativeLiteral
      (instantiateThreeWords x y suffix)
  simpa [xxyyz, xyyxz, w, instantiateThreeWords,
    Word.bind, Word.singleton, Word.append, Word.append_assoc] using
      substituted

/-- Every literal axiom of the complete `S5_381` basis is derivable
immediately before an arbitrary fixed nonempty suffix. -/
theorem derivesS5_381AxiomRelative
    (identity : Identity Nat)
    (member : identity ∈ SemigroupBasis.CoRoots.S5_381.basis)
    (suffix : Word Nat) :
    Derives targetBasis
      (identity.lhs ++ suffix) (identity.rhs ++ suffix) := by
  simp only [SemigroupBasis.CoRoots.S5_381.basis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [SemigroupBasis.CoRoots.S5_381.powerLaw,
      SemigroupBasis.CoRoots.S5_381.xx,
      SemigroupBasis.CoRoots.S5_381.xxx, xx, xxx, w] using
      Derives.appendRight targetPower suffix
  · simpa [SemigroupBasis.CoRoots.S5_381.leftDuplicationLaw,
      SemigroupBasis.CoRoots.S5_381.xyx,
      SemigroupBasis.CoRoots.S5_381.xxyx, xyx, xxyx, w] using
      Derives.appendRight targetLeftDuplication.symm suffix
  · simpa [SemigroupBasis.CoRoots.S5_381.rightDuplicationLaw,
      SemigroupBasis.CoRoots.S5_381.xyx,
      SemigroupBasis.CoRoots.S5_381.xyxx, xyx, xyxx, w] using
      Derives.appendRight targetRightDuplication suffix
  · simpa [SemigroupBasis.CoRoots.S5_381.squareInterleaveLaw,
      SemigroupBasis.CoRoots.S5_381.xxyy,
      SemigroupBasis.CoRoots.S5_381.xyxy, xxyy, xyxy, w] using
      Derives.appendRight targetSquareInterleave suffix
  · simpa [SemigroupBasis.CoRoots.S5_381.squareFinalSwitchLaw,
      SemigroupBasis.CoRoots.S5_381.xxyy,
      SemigroupBasis.CoRoots.S5_381.xyyx, w,
      Word.singleton, Word.append, Word.append_assoc] using
      derivesSquareFinalRelative
        (Word.singleton 0) (Word.singleton 1) suffix
  · simpa [SemigroupBasis.CoRoots.S5_381.squareInitialSwitchLaw,
      SemigroupBasis.CoRoots.S5_381.xxyy,
      SemigroupBasis.CoRoots.S5_381.yxxy, xxyy, yxxy, w] using
      Derives.appendRight targetSquareInitialSwitch suffix
  · simpa [SemigroupBasis.CoRoots.S5_381.interiorInsertionLaw,
      SemigroupBasis.CoRoots.S5_381.xyzx,
      SemigroupBasis.CoRoots.S5_381.xyxzx, xyzx, xyxzx, w] using
      Derives.appendRight targetInteriorInsertion.symm suffix
  · simpa [SemigroupBasis.CoRoots.S5_381.prefixedGatherLaw,
      SemigroupBasis.CoRoots.S5_381.xyzy,
      SemigroupBasis.CoRoots.S5_381.xzyy, xyzy, xzyy, w] using
      Derives.appendRight targetPrefixedGather suffix

private def suffixSubstitution
    (sigma : Nat -> Word Nat) (suffix : Word Nat) : Nat -> Word Nat
  | 3 => suffix
  | letter => sigma letter

/-- A substituted `S5_381` axiom lifts before the same suffix.  The fresh
literal variable `3` marks the suffix during the substitution step. -/
theorem liftS5_381AxiomUnderSuffix
    (identity : Identity Nat)
    (member : identity ∈ SemigroupBasis.CoRoots.S5_381.basis)
    (suffix : Word Nat) (sigma : Nat -> Word Nat) :
    Derives targetBasis
      (identity.lhs.bind sigma ++ suffix)
      (identity.rhs.bind sigma ++ suffix) := by
  have substituted :=
    Derives.subst
      (derivesS5_381AxiomRelative identity member (Word.singleton 3))
      (suffixSubstitution sigma suffix)
  simp only [SemigroupBasis.CoRoots.S5_381.basis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simpa [SemigroupBasis.CoRoots.S5_381.powerLaw,
      SemigroupBasis.CoRoots.S5_381.leftDuplicationLaw,
      SemigroupBasis.CoRoots.S5_381.rightDuplicationLaw,
      SemigroupBasis.CoRoots.S5_381.squareInterleaveLaw,
      SemigroupBasis.CoRoots.S5_381.squareFinalSwitchLaw,
      SemigroupBasis.CoRoots.S5_381.squareInitialSwitchLaw,
      SemigroupBasis.CoRoots.S5_381.interiorInsertionLaw,
      SemigroupBasis.CoRoots.S5_381.prefixedGatherLaw,
      SemigroupBasis.CoRoots.S5_381.xx,
      SemigroupBasis.CoRoots.S5_381.xxx,
      SemigroupBasis.CoRoots.S5_381.xyx,
      SemigroupBasis.CoRoots.S5_381.xxyx,
      SemigroupBasis.CoRoots.S5_381.xyxx,
      SemigroupBasis.CoRoots.S5_381.xxyy,
      SemigroupBasis.CoRoots.S5_381.xyxy,
      SemigroupBasis.CoRoots.S5_381.xyyx,
      SemigroupBasis.CoRoots.S5_381.yxxy,
      SemigroupBasis.CoRoots.S5_381.xyzx,
      SemigroupBasis.CoRoots.S5_381.xyxzx,
      SemigroupBasis.CoRoots.S5_381.xyzy,
      SemigroupBasis.CoRoots.S5_381.xzyy,
      suffixSubstitution, Word.bind, Word.singleton, Word.append,
      Word.append_assoc] using substituted

private theorem bind_append
    (left right : Word Nat) (sigma : Nat -> Word Nat) :
    (left ++ right).bind sigma =
      left.bind sigma ++ right.bind sigma := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (word : Word Nat) (tau sigma : Nat -> Word Nat) :
    (word.bind tau).bind sigma =
      word.bind (fun letter => (tau letter).bind sigma) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- Every unrestricted `S5_381` derivation lifts after an arbitrary
substitution and immediately before a fixed nonempty suffix. -/
theorem liftS5_381UnderSuffix
    {left right : Word Nat}
    (derivation :
      Derives SemigroupBasis.CoRoots.S5_381.basis left right)
    (suffix : Word Nat) (sigma : Nat -> Word Nat) :
    Derives targetBasis
      (left.bind sigma ++ suffix) (right.bind sigma ++ suffix) := by
  induction derivation generalizing suffix sigma with
  | fromBasis member =>
      exact liftS5_381AxiomUnderSuffix _ member suffix sigma
  | refl =>
      exact Derives.refl _
  | symm _ induction =>
      exact (induction suffix sigma).symm
  | trans _ _ first second =>
      exact (first suffix sigma).trans (second suffix sigma)
  | prepend stem _ induction =>
      simpa [bind_append, Word.append_assoc] using
        Derives.prepend (stem.bind sigma) (induction suffix sigma)
  | appendRight _ appended induction =>
      simpa [bind_append, Word.append_assoc] using
        induction (appended.bind sigma ++ suffix) sigma
  | subst _ tau induction =>
      simpa [bind_bind] using
        induction suffix (fun letter => (tau letter).bind sigma)

/-- Identity-substitution specialization of the final-relative lift. -/
theorem liftS5_381UnderSuffixIdentity
    {left right : Word Nat}
    (derivation :
      Derives SemigroupBasis.CoRoots.S5_381.basis left right)
    (suffix : Word Nat) :
    Derives targetBasis (left ++ suffix) (right ++ suffix) := by
  simpa [bind_singleton] using
    liftS5_381UnderSuffix derivation suffix Word.singleton

end SemigroupBasis.CoRoots.Order6L3HeavyRank2.S3_15opS5_381
