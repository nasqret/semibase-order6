import SemigroupBasis.CoRoots.Order6L3HeavyRank2.Blocks
import SemigroupBasis.CoRoots.S5_791

/-!
# Final-relative lift for `S3_15^op x S5_791`

Four of the five complete `S5_791` axioms occur in the exact eleven-law
block directly, up to orientation.  Its sixth displayed law
`xyxyz = xyxz` is exactly the missing alternating axiom immediately before
an arbitrary nonempty suffix.  Hence an unrestricted `S5_791` derivation
lifts before one fixed suffix.
-/

namespace SemigroupBasis.CoRoots.Order6L3HeavyRank2.S3_15opS5_791

open SemigroupBasis

private abbrev targetBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.basisS3_15opS5_791

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

private def xx : Word Nat := w 0 [0]
private def xxx : Word Nat := w 0 [0, 0]
private def xyx : Word Nat := w 0 [1, 0]
private def xxyx : Word Nat := w 0 [0, 1, 0]
private def xyxx : Word Nat := w 0 [1, 0, 0]
private def xyxy : Word Nat := w 0 [1, 0, 1]
private def xyxz : Word Nat := w 0 [1, 0, 2]
private def xyxyz : Word Nat := w 0 [1, 0, 1, 2]
private def xyzx : Word Nat := w 0 [1, 2, 0]
private def xyxzx : Word Nat := w 0 [1, 0, 2, 0]

private theorem targetPower :
    Derives targetBasis xx xxx :=
  Derives.fromBasis (e := Identity.mk xx xxx) (by decide)

private theorem targetLeftDuplication :
    Derives targetBasis xxyx xyx :=
  Derives.fromBasis (e := Identity.mk xxyx xyx) (by decide)

private theorem targetRightDuplication :
    Derives targetBasis xyx xyxx :=
  Derives.fromBasis (e := Identity.mk xyx xyxx) (by decide)

private theorem targetAlternatingRelativeLiteral :
    Derives targetBasis xyxyz xyxz :=
  Derives.fromBasis (e := Identity.mk xyxyz xyxz) (by decide)

private theorem targetRegularBand :
    Derives targetBasis xyxzx xyzx :=
  Derives.fromBasis (e := Identity.mk xyxzx xyzx) (by decide)

private def instantiateThreeWords
    (first second third : Word Nat) : Nat -> Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

/-- The sixth displayed law is the alternating expansion under a fixed
nonempty suffix after substituting the whole suffix for `z`. -/
theorem derivesAlternatingRelative
    (x y suffix : Word Nat) :
    Derives targetBasis
      (((x ++ y) ++ x) ++ suffix)
      ((((x ++ y) ++ x) ++ y) ++ suffix) := by
  have substituted :=
    Derives.subst targetAlternatingRelativeLiteral.symm
      (instantiateThreeWords x y suffix)
  simpa [xyxz, xyxyz, w, instantiateThreeWords,
    Word.bind, Word.singleton, Word.append, Word.append_assoc] using
      substituted

/-- Every literal axiom of the complete `S5_791` basis is derivable
immediately before an arbitrary fixed nonempty suffix. -/
theorem derivesS5_791AxiomRelative
    (identity : Identity Nat)
    (member : identity ∈ SemigroupBasis.CoRoots.S5_791.basis)
    (suffix : Word Nat) :
    Derives targetBasis
      (identity.lhs ++ suffix) (identity.rhs ++ suffix) := by
  simp only [SemigroupBasis.CoRoots.S5_791.basis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · simpa [SemigroupBasis.CoRoots.S5_791.powerLaw,
      SemigroupBasis.CoRoots.S5_791.xx,
      SemigroupBasis.CoRoots.S5_791.xxx, xx, xxx, w] using
      Derives.appendRight targetPower suffix
  · simpa [SemigroupBasis.CoRoots.S5_791.leftDuplicationLaw,
      SemigroupBasis.CoRoots.S5_791.xyx,
      SemigroupBasis.CoRoots.S5_791.xxyx, xyx, xxyx, w] using
      Derives.appendRight targetLeftDuplication.symm suffix
  · simpa [SemigroupBasis.CoRoots.S5_791.rightDuplicationLaw,
      SemigroupBasis.CoRoots.S5_791.xyx,
      SemigroupBasis.CoRoots.S5_791.xyxx, xyx, xyxx, w] using
      Derives.appendRight targetRightDuplication suffix
  · simpa [SemigroupBasis.CoRoots.S5_791.alternatingLaw,
      SemigroupBasis.CoRoots.S5_791.xyx,
      SemigroupBasis.CoRoots.S5_791.xyxy, w,
      Word.singleton, Word.append, Word.append_assoc] using
      derivesAlternatingRelative
        (Word.singleton 0) (Word.singleton 1) suffix
  · simpa [SemigroupBasis.CoRoots.S5_791.regularBandLaw,
      SemigroupBasis.CoRoots.S5_791.xyzx,
      SemigroupBasis.CoRoots.S5_791.xyxzx, xyzx, xyxzx, w] using
      Derives.appendRight targetRegularBand.symm suffix

private def suffixSubstitution
    (sigma : Nat -> Word Nat) (suffix : Word Nat) : Nat -> Word Nat
  | 3 => suffix
  | letter => sigma letter

/-- A substituted `S5_791` axiom lifts before the same suffix.  The fresh
literal variable `3` marks the suffix during substitution. -/
theorem liftS5_791AxiomUnderSuffix
    (identity : Identity Nat)
    (member : identity ∈ SemigroupBasis.CoRoots.S5_791.basis)
    (suffix : Word Nat) (sigma : Nat -> Word Nat) :
    Derives targetBasis
      (identity.lhs.bind sigma ++ suffix)
      (identity.rhs.bind sigma ++ suffix) := by
  have substituted :=
    Derives.subst
      (derivesS5_791AxiomRelative identity member (Word.singleton 3))
      (suffixSubstitution sigma suffix)
  simp only [SemigroupBasis.CoRoots.S5_791.basis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals
    simpa [SemigroupBasis.CoRoots.S5_791.powerLaw,
      SemigroupBasis.CoRoots.S5_791.leftDuplicationLaw,
      SemigroupBasis.CoRoots.S5_791.rightDuplicationLaw,
      SemigroupBasis.CoRoots.S5_791.alternatingLaw,
      SemigroupBasis.CoRoots.S5_791.regularBandLaw,
      SemigroupBasis.CoRoots.S5_791.xx,
      SemigroupBasis.CoRoots.S5_791.xxx,
      SemigroupBasis.CoRoots.S5_791.xyx,
      SemigroupBasis.CoRoots.S5_791.xxyx,
      SemigroupBasis.CoRoots.S5_791.xyxx,
      SemigroupBasis.CoRoots.S5_791.xyxy,
      SemigroupBasis.CoRoots.S5_791.xyzx,
      SemigroupBasis.CoRoots.S5_791.xyxzx,
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

/-- Every unrestricted `S5_791` derivation lifts after an arbitrary
substitution and immediately before a fixed nonempty suffix. -/
theorem liftS5_791UnderSuffix
    {left right : Word Nat}
    (derivation :
      Derives SemigroupBasis.CoRoots.S5_791.basis left right)
    (suffix : Word Nat) (sigma : Nat -> Word Nat) :
    Derives targetBasis
      (left.bind sigma ++ suffix) (right.bind sigma ++ suffix) := by
  induction derivation generalizing suffix sigma with
  | fromBasis member =>
      exact liftS5_791AxiomUnderSuffix _ member suffix sigma
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
theorem liftS5_791UnderSuffixIdentity
    {left right : Word Nat}
    (derivation :
      Derives SemigroupBasis.CoRoots.S5_791.basis left right)
    (suffix : Word Nat) :
    Derives targetBasis (left ++ suffix) (right ++ suffix) := by
  simpa [bind_singleton] using
    liftS5_791UnderSuffix derivation suffix Word.singleton

end SemigroupBasis.CoRoots.Order6L3HeavyRank2.S3_15opS5_791
