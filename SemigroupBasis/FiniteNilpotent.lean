import SemigroupBasis.Equational

namespace SemigroupBasis

/-- Substitution by singleton words is ordinary variable renaming. -/
theorem Word.bind_singletons_eq_map (word : Word α) (rename : α → β) :
    word.bind (fun x => Word.singleton (rename x)) =
      word.map rename := by
  apply Word.toList_injective
  rw [Word.toList_bind]
  change word.toList.flatMap (fun x => [rename x]) =
    word.toList.map rename
  induction word.toList with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.map_cons,
        List.singleton_append, ih]

/-- Equational derivations are stable under simultaneous variable renaming. -/
theorem Derives.rename
    {basis : List (Identity α)} {left right : Word α}
    (derivation : Derives basis left right) (rename : α → α) :
    Derives basis (left.map rename) (right.map rename) := by
  simpa only [Word.bind_singletons_eq_map] using
    Derives.subst derivation
      (fun x => Word.singleton (rename x))

/-- If every sufficiently long word derives to one common representative,
then every two sufficiently long words are derivably equal. -/
theorem Derives.longWords_of_common
    {basis : List (Identity α)} {cutoff : Nat} {common : Word α}
    (toCommon :
      ∀ word : Word α,
        cutoff ≤ word.toList.length → Derives basis word common)
    (left right : Word α)
    (leftLong : cutoff ≤ left.toList.length)
    (rightLong : cutoff ≤ right.toList.length) :
    Derives basis left right :=
  Derives.trans (toCommon left leftLong)
    (Derives.symm (toCommon right rightLong))

/-- Generic completeness split for a finite nilpotent short-word basis.

The nilpotency argument is isolated in `longLong`; the finite certificate only
has to handle identities with two short sides and identities with one short
side. The reverse short/long orientation is obtained by symmetry. -/
theorem BasisFor.ofLengthCutoff
    {G : Semigroup S} {basis : List (Identity α)} (cutoff : Nat)
    (models : Models G basis)
    (shortShort :
      ∀ left right : Word α,
        left.toList.length < cutoff →
        right.toList.length < cutoff →
        (∀ valuation, G.eval valuation left = G.eval valuation right) →
        Derives basis left right)
    (shortLong :
      ∀ short long : Word α,
        short.toList.length < cutoff →
        cutoff ≤ long.toList.length →
        (∀ valuation, G.eval valuation short = G.eval valuation long) →
        Derives basis short long)
    (longLong :
      ∀ left right : Word α,
        cutoff ≤ left.toList.length →
        cutoff ≤ right.toList.length →
        Derives basis left right) :
    BasisFor G basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  by_cases leftShort : identity.lhs.toList.length < cutoff
  · by_cases rightShort : identity.rhs.toList.length < cutoff
    · exact shortShort identity.lhs identity.rhs leftShort rightShort valid
    · exact shortLong identity.lhs identity.rhs leftShort
        (Nat.le_of_not_gt rightShort) valid
  · have leftLong : cutoff ≤ identity.lhs.toList.length :=
      Nat.le_of_not_gt leftShort
    by_cases rightShort : identity.rhs.toList.length < cutoff
    · apply Derives.symm
      exact shortLong identity.rhs identity.lhs rightShort leftLong
        (fun valuation => (valid valuation).symm)
    · exact longLong identity.lhs identity.rhs leftLong
        (Nat.le_of_not_gt rightShort)

/-- Completeness split specialized to finite nilpotent certificates.

Every long word is first sent to one common zero representative. Consequently,
the finite certificate only handles valid short--short identities and valid
short--common identities; no signature-specific proof may inspect an arbitrary
long word. -/
theorem BasisFor.ofNilpotentLengthCutoff
    {G : Semigroup S} {basis : List (Identity α)} {cutoff : Nat}
    {common : Word α}
    (models : Models G basis)
    (toCommon :
      ∀ word : Word α,
        cutoff ≤ word.toList.length → Derives basis word common)
    (shortShort :
      ∀ left right : Word α,
        left.toList.length < cutoff →
        right.toList.length < cutoff →
        (∀ valuation, G.eval valuation left = G.eval valuation right) →
        Derives basis left right)
    (shortCommon :
      ∀ short : Word α,
        short.toList.length < cutoff →
        (∀ valuation, G.eval valuation short = G.eval valuation common) →
        Derives basis short common) :
    BasisFor G basis := by
  apply BasisFor.ofLengthCutoff cutoff models shortShort
  · intro short long shortLength longLength valid
    have longToCommon : Derives basis long common :=
      toCommon long longLength
    have shortValidCommon :
        ∀ valuation, G.eval valuation short = G.eval valuation common :=
      fun valuation =>
        (valid valuation).trans
          (Derives.sound models longToCommon valuation)
    exact Derives.trans
      (shortCommon short shortLength shortValidCommon)
      (Derives.symm longToCommon)
  · exact Derives.longWords_of_common toCommon

end SemigroupBasis
