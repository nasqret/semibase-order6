import SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_209Normal
import SemigroupBasis.CoRoots.Order6FactorPairS3_6opS5_209Normal

/-!
# Square-free obstruction to the recorded ten-law candidate

The common identity `xyzw = xzyw` preserves the literal first letter and is
valid in `S5_209`. Every side of every recorded candidate law contains a
repeated variable. Since semigroup substitutions replace variables by
nonempty words, no candidate-law instance can occur in a square-free word.
Consequently the exact ten-law candidate cannot be an intersection basis.
-/

namespace SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_209Normal

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

/-- The square-free common identity missing from the exact ten-law packet. -/
def squareFreeInteriorSwap : Identity Nat :=
  Identity.mk (w 0 [1, 2, 3]) (w 0 [2, 1, 3])

private def squareFreeInteriorSwapFin : Identity (Fin 4) :=
  Identity.mk (Word.mk 0 [1, 2, 3]) (Word.mk 0 [2, 1, 3])

private theorem squareFreeInteriorSwapFin_map :
    squareFreeInteriorSwapFin.map Fin.val = squareFreeInteriorSwap := rfl

/-- The obstruction identity holds in the left-zero factor. -/
theorem squareFreeInteriorSwap_valid_s2_4 :
    squareFreeInteriorSwap.SatisfiedBy
      SemigroupBasis.Generated.S2_4.table.semigroup := by
  rw [← squareFreeInteriorSwapFin_map]
  exact
    SemigroupBasis.Generated.S2_4.table.checkIdentityNat_sound
      squareFreeInteriorSwapFin (by decide)

/-- The obstruction identity is the already-verified open-interior swap for
the stored `S5_209` factor. -/
theorem squareFreeInteriorSwap_valid_s5_209 :
    squareFreeInteriorSwap.SatisfiedBy
      SemigroupBasis.Generated.S5_209.table.semigroup := by
  simpa [squareFreeInteriorSwap,
    SemigroupBasis.CoRoots.Order6FactorPairS3_6opS5_209Normal.missingOpenInteriorSwap,
    w] using
      SemigroupBasis.CoRoots.Order6FactorPairS3_6opS5_209Normal.missingOpenInteriorSwap_valid_s5_209

private theorem nodup_of_flatMap_nodup
    (source : List Nat) (images : Nat → List Nat)
    (imageNonempty : ∀ letter, images letter ≠ [])
    (mappedNodup : (source.flatMap images).Nodup) :
    source.Nodup := by
  induction source with
  | nil =>
      simp
  | cons head tail ih =>
      rw [List.flatMap_cons] at mappedNodup
      have split := List.nodup_append.mp mappedNodup
      apply List.nodup_cons.mpr
      constructor
      · intro headMember
        obtain ⟨marker, markerMember⟩ :=
          List.exists_mem_of_ne_nil
            (images head) (imageNonempty head)
        have markerInTail : marker ∈ tail.flatMap images := by
          simp only [List.mem_flatMap]
          exact ⟨head, headMember, markerMember⟩
        exact split.2.2 marker markerMember marker markerInTail rfl
      · exact ih split.2.1

private theorem source_nodup_of_bind_nodup
    (source : Word Nat) (substitution : Nat → Word Nat)
    (bound : (source.bind substitution).toList.Nodup) :
    source.toList.Nodup := by
  rw [Word.toList_bind] at bound
  apply nodup_of_flatMap_nodup source.toList
    (fun letter => (substitution letter).toList)
  · intro letter
    cases substitution letter
    simp [Word.toList]
  · exact bound

private theorem basis_has_repetition :
    ∀ identity ∈ basis,
      ¬ identity.lhs.toList.Nodup ∧
        ¬ identity.rhs.toList.Nodup := by
  decide

/-- A derivation from the recorded ten laws cannot move a square-free word. -/
private theorem derives_nodup_rigid
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    (left.toList.Nodup → left = right) ∧
      (right.toList.Nodup → left = right) := by
  induction derivation with
  | fromBasis member =>
      have repeated := basis_has_repetition _ member
      exact
        ⟨fun nodup => False.elim (repeated.1 nodup),
          fun nodup => False.elim (repeated.2 nodup)⟩
  | refl =>
      exact ⟨fun _ => rfl, fun _ => rfl⟩
  | symm nestedDerivation ih =>
      exact
        ⟨fun nodup => (ih.2 nodup).symm,
          fun nodup => (ih.1 nodup).symm⟩
  | trans firstDerivation secondDerivation first second =>
      constructor
      · intro nodup
        have equalFirst := first.1 nodup
        subst_vars
        exact second.1 nodup
      · intro nodup
        have equalSecond := second.2 nodup
        subst_vars
        exact first.2 nodup
  | prepend p nestedDerivation ih =>
      constructor
      · intro nodup
        have suffixNodup : _ := (List.nodup_append.mp <| by
          simpa [Word.toList_append] using nodup).2.1
        rw [ih.1 suffixNodup]
      · intro nodup
        have suffixNodup : _ := (List.nodup_append.mp <| by
          simpa [Word.toList_append] using nodup).2.1
        rw [ih.2 suffixNodup]
  | appendRight nestedDerivation suffix ih =>
      constructor
      · intro nodup
        have prefixNodup : _ := (List.nodup_append.mp <| by
          simpa [Word.toList_append] using nodup).1
        rw [ih.1 prefixNodup]
      · intro nodup
        have prefixNodup : _ := (List.nodup_append.mp <| by
          simpa [Word.toList_append] using nodup).1
        rw [ih.2 prefixNodup]
  | subst nestedDerivation substitution ih =>
      constructor
      · intro nodup
        have sourceNodup :=
          source_nodup_of_bind_nodup _ substitution nodup
        rw [ih.1 sourceNodup]
      · intro nodup
        have targetNodup :=
          source_nodup_of_bind_nodup _ substitution nodup
        rw [ih.2 targetNodup]

/-- The common square-free identity is not derivable from the ten laws. -/
theorem squareFreeInteriorSwap_not_derivable :
    ¬ Derives basis
      squareFreeInteriorSwap.lhs squareFreeInteriorSwap.rhs := by
  intro derivation
  have literal :=
    (derives_nodup_rigid derivation).1 (by decide)
  exact
    (by decide :
      squareFreeInteriorSwap.lhs ≠ squareFreeInteriorSwap.rhs) literal

/-- Therefore the requested unconditional joint-completeness theorem for the
exact ten laws is false. -/
theorem jointCompleteness_isFalse :
    ¬ (∀ identity : Identity Nat,
        identity.SatisfiedBy
            SemigroupBasis.Generated.S2_4.table.semigroup →
          identity.SatisfiedBy
              SemigroupBasis.Generated.S5_209.table.semigroup →
            Derives basis identity.lhs identity.rhs) := by
  intro complete
  exact squareFreeInteriorSwap_not_derivable
    (complete squareFreeInteriorSwap
      squareFreeInteriorSwap_valid_s2_4
      squareFreeInteriorSwap_valid_s5_209)

/-- No `IntersectionBasis` can have the exact ten-law list as its basis. -/
theorem intersectionBasis_isFalse :
    ¬ IntersectionBasis
        SemigroupBasis.Generated.S2_4.table.semigroup
        SemigroupBasis.Generated.S5_209.table.semigroup
        basis := by
  intro intersection
  exact squareFreeInteriorSwap_not_derivable
    (intersection.complete squareFreeInteriorSwap
      squareFreeInteriorSwap_valid_s2_4
      squareFreeInteriorSwap_valid_s5_209)

end SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_209Normal
