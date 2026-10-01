import SemigroupBasis.CoRoots.S5_1000
import SemigroupBasis.CoRoots.S5_196
import SemigroupBasis.Examples.CyclicThree
import SemigroupBasis.Transfer

/-!
Source-only exact invariants for the `S5_1000`/`S5_1003` basis.

The two factor embeddings below are the Lean form of the deterministic marker
assignments recorded in the family semantic certificate.  No normalization or
completeness claim is made here.
-/

namespace SemigroupBasis.CoRoots

open SemigroupBasis
open SemigroupBasis.Examples

namespace S5_1000Invariant

/-- Equality of variable support, ignoring multiplicity. -/
abbrev SameSupport := S5_196.SameSupport

/-- Pointwise equality of occurrence counts modulo three.  Together with the
separate support field, this records positive multiplicity modulo three: an
absent variable is distinct from a positive multiple of three. -/
def SamePositiveMultiplicityModThree
    (left right : Word Nat) : Prop :=
  forall letter,
    left.toList.count letter % 3 =
      right.toList.count letter % 3

/-- The selected variable is final and occurs globally exactly once. -/
abbrev UniqueFinal := S5_196.SimpleFinal

/-- Equality of the optional globally unique final variable. -/
abbrev SameUniqueFinal := S5_196.SameSimpleFinal

/-- The exact invariant predicted by the semantic certificate. -/
structure SameSignature (left right : Word Nat) : Prop where
  support : SameSupport left right
  positiveMultiplicityModThree :
    SamePositiveMultiplicityModThree left right
  uniqueFinal : SameUniqueFinal left right

abbrev sameSignature (left right : Word Nat) : Prop :=
  SameSignature left right

namespace SameSignature

theorem refl (word : Word Nat) : SameSignature word word :=
  ⟨fun _ => Iff.rfl, fun _ => rfl, fun _ => Iff.rfl⟩

theorem symm {left right : Word Nat}
    (same : SameSignature left right) :
    SameSignature right left :=
  ⟨fun letter => (same.support letter).symm,
    fun letter => (same.positiveMultiplicityModThree letter).symm,
    fun letter => (same.uniqueFinal letter).symm⟩

theorem trans {left middle right : Word Nat}
    (first : SameSignature left middle)
    (second : SameSignature middle right) :
    SameSignature left right :=
  ⟨fun letter =>
      (first.support letter).trans (second.support letter),
    fun letter =>
      (first.positiveMultiplicityModThree letter).trans
        (second.positiveMultiplicityModThree letter),
    fun letter =>
      (first.uniqueFinal letter).trans (second.uniqueFinal letter)⟩

end SameSignature

/-- Final-marker validity recovers support and the optional unique final;
cyclic-three validity recovers every multiplicity modulo three. -/
theorem sameSignature_of_marker_residue_valid
    (identity : Identity Nat)
    (markerValid :
      identity.SatisfiedBy finalMarkerThree.semigroup)
    (residueValid :
      identity.SatisfiedBy cyclicThree.semigroup) :
    SameSignature identity.lhs identity.rhs :=
  ⟨S5_196.finalMarkerValid_support identity markerValid,
    cyclicThreeValid_mod_eq identity residueValid,
    S5_196.finalMarkerValid_simpleFinal identity markerValid⟩

end S5_1000Invariant

namespace S5_1000

private theorem finalMarkerModelsBasis :
    Models finalMarkerThree.semigroup basis :=
  models_of_finite_checks finalMarkerThree
    (by decide) (by decide) (by decide) (by decide)

private theorem cyclicThreeModelsBasis :
    Models cyclicThree.semigroup basis :=
  models_of_finite_checks cyclicThree
    (by decide) (by decide) (by decide) (by decide)

/-- Every derivation from the four-law basis preserves support, positive
multiplicity modulo three, and the optional globally unique final variable. -/
theorem derives_sameSignature
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    S5_1000Invariant.SameSignature left right :=
  S5_1000Invariant.sameSignature_of_marker_residue_valid
    ⟨left, right⟩
    (fun valuation =>
      derivation.sound finalMarkerModelsBasis valuation)
    (fun valuation =>
      derivation.sound cyclicThreeModelsBasis valuation)

/-- Every displayed basis law preserves the exact invariant after an
arbitrary simultaneous substitution by nonempty words. -/
theorem basisLaw_bind_sameSignature
    (identity : Identity Nat) (member : identity ∈ basis)
    (substitution : Nat → Word Nat) :
    S5_1000Invariant.SameSignature
      (identity.lhs.bind substitution)
      (identity.rhs.bind substitution) :=
  derives_sameSignature <|
    Derives.subst (Derives.fromBasis member) substitution

end S5_1000

namespace S5_1000FamilyInvariant

namespace S5_1000

/-- The certificate assignment `special = 2`, `default = 3` in one-based
notation, factored through the accepted final-marker model. -/
def finalMarkerEmbedding :
    Embedding finalMarkerThree.semigroup
      Generated.Catalogue.S5_1000.table.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩ else
      if value.val = 1 then ⟨1, by decide⟩ else ⟨2, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

/-- The certificate assignment `special = 4`, `default = 3` in one-based
notation, factored through the accepted cyclic-three model. -/
def residueEmbedding :
    Embedding cyclicThree.semigroup
      Generated.Catalogue.S5_1000.table.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨2, by decide⟩ else
      if value.val = 1 then ⟨3, by decide⟩ else ⟨4, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

/-- Every valid identity of the exact `S5_1000` catalogue table has the
complete support/residue/unique-final signature. -/
theorem valid_sameSignature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_1000.table.semigroup) :
    S5_1000Invariant.SameSignature
      identity.lhs identity.rhs :=
  S5_1000Invariant.sameSignature_of_marker_residue_valid identity
    (finalMarkerEmbedding.pullback_identity identity valid)
    (residueEmbedding.pullback_identity identity valid)

end S5_1000

namespace S5_1003

/-- The certificate assignment `special = 2`, `default = 3` in one-based
notation, factored through the accepted final-marker model. -/
def finalMarkerEmbedding :
    Embedding finalMarkerThree.semigroup
      Generated.Catalogue.S5_1003.table.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩ else
      if value.val = 1 then ⟨1, by decide⟩ else ⟨2, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

/-- The certificate assignment `special = 4`, `default = 1` in one-based
notation, factored through the accepted cyclic-three model. -/
def residueEmbedding :
    Embedding cyclicThree.semigroup
      Generated.Catalogue.S5_1003.table.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩ else
      if value.val = 1 then ⟨3, by decide⟩ else ⟨4, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

/-- Every valid identity of the exact `S5_1003` catalogue table has the
complete support/residue/unique-final signature. -/
theorem valid_sameSignature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_1003.table.semigroup) :
    S5_1000Invariant.SameSignature
      identity.lhs identity.rhs :=
  S5_1000Invariant.sameSignature_of_marker_residue_valid identity
    (finalMarkerEmbedding.pullback_identity identity valid)
    (residueEmbedding.pullback_identity identity valid)

end S5_1003

end S5_1000FamilyInvariant

end SemigroupBasis.CoRoots
