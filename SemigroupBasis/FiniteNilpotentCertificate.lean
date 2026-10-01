import SemigroupBasis.FiniteCertificate

namespace SemigroupBasis
namespace FiniteNilpotentCertificate

/--
The two finite obligations left by `BasisFor.ofNilpotentLengthCutoff`: either
both sides are short, or the left side is short and the right side is exactly
the fixed common representative.
-/
def ShortShape (cutoff : Nat) (common : Word Nat) :
    FiniteCertificate.PairShape :=
  fun left right =>
    (left.toList.length < cutoff ∧ right.toList.length < cutoff) ∨
      (left.toList.length < cutoff ∧ right = common)

/-- A restricted-growth inventory containing both finite nilpotent cases. -/
abbrev Inventory (T : FiniteTable) (cutoff : Nat) (common : Word Nat) :=
  FiniteCertificate.RestrictedGrowthInventory T (ShortShape cutoff common)

end FiniteNilpotentCertificate

namespace BasisFor

/--
Build a basis theorem from one finite restricted-growth inventory.

The inventory reduces all valid short--short and short--common identities to
its listed derivations. Long words remain the signature-specific nilpotency
argument and are delegated to `toCommon`.
-/
theorem ofFiniteNilpotentCertificate
    {T : FiniteTable} {basis : List (Identity Nat)} {cutoff : Nat}
    {common : Word Nat}
    (models : Models T.semigroup basis)
    (toCommon :
      ∀ word : Word Nat,
        cutoff ≤ word.toList.length → Derives basis word common)
    (inventory : FiniteNilpotentCertificate.Inventory T cutoff common)
    (listed : FiniteCertificate.DerivesAll basis inventory.identities) :
    BasisFor T.semigroup basis := by
  apply BasisFor.ofNilpotentLengthCutoff models toCommon
  · intro left right leftShort rightShort valid
    exact inventory.derives listed (Or.inl ⟨leftShort, rightShort⟩) valid
  · intro short shortLength valid
    exact inventory.derives listed (Or.inr ⟨shortLength, rfl⟩) valid

end BasisFor
end SemigroupBasis
