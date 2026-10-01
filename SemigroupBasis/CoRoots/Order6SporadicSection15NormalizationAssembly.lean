import SemigroupBasis.CoRoots.Order6SporadicSection15NormalizationBoundary

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis

/-- Assemble the total list normalizer from the two nontrivial branches. The
all-simple branch is definitionally the input list and needs no extra proof. -/
theorem listDerivesCanonicalList_of_branches
    (normalizeAlpha :
      ∀ letters : List Nat,
        CanonicalData.canonicalBranch letters = .alpha →
          ListDerives letters (CanonicalData.alphaCanonicalList letters))
    (normalizeBeta :
      ∀ letters : List Nat,
        CanonicalData.canonicalBranch letters = .beta →
          ListDerives letters (CanonicalData.betaCanonicalList letters))
    (letters : List Nat) :
    ListDerives letters (CanonicalData.canonicalList letters) := by
  generalize branchEq : CanonicalData.canonicalBranch letters = branch
  cases branch with
  | simple =>
      simpa [CanonicalData.canonicalList, branchEq] using
        (S5_107.ListDerives.refl (basis := basis) letters)
  | alpha =>
      simpa [CanonicalData.canonicalList, branchEq] using
        normalizeAlpha letters branchEq
  | beta =>
      simpa [CanonicalData.canonicalList, branchEq] using
        normalizeBeta letters branchEq

/-- Lift a total list derivation to the word-level normalization interface.
Nonemptiness of the target follows from list derivability itself. -/
theorem canonicalNormalization_of_list_derives
    (normalizeList :
      ∀ letters : List Nat,
        ListDerives letters (CanonicalData.canonicalList letters)) :
    CanonicalNormalization where
  normalize := by
    rintro ⟨head, tail⟩
    have normalized := normalizeList (head :: tail)
    obtain ⟨rightHead, rightTail, targetEq, wordDerivation⟩ :=
      S5_107.ListDerives.from_cons normalized
    refine ⟨S5_107.listWordOfCons rightHead rightTail, ?_, ?_⟩
    · exact wordDerivation
    · change rightHead :: rightTail =
        CanonicalData.canonicalList (head :: tail)
      exact targetEq.symm

/-- The exact remaining Proposition 15.1 interface: unrestricted alpha and
beta list normalizers imply the already isolated canonical normalization. -/
theorem canonicalNormalization_of_branches
    (normalizeAlpha :
      ∀ letters : List Nat,
        CanonicalData.canonicalBranch letters = .alpha →
          ListDerives letters (CanonicalData.alphaCanonicalList letters))
    (normalizeBeta :
      ∀ letters : List Nat,
        CanonicalData.canonicalBranch letters = .beta →
          ListDerives letters (CanonicalData.betaCanonicalList letters)) :
    CanonicalNormalization :=
  canonicalNormalization_of_list_derives <|
    listDerivesCanonicalList_of_branches normalizeAlpha normalizeBeta

end SemigroupBasis.CoRoots.Order6SporadicSection15
