import SemigroupBasis.CoRoots.Order6LeeLiProposition8ACanonicalSemantics
import SemigroupBasis.CoRoots.Order6LeeLiProposition8ACompleteness
import SemigroupBasis.CoRoots.Order6LeeLiProposition8ACubePosition

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeLiProposition8A

open SemigroupBasis

/-! # Unrestricted Lee--Li Proposition 8.1/A assembly -/

/-- The direct fifteen-law system is an identity basis for the published
Lee--Li Proposition 8.1 monoid A.  The proof combines the unrestricted
canonical reduction with the canonical semantic characterization and the
sorting subsystem. -/
theorem published_basis : BasisFor publishedTable.semigroup basis := by
  apply publishedBasisOfCanonicalPipeline Proposition8ACanonical
  · intro source
    obtain ⟨normal, canonical, counts, derivation⟩ :=
      existsProposition8ACanonicalReduction source
    exact ⟨normal, canonical, canonical.capThree, counts, derivation⟩
  · intro target canonical
    exact canonical.simpleSplitCanonical
  · intro leftHead rightHead leftTail rightTail leftCanonical
      rightCanonical valid
    exact Proposition8ACanonical.canonicalCompletePrecedence
      (Identity.mk
        (S5_107.listWordOfCons leftHead leftTail)
        (S5_107.listWordOfCons rightHead rightTail))
      valid leftCanonical rightCanonical

end SemigroupBasis.CoRoots.Order6LeeLiProposition8A
