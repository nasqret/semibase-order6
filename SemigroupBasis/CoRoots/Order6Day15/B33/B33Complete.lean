import SemigroupBasis.CoRoots.Order6Day15.B33.B33Parity
import SemigroupBasis.CoRoots.Order6Day15.B33.B33Boundary
import SemigroupBasis.CoRoots.Order6Day15.B33.B33LiteralProbes
import SemigroupBasis.CoRoots.Order6Day15.B33.B33Soundness6225
import SemigroupBasis.CoRoots.Order6Day15.B33.B33Soundness9878

namespace SemigroupBasis.CoRoots.Order6Day15.B33

variable {S : Type u} {G : Semigroup S}

theorem normal_eq_of_eval (P : Probes G) (bs cs : List Block)
    (hb : Normal bs) (hc : Normal cs)
    (same : ∀ v, evalBlocks G v bs = evalBlocks G v cs) : bs = cs := by
  have hl := letters_eq_of_eval P bs cs hb.1 hc.1 same
  exact normal_eq_of_key bs cs hb hc hl
    (oddPowers_eq_of_eval P bs cs hb.1 hc.1 hl same)
    (headSimple_eq_of_eval P bs cs hb.1 hc.1 hl same)
    (tailSimple_eq_of_eval P bs cs hb.1 hc.1 hl same)

/-- Unconditional completeness from actual derivation and normal-form separation. -/
theorem basisFor_of_probes (P : Probes G) (hm : Models G basis) : BasisFor G basis := by
  refine ⟨hm,?_⟩
  intro e valid
  have sameBlocks : normalBlocks e.lhs = normalBlocks e.rhs := by
    apply normal_eq_of_eval P _ _ (normalBlocks_normal e.lhs) (normalBlocks_normal e.rhs)
    intro v
    rw [normalBlocks_eval G hm,normalBlocks_eval G hm,valid v]
  have sameWords : normalWord e.lhs = normalWord e.rhs := by
    apply Word.toList_injective
    rw [normalWord_toList,normalWord_toList,sameBlocks]
  have right := normalWord_derives e.rhs
  rw [← sameWords] at right
  exact (normalWord_derives e.lhs).trans right.symm

theorem basisFor6225 : BasisFor table6225.semigroup basis :=
  basisFor_of_probes probes6225 models6225

theorem basisFor9878 : BasisFor table9878.semigroup basis :=
  basisFor_of_probes probes9878 models9878

end SemigroupBasis.CoRoots.Order6Day15.B33
