import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0442CyclicCompleteness

/-! S6_5480 uses the opposite marker factor and the same cyclic factor.
The reversed pair system is explicitly derived from the separately approved
singleton system. This is a genuine transport, not a self-duality claim. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0442Cyclic

open SemigroupBasis Examples

theorem singletonSuffixSwap (u v w : Word Nat) :
    Derives singletonBasis ((u ++ v) ++ w) ((u ++ w) ++ v) := by
  have primitive : Derives singletonBasis suffixSwapLaw.lhs suffixSwapLaw.rhs :=
    Derives.fromBasis (e := suffixSwapLaw) (by simp [singletonBasis])
  have substituted := Derives.subst primitive (substituteFour u v w u)
  simpa [suffixSwapLaw, substituteFour, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem singletonTerminalSwitch (u v : Word Nat) :
    Derives singletonBasis ((u ++ u) ++ v) ((v ++ v) ++ u) := by
  have primitive : Derives singletonBasis terminalSwitchLaw.lhs terminalSwitchLaw.rhs :=
    Derives.fromBasis (e := terminalSwitchLaw) (by simp [singletonBasis])
  have substituted := Derives.subst primitive (substituteFour u u u v)
  simpa [terminalSwitchLaw, substituteFour, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem singletonSandwich (u v : Word Nat) :
    Derives singletonBasis ((u ++ v) ++ u) ((v ++ u) ++ v) :=
  (singletonSuffixSwap u v u).trans
    ((singletonTerminalSwitch u v).trans (singletonSuffixSwap v v u))

theorem singletonDuplication (a b c d : Word Nat) :
    Derives singletonBasis (((a ++ b) ++ c) ++ d) ((((a ++ b) ++ b) ++ c) ++ d) := by
  have primitive : Derives singletonBasis duplicationLaw.lhs duplicationLaw.rhs :=
    Derives.fromBasis (e := duplicationLaw) (by simp [singletonBasis])
  have substituted := Derives.subst primitive (substituteFour a b c d)
  simpa [duplicationLaw, substituteFour, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem singletonReverseDuplication (a b c d : Word Nat) :
    Derives singletonBasis (((a ++ b) ++ c) ++ d) ((((a ++ b) ++ c) ++ c) ++ d) := by
  have move := Derives.appendRight (singletonSuffixSwap a b c) d
  have duplicate := singletonDuplication a c b d
  have restore : Derives singletonBasis ((((a ++ c) ++ c) ++ b) ++ d)
      ((((a ++ b) ++ c) ++ c) ++ d) := by
    simpa [Word.append_assoc] using Derives.appendRight (singletonSuffixSwap a (c ++ c) b) d
  exact move.trans (duplicate.trans restore)

theorem singletonReverseBridge (identity : Identity Nat) (member : identity ∈ reversedBasis pairBasis) :
    Derives singletonBasis identity.lhs identity.rhs := by
  change identity ∈ [prefixSwapLaw.reversed, sandwichLaw.reversed, duplicationLaw.reversed] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · change Derives singletonBasis (Word.mk 1 [3, 2]) (Word.mk 1 [2, 3])
    simpa [Word.singleton, Word.append] using
      singletonSuffixSwap (Word.singleton 1) (Word.singleton 3) (Word.singleton 2)
  · change Derives singletonBasis (Word.mk 2 [3, 2]) (Word.mk 3 [2, 3])
    simpa [Word.singleton, Word.append] using singletonSandwich (Word.singleton 2) (Word.singleton 3)
  · change Derives singletonBasis (Word.mk 3 [2, 1, 0]) (Word.mk 3 [2, 1, 1, 0])
    simpa [Word.singleton, Word.append] using
      singletonReverseDuplication (Word.singleton 3) (Word.singleton 2) (Word.singleton 1) (Word.singleton 0)

def cyclicOppositeEmbedding : Embedding cyclicTable.semigroup.opposite cyclicTable.semigroup where
  toFun := id
  map_mul := by decide
  injective := fun _ _ equal => equal

/-- Transport the proved opposite seed through the exact law bridge and
actual cyclic commutativity; no unrestricted hypothesis is supplied by hand. -/
noncomputable def singletonNormalizer : IntersectionNormalizer initialTable.semigroup cyclicTable.semigroup singletonBasis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.transportNormalizer pairOppositeNormalizer
    singletonReverseBridge (fun _ valid => valid)
    (fun identity valid => cyclicOppositeEmbedding.pullback_identity identity valid)

noncomputable def singletonIntersection : IntersectionBasis initialTable.semigroup cyclicTable.semigroup singletonBasis :=
  singletonNormalizer.toIntersectionBasis singletonMarkerModels singletonCyclicModels

theorem singleton_complete (identity : Identity Nat)
    (markerValid : identity.SatisfiedBy initialTable.semigroup)
    (cyclicValid : identity.SatisfiedBy cyclicTable.semigroup) :
    Derives singletonBasis identity.lhs identity.rhs := singletonIntersection.complete identity markerValid cyclicValid

theorem singleton5480_representative_basis : BasisFor table5480.semigroup singletonBasis :=
  singletonNormalizer.basisFor singletonMarkerModels singletonCyclicModels subdirect5480
theorem singleton5480_opposite_basis : BasisFor table5480.semigroup.opposite (reversedBasis singletonBasis) :=
  singleton5480_representative_basis.oppositeReversed
theorem singleton5480_complete (identity : Identity Nat) (valid : identity.SatisfiedBy table5480.semigroup) :
    Derives singletonBasis identity.lhs identity.rhs := singleton5480_representative_basis.2 identity valid
theorem singleton5480_opposite_complete (identity : Identity Nat) (valid : identity.SatisfiedBy table5480.semigroup.opposite) :
    Derives (reversedBasis singletonBasis) identity.lhs identity.rhs := singleton5480_opposite_basis.2 identity valid

noncomputable def singletonOppositeNormalizer :
    IntersectionNormalizer initialTable.semigroup.opposite cyclicTable.semigroup.opposite (reversedBasis singletonBasis) :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    singletonIntersection.oppositeReversed

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0442Cyclic
