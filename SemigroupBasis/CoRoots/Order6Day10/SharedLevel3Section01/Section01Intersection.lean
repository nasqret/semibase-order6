import SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section01.Section01TerminalForms
import SemigroupBasis.Subdirect

/-! Unrestricted exact B23 converse. Actual S5_240 semantics supplies the
endpoint signature; actual C2 (or C2-with-zero) semantics supplies parity.
The case split is exhaustive at arbitrary rank and length. No bounded key,
new displayed law, semigroup cancellation, or owner completeness parameter
is assumed. -/

namespace SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section01.Section01Intersection

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_107
open SemigroupBasis.CoRoots.S5_83
open SemigroupBasis.CoRoots.S5_240
open SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section01.Section01Macros
open SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section01.Section01TerminalForms

abbrev basis := Section01Macros.basis
abbrev leftTable := Section01Macros.leftTable
abbrev alternateTable := Section01Macros.alternateTable
abbrev rightTable := Section01Macros.rightTable

theorem repeatedPenultimateTransfer {left right : Word Nat}
    (same : SameEndpointSuffixSignature left right)
    {stem rest : List Nat} {p t q s : Nat}
    (leftSplit : terminalSplit left = .pair stem p t)
    (rightSplit : terminalSplit right = .pair rest q s)
    (repeated : p ∈ stem ∨ p = t) : q ∈ rest ∨ q = s := by
  by_cases member : q ∈ rest
  · exact Or.inl member
  by_cases equal : q = s
  · exact Or.inr equal
  have rightSimple : SimplePenultimatePair right q s := by
    simp [SimplePenultimatePair, rightSplit, member, Ne.symm equal]
  have leftSimple := (same.simplePenultimatePair q s).mpr rightSimple
  have parts : p = q ∧ t = s ∧ q ∉ stem ∧ s ≠ q := by
    simpa [SimplePenultimatePair, leftSplit] using leftSimple
  rcases parts with ⟨rfl, rfl, absent, distinct⟩
  rcases repeated with member | equal
  · exact False.elim (absent member)
  · exact False.elim (distinct equal.symm)

theorem repeatedFinalTransfer {left right : Word Nat}
    (same : SameEndpointSuffixSignature left right)
    {stem rest : List Nat} {p t q s : Nat}
    (leftSplit : terminalSplit left = .pair stem p t)
    (rightSplit : terminalSplit right = .pair rest q s)
    (repeated : t ∈ stem ∨ t = p) : s ∈ rest ∨ s = q := by
  by_cases member : s ∈ rest
  · exact Or.inl member
  by_cases equal : s = q
  · exact Or.inr equal
  have rightUnique : UniqueFinal right s := by
    simp [UniqueFinal, rightSplit, member, equal]
  have leftUnique := (same.uniqueFinal s).mpr rightUnique
  have parts : t = s ∧ t ≠ p ∧ t ∉ stem := by
    simpa [UniqueFinal, leftSplit] using leftUnique
  rcases repeated with member | equal
  · exact False.elim (parts.2.2 member)
  · exact False.elim (parts.2.1 equal)

theorem stemsSameAtSimpleFinal (left right : List Nat) (p q t : Nat)
    (support : ∀ z, z ∈ left ++ [p, t] ↔ z ∈ right ++ [q, t])
    (pMember : p ∈ left) (qMember : q ∈ right)
    (leftAbsent : t ∉ left) (rightAbsent : t ∉ right) :
    ∀ z, z ∈ left ↔ z ∈ right := by
  intro z
  constructor
  · intro member
    have whole : z ∈ right ++ [q, t] := (support z).mp (by simp [member])
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at whole
    rcases whole with whole | rfl | rfl
    · exact whole
    · exact qMember
    · exact False.elim (leftAbsent member)
  · intro member
    have whole : z ∈ left ++ [p, t] := (support z).mpr (by simp [member])
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at whole
    rcases whole with whole | rfl | rfl
    · exact whole
    · exact pMember
    · exact False.elim (rightAbsent member)

theorem stemsSameAtSimplePair (left right : List Nat) (p t : Nat)
    (support : ∀ z, z ∈ left ++ [p, t] ↔ z ∈ right ++ [p, t])
    (leftAbsent : p ∉ left) (rightAbsent : p ∉ right)
    (finalMembership : t ∈ left ↔ t ∈ right) :
    ∀ z, z ∈ left ↔ z ∈ right := by
  intro z
  by_cases isP : z = p
  · subst z
    simp [leftAbsent, rightAbsent]
  by_cases isT : z = t
  · subst z
    exact finalMembership
  simpa [isP, isT] using support z

set_option maxHeartbeats 800000 in
theorem listDerivesOfSignatureParity (left right : Word Nat)
    (same : SameEndpointSuffixSignature left right)
    (parity : ∀ z, left.toList.count z % 2 = right.toList.count z % 2) :
    D left.toList right.toList := by
  cases leftSplit : terminalSplit left with
  | singleton final =>
      have leftSingleton : IsSingletonWord left := by simp [IsSingletonWord, leftSplit]
      have rightSingleton := same.singleton.mp leftSingleton
      cases rightSplit : terminalSplit right with
      | singleton other =>
          have leftUnique : UniqueFinal left final := by simp [UniqueFinal, leftSplit]
          have rightUnique := (same.uniqueFinal final).mp leftUnique
          have equal : other = final := by simpa [UniqueFinal, rightSplit] using rightUnique
          subst other
          rw [← terminalSplit_renderList left, ← terminalSplit_renderList right,
            leftSplit, rightSplit]
          exact ListDerives.refl _
      | pair rest p t => simp [IsSingletonWord, rightSplit] at rightSingleton
  | pair stem p t =>
      cases rightSplit : terminalSplit right with
      | singleton other =>
          have rightSingleton : IsSingletonWord right := by simp [IsSingletonWord, rightSplit]
          have leftSingleton := same.singleton.mpr rightSingleton
          simp [IsSingletonWord, leftSplit] at leftSingleton
      | pair rest q s =>
          have leftList : left.toList = stem ++ [p, t] := by
            simpa [leftSplit, TerminalSplit.renderList] using (terminalSplit_renderList left).symm
          have rightList : right.toList = rest ++ [q, s] := by
            simpa [rightSplit, TerminalSplit.renderList] using (terminalSplit_renderList right).symm
          have support : ∀ z, z ∈ stem ++ [p, t] ↔ z ∈ rest ++ [q, s] := by
            simpa [SameSupport, leftList, rightList] using same.support
          have wholeParity : ∀ z, (stem ++ [p, t]).count z % 2 = (rest ++ [q, s]).count z % 2 := by
            simpa [leftList, rightList] using parity
          suffices derived : D (stem ++ [p, t]) (rest ++ [q, s]) by
            simpa [leftList, rightList] using derived
          by_cases pRepeated : p ∈ stem ∨ p = t
          · have qRepeated := repeatedPenultimateTransfer same leftSplit rightSplit pRepeated
            by_cases tRepeated : t ∈ stem ∨ t = p
            · have sRepeated := repeatedFinalTransfer same leftSplit rightSplit tRepeated
              have tMember : t ∈ rest ++ [q, s] := (support t).mp (by simp)
              obtain ⟨leftPre, leftNormal, leftSupport⟩ :=
                bothRepeatedNormal stem p t t pRepeated tRepeated (by simp)
              obtain ⟨rightPre, rightNormal, rightSupport⟩ :=
                bothRepeatedNormal rest q s t qRepeated sRepeated tMember
              have prefixSupport : ∀ z, z ∈ leftPre ↔ z ∈ rightPre := by
                intro z
                exact (leftSupport z).trans ((support z).trans (rightSupport z).symm)
              exact alignCommonSuffix (stem ++ [p, t]) (rest ++ [q, s])
                leftPre rightPre [] t t (by simpa using leftNormal)
                (by simpa using rightNormal) prefixSupport wholeParity
            · have tAbsent : t ∉ stem := fun h => tRepeated (Or.inl h)
              have distinct : t ≠ p := fun h => tRepeated (Or.inr h)
              have leftUnique : UniqueFinal left t := by simp [UniqueFinal, leftSplit, tAbsent, distinct]
              have rightUnique := (same.uniqueFinal t).mp leftUnique
              have rightParts : s = t ∧ s ≠ q ∧ s ∉ rest := by
                simpa [UniqueFinal, rightSplit] using rightUnique
              have sameFinal : s = t := rightParts.1
              subst s
              have pMember : p ∈ stem := pRepeated.resolve_right (Ne.symm distinct)
              have qMember : q ∈ rest := qRepeated.resolve_right (Ne.symm rightParts.2.1)
              have stemSupport := stemsSameAtSimpleFinal stem rest p q t support
                pMember qMember tAbsent rightParts.2.2
              have pRight : p ∈ rest := (stemSupport p).mp pMember
              obtain ⟨leftPre, leftNormal, leftSupport⟩ :=
                repeatedPenultimateNormal stem p t p pMember pMember
              obtain ⟨rightPre, rightNormal, rightSupport⟩ :=
                repeatedPenultimateNormal rest q t p qMember pRight
              have prefixSupport : ∀ z, z ∈ leftPre ↔ z ∈ rightPre := by
                intro z
                exact (leftSupport z).trans ((stemSupport z).trans (rightSupport z).symm)
              exact alignCommonSuffix (stem ++ [p, t]) (rest ++ [q, t])
                leftPre rightPre [t] p p
                (by simpa [List.append_assoc] using leftNormal)
                (by simpa [List.append_assoc] using rightNormal) prefixSupport wholeParity
          · have pAbsent : p ∉ stem := fun h => pRepeated (Or.inl h)
            have distinct : t ≠ p := fun h => pRepeated (Or.inr h.symm)
            have leftSimple : SimplePenultimatePair left p t := by
              simp [SimplePenultimatePair, leftSplit, pAbsent, distinct]
            have rightSimple := (same.simplePenultimatePair p t).mp leftSimple
            have rightParts : q = p ∧ s = t ∧ p ∉ rest ∧ t ≠ p := by
              simpa [SimplePenultimatePair, rightSplit] using rightSimple
            have samePenultimate : q = p := rightParts.1
            have sameFinal : s = t := rightParts.2.1
            subst q
            subst s
            have absentIff : t ∉ stem ↔ t ∉ rest := by
              simpa [UniqueFinal, leftSplit, rightSplit, distinct] using same.uniqueFinal t
            have finalMembership : t ∈ stem ↔ t ∈ rest := by
              constructor
              · intro member
                apply Decidable.byContradiction
                intro absent
                exact (absentIff.mpr absent) member
              · intro member
                apply Decidable.byContradiction
                intro absent
                exact (absentIff.mp absent) member
            have stemSupport := stemsSameAtSimplePair stem rest p t support
              pAbsent rightParts.2.2.1 finalMembership
            exact alignCommonSuffix (stem ++ [p, t]) (rest ++ [p, t])
              stem rest [] p t (by simpa using ListDerives.refl (basis := basis) (stem ++ [p, t]))
              (by simpa using ListDerives.refl (basis := basis) (rest ++ [p, t]))
              stemSupport wholeParity

theorem derivesOfSignatureParity (left right : Word Nat)
    (same : SameEndpointSuffixSignature left right)
    (parity : ∀ z, left.toList.count z % 2 = right.toList.count z % 2) :
    Derives basis left right := by
  have derived := listDerivesOfSignatureParity left right same parity
  cases left with
  | mk head tail =>
      cases right with
      | mk other rest => exact derived.toWord

def Complete : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy leftTable.semigroup →
    identity.SatisfiedBy rightTable.semigroup →
    Derives basis identity.lhs identity.rhs

theorem complete : Complete := by
  intro identity leftValid rightValid
  exact derivesOfSignatureParity identity.lhs identity.rhs
    (CoRoots.S5_240.valid_signature identity rightValid)
    (cyclicValid_parity_eq identity leftValid)

def AlternateComplete : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy alternateTable.semigroup →
    identity.SatisfiedBy rightTable.semigroup →
    Derives basis identity.lhs identity.rhs

theorem completeAlternate : AlternateComplete := by
  intro identity leftValid rightValid
  exact derivesOfSignatureParity identity.lhs identity.rhs
    (CoRoots.S5_240.valid_signature identity rightValid)
    (parityZeroValid_parity identity leftValid)

theorem derives_iff_joint_valid (identity : Identity Nat) :
    Derives basis identity.lhs identity.rhs ↔
      identity.SatisfiedBy leftTable.semigroup ∧ identity.SatisfiedBy rightTable.semigroup := by
  constructor
  · intro derivation
    exact ⟨fun valuation => derivation.sound modelsLeft valuation,
      fun valuation => derivation.sound modelsRight valuation⟩
  · intro valid
    exact complete identity valid.1 valid.2

theorem derives_iff_alternate_joint_valid (identity : Identity Nat) :
    Derives basis identity.lhs identity.rhs ↔
      identity.SatisfiedBy alternateTable.semigroup ∧ identity.SatisfiedBy rightTable.semigroup := by
  constructor
  · intro derivation
    exact ⟨fun valuation => derivation.sound modelsAlternate valuation,
      fun valuation => derivation.sound modelsRight valuation⟩
  · intro valid
    exact completeAlternate identity valid.1 valid.2

def intersectionBasis : IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := modelsLeft
  rightModels := modelsRight
  complete := complete

def alternateIntersectionBasis : IntersectionBasis alternateTable.semigroup rightTable.semigroup basis where
  leftModels := modelsAlternate
  rightModels := modelsRight
  complete := completeAlternate

abbrev FinitePair (target : FiniteTable) :=
  SubdirectPair target.semigroup leftTable.semigroup rightTable.semigroup

abbrev AlternateFinitePair (target : FiniteTable) :=
  SubdirectPair target.semigroup alternateTable.semigroup rightTable.semigroup

theorem basisForOfFinitePair (target : FiniteTable) (pair : FinitePair target) :
    BasisFor target.semigroup basis := intersectionBasis.basisFor pair

theorem basisForOfAlternateFinitePair (target : FiniteTable) (pair : AlternateFinitePair target) :
    BasisFor target.semigroup basis := alternateIntersectionBasis.basisFor pair

theorem basisForOppositeOfFinitePair (target : FiniteTable)
    (pair : SubdirectPair target.semigroup.opposite leftTable.semigroup.opposite rightTable.semigroup.opposite) :
    BasisFor target.semigroup.opposite (reversedBasis basis) :=
  intersectionBasis.oppositeReversed.basisFor pair

theorem basisForOppositeOfAlternateFinitePair (target : FiniteTable)
    (pair : SubdirectPair target.semigroup.opposite alternateTable.semigroup.opposite rightTable.semigroup.opposite) :
    BasisFor target.semigroup.opposite (reversedBasis basis) :=
  alternateIntersectionBasis.oppositeReversed.basisFor pair

end SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section01.Section01Intersection
