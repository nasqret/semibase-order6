import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0430Presentation

/-! Derive the already proved sixteen-law fixed-head S5_207 seed from each
corrected package. The bridge is actual substitution/context derivation,
including the doubled-final switch; no finite check supplies completeness. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0430

open SemigroupBasis Examples
open Msg0428LinearObstruction (zzy_zzzy yxzzy_zzyxy yyzzy_zzyyz zyyzy_zzyyz)
open S2_4.Rank045 (law00 law01 law02 law03 law04 law05 law06 law07 law08
  law09 law10 law11 law12 law13 law14 law15)

private def inst (first second third fourth : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | 3 => fourth
  | letter + 4 => Word.singleton (letter + 4)

theorem expansion_of_member {basis : List (Identity Nat)} (member : zzy_zzzy ∈ basis)
    (first final : Word Nat) :
    Derives basis (first ++ first ++ final) (first ++ first ++ first ++ final) := by
  have primitive := (Derives.fromBasis member).subst (inst final final first final)
  simpa [zzy_zzzy, inst, Word.bind, Word.append, Word.singleton, Word.append_assoc] using primitive

theorem swap_of_member {basis : List (Identity Nat)} (member : linearLaw ∈ basis)
    (head first second final : Word Nat) :
    Derives basis (head ++ first ++ second ++ final) (head ++ second ++ first ++ final) := by
  have primitive := (Derives.fromBasis member).subst (inst head first second final)
  simpa [linearLaw, Msg0428LinearObstruction.missingIdentity, inst,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using primitive

theorem pairExpansion (first final : Word Nat) :
    Derives pairBasis (first ++ first ++ final) (first ++ first ++ first ++ final) :=
  expansion_of_member (by simp [pairBasis, Msg0428LinearObstruction.pairBasis]) first final

theorem pairSwap (head first second final : Word Nat) :
    Derives pairBasis (head ++ first ++ second ++ final) (head ++ second ++ first ++ final) :=
  swap_of_member (by simp [pairBasis]) head first second final

theorem singletonExpansion (first final : Word Nat) :
    Derives singletonBasis (first ++ first ++ final) (first ++ first ++ first ++ final) :=
  expansion_of_member (by simp [singletonBasis, Msg0428LinearObstruction.singletonBasis]) first final

theorem singletonSwap (head first second final : Word Nat) :
    Derives singletonBasis (head ++ first ++ second ++ final) (head ++ second ++ first ++ final) :=
  swap_of_member (by simp [singletonBasis]) head first second final

/-- The head-changing approved law with arbitrary nonempty blocks. -/
theorem pairHeadShift (head middle next : Word Nat) :
    Derives pairBasis (head ++ middle ++ next ++ next ++ head)
      (next ++ next ++ head ++ middle ++ head) := by
  have primitive : Derives pairBasis yxzzy_zzyxy.lhs yxzzy_zzyxy.rhs :=
    Derives.fromBasis (by simp [pairBasis, Msg0428LinearObstruction.pairBasis])
  have substituted := primitive.subst (inst middle head next next)
  simpa [yxzzy_zzyxy, inst, Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted

theorem pairDoubleSwitch (first second : Word Nat) :
    Derives pairBasis (first ++ first ++ second ++ second ++ first)
      (second ++ second ++ first ++ first ++ second) := by
  have primitive : Derives pairBasis yyzzy_zzyyz.lhs yyzzy_zzyyz.rhs :=
    Derives.fromBasis (by simp [pairBasis, Msg0428LinearObstruction.pairBasis])
  have substituted := primitive.subst (inst first first second second)
  simpa [yyzzy_zzyyz, inst, Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Pair8 derives the singleton's five-letter terminal law. -/
theorem pairTerminalSwitch (first second : Word Nat) :
    Derives pairBasis (first ++ second ++ second ++ first ++ second)
      (first ++ first ++ second ++ second ++ first) := by
  have arrange := pairSwap first (second ++ second) first second
  have changeHead := (pairHeadShift second second first).symm
  have changeFinal := pairDoubleSwitch second first
  simp only [Word.append_assoc] at arrange changeHead changeFinal ⊢
  exact arrange.trans (changeHead.trans changeFinal)

theorem singletonTerminalSwitch (first second : Word Nat) :
    Derives singletonBasis (first ++ second ++ second ++ first ++ second)
      (first ++ first ++ second ++ second ++ first) := by
  have primitive : Derives singletonBasis zyyzy_zzyyz.lhs zyyzy_zzyyz.rhs :=
    Derives.fromBasis (by simp [singletonBasis, Msg0428LinearObstruction.singletonBasis])
  have substituted := primitive.subst (inst first second first first)
  simpa [zyyzy_zzyyz, inst, Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted

structure FixedHeadRules (basis : List (Identity Nat)) : Prop where
  expand : ∀ first final : Word Nat,
    Derives basis (first ++ first ++ final) (first ++ first ++ first ++ final)
  swap : ∀ head first second final : Word Nat,
    Derives basis (head ++ first ++ second ++ final) (head ++ second ++ first ++ final)
  doubled : ∀ first second : Word Nat,
    Derives basis (first ++ first ++ second ++ second ++ first)
      (first ++ first ++ second ++ second ++ second)

def pairFixedHeadRules : FixedHeadRules pairBasis where
  expand := pairExpansion
  swap := pairSwap
  doubled := fun first second => by
    have changeFinal := (pairTerminalSwitch first second).symm
    have arrange := pairSwap first (second ++ second) first second
    simp only [Word.append_assoc] at changeFinal arrange ⊢
    exact changeFinal.trans arrange

def singletonFixedHeadRules : FixedHeadRules singletonBasis where
  expand := singletonExpansion
  swap := singletonSwap
  doubled := fun first second => by
    have changeFinal := (singletonTerminalSwitch first second).symm
    have arrange := singletonSwap first (second ++ second) first second
    simp only [Word.append_assoc] at changeFinal arrange ⊢
    exact changeFinal.trans arrange

/-- Every old displayed law has an actual derivation from the new rules. -/
theorem FixedHeadRules.oldSeedLaw {basis : List (Identity Nat)} (rules : FixedHeadRules basis)
    (identity : Identity Nat) (member : identity ∈ S2_4.Rank045.basis) :
    Derives basis identity.lhs identity.rhs := by
  simp only [S2_4.Rank045.basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [law00, Word.append, Word.singleton] using rules.expand (Word.singleton 0) (Word.singleton 0)
  · simpa [law01, Word.append, Word.singleton] using (rules.expand (Word.singleton 0) (Word.singleton 1)).symm
  · simpa [law02, Word.append, Word.singleton] using
      rules.swap (Word.singleton 0) (Word.singleton 0) (Word.singleton 1) (Word.singleton 0)
  · simpa [law03, Word.append, Word.singleton] using
      rules.swap (Word.singleton 0) (Word.singleton 0) (Word.singleton 1) (Word.singleton 1)
  · simpa [law04, Word.append, Word.singleton] using rules.doubled (Word.singleton 0) (Word.singleton 1)
  · simpa [law05, Word.append, Word.singleton] using
      rules.swap (Word.singleton 0) (Word.singleton 0) (Word.singleton 1) (Word.singleton 2)
  · simpa [law06, Word.append, Word.singleton] using
      rules.swap (Word.singleton 0) (Word.singleton 1) (Word.singleton 2) (Word.singleton 0)
  · simpa [law07, Word.append, Word.singleton] using
      rules.swap (Word.singleton 0) (Word.singleton 1) (Word.singleton 2) (Word.singleton 1)
  · exact rules.swap (Word.singleton 0) (Word.singleton 1) (Word.singleton 2) (Word.singleton 3)
  · simpa [law09, Word.append, Word.singleton] using
      rules.swap (Word.mk 0 [1]) (Word.singleton 2) (Word.singleton 3) (Word.singleton 0)
  · exact rules.swap (Word.singleton 0) (Word.singleton 1) (Word.singleton 2) (Word.singleton 3)
  · exact rules.swap (Word.singleton 0) (Word.singleton 1) (Word.singleton 2) (Word.singleton 3)
  · exact rules.swap (Word.singleton 0) (Word.singleton 1) (Word.singleton 2) (Word.singleton 3)
  · exact rules.swap (Word.singleton 0) (Word.singleton 1) (Word.singleton 2) (Word.singleton 3)
  · simpa [law14, Word.append, Word.singleton] using
      rules.swap (Word.mk 0 [1]) (Word.singleton 2) (Word.singleton 3) (Word.singleton 0)
  · simpa [law15, Word.append, Word.singleton] using
      rules.swap (Word.mk 0 [1]) (Word.singleton 2) (Word.singleton 3) (Word.singleton 0)

/-- Unrestricted completeness with the SAME literal head and actual lower
theory. Both hypotheses are semantic/structural necessities, not a bounded key. -/
theorem FixedHeadRules.complete {basis : List (Identity Nat)} (rules : FixedHeadRules basis)
    (identity : Identity Nat) (heads : identity.lhs.head = identity.rhs.head)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have leftValid : identity.SatisfiedBy S2_4.Rank045.leftTable.semigroup := by
    change identity.SatisfiedBy leftZeroTwo.semigroup
    intro valuation
    rw [leftZeroTwo_eval, leftZeroTwo_eval, heads]
  exact (S2_4.Rank045.Seed.derives_of_factor_valid identity leftValid rightValid).transport rules.oldSeedLaw

theorem FixedHeadRules.middlePermutation {basis : List (Identity Nat)} (rules : FixedHeadRules basis)
    (head final : Nat) {left right : List Nat} (permutation : left.Perm right) :
    Derives basis (wordOfPrefixFinal (head :: left) final) (wordOfPrefixFinal (head :: right) final) :=
  (S2_4.Rank045.Seed.derivesMiddlePermutation head final permutation).transport rules.oldSeedLaw

theorem FixedHeadRules.duplicateInitial {basis : List (Identity Nat)} (rules : FixedHeadRules basis)
    (head final : Nat) (middle : List Nat) (present : head ∈ middle) :
    Derives basis (wordOfPrefixFinal (head :: middle) final)
      (wordOfPrefixFinal (head :: head :: middle) final) := by
  simpa only [wordOfPrefixFinal_cons] using
    (S2_4.Rank045.Seed.derivesDuplicateRepeatedHead head final middle present).transport rules.oldSeedLaw

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0430
