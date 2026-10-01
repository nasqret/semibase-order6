import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0442CyclicMoves
import SemigroupBasis.CoRoots.Order6GenericCASSubdirectS4_11Family

/-! Exact marker invariants and the three short strata. The long stratum
is handled by a guarded replay of the already complete marker theory. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0442Cyclic

open SemigroupBasis Examples

def separator (tested : Nat) : Nat → Fin 3 := fun x => if x = tested then 1 else 2

theorem separatorEval (tested : Nat) (p : List Nat) (final : Nat) :
    markerTable.semigroup.eval (separator tested) (wordOfPrefixFinal p final) =
      if tested ∈ p then (0 : Fin 3) else if final = tested then 1 else 2 :=
  finalMarkerEval_separator tested p final

theorem separatorZero (tested : Nat) (p : List Nat) (final : Nat) :
    markerTable.semigroup.eval (separator tested) (wordOfPrefixFinal p final) = (0 : Fin 3) ↔
      tested ∈ p := by
  rw [separatorEval]
  by_cases member : tested ∈ p <;> by_cases equal : final = tested <;> simp [member, equal]

theorem separatorOne (tested : Nat) (p : List Nat) (final : Nat) :
    markerTable.semigroup.eval (separator tested) (wordOfPrefixFinal p final) = (1 : Fin 3) ↔
      final = tested ∧ tested ∉ p := by
  rw [separatorEval]
  by_cases member : tested ∈ p <;> by_cases equal : final = tested <;> simp [member, equal]

theorem prefixMembership (p q : List Nat) (a b : Nat)
    (valid : (Identity.mk (wordOfPrefixFinal p a) (wordOfPrefixFinal q b)).SatisfiedBy markerTable.semigroup)
    (tested : Nat) : tested ∈ p ↔ tested ∈ q := by
  have evaluated := valid (separator tested)
  calc
    tested ∈ p ↔ markerTable.semigroup.eval (separator tested) (wordOfPrefixFinal p a) = (0 : Fin 3) :=
      (separatorZero tested p a).symm
    _ ↔ markerTable.semigroup.eval (separator tested) (wordOfPrefixFinal q b) = (0 : Fin 3) := by rw [evaluated]
    _ ↔ tested ∈ q := separatorZero tested q b

theorem simpleFinal (p q : List Nat) (a b : Nat)
    (valid : (Identity.mk (wordOfPrefixFinal p a) (wordOfPrefixFinal q b)).SatisfiedBy markerTable.semigroup)
    (tested : Nat) : (a = tested ∧ tested ∉ p) ↔ (b = tested ∧ tested ∉ q) := by
  have evaluated := valid (separator tested)
  calc
    (a = tested ∧ tested ∉ p) ↔ markerTable.semigroup.eval (separator tested) (wordOfPrefixFinal p a) = (1 : Fin 3) :=
      (separatorOne tested p a).symm
    _ ↔ markerTable.semigroup.eval (separator tested) (wordOfPrefixFinal q b) = (1 : Fin 3) := by rw [evaluated]
    _ ↔ (b = tested ∧ tested ∉ q) := separatorOne tested q b

theorem finalCases (p q : List Nat) (a b : Nat)
    (valid : (Identity.mk (wordOfPrefixFinal p a) (wordOfPrefixFinal q b)).SatisfiedBy markerTable.semigroup) :
    a = b ∨ (a ∈ p ∧ b ∈ q) := by
  by_cases equal : a = b
  · exact Or.inl equal
  right
  constructor
  · apply Decidable.byContradiction
    intro absent
    have forced := (simpleFinal p q a b valid a).mp ⟨rfl, absent⟩
    exact equal forced.1.symm
  · apply Decidable.byContradiction
    intro absent
    have forced := (simpleFinal p q a b valid b).mpr ⟨rfl, absent⟩
    exact equal forced.1

theorem twoPermOfMembers (a b c d : Nat)
    (members : ∀ tested, tested ∈ [a, b] ↔ tested ∈ [c, d]) :
    ([a, b] : List Nat).Perm [c, d] := by
  have ca : c = a ∨ c = b := by simpa using (members c).mpr (by simp)
  have da : d = a ∨ d = b := by simpa using (members d).mpr (by simp)
  have ac : a = c ∨ a = d := by simpa using (members a).mp (by simp)
  have bc : b = c ∨ b = d := by simpa using (members b).mp (by simp)
  by_cases equal : a = b
  · subst b
    have ceq : c = a := by simpa using ca
    have deq : d = a := by simpa using da
    subst c
    subst d
    exact List.Perm.refl _
  · rcases ca with ca | cb
    · subst c
      rcases da with da | db
      · subst d
        have impossible : b = a := by simpa using bc
        exact False.elim (equal impossible.symm)
      · subst d
        exact List.Perm.refl _
    · subst c
      rcases da with da | db
      · subst d
        exact List.Perm.swap b a []
      · subst d
        have impossible : a = b := by simpa using ac
        exact False.elim (equal impossible)

theorem oneComplete (a b : Nat)
    (valid : (Identity.mk (Word.singleton a) (Word.singleton b)).SatisfiedBy markerTable.semigroup) :
    Derives pairBasis (Word.singleton a) (Word.singleton b) := by
  have forced := (simpleFinal [] [] a b valid a).mp ⟨rfl, by simp⟩
  rw [forced.1]
  exact Derives.refl _

theorem twoComplete (a b c d : Nat)
    (valid : (Identity.mk (Word.mk a [b]) (Word.mk c [d])).SatisfiedBy markerTable.semigroup) :
    Derives pairBasis (Word.mk a [b]) (Word.mk c [d]) := by
  have heads : a = c := by
    simpa using (prefixMembership [a] [c] b d valid a).mp (by simp)
  subst c
  rcases finalCases [a] [a] b d valid with equal | repeated
  · subst d
    exact Derives.refl _
  · have left : b = a := by simpa using repeated.1
    have right : d = a := by simpa using repeated.2
    subst b
    subst d
    exact Derives.refl _

theorem threeComplete (a b c d e f : Nat)
    (valid : (Identity.mk (Word.mk a [b, c]) (Word.mk d [e, f])).SatisfiedBy markerTable.semigroup) :
    Derives pairBasis (Word.mk a [b, c]) (Word.mk d [e, f]) := by
  have members := prefixMembership [a, b] [d, e] c f valid
  have permuted := twoPermOfMembers a b d e members
  have move : Derives pairBasis (Word.mk a [b, c]) (Word.mk d [e, c]) :=
    prefixPermutation permuted c
  rcases finalCases [a, b] [d, e] c f valid with equal | repeated
  · subst f
    exact move
  · have cMember : c = d ∨ c = e := by simpa using (members c).mp repeated.1
    have fMember : f = d ∨ f = e := by simpa using repeated.2
    apply move.trans
    rcases cMember with cd | ce
    · subst c
      rcases fMember with fd | fe
      · subst f
        exact Derives.refl _
      · subst f
        simpa [Word.singleton, Word.append] using copyFinal (Word.singleton d) (Word.singleton e)
    · subst c
      rcases fMember with fd | fe
      · subst f
        simpa [Word.singleton, Word.append] using (copyFinal (Word.singleton d) (Word.singleton e)).symm
      · subst f
        exact Derives.refl _

theorem longPrefixComplete (p q : List Nat) (a b : Nat)
    (valid : (Identity.mk (wordOfPrefixFinal p a) (wordOfPrefixFinal q b)).SatisfiedBy markerTable.semigroup)
    (leftLong : 4 ≤ (wordOfPrefixFinal p a).toList.length)
    (rightLong : 4 ≤ (wordOfPrefixFinal q b).toList.length) :
    Derives pairBasis (wordOfPrefixFinal p a) (wordOfPrefixFinal q b) := by
  rcases p with _ | ⟨head, tail⟩
  · simp [wordOfPrefixFinal, Word.singleton, Word.toList] at leftLong
  have member : head ∈ q := (prefixMembership (head :: tail) q a b valid head).mp (by simp)
  have lower := finalMarkerThreeBasis_complete.2
    (Identity.mk (wordOfPrefixFinal (head :: tail) a) (wordOfPrefixFinal q b)) valid
  let letter := Word.singleton head
  have lifted := liftFinalMarker lower letter letter letter Word.singleton
  rw [bindSingleton, bindSingleton] at lifted
  have insertLeft := insertThreePrefixLetters (head :: tail) a head (by simp) leftLong
  have insertRight := insertThreePrefixLetters q b head member rightLong
  exact insertLeft.trans (lifted.trans insertRight.symm)

theorem longComplete (identity : Identity Nat)
    (valid : identity.SatisfiedBy markerTable.semigroup)
    (leftLong : 4 ≤ identity.lhs.toList.length)
    (rightLong : 4 ≤ identity.rhs.toList.length) :
    Derives pairBasis identity.lhs identity.rhs := by
  have leftReconstruct := wordOfPrefixFinal_split identity.lhs
  have rightReconstruct := wordOfPrefixFinal_split identity.rhs
  have result := longPrefixComplete (splitPrefixFinal identity.lhs).1 (splitPrefixFinal identity.rhs).1
    (splitPrefixFinal identity.lhs).2 (splitPrefixFinal identity.rhs).2
    (by simpa only [leftReconstruct, rightReconstruct] using valid)
    (by simpa only [leftReconstruct] using leftLong)
    (by simpa only [rightReconstruct] using rightLong)
  simpa only [leftReconstruct, rightReconstruct] using result

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0442Cyclic
