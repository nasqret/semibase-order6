import SemigroupBasis.CoRoots.Order6Astra.C8KeyInterfaces
import SemigroupBasis.CoRoots.Order6Astra.C8StarComparison

namespace SemigroupBasis.CoRoots.Order6Astra.C8Completeness

open Order6SporadicSection19.Published
open C8TailCuts C8SemanticKey C8ListDerives C8KeyInterfaces C8Star C8StarComparison
open ConnectedTerminalEndpoints

theorem complete_of_alphabet_size (size : Nat) :
    ∀ alphabet : List Nat, alphabet.length = size → ∀ u v : List Nat,
      (∀ x ∈ u, x ∈ alphabet) → Key u v → Rel u v := by
  refine Nat.strongRecOn (motive := fun n =>
    ∀ alphabet : List Nat, alphabet.length = n → ∀ u v : List Nat,
      (∀ x ∈ u, x ∈ alphabet) → Key u v → Rel u v) size ?_
  intro n ih alphabet length u v covered key
  have recursive : Smaller alphabet := by
    intro smaller shorter a b localCovered localKey
    have bound : smaller.length < n := by rw [← length]; exact shorter
    exact ih smaller.length bound smaller rfl a b localCovered localKey
  cases u with
  | nil =>
    have empty := (C8KeyInterfaces.empty_iff [] v key.support).mp rfl
    subst v
    trivial
  | cons x xs =>
    cases xs with
    | nil =>
      have equal := singleton_key x v key
      rw [equal]
      exact C8ListDerives.refl [x]
    | cons y ys =>
      let source : Word Nat := ⟨x, y :: ys⟩
      cases v with
      | nil =>
        have impossible := (key.support x).mp List.mem_cons_self
        cases impossible
      | cons z zs =>
        let target : Word Nat := ⟨z, zs⟩
        have actualKey : Key source.toList target.toList := key
        by_cases connected : Connected source
        · obtain ⟨left, right, first, second, normalKey⟩ :=
            normalized_star_keys source target actualKey connected
          have normalCovered : ∀ value ∈ left.word.toList, value ∈ alphabet := by
            intro value member
            exact covered value ((C8ListDerives.support (of_words first) value).mpr member)
          have compared := compare_stars alphabet recursive left right normalKey normalCovered
          exact of_words (first.trans (compared.trans second.symm))
        · have cut : ∃ a b : Word Nat, source = a ++ b ∧ RootFamily.Apart a b := by
            apply Classical.byContradiction
            intro noCut
            exact connected ⟨by simp [source, Word.toList], noCut⟩
          obtain ⟨a, b, sourceSplit, apart⟩ := cut
          have sourceLiteral : source.toList = a.toList ++ b.toList := by
            rw [sourceSplit, Word.toList_append]
          have cutKey : Key (a.toList ++ b.toList) target.toList := by
            simpa only [sourceLiteral] using actualKey
          obtain ⟨c, d, targetSplit, _, firstKey, secondKey⟩ :=
            transfer_split a.toList b.toList target.toList cutKey apart
          have wholeCovered : ∀ value ∈ a.toList ++ b.toList, value ∈ alphabet := by
            intro value member
            apply covered value
            change value ∈ source.toList
            rw [sourceLiteral]
            exact member
          have aHead : a.head ∈ alphabet :=
            wholeCovered a.head (List.mem_append.mpr (Or.inl List.mem_cons_self))
          have bHead : b.head ∈ alphabet :=
            wholeCovered b.head (List.mem_append.mpr (Or.inr List.mem_cons_self))
          have firstCovered : ∀ value ∈ a.toList, value ∈ alphabet.erase b.head := by
            intro value member
            have different : value ≠ b.head := by
              intro equal
              subst value
              exact apart b.head member List.mem_cons_self
            exact (List.mem_erase_of_ne different).mpr
              (wholeCovered value (List.mem_append.mpr (Or.inl member)))
          have secondCovered : ∀ value ∈ b.toList, value ∈ alphabet.erase a.head := by
            intro value member
            have different : value ≠ a.head := by
              intro equal
              subst value
              exact apart a.head List.mem_cons_self member
            exact (List.mem_erase_of_ne different).mpr
              (wholeCovered value (List.mem_append.mpr (Or.inr member)))
          have firstDerived := recursive (alphabet.erase b.head) (erase_shorter alphabet b.head bHead)
            a.toList c firstCovered firstKey
          have secondDerived := recursive (alphabet.erase a.head) (erase_shorter alphabet a.head aHead)
            b.toList d secondCovered secondKey
          change Rel source.toList target.toList
          rw [sourceLiteral, targetSplit]
          exact C8ListDerives.append firstDerived secondDerived

/-- Equality of the complete, unbounded component/tail key produces an actual
derivation from the literal 38-law basis. The recursive assumptions above
are discharged by strong induction on an ambient alphabet's length. -/
theorem complete_key (u v : List Nat) (key : Key u v) : Rel u v :=
  complete_of_alphabet_size u.length u rfl u v (fun _ h => h) key

theorem complete_word (u v : Word Nat) (same : SemanticSimpleAdjacency.EqualEval u v) :
    Derives basis u v := to_words (complete_key u.toList v.toList (semantic_key u v same))

theorem basisFor : BasisFor table.semigroup basis :=
  ⟨models, fun identity satisfied => complete_word identity.lhs identity.rhs satisfied⟩

end SemigroupBasis.CoRoots.Order6Astra.C8Completeness

#print axioms SemigroupBasis.CoRoots.Order6Astra.C8Completeness.complete_key
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8Completeness.complete_word
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8Completeness.basisFor
