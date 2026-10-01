import SemigroupBasis.CoRoots.Order6Astra.C8SplitKeys
import SemigroupBasis.CoRoots.Order6Astra.C8Star

namespace SemigroupBasis.CoRoots.Order6Astra.C8KeyInterfaces

open Order6SporadicSection19.Published
open C8TailCuts C8SemanticKey C8CutCalculus C8KeyCalculus C8SplitKeys
open C8Star ConnectedTerminalEndpoints

theorem empty_iff (u v : List Nat) (same : SameSupport u v) : u = [] ↔ v = [] := by
  cases u with
  | nil =>
    cases v with
    | nil => exact Iff.rfl
    | cons x xs =>
      have impossible := (same x).mpr List.mem_cons_self
      cases impossible
  | cons x xs =>
    cases v with
    | nil =>
      have impossible := (same x).mp List.mem_cons_self
      cases impossible
    | cons y ys => simp

theorem singleton_key (x : Nat) (letters : List Nat) (key : Key [x] letters) : letters = [x] := by
  apply singleton_of_support_count letters x
  · intro y hy
    exact List.mem_singleton.mp ((key.support y).mpr hy)
  · exact (key.simple x).mp (by simp)

theorem transfer_split (a b target : List Nat) (key : Key (a ++ b) target) (apart : Disjoint a b) :
    ∃ c d : List Nat, target = c ++ d ∧ Disjoint c d ∧ Key a c ∧ Key b d := by
  obtain ⟨c, d, literal, same, disjoint⟩ := (key.cuts a).mp ⟨a, b, rfl, same_refl a, apart⟩
  have actual : Key (a ++ b) (c ++ d) := by simpa only [literal] using key
  have both := split_keys a b c d actual apart disjoint (same_symm same)
  exact ⟨c, d, literal, disjoint, both.1, both.2⟩

theorem connected_key (source target : Word Nat) (key : Key source.toList target.toList)
    (connected : Connected source) : Connected target := by
  have size : 2 ≤ target.toList.length := by
    cases target with
    | mk x xs =>
      cases xs with
      | nil =>
        have single := singleton_key x source.toList key.symm
        have sourceSize := connected.1
        rw [single] at sourceSize
        simp at sourceSize
      | cons y ys => simp [Word.toList]
  refine ⟨size, ?_⟩
  rintro ⟨a, b, literal, apart⟩
  have reversed : Key (a.toList ++ b.toList) source.toList := by
    simpa only [literal, Word.toList_append] using key.symm
  obtain ⟨c, d, split, disjoint, first, second⟩ := transfer_split a.toList b.toList source.toList reversed apart
  have cNonempty : c ≠ [] := by
    intro empty
    have impossible := (first.support a.head).mp List.mem_cons_self
    rw [empty] at impossible
    cases impossible
  have dNonempty : d ≠ [] := by
    intro empty
    have impossible := (second.support b.head).mp List.mem_cons_self
    rw [empty] at impossible
    cases impossible
  obtain ⟨x, inC, inD⟩ := connected_cut_overlap source connected c d cNonempty dNonempty split
  exact disjoint x inC inD

theorem derives_key (source target : Word Nat) (derived : Derives basis source target) :
    Key source.toList target.toList := semantic_key source target
      (fun valuation => Derives.sound models derived valuation)

theorem normalized_star_keys (source target : Word Nat) (key : Key source.toList target.toList)
    (connected : Connected source) :
    ∃ left right : Star, Derives basis source left.word ∧ Derives basis target right.word ∧
      Key left.word.toList right.word.toList := by
  obtain ⟨left, first⟩ := C8Star.normalize_connected source connected
  obtain ⟨right, second⟩ := C8Star.normalize_connected target (connected_key source target key connected)
  exact ⟨left, right, first, second,
    (derives_key source left.word first).symm.trans (key.trans (derives_key target right.word second))⟩

end SemigroupBasis.CoRoots.Order6Astra.C8KeyInterfaces

#print axioms SemigroupBasis.CoRoots.Order6Astra.C8KeyInterfaces.transfer_split
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8KeyInterfaces.connected_key
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8KeyInterfaces.normalized_star_keys
