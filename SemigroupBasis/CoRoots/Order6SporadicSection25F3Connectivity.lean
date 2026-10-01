import SemigroupBasis.CoRoots.Order6SporadicSection25B0Bridge
import SemigroupBasis.CoRoots.Order6SporadicSection25ConnectedClosure

/-! The constructive connectivity assertion in Section25 Lemma25.6.
The inserted letters already occur in the adjacent factors. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection25
open SemigroupBasis

theorem first_mem_of_nonempty_front (head : Nat) (tail front back : List Nat)
    (shape : head :: tail = front ++ back) (nonempty : front ≠ []) : head ∈ front := by
  cases front with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest =>
      have equal := (List.cons.inj shape).1
      rw [← equal]
      exact List.Mem.head _

theorem supportConnected_bridge (left right : List Nat) (tail head : Nat)
    (leftConnected : SupportConnected left) (rightConnected : SupportConnected right)
    (tailMember : tail ∈ left) (headMember : head ∈ right) :
    SupportConnected (left ++ [head,head,tail,tail] ++ right) := by
  intro front back shape frontNonempty backNonempty
  have split : left ++ ([head,head,tail,tail] ++ right) = front ++ back := by
    simpa only [List.append_assoc] using shape
  rcases List.append_eq_append_iff.mp split with
    ⟨middle, frontShape, remainderShape⟩ | ⟨middle, leftShape, backShape⟩
  · rcases List.append_eq_append_iff.mp remainderShape with
      ⟨inside, middleShape, rightShape⟩ | ⟨inside, bridgeShape, backShape⟩
    · by_cases empty : inside = []
      · refine ⟨head, ?_, ?_⟩
        · rw [frontShape, middleShape]
          exact List.mem_append_right left (List.mem_append_left inside (by simp))
        · have rightEqual : right = back := by simpa only [empty, List.nil_append] using rightShape
          rw [← rightEqual]
          exact headMember
      · rcases rightConnected inside back rightShape empty backNonempty with ⟨letter, inInside, inBack⟩
        refine ⟨letter, ?_, inBack⟩
        rw [frontShape, middleShape]
        exact List.mem_append_right left (List.mem_append_right [head,head,tail,tail] inInside)
    · by_cases empty : middle = []
      · refine ⟨tail, ?_, ?_⟩
        · rw [frontShape, empty, List.append_nil]
          exact tailMember
        · have bridgeEqual : [head,head,tail,tail] = inside := by
            simpa only [empty, List.nil_append] using bridgeShape
          rw [backShape, ← bridgeEqual]
          exact List.mem_append_left right (by simp)
      · have inMiddle := first_mem_of_nonempty_front head [head,tail,tail] middle inside bridgeShape empty
        refine ⟨head, ?_, ?_⟩
        · rw [frontShape]
          exact List.mem_append_right left inMiddle
        · rw [backShape]
          exact List.mem_append_right inside headMember
  · by_cases empty : middle = []
    · refine ⟨tail, ?_, ?_⟩
      · have leftEqual : left = front := by simpa only [empty, List.append_nil] using leftShape
        rw [← leftEqual]
        exact tailMember
      · rw [backShape, empty, List.nil_append]
        exact List.mem_append_left right (by simp)
    · rcases leftConnected front middle leftShape frontNonempty empty with ⟨letter, inFront, inMiddle⟩
      refine ⟨letter, inFront, ?_⟩
      rw [backShape]
      exact List.mem_append_left ([head,head,tail,tail] ++ right) inMiddle

theorem bridge_support_iff (left right : List Nat) (tail head letter : Nat)
    (tailMember : tail ∈ left) (headMember : head ∈ right) :
    letter ∈ left ++ [head,head,tail,tail] ++ right ↔ letter ∈ left ++ right := by
  constructor
  · intro member
    rcases List.mem_append.mp member with inFront | inRight
    · rcases List.mem_append.mp inFront with inLeft | inBridge
      · exact List.mem_append_left right inLeft
      · have either : letter = head ∨ letter = tail := by simpa using inBridge
        rcases either with equal | equal
        · subst letter
          exact List.mem_append_right left headMember
        · subst letter
          exact List.mem_append_left right tailMember
    · exact List.mem_append_right left inRight
  · intro member
    rcases List.mem_append.mp member with inLeft | inRight
    · exact List.mem_append_left right (List.mem_append_left [head,head,tail,tail] inLeft)
    · exact List.mem_append_right (left ++ [head,head,tail,tail]) inRight

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.first_mem_of_nonempty_front
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.supportConnected_bridge
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.bridge_support_iff

end SemigroupBasis.CoRoots.Order6SporadicSection25
