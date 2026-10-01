import SemigroupBasis.CoRoots.Order6SporadicSection25ConnectedComparison

/-! A generic head detector for the proved affine lower basis. No finite
alphabet bound or assumed head-matching field is introduced. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection25
open SemigroupBasis

private def headDetector : Semigroup Nat where
  mul := fun first _ => first
  assoc := fun _ _ _ => rfl

private theorem headFold (tail : List Nat) (initial : Nat) :
    tail.foldl (fun value _ => value) initial = initial := by
  induction tail with
  | nil => rfl
  | cons letter rest ih =>
      simpa only [List.foldl_cons] using ih

private theorem headDetector_eval (valuation : Nat → Nat) (word : Word Nat) :
    headDetector.eval valuation word = valuation word.head := by
  exact headFold word.tail (valuation word.head)

theorem affineCore_models_headDetector : Models headDetector affineCore := by
  intro identity member valuation
  rw [headDetector_eval, headDetector_eval]
  simp only [affineCore, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> rfl

theorem affineDerives_heads_equal {left right : Word Nat}
    (derivation : Derives affineCore left right) : left.head = right.head := by
  have equal := derivation.sound affineCore_models_headDetector (fun n => n)
  simpa only [headDetector_eval] using equal

theorem actualAffineValid_heads_equal (identity : Identity Nat)
    (valid : identity.SatisfiedBy Generated.Catalogue.S4_96.table.semigroup.opposite) :
    identity.lhs.head = identity.rhs.head :=
  affineDerives_heads_equal (actualAffineValid_derives identity valid)

theorem connected_affineCompare (withB0 : Bool) (left right : Word Nat)
    (leftNontrivial : left.tail ≠ []) (rightNontrivial : right.tail ≠ [])
    (leftConnected : SupportConnected left.toList)
    (rightConnected : SupportConnected right.toList)
    (valid : (⟨left,right⟩ : Identity Nat).SatisfiedBy
      Generated.Catalogue.S4_96.table.semigroup.opposite) :
    Derives (basis withB0) left right := by
  cases left with
  | mk head leftTail =>
      cases right with
      | mk other rightTail =>
          have heads : head = other := actualAffineValid_heads_equal
            ⟨⟨head,leftTail⟩,⟨other,rightTail⟩⟩ valid
          cases heads
          exact connected_sameHead_affineCompare_words withB0 head leftTail rightTail
            leftNontrivial rightNontrivial leftConnected rightConnected valid

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.affineCore_models_headDetector
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.affineDerives_heads_equal
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.actualAffineValid_heads_equal
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.connected_affineCompare

end SemigroupBasis.CoRoots.Order6SporadicSection25
