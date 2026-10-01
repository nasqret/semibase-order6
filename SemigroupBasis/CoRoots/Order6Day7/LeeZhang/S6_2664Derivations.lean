import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2664Presentation
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.InteriorEndpointCalculus

/-!
# Instantiating the shared calculus from S6_2664's exact raw12

Every primitive obligation is discharged by a displayed law with an
arbitrary nonempty-word substitution. No condition-membership flag,
semantic completeness claim, or bounded screen is a premise.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2664

open SemigroupBasis

abbrev framedWord : Nat → List Nat → Nat → Word Nat := InteriorEndpoint.framedWord

private def substituteThree (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

theorem derivesSquareFinal (x y : Word Nat) :
    Derives basis (((x ++ x) ++ y) ++ x) (((x ++ x) ++ y) ++ y) := by
  have primitive : Derives basis law02.lhs law02.rhs :=
    Derives.fromBasis (by simp [basis])
  simpa [law02, substituteThree, Word.bind, Word.append, Word.append_assoc] using
    primitive.subst (substituteThree x y y)

theorem derivesSquareTransfer (x y : Word Nat) :
    Derives basis (((x ++ x) ++ y) ++ x) (((x ++ y) ++ x) ++ x) := by
  have primitive : Derives basis law03.lhs law03.rhs :=
    Derives.fromBasis (by simp [basis])
  simpa [law03, substituteThree, Word.bind, Word.append, Word.append_assoc] using
    primitive.subst (substituteThree x y y)

theorem derivesSquareInitial (x y : Word Nat) :
    Derives basis (((x ++ x) ++ y) ++ x) (((y ++ x) ++ y) ++ x) := by
  have primitive : Derives basis law04.lhs law04.rhs :=
    Derives.fromBasis (by simp [basis])
  simpa [law04, substituteThree, Word.bind, Word.append, Word.append_assoc] using
    primitive.subst (substituteThree x y y)

theorem derivesReturnDuplication (x y : Word Nat) :
    Derives basis ((x ++ y) ++ x) (((x ++ y) ++ y) ++ x) := by
  have primitive : Derives basis law08.lhs law08.rhs :=
    Derives.fromBasis (by simp [basis])
  simpa [law08, substituteThree, Word.bind, Word.append, Word.append_assoc] using
    primitive.subst (substituteThree x y y)

theorem derivesInteriorIdempotence (before middle after : Word Nat) :
    Derives basis (((before ++ middle) ++ middle) ++ after)
      ((before ++ middle) ++ after) := by
  have primitive : Derives basis law10.lhs law10.rhs :=
    Derives.fromBasis (by simp [basis])
  simpa [law10, substituteThree, Word.bind, Word.append, Word.append_assoc] using
    primitive.subst (substituteThree before middle after)

theorem derivesInitialPairRetarget (x y z : Word Nat) :
    Derives basis (((x ++ x) ++ y) ++ z) (((y ++ x) ++ y) ++ z) := by
  have primitive : Derives basis law05.lhs law05.rhs :=
    Derives.fromBasis (by simp [basis])
  simpa [law05, substituteThree, Word.bind, Word.append, Word.append_assoc] using
    primitive.subst (substituteThree x y z)

/-- Six proved raw derivations, not a stamped completeness field. -/
def calculus : InteriorEndpoint.Rules basis where
  squareFinal := derivesSquareFinal
  squareTransfer := derivesSquareTransfer
  squareInitial := derivesSquareInitial
  returnDuplication := derivesReturnDuplication
  interiorIdempotence := derivesInteriorIdempotence
  initialPairRetarget := derivesInitialPairRetarget

/-- The literal Condition16 swap is derived, not imported from a label. -/
theorem derivesInteriorCommutation (before left right after : Word Nat) :
    Derives basis (((before ++ left) ++ right) ++ after)
      (((before ++ right) ++ left) ++ after) :=
  calculus.derivesInteriorCommutation before left right after

theorem derivesSameInteriorContent (before after left right : Word Nat)
    (content : ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList) :
    Derives basis ((before ++ left) ++ after) ((before ++ right) ++ after) :=
  calculus.derivesSameInteriorContent before after left right content

theorem derivesFramedOfEndpointContent
    (first last otherFirst otherLast : Nat) (interior otherInterior : List Nat)
    (content : ∀ letter, letter ∈ interior ↔ letter ∈ otherInterior)
    (initial : first = otherFirst ∨ (first ∈ interior ∧ otherFirst ∈ otherInterior))
    (final : last = otherLast ∨ (last ∈ interior ∧ otherLast ∈ otherInterior)) :
    Derives basis (framedWord first interior last)
      (framedWord otherFirst otherInterior otherLast) :=
  calculus.derivesFramedOfEndpointContent first last otherFirst otherLast interior otherInterior
    content initial final

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2664
