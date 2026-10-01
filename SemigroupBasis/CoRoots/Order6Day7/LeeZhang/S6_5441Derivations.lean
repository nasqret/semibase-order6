import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_5441Presentation
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.PrefixTwoEndpointCalculus

/-!
# Three explicit raw11 derivations instantiate the shared calculus

Laws04,05,08 discharge every primitive field for arbitrary nonempty-word
substitutions. The other eight displayed laws remain unchanged in basis.
No finite-basability citation or bounded key is a derivational premise.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_5441

open SemigroupBasis

abbrev framedWord : List Nat → Nat → Nat → Word Nat := PrefixTwoEndpoint.framedWord

private def substituteThree (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

theorem derivesPrefixIdempotence (x y z : Word Nat) :
    Derives basis (((x ++ x) ++ y) ++ z) ((x ++ y) ++ z) := by
  have primitive : Derives basis law04.lhs law04.rhs := Derives.fromBasis (by simp [basis])
  simpa [law04, substituteThree, Word.bind, Word.append, Word.append_assoc] using
    primitive.subst (substituteThree x y z)

theorem derivesTerminalSwitch (x y : Word Nat) :
    Derives basis (((x ++ y) ++ x) ++ x) (((x ++ y) ++ x) ++ y) := by
  have primitive : Derives basis law05.lhs law05.rhs := Derives.fromBasis (by simp [basis])
  simpa [law05, substituteThree, Word.bind, Word.append, Word.append_assoc] using
    primitive.subst (substituteThree x y y)

theorem derivesTerminalSwap (x y : Word Nat) :
    Derives basis (((x ++ y) ++ x) ++ x) (((y ++ x) ++ x) ++ x) := by
  have primitive : Derives basis law08.lhs law08.rhs := Derives.fromBasis (by simp [basis])
  simpa [law08, substituteThree, Word.bind, Word.append, Word.append_assoc] using
    primitive.subst (substituteThree x y y)

def calculus : PrefixTwoEndpoint.Rules basis where
  prefixIdempotence := derivesPrefixIdempotence
  terminalSwitch := derivesTerminalSwitch
  terminalSwap := derivesTerminalSwap

theorem derivesPrefixCommutation (x y penultimate last : Word Nat) :
    Derives basis (((x ++ y) ++ penultimate) ++ last)
      (((y ++ x) ++ penultimate) ++ last) :=
  calculus.derivesPrefixCommutation x y penultimate last

theorem derivesSamePrefixContent (left right penultimate last : Word Nat)
    (content : ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList) :
    Derives basis ((left ++ penultimate) ++ last) ((right ++ penultimate) ++ last) :=
  calculus.derivesSamePrefixContent left right penultimate last content

theorem derivesFramesOfPrefixEndpoint
    (front otherFront : List Nat) (penultimate last otherPenultimate otherLast : Nat)
    (content : ∀ letter, letter ∈ front ↔ letter ∈ otherFront)
    (penultimateKey : penultimate = otherPenultimate ∨
      (penultimate ∈ front ∧ otherPenultimate ∈ otherFront))
    (lastKey : last = otherLast ∨ (penultimate ∈ front ∧ otherPenultimate ∈ otherFront ∧
      last ∈ front ∧ otherLast ∈ otherFront)) :
    Derives basis (framedWord front penultimate last)
      (framedWord otherFront otherPenultimate otherLast) :=
  calculus.derivesFramesOfPrefixEndpoint front otherFront penultimate last otherPenultimate otherLast
    content penultimateKey lastKey

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_5441
