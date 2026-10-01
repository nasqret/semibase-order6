import SemigroupBasis.CoRoots.Order6SporadicSection25Basis

/-! The guarded affine derivation layer used by the Section25 join argument.
The three literal laws are the reversed affine-parity root basis. This module
proves their entire equational closure inside arbitrary matching nonempty
anchors. It does not assume the still-open connected-component comparison. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection25
open SemigroupBasis

def affineLaw00 : Identity Nat := ⟨⟨0,[]⟩,⟨0,[0,0]⟩⟩
def affineLaw01 : Identity Nat := ⟨⟨0,[1,0,0]⟩,⟨0,[1]⟩⟩
def affineLaw02 : Identity Nat := ⟨⟨0,[1,1,0]⟩,⟨0,[1,0,1]⟩⟩
def affineCore : List (Identity Nat) := [affineLaw00,affineLaw01,affineLaw02]

theorem affineCore_length : affineCore.length = 3 := by decide

theorem anchoredTriple (withB0 : Bool) (anchor x : Word Nat)
    (before after : List Nat) :
    ListDerives withB0
      (anchor.toList ++ before ++ x.toList ++ x.toList ++ x.toList ++ after ++ anchor.toList)
      (anchor.toList ++ before ++ x.toList ++ after ++ anchor.toList) := by
  simpa only [List.append_nil, List.nil_append, List.append_assoc] using
    ruleB withB0 anchor x before [] after

theorem anchoredSquareReturn (withB0 : Bool) (anchor x y : Word Nat)
    (before after : List Nat) :
    ListDerives withB0
      (anchor.toList ++ before ++ x.toList ++ y.toList ++ x.toList ++ x.toList ++ after ++ anchor.toList)
      (anchor.toList ++ before ++ x.toList ++ y.toList ++ after ++ anchor.toList) := by
  simpa only [List.append_assoc] using
    ruleB withB0 anchor x before y.toList after

theorem anchoredSwap (withB0 : Bool) (anchor x y : Word Nat)
    (before after : List Nat) :
    ListDerives withB0
      (anchor.toList ++ before ++ x.toList ++ y.toList ++ y.toList ++ x.toList ++ after ++ anchor.toList)
      (anchor.toList ++ before ++ x.toList ++ y.toList ++ x.toList ++ y.toList ++ after ++ anchor.toList) := by
  have core : ListDerives withB0
      (x.toList ++ y.toList ++ y.toList ++ x.toList)
      (x.toList ++ y.toList ++ x.toList ++ y.toList) := by
    simpa only [List.append_nil, List.nil_append, List.append_assoc] using
      (ruleD withB0 x y [] []).symm
  simpa only [List.append_assoc] using
    S5_107.ListDerives.context (anchor.toList ++ before) (after ++ anchor.toList) core

theorem stripAnchorSquares (withB0 : Bool) (anchor : Word Nat)
    (middle : List Nat) :
    ListDerives withB0
      (anchor.toList ++ anchor.toList ++
        (anchor.toList ++ middle ++ anchor.toList) ++ anchor.toList ++ anchor.toList)
      (anchor.toList ++ middle ++ anchor.toList) := by
  have first : ListDerives withB0
      (anchor.toList ++ anchor.toList ++ anchor.toList ++ middle ++
        anchor.toList ++ anchor.toList ++ anchor.toList)
      (anchor.toList ++ middle ++ anchor.toList ++ anchor.toList ++ anchor.toList) := by
    simpa only [List.append_nil, List.nil_append, List.append_assoc] using
      ruleA withB0 anchor [] (middle ++ anchor.toList ++ anchor.toList)
  have second : ListDerives withB0
      (anchor.toList ++ middle ++ anchor.toList ++ anchor.toList ++ anchor.toList)
      (anchor.toList ++ middle ++ anchor.toList) := by
    simpa only [List.append_nil, List.nil_append, List.append_assoc] using
      ruleA withB0 anchor middle []
  simpa only [List.append_assoc] using first.trans second

theorem affineDerives_anchored_subst (withB0 : Bool)
    {left right : Word Nat} (derivation : Derives affineCore left right)
    (substitution : Nat → Word Nat) (anchor : Word Nat) (before after : List Nat) :
    ListDerives withB0
      (anchor.toList ++ before ++ (left.bind substitution).toList ++ after ++ anchor.toList)
      (anchor.toList ++ before ++ (right.bind substitution).toList ++ after ++ anchor.toList) := by
  induction derivation generalizing substitution anchor before after with
  | fromBasis member =>
      simp only [affineCore, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · simp only [Word.toList_bind]
        simpa only [affineLaw00, Word.toList,
          List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.append_assoc] using
          (anchoredTriple withB0 anchor (substitution 0) before after).symm
      · simp only [Word.toList_bind]
        simpa only [affineLaw01, Word.toList,
          List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.append_assoc] using
          anchoredSquareReturn withB0 anchor (substitution 0) (substitution 1) before after
      · simp only [Word.toList_bind]
        simpa only [affineLaw02, Word.toList,
          List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.append_assoc] using
          anchoredSwap withB0 anchor (substitution 0) (substitution 1) before after
  | refl => exact S5_107.ListDerives.refl _
  | symm _ ih => exact (ih substitution anchor before after).symm
  | trans _ _ first second =>
      exact (first substitution anchor before after).trans
        (second substitution anchor before after)
  | prepend pre _ ih =>
      simpa only [Word.toList_bind, Word.toList_append, List.flatMap_append,
        List.append_assoc] using
        ih substitution anchor (before ++ (pre.bind substitution).toList) after
  | appendRight _ post ih =>
      simpa only [Word.toList_bind, Word.toList_append, List.flatMap_append,
        List.append_assoc] using
        ih substitution anchor before ((post.bind substitution).toList ++ after)
  | subst _ replacement ih =>
      simpa only [Word.toList_bind, List.flatMap_assoc] using
        ih (fun letter => (replacement letter).bind substitution) anchor before after

private theorem flatMap_singletons (word : List Nat) :
    word.flatMap (fun letter => [letter]) = word := by
  induction word with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, ih]

theorem affineDerives_anchored (withB0 : Bool)
    {left right : Word Nat} (derivation : Derives affineCore left right)
    (anchor : Word Nat) (before after : List Nat) :
    ListDerives withB0
      (anchor.toList ++ before ++ left.toList ++ after ++ anchor.toList)
      (anchor.toList ++ before ++ right.toList ++ after ++ anchor.toList) := by
  simpa only [Word.toList_bind, Word.toList_singleton, flatMap_singletons] using
    affineDerives_anchored_subst withB0 derivation Word.singleton anchor before after

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.affineCore_length
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.anchoredTriple
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.anchoredSquareReturn
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.anchoredSwap
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.stripAnchorSquares
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.affineDerives_anchored_subst
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.affineDerives_anchored

end SemigroupBasis.CoRoots.Order6SporadicSection25
