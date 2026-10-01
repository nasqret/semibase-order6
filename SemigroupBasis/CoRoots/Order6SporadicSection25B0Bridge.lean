import SemigroupBasis.CoRoots.Order6SporadicSection25Basis

/-! The additional B0 rule, used through a fully typed bridge-collapse
chain. No connectivity or factor completeness is assumed by this lemma. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection25
open SemigroupBasis

theorem ruleE (x y : Word Nat) :
    ListDerives true
      (x.toList ++ x.toList ++ y.toList ++ y.toList ++
        x.toList ++ x.toList ++ y.toList ++ y.toList)
      (x.toList ++ x.toList ++ y.toList ++ y.toList) := by
  let substitution : Nat → Word Nat
    | 0 => x
    | _ => y
  have core : Derives (basis true) law24.lhs law24.rhs :=
    Derives.fromBasis (e := law24) (by decide)
  have instantiatedStep := S5_107.ListDerives.ofWord (Derives.subst core substitution)
  have converted : ListDerives true
      (law24.lhs.toList.flatMap (fun a => (substitution a).toList))
      (law24.rhs.toList.flatMap (fun a => (substitution a).toList)) := by
    simpa only [Word.toList_bind] using instantiatedStep
  simpa only [law24, Word.toList, substitution, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.cons_append, List.nil_append, List.append_assoc] using converted

theorem B0_bridgeCollapse (a b c d : List Nat) (tail head : Nat) :
    ListDerives true
      (a ++ [tail] ++ b ++ [tail] ++ [head,head,tail,tail] ++ [head] ++ c ++ [head] ++ d)
      (a ++ [tail] ++ b ++ [tail] ++ [head] ++ c ++ [head] ++ d) := by
  let left : List Nat := a ++ [tail] ++ b ++ [tail]
  let right : List Nat := [head] ++ c ++ [head] ++ d
  have insertTail : ListDerives true
      (left ++ [head,head,tail,tail] ++ right)
      (left ++ [tail,tail,head,head,tail,tail] ++ right) := by
    simpa only [left, Word.toList_singleton, List.append_nil, List.nil_append,
      List.cons_append, List.append_assoc] using
      S5_107.ListDerives.context a ([head,head,tail,tail] ++ right)
        (ruleA true (Word.singleton tail) b []).symm
  have insertHead : ListDerives true
      (left ++ [tail,tail,head,head,tail,tail] ++ right)
      (left ++ [tail,tail,head,head,tail,tail,head,head] ++ right) := by
    simpa only [right, Word.toList_singleton, List.append_nil, List.nil_append,
      List.cons_append, List.append_assoc] using
      S5_107.ListDerives.context (left ++ [tail,tail]) d
        (ruleA true (Word.singleton head) [head,tail,tail] ([head] ++ c)).symm
  have collapse : ListDerives true
      (left ++ [tail,tail,head,head,tail,tail,head,head] ++ right)
      (left ++ [tail,tail,head,head] ++ right) := by
    simpa only [Word.toList_singleton, List.append_nil, List.nil_append,
      List.cons_append, List.append_assoc] using
      S5_107.ListDerives.context left right
        (ruleE (Word.singleton tail) (Word.singleton head))
  have removeTail : ListDerives true
      (left ++ [tail,tail,head,head] ++ right)
      (left ++ [head,head] ++ right) := by
    simpa only [left, Word.toList_singleton, List.append_nil, List.nil_append,
      List.cons_append, List.append_assoc] using
      S5_107.ListDerives.context a ([head,head] ++ right)
        (ruleA true (Word.singleton tail) b [])
  have removeHead : ListDerives true
      (left ++ [head,head] ++ right) (left ++ right) := by
    simpa only [right, Word.toList_singleton, List.append_nil, List.nil_append,
      List.cons_append, List.append_assoc] using
      S5_107.ListDerives.context left d (ruleA true (Word.singleton head) [] c)
  simpa only [left, right, List.append_assoc] using
    insertTail.trans (insertHead.trans (collapse.trans (removeTail.trans removeHead)))

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.ruleE
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.B0_bridgeCollapse

end SemigroupBasis.CoRoots.Order6SporadicSection25
