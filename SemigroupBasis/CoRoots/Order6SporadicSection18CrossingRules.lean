import SemigroupBasis.CoRoots.Order6SporadicSection18BlockMerge

/-! The two crossing identities for arbitrary nonempty words and arbitrary
possibly-empty H/K/T lists. Every empty case uses its own actual basis law. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18
open SemigroupBasis

private def replacement (a b c d e : Word Nat) : Nat → Word Nat
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d
  | _ => e

private theorem instantiate (law : Identity Nat) (member : law ∈ basis)
    (a b c d e : Word Nat) :
    ListDerives (law.lhs.bind (replacement a b c d e)).toList
      (law.rhs.bind (replacement a b c d e)).toList :=
  S5_107.ListDerives.ofWord
    (Derives.subst (Derives.fromBasis (e := law) member) (replacement a b c d e))

theorem appendCrossing (a b : Word Nat) (h k t : List Nat) :
    ListDerives (a.toList ++ h ++ b.toList ++ k ++ a.toList ++ t ++ b.toList)
      (a.toList ++ h ++ b.toList ++ k ++ a.toList ++ t ++ b.toList ++ a.toList) := by
  cases h with
  | nil =>
      cases k with
      | nil =>
          cases t with
          | nil =>
              have raw := instantiate law06 (by decide) a b a a a
              simpa [law06,replacement,Word.bind,Word.toList,Word.append,
                S5_107.listWordOfCons,List.append_assoc] using raw
          | cons tHead tTail =>
              have raw := instantiate law07 (by decide) a b (S5_107.listWordOfCons tHead tTail) a a
              simpa [law07,replacement,Word.bind,Word.toList,Word.append,
                S5_107.listWordOfCons,List.append_assoc] using raw
      | cons kHead kTail =>
          cases t with
          | nil =>
              have raw := instantiate law08 (by decide) a b (S5_107.listWordOfCons kHead kTail) a a
              simpa [law08,replacement,Word.bind,Word.toList,Word.append,
                S5_107.listWordOfCons,List.append_assoc] using raw
          | cons tHead tTail =>
              have raw := instantiate law09 (by decide) a b (S5_107.listWordOfCons kHead kTail) (S5_107.listWordOfCons tHead tTail) a
              simpa [law09,replacement,Word.bind,Word.toList,Word.append,
                S5_107.listWordOfCons,List.append_assoc] using raw
  | cons hHead hTail =>
      cases k with
      | nil =>
          cases t with
          | nil =>
              have raw := instantiate law10 (by decide) a (S5_107.listWordOfCons hHead hTail) b a a
              simpa [law10,replacement,Word.bind,Word.toList,Word.append,
                S5_107.listWordOfCons,List.append_assoc] using raw
          | cons tHead tTail =>
              have raw := instantiate law11 (by decide) a (S5_107.listWordOfCons hHead hTail) b (S5_107.listWordOfCons tHead tTail) a
              simpa [law11,replacement,Word.bind,Word.toList,Word.append,
                S5_107.listWordOfCons,List.append_assoc] using raw
      | cons kHead kTail =>
          cases t with
          | nil =>
              have raw := instantiate law12 (by decide) a (S5_107.listWordOfCons hHead hTail) b (S5_107.listWordOfCons kHead kTail) a
              simpa [law12,replacement,Word.bind,Word.toList,Word.append,
                S5_107.listWordOfCons,List.append_assoc] using raw
          | cons tHead tTail =>
              have raw := instantiate law13 (by decide) a (S5_107.listWordOfCons hHead hTail) b (S5_107.listWordOfCons kHead kTail) (S5_107.listWordOfCons tHead tTail)
              simpa [law13,replacement,Word.bind,Word.toList,Word.append,
                S5_107.listWordOfCons,List.append_assoc] using raw

theorem prependCrossing (a b : Word Nat) (h k t : List Nat) :
    ListDerives (a.toList ++ h ++ b.toList ++ k ++ a.toList ++ t ++ b.toList)
      (b.toList ++ a.toList ++ h ++ b.toList ++ k ++ a.toList ++ t ++ b.toList) := by
  cases h with
  | nil =>
      cases k with
      | nil =>
          cases t with
          | nil =>
              have raw := instantiate law14 (by decide) a b a a a
              simpa [law14,replacement,Word.bind,Word.toList,Word.append,
                S5_107.listWordOfCons,List.append_assoc] using raw
          | cons tHead tTail =>
              have raw := instantiate law15 (by decide) a b (S5_107.listWordOfCons tHead tTail) a a
              simpa [law15,replacement,Word.bind,Word.toList,Word.append,
                S5_107.listWordOfCons,List.append_assoc] using raw
      | cons kHead kTail =>
          cases t with
          | nil =>
              have raw := instantiate law16 (by decide) a b (S5_107.listWordOfCons kHead kTail) a a
              simpa [law16,replacement,Word.bind,Word.toList,Word.append,
                S5_107.listWordOfCons,List.append_assoc] using raw
          | cons tHead tTail =>
              have raw := instantiate law17 (by decide) a b (S5_107.listWordOfCons kHead kTail) (S5_107.listWordOfCons tHead tTail) a
              simpa [law17,replacement,Word.bind,Word.toList,Word.append,
                S5_107.listWordOfCons,List.append_assoc] using raw
  | cons hHead hTail =>
      cases k with
      | nil =>
          cases t with
          | nil =>
              have raw := instantiate law18 (by decide) a (S5_107.listWordOfCons hHead hTail) b a a
              simpa [law18,replacement,Word.bind,Word.toList,Word.append,
                S5_107.listWordOfCons,List.append_assoc] using raw
          | cons tHead tTail =>
              have raw := instantiate law19 (by decide) a (S5_107.listWordOfCons hHead hTail) b (S5_107.listWordOfCons tHead tTail) a
              simpa [law19,replacement,Word.bind,Word.toList,Word.append,
                S5_107.listWordOfCons,List.append_assoc] using raw
      | cons kHead kTail =>
          cases t with
          | nil =>
              have raw := instantiate law20 (by decide) a (S5_107.listWordOfCons hHead hTail) b (S5_107.listWordOfCons kHead kTail) a
              simpa [law20,replacement,Word.bind,Word.toList,Word.append,
                S5_107.listWordOfCons,List.append_assoc] using raw
          | cons tHead tTail =>
              have raw := instantiate law21 (by decide) a (S5_107.listWordOfCons hHead hTail) b (S5_107.listWordOfCons kHead kTail) (S5_107.listWordOfCons tHead tTail)
              simpa [law21,replacement,Word.bind,Word.toList,Word.append,
                S5_107.listWordOfCons,List.append_assoc] using raw

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.appendCrossing
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.prependCrossing

end SemigroupBasis.CoRoots.Order6SporadicSection18
