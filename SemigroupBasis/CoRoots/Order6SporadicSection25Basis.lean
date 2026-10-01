import SemigroupBasis.CoRoots.S5_107ListDerives

/-! Section25's exact expanded published laws and their optional-context
instances. Every substituted semigroup word is explicitly nonempty.
The 24-law core is Prop25.2; the 25th law extends it to Prop25.5.
No completeness or semantic assumption is introduced here. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection25
open SemigroupBasis

def law00 : Identity Nat := ⟨⟨0,[0,0,0]⟩,⟨0,[0]⟩⟩
def law01 : Identity Nat := ⟨⟨0,[0,0,1,0]⟩,⟨0,[1,0]⟩⟩
def law02 : Identity Nat := ⟨⟨0,[1,0,0,0]⟩,⟨0,[1,0]⟩⟩
def law03 : Identity Nat := ⟨⟨0,[1,0,0,2,0]⟩,⟨0,[1,2,0]⟩⟩
def law04 : Identity Nat := ⟨⟨0,[1,1,1,0]⟩,⟨0,[1,0]⟩⟩
def law05 : Identity Nat := ⟨⟨0,[1,1,1,2,0]⟩,⟨0,[1,2,0]⟩⟩
def law06 : Identity Nat := ⟨⟨0,[1,2,1,1,0]⟩,⟨0,[1,2,0]⟩⟩
def law07 : Identity Nat := ⟨⟨0,[1,2,1,1,3,0]⟩,⟨0,[1,2,3,0]⟩⟩
def law08 : Identity Nat := ⟨⟨0,[1,2,2,2,0]⟩,⟨0,[1,2,0]⟩⟩
def law09 : Identity Nat := ⟨⟨0,[1,2,2,2,3,0]⟩,⟨0,[1,2,3,0]⟩⟩
def law10 : Identity Nat := ⟨⟨0,[1,2,3,2,2,0]⟩,⟨0,[1,2,3,0]⟩⟩
def law11 : Identity Nat := ⟨⟨0,[1,2,3,2,2,4,0]⟩,⟨0,[1,2,3,4,0]⟩⟩
def law12 : Identity Nat := ⟨⟨0,[1,0,0,1]⟩,⟨0,[1,1,0,0]⟩⟩
def law13 : Identity Nat := ⟨⟨0,[1,0,0,2,1]⟩,⟨0,[1,2,1,0,0]⟩⟩
def law14 : Identity Nat := ⟨⟨0,[1,2,0,0,1]⟩,⟨0,[1,2,1,0,0]⟩⟩
def law15 : Identity Nat := ⟨⟨0,[1,2,0,0,3,1]⟩,⟨0,[1,2,3,1,0,0]⟩⟩
def law16 : Identity Nat := ⟨⟨0,[1,2,0,0,2]⟩,⟨0,[1,2,2,0,0]⟩⟩
def law17 : Identity Nat := ⟨⟨0,[1,2,0,0,3,2]⟩,⟨0,[1,2,3,2,0,0]⟩⟩
def law18 : Identity Nat := ⟨⟨0,[1,2,3,0,0,2]⟩,⟨0,[1,2,3,2,0,0]⟩⟩
def law19 : Identity Nat := ⟨⟨0,[1,2,3,0,0,4,2]⟩,⟨0,[1,2,3,4,2,0,0]⟩⟩
def law20 : Identity Nat := ⟨⟨0,[1,0,1]⟩,⟨0,[1,1,0]⟩⟩
def law21 : Identity Nat := ⟨⟨0,[1,2,0,1]⟩,⟨0,[1,2,1,0]⟩⟩
def law22 : Identity Nat := ⟨⟨0,[1,2,0,2]⟩,⟨0,[1,2,2,0]⟩⟩
def law23 : Identity Nat := ⟨⟨0,[1,2,3,0,2]⟩,⟨0,[1,2,3,2,0]⟩⟩
def law24 : Identity Nat := ⟨⟨0,[0,1,1,0,0,1,1]⟩,⟨0,[0,1,1]⟩⟩

def coreBasis : List (Identity Nat) :=
  [law00,law01,law02,law03,law04,law05,law06,law07,law08,law09,law10,law11,law12,law13,law14,law15,law16,law17,law18,law19,law20,law21,law22,law23]

def basis (withB0 : Bool) : List (Identity Nat) :=
  if withB0 then coreBasis ++ [law24] else coreBasis

abbrev ListDerives (withB0 : Bool) := S5_107.ListDerives (basis withB0)

theorem coreBasis_length : coreBasis.length = 24 := by decide
theorem basis_false_length : (basis false).length = 24 := by decide
theorem basis_true_length : (basis true).length = 25 := by decide

theorem coreMember (withB0 : Bool) {law : Identity Nat}
    (member : law ∈ coreBasis) : law ∈ basis withB0 := by
  cases withB0 with
  | false => exact member
  | true => exact List.mem_append_left _ member

private def substitutionFive (a b c d e : Word Nat) : Nat → Word Nat
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d
  | 4 => e
  | n + 5 => Word.singleton (n + 5)

private theorem instantiated (withB0 : Bool) (law : Identity Nat)
    (member : law ∈ coreBasis) (substitution : Nat → Word Nat) :
    ListDerives withB0 (law.lhs.toList.flatMap (fun a => (substitution a).toList))
      (law.rhs.toList.flatMap (fun a => (substitution a).toList)) := by
  have step : Derives (basis withB0) (law.lhs.bind substitution)
      (law.rhs.bind substitution) :=
    Derives.subst (Derives.fromBasis (e := law) (coreMember withB0 member)) substitution
  have converted := S5_107.ListDerives.ofWord step
  simpa only [Word.toList_bind] using converted

theorem ruleA (withB0 : Bool) (x : Word Nat)
    (h k : List Nat) :
    ListDerives withB0 (x.toList ++ h ++ x.toList ++ x.toList ++ k ++ x.toList)
      (x.toList ++ h ++ k ++ x.toList) := by
  cases h with
  | nil =>
      cases k with
      | nil =>
          simpa only [law00, Word.toList,
            substitutionFive, List.flatMap_cons, List.flatMap_nil,
            List.append_nil, List.nil_append, List.cons_append,
            List.append_assoc] using
            instantiated withB0 law00 (by decide)
              (substitutionFive x x x x x)
      | cons kHead kTail =>
          simpa only [law01, Word.toList,
            substitutionFive, List.flatMap_cons, List.flatMap_nil,
            List.append_nil, List.nil_append, List.cons_append,
            List.append_assoc] using
            instantiated withB0 law01 (by decide)
              (substitutionFive x ⟨kHead,kTail⟩ x x x)
  | cons hHead hTail =>
      cases k with
      | nil =>
          simpa only [law02, Word.toList,
            substitutionFive, List.flatMap_cons, List.flatMap_nil,
            List.append_nil, List.nil_append, List.cons_append,
            List.append_assoc] using
            instantiated withB0 law02 (by decide)
              (substitutionFive x ⟨hHead,hTail⟩ x x x)
      | cons kHead kTail =>
          simpa only [law03, Word.toList,
            substitutionFive, List.flatMap_cons, List.flatMap_nil,
            List.append_nil, List.nil_append, List.cons_append,
            List.append_assoc] using
            instantiated withB0 law03 (by decide)
              (substitutionFive x ⟨hHead,hTail⟩ ⟨kHead,kTail⟩ x x)

theorem ruleB (withB0 : Bool) (x : Word Nat) (y : Word Nat)
    (h k t : List Nat) :
    ListDerives withB0 (x.toList ++ h ++ y.toList ++ k ++ y.toList ++ y.toList ++ t ++ x.toList)
      (x.toList ++ h ++ y.toList ++ k ++ t ++ x.toList) := by
  cases h with
  | nil =>
      cases k with
      | nil =>
          cases t with
          | nil =>
              simpa only [law04, Word.toList,
                substitutionFive, List.flatMap_cons, List.flatMap_nil,
                List.append_nil, List.nil_append, List.cons_append,
                List.append_assoc] using
                instantiated withB0 law04 (by decide)
                  (substitutionFive x y x x x)
          | cons tHead tTail =>
              simpa only [law05, Word.toList,
                substitutionFive, List.flatMap_cons, List.flatMap_nil,
                List.append_nil, List.nil_append, List.cons_append,
                List.append_assoc] using
                instantiated withB0 law05 (by decide)
                  (substitutionFive x y ⟨tHead,tTail⟩ x x)
      | cons kHead kTail =>
          cases t with
          | nil =>
              simpa only [law06, Word.toList,
                substitutionFive, List.flatMap_cons, List.flatMap_nil,
                List.append_nil, List.nil_append, List.cons_append,
                List.append_assoc] using
                instantiated withB0 law06 (by decide)
                  (substitutionFive x y ⟨kHead,kTail⟩ x x)
          | cons tHead tTail =>
              simpa only [law07, Word.toList,
                substitutionFive, List.flatMap_cons, List.flatMap_nil,
                List.append_nil, List.nil_append, List.cons_append,
                List.append_assoc] using
                instantiated withB0 law07 (by decide)
                  (substitutionFive x y ⟨kHead,kTail⟩ ⟨tHead,tTail⟩ x)
  | cons hHead hTail =>
      cases k with
      | nil =>
          cases t with
          | nil =>
              simpa only [law08, Word.toList,
                substitutionFive, List.flatMap_cons, List.flatMap_nil,
                List.append_nil, List.nil_append, List.cons_append,
                List.append_assoc] using
                instantiated withB0 law08 (by decide)
                  (substitutionFive x ⟨hHead,hTail⟩ y x x)
          | cons tHead tTail =>
              simpa only [law09, Word.toList,
                substitutionFive, List.flatMap_cons, List.flatMap_nil,
                List.append_nil, List.nil_append, List.cons_append,
                List.append_assoc] using
                instantiated withB0 law09 (by decide)
                  (substitutionFive x ⟨hHead,hTail⟩ y ⟨tHead,tTail⟩ x)
      | cons kHead kTail =>
          cases t with
          | nil =>
              simpa only [law10, Word.toList,
                substitutionFive, List.flatMap_cons, List.flatMap_nil,
                List.append_nil, List.nil_append, List.cons_append,
                List.append_assoc] using
                instantiated withB0 law10 (by decide)
                  (substitutionFive x ⟨hHead,hTail⟩ y ⟨kHead,kTail⟩ x)
          | cons tHead tTail =>
              simpa only [law11, Word.toList,
                substitutionFive, List.flatMap_cons, List.flatMap_nil,
                List.append_nil, List.nil_append, List.cons_append,
                List.append_assoc] using
                instantiated withB0 law11 (by decide)
                  (substitutionFive x ⟨hHead,hTail⟩ y ⟨kHead,kTail⟩ ⟨tHead,tTail⟩)

theorem ruleC (withB0 : Bool) (x : Word Nat) (y : Word Nat)
    (h k t : List Nat) :
    ListDerives withB0 (x.toList ++ h ++ y.toList ++ k ++ x.toList ++ x.toList ++ t ++ y.toList)
      (x.toList ++ h ++ y.toList ++ k ++ t ++ y.toList ++ x.toList ++ x.toList) := by
  cases h with
  | nil =>
      cases k with
      | nil =>
          cases t with
          | nil =>
              simpa only [law12, Word.toList,
                substitutionFive, List.flatMap_cons, List.flatMap_nil,
                List.append_nil, List.nil_append, List.cons_append,
                List.append_assoc] using
                instantiated withB0 law12 (by decide)
                  (substitutionFive x y x x x)
          | cons tHead tTail =>
              simpa only [law13, Word.toList,
                substitutionFive, List.flatMap_cons, List.flatMap_nil,
                List.append_nil, List.nil_append, List.cons_append,
                List.append_assoc] using
                instantiated withB0 law13 (by decide)
                  (substitutionFive x y ⟨tHead,tTail⟩ x x)
      | cons kHead kTail =>
          cases t with
          | nil =>
              simpa only [law14, Word.toList,
                substitutionFive, List.flatMap_cons, List.flatMap_nil,
                List.append_nil, List.nil_append, List.cons_append,
                List.append_assoc] using
                instantiated withB0 law14 (by decide)
                  (substitutionFive x y ⟨kHead,kTail⟩ x x)
          | cons tHead tTail =>
              simpa only [law15, Word.toList,
                substitutionFive, List.flatMap_cons, List.flatMap_nil,
                List.append_nil, List.nil_append, List.cons_append,
                List.append_assoc] using
                instantiated withB0 law15 (by decide)
                  (substitutionFive x y ⟨kHead,kTail⟩ ⟨tHead,tTail⟩ x)
  | cons hHead hTail =>
      cases k with
      | nil =>
          cases t with
          | nil =>
              simpa only [law16, Word.toList,
                substitutionFive, List.flatMap_cons, List.flatMap_nil,
                List.append_nil, List.nil_append, List.cons_append,
                List.append_assoc] using
                instantiated withB0 law16 (by decide)
                  (substitutionFive x ⟨hHead,hTail⟩ y x x)
          | cons tHead tTail =>
              simpa only [law17, Word.toList,
                substitutionFive, List.flatMap_cons, List.flatMap_nil,
                List.append_nil, List.nil_append, List.cons_append,
                List.append_assoc] using
                instantiated withB0 law17 (by decide)
                  (substitutionFive x ⟨hHead,hTail⟩ y ⟨tHead,tTail⟩ x)
      | cons kHead kTail =>
          cases t with
          | nil =>
              simpa only [law18, Word.toList,
                substitutionFive, List.flatMap_cons, List.flatMap_nil,
                List.append_nil, List.nil_append, List.cons_append,
                List.append_assoc] using
                instantiated withB0 law18 (by decide)
                  (substitutionFive x ⟨hHead,hTail⟩ y ⟨kHead,kTail⟩ x)
          | cons tHead tTail =>
              simpa only [law19, Word.toList,
                substitutionFive, List.flatMap_cons, List.flatMap_nil,
                List.append_nil, List.nil_append, List.cons_append,
                List.append_assoc] using
                instantiated withB0 law19 (by decide)
                  (substitutionFive x ⟨hHead,hTail⟩ y ⟨kHead,kTail⟩ ⟨tHead,tTail⟩)

theorem ruleD (withB0 : Bool) (x : Word Nat) (y : Word Nat)
    (h k : List Nat) :
    ListDerives withB0 (x.toList ++ h ++ y.toList ++ k ++ x.toList ++ y.toList)
      (x.toList ++ h ++ y.toList ++ k ++ y.toList ++ x.toList) := by
  cases h with
  | nil =>
      cases k with
      | nil =>
          simpa only [law20, Word.toList,
            substitutionFive, List.flatMap_cons, List.flatMap_nil,
            List.append_nil, List.nil_append, List.cons_append,
            List.append_assoc] using
            instantiated withB0 law20 (by decide)
              (substitutionFive x y x x x)
      | cons kHead kTail =>
          simpa only [law21, Word.toList,
            substitutionFive, List.flatMap_cons, List.flatMap_nil,
            List.append_nil, List.nil_append, List.cons_append,
            List.append_assoc] using
            instantiated withB0 law21 (by decide)
              (substitutionFive x y ⟨kHead,kTail⟩ x x)
  | cons hHead hTail =>
      cases k with
      | nil =>
          simpa only [law22, Word.toList,
            substitutionFive, List.flatMap_cons, List.flatMap_nil,
            List.append_nil, List.nil_append, List.cons_append,
            List.append_assoc] using
            instantiated withB0 law22 (by decide)
              (substitutionFive x ⟨hHead,hTail⟩ y x x)
      | cons kHead kTail =>
          simpa only [law23, Word.toList,
            substitutionFive, List.flatMap_cons, List.flatMap_nil,
            List.append_nil, List.nil_append, List.cons_append,
            List.append_assoc] using
            instantiated withB0 law23 (by decide)
              (substitutionFive x ⟨hHead,hTail⟩ y ⟨kHead,kTail⟩ x)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.coreBasis_length
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.basis_false_length
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.basis_true_length
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.coreMember
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.ruleA
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.ruleB
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.ruleC
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.ruleD

end SemigroupBasis.CoRoots.Order6SporadicSection25
