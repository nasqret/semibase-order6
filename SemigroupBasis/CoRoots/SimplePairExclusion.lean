import SemigroupBasis.CoRoots.SimplePairSyntax

/-!
Lee-Zhang2015 Lemma2.10 at n=2, transcribed through its actual padded
substitution. The only algebraic premise is x^4=x^2. Losing a directed
simple-letter factor forces x²yx²zx²=x²yzx². Reverse order is handled by
the paper's second substitution, not by assuming both missed cases have
the same value in the ambient semigroup.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace SemigroupBasis.CoRoots.SimplePairExclusion

open SemigroupBasis

def folded {S : Type u} (G : Semigroup S) (initial : S)
    (valuation : Nat → S) (letters : List Nat) : S :=
  letters.foldl (fun current letter => G.mul current (valuation letter)) initial

theorem folded_nil {S : Type u} (G : Semigroup S) (initial : S) (valuation : Nat → S) :
    folded G initial valuation [] = initial := rfl

theorem folded_cons {S : Type u} (G : Semigroup S) (initial : S)
    (valuation : Nat → S) (letter : Nat) (rest : List Nat) :
    folded G initial valuation (letter :: rest) =
      folded G (G.mul initial (valuation letter)) valuation rest := rfl

theorem folded_append {S : Type u} (G : Semigroup S) (initial : S)
    (valuation : Nat → S) (before after : List Nat) :
    folded G initial valuation (before ++ after) =
      folded G (folded G initial valuation before) valuation after := by
  exact List.foldl_append

theorem folded_mul {S : Type u} (G : Semigroup S) (a b : S)
    (valuation : Nat → S) (letters : List Nat) :
    folded G (G.mul a b) valuation letters = G.mul a (folded G b valuation letters) := by
  induction letters generalizing b with
  | nil => rfl
  | cons letter rest ih =>
      simp only [folded_cons]
      rw [G.assoc]
      exact ih (G.mul b (valuation letter))

def padded {S : Type u} (G : Semigroup S) (e : S)
    (valuation : Nat → S) (letters : List Nat) : S :=
  G.mul (folded G e valuation letters) e

theorem padded_toList {S : Type u} (G : Semigroup S) (e : S)
    (valuation : Nat → S) (word : Word Nat) :
    padded G e valuation word.toList = G.mul (G.mul e (G.eval valuation word)) e := by
  cases word with
  | mk head tail =>
      change G.mul (folded G (G.mul e (valuation head)) valuation tail) e =
        G.mul (G.mul e (folded G (valuation head) valuation tail)) e
      rw [folded_mul]

theorem padded_valid {S : Type u} (G : Semigroup S) (identity : Identity Nat)
    (valid : identity.SatisfiedBy G) (e : S) (valuation : Nat → S) :
    padded G e valuation identity.lhs.toList = padded G e valuation identity.rhs.toList := by
  rw [padded_toList, padded_toList]
  exact congrArg (fun value => G.mul (G.mul e value) e) (valid valuation)

theorem idempotentLeft {S : Type u} (G : Semigroup S) (e : S)
    (idem : G.mul e e = e) (a : S) : G.mul e (G.mul e a) = G.mul e a := by
  rw [← G.assoc, idem]

theorem folded_free_fixed {S : Type u} (G : Semigroup S) (e initial : S)
    (valuation : Nat → S) (letters : List Nat) (fixed : G.mul initial e = initial)
    (constant : ∀ x ∈ letters, valuation x = e) :
    folded G initial valuation letters = initial := by
  induction letters with
  | nil => rfl
  | cons letter rest ih =>
      rw [folded_cons, constant letter (List.Mem.head rest), fixed]
      exact ih (fun x member => constant x (List.Mem.tail letter member))

theorem folded_free_nonempty {S : Type u} (G : Semigroup S) (e initial : S)
    (idem : G.mul e e = e) (valuation : Nat → S) (letters : List Nat)
    (nonempty : letters ≠ []) (constant : ∀ x ∈ letters, valuation x = e) :
    folded G initial valuation letters = G.mul initial e := by
  cases letters with
  | nil => exact False.elim (nonempty rfl)
  | cons letter rest =>
      rw [folded_cons, constant letter (List.Mem.head rest)]
      apply folded_free_fixed G e
      · rw [G.assoc, idem]
      · intro x member
        exact constant x (List.Mem.tail letter member)

theorem finish_free {S : Type u} (G : Semigroup S) (e initial : S)
    (idem : G.mul e e = e) (valuation : Nat → S) (letters : List Nat)
    (constant : ∀ x ∈ letters, valuation x = e) :
    G.mul (folded G initial valuation letters) e = G.mul initial e := by
  by_cases empty : letters = []
  · subst letters; rfl
  · rw [folded_free_nonempty G e initial idem valuation letters empty constant, G.assoc, idem]

theorem padded_pair {S : Type u} (G : Semigroup S) (e : S) (idem : G.mul e e = e)
    (valuation : Nat → S) (first second : Nat) (a b : S)
    (firstValue : valuation first = a) (secondValue : valuation second = b)
    (before middle after : List Nat)
    (beforeFree : ∀ x ∈ before, valuation x = e)
    (middleFree : ∀ x ∈ middle, valuation x = e)
    (afterFree : ∀ x ∈ after, valuation x = e) :
    padded G e valuation (before ++ first :: (middle ++ second :: after)) =
      if middle = [] then G.mul (G.mul (G.mul e a) b) e
      else G.mul (G.mul (G.mul (G.mul e a) e) b) e := by
  unfold padded
  rw [folded_append, folded_free_fixed G e e valuation before idem beforeFree,
      folded_cons, firstValue, folded_append, folded_cons, secondValue,
      finish_free G e _ idem valuation after afterFree]
  by_cases empty : middle = []
  · subst middle; rfl
  · rw [if_neg empty, folded_free_nonempty G e _ idem valuation middle empty middleFree]

def adjacentValue {S : Type u} (G : Semigroup S) (e a b : S) : S :=
  G.mul (G.mul (G.mul e a) b) e

def separatedValue {S : Type u} (G : Semigroup S) (e a b : S) : S :=
  G.mul (G.mul (G.mul (G.mul e a) e) b) e

def paddedValuation {S : Type u} (G : Semigroup S) (e : S)
    (source target : Nat) (a b : S) : Nat → S :=
  directedSimpleAdjacencyValuation source target (G.mul e a) (G.mul b e) e

theorem padded_forward {S : Type u} (G : Semigroup S) (e : S) (idem : G.mul e e = e)
    (source target : Nat) (different : source ≠ target) (a b : S)
    (before middle after : List Nat)
    (beforeFree : PairFree source target before)
    (middleFree : PairFree source target middle)
    (afterFree : PairFree source target after) :
    padded G e (paddedValuation G e source target a b)
      (before ++ source :: (middle ++ target :: after)) =
      if middle = [] then adjacentValue G e a b else separatedValue G e a b := by
  unfold paddedValuation
  rw [padded_pair G e idem _ source target (G.mul e a) (G.mul b e)
    (directedSimpleAdjacencyValuation_source source target _ _ _)
    (directedSimpleAdjacencyValuation_target different _ _ _) before middle after
    (fun x member => directedSimpleAdjacencyValuation_eq_other _ _ _ beforeFree member)
    (fun x member => directedSimpleAdjacencyValuation_eq_other _ _ _ middleFree member)
    (fun x member => directedSimpleAdjacencyValuation_eq_other _ _ _ afterFree member)]
  split <;> simp_all only [adjacentValue, separatedValue, G.assoc, idem, idempotentLeft G e idem]

theorem padded_reverse {S : Type u} (G : Semigroup S) (e : S) (idem : G.mul e e = e)
    (source target : Nat) (different : source ≠ target) (a b : S)
    (before middle after : List Nat)
    (beforeFree : PairFree source target before)
    (middleFree : PairFree source target middle)
    (afterFree : PairFree source target after) :
    padded G e (paddedValuation G e source target a b)
      (before ++ target :: (middle ++ source :: after)) = separatedValue G e b a := by
  unfold paddedValuation
  rw [padded_pair G e idem _ target source (G.mul b e) (G.mul e a)
    (directedSimpleAdjacencyValuation_target different _ _ _)
    (directedSimpleAdjacencyValuation_source source target _ _ _) before middle after
    (fun x member => directedSimpleAdjacencyValuation_eq_other _ _ _ beforeFree member)
    (fun x member => directedSimpleAdjacencyValuation_eq_other _ _ _ middleFree member)
    (fun x member => directedSimpleAdjacencyValuation_eq_other _ _ _ afterFree member)]
  split <;> simp only [separatedValue, G.assoc, idem, idempotentLeft G e idem]

/-- The paper's second substitution converts a reversed padded comparison
to the same separated-versus-adjacent identity. -/
theorem exclusion_of_reverse {S : Type u} (G : Semigroup S) (e : S)
    (idem : G.mul e e = e)
    (reverse : ∀ a b, adjacentValue G e a b = separatedValue G e b a) :
    ∀ a b, separatedValue G e a b = adjacentValue G e a b := by
  intro a b
  symm
  calc
    adjacentValue G e a b = separatedValue G e b a := reverse a b
    _ = adjacentValue G e b (G.mul e a) := by
      simp only [separatedValue, adjacentValue, G.assoc]
    _ = separatedValue G e (G.mul e a) b := reverse b (G.mul e a)
    _ = separatedValue G e a b := by
      simp only [separatedValue, G.assoc, idempotentLeft G e idem]

/-- Lemma2.10's actual loss-of-FSS implication, specialized only to n=2.
Both distinguished variables are required to be globally simple on both
sides; no ambient first/last-order premise is inserted. -/
theorem exclusion_of_adjacency_loss {S : Type u} (G : Semigroup S)
    (squares : ∀ a, G.mul (G.mul a a) (G.mul a a) = G.mul a a)
    (identity : Identity Nat) (valid : identity.SatisfiedBy G)
    (source target : Nat) (different : source ≠ target)
    (leftSource : identity.lhs.toList.count source = 1)
    (leftTarget : identity.lhs.toList.count target = 1)
    (rightSource : identity.rhs.toList.count source = 1)
    (rightTarget : identity.rhs.toList.count target = 1)
    (leftAdjacent : (source,target) ∈ identity.lhs.adjacentPairs)
    (rightNotAdjacent : (source,target) ∉ identity.rhs.adjacentPairs) :
    ∀ x a b, separatedValue G (G.mul x x) a b = adjacentValue G (G.mul x x) a b := by
  obtain ⟨before, after, splitLeft⟩ :=
    (mem_adjacentPairs_iff_exists_split source target identity.lhs).mp leftAdjacent
  have leftFree := pairFree_ends_of_adjacent_split different
    (by rw [← splitLeft]; exact leftSource) (by rw [← splitLeft]; exact leftTarget)
  intro x
  let e := G.mul x x
  have idem : G.mul e e = e := squares x
  have lhsValue (a b : S) :
      padded G e (paddedValuation G e source target a b) identity.lhs.toList = adjacentValue G e a b := by
    rw [splitLeft]
    simpa only [List.nil_append, if_pos rfl] using
      padded_forward G e idem source target different a b before [] after
        leftFree.1 ⟨by simp, by simp⟩ leftFree.2
  obtain forward | reverse := simplePair_order_cases different rightSource rightTarget
  · obtain ⟨beforeR, middleR, afterR, splitRight⟩ := forward
    have rightFree := pairFree_parts_of_simple_split different
      (by rw [← splitRight]; exact rightSource) (by rw [← splitRight]; exact rightTarget)
    have nonempty : middleR ≠ [] := by
      intro empty
      apply rightNotAdjacent
      apply (mem_adjacentPairs_iff_exists_split source target identity.rhs).mpr
      exact ⟨beforeR, afterR, by simpa only [empty, List.nil_append] using splitRight⟩
    intro a b
    have equal := padded_valid G identity valid e (paddedValuation G e source target a b)
    rw [lhsValue a b, splitRight,
      padded_forward G e idem source target different a b beforeR middleR afterR
        rightFree.1 rightFree.2.1 rightFree.2.2, if_neg nonempty] at equal
    exact equal.symm
  · obtain ⟨beforeR, middleR, afterR, splitRight⟩ := reverse
    have rightFree := pairFree_parts_of_simple_split (Ne.symm different)
      (by rw [← splitRight]; exact rightTarget) (by rw [← splitRight]; exact rightSource)
    apply exclusion_of_reverse G e idem
    intro a b
    have equal := padded_valid G identity valid e (paddedValuation G e source target a b)
    rw [lhsValue a b, splitRight,
      padded_reverse G e idem source target different a b beforeR middleR afterR
        (pairFree_symm rightFree.1) (pairFree_symm rightFree.2.1) (pairFree_symm rightFree.2.2)] at equal
    exact equal

#print axioms padded_forward
#print axioms padded_reverse
#print axioms exclusion_of_reverse
#print axioms exclusion_of_adjacency_loss

end SemigroupBasis.CoRoots.SimplePairExclusion
