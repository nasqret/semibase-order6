import SemigroupBasis.CoRoots.Order6SporadicSection22E7Ini

/-! Source-bound E7 observations used on paper p99. A next fresh letter
is sent to6; the terminal guard handles the final-block boundary. The
{4,5} probe reads the last old letter, and the2 probe distinguishes an
empty tail from the current first letter repeated once. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection22.E7
open SemigroupBasis

def run (valuation : Nat → Fin 6) (acc : Fin 6) (letters : List Nat) : Fin 6 :=
  letters.foldl (fun current x => tableMul current (valuation x)) acc

theorem run_nil (valuation : Nat → Fin 6) (acc : Fin 6) : run valuation acc [] = acc := rfl
theorem run_cons (valuation : Nat → Fin 6) (acc : Fin 6) (x : Nat) (xs : List Nat) :
    run valuation acc (x :: xs) = run valuation (tableMul acc (valuation x)) xs := rfl
theorem run_append (valuation : Nat → Fin 6) (acc : Fin 6) (xs ys : List Nat) :
    run valuation acc (xs ++ ys) = run valuation (run valuation acc xs) ys := by
  exact List.foldl_append

def sandwich (valuation : Nat → Fin 6) (letters : List Nat) : Fin 6 :=
  tableMul (run valuation 3 letters) 5

theorem zeroRow (a : Fin 6) : tableMul 0 a = 0 := by revert a; decide
theorem twoRow (a : Fin 6) : tableMul 2 a = 2 := by revert a; decide
theorem rightZero35 (a b : Fin 6) (ha : a = 3 ∨ a = 4) (hb : b = 3 ∨ b = 4) :
    tableMul a b = b := by revert a b; decide
theorem rightFive (a : Fin 6) (ha : a ≠ 5) : tableMul a 5 = 0 ∨ tableMul a 5 = 2 := by
  revert a; decide

theorem run_absorbing (valuation : Nat → Fin 6) (letters : List Nat) (acc : Fin 6)
    (absorbs : acc = 0 ∨ acc = 2) : run valuation acc letters = acc := by
  induction letters with
  | nil => rfl
  | cons x xs ih =>
      rcases absorbs with rfl | rfl
      · rw [run_cons,zeroRow]
        exact ih
      · rw [run_cons,twoRow]
        exact ih

def ReadySuffix (valuation : Nat → Fin 6) : List Nat → Prop
  | [] => True
  | x :: _ => valuation x = 5

theorem finish_suffix (valuation : Nat → Fin 6) (suffix : List Nat)
    (ready : ReadySuffix valuation suffix) (acc : Fin 6) (notFive : acc ≠ 5) :
    tableMul (run valuation acc suffix) 5 = tableMul acc 5 := by
  cases suffix with
  | nil => rfl
  | cons x xs =>
      have starts : valuation x = 5 := ready
      rw [run_cons,starts,run_absorbing valuation xs _ (rightFive acc notFive)]
      rcases rightFive acc notFive with equal | equal
      · rw [equal,zeroRow]
      · rw [equal,twoRow]

theorem run35 (valuation : Nat → Fin 6) (letters : List Nat)
    (bounded : ∀ x ∈ letters, valuation x = 3 ∨ valuation x = 4)
    (acc : Fin 6) (initial : acc = 3 ∨ acc = 4) :
    run valuation acc letters = 3 ∨ run valuation acc letters = 4 := by
  induction letters generalizing acc with
  | nil => exact initial
  | cons x xs ih =>
      have current := bounded x (by simp)
      rw [run_cons,rightZero35 acc (valuation x) initial current]
      exact ih (fun y member => bounded y (List.mem_cons_of_mem x member)) _ current

theorem run_all_three (valuation : Nat → Fin 6) (letters : List Nat)
    (constant : ∀ x ∈ letters, valuation x = 3) : run valuation 3 letters = 3 := by
  induction letters with
  | nil => rfl
  | cons x xs ih =>
      rw [run_cons,constant x (by simp),show tableMul 3 3 = 3 by decide]
      exact ih (fun y member => constant y (List.mem_cons_of_mem x member))

theorem sandwich_last (valuation : Nat → Fin 6) (stem : List Nat) (last : Nat)
    (suffix : List Nat) (bounded : ∀ x ∈ stem, valuation x = 3 ∨ valuation x = 4)
    (lastBound : valuation last = 3 ∨ valuation last = 4)
    (ready : ReadySuffix valuation suffix) :
    sandwich valuation (stem ++ [last] ++ suffix) = tableMul (valuation last) 5 := by
  have prefixBound := run35 valuation stem bounded 3 (Or.inl rfl)
  have lastNotFive : valuation last ≠ 5 := by rcases lastBound with equal | equal <;> simp [equal]
  unfold sandwich
  rw [run_append,run_append,run_cons,run_nil,
    rightZero35 _ _ prefixBound lastBound]
  exact finish_suffix valuation suffix ready (valuation last) lastNotFive

def markerVal (mark : Nat) (stop : Option Nat) (value : Fin 6) (x : Nat) : Fin 6 :=
  if x = mark then value else if stop = some x then 5 else 3

theorem markerVal_mark (mark : Nat) (stop : Option Nat) (value : Fin 6) :
    markerVal mark stop value mark = value := by simp [markerVal]

theorem markerVal35 (mark : Nat) (stop : Option Nat) (x : Nat)
    (notStop : stop ≠ some x) :
    markerVal mark stop 4 x = 3 ∨ markerVal mark stop 4 x = 4 := by
  by_cases same : x = mark <;> simp [markerVal,same,notStop]

theorem sandwich_marker_last (stem : List Nat) (last : Nat) (suffix : List Nat)
    (mark : Nat) (stop : Option Nat)
    (noStop : ∀ x ∈ stem, stop ≠ some x) (lastNoStop : stop ≠ some last)
    (ready : ReadySuffix (markerVal mark stop 4) suffix) :
    sandwich (markerVal mark stop 4) (stem ++ [last] ++ suffix) =
      if last = mark then 2 else 0 := by
  rw [sandwich_last _ _ _ _ (fun x member => markerVal35 mark stop x (noStop x member))
    (markerVal35 mark stop last lastNoStop) ready]
  by_cases same : last = mark <;> simp [markerVal,same,lastNoStop,tableMul]

theorem sandwich_marker_power (stem suffix : List Nat) (mark : Nat) (stop : Option Nat)
    (noMark : ∀ x ∈ stem, x ≠ mark) (noStop : ∀ x ∈ stem, stop ≠ some x)
    (ready : ReadySuffix (markerVal mark stop 1) suffix) :
    sandwich (markerVal mark stop 1) (stem ++ [mark] ++ suffix) = 2 ∧
    sandwich (markerVal mark stop 1) (stem ++ [mark,mark] ++ suffix) = 0 := by
  have prefixRun : run (markerVal mark stop 1) 3 stem = 3 :=
    run_all_three _ stem (fun x member => by simp [markerVal,noMark x member,noStop x member])
  have one := finish_suffix (markerVal mark stop 1) suffix ready 1 (by decide)
  have zero := finish_suffix (markerVal mark stop 1) suffix ready 0 (by decide)
  constructor
  · simpa only [sandwich,run_append,run_cons,run_nil,prefixRun,markerVal_mark,
      show tableMul 3 1 = 1 by decide,show tableMul 1 5 = 2 by decide] using one
  · simpa only [sandwich,run_append,run_cons,run_nil,prefixRun,markerVal_mark,
      show tableMul 3 1 = 1 by decide,show tableMul 1 1 = 0 by decide,
      show tableMul 0 5 = 0 by decide] using zero

def nextLetter : List CanonicalBlock → Option Nat
  | [] => none
  | first :: _ => some first.letter

theorem nextLetter_eq_of_labels {left right : List CanonicalBlock}
    (labels : left.map CanonicalBlock.letter = right.map CanonicalBlock.letter) :
    nextLetter left = nextLetter right := by
  cases left <;> cases right <;> simp_all [nextLetter]

theorem nextLetter_fresh (seen : List Nat) (blocks : List CanonicalBlock)
    (good : WellFormed seen blocks) (x : Nat) (member : x ∈ seen) : nextLetter blocks ≠ some x := by
  cases blocks with
  | nil => simp [nextLetter]
  | cons first rest =>
      intro equal
      have same : first.letter = x := Option.some.inj equal
      exact good.1 (by simpa [same] using member)

theorem marker_ready (blocks : List CanonicalBlock) (mark : Nat) (value : Fin 6)
    (different : nextLetter blocks ≠ some mark) :
    ReadySuffix (markerVal mark (nextLetter blocks) value) (renderBlocks blocks) := by
  cases blocks with
  | nil => trivial
  | cons first rest =>
      have notMark : first.letter ≠ mark := by
        intro same
        exact different (by simp [nextLetter,same])
      simp [ReadySuffix,renderBlocks,markerVal,nextLetter,notMark]

theorem run_mul (valuation : Nat → Fin 6) (letters : List Nat) (a b : Fin 6) :
    run valuation (tableMul a b) letters = tableMul a (run valuation b letters) := by
  induction letters generalizing b with
  | nil => rfl
  | cons x xs ih =>
      have associated : tableMul (tableMul a b) (valuation x) =
          tableMul a (tableMul b (valuation x)) := table.assoc a b (valuation x)
      rw [run_cons,associated,run_cons]
      exact ih _

theorem sandwich_valid (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup)
    (valuation : Nat → Fin 6) :
    sandwich valuation identity.lhs.toList = sandwich valuation identity.rhs.toList := by
  have boundary (word : Word Nat) :
      run valuation 3 word.toList = tableMul 3 (table.semigroup.eval valuation word) := by
    cases word with
    | mk head tail => exact run_mul valuation tail 3 (valuation head)
  unfold sandwich
  rw [boundary,boundary,valid valuation]

#print axioms finish_suffix
#print axioms sandwich_last
#print axioms sandwich_marker_last
#print axioms sandwich_marker_power
#print axioms nextLetter_fresh
#print axioms marker_ready
#print axioms sandwich_valid

end SemigroupBasis.CoRoots.Order6SporadicSection22.E7
