import SemigroupBasis.FiniteTable

namespace SemigroupBasis.Examples

open SemigroupBasis

def parityInitialX : Word Nat := Word.singleton 0
def parityInitialXXX : Word Nat := ⟨0, [0, 0]⟩
def parityInitialXYX : Word Nat := ⟨0, [1, 0]⟩
def parityInitialXXY : Word Nat := ⟨0, [0, 1]⟩

def parityInitialPowerLaw : Identity Nat :=
  ⟨parityInitialX, parityInitialXXX⟩

def parityInitialGatherLaw : Identity Nat :=
  ⟨parityInitialXYX, parityInitialXXY⟩

/-- The exact basis `x = xxx`, `xyx = xxy`. -/
def parityInitialBasis : List (Identity Nat) :=
  [parityInitialPowerLaw, parityInitialGatherLaw]

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

theorem parityInitialDerivesPowerContraction (u : Word Nat) :
    Derives parityInitialBasis ((u ++ u) ++ u) u := by
  have hbase :
      Derives parityInitialBasis parityInitialXXX parityInitialX :=
    Derives.symm <|
      Derives.fromBasis (e := parityInitialPowerLaw) <|
        List.Mem.head _
  have h := Derives.subst hbase (instantiateTwoWords u u)
  simpa [parityInitialBasis, parityInitialPowerLaw, parityInitialXXX,
    parityInitialX, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using h

theorem parityInitialDerivesGather (u v : Word Nat) :
    Derives parityInitialBasis
      ((u ++ v) ++ u) ((u ++ u) ++ v) := by
  have hbase :
      Derives parityInitialBasis parityInitialXYX parityInitialXXY :=
    Derives.fromBasis (e := parityInitialGatherLaw) <|
      List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [parityInitialBasis, parityInitialGatherLaw, parityInitialXYX,
    parityInitialXXY, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using h

def parityInitialWordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

/-- Move one later occurrence of the initial variable next to its first
occurrence. -/
private theorem parityInitialDerivesFirstRepeat
    (x : Nat) (middle suffix : List Nat) :
    Derives parityInitialBasis
      (parityInitialWordOfCons x (middle ++ x :: suffix))
      (parityInitialWordOfCons x (x :: middle ++ suffix)) := by
  cases middle with
  | nil =>
      exact Derives.refl _
  | cons y ys =>
      let middleWord := parityInitialWordOfCons y ys
      cases suffix with
      | nil =>
          simpa [parityInitialWordOfCons, middleWord, Word.append,
            Word.singleton, Word.append_assoc] using
              parityInitialDerivesGather (Word.singleton x) middleWord
      | cons z zs =>
          have h :=
            Derives.appendRight
              (parityInitialDerivesGather
                (Word.singleton x) middleWord)
              (parityInitialWordOfCons z zs)
          simpa [parityInitialWordOfCons, middleWord, Word.append,
            Word.singleton, Word.append_assoc] using h

/-- When two initial copies are present, a later third copy toggles the block
back to a singleton. -/
private theorem parityInitialDerivesToggleDouble
    (x : Nat) (middle suffix : List Nat) :
    Derives parityInitialBasis
      (parityInitialWordOfCons x (x :: middle ++ x :: suffix))
      (parityInitialWordOfCons x (middle ++ suffix)) := by
  cases middle with
  | nil =>
      cases suffix with
      | nil =>
          simpa [parityInitialWordOfCons, Word.append, Word.singleton,
            Word.append_assoc] using
              parityInitialDerivesPowerContraction (Word.singleton x)
      | cons z zs =>
          have h :=
            Derives.appendRight
              (parityInitialDerivesPowerContraction
                (Word.singleton x))
              (parityInitialWordOfCons z zs)
          simpa [parityInitialWordOfCons, Word.append, Word.singleton,
            Word.append_assoc] using h
  | cons y ys =>
      let middleWord := parityInitialWordOfCons y ys
      have moved :=
        Derives.prepend (Word.singleton x) <|
          parityInitialDerivesGather (Word.singleton x) middleWord
      have contracted :=
        Derives.appendRight
          (parityInitialDerivesPowerContraction (Word.singleton x))
          middleWord
      cases suffix with
      | nil =>
          exact Derives.trans
            (by
              simpa [parityInitialWordOfCons, middleWord, Word.append,
                Word.singleton, Word.append_assoc] using moved)
            (by
              simpa [parityInitialWordOfCons, middleWord, Word.append,
                Word.singleton, Word.append_assoc] using contracted)
      | cons z zs =>
          have movedWithSuffix :=
            Derives.appendRight moved (parityInitialWordOfCons z zs)
          have contractedWithSuffix :=
            Derives.appendRight contracted
              (parityInitialWordOfCons z zs)
          exact Derives.trans
            (by
              simpa [parityInitialWordOfCons, middleWord, Word.append,
                Word.singleton, Word.append_assoc] using movedWithSuffix)
            (by
              simpa [parityInitialWordOfCons, middleWord, Word.append,
                Word.singleton, Word.append_assoc] using
                  contractedWithSuffix)

private def parityInitialToggle (double : Bool) (count : Nat) : Bool :=
  if count % 2 = 0 then double else !double

private def parityInitialBlockTail
    (double : Bool) (x : Nat) (middle suffix : List Nat) : List Nat :=
  match double with
  | false => middle ++ suffix
  | true => x :: middle ++ suffix

private theorem parityInitialToggle_succ
    (double : Bool) (count : Nat) :
    parityInitialToggle double (count + 1) =
      parityInitialToggle (!double) count := by
  by_cases even : count % 2 = 0
  · simp [parityInitialToggle, even, Nat.add_mod]
  · have odd : count % 2 = 1 := by omega
    cases double <;>
      simp [parityInitialToggle, odd, Nat.add_mod]

/-- Scan the suffix and gather every later copy of the initial variable.
The front block toggles between one and two copies, so its final size records
the total exponent parity. -/
private theorem parityInitialDerivesGatherParity :
    ∀ (double : Bool) (x : Nat) (middle rest : List Nat),
      Derives parityInitialBasis
        (parityInitialWordOfCons x
          (parityInitialBlockTail double x middle rest))
        (parityInitialWordOfCons x
          (parityInitialBlockTail
            (parityInitialToggle double (rest.count x))
            x middle
            (rest.filter (fun y => decide (y ≠ x)))))
  | double, x, middle, [] => by
      cases double <;>
        simp [parityInitialBlockTail, parityInitialToggle] <;>
        exact Derives.refl _
  | double, x, middle, y :: ys => by
      by_cases hy : y = x
      · subst y
        cases double with
        | false =>
            have first :=
              parityInitialDerivesFirstRepeat x middle ys
            have remaining :=
              parityInitialDerivesGatherParity true x middle ys
            exact Derives.trans first <| by
              simpa [parityInitialBlockTail, List.count_cons_self,
                parityInitialToggle_succ] using remaining
        | true =>
            have first :=
              parityInitialDerivesToggleDouble x middle ys
            have remaining :=
              parityInitialDerivesGatherParity false x middle ys
            exact Derives.trans first <| by
              simpa [parityInitialBlockTail, List.count_cons_self,
                parityInitialToggle_succ] using remaining
      · have remaining :=
          parityInitialDerivesGatherParity
            double x (middle ++ [y]) ys
        simpa [parityInitialBlockTail, hy, List.count_cons_of_ne hy,
          List.append_assoc] using remaining

/-- The unrestricted canonical list: variables occur in first-occurrence
order, and each variable has one or two adjacent copies according to whether
its total exponent is odd or even. -/
def parityInitialNormalList : List Nat → List Nat
  | [] => []
  | x :: xs =>
      let rest := parityInitialNormalList xs
      x ::
        parityInitialBlockTail
          (parityInitialToggle false (rest.count x))
          x [] (rest.filter (fun y => decide (y ≠ x)))

theorem parityInitialNormalList_cons_ne_nil
    (x : Nat) (xs : List Nat) :
    parityInitialNormalList (x :: xs) ≠ [] := by
  simp [parityInitialNormalList]

private theorem parityInitialDerivesNormalizeList :
    ∀ x xs,
      match parityInitialNormalList (x :: xs) with
      | [] => False
      | y :: ys =>
          Derives parityInitialBasis
            (parityInitialWordOfCons x xs)
            (parityInitialWordOfCons y ys)
  | x, [] => by
      exact Derives.refl _
  | x, y :: ys => by
      have suffixNormal :=
        parityInitialDerivesNormalizeList y ys
      cases hn : parityInitialNormalList (y :: ys) with
      | nil =>
          exact False.elim <|
            parityInitialNormalList_cons_ne_nil y ys hn
      | cons z zs =>
          rw [hn] at suffixNormal
          have prefixed :=
            Derives.prepend (Word.singleton x) suffixNormal
          have gathered :=
            parityInitialDerivesGatherParity false x [] (z :: zs)
          rw [parityInitialNormalList, hn]
          change
            Derives parityInitialBasis
              (parityInitialWordOfCons x (y :: ys))
              (parityInitialWordOfCons x
                (parityInitialBlockTail
                  (parityInitialToggle false ((z :: zs).count x))
                  x [] ((z :: zs).filter
                    (fun a => decide (a ≠ x)))))
          exact Derives.trans
            (by
              simpa [parityInitialWordOfCons, Word.append,
                Word.singleton, Word.append_assoc] using prefixed)
            gathered

theorem parityInitialDerivesNormal (w : Word Nat) :
    match parityInitialNormalList w.toList with
    | [] => False
    | x :: xs =>
        Derives parityInitialBasis w
          (parityInitialWordOfCons x xs) := by
  cases w with
  | mk head tail =>
      exact parityInitialDerivesNormalizeList head tail

/-- Canonical block lists contain one or two copies of each variable and no
variable occurs in a later block. -/
inductive ParityInitialNormal : List Nat → Prop
  | nil : ParityInitialNormal []
  | single (x : Nat) (xs : List Nat) :
      ParityInitialNormal xs →
      x ∉ xs →
      ParityInitialNormal (x :: xs)
  | double (x : Nat) (xs : List Nat) :
      ParityInitialNormal xs →
      x ∉ xs →
      ParityInitialNormal (x :: x :: xs)

private theorem ParityInitialNormal.filter_ne
    {xs : List Nat} (normal : ParityInitialNormal xs) (x : Nat) :
    ParityInitialNormal
      (xs.filter (fun y => decide (y ≠ x))) := by
  induction normal with
  | nil =>
      exact ParityInitialNormal.nil
  | single y ys normalY yNotMem ih =>
      by_cases hyx : y = x
      · subst y
        have wholeFilterEq :
            (x :: ys).filter (fun z => decide (z ≠ x)) = ys := by
          have tailFilterEq :
              ys.filter (fun z => decide (z ≠ x)) = ys := by
            apply List.filter_eq_self.mpr
            intro z hz
            have hzx : z ≠ x := by
              intro h
              subst z
              exact yNotMem hz
            simp [hzx]
          rw [List.filter_cons_of_neg (by simp)]
          exact tailFilterEq
        rw [wholeFilterEq]
        exact normalY
      · have yNotMemFilter :
            y ∉ ys.filter (fun z => decide (z ≠ x)) := by
          simp only [List.mem_filter]
          exact fun h => yNotMem h.1
        simpa [hyx] using
          ParityInitialNormal.single y
            (ys.filter (fun z => decide (z ≠ x)))
            ih yNotMemFilter
  | double y ys normalY yNotMem ih =>
      by_cases hyx : y = x
      · subst y
        have wholeFilterEq :
            (x :: x :: ys).filter (fun z => decide (z ≠ x)) = ys := by
          have tailFilterEq :
              ys.filter (fun z => decide (z ≠ x)) = ys := by
            apply List.filter_eq_self.mpr
            intro z hz
            have hzx : z ≠ x := by
              intro h
              subst z
              exact yNotMem hz
            simp [hzx]
          rw [List.filter_cons_of_neg (by simp),
            List.filter_cons_of_neg (by simp)]
          exact tailFilterEq
        rw [wholeFilterEq]
        exact normalY
      · have yNotMemFilter :
            y ∉ ys.filter (fun z => decide (z ≠ x)) := by
          simp only [List.mem_filter]
          exact fun h => yNotMem h.1
        simpa [hyx] using
          ParityInitialNormal.double y
            (ys.filter (fun z => decide (z ≠ x)))
            ih yNotMemFilter

theorem parityInitialNormalList_normal :
    ∀ xs : List Nat,
      ParityInitialNormal (parityInitialNormalList xs)
  | [] => by
      exact ParityInitialNormal.nil
  | x :: xs => by
      have restNormal := parityInitialNormalList_normal xs
      have filteredNormal := restNormal.filter_ne x
      have xNotMem :
          x ∉ (parityInitialNormalList xs).filter
            (fun y => decide (y ≠ x)) := by
        simp
      cases toggle :
          parityInitialToggle false
            ((parityInitialNormalList xs).count x) with
      | false =>
          simpa [parityInitialNormalList, toggle,
            parityInitialBlockTail] using
              ParityInitialNormal.single x
                ((parityInitialNormalList xs).filter
                  (fun y => decide (y ≠ x)))
                filteredNormal xNotMem
      | true =>
          simpa [parityInitialNormalList, toggle,
            parityInitialBlockTail] using
              ParityInitialNormal.double x
                ((parityInitialNormalList xs).filter
                  (fun y => decide (y ≠ x)))
                filteredNormal xNotMem

end SemigroupBasis.Examples
