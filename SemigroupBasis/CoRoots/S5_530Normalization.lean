import SemigroupBasis.CoRoots.S5_345Factors

namespace SemigroupBasis.CoRoots.S5_530

open SemigroupBasis
open SemigroupBasis.Examples

def s5_530XXX : Word Nat := ⟨0, [0, 0]⟩
def s5_530XXXX : Word Nat := ⟨0, [0, 0, 0]⟩
def s5_530XYX : Word Nat := ⟨0, [1, 0]⟩
def s5_530XXY : Word Nat := ⟨0, [0, 1]⟩

def s5_530PowerLaw : Identity Nat :=
  ⟨s5_530XXX, s5_530XXXX⟩

def s5_530GatherLaw : Identity Nat :=
  ⟨s5_530XXY, s5_530XYX⟩

/-- The exact S5_530 basis `xxx = xxxx`, `xxy = xyx`. -/
def s5_530Basis : List (Identity Nat) :=
  [s5_530PowerLaw, s5_530GatherLaw]

theorem s5_530Basis_models_leftRegularBandThree :
    Models leftRegularBandThree.semigroup s5_530Basis := by
  intro identity member
  simp only [s5_530Basis, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl
  · intro valuation
    change Nat → Fin 3 at valuation
    change
      leftRegularBandThreeMul
          (leftRegularBandThreeMul (valuation 0) (valuation 0))
          (valuation 0) =
        leftRegularBandThreeMul
          (leftRegularBandThreeMul
            (leftRegularBandThreeMul
              (valuation 0) (valuation 0))
            (valuation 0))
          (valuation 0)
    by_cases h : valuation 0 = 1
    · simp [leftRegularBandThreeMul, h]
    · simp [leftRegularBandThreeMul, h]
  · intro valuation
    change Nat → Fin 3 at valuation
    change
      leftRegularBandThreeMul
          (leftRegularBandThreeMul (valuation 0) (valuation 0))
          (valuation 1) =
        leftRegularBandThreeMul
          (leftRegularBandThreeMul (valuation 0) (valuation 1))
          (valuation 0)
    by_cases h : valuation 0 = 1
    · simp [leftRegularBandThreeMul, h]
    · simp [leftRegularBandThreeMul, h]

theorem s5_530Derives_firstOccurrenceSequence_eq
    {left right : Word Nat}
    (derivation : Derives s5_530Basis left right) :
    firstOccurrenceSequence left.toList =
      firstOccurrenceSequence right.toList :=
  SemigroupBasis.CoRoots.S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
      ⟨left, right⟩
      (derivation.sound s5_530Basis_models_leftRegularBandThree)

private def s5_530Instantiate
    (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

/-- Four consecutive copies of a nonempty block contract to three copies. -/
theorem s5_530DerivesFourToThree (u : Word Nat) :
    Derives s5_530Basis
      (((u ++ u) ++ u) ++ u) ((u ++ u) ++ u) := by
  have hbase :
      Derives s5_530Basis
        s5_530XXXX s5_530XXX :=
    Derives.symm <|
      Derives.fromBasis (e := s5_530PowerLaw) <|
        List.Mem.head _
  have h :=
    Derives.subst hbase (s5_530Instantiate u u)
  simpa [s5_530Basis,
    s5_530PowerLaw, s5_530XXXX,
    s5_530XXX, s5_530Instantiate,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using h

/-- Gather a later copy of a block next to its first copy. -/
theorem s5_530DerivesGather (u v : Word Nat) :
    Derives s5_530Basis
      ((u ++ v) ++ u) ((u ++ u) ++ v) := by
  have hbase :
      Derives s5_530Basis
        s5_530XYX s5_530XXY :=
    Derives.symm <|
      Derives.fromBasis (e := s5_530GatherLaw) <|
        List.Mem.tail _ (List.Mem.head _)
  have h :=
    Derives.subst hbase (s5_530Instantiate u v)
  simpa [s5_530Basis,
    s5_530GatherLaw, s5_530XYX,
    s5_530XXY, s5_530Instantiate,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using h

def s5_530WordOfCons
    (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

/-- Move one later occurrence of the initial variable next to its first
occurrence. -/
private theorem s5_530DerivesFirstRepeat
    (x : Nat) (middle suffix : List Nat) :
    Derives s5_530Basis
      (s5_530WordOfCons x (middle ++ x :: suffix))
      (s5_530WordOfCons x (x :: middle ++ suffix)) := by
  cases middle with
  | nil =>
      exact Derives.refl _
  | cons y ys =>
      let middleWord := s5_530WordOfCons y ys
      cases suffix with
      | nil =>
          simpa [s5_530WordOfCons, middleWord,
            Word.append, Word.singleton, Word.append_assoc] using
              s5_530DerivesGather
                (Word.singleton x) middleWord
      | cons z zs =>
          have h :=
            Derives.appendRight
              (s5_530DerivesGather
                (Word.singleton x) middleWord)
              (s5_530WordOfCons z zs)
          simpa [s5_530WordOfCons, middleWord,
            Word.append, Word.singleton, Word.append_assoc] using h

/-- Move a third occurrence of the initial variable next to its initial
double block. -/
private theorem s5_530DerivesThird
    (x : Nat) (middle suffix : List Nat) :
    Derives s5_530Basis
      (s5_530WordOfCons x
        (x :: middle ++ x :: suffix))
      (s5_530WordOfCons x
        (x :: x :: middle ++ suffix)) := by
  cases middle with
  | nil =>
      exact Derives.refl _
  | cons y ys =>
      let middleWord := s5_530WordOfCons y ys
      have moved :=
        Derives.prepend (Word.singleton x) <|
          s5_530DerivesGather
            (Word.singleton x) middleWord
      cases suffix with
      | nil =>
          simpa [s5_530WordOfCons, middleWord,
            Word.append, Word.singleton, Word.append_assoc] using moved
      | cons z zs =>
          have movedWithSuffix :=
            Derives.appendRight moved
              (s5_530WordOfCons z zs)
          simpa [s5_530WordOfCons, middleWord,
            Word.append, Word.singleton, Word.append_assoc] using
              movedWithSuffix

/-- Gather a fourth occurrence and contract the resulting initial fourth
power back to a triple block. -/
private theorem s5_530DerivesFourthToThree
    (x : Nat) (middle suffix : List Nat) :
    Derives s5_530Basis
      (s5_530WordOfCons x
        (x :: x :: middle ++ x :: suffix))
      (s5_530WordOfCons x
        (x :: x :: middle ++ suffix)) := by
  cases middle with
  | nil =>
      cases suffix with
      | nil =>
          simpa [s5_530WordOfCons, Word.append,
            Word.singleton, Word.append_assoc] using
              s5_530DerivesFourToThree
                (Word.singleton x)
      | cons z zs =>
          have h :=
            Derives.appendRight
              (s5_530DerivesFourToThree
                (Word.singleton x))
              (s5_530WordOfCons z zs)
          simpa [s5_530WordOfCons, Word.append,
            Word.singleton, Word.append_assoc] using h
  | cons y ys =>
      let middleWord := s5_530WordOfCons y ys
      have moved :=
        Derives.prepend
          ((Word.singleton x) ++ (Word.singleton x)) <|
            s5_530DerivesGather
              (Word.singleton x) middleWord
      have contracted :=
        Derives.appendRight
          (s5_530DerivesFourToThree
            (Word.singleton x))
          middleWord
      cases suffix with
      | nil =>
          exact Derives.trans
            (by
              simpa [s5_530WordOfCons, middleWord,
                Word.append, Word.singleton, Word.append_assoc] using moved)
            (by
              simpa [s5_530WordOfCons, middleWord,
                Word.append, Word.singleton, Word.append_assoc] using
                  contracted)
      | cons z zs =>
          have movedWithSuffix :=
            Derives.appendRight moved
              (s5_530WordOfCons z zs)
          have contractedWithSuffix :=
            Derives.appendRight contracted
              (s5_530WordOfCons z zs)
          exact Derives.trans
            (by
              simpa [s5_530WordOfCons, middleWord,
                Word.append, Word.singleton, Word.append_assoc] using
                  movedWithSuffix)
            (by
              simpa [s5_530WordOfCons, middleWord,
                Word.append, Word.singleton, Word.append_assoc] using
                  contractedWithSuffix)

private inductive S5_530GatherState where
  | one
  | two
  | three
deriving DecidableEq, Repr

private def S5_530GatherState.exponent :
    S5_530GatherState → Nat
  | .one => 1
  | .two => 2
  | .three => 3

private def S5_530GatherState.next :
    S5_530GatherState → S5_530GatherState
  | .one => .two
  | .two => .three
  | .three => .three

private def S5_530GatherState.advance :
    S5_530GatherState → Nat → S5_530GatherState
  | state, 0 => state
  | state, n + 1 => advance state.next n

private def s5_530BlockTail
    (state : S5_530GatherState)
    (x : Nat) (middle suffix : List Nat) : List Nat :=
  List.replicate (state.exponent - 1) x ++ middle ++ suffix

/-- Positive multiplicities are represented by one, two, or three copies. -/
def s5_530Exponent (n : Nat) : Nat :=
  min n 3

theorem s5_530Exponent_pos {n : Nat} (positive : 0 < n) :
    0 < s5_530Exponent n := by
  unfold s5_530Exponent
  omega

theorem s5_530Exponent_succ (n : Nat) :
    s5_530Exponent (n + 1) =
      min (s5_530Exponent n + 1) 3 := by
  simp [s5_530Exponent]
  omega

private theorem s5_530Advance_exponent
    (state : S5_530GatherState) (n : Nat) :
    (state.advance n).exponent =
      s5_530Exponent (state.exponent + n) := by
  induction n generalizing state with
  | zero =>
      cases state <;> rfl
  | succ n ih =>
      rw [S5_530GatherState.advance]
      rw [ih]
      cases state with
      | one =>
          simp only [S5_530GatherState.next,
            S5_530GatherState.exponent]
          congr 1
          omega
      | two =>
          simp only [S5_530GatherState.next,
            S5_530GatherState.exponent]
          congr 1
          omega
      | three =>
          simp only [S5_530GatherState.next,
            S5_530GatherState.exponent]
          simp [s5_530Exponent]

private theorem s5_530Exponent_le_three (n : Nat) :
    s5_530Exponent n ≤ 3 := by
  exact Nat.min_le_right _ _

private theorem s5_530Exponent_succ_normalized (n : Nat) :
    s5_530Exponent
        (s5_530Exponent n + 1) =
      s5_530Exponent (n + 1) := by
  have bound := s5_530Exponent_le_three n
  have cases :
      s5_530Exponent n = 0 ∨
          s5_530Exponent n = 1 ∨
          s5_530Exponent n = 2 ∨
            s5_530Exponent n = 3 := by
    have nonnegative : 0 ≤ s5_530Exponent n := by omega
    omega
  rcases cases with h | h | h | h <;>
    rw [s5_530Exponent_succ n] <;>
    rw [h] <;>
    simp [s5_530Exponent]

/-- Scan a suffix, gathering every later copy of the initial variable. The
front block moves through the states one, two, and saturated three. -/
private theorem s5_530DerivesGatherPeriod :
    ∀ (state : S5_530GatherState)
        (x : Nat) (middle rest : List Nat),
      Derives s5_530Basis
        (s5_530WordOfCons x
          (s5_530BlockTail state x middle rest))
        (s5_530WordOfCons x
          (s5_530BlockTail
            (state.advance (rest.count x)) x middle
            (rest.filter (fun y => decide (y ≠ x)))))
  | state, x, middle, [] => by
      simp [s5_530BlockTail,
        S5_530GatherState.advance]
      exact Derives.refl _
  | state, x, middle, y :: ys => by
      by_cases hy : y = x
      · subst y
        cases state with
        | one =>
            have first :=
              s5_530DerivesFirstRepeat x middle ys
            have remaining :=
              s5_530DerivesGatherPeriod
                .two x middle ys
            exact Derives.trans first <| by
              simpa [s5_530BlockTail,
                S5_530GatherState.advance] using remaining
        | two =>
            have first :=
              s5_530DerivesThird x middle ys
            have remaining :=
              s5_530DerivesGatherPeriod
                .three x middle ys
            exact Derives.trans first <| by
              simpa [s5_530BlockTail,
                S5_530GatherState.advance] using remaining
        | three =>
            have first :=
              s5_530DerivesFourthToThree x middle ys
            have remaining :=
              s5_530DerivesGatherPeriod
                .three x middle ys
            exact Derives.trans first <| by
              simpa [s5_530BlockTail,
                S5_530GatherState.advance] using remaining
      · have remaining :=
          s5_530DerivesGatherPeriod
            state x (middle ++ [y]) ys
        simpa [s5_530BlockTail, hy,
          List.count_cons_of_ne hy, List.append_assoc] using remaining

private theorem s5_530Count_replicate_of_ne
    {x z : Nat} (hzx : z ≠ x) :
    ∀ n : Nat, (List.replicate n x).count z = 0
  | 0 => rfl
  | n + 1 => by
      rw [List.replicate_succ,
        List.count_cons_of_ne (Ne.symm hzx),
        s5_530Count_replicate_of_ne hzx n]

private theorem s5_530Count_filter_ne_self
    (x : Nat) (xs : List Nat) :
    (xs.filter (fun z => decide (z ≠ x))).count x = 0 := by
  apply List.count_eq_zero.mpr
  simp

private theorem s5_530Count_filter_ne_of_ne
    {x z : Nat} (hzx : z ≠ x) (xs : List Nat) :
    (xs.filter (fun a => decide (a ≠ x))).count z = xs.count z := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
      by_cases hax : a = x
      · subst a
        rw [List.filter_cons_of_neg (by simp),
          List.count_cons_of_ne (Ne.symm hzx)]
        exact ih
      · rw [List.filter_cons_of_pos (by simpa)]
        simp only [List.count_cons]
        rw [ih]

/-- The unrestricted first-occurrence normal list. Each variable occurs in
one block of length one, two, or three, with length determined by
`s5_530Exponent`. -/
def s5_530NormalList : List Nat → List Nat
  | [] => []
  | x :: xs =>
      let rest := s5_530NormalList xs
      List.replicate
          (s5_530Exponent ((x :: xs).count x)) x ++
        rest.filter (fun y => decide (y ≠ x))

theorem s5_530NormalList_count
    (z : Nat) :
    ∀ xs : List Nat,
      (s5_530NormalList xs).count z =
        s5_530Exponent (xs.count z)
  | [] => by
      simp [s5_530NormalList,
        s5_530Exponent]
  | x :: xs => by
      simp only [s5_530NormalList, List.count_append]
      by_cases hzx : z = x
      · subst z
        rw [List.count_replicate_self,
          s5_530Count_filter_ne_self]
        omega
      · rw [s5_530Count_replicate_of_ne hzx,
          s5_530Count_filter_ne_of_ne hzx,
          Nat.zero_add, s5_530NormalList_count]
        rw [List.count_cons_of_ne (Ne.symm hzx)]

theorem s5_530NormalList_cons_ne_nil
    (x : Nat) (xs : List Nat) :
    s5_530NormalList (x :: xs) ≠ [] := by
  intro h
  have countEq :=
    s5_530NormalList_count x (x :: xs)
  rw [h, List.count_nil, List.count_cons_self] at countEq
  exact (Nat.ne_of_gt <|
    s5_530Exponent_pos (by omega)) countEq.symm

/-- Flattened first-occurrence block normal forms. Every variable has exactly
one block, of length one, two, or three. -/
inductive S5_530Normal : List Nat → Prop
  | nil : S5_530Normal []
  | single (x : Nat) (xs : List Nat) :
      S5_530Normal xs →
      x ∉ xs →
      S5_530Normal (x :: xs)
  | double (x : Nat) (xs : List Nat) :
      S5_530Normal xs →
      x ∉ xs →
      S5_530Normal (x :: x :: xs)
  | triple (x : Nat) (xs : List Nat) :
      S5_530Normal xs →
      x ∉ xs →
      S5_530Normal (x :: x :: x :: xs)

private theorem s5_530Mem_firstOccurrenceSequence_iff
    (z : Nat) :
    ∀ xs : List Nat,
      z ∈ firstOccurrenceSequence xs ↔ z ∈ xs
  | [] => by simp [firstOccurrenceSequence]
  | x :: xs => by
      by_cases hzx : z = x
      · subst z
        simp [firstOccurrenceSequence]
      · simp [firstOccurrenceSequence, hzx,
          s5_530Mem_firstOccurrenceSequence_iff z xs]

private theorem s5_530FirstOccurrences_single
    {x : Nat} {xs : List Nat} (notMem : x ∉ xs) :
    firstOccurrenceSequence (x :: xs) =
      x :: firstOccurrenceSequence xs := by
  simp only [firstOccurrenceSequence]
  congr 1
  apply List.filter_eq_self.mpr
  intro z member
  simp only [decide_eq_true_eq]
  intro equal
  subst z
  exact notMem <|
    (s5_530Mem_firstOccurrenceSequence_iff x xs).mp member

private theorem s5_530FirstOccurrences_double
    {x : Nat} {xs : List Nat} (notMem : x ∉ xs) :
    firstOccurrenceSequence (x :: x :: xs) =
      x :: firstOccurrenceSequence xs := by
  rw [firstOccurrenceSequence,
    s5_530FirstOccurrences_single notMem]
  simp
  intro a member equal
  subst a
  exact notMem <|
    (s5_530Mem_firstOccurrenceSequence_iff x xs).mp member

private theorem s5_530FirstOccurrences_triple
    {x : Nat} {xs : List Nat} (notMem : x ∉ xs) :
    firstOccurrenceSequence (x :: x :: x :: xs) =
      x :: firstOccurrenceSequence xs := by
  rw [firstOccurrenceSequence, firstOccurrenceSequence,
    s5_530FirstOccurrences_single notMem]
  simp
  intro a member equal
  subst a
  exact notMem <|
    (s5_530Mem_firstOccurrenceSequence_iff x xs).mp member

private theorem s5_530TailCounts
    {x : Nat} {xs ys : List Nat}
    (xNotMemXs : x ∉ xs) (xNotMemYs : x ∉ ys)
    (counts :
      ∀ z, (x :: xs).count z = (x :: ys).count z) :
    ∀ z, xs.count z = ys.count z := by
  intro z
  by_cases hzx : z = x
  · subst z
    exact (List.count_eq_zero.mpr xNotMemXs).trans
      (List.count_eq_zero.mpr xNotMemYs).symm
  · simpa [List.count_cons_of_ne (Ne.symm hzx)] using counts z

private theorem s5_530TailCounts_double
    {x : Nat} {xs ys : List Nat}
    (xNotMemXs : x ∉ xs) (xNotMemYs : x ∉ ys)
    (counts :
      ∀ z, (x :: x :: xs).count z =
        (x :: x :: ys).count z) :
    ∀ z, xs.count z = ys.count z := by
  intro z
  by_cases hzx : z = x
  · subst z
    exact (List.count_eq_zero.mpr xNotMemXs).trans
      (List.count_eq_zero.mpr xNotMemYs).symm
  · simpa [List.count_cons_of_ne (Ne.symm hzx)] using counts z

private theorem s5_530TailCounts_triple
    {x : Nat} {xs ys : List Nat}
    (xNotMemXs : x ∉ xs) (xNotMemYs : x ∉ ys)
    (counts :
      ∀ z, (x :: x :: x :: xs).count z =
        (x :: x :: x :: ys).count z) :
    ∀ z, xs.count z = ys.count z := by
  intro z
  by_cases hzx : z = x
  · subst z
    exact (List.count_eq_zero.mpr xNotMemXs).trans
      (List.count_eq_zero.mpr xNotMemYs).symm
  · simpa [List.count_cons_of_ne (Ne.symm hzx)] using counts z

/-- Normal block lists are determined by first-occurrence order and their
exact multiplicities. -/
theorem s5_530Normal_eq_of_invariants
    {xs ys : List Nat}
    (normalXs : S5_530Normal xs) (normalYs : S5_530Normal ys)
    (order :
      firstOccurrenceSequence xs =
        firstOccurrenceSequence ys)
    (counts : ∀ z, xs.count z = ys.count z) :
    xs = ys := by
  induction normalXs generalizing ys with
  | nil =>
      cases normalYs with
      | nil => rfl
      | single y ys _ yNotMem =>
          have count := counts y
          simp [List.count_eq_zero.mpr yNotMem] at count
      | double y ys _ yNotMem =>
          have count := counts y
          simp [List.count_eq_zero.mpr yNotMem] at count
      | triple y ys _ yNotMem =>
          have count := counts y
          simp [List.count_eq_zero.mpr yNotMem] at count
  | single x xs normalTail xNotMem ih =>
      cases normalYs with
      | nil =>
          have count := counts x
          simp [List.count_eq_zero.mpr xNotMem] at count
      | single y ys normalRight yNotMem =>
          rw [s5_530FirstOccurrences_single xNotMem,
            s5_530FirstOccurrences_single yNotMem] at order
          have heads := (List.cons.inj order).1
          subst y
          congr 1
          exact ih normalRight (List.cons.inj order).2 <|
            s5_530TailCounts xNotMem yNotMem counts
      | double y ys normalRight yNotMem =>
          rw [s5_530FirstOccurrences_single xNotMem,
            s5_530FirstOccurrences_double yNotMem] at order
          have heads := (List.cons.inj order).1
          subst y
          have count := counts x
          simp [List.count_eq_zero.mpr xNotMem,
            List.count_eq_zero.mpr yNotMem] at count
      | triple y ys normalRight yNotMem =>
          rw [s5_530FirstOccurrences_single xNotMem,
            s5_530FirstOccurrences_triple yNotMem] at order
          have heads := (List.cons.inj order).1
          subst y
          have count := counts x
          simp [List.count_eq_zero.mpr xNotMem,
            List.count_eq_zero.mpr yNotMem] at count
  | double x xs normalTail xNotMem ih =>
      cases normalYs with
      | nil =>
          have count := counts x
          simp [List.count_eq_zero.mpr xNotMem] at count
      | single y ys normalRight yNotMem =>
          rw [s5_530FirstOccurrences_double xNotMem,
            s5_530FirstOccurrences_single yNotMem] at order
          have heads := (List.cons.inj order).1
          subst y
          have count := counts x
          simp [List.count_eq_zero.mpr xNotMem,
            List.count_eq_zero.mpr yNotMem] at count
      | double y ys normalRight yNotMem =>
          rw [s5_530FirstOccurrences_double xNotMem,
            s5_530FirstOccurrences_double yNotMem] at order
          have heads := (List.cons.inj order).1
          subst y
          congr 2
          exact ih normalRight (List.cons.inj order).2 <|
            s5_530TailCounts_double xNotMem yNotMem counts
      | triple y ys normalRight yNotMem =>
          rw [s5_530FirstOccurrences_double xNotMem,
            s5_530FirstOccurrences_triple yNotMem] at order
          have heads := (List.cons.inj order).1
          subst y
          have count := counts x
          simp [List.count_eq_zero.mpr xNotMem,
            List.count_eq_zero.mpr yNotMem] at count
  | triple x xs normalTail xNotMem ih =>
      cases normalYs with
      | nil =>
          have count := counts x
          simp [List.count_eq_zero.mpr xNotMem] at count
      | single y ys normalRight yNotMem =>
          rw [s5_530FirstOccurrences_triple xNotMem,
            s5_530FirstOccurrences_single yNotMem] at order
          have heads := (List.cons.inj order).1
          subst y
          have count := counts x
          simp [List.count_eq_zero.mpr xNotMem,
            List.count_eq_zero.mpr yNotMem] at count
      | double y ys normalRight yNotMem =>
          rw [s5_530FirstOccurrences_triple xNotMem,
            s5_530FirstOccurrences_double yNotMem] at order
          have heads := (List.cons.inj order).1
          subst y
          have count := counts x
          simp [List.count_eq_zero.mpr xNotMem,
            List.count_eq_zero.mpr yNotMem] at count
      | triple y ys normalRight yNotMem =>
          rw [s5_530FirstOccurrences_triple xNotMem,
            s5_530FirstOccurrences_triple yNotMem] at order
          have heads := (List.cons.inj order).1
          subst y
          congr 3
          exact ih normalRight (List.cons.inj order).2 <|
            s5_530TailCounts_triple xNotMem yNotMem counts

private theorem S5_530Normal.filter_ne
    {xs : List Nat} (normal : S5_530Normal xs) (x : Nat) :
    S5_530Normal
      (xs.filter (fun y => decide (y ≠ x))) := by
  induction normal with
  | nil =>
      exact .nil
  | single y ys _ yNotMem ih =>
      by_cases hyx : y = x
      · subst y
        have tailEq :
            ys.filter (fun z => decide (z ≠ x)) = ys := by
          apply List.filter_eq_self.mpr
          intro z hz
          simp only [decide_eq_true_eq]
          intro h
          subst z
          exact yNotMem hz
        simpa [tailEq] using ih
      · have yNotMemFilter :
            y ∉ ys.filter (fun z => decide (z ≠ x)) := by
          exact fun h => yNotMem (List.mem_filter.mp h).1
        simpa [hyx] using
          S5_530Normal.single y _ ih yNotMemFilter
  | double y ys _ yNotMem ih =>
      by_cases hyx : y = x
      · subst y
        have tailEq :
            ys.filter (fun z => decide (z ≠ x)) = ys := by
          apply List.filter_eq_self.mpr
          intro z hz
          simp only [decide_eq_true_eq]
          intro h
          subst z
          exact yNotMem hz
        simpa [tailEq] using ih
      · have yNotMemFilter :
            y ∉ ys.filter (fun z => decide (z ≠ x)) := by
          exact fun h => yNotMem (List.mem_filter.mp h).1
        simpa [hyx] using
          S5_530Normal.double y _ ih yNotMemFilter
  | triple y ys _ yNotMem ih =>
      by_cases hyx : y = x
      · subst y
        have tailEq :
            ys.filter (fun z => decide (z ≠ x)) = ys := by
          apply List.filter_eq_self.mpr
          intro z hz
          simp only [decide_eq_true_eq]
          intro h
          subst z
          exact yNotMem hz
        simpa [tailEq] using ih
      · have yNotMemFilter :
            y ∉ ys.filter (fun z => decide (z ≠ x)) := by
          exact fun h => yNotMem (List.mem_filter.mp h).1
        simpa [hyx] using
          S5_530Normal.triple y _ ih yNotMemFilter

theorem s5_530NormalList_normal :
    ∀ xs : List Nat,
      S5_530Normal
        (s5_530NormalList xs)
  | [] => .nil
  | x :: xs => by
      let rest := s5_530NormalList xs
      have restNormal := s5_530NormalList_normal xs
      have filteredNormal := restNormal.filter_ne x
      have xNotMem :
          x ∉ rest.filter (fun y => decide (y ≠ x)) := by
        simp
      have positive :
          0 < s5_530Exponent ((x :: xs).count x) :=
        s5_530Exponent_pos (by simp)
      have bound :=
        s5_530Exponent_le_three ((x :: xs).count x)
      have cases :
          s5_530Exponent ((x :: xs).count x) = 1 ∨
            s5_530Exponent ((x :: xs).count x) = 2 ∨
              s5_530Exponent ((x :: xs).count x) = 3 := by
        omega
      rcases cases with h | h | h
      · change S5_530Normal
          (List.replicate
              (s5_530Exponent ((x :: xs).count x)) x ++
            rest.filter (fun y => decide (y ≠ x)))
        rw [h]
        simpa using
          S5_530Normal.single
            x _ filteredNormal xNotMem
      · change S5_530Normal
          (List.replicate
              (s5_530Exponent ((x :: xs).count x)) x ++
            rest.filter (fun y => decide (y ≠ x)))
        rw [h]
        simpa using
          S5_530Normal.double
            x _ filteredNormal xNotMem
      · change S5_530Normal
          (List.replicate
              (s5_530Exponent ((x :: xs).count x)) x ++
            rest.filter (fun y => decide (y ≠ x)))
        rw [h]
        simpa using
          S5_530Normal.triple
            x _ filteredNormal xNotMem

private theorem s5_530DerivesNormalizeList :
    ∀ x xs,
      match s5_530NormalList (x :: xs) with
      | [] => False
      | y :: ys =>
          Derives s5_530Basis
            (s5_530WordOfCons x xs)
            (s5_530WordOfCons y ys)
  | x, [] => by
      have normalEq :
          s5_530NormalList [x] = [x] := by
        simp [s5_530NormalList,
          s5_530Exponent]
      rw [normalEq]
      exact Derives.refl _
  | x, y :: ys => by
      have suffixNormal :=
        s5_530DerivesNormalizeList y ys
      cases hn : s5_530NormalList (y :: ys) with
      | nil =>
          exact False.elim <|
            s5_530NormalList_cons_ne_nil y ys hn
      | cons z zs =>
          rw [hn] at suffixNormal
          have prefixed :=
            Derives.prepend (Word.singleton x) suffixNormal
          have gathered :=
            s5_530DerivesGatherPeriod
              .one x [] (z :: zs)
          have restCount :
              (z :: zs).count x =
                s5_530Exponent ((y :: ys).count x) := by
            simpa [hn] using
              s5_530NormalList_count x (y :: ys)
          have exponentEq :
              ((S5_530GatherState.one.advance
                  ((z :: zs).count x)).exponent) =
                s5_530Exponent
                  ((x :: y :: ys).count x) := by
            rw [s5_530Advance_exponent]
            simp only [S5_530GatherState.exponent]
            rw [restCount, List.count_cons_self]
            simpa [Nat.add_comm] using
              s5_530Exponent_succ_normalized
                ((y :: ys).count x)
          have positive :
              0 <
                s5_530Exponent
                  ((x :: y :: ys).count x) :=
            s5_530Exponent_pos (by simp)
          have normalEq :
              s5_530NormalList (x :: y :: ys) =
                x ::
                  List.replicate
                    (s5_530Exponent
                      ((x :: y :: ys).count x) - 1) x ++
                    (z :: zs).filter
                      (fun a => decide (a ≠ x)) := by
            change
              List.replicate
                  (s5_530Exponent
                    ((x :: y :: ys).count x)) x ++
                  (s5_530NormalList
                    (y :: ys)).filter
                    (fun a => decide (a ≠ x)) =
                x ::
                  List.replicate
                    (s5_530Exponent
                      ((x :: y :: ys).count x) - 1) x ++
                    (z :: zs).filter
                      (fun a => decide (a ≠ x))
            rw [hn]
            cases h :
                s5_530Exponent
                  ((x :: y :: ys).count x) with
            | zero => omega
            | succ n =>
                simp [List.replicate_succ]
          rw [normalEq]
          exact Derives.trans
            (by
              simpa [s5_530WordOfCons, Word.append,
                Word.singleton, Word.append_assoc] using prefixed)
            (by
              simpa [s5_530BlockTail, exponentEq] using
                gathered)
termination_by
  _ xs => xs.length

/-- Every nonempty word derives to its first-occurrence block normal form,
whose block sizes are one, two, or three. -/
theorem s5_530DerivesNormal (w : Word Nat) :
    match s5_530NormalList w.toList with
    | [] => False
    | x :: xs =>
        Derives s5_530Basis w
          (s5_530WordOfCons x xs) := by
  cases w with
  | mk head tail =>
      exact s5_530DerivesNormalizeList head tail

/-- First-occurrence order and capped multiplicities are a complete
derivability invariant for the exact two-law basis. -/
theorem s5_530DerivesOfInvariantEq
    (left right : Word Nat)
    (order :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList)
    (counts :
      ∀ z,
        s5_530Exponent (left.toList.count z) =
          s5_530Exponent (right.toList.count z)) :
    Derives s5_530Basis left right := by
  have leftNormal := s5_530DerivesNormal left
  have rightNormal := s5_530DerivesNormal right
  cases hl : s5_530NormalList left.toList with
  | nil =>
      exact False.elim <|
        s5_530NormalList_cons_ne_nil left.head left.tail <| by
          simpa [Word.toList] using hl
  | cons x xs =>
      cases hr : s5_530NormalList right.toList with
      | nil =>
          exact False.elim <|
            s5_530NormalList_cons_ne_nil right.head right.tail <| by
              simpa [Word.toList] using hr
      | cons y ys =>
          rw [hl] at leftNormal
          rw [hr] at rightNormal
          have normalOrder :
              firstOccurrenceSequence (x :: xs) =
                firstOccurrenceSequence (y :: ys) := by
            have leftPreserved :=
              s5_530Derives_firstOccurrenceSequence_eq leftNormal
            have rightPreserved :=
              s5_530Derives_firstOccurrenceSequence_eq rightNormal
            exact leftPreserved.symm.trans <|
              order.trans rightPreserved
          have normalCounts :
              ∀ z, (x :: xs).count z = (y :: ys).count z := by
            intro z
            calc
              (x :: xs).count z =
                  s5_530Exponent (left.toList.count z) := by
                    rw [← hl]
                    exact s5_530NormalList_count z left.toList
              _ = s5_530Exponent (right.toList.count z) :=
                    counts z
              _ = (y :: ys).count z := by
                    rw [← hr]
                    exact (s5_530NormalList_count z right.toList).symm
          have leftForm : S5_530Normal (x :: xs) := by
            rw [← hl]
            exact s5_530NormalList_normal left.toList
          have rightForm : S5_530Normal (y :: ys) := by
            rw [← hr]
            exact s5_530NormalList_normal right.toList
          have reducedEqual : x :: xs = y :: ys :=
            s5_530Normal_eq_of_invariants
              leftForm rightForm normalOrder normalCounts
          cases reducedEqual
          exact Derives.trans leftNormal (Derives.symm rightNormal)

/-- Generic completeness interface for a model that separates the two
normal-form invariants. -/
theorem s5_530Basis_complete_of_invariants
    (T : FiniteTable)
    (models : Models T.semigroup s5_530Basis)
    (separatesOrder :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy T.semigroup →
          firstOccurrenceSequence identity.lhs.toList =
            firstOccurrenceSequence identity.rhs.toList)
    (separatesCounts :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy T.semigroup →
          ∀ z,
            s5_530Exponent (identity.lhs.toList.count z) =
              s5_530Exponent (identity.rhs.toList.count z)) :
    BasisFor T.semigroup s5_530Basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact s5_530DerivesOfInvariantEq identity.lhs identity.rhs
    (separatesOrder identity valid)
    (separatesCounts identity valid)

end SemigroupBasis.CoRoots.S5_530
