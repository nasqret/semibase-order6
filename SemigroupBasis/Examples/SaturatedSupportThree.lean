import SemigroupBasis.Examples.CommutativeExponentThree
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

def saturatedX : Word Nat := Word.singleton 0
def saturatedXX : Word Nat := ⟨0, [0]⟩
def saturatedXXX : Word Nat := ⟨0, [0, 0]⟩
def saturatedXY : Word Nat := ⟨0, [1]⟩
def saturatedYX : Word Nat := ⟨1, [0]⟩
def saturatedXXY : Word Nat := ⟨0, [0, 1]⟩

def saturatedPowerLaw : Identity Nat :=
  ⟨saturatedXX, saturatedXXX⟩

def saturatedCommutativityLaw : Identity Nat :=
  ⟨saturatedXY, saturatedYX⟩

def saturatedPrefixDuplicationLaw : Identity Nat :=
  ⟨saturatedXY, saturatedXXY⟩

/-- The common basis `xx = xxx`, `xy = yx`, `xy = xxy`. -/
def saturatedSupportBasis : List (Identity Nat) :=
  [saturatedPowerLaw, saturatedCommutativityLaw,
    saturatedPrefixDuplicationLaw]

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

private theorem exponentAxiomsDeriveInSaturated
    (e : Identity Nat) (he : e ∈ commutativeExponentThreeBasis) :
    Derives saturatedSupportBasis e.lhs e.rhs := by
  simp only [commutativeExponentThreeBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact Derives.fromBasis (e := saturatedPowerLaw) <| by
      exact List.Mem.head _
  · exact Derives.fromBasis (e := saturatedCommutativityLaw) <| by
      exact List.Mem.tail _ (List.Mem.head _)

theorem saturatedDerivesExponent {u v : Word Nat}
    (h : Derives commutativeExponentThreeBasis u v) :
    Derives saturatedSupportBasis u v :=
  h.transport exponentAxiomsDeriveInSaturated

theorem saturatedDerivesCommutativity (u v : Word Nat) :
    Derives saturatedSupportBasis (u ++ v) (v ++ u) :=
  saturatedDerivesExponent (exponentDerivesCommutativity u v)

theorem saturatedDerivesPermutation (u v : Word Nat)
    (h : u.toList.Perm v.toList) :
    Derives saturatedSupportBasis u v :=
  saturatedDerivesExponent (exponentDerivesPermutation u v h)

theorem saturatedDerivesPrefixDuplication (u v : Word Nat) :
    Derives saturatedSupportBasis (u ++ v) ((u ++ u) ++ v) := by
  have hbase :
      Derives saturatedSupportBasis saturatedXY saturatedXXY :=
    Derives.fromBasis (e := saturatedPrefixDuplicationLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [saturatedSupportBasis, saturatedPrefixDuplicationLaw,
    saturatedXY, saturatedXXY, instantiateTwoWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using h

/-- Every non-singleton word derives to its square. -/
theorem saturatedDerivesSquare (w : Word Nat) (h : w.tail ≠ []) :
    Derives saturatedSupportBasis w (w ++ w) := by
  cases w with
  | mk head tail =>
      cases tail with
      | nil => exact False.elim (h rfl)
      | cons next rest =>
          let u := Word.singleton head
          let v : Word Nat := ⟨next, rest⟩
          have duplicateU := saturatedDerivesPrefixDuplication u v
          have moveV :=
            saturatedDerivesCommutativity (u ++ u) v
          have duplicateV :=
            saturatedDerivesPrefixDuplication v (u ++ u)
          have finalPerm :
              ((v ++ v) ++ (u ++ u)).toList.Perm
                ((u ++ v) ++ (u ++ v)).toList := by
            rw [List.perm_iff_count]
            intro z
            simp only [Word.toList_append, List.count_append]
            omega
          have finish :=
            saturatedDerivesPermutation
              ((v ++ v) ++ (u ++ u)) ((u ++ v) ++ (u ++ v))
              finalPerm
          exact Derives.trans
            (by simpa [u, v, Word.append_assoc] using duplicateU) <|
            Derives.trans moveV <|
            Derives.trans duplicateV <|
            (by simpa [u, v, Word.append_assoc] using finish)

/-- The saturated-support normal form contains two copies of every supported
letter. -/
def saturatedReduce (xs : List Nat) : List Nat :=
  exponentReduce (xs ++ xs)

theorem count_saturatedReduce (z : Nat) (xs : List Nat) :
    (saturatedReduce xs).count z =
      if z ∈ xs then 2 else 0 := by
  rw [saturatedReduce, count_exponentReduce, List.count_append]
  by_cases hz : z ∈ xs
  · rw [if_pos hz]
    have hpos : 0 < xs.count z := List.count_pos_iff.mpr hz
    omega
  · rw [if_neg hz]
    have hzero : xs.count z = 0 := by
      exact Nat.eq_zero_of_not_pos <| by
        simpa [List.count_pos_iff] using hz
    omega

private theorem exponentReduce_cons_ne_nil (x : Nat) (xs : List Nat) :
    exponentReduce (x :: xs) ≠ [] := by
  intro hempty
  have hcount := count_exponentReduce x (x :: xs)
  rw [hempty] at hcount
  simp at hcount
  omega

theorem saturatedReduce_perm_of_support_eq {xs ys : List Nat}
    (hsupport : ∀ z, z ∈ xs ↔ z ∈ ys) :
    (saturatedReduce xs).Perm (saturatedReduce ys) := by
  rw [List.perm_iff_count]
  intro z
  rw [count_saturatedReduce, count_saturatedReduce]
  simp only [hsupport z]

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

theorem saturatedDerivesNormal (w : Word Nat) (h : w.tail ≠ []) :
    match saturatedReduce w.toList with
    | [] => False
    | x :: xs =>
        Derives saturatedSupportBasis w (wordOfCons x xs) := by
  have square := saturatedDerivesSquare w h
  have normalized := exponentDerivesNormal (w ++ w)
  have hsame :
      saturatedReduce w.toList = exponentReduce (w ++ w).toList := by
    simp [saturatedReduce, Word.toList_append]
  cases hreduce : exponentReduce (w ++ w).toList with
  | nil =>
      rw [hreduce] at normalized
      exact False.elim normalized
  | cons x xs =>
      rw [hreduce] at normalized
      rw [hsame, hreduce]
      change Derives commutativeExponentThreeBasis
        (w ++ w) ⟨x, xs⟩ at normalized
      change Derives saturatedSupportBasis w (wordOfCons x xs)
      exact Derives.trans square (saturatedDerivesExponent normalized)

/-- Shared completeness criterion. A model of the basis is complete as soon
as its valid identities preserve support and distinguish singleton words from
non-singleton words. -/
theorem saturatedSupportBasis_complete_of
    (T : FiniteTable)
    (models : Models T.semigroup saturatedSupportBasis)
    (supportEq :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList)
    (singletonEq :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        (e.lhs.tail = [] ↔ e.rhs.tail = [])) :
    BasisFor T.semigroup saturatedSupportBasis := by
  refine ⟨models, ?_⟩
  intro e valid
  have hsupport := supportEq e valid
  have hsingleton := singletonEq e valid
  by_cases hl : e.lhs.tail = []
  · have hr : e.rhs.tail = [] := hsingleton.mp hl
    have hheadMem : e.lhs.head ∈ e.rhs.toList :=
      (hsupport e.lhs.head).mp (List.Mem.head _)
    have hheads : e.lhs.head = e.rhs.head := by
      simpa [Word.toList, hr] using hheadMem
    have hwords : e.lhs = e.rhs := by
      apply Word.toList_injective
      simp [Word.toList, hl, hr, hheads]
    rw [hwords]
    exact Derives.refl _
  · have hr : e.rhs.tail ≠ [] := by
      intro rhsSingleton
      exact hl (hsingleton.mpr rhsSingleton)
    have reducedPerm :
        (saturatedReduce e.lhs.toList).Perm
          (saturatedReduce e.rhs.toList) :=
      saturatedReduce_perm_of_support_eq hsupport
    have lhsNormal := saturatedDerivesNormal e.lhs hl
    have rhsNormal := saturatedDerivesNormal e.rhs hr
    cases hleft : saturatedReduce e.lhs.toList with
    | nil =>
        exact False.elim <| exponentReduce_cons_ne_nil
          e.lhs.head (e.lhs.tail ++ e.lhs.toList) <| by
            simpa [saturatedReduce, Word.toList, List.append_assoc] using hleft
    | cons x xs =>
        cases hright : saturatedReduce e.rhs.toList with
        | nil =>
            exact False.elim <| exponentReduce_cons_ne_nil
              e.rhs.head (e.rhs.tail ++ e.rhs.toList) <| by
                simpa [saturatedReduce, Word.toList,
                  List.append_assoc] using hright
        | cons y ys =>
            rw [hleft] at lhsNormal
            rw [hright] at rhsNormal
            rw [hleft, hright] at reducedPerm
            exact Derives.trans lhsNormal <|
              Derives.trans
                (saturatedDerivesPermutation
                  (wordOfCons x xs) (wordOfCons y ys) reducedPerm)
                (Derives.symm rhsNormal)

private theorem saturatedReversedAxiomsDerive
    (e : Identity Nat) (he : e ∈ reversedBasis saturatedSupportBasis) :
    Derives saturatedSupportBasis e.lhs e.rhs := by
  simp only [reversedBasis, saturatedSupportBasis, List.map_cons,
    List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · simpa [Identity.reversed, saturatedPowerLaw, saturatedXX,
      saturatedXXX, Word.reverse] using
        (Derives.fromBasis (e := saturatedPowerLaw) <|
          List.Mem.head _)
  · simpa [Identity.reversed, saturatedCommutativityLaw, saturatedXY,
      saturatedYX, Word.reverse] using
        Derives.symm
          (Derives.fromBasis (e := saturatedCommutativityLaw) <| by
            exact List.Mem.tail _ (List.Mem.head _))
  · have first :
        Derives saturatedSupportBasis saturatedYX saturatedXY :=
      Derives.symm <|
        Derives.fromBasis (e := saturatedCommutativityLaw) <| by
          exact List.Mem.tail _ (List.Mem.head _)
    have duplicate :
        Derives saturatedSupportBasis saturatedXY saturatedXXY :=
      Derives.fromBasis (e := saturatedPrefixDuplicationLaw) <| by
        exact List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _
    have move :
        Derives saturatedSupportBasis saturatedXXY ⟨1, [0, 0]⟩ := by
      simpa [saturatedXXY, saturatedYX, saturatedXX, Word.append,
        Word.singleton, Word.append_assoc] using
          saturatedDerivesCommutativity saturatedXX (Word.singleton 1)
    simpa [Identity.reversed, saturatedPrefixDuplicationLaw,
      saturatedXY, saturatedXXY, Word.reverse] using
        Derives.trans first (Derives.trans duplicate move)

theorem saturatedSupportBasis_opposite
    {T : FiniteTable}
    (complete : BasisFor T.semigroup saturatedSupportBasis)
    (oppositeModels :
      Models T.semigroup.opposite saturatedSupportBasis) :
    BasisFor T.semigroup.opposite saturatedSupportBasis :=
  complete.oppositeReversed.replace oppositeModels
    saturatedReversedAxiomsDerive

/-- Multiplication for the zero-based table
`[[1,1,1],[1,1,1],[1,1,3]]`. -/
def saturatedSupportThreeFiveMul (a b : Fin 3) : Fin 3 :=
  if a = 2 ∧ b = 2 then 2 else 0

/-- The exact Smallsemi representative `S3_5`. -/
def saturatedSupportThreeFive : FiniteTable where
  order := 3
  mul := saturatedSupportThreeFiveMul
  assoc := by decide

private theorem saturatedSupportThreeFiveMul_eq_two_iff
    (a b : Fin 3) :
    saturatedSupportThreeFiveMul a b = 2 ↔ a = 2 ∧ b = 2 := by
  decide +revert

private theorem saturatedSupportThreeFiveFold_eq_two_iff
    (valuation : Nat → Fin 3) (xs : List Nat) (acc : Fin 3) :
    xs.foldl
        (fun current x =>
          saturatedSupportThreeFiveMul current (valuation x)) acc = 2 ↔
      acc = 2 ∧ ∀ x, x ∈ xs → valuation x = 2 := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih,
        saturatedSupportThreeFiveMul_eq_two_iff]
      constructor
      · rintro ⟨⟨hacc, hx⟩, hrest⟩
        exact ⟨hacc, fun y hy => by
          rcases List.mem_cons.mp hy with rfl | hy
          · exact hx
          · exact hrest y hy⟩
      · rintro ⟨hacc, hall⟩
        exact ⟨⟨hacc, hall x (List.Mem.head xs)⟩,
          fun y hy => hall y (List.Mem.tail x hy)⟩

theorem saturatedSupportThreeFiveEval_eq_two_iff
    (valuation : Nat → Fin 3) (w : Word Nat) :
    saturatedSupportThreeFive.semigroup.eval valuation w =
        (2 : Fin 3) ↔
      ∀ x, x ∈ w.toList → valuation x = (2 : Fin 3) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              saturatedSupportThreeFiveMul current (valuation x))
            (valuation head) = 2 ↔
          ∀ x, x ∈ head :: tail → valuation x = 2
      rw [saturatedSupportThreeFiveFold_eq_two_iff]
      constructor
      · rintro ⟨hhead, htail⟩ x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hhead
        · exact htail x hx
      · intro hall
        exact ⟨hall head (List.Mem.head tail),
          fun x hx => hall x (List.Mem.tail head hx)⟩

private def saturatedSupportThreeFiveSeparator (z : Nat) : Nat → Fin 3 :=
  fun x => if x = z then 0 else 2

private theorem saturatedSupportThreeFiveSeparator_eq_two_iff
    (z : Nat) (w : Word Nat) :
    saturatedSupportThreeFive.semigroup.eval
        (saturatedSupportThreeFiveSeparator z) w = (2 : Fin 3) ↔
      z ∉ w.toList := by
  rw [saturatedSupportThreeFiveEval_eq_two_iff]
  constructor
  · intro hall hz
    have := hall z hz
    simp [saturatedSupportThreeFiveSeparator] at this
  · intro hz x hx
    have hne : x ≠ z := by
      intro h
      exact hz (h ▸ hx)
    simp [saturatedSupportThreeFiveSeparator, hne]

private theorem saturatedSupportThreeFiveSupportEq
    (e : Identity Nat)
    (valid : e.SatisfiedBy saturatedSupportThreeFive.semigroup) :
    ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList := by
  intro z
  have evaluated := valid (saturatedSupportThreeFiveSeparator z)
  constructor
  · intro hl
    apply Decidable.byContradiction
    intro hr
    have rhsTwo :=
      (saturatedSupportThreeFiveSeparator_eq_two_iff z e.rhs).2 hr
    have lhsNotTwo : saturatedSupportThreeFive.semigroup.eval
        (saturatedSupportThreeFiveSeparator z) e.lhs ≠ (2 : Fin 3) := by
      intro lhsTwo
      exact (saturatedSupportThreeFiveSeparator_eq_two_iff z e.lhs).1
        lhsTwo hl
    exact lhsNotTwo (evaluated.trans rhsTwo)
  · intro hr
    apply Decidable.byContradiction
    intro hl
    have lhsTwo :=
      (saturatedSupportThreeFiveSeparator_eq_two_iff z e.lhs).2 hl
    have rhsNotTwo : saturatedSupportThreeFive.semigroup.eval
        (saturatedSupportThreeFiveSeparator z) e.rhs ≠ (2 : Fin 3) := by
      intro rhsTwo
      exact (saturatedSupportThreeFiveSeparator_eq_two_iff z e.rhs).1
        rhsTwo hr
    exact rhsNotTwo (evaluated.symm.trans lhsTwo)

private def constantOne : Nat → Fin 3 := fun _ => 1

private theorem saturatedSupportThreeFiveFold_zero (xs : List Nat) :
    xs.foldl
        (fun current x =>
          saturatedSupportThreeFiveMul current (constantOne x)) 0 = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      simpa [saturatedSupportThreeFiveMul, constantOne] using ih

private theorem saturatedSupportThreeFiveSingleton_iff (w : Word Nat) :
    saturatedSupportThreeFive.semigroup.eval constantOne w =
        (1 : Fin 3) ↔
      w.tail = [] := by
  cases w with
  | mk head tail =>
      cases tail with
      | nil =>
          simp [FiniteTable.semigroup, Semigroup.eval, constantOne]
      | cons next rest =>
          simp only [List.cons_ne_nil, iff_false]
          simp only [saturatedSupportThreeFive, FiniteTable.semigroup,
            Semigroup.eval, List.foldl_cons]
          change
            rest.foldl
                (fun current x =>
                  saturatedSupportThreeFiveMul current (constantOne x))
                (saturatedSupportThreeFiveMul
                  (constantOne head) (constantOne next)) =
                (1 : Fin 3) → False
          rw [show saturatedSupportThreeFiveMul
              (constantOne head) (constantOne next) = (0 : Fin 3) by
                rfl]
          rw [saturatedSupportThreeFiveFold_zero]
          decide

private theorem saturatedSupportThreeFiveSingletonEq
    (e : Identity Nat)
    (valid : e.SatisfiedBy saturatedSupportThreeFive.semigroup) :
    e.lhs.tail = [] ↔ e.rhs.tail = [] := by
  have evaluated := valid constantOne
  rw [← saturatedSupportThreeFiveSingleton_iff,
    ← saturatedSupportThreeFiveSingleton_iff]
  rw [evaluated]

private theorem saturatedSupportThreeFiveMul_power (a : Fin 3) :
    saturatedSupportThreeFiveMul a a =
      saturatedSupportThreeFiveMul
        (saturatedSupportThreeFiveMul a a) a := by
  decide +revert

private theorem saturatedSupportThreeFiveMul_commutative
    (a b : Fin 3) :
    saturatedSupportThreeFiveMul a b =
      saturatedSupportThreeFiveMul b a := by
  decide +revert

private theorem saturatedSupportThreeFiveMul_prefixDuplication
    (a b : Fin 3) :
    saturatedSupportThreeFiveMul a b =
      saturatedSupportThreeFiveMul
        (saturatedSupportThreeFiveMul a a) b := by
  decide +revert

private theorem saturatedSupportThreeFiveModels :
    Models saturatedSupportThreeFive.semigroup saturatedSupportBasis := by
  intro e he
  simp only [saturatedSupportBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl | rfl
  · intro valuation
    change saturatedSupportThreeFiveMul (valuation 0) (valuation 0) =
      saturatedSupportThreeFiveMul
        (saturatedSupportThreeFiveMul (valuation 0) (valuation 0))
        (valuation 0)
    exact saturatedSupportThreeFiveMul_power (valuation 0)
  · intro valuation
    change saturatedSupportThreeFiveMul (valuation 0) (valuation 1) =
      saturatedSupportThreeFiveMul (valuation 1) (valuation 0)
    exact saturatedSupportThreeFiveMul_commutative
      (valuation 0) (valuation 1)
  · intro valuation
    change saturatedSupportThreeFiveMul (valuation 0) (valuation 1) =
      saturatedSupportThreeFiveMul
        (saturatedSupportThreeFiveMul (valuation 0) (valuation 0))
        (valuation 1)
    exact saturatedSupportThreeFiveMul_prefixDuplication
      (valuation 0) (valuation 1)

theorem saturatedSupportThreeFiveBasis_complete :
    BasisFor saturatedSupportThreeFive.semigroup saturatedSupportBasis :=
  saturatedSupportBasis_complete_of saturatedSupportThreeFive
    saturatedSupportThreeFiveModels
    saturatedSupportThreeFiveSupportEq
    saturatedSupportThreeFiveSingletonEq

private theorem saturatedSupportThreeFiveOppositeModels :
    Models saturatedSupportThreeFive.semigroup.opposite
      saturatedSupportBasis := by
  intro e he
  simp only [saturatedSupportBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl | rfl
  · intro valuation
    change saturatedSupportThreeFiveMul (valuation 0) (valuation 0) =
      saturatedSupportThreeFiveMul
        (valuation 0)
        (saturatedSupportThreeFiveMul (valuation 0) (valuation 0))
    exact (saturatedSupportThreeFiveMul_power (valuation 0)).trans <|
      saturatedSupportThreeFiveMul_commutative
        (saturatedSupportThreeFiveMul (valuation 0) (valuation 0))
        (valuation 0)
  · intro valuation
    change saturatedSupportThreeFiveMul (valuation 1) (valuation 0) =
      saturatedSupportThreeFiveMul (valuation 0) (valuation 1)
    exact saturatedSupportThreeFiveMul_commutative
      (valuation 1) (valuation 0)
  · intro valuation
    change saturatedSupportThreeFiveMul (valuation 1) (valuation 0) =
      saturatedSupportThreeFiveMul
        (valuation 1)
        (saturatedSupportThreeFiveMul (valuation 0) (valuation 0))
    rw [saturatedSupportThreeFiveMul_commutative
      (valuation 1) (valuation 0)]
    exact (saturatedSupportThreeFiveMul_prefixDuplication
      (valuation 0) (valuation 1)).trans <|
        saturatedSupportThreeFiveMul_commutative
          (saturatedSupportThreeFiveMul (valuation 0) (valuation 0))
          (valuation 1)

theorem saturatedSupportThreeFiveOppositeBasis_complete :
    BasisFor saturatedSupportThreeFive.semigroup.opposite
      saturatedSupportBasis :=
  saturatedSupportBasis_opposite
    saturatedSupportThreeFiveBasis_complete
    saturatedSupportThreeFiveOppositeModels

/-- Multiplication for the zero-based table
`[[1,1,3],[1,1,3],[3,3,3]]`. -/
def saturatedSupportThreeNineMul (a b : Fin 3) : Fin 3 :=
  if a = 2 ∨ b = 2 then 2 else 0

/-- The exact Smallsemi representative `S3_9`. -/
def saturatedSupportThreeNine : FiniteTable where
  order := 3
  mul := saturatedSupportThreeNineMul
  assoc := by decide

private theorem saturatedSupportThreeNineMul_eq_two_iff
    (a b : Fin 3) :
    saturatedSupportThreeNineMul a b = 2 ↔ a = 2 ∨ b = 2 := by
  decide +revert

private theorem saturatedSupportThreeNineFold_eq_two_iff
    (valuation : Nat → Fin 3) (xs : List Nat) (acc : Fin 3) :
    xs.foldl
        (fun current x =>
          saturatedSupportThreeNineMul current (valuation x)) acc = 2 ↔
      acc = 2 ∨ ∃ x, x ∈ xs ∧ valuation x = 2 := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih,
        saturatedSupportThreeNineMul_eq_two_iff]
      constructor
      · rintro ((hacc | hx) | ⟨y, hy, hval⟩)
        · exact Or.inl hacc
        · exact Or.inr ⟨x, List.Mem.head xs, hx⟩
        · exact Or.inr ⟨y, List.Mem.tail x hy, hval⟩
      · rintro (hacc | ⟨y, hy, hval⟩)
        · exact Or.inl (Or.inl hacc)
        · rcases List.mem_cons.mp hy with rfl | hy
          · exact Or.inl (Or.inr hval)
          · exact Or.inr ⟨y, hy, hval⟩

theorem saturatedSupportThreeNineEval_eq_two_iff
    (valuation : Nat → Fin 3) (w : Word Nat) :
    saturatedSupportThreeNine.semigroup.eval valuation w =
        (2 : Fin 3) ↔
      ∃ x, x ∈ w.toList ∧ valuation x = (2 : Fin 3) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              saturatedSupportThreeNineMul current (valuation x))
            (valuation head) = 2 ↔
          ∃ x, x ∈ head :: tail ∧ valuation x = 2
      rw [saturatedSupportThreeNineFold_eq_two_iff]
      constructor
      · rintro (hhead | ⟨x, hx, hval⟩)
        · exact ⟨head, List.Mem.head tail, hhead⟩
        · exact ⟨x, List.Mem.tail head hx, hval⟩
      · rintro ⟨x, hx, hval⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Or.inl hval
        · exact Or.inr ⟨x, hx, hval⟩

private def saturatedSupportThreeNineSeparator (z : Nat) : Nat → Fin 3 :=
  fun x => if x = z then 2 else 0

private theorem saturatedSupportThreeNineSeparator_eq_two_iff
    (z : Nat) (w : Word Nat) :
    saturatedSupportThreeNine.semigroup.eval
        (saturatedSupportThreeNineSeparator z) w = (2 : Fin 3) ↔
      z ∈ w.toList := by
  rw [saturatedSupportThreeNineEval_eq_two_iff]
  constructor
  · rintro ⟨x, hx, hval⟩
    by_cases hxz : x = z
    · simpa [hxz] using hx
    · simp [saturatedSupportThreeNineSeparator, hxz] at hval
  · intro hz
    exact ⟨z, hz, by simp [saturatedSupportThreeNineSeparator]⟩

private theorem saturatedSupportThreeNineSupportEq
    (e : Identity Nat)
    (valid : e.SatisfiedBy saturatedSupportThreeNine.semigroup) :
    ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList := by
  intro z
  have evaluated := valid (saturatedSupportThreeNineSeparator z)
  constructor
  · intro hl
    apply Decidable.byContradiction
    intro hr
    have lhsTwo :=
      (saturatedSupportThreeNineSeparator_eq_two_iff z e.lhs).2 hl
    have rhsNotTwo : saturatedSupportThreeNine.semigroup.eval
        (saturatedSupportThreeNineSeparator z) e.rhs ≠ (2 : Fin 3) := by
      intro rhsTwo
      exact hr
        ((saturatedSupportThreeNineSeparator_eq_two_iff z e.rhs).1 rhsTwo)
    exact rhsNotTwo (evaluated.symm.trans lhsTwo)
  · intro hr
    apply Decidable.byContradiction
    intro hl
    have rhsTwo :=
      (saturatedSupportThreeNineSeparator_eq_two_iff z e.rhs).2 hr
    have lhsNotTwo : saturatedSupportThreeNine.semigroup.eval
        (saturatedSupportThreeNineSeparator z) e.lhs ≠ (2 : Fin 3) := by
      intro lhsTwo
      exact hl
        ((saturatedSupportThreeNineSeparator_eq_two_iff z e.lhs).1 lhsTwo)
    exact lhsNotTwo (evaluated.trans rhsTwo)

private theorem saturatedSupportThreeNineFold_zero (xs : List Nat) :
    xs.foldl
        (fun current x =>
          saturatedSupportThreeNineMul current (constantOne x)) 0 = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      simpa [saturatedSupportThreeNineMul, constantOne] using ih

private theorem saturatedSupportThreeNineSingleton_iff (w : Word Nat) :
    saturatedSupportThreeNine.semigroup.eval constantOne w =
        (1 : Fin 3) ↔
      w.tail = [] := by
  cases w with
  | mk head tail =>
      cases tail with
      | nil =>
          simp [FiniteTable.semigroup, Semigroup.eval, constantOne]
      | cons next rest =>
          simp only [List.cons_ne_nil, iff_false]
          simp only [saturatedSupportThreeNine, FiniteTable.semigroup,
            Semigroup.eval, List.foldl_cons]
          change
            rest.foldl
                (fun current x =>
                  saturatedSupportThreeNineMul current (constantOne x))
                (saturatedSupportThreeNineMul
                  (constantOne head) (constantOne next)) =
                (1 : Fin 3) → False
          rw [show saturatedSupportThreeNineMul
              (constantOne head) (constantOne next) = (0 : Fin 3) by
                rfl]
          rw [saturatedSupportThreeNineFold_zero]
          decide

private theorem saturatedSupportThreeNineSingletonEq
    (e : Identity Nat)
    (valid : e.SatisfiedBy saturatedSupportThreeNine.semigroup) :
    e.lhs.tail = [] ↔ e.rhs.tail = [] := by
  have evaluated := valid constantOne
  rw [← saturatedSupportThreeNineSingleton_iff,
    ← saturatedSupportThreeNineSingleton_iff]
  rw [evaluated]

private theorem saturatedSupportThreeNineMul_power (a : Fin 3) :
    saturatedSupportThreeNineMul a a =
      saturatedSupportThreeNineMul
        (saturatedSupportThreeNineMul a a) a := by
  decide +revert

private theorem saturatedSupportThreeNineMul_commutative
    (a b : Fin 3) :
    saturatedSupportThreeNineMul a b =
      saturatedSupportThreeNineMul b a := by
  decide +revert

private theorem saturatedSupportThreeNineMul_prefixDuplication
    (a b : Fin 3) :
    saturatedSupportThreeNineMul a b =
      saturatedSupportThreeNineMul
        (saturatedSupportThreeNineMul a a) b := by
  decide +revert

private theorem saturatedSupportThreeNineModels :
    Models saturatedSupportThreeNine.semigroup saturatedSupportBasis := by
  intro e he
  simp only [saturatedSupportBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl | rfl
  · intro valuation
    change saturatedSupportThreeNineMul (valuation 0) (valuation 0) =
      saturatedSupportThreeNineMul
        (saturatedSupportThreeNineMul (valuation 0) (valuation 0))
        (valuation 0)
    exact saturatedSupportThreeNineMul_power (valuation 0)
  · intro valuation
    change saturatedSupportThreeNineMul (valuation 0) (valuation 1) =
      saturatedSupportThreeNineMul (valuation 1) (valuation 0)
    exact saturatedSupportThreeNineMul_commutative
      (valuation 0) (valuation 1)
  · intro valuation
    change saturatedSupportThreeNineMul (valuation 0) (valuation 1) =
      saturatedSupportThreeNineMul
        (saturatedSupportThreeNineMul (valuation 0) (valuation 0))
        (valuation 1)
    exact saturatedSupportThreeNineMul_prefixDuplication
      (valuation 0) (valuation 1)

theorem saturatedSupportThreeNineBasis_complete :
    BasisFor saturatedSupportThreeNine.semigroup saturatedSupportBasis :=
  saturatedSupportBasis_complete_of saturatedSupportThreeNine
    saturatedSupportThreeNineModels
    saturatedSupportThreeNineSupportEq
    saturatedSupportThreeNineSingletonEq

private theorem saturatedSupportThreeNineOppositeModels :
    Models saturatedSupportThreeNine.semigroup.opposite
      saturatedSupportBasis := by
  intro e he
  simp only [saturatedSupportBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl | rfl
  · intro valuation
    change saturatedSupportThreeNineMul (valuation 0) (valuation 0) =
      saturatedSupportThreeNineMul
        (valuation 0)
        (saturatedSupportThreeNineMul (valuation 0) (valuation 0))
    exact (saturatedSupportThreeNineMul_power (valuation 0)).trans <|
      saturatedSupportThreeNineMul_commutative
        (saturatedSupportThreeNineMul (valuation 0) (valuation 0))
        (valuation 0)
  · intro valuation
    change saturatedSupportThreeNineMul (valuation 1) (valuation 0) =
      saturatedSupportThreeNineMul (valuation 0) (valuation 1)
    exact saturatedSupportThreeNineMul_commutative
      (valuation 1) (valuation 0)
  · intro valuation
    change saturatedSupportThreeNineMul (valuation 1) (valuation 0) =
      saturatedSupportThreeNineMul
        (valuation 1)
        (saturatedSupportThreeNineMul (valuation 0) (valuation 0))
    rw [saturatedSupportThreeNineMul_commutative
      (valuation 1) (valuation 0)]
    exact (saturatedSupportThreeNineMul_prefixDuplication
      (valuation 0) (valuation 1)).trans <|
        saturatedSupportThreeNineMul_commutative
          (saturatedSupportThreeNineMul (valuation 0) (valuation 0))
          (valuation 1)

theorem saturatedSupportThreeNineOppositeBasis_complete :
    BasisFor saturatedSupportThreeNine.semigroup.opposite
      saturatedSupportBasis :=
  saturatedSupportBasis_opposite
    saturatedSupportThreeNineBasis_complete
    saturatedSupportThreeNineOppositeModels

end SemigroupBasis.Examples
