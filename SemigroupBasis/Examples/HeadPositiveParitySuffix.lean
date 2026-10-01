import SemigroupBasis.Examples.CommutativeParityThree
import SemigroupBasis.Examples.CommutativePeriodTwoFromTwo

namespace SemigroupBasis.Examples

open SemigroupBasis

def headPositiveParitySuffixXX : Word Nat := ⟨0, [0]⟩
def headPositiveParitySuffixXXXX : Word Nat := ⟨0, [0, 0, 0]⟩
def headPositiveParitySuffixXY : Word Nat := ⟨0, [1]⟩
def headPositiveParitySuffixXYYY : Word Nat := ⟨0, [1, 1, 1]⟩
def headPositiveParitySuffixXXY : Word Nat := ⟨0, [0, 1]⟩
def headPositiveParitySuffixXYX : Word Nat := ⟨0, [1, 0]⟩
def headPositiveParitySuffixXYZ : Word Nat := ⟨0, [1, 2]⟩
def headPositiveParitySuffixXZY : Word Nat := ⟨0, [2, 1]⟩

def headPositiveParitySuffixHeadPowerLaw : Identity Nat :=
  ⟨headPositiveParitySuffixXX, headPositiveParitySuffixXXXX⟩

def headPositiveParitySuffixContextPowerLaw : Identity Nat :=
  ⟨headPositiveParitySuffixXY, headPositiveParitySuffixXYYY⟩

def headPositiveParitySuffixGatherLaw : Identity Nat :=
  ⟨headPositiveParitySuffixXXY, headPositiveParitySuffixXYX⟩

def headPositiveParitySuffixSwapLaw : Identity Nat :=
  ⟨headPositiveParitySuffixXYZ, headPositiveParitySuffixXZY⟩

/-- The two laws used by the normalization proof. The displayed head-power
and gather laws are substitution instances of these laws. -/
def headPositiveParitySuffixCoreBasis : List (Identity Nat) :=
  [headPositiveParitySuffixContextPowerLaw,
    headPositiveParitySuffixSwapLaw]

/-- The exact stored basis
`xx = xxxx`, `xy = xyyy`, `xxy = xyx`, and `xyz = xzy`. -/
def headPositiveParitySuffixBasis : List (Identity Nat) :=
  [headPositiveParitySuffixHeadPowerLaw,
    headPositiveParitySuffixContextPowerLaw,
    headPositiveParitySuffixGatherLaw,
    headPositiveParitySuffixSwapLaw]

private def headPositiveParitySuffixInstantiate
    (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

/-- Three copies of a nonempty block may be contracted after any nonempty
prefix. -/
theorem headPositiveParitySuffixDerivesSuffixTripleContraction
    (p u : Word Nat) :
    Derives headPositiveParitySuffixCoreBasis
      (((p ++ u) ++ u) ++ u) (p ++ u) := by
  have base :
      Derives headPositiveParitySuffixCoreBasis
        headPositiveParitySuffixXYYY
        headPositiveParitySuffixXY :=
    Derives.symm <|
      Derives.fromBasis
        (e := headPositiveParitySuffixContextPowerLaw) <|
        List.Mem.head _
  have instantiated :=
    Derives.subst base
      (headPositiveParitySuffixInstantiate p u u)
  simpa [headPositiveParitySuffixCoreBasis,
    headPositiveParitySuffixContextPowerLaw,
    headPositiveParitySuffixXYYY,
    headPositiveParitySuffixXY,
    headPositiveParitySuffixInstantiate, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using instantiated

/-- The displayed law `xx = xxxx` follows by taking the suffix block equal
to the prefix block in `xy = xyyy`. -/
theorem headPositiveParitySuffixDerivesHeadPower (u : Word Nat) :
    Derives headPositiveParitySuffixCoreBasis
      (u ++ u) (((u ++ u) ++ u) ++ u) := by
  simpa [Word.append_assoc] using
    (headPositiveParitySuffixDerivesSuffixTripleContraction u u).symm

/-- The displayed law `xxy = xyx` follows by swapping two suffix blocks. -/
theorem headPositiveParitySuffixDerivesGather (u v : Word Nat) :
    Derives headPositiveParitySuffixCoreBasis
      ((u ++ u) ++ v) ((u ++ v) ++ u) := by
  have base :
      Derives headPositiveParitySuffixCoreBasis
        headPositiveParitySuffixXYZ
        headPositiveParitySuffixXZY :=
    Derives.fromBasis
      (e := headPositiveParitySuffixSwapLaw) <|
      List.Mem.tail _ (List.Mem.head _)
  have instantiated :=
    Derives.subst base
      (headPositiveParitySuffixInstantiate u u v)
  simpa [headPositiveParitySuffixCoreBasis,
    headPositiveParitySuffixSwapLaw,
    headPositiveParitySuffixXYZ,
    headPositiveParitySuffixXZY,
    headPositiveParitySuffixInstantiate, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using instantiated

/-- Arbitrary nonempty blocks in the suffix may be swapped. -/
theorem headPositiveParitySuffixDerivesSuffixSwap
    (p u v : Word Nat) :
    Derives headPositiveParitySuffixCoreBasis
      ((p ++ u) ++ v) ((p ++ v) ++ u) := by
  have base :
      Derives headPositiveParitySuffixCoreBasis
        headPositiveParitySuffixXYZ
        headPositiveParitySuffixXZY :=
    Derives.fromBasis
      (e := headPositiveParitySuffixSwapLaw) <|
      List.Mem.tail _ (List.Mem.head _)
  have instantiated :=
    Derives.subst base
      (headPositiveParitySuffixInstantiate p u v)
  simpa [headPositiveParitySuffixCoreBasis,
    headPositiveParitySuffixSwapLaw,
    headPositiveParitySuffixXYZ,
    headPositiveParitySuffixXZY,
    headPositiveParitySuffixInstantiate, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using instantiated

/-- Every exact basis axiom is derivable from the two-law core. -/
theorem headPositiveParitySuffixExactAxiomsDeriveCore
    (e : Identity Nat) (member : e ∈ headPositiveParitySuffixBasis) :
    Derives headPositiveParitySuffixCoreBasis e.lhs e.rhs := by
  simp only [headPositiveParitySuffixBasis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · simpa [headPositiveParitySuffixHeadPowerLaw,
      headPositiveParitySuffixXX,
      headPositiveParitySuffixXXXX,
      Word.append, Word.singleton, Word.append_assoc] using
      headPositiveParitySuffixDerivesHeadPower (Word.singleton 0)
  · exact Derives.fromBasis (List.Mem.head _)
  · simpa [headPositiveParitySuffixGatherLaw,
      headPositiveParitySuffixXXY,
      headPositiveParitySuffixXYX,
      Word.append, Word.singleton, Word.append_assoc] using
      headPositiveParitySuffixDerivesGather
        (Word.singleton 0) (Word.singleton 1)
  · exact Derives.fromBasis <|
      List.Mem.tail _ (List.Mem.head _)

/-- Every core axiom is present in the exact four-law basis. -/
theorem headPositiveParitySuffixCoreAxiomsDeriveExact
    (e : Identity Nat)
    (member : e ∈ headPositiveParitySuffixCoreBasis) :
    Derives headPositiveParitySuffixBasis e.lhs e.rhs := by
  simp only [headPositiveParitySuffixCoreBasis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact Derives.fromBasis <|
      List.Mem.tail _ (List.Mem.head _)
  · exact Derives.fromBasis <|
      List.Mem.tail _ <|
        List.Mem.tail _ <|
          List.Mem.tail _ (List.Mem.head _)

private def headPositiveParitySuffixWordOfCons
    (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

/-- Every permutation strictly behind a fixed head is derivable. -/
theorem headPositiveParitySuffixDerivesTailPermutation
    (head : Nat) {xs ys : List Nat} (permutation : xs.Perm ys) :
    Derives headPositiveParitySuffixCoreBasis
      (headPositiveParitySuffixWordOfCons head xs)
      (headPositiveParitySuffixWordOfCons head ys) := by
  induction permutation generalizing head with
  | nil =>
      exact Derives.refl _
  | cons x _ ih =>
      have suffix := ih (head := x)
      simpa [headPositiveParitySuffixWordOfCons,
        Word.singleton, Word.append] using
        Derives.prepend (Word.singleton head) suffix
  | swap x y xs =>
      cases xs with
      | nil =>
          simpa [headPositiveParitySuffixWordOfCons,
            Word.singleton, Word.append, Word.append_assoc] using
            headPositiveParitySuffixDerivesSuffixSwap
              (Word.singleton head) (Word.singleton y)
              (Word.singleton x)
      | cons z zs =>
          have swapped :=
            Derives.appendRight
              (headPositiveParitySuffixDerivesSuffixSwap
                (Word.singleton head) (Word.singleton y)
                (Word.singleton x))
              (headPositiveParitySuffixWordOfCons z zs)
          simpa [headPositiveParitySuffixWordOfCons,
            Word.singleton, Word.append, Word.append_assoc] using
            swapped
  | trans _ _ ih₁ ih₂ =>
      exact Derives.trans
        (ih₁ (head := head)) (ih₂ (head := head))

private theorem headPositiveParitySuffixContractTailTriple
    (head x : Nat) (suffix : List Nat) :
    Derives headPositiveParitySuffixCoreBasis
      (headPositiveParitySuffixWordOfCons
        head (x :: x :: x :: suffix))
      (headPositiveParitySuffixWordOfCons head (x :: suffix)) := by
  cases suffix with
  | nil =>
      simpa [headPositiveParitySuffixWordOfCons,
        Word.append, Word.singleton, Word.append_assoc] using
        headPositiveParitySuffixDerivesSuffixTripleContraction
          (Word.singleton head) (Word.singleton x)
  | cons y ys =>
      have contracted :=
        Derives.appendRight
          (headPositiveParitySuffixDerivesSuffixTripleContraction
            (Word.singleton head) (Word.singleton x))
          (headPositiveParitySuffixWordOfCons y ys)
      simpa [headPositiveParitySuffixWordOfCons,
        Word.append, Word.singleton, Word.append_assoc] using contracted

private theorem headPositiveParitySuffixDeleteThirdCopy
    (head x : Nat) (before rest : List Nat)
    (count : rest.count x = 2) :
    Derives headPositiveParitySuffixCoreBasis
      (headPositiveParitySuffixWordOfCons
        head (before ++ x :: rest))
      (headPositiveParitySuffixWordOfCons
        head (before ++ rest.erase x)) := by
  let remainder := (rest.erase x).erase x
  have sourcePermutation :
      (before ++ x :: rest).Perm
        (x :: x :: x :: before ++ remainder) := by
    rw [List.perm_iff_count]
    intro z
    simp only [List.count_append]
    by_cases hz : z = x
    · subst z
      simp only [List.count_cons_self]
      have firstErase : (rest.erase x).count x = 1 := by
        rw [List.count_erase_self, count]
      have secondErase :
          ((rest.erase x).erase x).count x = 0 := by
        rw [List.count_erase_self, firstErase]
      simp only [remainder, secondErase, count]
    · simp only [List.count_cons_of_ne (Ne.symm hz),
        List.count_erase_of_ne hz, remainder]
  have targetPermutation :
      (before ++ rest.erase x).Perm
        (x :: before ++ remainder) := by
    rw [List.perm_iff_count]
    intro z
    simp only [List.count_append]
    by_cases hz : z = x
    · subst z
      simp only [List.count_cons_self]
      have firstErase : (rest.erase x).count x = 1 := by
        rw [List.count_erase_self, count]
      have secondErase :
          ((rest.erase x).erase x).count x = 0 := by
        rw [List.count_erase_self, firstErase]
      simp only [remainder, secondErase]
      rw [firstErase]
    · simp only [List.count_cons_of_ne (Ne.symm hz),
        List.count_erase_of_ne hz, remainder]
  exact Derives.trans
    (headPositiveParitySuffixDerivesTailPermutation
      head sourcePermutation) <|
    Derives.trans
      (headPositiveParitySuffixContractTailTriple
        head x (before ++ remainder)) <|
      headPositiveParitySuffixDerivesTailPermutation
        head targetPermutation.symm

private theorem headPositiveParitySuffixDerivesNormalizeTail :
    ∀ head before xs,
      Derives headPositiveParitySuffixCoreBasis
        (headPositiveParitySuffixWordOfCons head (before ++ xs))
        (headPositiveParitySuffixWordOfCons
          head (before ++ positiveParityReduce xs))
  | head, before, [] =>
      Derives.refl _
  | head, before, x :: xs => by
      have suffixNormal :=
        headPositiveParitySuffixDerivesNormalizeTail
          head (before ++ [x]) xs
      let reduced := positiveParityReduce xs
      have firstStep :
          Derives headPositiveParitySuffixCoreBasis
            (headPositiveParitySuffixWordOfCons
              head (before ++ x :: xs))
            (headPositiveParitySuffixWordOfCons
              head (before ++ x :: reduced)) := by
        simpa [reduced, List.append_assoc] using suffixNormal
      by_cases hcount : reduced.count x < 2
      · have reducedEq :
            positiveParityReduce (x :: xs) = x :: reduced := by
          simp [positiveParityReduce, reduced, hcount]
        rw [reducedEq]
        exact firstStep
      · have countLe : reduced.count x ≤ 2 := by
          simpa [reduced] using
            positiveParityReduce_count_le_two x xs
        have countEq : reduced.count x = 2 := by
          omega
        have reducedEq :
            positiveParityReduce (x :: xs) = reduced.erase x := by
          simp [positiveParityReduce, reduced, hcount]
        rw [reducedEq]
        exact Derives.trans firstStep <|
          headPositiveParitySuffixDeleteThirdCopy
            head x before reduced countEq
termination_by
  _ _ xs => xs.length

/-- Canonical fixed-head representative. Every suffix variable is absent,
represented once for positive odd multiplicity, or represented twice for
positive even multiplicity. -/
def headPositiveParitySuffixNormal (w : Word Nat) : Word Nat :=
  ⟨w.head, positiveParityReduce w.tail⟩

theorem headPositiveParitySuffixDerivesNormal (w : Word Nat) :
    Derives headPositiveParitySuffixCoreBasis w
      (headPositiveParitySuffixNormal w) := by
  cases w with
  | mk head tail =>
      simpa [headPositiveParitySuffixNormal,
        headPositiveParitySuffixWordOfCons] using
        headPositiveParitySuffixDerivesNormalizeTail
          head [] tail

private theorem
    headPositiveParitySuffixHeadState_eq_one_iff (n : Nat) :
    periodTwoFromTwoExponent (n + 1) = 1 ↔ n = 0 := by
  by_cases hn : n = 0
  · subst n
    simp [periodTwoFromTwoExponent]
  · have hlarge : ¬n + 1 < 2 := by
      omega
    simp only [periodTwoFromTwoExponent, hlarge, if_false]
    constructor
    · intro impossible
      omega
    · intro zero
      exact (hn zero).elim

private theorem headPositiveParitySuffixModTwoOfSuccModTwoEq
    (m n : Nat)
    (equal : (m + 1) % 2 = (n + 1) % 2) :
    m % 2 = n % 2 := by
  have mLt : m % 2 < 2 := Nat.mod_lt _ (by decide)
  have nLt : n % 2 < 2 := Nat.mod_lt _ (by decide)
  have mCases : m % 2 = 0 ∨ m % 2 = 1 := by
    omega
  have nCases : n % 2 = 0 ∨ n % 2 = 1 := by
    omega
  rcases mCases with mZero | mOne
  · rcases nCases with nZero | nOne
    · simpa [mZero, nZero]
    · have impossible : False := by
        simpa [Nat.add_mod, mZero, nOne] using equal
      exact impossible.elim
  · rcases nCases with nZero | nOne
    · have impossible : False := by
        simpa [Nat.add_mod, mOne, nZero] using equal
      exact impossible.elim
    · simpa [mOne, nOne]

private theorem headPositiveParitySuffixNormalTailPerm
    (u v : Word Nat)
    (heads : u.head = v.head)
    (support :
      ∀ z, z ∈ u.toList ↔ z ∈ v.toList)
    (parity :
      ∀ z, u.toList.count z % 2 =
        v.toList.count z % 2)
    (headState :
      periodTwoFromTwoExponent (u.toList.count u.head) =
        periodTwoFromTwoExponent (v.toList.count v.head)) :
    (headPositiveParitySuffixNormal u).tail.Perm
      (headPositiveParitySuffixNormal v).tail := by
  change
    (positiveParityReduce u.tail).Perm
      (positiveParityReduce v.tail)
  apply positiveParityReduce_perm
  · intro z
    cases u with
    | mk uHead uTail =>
        cases v with
        | mk vHead vTail =>
            simp only at heads support parity headState
            subst vHead
            by_cases hz : z = uHead
            · subst z
              have states := headState
              simp only [Word.toList, List.count_cons_self] at states
              have zeroEq :
                  uTail.count uHead = 0 ↔
                    vTail.count uHead = 0 := by
                constructor
                · intro leftZero
                  have leftOne :
                      periodTwoFromTwoExponent
                          (uTail.count uHead + 1) = 1 :=
                    (headPositiveParitySuffixHeadState_eq_one_iff
                      (uTail.count uHead)).2 leftZero
                  have rightOne :
                      periodTwoFromTwoExponent
                          (vTail.count uHead + 1) = 1 :=
                    states.symm.trans leftOne
                  exact
                    (headPositiveParitySuffixHeadState_eq_one_iff
                      (vTail.count uHead)).1 rightOne
                · intro rightZero
                  have rightOne :
                      periodTwoFromTwoExponent
                          (vTail.count uHead + 1) = 1 :=
                    (headPositiveParitySuffixHeadState_eq_one_iff
                      (vTail.count uHead)).2 rightZero
                  have leftOne :
                      periodTwoFromTwoExponent
                          (uTail.count uHead + 1) = 1 :=
                    states.trans rightOne
                  exact
                    (headPositiveParitySuffixHeadState_eq_one_iff
                      (uTail.count uHead)).1 leftOne
              constructor
              · intro leftMem
                have leftNe :
                    uTail.count uHead ≠ 0 :=
                  Nat.ne_of_gt (List.count_pos_iff.mpr leftMem)
                have rightNe :
                    vTail.count uHead ≠ 0 :=
                  fun rightZero =>
                    leftNe (zeroEq.mpr rightZero)
                exact List.count_pos_iff.mp
                  (Nat.pos_of_ne_zero rightNe)
              · intro rightMem
                have rightNe :
                    vTail.count uHead ≠ 0 :=
                  Nat.ne_of_gt (List.count_pos_iff.mpr rightMem)
                have leftNe :
                    uTail.count uHead ≠ 0 :=
                  fun leftZero =>
                    rightNe (zeroEq.mp leftZero)
                exact List.count_pos_iff.mp
                  (Nat.pos_of_ne_zero leftNe)
            · have wholeSupport := support z
              simpa [Word.toList, hz, Ne.symm hz] using
                wholeSupport
  · intro z
    cases u with
    | mk uHead uTail =>
        cases v with
        | mk vHead vTail =>
            simp only at heads support parity headState
            subst vHead
            have wholeParity := parity z
            by_cases hz : z = uHead
            · subst z
              simp only [Word.toList,
                List.count_cons_self] at wholeParity
              exact
                headPositiveParitySuffixModTwoOfSuccModTwoEq
                  _ _ wholeParity
            · simpa [Word.toList,
                List.count_cons_of_ne (Ne.symm hz)] using
                wholeParity

/-- Normal representatives have permutationally equal tails whenever their
fixed heads, support, total parity, and head exponent states agree. -/
theorem headPositiveParitySuffixNormal_tail_perm
    (u v : Word Nat)
    (heads : u.head = v.head)
    (support :
      ∀ z, z ∈ u.toList ↔ z ∈ v.toList)
    (parity :
      ∀ z, u.toList.count z % 2 =
        v.toList.count z % 2)
    (headState :
      periodTwoFromTwoExponent (u.toList.count u.head) =
        periodTwoFromTwoExponent (v.toList.count v.head)) :
    (headPositiveParitySuffixNormal u).tail.Perm
      (headPositiveParitySuffixNormal v).tail :=
  headPositiveParitySuffixNormalTailPerm
    u v heads support parity headState

theorem headPositiveParitySuffixDerivesOfInvariantEq
    (u v : Word Nat)
    (heads : u.head = v.head)
    (support :
      ∀ z, z ∈ u.toList ↔ z ∈ v.toList)
    (parity :
      ∀ z, u.toList.count z % 2 =
        v.toList.count z % 2)
    (headState :
      periodTwoFromTwoExponent (u.toList.count u.head) =
        periodTwoFromTwoExponent (v.toList.count v.head)) :
    Derives headPositiveParitySuffixCoreBasis u v := by
  have leftNormal :=
    headPositiveParitySuffixDerivesNormal u
  have rightNormal :=
    headPositiveParitySuffixDerivesNormal v
  have middle :
      Derives headPositiveParitySuffixCoreBasis
        (headPositiveParitySuffixNormal u)
        (headPositiveParitySuffixNormal v) := by
    simpa [headPositiveParitySuffixNormal,
      headPositiveParitySuffixWordOfCons, heads] using
      headPositiveParitySuffixDerivesTailPermutation
        u.head
        (headPositiveParitySuffixNormalTailPerm
          u v heads support parity headState)
  exact Derives.trans leftNormal <|
    Derives.trans middle (Derives.symm rightNormal)

private theorem headPositiveParitySuffixCoreModelsOfExact
    {S : Type} (G : Semigroup S)
    (models : Models G headPositiveParitySuffixBasis) :
    Models G headPositiveParitySuffixCoreBasis := by
  intro e member
  simp only [headPositiveParitySuffixCoreBasis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact models headPositiveParitySuffixContextPowerLaw <|
      List.Mem.tail _ (List.Mem.head _)
  · exact models headPositiveParitySuffixSwapLaw <|
      List.Mem.tail _ <|
        List.Mem.tail _ <|
          List.Mem.tail _ (List.Mem.head _)

theorem headPositiveParitySuffixCoreBasis_complete_of_separates
    (T : FiniteTable)
    (models : Models T.semigroup headPositiveParitySuffixCoreBasis)
    (separatesHead :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        e.lhs.head = e.rhs.head)
    (separatesSupport :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList)
    (separatesParity :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        ∀ z, e.lhs.toList.count z % 2 =
          e.rhs.toList.count z % 2)
    (separatesHeadState :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        periodTwoFromTwoExponent
            (e.lhs.toList.count e.lhs.head) =
          periodTwoFromTwoExponent
            (e.rhs.toList.count e.rhs.head)) :
    BasisFor T.semigroup headPositiveParitySuffixCoreBasis := by
  refine ⟨models, ?_⟩
  intro e valid
  exact headPositiveParitySuffixDerivesOfInvariantEq
    e.lhs e.rhs
    (separatesHead e valid)
    (separatesSupport e valid)
    (separatesParity e valid)
    (separatesHeadState e valid)

/-- Generic unrestricted completeness theorem for the exact four-law basis. -/
theorem headPositiveParitySuffixBasis_complete_of_separates
    (T : FiniteTable)
    (models : Models T.semigroup headPositiveParitySuffixBasis)
    (separatesHead :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        e.lhs.head = e.rhs.head)
    (separatesSupport :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList)
    (separatesParity :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        ∀ z, e.lhs.toList.count z % 2 =
          e.rhs.toList.count z % 2)
    (separatesHeadState :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        periodTwoFromTwoExponent
            (e.lhs.toList.count e.lhs.head) =
          periodTwoFromTwoExponent
            (e.rhs.toList.count e.rhs.head)) :
    BasisFor T.semigroup headPositiveParitySuffixBasis := by
  have coreComplete :=
    headPositiveParitySuffixCoreBasis_complete_of_separates
      T
      (headPositiveParitySuffixCoreModelsOfExact T.semigroup models)
      separatesHead separatesSupport separatesParity
      separatesHeadState
  exact coreComplete.replace models
    headPositiveParitySuffixCoreAxiomsDeriveExact

end SemigroupBasis.Examples
