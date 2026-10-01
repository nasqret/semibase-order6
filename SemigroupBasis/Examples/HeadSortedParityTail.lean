import SemigroupBasis.Examples.CommutativeParitySupportFour
import SemigroupBasis.Examples.CommutativePeriodTwoFromTwo

namespace SemigroupBasis.Examples

open SemigroupBasis

def headSortedParityTailXX : Word Nat := ⟨0, [0]⟩
def headSortedParityTailXXXX : Word Nat := ⟨0, [0, 0, 0]⟩
def headSortedParityTailXY : Word Nat := ⟨0, [1]⟩
def headSortedParityTailXYYY : Word Nat := ⟨0, [1, 1, 1]⟩
def headSortedParityTailXXY : Word Nat := ⟨0, [0, 1]⟩
def headSortedParityTailXYX : Word Nat := ⟨0, [1, 0]⟩
def headSortedParityTailXYZ : Word Nat := ⟨0, [1, 2]⟩
def headSortedParityTailXZY : Word Nat := ⟨0, [2, 1]⟩

def headSortedParityTailHeadPowerLaw : Identity Nat :=
  ⟨headSortedParityTailXX, headSortedParityTailXXXX⟩

def headSortedParityTailContextPowerLaw : Identity Nat :=
  ⟨headSortedParityTailXY, headSortedParityTailXYYY⟩

def headSortedParityTailGatherLaw : Identity Nat :=
  ⟨headSortedParityTailXXY, headSortedParityTailXYX⟩

def headSortedParityTailSwapLaw : Identity Nat :=
  ⟨headSortedParityTailXYZ, headSortedParityTailXZY⟩

/-- The contextual triple law and fixed-head suffix swap are the
normalization core. -/
def headSortedParityTailCoreBasis : List (Identity Nat) :=
  [headSortedParityTailContextPowerLaw,
    headSortedParityTailSwapLaw]

/-- The exact cleaner basis
`xx = xxxx`, `xy = xyyy`, `xxy = xyx`, and `xyz = xzy`. -/
def headSortedParityTailBasis : List (Identity Nat) :=
  [headSortedParityTailHeadPowerLaw,
    headSortedParityTailContextPowerLaw,
    headSortedParityTailGatherLaw,
    headSortedParityTailSwapLaw]

private def instantiateThreeWords
    (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

/-- Contract three copies of a nonempty suffix block after a fixed
nonempty prefix. -/
theorem headSortedParityTailDerivesSuffixTripleContraction
    (stem repeated : Word Nat) :
    Derives headSortedParityTailCoreBasis
      (((stem ++ repeated) ++ repeated) ++ repeated)
      (stem ++ repeated) := by
  have base :
      Derives headSortedParityTailCoreBasis
        headSortedParityTailXYYY headSortedParityTailXY :=
    Derives.symm <|
      Derives.fromBasis
        (e := headSortedParityTailContextPowerLaw) <|
        List.Mem.head _
  have instantiated :=
    Derives.subst base
      (instantiateThreeWords stem repeated repeated)
  simpa [headSortedParityTailCoreBasis,
    headSortedParityTailContextPowerLaw,
    headSortedParityTailXYYY, headSortedParityTailXY,
    instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using instantiated

/-- The displayed head power law is a substitution instance of the
contextual triple law. -/
theorem headSortedParityTailDerivesHeadPower (u : Word Nat) :
    Derives headSortedParityTailCoreBasis
      (u ++ u) (((u ++ u) ++ u) ++ u) := by
  simpa [Word.append_assoc] using
    (headSortedParityTailDerivesSuffixTripleContraction u u).symm

/-- Swap arbitrary nonempty blocks strictly behind a fixed prefix. -/
theorem headSortedParityTailDerivesSuffixSwap
    (stem u v : Word Nat) :
    Derives headSortedParityTailCoreBasis
      ((stem ++ u) ++ v) ((stem ++ v) ++ u) := by
  have base :
      Derives headSortedParityTailCoreBasis
        headSortedParityTailXYZ headSortedParityTailXZY :=
    Derives.fromBasis
      (e := headSortedParityTailSwapLaw) <|
      List.Mem.tail _ (List.Mem.head _)
  have instantiated :=
    Derives.subst base (instantiateThreeWords stem u v)
  simpa [headSortedParityTailCoreBasis,
    headSortedParityTailSwapLaw,
    headSortedParityTailXYZ, headSortedParityTailXZY,
    instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using instantiated

/-- The displayed gather law is a fixed-head suffix swap. -/
theorem headSortedParityTailDerivesGather (u v : Word Nat) :
    Derives headSortedParityTailCoreBasis
      ((u ++ u) ++ v) ((u ++ v) ++ u) := by
  simpa using
    headSortedParityTailDerivesSuffixSwap u u v

/-- Every exact cleaner axiom follows from the two-law core. -/
theorem headSortedParityTailExactAxiomsDeriveCore
    (identity : Identity Nat)
    (member : identity ∈ headSortedParityTailBasis) :
    Derives headSortedParityTailCoreBasis
      identity.lhs identity.rhs := by
  simp only [headSortedParityTailBasis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · simpa [headSortedParityTailHeadPowerLaw,
      headSortedParityTailXX, headSortedParityTailXXXX,
      Word.append, Word.singleton, Word.append_assoc] using
      headSortedParityTailDerivesHeadPower (Word.singleton 0)
  · exact Derives.fromBasis (List.Mem.head _)
  · simpa [headSortedParityTailGatherLaw,
      headSortedParityTailXXY, headSortedParityTailXYX,
      Word.append, Word.singleton, Word.append_assoc] using
      headSortedParityTailDerivesGather
        (Word.singleton 0) (Word.singleton 1)
  · exact Derives.fromBasis <|
      List.Mem.tail _ (List.Mem.head _)

/-- Both core laws occur literally in the exact four-law basis. -/
theorem headSortedParityTailCoreAxiomsDeriveExact
    (identity : Identity Nat)
    (member : identity ∈ headSortedParityTailCoreBasis) :
    Derives headSortedParityTailBasis identity.lhs identity.rhs := by
  simp only [headSortedParityTailCoreBasis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact Derives.fromBasis <|
      List.Mem.tail _ (List.Mem.head _)
  · exact Derives.fromBasis <|
      List.Mem.tail _ <|
        List.Mem.tail _ <|
          List.Mem.tail _ (List.Mem.head _)

private theorem bind_append
    (u v : Word Nat) (substitution : Nat → Word Nat) :
    (u ++ v).bind substitution =
      u.bind substitution ++ v.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (word : Word Nat) (first second : Nat → Word Nat) :
    (word.bind first).bind second =
      word.bind (fun x => (first x).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- Fixed-head analogue of `paritySupportLiftParity`: replay a derivation
from `x = xxx`, `xy = yx` strictly behind a common nonempty prefix. -/
theorem headSortedParityTailLiftParity
    {u v : Word Nat}
    (derivation : Derives commutativeParityBasis u v)
    (stem : Word Nat) (substitution : Nat → Word Nat) :
    Derives headSortedParityTailCoreBasis
      (stem ++ u.bind substitution)
      (stem ++ v.bind substitution) := by
  induction derivation generalizing stem substitution with
  | fromBasis member =>
      simp only [commutativeParityBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simpa [parityPowerLaw, parityX, parityXXX, Word.bind,
          Word.append, Word.singleton, Word.append_assoc] using
          (headSortedParityTailDerivesSuffixTripleContraction
            stem (substitution 0)).symm
      · simpa [parityCommutativityLaw, parityXY, parityYX,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          headSortedParityTailDerivesSuffixSwap
            stem (substitution 0) (substitution 1)
  | refl =>
      exact Derives.refl _
  | symm _ ih =>
      exact Derives.symm (ih stem substitution)
  | trans _ _ firstIH secondIH =>
      exact Derives.trans
        (firstIH stem substitution)
        (secondIH stem substitution)
  | prepend left _ ih =>
      simpa [bind_append, Word.append_assoc] using
        ih (stem ++ left.bind substitution) substitution
  | appendRight _ right ih =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight
          (ih stem substitution) (right.bind substitution)
  | subst _ next ih =>
      simpa [bind_bind] using
        ih stem
          (fun x => (next x).bind substitution)

private def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

/-- Every permutation strictly behind a fixed head is derivable. -/
theorem headSortedParityTailDerivesTailPermutation
    (head : Nat) {left right : List Nat}
    (permutation : left.Perm right) :
    Derives headSortedParityTailCoreBasis
      (wordOfCons head left) (wordOfCons head right) := by
  induction permutation generalizing head with
  | nil =>
      exact Derives.refl _
  | cons x _ ih =>
      have suffix := ih (head := x)
      simpa [wordOfCons, Word.singleton, Word.append] using
        Derives.prepend (Word.singleton head) suffix
  | swap x y rest =>
      cases rest with
      | nil =>
          simpa [wordOfCons, Word.singleton, Word.append,
            Word.append_assoc] using
            headSortedParityTailDerivesSuffixSwap
              (Word.singleton head) (Word.singleton y)
              (Word.singleton x)
      | cons z zs =>
          have swapped :=
            Derives.appendRight
              (headSortedParityTailDerivesSuffixSwap
                (Word.singleton head) (Word.singleton y)
                (Word.singleton x))
              (wordOfCons z zs)
          simpa [wordOfCons, Word.singleton, Word.append,
            Word.append_assoc] using swapped
  | trans _ _ firstIH secondIH =>
      exact Derives.trans
        (firstIH (head := head)) (secondIH (head := head))

/-- Canonical fixed-head representative. Every supported suffix variable
occurs once for positive odd multiplicity and twice for positive even
multiplicity. -/
def headSortedParityTailNormal (word : Word Nat) : Word Nat :=
  ⟨word.head, positiveParityReduce word.tail⟩

theorem headSortedParityTailDerivesNormal (word : Word Nat) :
    Derives headSortedParityTailCoreBasis word
      (headSortedParityTailNormal word) := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil =>
          exact Derives.refl _
      | cons first rest =>
          let suffix : Word Nat := ⟨first, rest⟩
          have suffixNormal := positiveParityDerivesNormal suffix
          change
            match positiveParityReduce (first :: rest) with
            | [] => False
            | next :: reduced =>
                Derives commutativeParityBasis suffix
                  ⟨next, reduced⟩ at suffixNormal
          cases reducedEq :
              positiveParityReduce (first :: rest) with
          | nil =>
              rw [reducedEq] at suffixNormal
              exact False.elim suffixNormal
          | cons next reduced =>
              rw [reducedEq] at suffixNormal
              have lifted :=
                headSortedParityTailLiftParity suffixNormal
                  (Word.singleton head) Word.singleton
              rw [bind_singleton, bind_singleton] at lifted
              simpa [headSortedParityTailNormal, suffix,
                Word.append, Word.singleton, reducedEq] using lifted

private theorem headState_eq_one_iff (n : Nat) :
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

private theorem mod_two_of_succ_mod_two_eq (m n : Nat)
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

/-- Equal heads, total support, total parity, and the distinguished head
multiplicity state determine the positive-parity suffix normal form up to
permutation. -/
theorem headSortedParityTailNormal_tail_perm
    (u v : Word Nat)
    (heads : u.head = v.head)
    (support :
      ∀ z, z ∈ u.toList ↔ z ∈ v.toList)
    (parity :
      ∀ z, u.toList.count z % 2 =
        v.toList.count z % 2)
    (headState :
      periodTwoFromTwoExponent
          (u.toList.count u.head) =
        periodTwoFromTwoExponent
          (v.toList.count u.head)) :
    (headSortedParityTailNormal u).tail.Perm
      (headSortedParityTailNormal v).tail := by
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
              simp only [Word.toList,
                List.count_cons_self] at headState
              have zeroEq :
                  uTail.count uHead = 0 ↔
                    vTail.count uHead = 0 := by
                constructor
                · intro leftZero
                  have leftOne :
                      periodTwoFromTwoExponent
                          (uTail.count uHead + 1) = 1 :=
                    (headState_eq_one_iff
                      (uTail.count uHead)).2 leftZero
                  have rightOne :
                      periodTwoFromTwoExponent
                          (vTail.count uHead + 1) = 1 :=
                    headState.symm.trans leftOne
                  exact
                    (headState_eq_one_iff
                      (vTail.count uHead)).1 rightOne
                · intro rightZero
                  have rightOne :
                      periodTwoFromTwoExponent
                          (vTail.count uHead + 1) = 1 :=
                    (headState_eq_one_iff
                      (vTail.count uHead)).2 rightZero
                  have leftOne :
                      periodTwoFromTwoExponent
                          (uTail.count uHead + 1) = 1 :=
                    headState.trans rightOne
                  exact
                    (headState_eq_one_iff
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
              exact mod_two_of_succ_mod_two_eq _ _ wholeParity
            · simpa [Word.toList,
                List.count_cons_of_ne (Ne.symm hz)] using
                wholeParity

theorem headSortedParityTailDerivesOfInvariantEq
    (u v : Word Nat)
    (heads : u.head = v.head)
    (support :
      ∀ z, z ∈ u.toList ↔ z ∈ v.toList)
    (parity :
      ∀ z, u.toList.count z % 2 =
        v.toList.count z % 2)
    (headState :
      periodTwoFromTwoExponent
          (u.toList.count u.head) =
        periodTwoFromTwoExponent
          (v.toList.count u.head)) :
    Derives headSortedParityTailCoreBasis u v := by
  have leftNormal :=
    headSortedParityTailDerivesNormal u
  have rightNormal :=
    headSortedParityTailDerivesNormal v
  have middle :
      Derives headSortedParityTailCoreBasis
        (headSortedParityTailNormal u)
        (headSortedParityTailNormal v) := by
    simpa [headSortedParityTailNormal, wordOfCons, heads] using
      headSortedParityTailDerivesTailPermutation
        u.head
        (headSortedParityTailNormal_tail_perm
          u v heads support parity headState)
  exact Derives.trans leftNormal <|
    Derives.trans middle (Derives.symm rightNormal)

private theorem coreModelsOfExact
    {S : Type} (semigroup : Semigroup S)
    (models : Models semigroup headSortedParityTailBasis) :
    Models semigroup headSortedParityTailCoreBasis := by
  intro identity member
  simp only [headSortedParityTailCoreBasis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact models headSortedParityTailContextPowerLaw <|
      List.Mem.tail _ (List.Mem.head _)
  · exact models headSortedParityTailSwapLaw <|
      List.Mem.tail _ <|
        List.Mem.tail _ <|
          List.Mem.tail _ (List.Mem.head _)

theorem headSortedParityTailCoreBasis_complete_of_separates
    (table : FiniteTable)
    (models :
      Models table.semigroup headSortedParityTailCoreBasis)
    (separatesHead :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy table.semigroup →
          identity.lhs.head = identity.rhs.head)
    (separatesSupport :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy table.semigroup →
          ∀ z, z ∈ identity.lhs.toList ↔
            z ∈ identity.rhs.toList)
    (separatesParity :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy table.semigroup →
          ∀ z,
            identity.lhs.toList.count z % 2 =
              identity.rhs.toList.count z % 2)
    (separatesHeadState :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy table.semigroup →
          periodTwoFromTwoExponent
              (identity.lhs.toList.count identity.lhs.head) =
            periodTwoFromTwoExponent
              (identity.rhs.toList.count identity.lhs.head)) :
    BasisFor table.semigroup headSortedParityTailCoreBasis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact headSortedParityTailDerivesOfInvariantEq
    identity.lhs identity.rhs
    (separatesHead identity valid)
    (separatesSupport identity valid)
    (separatesParity identity valid)
    (separatesHeadState identity valid)

/-- Generic unrestricted completeness for the exact four-law cleaner
basis. -/
theorem headSortedParityTailBasis_complete_of_separates
    (table : FiniteTable)
    (models : Models table.semigroup headSortedParityTailBasis)
    (separatesHead :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy table.semigroup →
          identity.lhs.head = identity.rhs.head)
    (separatesSupport :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy table.semigroup →
          ∀ z, z ∈ identity.lhs.toList ↔
            z ∈ identity.rhs.toList)
    (separatesParity :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy table.semigroup →
          ∀ z,
            identity.lhs.toList.count z % 2 =
              identity.rhs.toList.count z % 2)
    (separatesHeadState :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy table.semigroup →
          periodTwoFromTwoExponent
              (identity.lhs.toList.count identity.lhs.head) =
            periodTwoFromTwoExponent
              (identity.rhs.toList.count identity.lhs.head)) :
    BasisFor table.semigroup headSortedParityTailBasis := by
  have coreComplete :=
    headSortedParityTailCoreBasis_complete_of_separates
      table (coreModelsOfExact table.semigroup models)
      separatesHead separatesSupport separatesParity
      separatesHeadState
  exact coreComplete.replace models
    headSortedParityTailCoreAxiomsDeriveExact

end SemigroupBasis.Examples
