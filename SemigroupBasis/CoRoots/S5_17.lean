import SemigroupBasis.CoRoots.S5_16

namespace SemigroupBasis.CoRoots.S5_17

open SemigroupBasis
open SemigroupBasis.Examples

/-- The published three-identity basis of the `S5_17` family. -/
def basis : List (Identity Nat) :=
  [commonSquareLaw, commonSquareCommutativityLaw,
    SemigroupBasis.CoRoots.S5_58.longInsertionLaw]

def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

def tripleThen (x y : Nat) : Word Nat :=
  ⟨x, [x, x, y]⟩

private def instantiateTwoWords
    (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

theorem derivesCommonSquares (u v : Word Nat) :
    Derives basis (u ++ u) (v ++ v) := by
  have hbase :
      Derives basis commonSquareXX commonSquareYY :=
    Derives.fromBasis (e := commonSquareLaw) <| List.Mem.head _
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [basis, commonSquareLaw, commonSquareXX, commonSquareYY,
    instantiateTwoWords, Word.bind, Word.append, Word.singleton] using h

theorem derivesCommutativity (u v : Word Nat) :
    Derives basis (u ++ v) (v ++ u) := by
  have hbase :
      Derives basis commonSquareXY commonSquareYX :=
    Derives.fromBasis (e := commonSquareCommutativityLaw) <| by
      exact List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [basis, commonSquareCommutativityLaw, commonSquareXY,
    commonSquareYX, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton] using h

private theorem derivesS5_16Axiom
    (e : Identity Nat)
    (member : e ∈ SemigroupBasis.CoRoots.S5_16.basis) :
    Derives basis e.lhs e.rhs := by
  simp only [SemigroupBasis.CoRoots.S5_16.basis,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact
      Derives.fromBasis (e := commonSquareLaw) <| by
        simp [basis]
  · have square :=
      derivesCommonSquares (Word.singleton 0) (Word.singleton 1)
    have prefixed := Derives.prepend (Word.singleton 0) square
    have commute :=
      derivesCommutativity (Word.singleton 0) (Word.singleton 1)
    have rearrange :=
      Derives.appendRight commute (Word.singleton 1)
    exact Derives.trans
      (by
        simpa [SemigroupBasis.CoRoots.S5_58.squareMiddleLaw,
          SemigroupBasis.CoRoots.S5_58.xxx,
          SemigroupBasis.CoRoots.S5_58.yxy,
          commonSquareXX, commonSquareYY, Word.singleton, Word.append,
          Word.append_assoc] using prefixed)
      (by
        simpa [SemigroupBasis.CoRoots.S5_58.squareMiddleLaw,
          SemigroupBasis.CoRoots.S5_58.xxx,
          SemigroupBasis.CoRoots.S5_58.yxy,
          Word.singleton, Word.append, Word.append_assoc] using rearrange)
  · have commute :=
      derivesCommutativity (Word.singleton 1) (Word.singleton 2)
    simpa [SemigroupBasis.CoRoots.S5_58.suffixCommutationLaw,
      SemigroupBasis.CoRoots.S5_58.xyz,
      SemigroupBasis.CoRoots.S5_58.xzy,
      Word.singleton, Word.append, Word.append_assoc] using
        Derives.prepend (Word.singleton 0) commute
  · have commute :=
      derivesCommutativity (Word.singleton 0) (Word.singleton 1)
    simpa [SemigroupBasis.CoRoots.S5_58.prefixCommutationLaw,
      SemigroupBasis.CoRoots.S5_58.xyz,
      SemigroupBasis.CoRoots.S5_58.yxz,
      Word.singleton, Word.append, Word.append_assoc] using
        Derives.appendRight commute (Word.singleton 2)
  · exact
      Derives.fromBasis
        (e := SemigroupBasis.CoRoots.S5_58.longInsertionLaw) <| by
          simp [basis]

/-- The unrestricted long-word parity normalizer from the accepted `S5_16`
proof transports to the three commutative laws. -/
theorem derivesLongOfParityEq
    (u v : Word Nat)
    (uLong : 3 ≤ u.toList.length)
    (vLong : 3 ≤ v.toList.length)
    (parity : SemigroupBasis.CoRoots.S5_58.SameParity u v) :
    Derives basis u v :=
  (SemigroupBasis.CoRoots.S5_16.derivesLongOfParityEq
    u v uLong vLong parity).transport derivesS5_16Axiom

/-- Squares and words of length at least three share the parity stratum. -/
theorem derivesParityStratumOfSameParity
    (u v : Word Nat)
    (uShape : SemigroupBasis.CoRoots.S5_16.InParityStratum u)
    (vShape : SemigroupBasis.CoRoots.S5_16.InParityStratum v)
    (parity : SemigroupBasis.CoRoots.S5_58.SameParity u v) :
    Derives basis u v :=
  (SemigroupBasis.CoRoots.S5_16.derivesParityStratumOfSameParity
    u v uShape vShape parity).transport derivesS5_16Axiom

private theorem word_length_positive (w : Word Nat) :
    1 ≤ w.toList.length := by
  cases w
  simp [Word.toList]

private theorem lengthOne_eq_of_parity
    (u v : Word Nat)
    (uOne : u.toList.length = 1)
    (vOne : v.toList.length = 1)
    (parity : SemigroupBasis.CoRoots.S5_58.SameParity u v) :
    u = v := by
  cases u with
  | mk uHead uTail =>
      cases uTail with
      | nil =>
          cases v with
          | mk vHead vTail =>
              cases vTail with
              | nil =>
                  have heads : uHead = vHead := by
                    apply Decidable.byContradiction
                    intro different
                    have coordinate := parity uHead
                    simp [Word.toList, Ne.symm different] at coordinate
                  subst vHead
                  rfl
              | cons vNext vRest =>
                  simp [Word.toList] at vOne
      | cons uNext uRest =>
          simp [Word.toList] at uOne

private theorem pair_of_length_two
    (w : Word Nat) (lengthTwo : w.toList.length = 2) :
    ∃ a b, w = wordOfCons a [b] := by
  cases w with
  | mk head tail =>
      cases tail with
      | nil =>
          simp [Word.toList] at lengthTwo
      | cons next rest =>
          cases rest with
          | nil =>
              exact ⟨head, next, rfl⟩
          | cons third more =>
              simp [Word.toList] at lengthTwo

private theorem squarePair_inParityStratum (a : Nat) :
    SemigroupBasis.CoRoots.S5_16.InParityStratum
      (wordOfCons a [a]) := by
  exact Or.inl ⟨Word.singleton a, rfl⟩

private theorem rhs_square_of_lhs_square_parity
    {a c d : Nat}
    (parity :
      ∀ z, [a, a].count z % 2 = [c, d].count z % 2) :
    c = d := by
  apply Decidable.byContradiction
  intro different
  have coordinate := parity c
  by_cases ac : a = c
  · subst c
    have leftTwo : [a, a].count a = 2 := by simp
    have rightOne : [a, d].count a = 1 := by
      rw [List.count_cons_self,
        List.count_cons_of_ne (Ne.symm different)]
      rfl
    rw [leftTwo, rightOne] at coordinate
    omega
  · have leftZero : [a, a].count c = 0 :=
      List.count_eq_zero.mpr (by simp [Ne.symm ac])
    have rightOne : [c, d].count c = 1 := by
      rw [List.count_cons_self,
        List.count_cons_of_ne (Ne.symm different)]
      rfl
    rw [leftZero, rightOne] at coordinate
    omega

private theorem distinct_pair_support_of_parity
    {a b c d : Nat} (ab : a ≠ b)
    (parity :
      ∀ z, [a, b].count z % 2 = [c, d].count z % 2) :
    ∀ z, z ∈ [a, b] ↔ z ∈ [c, d] := by
  have cd : c ≠ d := by
    intro equal
    subst d
    have coordinate := parity a
    by_cases ac : a = c
    · subst c
      have leftOne : [a, b].count a = 1 := by
        rw [List.count_cons_self,
          List.count_cons_of_ne (Ne.symm ab)]
        rfl
      have rightTwo : [a, a].count a = 2 := by simp
      rw [leftOne, rightTwo] at coordinate
      omega
    · have leftOne : [a, b].count a = 1 := by
        rw [List.count_cons_self,
          List.count_cons_of_ne (Ne.symm ab)]
        rfl
      have rightZero : [c, c].count a = 0 :=
        List.count_eq_zero.mpr (by simp [ac])
      rw [leftOne, rightZero] at coordinate
      omega
  intro z
  constructor
  · intro member
    have leftCount : [a, b].count z = 1 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with equal | equal
      · subst z
        rw [List.count_cons_self,
          List.count_cons_of_ne (Ne.symm ab)]
        rfl
      · subst z
        rw [List.count_cons_of_ne ab, List.count_cons_self]
        rfl
    have coordinate := parity z
    have rightBound := List.count_le_length (a := z) (l := [c, d])
    have rightPositive : 0 < [c, d].count z := by omega
    exact List.count_pos_iff.mp rightPositive
  · intro member
    have rightCount : [c, d].count z = 1 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with equal | equal
      · subst z
        rw [List.count_cons_self,
          List.count_cons_of_ne (Ne.symm cd)]
        rfl
      · subst z
        rw [List.count_cons_of_ne cd, List.count_cons_self]
        rfl
    have coordinate := parity z
    have leftBound := List.count_le_length (a := z) (l := [a, b])
    have leftPositive : 0 < [a, b].count z := by omega
    exact List.count_pos_iff.mp leftPositive

private theorem derivesDistinctPair_of_support
    {a b c d : Nat} (ab : a ≠ b)
    (support : ∀ z, z ∈ [a, b] ↔ z ∈ [c, d]) :
    Derives basis (wordOfCons a [b]) (wordOfCons c [d]) := by
  have hc : c = a ∨ c = b := by
    simpa using (support c).mpr (by simp)
  have hd : d = a ∨ d = b := by
    simpa using (support d).mpr (by simp)
  rcases hc with hc | hc
  · rcases hd with hd | hd
    · have bMember := (support b).mp (by simp)
      have hba : b = a := by simpa [hc, hd] using bMember
      exact False.elim (ab hba.symm)
    · subst c
      subst d
      exact Derives.refl _
  · rcases hd with hd | hd
    · subst c
      subst d
      simpa [wordOfCons, Word.singleton, Word.append] using
        derivesCommutativity (Word.singleton a) (Word.singleton b)
    · have aMember := (support a).mp (by simp)
      have hab : a = b := by simpa [hc, hd] using aMember
      exact False.elim (ab hab)

private theorem derivesLengthTwoOfSameParity
    (u v : Word Nat)
    (uTwo : u.toList.length = 2)
    (vTwo : v.toList.length = 2)
    (parity : SemigroupBasis.CoRoots.S5_58.SameParity u v) :
    Derives basis u v := by
  obtain ⟨a, b, uEq⟩ := pair_of_length_two u uTwo
  obtain ⟨c, d, vEq⟩ := pair_of_length_two v vTwo
  have listParity :
      ∀ z, [a, b].count z % 2 = [c, d].count z % 2 := by
    simpa [uEq, vEq, wordOfCons, Word.toList] using parity
  rw [uEq, vEq]
  by_cases ab : a = b
  · subst b
    have cd := rhs_square_of_lhs_square_parity listParity
    subst d
    simpa [wordOfCons, Word.singleton, Word.append] using
      derivesCommonSquares (Word.singleton a) (Word.singleton c)
  · exact derivesDistinctPair_of_support ab
      (distinct_pair_support_of_parity ab listParity)

private theorem pair_tripleThen_sameParity (a b : Nat) :
    SemigroupBasis.CoRoots.S5_58.SameParity
      (wordOfCons a [b]) (tripleThen a b) := by
  intro z
  simp only [wordOfCons, tripleThen, Word.toList]
  by_cases za : z = a
  · subst z
    by_cases ab : a = b
    · subst b
      simp
    · simp [Ne.symm ab]
  · simp [Ne.symm za]

private theorem validDistinctPair_not_long
    (T : FiniteTable)
    (modelsT : Models T.semigroup basis)
    (left right : Fin T.order)
    (shortLongNe :
      T.mul left right ≠
        T.mul (T.mul (T.mul left left) left) right)
    {a b : Nat} (ab : a ≠ b)
    (v : Word Nat) (vLong : 3 ≤ v.toList.length)
    (valid :
      (Identity.mk (wordOfCons a [b]) v).SatisfiedBy T.semigroup)
    (parity :
      SemigroupBasis.CoRoots.S5_58.SameParity
        (wordOfCons a [b]) v) :
    False := by
  have vCanonicalParity :
      SemigroupBasis.CoRoots.S5_58.SameParity
        v (tripleThen a b) := by
    intro z
    exact (parity z).symm.trans (pair_tripleThen_sameParity a b z)
  have canonicalLong : 3 ≤ (tripleThen a b).toList.length := by
    simp [tripleThen, Word.toList]
  have normalize :=
    derivesLongOfParityEq v (tripleThen a b)
      vLong canonicalLong vCanonicalParity
  have normalizedValid :
      (Identity.mk (wordOfCons a [b]) (tripleThen a b)).SatisfiedBy
        T.semigroup := by
    intro valuation
    exact (valid valuation).trans (normalize.sound modelsT valuation)
  let valuation : Nat → Fin T.order :=
    fun z => if z = a then left else right
  have evaluated := normalizedValid valuation
  have valueA : valuation a = left := by simp [valuation]
  have valueB : valuation b = right := by
    simp [valuation, Ne.symm ab]
  change
    T.mul (valuation a) (valuation b) =
      T.mul
        (T.mul (T.mul (valuation a) (valuation a)) (valuation a))
        (valuation b) at evaluated
  rw [valueA, valueB] at evaluated
  exact shortLongNe evaluated

/-- Generic unrestricted completeness for the `S5_17` basis. The table must
model the basis, recover coordinate parity, preserve singleton words, and
separate a distinct quadratic word from its same-parity long expansion. -/
theorem basis_complete_of_separates
    (T : FiniteTable)
    (modelsT : Models T.semigroup basis)
    (parityT :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        SemigroupBasis.CoRoots.S5_58.SameParity e.lhs e.rhs)
    (lengthOneT :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        (e.lhs.toList.length = 1 ↔
          e.rhs.toList.length = 1))
    (left right : Fin T.order)
    (shortLongNe :
      T.mul left right ≠
        T.mul (T.mul (T.mul left left) left) right) :
    BasisFor T.semigroup basis := by
  refine ⟨modelsT, ?_⟩
  intro e valid
  have parity := parityT e valid
  by_cases lhsOne : e.lhs.toList.length = 1
  · have rhsOne := (lengthOneT e valid).mp lhsOne
    have equal :=
      lengthOne_eq_of_parity e.lhs e.rhs lhsOne rhsOne parity
    rw [equal]
    exact Derives.refl _
  · have rhsNotOne : e.rhs.toList.length ≠ 1 := by
      intro rhsOne
      exact lhsOne ((lengthOneT e valid).mpr rhsOne)
    by_cases lhsTwo : e.lhs.toList.length = 2
    · by_cases rhsTwo : e.rhs.toList.length = 2
      · exact derivesLengthTwoOfSameParity
          e.lhs e.rhs lhsTwo rhsTwo parity
      · have rhsLong : 3 ≤ e.rhs.toList.length := by
          have positive : 0 < e.rhs.toList.length := by
            exact word_length_positive e.rhs
          omega
        obtain ⟨a, b, lhsEq⟩ := pair_of_length_two e.lhs lhsTwo
        have validPairLong :
            (Identity.mk (wordOfCons a [b]) e.rhs).SatisfiedBy
              T.semigroup := by
          intro valuation
          simpa [lhsEq] using valid valuation
        have parityPairLong :
            SemigroupBasis.CoRoots.S5_58.SameParity
              (wordOfCons a [b]) e.rhs := by
          simpa [lhsEq] using parity
        rw [lhsEq]
        by_cases ab : a = b
        · subst b
          exact derivesParityStratumOfSameParity
            (wordOfCons a [a]) e.rhs
            (squarePair_inParityStratum a) (Or.inr rhsLong)
            parityPairLong
        · exact False.elim <|
            validDistinctPair_not_long
              T modelsT left right shortLongNe ab
              e.rhs rhsLong validPairLong parityPairLong
    · have lhsLong : 3 ≤ e.lhs.toList.length := by
        have positive : 0 < e.lhs.toList.length := by
          exact word_length_positive e.lhs
        omega
      by_cases rhsTwo : e.rhs.toList.length = 2
      · obtain ⟨c, d, rhsEq⟩ := pair_of_length_two e.rhs rhsTwo
        have validLongPair :
            (Identity.mk e.lhs (wordOfCons c [d])).SatisfiedBy
              T.semigroup := by
          intro valuation
          simpa [rhsEq] using valid valuation
        have parityLongPair :
            SemigroupBasis.CoRoots.S5_58.SameParity
              e.lhs (wordOfCons c [d]) := by
          simpa [rhsEq] using parity
        rw [rhsEq]
        by_cases cd : c = d
        · subst d
          exact derivesParityStratumOfSameParity
            e.lhs (wordOfCons c [c])
            (Or.inr lhsLong) (squarePair_inParityStratum c)
            parityLongPair
        · have validSymm :
              (Identity.mk (wordOfCons c [d]) e.lhs).SatisfiedBy
                T.semigroup := by
            intro valuation
            exact (validLongPair valuation).symm
          have paritySymm :
              SemigroupBasis.CoRoots.S5_58.SameParity
                (wordOfCons c [d]) e.lhs :=
            fun z => (parityLongPair z).symm
          exact False.elim <|
            validDistinctPair_not_long
              T modelsT left right shortLongNe cd
              e.lhs lhsLong validSymm paritySymm
      · have rhsLong : 3 ≤ e.rhs.toList.length := by
          have positive : 0 < e.rhs.toList.length := by
            exact word_length_positive e.rhs
          omega
        exact derivesLongOfParityEq
          e.lhs e.rhs lhsLong rhsLong parity

end SemigroupBasis.CoRoots.S5_17
