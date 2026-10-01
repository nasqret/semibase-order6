import SemigroupBasis.CoRoots.S5_199

namespace SemigroupBasis.CoRoots.S5_82

open SemigroupBasis

def xx : Word Nat := ⟨0, [0]⟩
def xxx : Word Nat := ⟨0, [0, 0]⟩
def xxy : Word Nat := ⟨0, [0, 1]⟩
def xyx : Word Nat := ⟨0, [1, 0]⟩
def xyy : Word Nat := ⟨0, [1, 1]⟩
def yxx : Word Nat := ⟨1, [0, 0]⟩
def xyz : Word Nat := ⟨0, [1, 2]⟩
def xzy : Word Nat := ⟨0, [2, 1]⟩
def yxz : Word Nat := ⟨1, [0, 2]⟩
def xxyz : Word Nat := ⟨0, [0, 1, 2]⟩

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def firstSwapLaw : Identity Nat := ⟨xxy, xyx⟩
def transferLaw : Identity Nat := ⟨xxy, xyy⟩
def prefixSwapLaw : Identity Nat := ⟨xxy, yxx⟩
def suffixCommutationLaw : Identity Nat := ⟨xyz, xzy⟩
def prefixCommutationLaw : Identity Nat := ⟨xyz, yxz⟩
def longInsertionLaw : Identity Nat := ⟨xyz, xxyz⟩

/-- The seven-identity support basis with rigid projections and ordered
quadratic exceptions. -/
def basis : List (Identity Nat) :=
  [powerLaw, firstSwapLaw, transferLaw, prefixSwapLaw,
    suffixCommutationLaw, prefixCommutationLaw, longInsertionLaw]

def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

def tripleThen (x y : Nat) : Word Nat :=
  ⟨x, [x, y]⟩

private def instantiateOneWord (u : Word Nat) : Nat → Word Nat
  | 0 => u
  | n + 1 => Word.singleton (n + 1)

private theorem coreAxiomsDerive
    (e : Identity Nat)
    (member : e ∈ SemigroupBasis.CoRoots.S5_199.coreBasis) :
    Derives basis e.lhs e.rhs := by
  simp only [SemigroupBasis.CoRoots.S5_199.coreBasis,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact Derives.fromBasis (e := suffixCommutationLaw) <| by
      simp [basis, suffixCommutationLaw, xyz, xzy]
  · exact Derives.fromBasis (e := prefixCommutationLaw) <| by
      simp [basis, prefixCommutationLaw, xyz, yxz]
  · exact Derives.fromBasis (e := longInsertionLaw) <| by
      simp [basis, longInsertionLaw, xyz, xxyz]

/-- The accepted `S5_199` support normalizer depends only on the common
three-law core, so it transports directly to this seven-law presentation. -/
theorem derivesLongOfSupportEq
    (u v : Word Nat)
    (uLong : 3 ≤ u.toList.length)
    (vLong : 3 ≤ v.toList.length)
    (support : ∀ z, z ∈ u.toList ↔ z ∈ v.toList) :
    Derives basis u v :=
  (SemigroupBasis.CoRoots.S5_199.derivesCore <|
    SemigroupBasis.CoRoots.S5_199.derivesLongOfSupportEq
      u v uLong vLong support).transport coreAxiomsDerive

/-- The additional power law joins a square to the long support stratum. -/
theorem derivesQuadraticExpansion (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have base : Derives basis xx xxx :=
    Derives.fromBasis (e := powerLaw) <| List.Mem.head _
  have instantiated := Derives.subst base (instantiateOneWord u)
  simpa [basis, powerLaw, xx, xxx, instantiateOneWord,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      instantiated

private theorem word_length_positive (w : Word Nat) :
    1 ≤ w.toList.length := by
  cases w
  simp [Word.toList]

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

private theorem lengthOne_eq_of_support
    (u v : Word Nat)
    (uOne : u.toList.length = 1)
    (vOne : v.toList.length = 1)
    (support : ∀ z, z ∈ u.toList ↔ z ∈ v.toList) :
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
                    have member :=
                      (support uHead).mp (by simp [Word.toList])
                    simpa [Word.toList] using member
                  subst vHead
                  rfl
              | cons vNext vRest =>
                  simp [Word.toList] at vOne
      | cons uNext uRest =>
          simp [Word.toList] at uOne

private theorem validLengthTwo_eq_of_support_and_order
    (T : FiniteTable) (left right : Fin T.order)
    (orderNe : T.mul left right ≠ T.mul right left)
    (e : Identity Nat) (valid : e.SatisfiedBy T.semigroup)
    (support :
      ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList)
    (lhsTwo : e.lhs.toList.length = 2)
    (rhsTwo : e.rhs.toList.length = 2) :
    e.lhs = e.rhs := by
  cases e with
  | mk lhs rhs =>
      obtain ⟨a, b, lhsEq⟩ := pair_of_length_two lhs lhsTwo
      obtain ⟨c, d, rhsEq⟩ := pair_of_length_two rhs rhsTwo
      have coordinates :=
        SemigroupBasis.CoRoots.S5_199.validPair_eq_of_support_and_order
          T left right orderNe
          (a := a) (b := b) (c := c) (d := d)
          (by simpa [lhsEq, rhsEq] using valid)
          (by
            intro z
            simpa [lhsEq, rhsEq, wordOfCons, Word.toList] using
              support z)
      rcases coordinates with ⟨rfl, rfl⟩
      simp [lhsEq, rhsEq]

private theorem pair_triple_same_support (a b : Nat) :
    ∀ z, z ∈ (wordOfCons a [b]).toList ↔
      z ∈ (tripleThen a b).toList := by
  intro z
  simp [wordOfCons, tripleThen, Word.toList]

private theorem validDistinctPair_not_long
    (T : FiniteTable)
    (modelsT : Models T.semigroup basis)
    (left right : Fin T.order)
    (shortLongNe :
      T.mul left right ≠ T.mul (T.mul left left) right)
    {a b : Nat} (ab : a ≠ b)
    (v : Word Nat) (vLong : 3 ≤ v.toList.length)
    (valid :
      (Identity.mk (wordOfCons a [b]) v).SatisfiedBy T.semigroup)
    (support :
      ∀ z, z ∈ (wordOfCons a [b]).toList ↔ z ∈ v.toList) :
    False := by
  have vCanonicalSupport :
      ∀ z, z ∈ v.toList ↔ z ∈ (tripleThen a b).toList := by
    intro z
    exact (support z).symm.trans (pair_triple_same_support a b z)
  have canonicalLong : 3 ≤ (tripleThen a b).toList.length := by
    simp [tripleThen, Word.toList]
  have normalize :=
    derivesLongOfSupportEq v (tripleThen a b)
      vLong canonicalLong vCanonicalSupport
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
      T.mul (T.mul (valuation a) (valuation a)) (valuation b)
    at evaluated
  rw [valueA, valueB] at evaluated
  exact shortLongNe evaluated

private theorem derivesSquareToLong
    (a : Nat) (v : Word Nat)
    (vLong : 3 ≤ v.toList.length)
    (support :
      ∀ z, z ∈ (wordOfCons a [a]).toList ↔ z ∈ v.toList) :
    Derives basis (wordOfCons a [a]) v := by
  have expand := derivesQuadraticExpansion (Word.singleton a)
  have tripleSupport :
      ∀ z, z ∈ (tripleThen a a).toList ↔ z ∈ v.toList := by
    intro z
    simpa [wordOfCons, tripleThen, Word.toList] using support z
  have normalize :=
    derivesLongOfSupportEq (tripleThen a a) v
      (by simp [tripleThen, Word.toList]) vLong tripleSupport
  exact Derives.trans
    (by
      simpa [wordOfCons, tripleThen, Word.singleton, Word.append,
        Word.append_assoc] using expand)
    normalize

/-- Generic unrestricted completeness for the support basis. A finite table
must model the laws, recover support, preserve the one-letter stratum, and
separate one ordered pair from its reversal and from its long expansion. -/
theorem basis_complete_of_separates
    (T : FiniteTable)
    (modelsT : Models T.semigroup basis)
    (supportT :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList)
    (lengthOneT :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        (e.lhs.toList.length = 1 ↔ e.rhs.toList.length = 1))
    (left right : Fin T.order)
    (orderNe : T.mul left right ≠ T.mul right left)
    (shortLongNe :
      T.mul left right ≠ T.mul (T.mul left left) right) :
    BasisFor T.semigroup basis := by
  refine ⟨modelsT, ?_⟩
  intro e valid
  have support := supportT e valid
  by_cases lhsOne : e.lhs.toList.length = 1
  · have rhsOne := (lengthOneT e valid).mp lhsOne
    have equal :=
      lengthOne_eq_of_support e.lhs e.rhs lhsOne rhsOne support
    rw [equal]
    exact Derives.refl _
  · have rhsNotOne : e.rhs.toList.length ≠ 1 := by
      intro rhsOne
      exact lhsOne ((lengthOneT e valid).mpr rhsOne)
    by_cases lhsTwo : e.lhs.toList.length = 2
    · by_cases rhsTwo : e.rhs.toList.length = 2
      · have equal :=
          validLengthTwo_eq_of_support_and_order
            T left right orderNe e valid support lhsTwo rhsTwo
        rw [equal]
        exact Derives.refl _
      · have rhsLong : 3 ≤ e.rhs.toList.length := by
          have positive := word_length_positive e.rhs
          omega
        obtain ⟨a, b, lhsEq⟩ :=
          pair_of_length_two e.lhs lhsTwo
        have validPairLong :
            (Identity.mk (wordOfCons a [b]) e.rhs).SatisfiedBy
              T.semigroup := by
          intro valuation
          simpa [lhsEq] using valid valuation
        have supportPairLong :
            ∀ z, z ∈ (wordOfCons a [b]).toList ↔
              z ∈ e.rhs.toList := by
          intro z
          simpa [lhsEq] using support z
        rw [lhsEq]
        by_cases ab : a = b
        · subst b
          exact derivesSquareToLong a e.rhs rhsLong supportPairLong
        · exact False.elim <|
            validDistinctPair_not_long
              T modelsT left right shortLongNe ab e.rhs rhsLong
              validPairLong supportPairLong
    · have lhsLong : 3 ≤ e.lhs.toList.length := by
        have positive := word_length_positive e.lhs
        omega
      by_cases rhsTwo : e.rhs.toList.length = 2
      · obtain ⟨c, d, rhsEq⟩ :=
          pair_of_length_two e.rhs rhsTwo
        have validLongPair :
            (Identity.mk e.lhs (wordOfCons c [d])).SatisfiedBy
              T.semigroup := by
          intro valuation
          simpa [rhsEq] using valid valuation
        have supportLongPair :
            ∀ z, z ∈ e.lhs.toList ↔
              z ∈ (wordOfCons c [d]).toList := by
          intro z
          simpa [rhsEq] using support z
        rw [rhsEq]
        by_cases cd : c = d
        · subst d
          exact Derives.symm <|
            derivesSquareToLong c e.lhs lhsLong
              (fun z => (supportLongPair z).symm)
        · have validSymm :
              (Identity.mk (wordOfCons c [d]) e.lhs).SatisfiedBy
                T.semigroup := by
            intro valuation
            exact (validLongPair valuation).symm
          exact False.elim <|
            validDistinctPair_not_long
              T modelsT left right shortLongNe cd e.lhs lhsLong
              validSymm (fun z => (supportLongPair z).symm)
      · have rhsLong : 3 ≤ e.rhs.toList.length := by
          have positive := word_length_positive e.rhs
          omega
        exact derivesLongOfSupportEq
          e.lhs e.rhs lhsLong rhsLong support

end SemigroupBasis.CoRoots.S5_82
