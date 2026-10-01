import SemigroupBasis.CoRoots.S5_199

namespace SemigroupBasis.CoRoots.S5_97

open SemigroupBasis

def xx : Word Nat := ⟨0, [0]⟩
def xxx : Word Nat := ⟨0, [0, 0]⟩
def xy : Word Nat := ⟨0, [1]⟩
def yx : Word Nat := ⟨1, [0]⟩
def xxy : Word Nat := ⟨0, [0, 1]⟩
def xyy : Word Nat := ⟨0, [1, 1]⟩
def xyz : Word Nat := ⟨0, [1, 2]⟩
def xzy : Word Nat := ⟨0, [2, 1]⟩
def yxz : Word Nat := ⟨1, [0, 2]⟩
def xxyz : Word Nat := ⟨0, [0, 1, 2]⟩

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def commutativityLaw : Identity Nat := ⟨xy, yx⟩
def transferLaw : Identity Nat := ⟨xxy, xyy⟩
def longInsertionLaw : Identity Nat := ⟨xyz, xxyz⟩

/-- The four-identity commutative support basis of the `S5_97` family. -/
def basis : List (Identity Nat) :=
  [powerLaw, commutativityLaw, transferLaw, longInsertionLaw]

def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

def tripleThen (x y : Nat) : Word Nat :=
  ⟨x, [x, y]⟩

private def instantiateOneWord (u : Word Nat) : Nat → Word Nat
  | 0 => u
  | n + 1 => Word.singleton (n + 1)

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

/-- Commutativity may be applied to arbitrary nonempty word blocks. -/
theorem derivesCommutativity (u v : Word Nat) :
    Derives basis (u ++ v) (v ++ u) := by
  have base : Derives basis xy yx :=
    Derives.fromBasis (e := commutativityLaw) <| by
      exact List.Mem.tail _ (List.Mem.head _)
  have instantiated := Derives.subst base (instantiateTwoWords u v)
  simpa [basis, commutativityLaw, xy, yx, instantiateTwoWords,
    Word.bind, Word.append, Word.singleton] using instantiated

private theorem derivesSuffixCommutationLaw :
    Derives basis xyz xzy := by
  have swapped :=
    Derives.prepend (Word.singleton 0) <|
      derivesCommutativity (Word.singleton 1) (Word.singleton 2)
  simpa [xyz, xzy, Word.singleton, Word.append,
    Word.append_assoc] using swapped

private theorem derivesPrefixCommutationLaw :
    Derives basis xyz yxz := by
  have swapped :=
    Derives.appendRight
      (derivesCommutativity (Word.singleton 0) (Word.singleton 1))
      (Word.singleton 2)
  simpa [xyz, yxz, Word.singleton, Word.append,
    Word.append_assoc] using swapped

private theorem coreAxiomsDerive
    (e : Identity Nat)
    (member : e ∈ SemigroupBasis.CoRoots.S5_199.coreBasis) :
    Derives basis e.lhs e.rhs := by
  simp only [SemigroupBasis.CoRoots.S5_199.coreBasis,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact derivesSuffixCommutationLaw
  · exact derivesPrefixCommutationLaw
  · exact Derives.fromBasis (e := longInsertionLaw) <| by
      simp [basis, longInsertionLaw, xyz, xxyz]

/-- Long words are classified exactly by their support. -/
theorem derivesLongOfSupportEq
    (u v : Word Nat)
    (uLong : 3 ≤ u.toList.length)
    (vLong : 3 ≤ v.toList.length)
    (support : ∀ z, z ∈ u.toList ↔ z ∈ v.toList) :
    Derives basis u v :=
  (SemigroupBasis.CoRoots.S5_199.derivesCore <|
    SemigroupBasis.CoRoots.S5_199.derivesLongOfSupportEq
      u v uLong vLong support).transport coreAxiomsDerive

/-- The power law joins a square to its cubic expansion. -/
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

private theorem pair_support (a b c d : Nat)
    (support :
      ∀ z, z ∈ (wordOfCons a [b]).toList ↔
        z ∈ (wordOfCons c [d]).toList)
    (z : Nat) :
    (z = a ∨ z = b) ↔ (z = c ∨ z = d) := by
  simpa [wordOfCons, Word.toList, eq_comm] using support z

/-- Length-two words with the same support differ at most by commutativity. -/
theorem derivesLengthTwoOfSupport
    (u v : Word Nat)
    (uTwo : u.toList.length = 2)
    (vTwo : v.toList.length = 2)
    (support : ∀ z, z ∈ u.toList ↔ z ∈ v.toList) :
    Derives basis u v := by
  obtain ⟨a, b, rfl⟩ := pair_of_length_two u uTwo
  obtain ⟨c, d, rfl⟩ := pair_of_length_two v vTwo
  have support' := pair_support a b c d
    (by
      intro z
      exact support z)
  have cMember : c = a ∨ c = b :=
    (support' c).mpr (Or.inl rfl)
  have dMember : d = a ∨ d = b :=
    (support' d).mpr (Or.inr rfl)
  rcases cMember with hc | hc
  · subst c
    rcases dMember with hd | hd
    · subst d
      have bMember : b = a := by
        have := (support' b).mp (Or.inr rfl)
        rcases this with h | h
        · exact h
        · exact h
      subst b
      exact Derives.refl _
    · subst d
      exact Derives.refl _
  · subst c
    rcases dMember with hd | hd
    · subst d
      simpa [wordOfCons, Word.singleton, Word.append] using
        derivesCommutativity (Word.singleton a) (Word.singleton b)
    · subst d
      have aMember : a = b := by
        have := (support' a).mp (Or.inl rfl)
        rcases this with h | h
        · exact h
        · exact h
      subst b
      exact Derives.refl _

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

/-- Generic unrestricted completeness for the four-law support basis. A
finite table must model the laws, recover support, preserve the one-letter
stratum, and separate a square-free pair from its repeated expansion. -/
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
      · exact derivesLengthTwoOfSupport
          e.lhs e.rhs lhsTwo rhsTwo support
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

end SemigroupBasis.CoRoots.S5_97
