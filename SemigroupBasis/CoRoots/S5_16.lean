import SemigroupBasis.CoRoots.S5_58

namespace SemigroupBasis.CoRoots.S5_16

open SemigroupBasis
open SemigroupBasis.Examples

/-- The common published five-identity basis of the `S5_16` family. -/
def basis : List (Identity Nat) :=
  [commonSquareLaw, SemigroupBasis.CoRoots.S5_58.squareMiddleLaw,
    SemigroupBasis.CoRoots.S5_58.suffixCommutationLaw,
    SemigroupBasis.CoRoots.S5_58.prefixCommutationLaw,
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

private theorem derivesCommonSquares (u v : Word Nat) :
    Derives basis (u ++ u) (v ++ v) := by
  have hbase :
      Derives basis commonSquareXX commonSquareYY :=
    Derives.fromBasis (e := commonSquareLaw) <| List.Mem.head _
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [basis, commonSquareLaw, commonSquareXX, commonSquareYY,
    instantiateTwoWords, Word.bind, Word.append, Word.singleton] using h

private theorem derivesS5_58Axiom
    (e : Identity Nat)
    (member : e ∈ SemigroupBasis.CoRoots.S5_58.basis) :
    Derives basis e.lhs e.rhs := by
  simp only [SemigroupBasis.CoRoots.S5_58.basis,
    List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · have square :
        Derives basis commonSquareXX commonSquareYY :=
      Derives.fromBasis (e := commonSquareLaw) <| List.Mem.head _
    have prefixed := Derives.prepend (Word.singleton 0) square
    simpa [SemigroupBasis.CoRoots.S5_58.squareRightLaw,
      SemigroupBasis.CoRoots.S5_58.xxx,
      SemigroupBasis.CoRoots.S5_58.xyy,
      commonSquareXX, commonSquareYY, Word.singleton, Word.append,
      Word.append_assoc] using prefixed
  · exact
      Derives.fromBasis (e :=
        SemigroupBasis.CoRoots.S5_58.squareMiddleLaw) <| by
          simp [basis]
  · have square :
        Derives basis commonSquareXX commonSquareYY :=
      Derives.fromBasis (e := commonSquareLaw) <| List.Mem.head _
    have suffixed := Derives.appendRight square (Word.singleton 0)
    simpa [SemigroupBasis.CoRoots.S5_58.squareLeftLaw,
      SemigroupBasis.CoRoots.S5_58.xxx,
      SemigroupBasis.CoRoots.S5_58.yyx,
      commonSquareXX, commonSquareYY, Word.singleton, Word.append,
      Word.append_assoc] using suffixed
  · exact
      Derives.fromBasis (e :=
        SemigroupBasis.CoRoots.S5_58.suffixCommutationLaw) <| by
          simp [basis]
  · exact
      Derives.fromBasis (e :=
        SemigroupBasis.CoRoots.S5_58.prefixCommutationLaw) <| by
          simp [basis]
  · exact
      Derives.fromBasis (e :=
        SemigroupBasis.CoRoots.S5_58.longInsertionLaw) <| by
          simp [basis]

/-- The accepted `S5_58` long-word normalizer transports to the smaller
five-law basis. -/
theorem derivesLongOfParityEq
    (u v : Word Nat)
    (uLong : 3 ≤ u.toList.length)
    (vLong : 3 ≤ v.toList.length)
    (parityEq : SemigroupBasis.CoRoots.S5_58.SameParity u v) :
    Derives basis u v :=
  (SemigroupBasis.CoRoots.S5_58.derivesLongOfParityEq
    u v uLong vLong parityEq).transport
    derivesS5_58Axiom

/-- Squares and words of length at least three form the nonliteral parity
stratum of the exact congruence. -/
def InParityStratum (w : Word Nat) : Prop :=
  (∃ p : Word Nat, w = p ++ p) ∨ 3 ≤ w.toList.length

/-- One-letter words and ordered distinct pairs remain literal. Every other
word is classified by its coordinate-parity vector. -/
def ExactBasisClass (u v : Word Nat) : Prop :=
  u = v ∨
    (InParityStratum u ∧ InParityStratum v ∧
      SemigroupBasis.CoRoots.S5_58.SameParity u v)

private def ShapeClass (u v : Word Nat) : Prop :=
  u = v ∨ (InParityStratum u ∧ InParityStratum v)

private theorem word_length_positive (w : Word Nat) :
    1 ≤ w.toList.length := by
  cases w
  simp [Word.toList]

private theorem parityStratum_length_two
    {w : Word Nat} (inStratum : InParityStratum w) :
    2 ≤ w.toList.length := by
  rcases inStratum with ⟨p, rfl⟩ | long
  · simp only [Word.toList_append, List.length_append]
    have positive := word_length_positive p
    omega
  · omega

private theorem bind_append
    (u v : Word Nat) (substitution : Nat → Word Nat) :
    (u ++ v).bind substitution =
      u.bind substitution ++ v.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem list_length_le_flatMap_words
    (letters : List Nat) (substitution : Nat → Word Nat) :
    letters.length ≤
      (letters.flatMap fun letter =>
        (substitution letter).toList).length := by
  induction letters with
  | nil =>
      simp
  | cons letter rest ih =>
      simp only [List.length_cons, List.flatMap_cons, List.length_append]
      have imagePositive :
          1 ≤ (substitution letter).toList.length := by
        exact word_length_positive (substitution letter)
      omega

private theorem bind_preserves_long
    (w : Word Nat) (substitution : Nat → Word Nat)
    (long : 3 ≤ w.toList.length) :
    3 ≤ (w.bind substitution).toList.length := by
  rw [Word.toList_bind]
  exact Nat.le_trans long
    (list_length_le_flatMap_words w.toList substitution)

private theorem parityStratum_subst
    (substitution : Nat → Word Nat)
    {w : Word Nat} (inStratum : InParityStratum w) :
    InParityStratum (w.bind substitution) := by
  rcases inStratum with ⟨p, rfl⟩ | long
  · exact Or.inl ⟨p.bind substitution, bind_append p p substitution⟩
  · exact Or.inr (bind_preserves_long w substitution long)

private theorem shapeClass_symm
    {u v : Word Nat} (sameShape : ShapeClass u v) :
    ShapeClass v u := by
  rcases sameShape with equal | ⟨uShape, vShape⟩
  · exact Or.inl equal.symm
  · exact Or.inr ⟨vShape, uShape⟩

private theorem shapeClass_trans
    {u v w : Word Nat}
    (first : ShapeClass u v) (second : ShapeClass v w) :
    ShapeClass u w := by
  rcases first with equal | ⟨uShape, vShape⟩
  · subst v
    exact second
  · rcases second with equal | ⟨vShape', wShape⟩
    · subst w
      exact Or.inr ⟨uShape, vShape⟩
    · exact Or.inr ⟨uShape, wShape⟩

private theorem shapeClass_prepend
    (p : Word Nat) {u v : Word Nat}
    (sameShape : ShapeClass u v) :
    ShapeClass (p ++ u) (p ++ v) := by
  rcases sameShape with equal | ⟨uShape, vShape⟩
  · exact Or.inl (congrArg (fun w => p ++ w) equal)
  · refine Or.inr ⟨Or.inr ?_, Or.inr ?_⟩ <;>
      simp only [Word.toList_append, List.length_append]
    · have pPositive := word_length_positive p
      have uTwo := parityStratum_length_two uShape
      omega
    · have pPositive := word_length_positive p
      have vTwo := parityStratum_length_two vShape
      omega

private theorem shapeClass_appendRight
    (q : Word Nat) {u v : Word Nat}
    (sameShape : ShapeClass u v) :
    ShapeClass (u ++ q) (v ++ q) := by
  rcases sameShape with equal | ⟨uShape, vShape⟩
  · exact Or.inl (congrArg (fun w => w ++ q) equal)
  · refine Or.inr ⟨Or.inr ?_, Or.inr ?_⟩ <;>
      simp only [Word.toList_append, List.length_append]
    · have qPositive := word_length_positive q
      have uTwo := parityStratum_length_two uShape
      omega
    · have qPositive := word_length_positive q
      have vTwo := parityStratum_length_two vShape
      omega

private theorem shapeClass_subst
    (substitution : Nat → Word Nat)
    {u v : Word Nat} (sameShape : ShapeClass u v) :
    ShapeClass (u.bind substitution) (v.bind substitution) := by
  rcases sameShape with equal | ⟨uShape, vShape⟩
  · exact Or.inl (congrArg (fun w => w.bind substitution) equal)
  · exact Or.inr
      ⟨parityStratum_subst substitution uShape,
        parityStratum_subst substitution vShape⟩

private theorem basis_member_shapeClass
    (e : Identity Nat) (member : e ∈ basis) :
    ShapeClass e.lhs e.rhs := by
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact Or.inr
      ⟨Or.inl ⟨Word.singleton 0, rfl⟩,
        Or.inl ⟨Word.singleton 1, rfl⟩⟩
  · exact Or.inr ⟨Or.inr (by decide), Or.inr (by decide)⟩
  · exact Or.inr ⟨Or.inr (by decide), Or.inr (by decide)⟩
  · exact Or.inr ⟨Or.inr (by decide), Or.inr (by decide)⟩
  · exact Or.inr ⟨Or.inr (by decide), Or.inr (by decide)⟩

private theorem derives_shapeClass
    {u v : Word Nat} (derivation : Derives basis u v) :
    ShapeClass u v := by
  induction derivation with
  | fromBasis member =>
      exact basis_member_shapeClass _ member
  | refl =>
      exact Or.inl rfl
  | symm _ ih =>
      exact shapeClass_symm ih
  | trans _ _ ih₁ ih₂ =>
      exact shapeClass_trans ih₁ ih₂
  | prepend p _ ih =>
      exact shapeClass_prepend p ih
  | appendRight _ q ih =>
      exact shapeClass_appendRight q ih
  | subst _ substitution ih =>
      exact shapeClass_subst substitution ih

private def cyclicFiniteCommonSquareLaw : Identity (Fin 2) :=
  Identity.mk (Word.mk 0 [0]) (Word.mk 1 [1])

private def cyclicFiniteSquareMiddleLaw : Identity (Fin 2) :=
  Identity.mk (Word.mk 0 [0, 0]) (Word.mk 1 [0, 1])

private def cyclicFiniteSuffixCommutationLaw : Identity (Fin 3) :=
  Identity.mk (Word.mk 0 [1, 2]) (Word.mk 0 [2, 1])

private def cyclicFinitePrefixCommutationLaw : Identity (Fin 3) :=
  Identity.mk (Word.mk 0 [1, 2]) (Word.mk 1 [0, 2])

private def cyclicFiniteLongInsertionLaw : Identity (Fin 3) :=
  Identity.mk (Word.mk 0 [1, 2]) (Word.mk 0 [0, 0, 1, 2])

private theorem cyclicFiniteCommonSquareLaw_map :
    cyclicFiniteCommonSquareLaw.map Fin.val = commonSquareLaw := rfl

private theorem cyclicFiniteSquareMiddleLaw_map :
    cyclicFiniteSquareMiddleLaw.map Fin.val =
      SemigroupBasis.CoRoots.S5_58.squareMiddleLaw := rfl

private theorem cyclicFiniteSuffixCommutationLaw_map :
    cyclicFiniteSuffixCommutationLaw.map Fin.val =
      SemigroupBasis.CoRoots.S5_58.suffixCommutationLaw := rfl

private theorem cyclicFinitePrefixCommutationLaw_map :
    cyclicFinitePrefixCommutationLaw.map Fin.val =
      SemigroupBasis.CoRoots.S5_58.prefixCommutationLaw := rfl

private theorem cyclicFiniteLongInsertionLaw_map :
    cyclicFiniteLongInsertionLaw.map Fin.val =
      SemigroupBasis.CoRoots.S5_58.longInsertionLaw := rfl

private theorem cyclicTwo_models_basis :
    Models cyclicTwo.semigroup basis := by
  intro e member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · rw [cyclicFiniteCommonSquareLaw_map.symm]
    exact cyclicTwo.checkIdentityNat_sound
      cyclicFiniteCommonSquareLaw (by decide)
  · rw [cyclicFiniteSquareMiddleLaw_map.symm]
    exact cyclicTwo.checkIdentityNat_sound
      cyclicFiniteSquareMiddleLaw (by decide)
  · rw [cyclicFiniteSuffixCommutationLaw_map.symm]
    exact cyclicTwo.checkIdentityNat_sound
      cyclicFiniteSuffixCommutationLaw (by decide)
  · rw [cyclicFinitePrefixCommutationLaw_map.symm]
    exact cyclicTwo.checkIdentityNat_sound
      cyclicFinitePrefixCommutationLaw (by decide)
  · rw [cyclicFiniteLongInsertionLaw_map.symm]
    exact cyclicTwo.checkIdentityNat_sound
      cyclicFiniteLongInsertionLaw (by decide)

private theorem derives_parity
    {u v : Word Nat} (derivation : Derives basis u v) :
    SemigroupBasis.CoRoots.S5_58.SameParity u v := by
  have valid :
      (Identity.mk u v).SatisfiedBy cyclicTwo.semigroup := by
    intro valuation
    exact derivation.sound cyclicTwo_models_basis valuation
  exact cyclicValid_parity_eq (Identity.mk u v) valid

private theorem square_four_parity
    (p v : Word Nat)
    (parity :
      SemigroupBasis.CoRoots.S5_58.SameParity (p ++ p) v) :
    SemigroupBasis.CoRoots.S5_58.SameParity
      ((p ++ p) ++ (p ++ p)) v := by
  intro z
  have coordinate := parity z
  simp only [Word.toList_append, List.count_append] at coordinate ⊢
  omega

private theorem derivesSquareLong
    (p v : Word Nat)
    (vLong : 3 ≤ v.toList.length)
    (parity :
      SemigroupBasis.CoRoots.S5_58.SameParity (p ++ p) v) :
    Derives basis (p ++ p) v := by
  have expand := derivesCommonSquares p (p ++ p)
  have expandedLong :
      3 ≤ ((p ++ p) ++ (p ++ p)).toList.length := by
    simp only [Word.toList_append, List.length_append]
    have positive := word_length_positive p
    omega
  have normalize :=
    derivesLongOfParityEq
      ((p ++ p) ++ (p ++ p)) v expandedLong vLong
      (square_four_parity p v parity)
  exact Derives.trans expand normalize

/-- Any two members of the square-or-long stratum with equal parity are
derivably equal. -/
theorem derivesParityStratumOfSameParity
    (u v : Word Nat)
    (uShape : InParityStratum u)
    (vShape : InParityStratum v)
    (parity : SemigroupBasis.CoRoots.S5_58.SameParity u v) :
    Derives basis u v := by
  rcases uShape with ⟨p, rfl⟩ | uLong
  · rcases vShape with ⟨q, rfl⟩ | vLong
    · exact derivesCommonSquares p q
    · exact derivesSquareLong p v vLong parity
  · rcases vShape with ⟨q, rfl⟩ | vLong
    · exact Derives.symm <|
        derivesSquareLong q u uLong (fun z => (parity z).symm)
    · exact derivesLongOfParityEq u v uLong vLong parity

/-- Complete syntactic characterization of derivability from the five
published identities. -/
theorem derives_iff_exactBasisClass {u v : Word Nat} :
    Derives basis u v ↔ ExactBasisClass u v := by
  constructor
  · intro derivation
    rcases derives_shapeClass derivation with
      equal | ⟨uShape, vShape⟩
    · exact Or.inl equal
    · exact Or.inr ⟨uShape, vShape, derives_parity derivation⟩
  · intro sameClass
    rcases sameClass with equal | ⟨uShape, vShape, parity⟩
    · subst v
      exact Derives.refl _
    · exact derivesParityStratumOfSameParity
        u v uShape vShape parity

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
    InParityStratum (wordOfCons a [a]) := by
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

private theorem validPair_eq_of_support_and_order
    (T : FiniteTable) (left right : Fin T.order)
    (orderNe : T.mul left right ≠ T.mul right left)
    {a b c d : Nat}
    (valid :
      (Identity.mk (wordOfCons a [b]) (wordOfCons c [d])).SatisfiedBy
        T.semigroup)
    (support : ∀ z, z ∈ [a, b] ↔ z ∈ [c, d]) :
    a = c ∧ b = d := by
  by_cases hab : a = b
  · subst b
    have hc : c = a := by
      have member := (support c).mpr (by simp)
      simpa using member
    have hd : d = a := by
      have member := (support d).mpr (by simp)
      simpa using member
    subst c
    subst d
    exact ⟨rfl, rfl⟩
  · have hc : c = a ∨ c = b := by
      simpa using (support c).mpr (by simp)
    have hd : d = a ∨ d = b := by
      simpa using (support d).mpr (by simp)
    rcases hc with hc | hc
    · rcases hd with hd | hd
      · have bMember := (support b).mp (by simp)
        have hba : b = a := by simpa [hc, hd] using bMember
        exact False.elim (hab hba.symm)
      · exact ⟨hc.symm, hd.symm⟩
    · rcases hd with hd | hd
      · let valuation : Nat → Fin T.order :=
          fun z => if z = a then left else right
        have evaluated := valid valuation
        change
          T.mul (valuation a) (valuation b) =
            T.mul (valuation c) (valuation d) at evaluated
        rw [hc, hd] at evaluated
        have valueA : valuation a = left := by simp [valuation]
        have valueB : valuation b = right := by
          simp [valuation, Ne.symm hab]
        rw [valueA, valueB] at evaluated
        exact (orderNe evaluated).elim
      · have aMember := (support a).mp (by simp)
        have hab' : a = b := by simpa [hc, hd] using aMember
        exact False.elim (hab hab')

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

private theorem lengthTwo_class
    (T : FiniteTable)
    (left right : Fin T.order)
    (orderNe : T.mul left right ≠ T.mul right left)
    (e : Identity Nat) (valid : e.SatisfiedBy T.semigroup)
    (parity :
      SemigroupBasis.CoRoots.S5_58.SameParity e.lhs e.rhs)
    (lhsTwo : e.lhs.toList.length = 2)
    (rhsTwo : e.rhs.toList.length = 2) :
    ExactBasisClass e.lhs e.rhs := by
  obtain ⟨a, b, lhsEq⟩ := pair_of_length_two e.lhs lhsTwo
  obtain ⟨c, d, rhsEq⟩ := pair_of_length_two e.rhs rhsTwo
  have validPairs :
      (Identity.mk (wordOfCons a [b]) (wordOfCons c [d])).SatisfiedBy
        T.semigroup := by
    intro valuation
    simpa [lhsEq, rhsEq] using valid valuation
  have parityPairs :
      SemigroupBasis.CoRoots.S5_58.SameParity
        (wordOfCons a [b]) (wordOfCons c [d]) := by
    simpa [lhsEq, rhsEq] using parity
  rw [lhsEq, rhsEq]
  have listParity :
      ∀ z, [a, b].count z % 2 = [c, d].count z % 2 := by
    simpa [wordOfCons, Word.toList] using parityPairs
  by_cases ab : a = b
  · subst b
    have cd := rhs_square_of_lhs_square_parity listParity
    subst d
    exact Or.inr
      ⟨squarePair_inParityStratum a,
        squarePair_inParityStratum c, parityPairs⟩
  · have support := distinct_pair_support_of_parity ab listParity
    have coordinates :=
      validPair_eq_of_support_and_order
        T left right orderNe validPairs support
    rcases coordinates with ⟨rfl, rfl⟩
    exact Or.inl rfl

/-- Generic unrestricted completeness for the `S5_16` basis. The table must
model the basis, recover coordinate parity, preserve singleton words, separate
one ordered pair from its reversal, and separate that pair from its
same-parity long expansion. -/
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
    (orderNe : T.mul left right ≠ T.mul right left)
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
      · exact derives_iff_exactBasisClass.mpr <|
          lengthTwo_class T left right orderNe
            e valid parity lhsTwo rhsTwo
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

end SemigroupBasis.CoRoots.S5_16
