import SemigroupBasis.Examples.CommonSquareParityThree
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_58

open SemigroupBasis
open SemigroupBasis.Examples

def xxx : Word Nat := ⟨0, [0, 0]⟩
def xyy : Word Nat := ⟨0, [1, 1]⟩
def yxy : Word Nat := ⟨1, [0, 1]⟩
def yyx : Word Nat := ⟨1, [1, 0]⟩
def xyz : Word Nat := ⟨0, [1, 2]⟩
def xzy : Word Nat := ⟨0, [2, 1]⟩
def yxz : Word Nat := ⟨1, [0, 2]⟩
def xxxyz : Word Nat := ⟨0, [0, 0, 1, 2]⟩

def squareRightLaw : Identity Nat := ⟨xxx, xyy⟩
def squareMiddleLaw : Identity Nat := ⟨xxx, yxy⟩
def squareLeftLaw : Identity Nat := ⟨xxx, yyx⟩
def suffixCommutationLaw : Identity Nat := ⟨xyz, xzy⟩
def prefixCommutationLaw : Identity Nat := ⟨xyz, yxz⟩
def longInsertionLaw : Identity Nat := ⟨xyz, xxxyz⟩

/-- The common published six-identity basis of the `S5_58` family. -/
def basis : List (Identity Nat) :=
  [squareRightLaw, squareMiddleLaw, squareLeftLaw,
    suffixCommutationLaw, prefixCommutationLaw, longInsertionLaw]

def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private def instantiateThreeWords
    (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

/-- Behind one fixed nonempty marker, any square may be replaced by any
other square. -/
theorem derivesContextSquares (marker u v : Word Nat) :
    Derives basis
      (marker ++ (u ++ u)) (marker ++ (v ++ v)) := by
  have hbase :
      Derives basis xxx xyy :=
    Derives.fromBasis (e := squareRightLaw) <| List.Mem.head _
  have hu :=
    Derives.subst hbase (instantiateThreeWords marker u v)
  have hv :=
    Derives.subst hbase (instantiateThreeWords marker v u)
  exact Derives.trans
    (by
      simpa [basis, squareRightLaw, xxx, xyy,
        instantiateThreeWords, Word.bind, Word.append,
        Word.singleton, Word.append_assoc] using Derives.symm hu)
    (by
      simpa [basis, squareRightLaw, xxx, xyy,
        instantiateThreeWords, Word.bind, Word.append,
        Word.singleton, Word.append_assoc] using hv)

/-- Swap the last two nonempty blocks after a fixed nonempty marker. -/
theorem derivesContextCommutativity (marker u v : Word Nat) :
    Derives basis
      (marker ++ (u ++ v)) (marker ++ (v ++ u)) := by
  have hbase :
      Derives basis xyz xzy :=
    Derives.fromBasis (e := suffixCommutationLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.head _
  have h :=
    Derives.subst hbase (instantiateThreeWords marker u v)
  simpa [basis, suffixCommutationLaw, xyz, xzy,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

/-- Swap the first two nonempty blocks before a fixed nonempty suffix. -/
theorem derivesPrefixSwap (u v suffix : Word Nat) :
    Derives basis
      ((u ++ v) ++ suffix) ((v ++ u) ++ suffix) := by
  have hbase :
      Derives basis xyz yxz :=
    Derives.fromBasis (e := prefixCommutationLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _
  have h :=
    Derives.subst hbase (instantiateThreeWords u v suffix)
  simpa [basis, prefixCommutationLaw, xyz, yxz,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

/-- Insert two extra copies of the first nonempty block in a product of
three nonempty blocks. -/
theorem derivesLongInsertion (u v w : Word Nat) :
    Derives basis
      ((u ++ v) ++ w) ((((u ++ u) ++ u) ++ v) ++ w) := by
  have hbase :
      Derives basis xyz xxxyz :=
    Derives.fromBasis (e := longInsertionLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.head _
  have h :=
    Derives.subst hbase (instantiateThreeWords u v w)
  simpa [basis, longInsertionLaw, xyz, xxxyz,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

/-- Behind one fixed marker, replay the common-square insertion
`uv = uuuv`. -/
theorem derivesContextInsertion (marker u v : Word Nat) :
    Derives basis
      (marker ++ (u ++ v))
      (marker ++ ((((u ++ u) ++ u) ++ v))) := by
  have enter := derivesPrefixSwap marker u v
  have expand := derivesLongInsertion u marker v
  have exit := derivesPrefixSwap ((u ++ u) ++ u) marker v
  exact Derives.trans
    (by simpa [Word.append_assoc] using enter) <|
    Derives.trans
      (by simpa [Word.append_assoc] using expand)
      (by simpa [Word.append_assoc] using exit)

private theorem bind_append (u v : Word Nat) (σ : Nat → Word Nat) :
    (u ++ v).bind σ = u.bind σ ++ v.bind σ := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind (w : Word Nat)
    (τ σ : Nat → Word Nat) :
    (w.bind τ).bind σ = w.bind (fun x => (τ x).bind σ) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (w : Word Nat) :
    w.bind Word.singleton = w := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- Every derivation from the common-square parity basis can be replayed
behind one fixed nonempty marker. -/
theorem liftCommonSquare
    {u v : Word Nat}
    (h : Derives commonSquareParityBasis u v)
    (marker : Word Nat) (σ : Nat → Word Nat) :
    Derives basis
      (marker ++ u.bind σ) (marker ++ v.bind σ) := by
  induction h generalizing marker σ with
  | fromBasis hmem =>
      simp only [commonSquareParityBasis, List.mem_cons,
        List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl
      · simpa [commonSquareLaw, commonSquareXX, commonSquareYY,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
            derivesContextSquares marker (σ 0) (σ 1)
      · simpa [commonSquareCommutativityLaw, commonSquareXY,
          commonSquareYX, Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
            derivesContextCommutativity marker (σ 0) (σ 1)
      · simpa [commonSquareInsertionLaw, commonSquareXY,
          commonSquareXXXY, Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
            derivesContextInsertion marker (σ 0) (σ 1)
  | refl =>
      exact Derives.refl _
  | symm _ ih =>
      exact Derives.symm (ih marker σ)
  | trans _ _ ih₁ ih₂ =>
      exact Derives.trans (ih₁ marker σ) (ih₂ marker σ)
  | prepend p _ ih =>
      simpa [bind_append, Word.append_assoc] using
        ih (marker ++ p.bind σ) σ
  | appendRight _ q ih =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight (ih marker σ) (q.bind σ)
  | subst _ τ ih =>
      simpa [bind_bind] using
        ih marker (fun x => (τ x).bind σ)

private theorem derivesTripleReplacement (u marker : Word Nat) :
    Derives basis
      ((u ++ u) ++ u) ((marker ++ marker) ++ u) := by
  have hbase :
      Derives basis xxx yyx :=
    Derives.fromBasis (e := squareLeftLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _
  have h :=
    Derives.subst hbase (instantiateThreeWords u marker marker)
  simpa [basis, squareLeftLaw, xxx, yyx,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

/-- Insert a square of an arbitrary marker before any product already split
into three nonempty blocks. -/
theorem derivesInsertSquare
    (marker u v w : Word Nat) :
    Derives basis
      ((u ++ v) ++ w)
      ((marker ++ marker) ++ ((u ++ v) ++ w)) := by
  have expand := derivesLongInsertion u v w
  have replace :=
    Derives.appendRight
      (Derives.appendRight (derivesTripleReplacement u marker) v) w
  exact Derives.trans expand <| by
    simpa [Word.append_assoc] using replace

/-- Insert a square of an arbitrary marker before any word of length at
least three. -/
theorem derivesInsertSquareLong
    (marker w : Word Nat) (long : 3 ≤ w.toList.length) :
    Derives basis w ((marker ++ marker) ++ w) := by
  cases w with
  | mk head tail =>
      cases tail with
      | nil =>
          simp [Word.toList] at long
      | cons second rest =>
          cases rest with
          | nil =>
              simp [Word.toList] at long
          | cons third more =>
              have inserted :=
                derivesInsertSquare marker
                  (Word.singleton head) (Word.singleton second)
                  (wordOfCons third more)
              simpa [wordOfCons, Word.singleton, Word.append,
                Word.append_assoc] using inserted

private theorem commonSquareDerivesOfParity
    (u v : Word Nat)
    (uProduct : u.tail ≠ [])
    (vProduct : v.tail ≠ [])
    (parityEq :
      ∀ z, u.toList.count z % 2 =
        v.toList.count z % 2) :
    Derives commonSquareParityBasis u v := by
  have lhsTail :
      ∃ x xs, u.tail = x :: xs := by
    cases htail : u.tail with
    | nil => exact False.elim (uProduct htail)
    | cons x xs => exact ⟨x, xs, rfl⟩
  have rhsTail :
      ∃ x xs, v.tail = x :: xs := by
    cases htail : v.tail with
    | nil => exact False.elim (vProduct htail)
    | cons x xs => exact ⟨x, xs, rfl⟩
  obtain ⟨lx, lxs, lhsTailEq⟩ := lhsTail
  obtain ⟨rx, rxs, rhsTailEq⟩ := rhsTail
  have reducedPerm :
      (parityReduce u.toList).Perm
        (parityReduce v.toList) :=
    parityReduce_perm_of_parity_eq parityEq
  have lhsNormal := commonSquareParityDerivesNormal u
  have rhsNormal := commonSquareParityDerivesNormal v
  cases hlp : parityReduce u.toList with
  | nil =>
      rw [hlp] at reducedPerm
      have hrp : parityReduce v.toList = [] :=
        reducedPerm.nil_eq.symm
      rw [commonSquareParityNormal, lhsTailEq, hlp] at lhsNormal
      rw [commonSquareParityNormal, rhsTailEq, hrp] at rhsNormal
      exact Derives.trans lhsNormal (Derives.symm rhsNormal)
  | cons x xs =>
      cases hrp : parityReduce v.toList with
      | nil =>
          rw [hlp, hrp] at reducedPerm
          exact False.elim (List.not_perm_cons_nil reducedPerm)
      | cons y ys =>
          rw [commonSquareParityNormal, lhsTailEq, hlp] at lhsNormal
          rw [commonSquareParityNormal, rhsTailEq, hrp] at rhsNormal
          rw [hlp, hrp] at reducedPerm
          have cyclicPermutation :=
            cyclicDerivesPermutation
              (wordOfCons x xs) (wordOfCons y ys) reducedPerm
          have commonPermutation :=
            commonSquareLiftCyclic cyclicPermutation (Word.singleton 0)
          exact Derives.trans lhsNormal <|
            Derives.trans
              (by
                simpa [commonSquareMarker, wordOfCons,
                  Word.append_assoc] using commonPermutation)
              (Derives.symm rhsNormal)

/-- Every two long words with the same coordinate-parity vector are
derivably equal. -/
theorem derivesLongOfParityEq
    (u v : Word Nat)
    (uLong : 3 ≤ u.toList.length)
    (vLong : 3 ≤ v.toList.length)
    (parityEq :
      ∀ z, u.toList.count z % 2 =
        v.toList.count z % 2) :
    Derives basis u v := by
  let marker := Word.singleton 0
  have insertU := derivesInsertSquareLong marker u uLong
  have insertV := derivesInsertSquareLong marker v vLong
  have markerUProduct : (marker ++ u).tail ≠ [] := by
    cases u
    simp [marker, Word.singleton]
  have markerVProduct : (marker ++ v).tail ≠ [] := by
    cases v
    simp [marker, Word.singleton]
  have extendedParity :
      ∀ z,
        (marker ++ u).toList.count z % 2 =
          (marker ++ v).toList.count z % 2 := by
    intro z
    simp only [Word.toList_append, List.count_append]
    have same := parityEq z
    omega
  have common :=
    commonSquareDerivesOfParity
      (marker ++ u) (marker ++ v)
      markerUProduct markerVProduct extendedParity
  have lifted := liftCommonSquare common marker Word.singleton
  rw [bind_singleton, bind_singleton] at lifted
  exact Derives.trans insertU <|
    Derives.trans
      (by simpa [marker, Word.append_assoc] using lifted)
      (Derives.symm insertV)

/-- Coordinate parity is the complete invariant among long words. -/
def SameParity (u v : Word Nat) : Prop :=
  ∀ z, u.toList.count z % 2 = v.toList.count z % 2

/-- The exact congruence generated by the `S5_58` basis: words of lengths
one and two are literal, while longer words are classified by coordinate
parity. -/
def ExactBasisClass (u v : Word Nat) : Prop :=
  u = v ∨
    (3 ≤ u.toList.length ∧
      3 ≤ v.toList.length ∧
      SameParity u v)

private def LengthClass (u v : Word Nat) : Prop :=
  u = v ∨
    (3 ≤ u.toList.length ∧ 3 ≤ v.toList.length)

private theorem lengthClass_symm {u v : Word Nat}
    (sameClass : LengthClass u v) :
    LengthClass v u := by
  rcases sameClass with equal | ⟨uLong, vLong⟩
  · exact Or.inl equal.symm
  · exact Or.inr ⟨vLong, uLong⟩

private theorem lengthClass_trans {u v w : Word Nat}
    (first : LengthClass u v)
    (second : LengthClass v w) :
    LengthClass u w := by
  rcases first with equal | ⟨uLong, vLong⟩
  · subst v
    exact second
  · rcases second with equal | ⟨vLong', wLong⟩
    · subst w
      exact Or.inr ⟨uLong, vLong⟩
    · exact Or.inr ⟨uLong, wLong⟩

private theorem lengthClass_prepend (p : Word Nat)
    {u v : Word Nat} (sameClass : LengthClass u v) :
    LengthClass (p ++ u) (p ++ v) := by
  rcases sameClass with equal | ⟨uLong, vLong⟩
  · exact Or.inl (congrArg (fun w => p ++ w) equal)
  · refine Or.inr ⟨?_, ?_⟩ <;>
      simp only [Word.toList_append, List.length_append] <;> omega

private theorem lengthClass_appendRight (q : Word Nat)
    {u v : Word Nat} (sameClass : LengthClass u v) :
    LengthClass (u ++ q) (v ++ q) := by
  rcases sameClass with equal | ⟨uLong, vLong⟩
  · exact Or.inl (congrArg (fun w => w ++ q) equal)
  · refine Or.inr ⟨?_, ?_⟩ <;>
      simp only [Word.toList_append, List.length_append] <;> omega

private theorem list_length_le_flatMap_words
    (letters : List Nat) (substitution : Nat → Word Nat) :
    letters.length ≤
      (letters.flatMap fun letter => (substitution letter).toList).length := by
  induction letters with
  | nil =>
      simp
  | cons letter rest ih =>
      simp only [List.length_cons, List.flatMap_cons, List.length_append]
      have imagePositive : 1 ≤ (substitution letter).toList.length := by
        cases substitution letter
        simp [Word.toList]
      omega

private theorem bind_preserves_long
    (w : Word Nat) (substitution : Nat → Word Nat)
    (long : 3 ≤ w.toList.length) :
    3 ≤ (w.bind substitution).toList.length := by
  rw [Word.toList_bind]
  exact Nat.le_trans long
    (list_length_le_flatMap_words w.toList substitution)

private theorem lengthClass_subst
    (substitution : Nat → Word Nat)
    {u v : Word Nat} (sameClass : LengthClass u v) :
    LengthClass (u.bind substitution) (v.bind substitution) := by
  rcases sameClass with equal | ⟨uLong, vLong⟩
  · exact Or.inl (congrArg (fun w => w.bind substitution) equal)
  · exact Or.inr
      ⟨bind_preserves_long u substitution uLong,
        bind_preserves_long v substitution vLong⟩

private theorem basis_member_lengthClass
    (e : Identity Nat) (member : e ∈ basis) :
    LengthClass e.lhs e.rhs := by
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [LengthClass, squareRightLaw, squareMiddleLaw,
      squareLeftLaw, suffixCommutationLaw, prefixCommutationLaw,
      longInsertionLaw, xxx, xyy, yxy, yyx, xyz, xzy, yxz,
      xxxyz, Word.toList]

private theorem derives_lengthClass {u v : Word Nat}
    (derivation : Derives basis u v) :
    LengthClass u v := by
  induction derivation with
  | fromBasis member =>
      exact basis_member_lengthClass _ member
  | refl =>
      exact Or.inl rfl
  | symm _ ih =>
      exact lengthClass_symm ih
  | trans _ _ ih₁ ih₂ =>
      exact lengthClass_trans ih₁ ih₂
  | prepend p _ ih =>
      exact lengthClass_prepend p ih
  | appendRight _ q ih =>
      exact lengthClass_appendRight q ih
  | subst _ substitution ih =>
      exact lengthClass_subst substitution ih

private def cyclicFiniteSquareRightLaw : Identity (Fin 2) :=
  Identity.mk (Word.mk 0 [0, 0]) (Word.mk 0 [1, 1])

private def cyclicFiniteSquareMiddleLaw : Identity (Fin 2) :=
  Identity.mk (Word.mk 0 [0, 0]) (Word.mk 1 [0, 1])

private def cyclicFiniteSquareLeftLaw : Identity (Fin 2) :=
  Identity.mk (Word.mk 0 [0, 0]) (Word.mk 1 [1, 0])

private def cyclicFiniteSuffixCommutationLaw : Identity (Fin 3) :=
  Identity.mk (Word.mk 0 [1, 2]) (Word.mk 0 [2, 1])

private def cyclicFinitePrefixCommutationLaw : Identity (Fin 3) :=
  Identity.mk (Word.mk 0 [1, 2]) (Word.mk 1 [0, 2])

private def cyclicFiniteLongInsertionLaw : Identity (Fin 3) :=
  Identity.mk (Word.mk 0 [1, 2]) (Word.mk 0 [0, 0, 1, 2])

private theorem cyclicFiniteSquareRightLaw_map :
    cyclicFiniteSquareRightLaw.map Fin.val = squareRightLaw := rfl

private theorem cyclicFiniteSquareMiddleLaw_map :
    cyclicFiniteSquareMiddleLaw.map Fin.val = squareMiddleLaw := rfl

private theorem cyclicFiniteSquareLeftLaw_map :
    cyclicFiniteSquareLeftLaw.map Fin.val = squareLeftLaw := rfl

private theorem cyclicFiniteSuffixCommutationLaw_map :
    cyclicFiniteSuffixCommutationLaw.map Fin.val =
      suffixCommutationLaw := rfl

private theorem cyclicFinitePrefixCommutationLaw_map :
    cyclicFinitePrefixCommutationLaw.map Fin.val =
      prefixCommutationLaw := rfl

private theorem cyclicFiniteLongInsertionLaw_map :
    cyclicFiniteLongInsertionLaw.map Fin.val =
      longInsertionLaw := rfl

private theorem cyclicTwo_models_basis :
    Models cyclicTwo.semigroup basis := by
  intro e he
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [cyclicFiniteSquareRightLaw_map.symm]
    exact cyclicTwo.checkIdentityNat_sound
      cyclicFiniteSquareRightLaw (by decide)
  · rw [cyclicFiniteSquareMiddleLaw_map.symm]
    exact cyclicTwo.checkIdentityNat_sound
      cyclicFiniteSquareMiddleLaw (by decide)
  · rw [cyclicFiniteSquareLeftLaw_map.symm]
    exact cyclicTwo.checkIdentityNat_sound
      cyclicFiniteSquareLeftLaw (by decide)
  · rw [cyclicFiniteSuffixCommutationLaw_map.symm]
    exact cyclicTwo.checkIdentityNat_sound
      cyclicFiniteSuffixCommutationLaw (by decide)
  · rw [cyclicFinitePrefixCommutationLaw_map.symm]
    exact cyclicTwo.checkIdentityNat_sound
      cyclicFinitePrefixCommutationLaw (by decide)
  · rw [cyclicFiniteLongInsertionLaw_map.symm]
    exact cyclicTwo.checkIdentityNat_sound
      cyclicFiniteLongInsertionLaw (by decide)

private theorem derives_parity {u v : Word Nat}
    (derivation : Derives basis u v) :
    SameParity u v := by
  have valid :
      (Identity.mk u v).SatisfiedBy cyclicTwo.semigroup := by
    intro valuation
    exact derivation.sound cyclicTwo_models_basis valuation
  exact cyclicValid_parity_eq (Identity.mk u v) valid

/-- Complete syntactic characterization of derivability from the six
published identities. -/
theorem derives_iff_exactBasisClass {u v : Word Nat} :
    Derives basis u v ↔ ExactBasisClass u v := by
  constructor
  · intro derivation
    rcases derives_lengthClass derivation with
      equal | ⟨uLong, vLong⟩
    · exact Or.inl equal
    · exact Or.inr
        ⟨uLong, vLong, derives_parity derivation⟩
  · intro sameClass
    rcases sameClass with equal | ⟨uLong, vLong, parity⟩
    · subst v
      exact Derives.refl _
    · exact derivesLongOfParityEq u v uLong vLong parity

private theorem lengthOne_eq_of_parity
    (u v : Word Nat)
    (uOne : u.toList.length = 1)
    (vOne : v.toList.length = 1)
    (parity : SameParity u v) :
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

private theorem validPair_eq_of_support_and_order
    (T : FiniteTable) (left right : Fin T.order)
    (orderNe : T.mul left right ≠ T.mul right left)
    {a b c d : Nat}
    (valid :
      (Identity.mk (wordOfCons a [b]) (wordOfCons c [d])).SatisfiedBy
        T.semigroup)
    (support :
      ∀ z, z ∈ [a, b] ↔ z ∈ [c, d]) :
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
        have hba : b = a := by
          simpa [hc, hd] using bMember
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
        have valueA : valuation a = left := by
          simp [valuation]
        have valueB : valuation b = right := by
          simp [valuation, Ne.symm hab]
        rw [valueA, valueB] at evaluated
        exact (orderNe evaluated).elim
      · have aMember := (support a).mp (by simp)
        have hab' : a = b := by
          simpa [hc, hd] using aMember
        exact False.elim (hab hab')

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
      have rightTwo : [a, a].count a = 2 := by
        simp
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
    have rightBound :=
      List.count_le_length (a := z) (l := [c, d])
    have rightPositive : 0 < [c, d].count z := by
      omega
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
    have leftBound :=
      List.count_le_length (a := z) (l := [a, b])
    have leftPositive : 0 < [a, b].count z := by
      omega
    exact List.count_pos_iff.mp leftPositive

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
    have leftTwo : [a, a].count a = 2 := by
      simp
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

private theorem validLengthTwo_eq_of_parity_and_separation
    (T : FiniteTable)
    (orderLeft orderRight squareLeft squareRight : Fin T.order)
    (orderNe :
      T.mul orderLeft orderRight ≠
        T.mul orderRight orderLeft)
    (squareNe :
      T.mul squareLeft squareLeft ≠
        T.mul squareRight squareRight)
    (e : Identity Nat) (valid : e.SatisfiedBy T.semigroup)
    (parity : SameParity e.lhs e.rhs)
    (lhsTwo : e.lhs.toList.length = 2)
    (rhsTwo : e.rhs.toList.length = 2) :
    e.lhs = e.rhs := by
  cases e with
  | mk lhs rhs =>
      cases lhs with
      | mk a lhsTail =>
          cases lhsTail with
          | nil =>
              simp [Word.toList] at lhsTwo
          | cons b lhsRest =>
              cases lhsRest with
              | nil =>
                  cases rhs with
                  | mk c rhsTail =>
                      cases rhsTail with
                      | nil =>
                          simp [Word.toList] at rhsTwo
                      | cons d rhsRest =>
                          cases rhsRest with
                          | nil =>
                              have listParity :
                                  ∀ z,
                                    [a, b].count z % 2 =
                                      [c, d].count z % 2 := by
                                simpa [SameParity, wordOfCons,
                                  Word.toList] using parity
                              by_cases ab : a = b
                              · subst b
                                have cd :
                                    c = d :=
                                  rhs_square_of_lhs_square_parity
                                    listParity
                                subst d
                                by_cases ac : a = c
                                · subst c
                                  rfl
                                · let valuation : Nat → Fin T.order :=
                                    fun z =>
                                      if z = a then squareLeft
                                      else squareRight
                                  have evaluated := valid valuation
                                  change
                                    T.mul (valuation a) (valuation a) =
                                      T.mul (valuation c) (valuation c)
                                    at evaluated
                                  have valueA :
                                      valuation a = squareLeft := by
                                    simp [valuation]
                                  have valueC :
                                      valuation c = squareRight := by
                                    simp [valuation, Ne.symm ac]
                                  rw [valueA, valueC] at evaluated
                                  exact (squareNe evaluated).elim
                              · have support :=
                                  distinct_pair_support_of_parity
                                    ab listParity
                                have coordinates :=
                                  validPair_eq_of_support_and_order
                                    T orderLeft orderRight orderNe
                                    valid support
                                rcases coordinates with ⟨rfl, rfl⟩
                                rfl
                          | cons next more =>
                              simp [Word.toList] at rhsTwo
              | cons next more =>
                  simp [Word.toList] at lhsTwo

/-- Generic unrestricted completeness for the `S5_58` basis. A finite table
only has to model the basis, recover coordinate parity and the length stratum
capped at three, distinguish one ordered pair from its reversal, and
distinguish two squares. -/
theorem basis_complete_of_separates
    (T : FiniteTable)
    (modelsT : Models T.semigroup basis)
    (parityT :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        SameParity e.lhs e.rhs)
    (lengthOneT :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        (e.lhs.toList.length = 1 ↔
          e.rhs.toList.length = 1))
    (lengthTwoT :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        (e.lhs.toList.length = 2 ↔
          e.rhs.toList.length = 2))
    (orderLeft orderRight squareLeft squareRight : Fin T.order)
    (orderNe :
      T.mul orderLeft orderRight ≠
        T.mul orderRight orderLeft)
    (squareNe :
      T.mul squareLeft squareLeft ≠
        T.mul squareRight squareRight) :
    BasisFor T.semigroup basis := by
  refine ⟨modelsT, ?_⟩
  intro e valid
  have parity := parityT e valid
  by_cases lhsOne : e.lhs.toList.length = 1
  · have rhsOne : e.rhs.toList.length = 1 := by
      exact (lengthOneT e valid).mp lhsOne
    have words :=
      lengthOne_eq_of_parity e.lhs e.rhs lhsOne rhsOne parity
    rw [words]
    exact Derives.refl _
  · by_cases lhsTwo : e.lhs.toList.length = 2
    · have rhsTwo : e.rhs.toList.length = 2 := by
        exact (lengthTwoT e valid).mp lhsTwo
      have words :=
        validLengthTwo_eq_of_parity_and_separation
          T orderLeft orderRight squareLeft squareRight
          orderNe squareNe e valid parity lhsTwo rhsTwo
      rw [words]
      exact Derives.refl _
    · have lhsLong : 3 ≤ e.lhs.toList.length := by
        have lhsPositive : 0 < e.lhs.toList.length := by
          simp [Word.toList]
        omega
      have rhsLong : 3 ≤ e.rhs.toList.length := by
        have rhsPositive : 0 < e.rhs.toList.length := by
          simp [Word.toList]
        have rhsNotOne : e.rhs.toList.length ≠ 1 := by
          intro rhsOne
          exact lhsOne ((lengthOneT e valid).mpr rhsOne)
        have rhsNotTwo : e.rhs.toList.length ≠ 2 := by
          intro rhsTwo
          exact lhsTwo ((lengthTwoT e valid).mpr rhsTwo)
        omega
      exact derivesLongOfParityEq
        e.lhs e.rhs lhsLong rhsLong parity

end SemigroupBasis.CoRoots.S5_58
