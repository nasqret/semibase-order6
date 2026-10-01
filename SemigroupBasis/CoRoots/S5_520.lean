import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_520

open SemigroupBasis

def xxx : Word Nat := ⟨0, [0, 0]⟩
def xxxx : Word Nat := ⟨0, [0, 0, 0]⟩
def xxy : Word Nat := ⟨0, [0, 1]⟩
def xyx : Word Nat := ⟨0, [1, 0]⟩
def xyy : Word Nat := ⟨0, [1, 1]⟩
def xxxy : Word Nat := ⟨0, [0, 0, 1]⟩
def xyz : Word Nat := ⟨0, [1, 2]⟩
def xzy : Word Nat := ⟨0, [2, 1]⟩
def xxyz : Word Nat := ⟨0, [0, 1, 2]⟩

def powerLaw : Identity Nat := ⟨xxx, xxxx⟩
def firstSwapLaw : Identity Nat := ⟨xxy, xyx⟩
def transferLaw : Identity Nat := ⟨xxy, xyy⟩
def heavyInsertionLaw : Identity Nat := ⟨xxy, xxxy⟩
def suffixCommutationLaw : Identity Nat := ⟨xyz, xzy⟩
def longInsertionLaw : Identity Nat := ⟨xyz, xxyz⟩

/-- The common published six-identity basis of the `S5_520` family. -/
def basis : List (Identity Nat) :=
  [powerLaw, firstSwapLaw, transferLaw, heavyInsertionLaw,
    suffixCommutationLaw, longInsertionLaw]

def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private def instantiateThreeWords
    (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

/-- Transfer one duplicate of the first block to the final block. -/
theorem derivesTransfer (u v : Word Nat) :
    Derives basis ((u ++ u) ++ v) ((u ++ v) ++ v) := by
  have hbase : Derives basis xxy xyy :=
    Derives.fromBasis (e := transferLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _
  have h := Derives.subst hbase (instantiateThreeWords u v v)
  simpa [basis, transferLaw, xxy, xyy, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using h

/-- Swap two nonempty blocks after a fixed nonempty prefix. -/
theorem derivesSuffixSwap (p u v : Word Nat) :
    Derives basis ((p ++ u) ++ v) ((p ++ v) ++ u) := by
  have hbase : Derives basis xyz xzy :=
    Derives.fromBasis (e := suffixCommutationLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _
  have h := Derives.subst hbase (instantiateThreeWords p u v)
  simpa [basis, suffixCommutationLaw, xyz, xzy,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

/-- Duplicate the first block in a product of three nonempty blocks. -/
theorem derivesLongDuplication (u v w : Word Nat) :
    Derives basis ((u ++ v) ++ w) (((u ++ u) ++ v) ++ w) := by
  have hbase : Derives basis xyz xxyz :=
    Derives.fromBasis (e := longInsertionLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.head _
  have h := Derives.subst hbase (instantiateThreeWords u v w)
  simpa [basis, longInsertionLaw, xyz, xxyz,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

/-- Duplicate the final block in a product of three nonempty blocks. -/
theorem derivesRightDuplication (p u v : Word Nat) :
    Derives basis ((p ++ u) ++ v) (((p ++ u) ++ v) ++ v) := by
  have swapFirst := derivesSuffixSwap p u v
  have duplicatePrefix := derivesLongDuplication p v u
  have transfer :=
    Derives.appendRight (derivesTransfer p v) u
  have swapBack :=
    derivesSuffixSwap (p ++ v) v u
  have finish :=
    Derives.appendRight (derivesSuffixSwap p v u) v
  exact Derives.trans swapFirst <|
    Derives.trans duplicatePrefix <|
    Derives.trans
      (by simpa [Word.append_assoc] using transfer) <|
    Derives.trans
      (by simpa [Word.append_assoc] using swapBack) <| by
    simpa [Word.append_assoc] using finish

/-- Every permutation of a suffix is derivable while the first letter stays
fixed. -/
theorem derivesTailPermutation (head : Nat) {xs ys : List Nat}
    (permutation : xs.Perm ys) :
    Derives basis (wordOfCons head xs) (wordOfCons head ys) := by
  induction permutation generalizing head with
  | nil =>
      exact Derives.refl _
  | cons x _ ih =>
      have suffix := ih (head := x)
      simpa [wordOfCons, Word.singleton, Word.append] using
        Derives.prepend (Word.singleton head) suffix
  | swap x y xs =>
      cases xs with
      | nil =>
          simpa [wordOfCons, Word.singleton, Word.append,
            Word.append_assoc] using
              derivesSuffixSwap
                (Word.singleton head) (Word.singleton y)
                (Word.singleton x)
      | cons z zs =>
          have swapped :=
            Derives.appendRight
              (derivesSuffixSwap
                (Word.singleton head) (Word.singleton y)
                (Word.singleton x))
              (wordOfCons z zs)
          simpa [wordOfCons, Word.singleton, Word.append,
            Word.append_assoc] using swapped
  | trans _ _ ihFirst ihSecond =>
      exact Derives.trans (ihFirst (head := head))
        (ihSecond (head := head))

private theorem perm_cons_to_end (x : Nat) :
    ∀ xs : List Nat, (x :: xs).Perm (xs ++ [x])
  | [] => List.Perm.refl _
  | y :: ys =>
      (List.Perm.swap y x ys).trans <|
        List.Perm.cons y (perm_cons_to_end x ys)

/-- A long word may be expanded by one copy of any variable already in its
support. -/
theorem derivesAppendMember (w : Word Nat) (x : Nat)
    (hlong : 3 ≤ w.toList.length) (member : x ∈ w.toList) :
    Derives basis w (w ++ Word.singleton x) := by
  cases w with
  | mk head tail =>
      cases tail with
      | nil =>
          simp [Word.toList] at hlong
      | cons second rest =>
          cases rest with
          | nil =>
              simp [Word.toList] at hlong
          | cons third more =>
              by_cases xHead : x = head
              · subst x
                let suffix := wordOfCons third more
                have duplicate :=
                  derivesLongDuplication
                    (Word.singleton head) (Word.singleton second) suffix
                have moveToEnd :=
                  derivesTailPermutation head
                    (perm_cons_to_end head (second :: third :: more))
                exact Derives.trans
                  (by
                    simpa [suffix, wordOfCons, Word.singleton, Word.append,
                      Word.append_assoc] using duplicate)
                  (by
                    simpa [wordOfCons, Word.singleton, Word.append,
                      List.append_assoc] using moveToEnd)
              · have inTail : x ∈ second :: third :: more := by
                  simpa [Word.toList, xHead] using member
                let remaining := (second :: third :: more).erase x
                have remainingNonempty : remaining ≠ [] := by
                  intro empty
                  have lengthErase :=
                    List.length_erase_of_mem inTail
                  rw [show (second :: third :: more).erase x =
                    remaining by rfl, empty] at lengthErase
                  simp at lengthErase
                have arrange :
                    (second :: third :: more).Perm
                      (remaining ++ [x]) := by
                  exact
                    (List.perm_cons_erase inTail).trans <|
                      perm_cons_to_end x remaining
                cases remainingEq : remaining with
                | nil =>
                    exact False.elim (remainingNonempty remainingEq)
                | cons next later =>
                    have arrange' :
                        (second :: third :: more).Perm
                          ((next :: later) ++ [x]) := by
                      simpa [remainingEq] using arrange
                    have arranged :=
                      derivesTailPermutation head arrange'
                    have duplicate :=
                      derivesRightDuplication
                        (Word.singleton head)
                        (wordOfCons next later)
                        (Word.singleton x)
                    have restore :
                        (((next :: later) ++ [x]) ++ [x]).Perm
                          ((second :: third :: more) ++ [x]) := by
                      simpa using arrange'.symm.append_right [x]
                    have restored :=
                      derivesTailPermutation head restore
                    exact Derives.trans arranged <|
                      Derives.trans
                        (by
                          simpa [wordOfCons, Word.singleton, Word.append,
                            Word.append_assoc, List.append_assoc] using
                              duplicate)
                        (by
                          simpa [wordOfCons, Word.singleton, Word.append,
                            List.append_assoc] using restored)

theorem derivesAppendList (w : Word Nat) (xs : List Nat)
    (hlong : 3 ≤ w.toList.length)
    (supported : ∀ x, x ∈ xs → x ∈ w.toList) :
    Derives basis w ⟨w.head, w.tail ++ xs⟩ := by
  induction xs generalizing w with
  | nil =>
      simpa using Derives.refl w
  | cons x xs ih =>
      have xSupported : x ∈ w.toList :=
        supported x (List.Mem.head xs)
      have firstStep := derivesAppendMember w x hlong xSupported
      have appendedLong :
          3 ≤ (w ++ Word.singleton x).toList.length := by
        simp only [Word.toList_append, Word.toList_singleton,
          List.length_append, List.length_cons, List.length_nil]
        omega
      have restSupported :
          ∀ y, y ∈ xs →
            y ∈ (w ++ Word.singleton x).toList := by
        intro y hy
        rw [Word.toList_append]
        exact List.mem_append_left _ <|
          supported y (List.Mem.tail x hy)
      have restStep :=
        ih (w ++ Word.singleton x) appendedLong restSupported
      exact Derives.trans firstStep <| by
        simpa [Word.singleton, List.append_assoc] using restStep

/-- A long word may be expanded by any word whose support it contains. -/
theorem derivesContentExpansion (u v : Word Nat)
    (uLong : 3 ≤ u.toList.length)
    (supported : ∀ x, x ∈ v.toList → x ∈ u.toList) :
    Derives basis u (u ++ v) := by
  have expanded :=
    derivesAppendList u v.toList uLong supported
  simpa [Word.toList, Word.append] using expanded

/-- Concatenated words with the same first letter commute as whole blocks. -/
theorem derivesConcatSwap (u v : Word Nat)
    (heads : u.head = v.head) :
    Derives basis (u ++ v) (v ++ u) := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          simp only at heads
          subst vHead
          have permutation :
              (uTail ++ uHead :: vTail).Perm
                (vTail ++ uHead :: uTail) := by
            rw [List.perm_iff_count]
            intro z
            simp only [List.count_append, List.count_cons]
            omega
          simpa [wordOfCons, Word.append] using
            derivesTailPermutation uHead permutation

/-- Two words have the same support when they contain the same variables,
without regard to multiplicity. -/
def SameSupport (u v : Word Nat) : Prop :=
  ∀ z, z ∈ u.toList ↔ z ∈ v.toList

/-- The exact congruence generated by the `S5_520` basis: words of lengths
one and two are literal, while longer words are classified by first letter
and support. -/
def ExactBasisClass (u v : Word Nat) : Prop :=
  u = v ∨
    (3 ≤ u.toList.length ∧
      3 ≤ v.toList.length ∧
      u.head = v.head ∧
      SameSupport u v)

private theorem sameSupport_refl (u : Word Nat) :
    SameSupport u u := by
  intro z
  rfl

private theorem sameSupport_symm {u v : Word Nat}
    (support : SameSupport u v) :
    SameSupport v u := by
  intro z
  exact (support z).symm

private theorem sameSupport_trans {u v w : Word Nat}
    (first : SameSupport u v)
    (second : SameSupport v w) :
    SameSupport u w := by
  intro z
  exact (first z).trans (second z)

private theorem exactBasisClass_symm {u v : Word Nat}
    (sameClass : ExactBasisClass u v) :
    ExactBasisClass v u := by
  rcases sameClass with equal | ⟨uLong, vLong, heads, support⟩
  · exact Or.inl equal.symm
  · exact Or.inr
      ⟨vLong, uLong, heads.symm, sameSupport_symm support⟩

private theorem exactBasisClass_trans {u v w : Word Nat}
    (first : ExactBasisClass u v)
    (second : ExactBasisClass v w) :
    ExactBasisClass u w := by
  rcases first with equal | ⟨uLong, vLong, headsUV, supportUV⟩
  · subst v
    exact second
  · rcases second with equal | ⟨vLong', wLong, headsVW, supportVW⟩
    · subst w
      exact Or.inr ⟨uLong, vLong, headsUV, supportUV⟩
    · exact Or.inr
        ⟨uLong, wLong, headsUV.trans headsVW,
          sameSupport_trans supportUV supportVW⟩

private theorem exactBasisClass_prepend (p : Word Nat)
    {u v : Word Nat} (sameClass : ExactBasisClass u v) :
    ExactBasisClass (p ++ u) (p ++ v) := by
  rcases sameClass with equal | ⟨uLong, vLong, heads, support⟩
  · exact Or.inl (congrArg (fun w => p ++ w) equal)
  · refine Or.inr ⟨?_, ?_, rfl, ?_⟩
    · simp only [Word.toList_append, List.length_append]
      omega
    · simp only [Word.toList_append, List.length_append]
      omega
    · intro z
      simp only [Word.toList_append, List.mem_append]
      constructor
      · rintro (inPrefix | inU)
        · exact Or.inl inPrefix
        · exact Or.inr ((support z).mp inU)
      · rintro (inPrefix | inV)
        · exact Or.inl inPrefix
        · exact Or.inr ((support z).mpr inV)

private theorem exactBasisClass_appendRight (q : Word Nat)
    {u v : Word Nat} (sameClass : ExactBasisClass u v) :
    ExactBasisClass (u ++ q) (v ++ q) := by
  rcases sameClass with equal | ⟨uLong, vLong, heads, support⟩
  · exact Or.inl (congrArg (fun w => w ++ q) equal)
  · refine Or.inr ⟨?_, ?_, heads, ?_⟩
    · simp only [Word.toList_append, List.length_append]
      omega
    · simp only [Word.toList_append, List.length_append]
      omega
    · intro z
      simp only [Word.toList_append, List.mem_append]
      constructor
      · rintro (inU | inSuffix)
        · exact Or.inl ((support z).mp inU)
        · exact Or.inr inSuffix
      · rintro (inV | inSuffix)
        · exact Or.inl ((support z).mpr inV)
        · exact Or.inr inSuffix

private theorem list_length_le_flatMap_words
    (letters : List Nat) (substitution : Nat → Word Nat) :
    letters.length ≤
      (letters.flatMap fun letter => (substitution letter).toList).length := by
  induction letters with
  | nil => simp
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

private theorem bind_head
    (w : Word Nat) (substitution : Nat → Word Nat) :
    (w.bind substitution).head = (substitution w.head).head := by
  unfold Word.bind
  generalize substitution w.head = initial
  induction w.tail generalizing initial with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      simpa using ih (initial ++ substitution x)

private theorem bind_preserves_support
    {u v : Word Nat} (substitution : Nat → Word Nat)
    (support : SameSupport u v) :
    SameSupport (u.bind substitution) (v.bind substitution) := by
  intro z
  rw [Word.toList_bind, Word.toList_bind]
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨x, inU, inImage⟩
    exact ⟨x, (support x).mp inU, inImage⟩
  · rintro ⟨x, inV, inImage⟩
    exact ⟨x, (support x).mpr inV, inImage⟩

private theorem exactBasisClass_subst
    (substitution : Nat → Word Nat)
    {u v : Word Nat} (sameClass : ExactBasisClass u v) :
    ExactBasisClass (u.bind substitution) (v.bind substitution) := by
  rcases sameClass with equal | ⟨uLong, vLong, heads, support⟩
  · exact Or.inl (congrArg (fun w => w.bind substitution) equal)
  · refine Or.inr
      ⟨bind_preserves_long u substitution uLong,
        bind_preserves_long v substitution vLong, ?_,
        bind_preserves_support substitution support⟩
    rw [bind_head, bind_head, heads]

private theorem basis_member_exact
    (e : Identity Nat) (member : e ∈ basis) :
    ExactBasisClass e.lhs e.rhs := by
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [ExactBasisClass, SameSupport, powerLaw, firstSwapLaw,
      transferLaw, heavyInsertionLaw, suffixCommutationLaw,
      longInsertionLaw, xxx, xxxx, xxy, xyx, xyy, xxxy, xyz, xzy,
      xxyz, Word.toList] <;>
    intro z <;> omega

private theorem derives_exact {u v : Word Nat}
    (derivation : Derives basis u v) :
    ExactBasisClass u v := by
  induction derivation with
  | fromBasis member =>
      exact basis_member_exact _ member
  | refl =>
      exact Or.inl rfl
  | symm _ ih =>
      exact exactBasisClass_symm ih
  | trans _ _ ihFirst ihSecond =>
      exact exactBasisClass_trans ihFirst ihSecond
  | prepend p _ ih =>
      exact exactBasisClass_prepend p ih
  | appendRight _ q ih =>
      exact exactBasisClass_appendRight q ih
  | subst _ substitution ih =>
      exact exactBasisClass_subst substitution ih

/-- Long words with the same first letter and support are derivably equal. -/
theorem derivesLongOfHeadSupportEq (u v : Word Nat)
    (uLong : 3 ≤ u.toList.length)
    (vLong : 3 ≤ v.toList.length)
    (heads : u.head = v.head)
    (support : SameSupport u v) :
    Derives basis u v := by
  have uExpansion :
      Derives basis u (u ++ v) :=
    derivesContentExpansion u v uLong
      (fun x hx => (support x).mpr hx)
  have vExpansion :
      Derives basis v (v ++ u) :=
    derivesContentExpansion v u vLong
      (fun x hx => (support x).mp hx)
  exact Derives.trans uExpansion <|
    Derives.trans (derivesConcatSwap u v heads)
      (Derives.symm vExpansion)

/-- Complete syntactic characterization of derivability from the published
six identities. -/
theorem derives_iff_exactBasisClass {u v : Word Nat} :
    Derives basis u v ↔ ExactBasisClass u v := by
  constructor
  · exact derives_exact
  · intro sameClass
    rcases sameClass with equal | ⟨uLong, vLong, heads, support⟩
    · subst v
      exact Derives.refl _
    · exact derivesLongOfHeadSupportEq u v
        uLong vLong heads support

private theorem lengthTwo_eq_of_head_and_support
    (u v : Word Nat)
    (heads : u.head = v.head)
    (support : SameSupport u v)
    (uTwo : u.toList.length = 2)
    (vTwo : v.toList.length = 2) :
    u = v := by
  cases u with
  | mk uHead uTail =>
      cases uTail with
      | nil =>
          simp [Word.toList] at uTwo
      | cons uNext uRest =>
          cases uRest with
          | nil =>
              cases v with
              | mk vHead vTail =>
                  cases vTail with
                  | nil =>
                      simp [Word.toList] at vTwo
                  | cons vNext vRest =>
                      cases vRest with
                      | nil =>
                          simp only at heads
                          subst vHead
                          have nextEqual : uNext = vNext := by
                            by_cases nextHead : uNext = uHead
                            · subst uNext
                              have member :=
                                (support vNext).mpr <| by
                                  simp [Word.toList]
                              have vNextHead : vNext = uHead := by
                                simpa [Word.toList] using member
                              exact vNextHead.symm
                            · have member :=
                                (support uNext).mp <| by
                                  simp [Word.toList]
                              simpa [Word.toList, nextHead] using member
                          subst vNext
                          rfl
                      | cons vThird vMore =>
                          simp [Word.toList] at vTwo
          | cons uThird uMore =>
              simp [Word.toList] at uTwo

/-- Generic completeness theorem for the `S5_520` basis. A finite table only
has to model the basis and recover first letter, support, and the length
stratum capped at three. -/
theorem basis_complete_of_separates
    (T : FiniteTable)
    (modelsT : Models T.semigroup basis)
    (headsT :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        e.lhs.head = e.rhs.head)
    (supportT :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        SameSupport e.lhs e.rhs)
    (cappedLengthT :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        min e.lhs.toList.length 3 =
          min e.rhs.toList.length 3) :
    BasisFor T.semigroup basis := by
  refine ⟨modelsT, ?_⟩
  intro e valid
  have heads := headsT e valid
  have support := supportT e valid
  have cappedLength := cappedLengthT e valid
  have lhsPositive : 0 < e.lhs.toList.length := by
    simp [Word.toList]
  have rhsPositive : 0 < e.rhs.toList.length := by
    simp [Word.toList]
  by_cases lhsOne : e.lhs.toList.length = 1
  · have rhsOne : e.rhs.toList.length = 1 := by
      omega
    have lhsTail : e.lhs.tail = [] := by
      cases tailShape : e.lhs.tail with
      | nil => rfl
      | cons x xs =>
          have atLeastTwo : 2 ≤ e.lhs.toList.length := by
            simp [Word.toList, tailShape]
          omega
    have rhsTail : e.rhs.tail = [] := by
      cases tailShape : e.rhs.tail with
      | nil => rfl
      | cons x xs =>
          have atLeastTwo : 2 ≤ e.rhs.toList.length := by
            simp [Word.toList, tailShape]
          omega
    have words : e.lhs = e.rhs := by
      apply Word.toList_injective
      simp [Word.toList, lhsTail, rhsTail, heads]
    rw [words]
    exact Derives.refl _
  · by_cases lhsTwo : e.lhs.toList.length = 2
    · have rhsTwo : e.rhs.toList.length = 2 := by
        omega
      have words :=
        lengthTwo_eq_of_head_and_support
          e.lhs e.rhs heads support lhsTwo rhsTwo
      rw [words]
      exact Derives.refl _
    · have lhsLong : 3 ≤ e.lhs.toList.length := by
        omega
      have rhsLong : 3 ≤ e.rhs.toList.length := by
        omega
      exact derivesLongOfHeadSupportEq e.lhs e.rhs
        lhsLong rhsLong heads support

end SemigroupBasis.CoRoots.S5_520
