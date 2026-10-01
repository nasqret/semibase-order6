import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_55

open SemigroupBasis

def xxy : Word Nat := ⟨0, [0, 1]⟩
def xyx : Word Nat := ⟨0, [1, 0]⟩
def xyy : Word Nat := ⟨0, [1, 1]⟩
def yxx : Word Nat := ⟨1, [0, 0]⟩
def xyz : Word Nat := ⟨0, [1, 2]⟩
def xzy : Word Nat := ⟨0, [2, 1]⟩
def yxz : Word Nat := ⟨1, [0, 2]⟩
def xyzt : Word Nat := ⟨0, [1, 2, 3]⟩
def xxxx : Word Nat := ⟨0, [0, 0, 0]⟩

def firstSwapLaw : Identity Nat := ⟨xxy, xyx⟩
def multiplicityTransferLaw : Identity Nat := ⟨xxy, xyy⟩
def prefixSwapLaw : Identity Nat := ⟨xxy, yxx⟩
def suffixCommutationLaw : Identity Nat := ⟨xyz, xzy⟩
def prefixCommutationLaw : Identity Nat := ⟨xyz, yxz⟩
def longCollapseLaw : Identity Nat := ⟨xyzt, xxxx⟩

/-- The exact six-law basis shared by `S5_55` and `S5_192`. -/
def basis : List (Identity Nat) :=
  [firstSwapLaw, multiplicityTransferLaw, prefixSwapLaw,
    suffixCommutationLaw, prefixCommutationLaw, longCollapseLaw]

def yyx : Word Nat := ⟨1, [1, 0]⟩
def zyx : Word Nat := ⟨2, [1, 0]⟩
def yzx : Word Nat := ⟨1, [2, 0]⟩
def zxy : Word Nat := ⟨2, [0, 1]⟩
def tzyx : Word Nat := ⟨3, [2, 1, 0]⟩

/-- The literal reverse-word transform of the six-law basis. -/
def expectedReversedBasis : List (Identity Nat) :=
  [⟨yxx, xyx⟩, ⟨yxx, yyx⟩, ⟨yxx, xxy⟩,
    ⟨zyx, yzx⟩, ⟨zyx, zxy⟩, ⟨tzyx, xxxx⟩]

theorem reversedBasis_eq_expected :
    reversedBasis basis = expectedReversedBasis := by
  rfl

def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private def instantiateThreeWords
    (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

private def instantiateFourWords
    (u v w t : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | 3 => t
  | n + 4 => Word.singleton (n + 4)

/-- Transfer the repeated variable in a product of three nonempty blocks. -/
theorem derivesMultiplicityTransfer (u v : Word Nat) :
    Derives basis ((u ++ u) ++ v) ((u ++ v) ++ v) := by
  have hbase :
      Derives basis xxy xyy :=
    Derives.fromBasis (e := multiplicityTransferLaw) <| by
      exact List.Mem.tail _ (List.Mem.head _)
  have h :=
    Derives.subst hbase (instantiateThreeWords u v v)
  simpa [basis, multiplicityTransferLaw, xxy, xyy,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

/-- Swap the last two nonempty blocks after a fixed nonempty prefix. -/
theorem derivesSuffixSwap (pre u v : Word Nat) :
    Derives basis
      ((pre ++ u) ++ v) ((pre ++ v) ++ u) := by
  have hbase :
      Derives basis xyz xzy :=
    Derives.fromBasis (e := suffixCommutationLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.head _
  have h :=
    Derives.subst hbase (instantiateThreeWords pre u v)
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

/-- Collapse four nonempty blocks to four copies of the first block. -/
theorem derivesLongCollapse (u v w t : Word Nat) :
    Derives basis
      (((u ++ v) ++ w) ++ t)
      (((u ++ u) ++ u) ++ u) := by
  have hbase :
      Derives basis xyzt xxxx :=
    Derives.fromBasis (e := longCollapseLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.head _
  have h :=
    Derives.subst hbase (instantiateFourWords u v w t)
  simpa [basis, longCollapseLaw, xyzt, xxxx,
    instantiateFourWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

private inductive ListDerives : List Nat → List Nat → Prop
  | empty : ListDerives [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives basis (wordOfCons x xs) (wordOfCons y ys) →
      ListDerives (x :: xs) (y :: ys)

private theorem ListDerives.trans {xs ys zs : List Nat}
    (first : ListDerives xs ys) (second : ListDerives ys zs) :
    ListDerives xs zs := by
  cases first with
  | empty =>
      cases second
      exact ListDerives.empty
  | words firstProof =>
      cases second with
      | words secondProof =>
          exact ListDerives.words
            (Derives.trans firstProof secondProof)

private theorem listDerives_of_perm_with_prefix
    (pre : List Nat) {xs ys : List Nat}
    (permutation : xs.Perm ys)
    (hlong : 3 ≤ (pre ++ xs).length) :
    ListDerives (pre ++ xs) (pre ++ ys) := by
  induction permutation generalizing pre with
  | nil =>
      cases pre with
      | nil => simp at hlong
      | cons p ps =>
          exact ListDerives.words (Derives.refl _)
  | cons x permutation ih =>
      have next :=
        ih (pre := pre ++ [x]) <| by
          simpa [List.append_assoc] using hlong
      simpa [List.append_assoc] using next
  | swap x y xs =>
      cases pre with
      | nil =>
          cases xs with
          | nil =>
              simp at hlong
          | cons z zs =>
              exact ListDerives.words <| by
                simpa [wordOfCons, Word.singleton, Word.append,
                  Word.append_assoc] using
                    derivesPrefixSwap
                      (Word.singleton y) (Word.singleton x)
                      (wordOfCons z zs)
      | cons p ps =>
          cases xs with
          | nil =>
              exact ListDerives.words <| by
                simpa [wordOfCons, Word.singleton, Word.append,
                  Word.append_assoc] using
                    derivesSuffixSwap
                      (wordOfCons p ps) (Word.singleton y)
                      (Word.singleton x)
          | cons z zs =>
              have swapped :=
                Derives.appendRight
                  (derivesSuffixSwap
                    (wordOfCons p ps) (Word.singleton y)
                    (Word.singleton x))
                  (wordOfCons z zs)
              exact ListDerives.words <| by
                simpa [wordOfCons, Word.singleton, Word.append,
                  Word.append_assoc] using swapped
  | trans first second ihFirst ihSecond =>
      have firstDerivation := ihFirst (pre := pre) hlong
      have secondDerivation :=
        ihSecond (pre := pre) <| by
          rw [List.length_append, ← first.length_eq]
          simpa [List.length_append] using hlong
      exact firstDerivation.trans secondDerivation

/-- Every permutation of a word of length at least three is derivable. -/
theorem derivesLongPermutation (u v : Word Nat)
    (hlong : 3 ≤ u.toList.length)
    (permutation : u.toList.Perm v.toList) :
    Derives basis u v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          have lifted :=
            listDerives_of_perm_with_prefix []
              (xs := uHead :: uTail) (ys := vHead :: vTail)
              permutation hlong
          cases lifted with
          | words derivation =>
              exact derivation

private theorem perm_xyx_xxy (x y : Nat) :
    [x, y, x].Perm [x, x, y] := by
  rw [List.perm_iff_count]
  intro z
  simp only [List.count_cons, List.count_nil]
  omega

private theorem perm_yxx_xxy (x y : Nat) :
    [y, x, x].Perm [x, x, y] := by
  rw [List.perm_iff_count]
  intro z
  simp only [List.count_cons, List.count_nil]
  omega

private theorem perm_yxy_xyy (x y : Nat) :
    [y, x, y].Perm [x, y, y] := by
  rw [List.perm_iff_count]
  intro z
  simp only [List.count_cons, List.count_nil]
  omega

private theorem perm_yyx_xyy (x y : Nat) :
    [y, y, x].Perm [x, y, y] := by
  rw [List.perm_iff_count]
  intro z
  simp only [List.count_cons, List.count_nil]
  omega

private theorem derivesXYYToXXY (x y : Nat) :
    Derives basis
      (wordOfCons x [y, y]) (wordOfCons x [x, y]) := by
  simpa [wordOfCons, Word.singleton, Word.append,
    Word.append_assoc] using
      Derives.symm
        (derivesMultiplicityTransfer
          (Word.singleton x) (Word.singleton y))

private theorem derivesTripleTwoSupport
    (x y a b c : Nat) (xy : x ≠ y)
    (support :
      ∀ z, z ∈ [a, b, c] ↔ z = x ∨ z = y) :
    Derives basis
      (wordOfCons a [b, c]) (wordOfCons x [x, y]) := by
  have xMember : x ∈ [a, b, c] :=
    (support x).mpr (Or.inl rfl)
  have yMember : y ∈ [a, b, c] :=
    (support y).mpr (Or.inr rfl)
  have ha : a = x ∨ a = y :=
    (support a).mp (by simp)
  have hb : b = x ∨ b = y :=
    (support b).mp (by simp)
  have hc : c = x ∨ c = y :=
    (support c).mp (by simp)
  rcases ha with hax | hay
  · subst a
    rcases hb with hbx | hby
    · subst b
      rcases hc with hcx | hcy
      · subst c
        have yx : y = x := by
          simpa using yMember
        exact False.elim (xy yx.symm)
      · subst c
        exact Derives.refl _
    · subst b
      rcases hc with hcx | hcy
      · subst c
        exact derivesLongPermutation _ _
          (by simp [wordOfCons, Word.toList]) <| by
          simpa [wordOfCons, Word.toList] using perm_xyx_xxy x y
      · subst c
        exact derivesXYYToXXY x y
  · subst a
    rcases hb with hbx | hby
    · subst b
      rcases hc with hcx | hcy
      · subst c
        exact derivesLongPermutation _ _
          (by simp [wordOfCons, Word.toList]) <| by
          simpa [wordOfCons, Word.toList] using perm_yxx_xxy x y
      · subst c
        exact Derives.trans
          (derivesLongPermutation _ _
            (by simp [wordOfCons, Word.toList]) <| by
            simpa [wordOfCons, Word.toList] using perm_yxy_xyy x y)
          (derivesXYYToXXY x y)
    · subst b
      rcases hc with hcx | hcy
      · subst c
        exact Derives.trans
          (derivesLongPermutation _ _
            (by simp [wordOfCons, Word.toList]) <| by
            simpa [wordOfCons, Word.toList] using perm_yyx_xyy x y)
          (derivesXYYToXXY x y)
      · subst c
        have xy' : x = y := by
          simpa using xMember
        exact False.elim (xy xy')

private theorem nodupPerm
    {xs ys : List Nat} (xsNodup : xs.Nodup) (ysNodup : ys.Nodup)
    (support : ∀ z, z ∈ xs ↔ z ∈ ys) :
    xs.Perm ys := by
  rw [List.perm_iff_count]
  intro z
  rw [xsNodup.count, ysNodup.count]
  simp only [support z]

private theorem tripleNodup_of_support
    {a b c d e f : Nat}
    (sourceNodup : [a, b, c].Nodup)
    (support :
      ∀ z, z ∈ [a, b, c] ↔ z ∈ [d, e, f]) :
    [d, e, f].Nodup := by
  have ha : a = d ∨ a = e ∨ a = f := by
    simpa using (support a).mp (by simp)
  have hb : b = d ∨ b = e ∨ b = f := by
    simpa using (support b).mp (by simp)
  have hc : c = d ∨ c = e ∨ c = f := by
    simpa using (support c).mp (by simp)
  rcases ha with ha | ha | ha <;>
    rcases hb with hb | hb | hb <;>
    rcases hc with hc | hc | hc <;>
    simp_all [eq_comm]

/-- Length-three words are classified exactly by variable support. -/
theorem derivesTripleOfSupportEq
    (a b c d e f : Nat)
    (support :
      ∀ z, z ∈ [a, b, c] ↔ z ∈ [d, e, f]) :
    Derives basis
      (wordOfCons a [b, c]) (wordOfCons d [e, f]) := by
  by_cases hab : a = b
  · subst b
    by_cases hac : a = c
    · subst c
      have hd : d = a := by
        have member := (support d).mpr (by simp)
        simpa using member
      have he : e = a := by
        have member := (support e).mpr (by simp)
        simpa using member
      have hf : f = a := by
        have member := (support f).mpr (by simp)
        simpa using member
      subst d
      subst e
      subst f
      exact Derives.refl _
    · have sourceSupport :
          ∀ z, z ∈ [a, a, c] ↔ z = a ∨ z = c := by
        intro z
        simp [or_assoc, or_left_comm, or_comm]
      have targetSupport :
          ∀ z, z ∈ [d, e, f] ↔ z = a ∨ z = c := by
        intro z
        exact (support z).symm.trans (sourceSupport z)
      have left :=
        derivesTripleTwoSupport a c a a c hac sourceSupport
      have right :=
        derivesTripleTwoSupport a c d e f hac targetSupport
      exact Derives.trans left (Derives.symm right)
  · by_cases hac : a = c
    · subst c
      have sourceSupport :
          ∀ z, z ∈ [a, b, a] ↔ z = a ∨ z = b := by
        intro z
        simp [or_assoc, or_left_comm, or_comm]
      have targetSupport :
          ∀ z, z ∈ [d, e, f] ↔ z = a ∨ z = b := by
        intro z
        exact (support z).symm.trans (sourceSupport z)
      have left :=
        derivesTripleTwoSupport a b a b a hab sourceSupport
      have right :=
        derivesTripleTwoSupport a b d e f hab targetSupport
      exact Derives.trans left (Derives.symm right)
    · by_cases hbc : b = c
      · subst c
        have sourceSupport :
            ∀ z, z ∈ [a, b, b] ↔ z = a ∨ z = b := by
          intro z
          simp [or_assoc, or_left_comm, or_comm]
        have targetSupport :
            ∀ z, z ∈ [d, e, f] ↔ z = a ∨ z = b := by
          intro z
          exact (support z).symm.trans (sourceSupport z)
        have left :=
          derivesTripleTwoSupport a b a b b hab sourceSupport
        have right :=
          derivesTripleTwoSupport a b d e f hab targetSupport
        exact Derives.trans left (Derives.symm right)
      · have sourceNodup : [a, b, c].Nodup := by
          simp [hab, hac, hbc, Ne.symm hab, Ne.symm hac,
            Ne.symm hbc]
        have targetNodup :=
          tripleNodup_of_support sourceNodup support
        exact derivesLongPermutation _ _
          (by simp [wordOfCons, Word.toList]) <| by
          simpa [wordOfCons, Word.toList] using
            nodupPerm sourceNodup targetNodup support

/-- Word-level length-three support completeness. -/
theorem derivesLengthThreeOfSupportEq
    (u v : Word Nat)
    (uThree : u.toList.length = 3)
    (vThree : v.toList.length = 3)
    (support :
      ∀ z, z ∈ u.toList ↔ z ∈ v.toList) :
    Derives basis u v := by
  cases u with
  | mk a uTail =>
      cases uTail with
      | nil =>
          simp [Word.toList] at uThree
      | cons b uRest =>
          cases uRest with
          | nil =>
              simp [Word.toList] at uThree
          | cons c uMore =>
              have uMoreNil : uMore = [] := by
                simp [Word.toList] at uThree
                omega
              subst uMore
              cases v with
              | mk d vTail =>
                  cases vTail with
                  | nil =>
                      simp [Word.toList] at vThree
                  | cons e vRest =>
                      cases vRest with
                      | nil =>
                          simp [Word.toList] at vThree
                      | cons f vMore =>
                          have vMoreNil : vMore = [] := by
                            simp [Word.toList] at vThree
                            omega
                          subst vMore
                          simpa [wordOfCons, Word.toList] using
                            derivesTripleOfSupportEq a b c d e f <| by
                              simpa [Word.toList] using support

private def longMarker : Word Nat :=
  wordOfCons 0 [0, 0, 0]

private theorem derivesFourthPowerToMarker (a : Nat) :
    Derives basis (wordOfCons a [a, a, a]) longMarker := by
  have expand :=
    Derives.symm <|
      derivesLongCollapse
        (Word.singleton a) (Word.singleton 0)
        (Word.singleton 0) (Word.singleton 0)
  have permute :
      Derives basis
        (wordOfCons a [0, 0, 0])
        (wordOfCons 0 [0, 0, a]) :=
    derivesLongPermutation _ _
      (by simp [wordOfCons, Word.toList]) <| by
      rw [List.perm_iff_count]
      intro z
      simp only [wordOfCons, Word.toList, List.count_cons,
        List.count_nil]
      omega
  have collapse :=
    derivesLongCollapse
      (Word.singleton 0) (Word.singleton 0)
      (Word.singleton 0) (Word.singleton a)
  exact Derives.trans
    (by
      simpa [wordOfCons, Word.singleton, Word.append,
        Word.append_assoc] using expand)
    (Derives.trans permute <| by
      simpa [longMarker, wordOfCons, Word.singleton, Word.append,
        Word.append_assoc] using collapse)

private theorem derivesLongToMarker (w : Word Nat)
    (hlong : 4 ≤ w.toList.length) :
    Derives basis w longMarker := by
  cases w with
  | mk a tail =>
      cases tail with
      | nil =>
          simp [Word.toList] at hlong
      | cons b rest =>
          cases rest with
          | nil =>
              simp [Word.toList] at hlong
          | cons c more =>
              cases more with
              | nil =>
                  simp [Word.toList] at hlong
              | cons d suffix =>
                  have collapse :=
                    derivesLongCollapse
                      (Word.singleton a) (Word.singleton b)
                      (Word.singleton c) (wordOfCons d suffix)
                  exact Derives.trans
                    (by
                      simpa [wordOfCons, Word.singleton, Word.append,
                        Word.append_assoc] using collapse)
                    (derivesFourthPowerToMarker a)

/-- Every two words of length at least four are derivably equal. -/
theorem derivesLongWords (u v : Word Nat)
    (uLong : 4 ≤ u.toList.length)
    (vLong : 4 ≤ v.toList.length) :
    Derives basis u v :=
  Derives.trans
    (derivesLongToMarker u uLong)
    (Derives.symm (derivesLongToMarker v vLong))

/-- Two words have the same variable support. -/
def SameSupport (u v : Word Nat) : Prop :=
  ∀ z, z ∈ u.toList ↔ z ∈ v.toList

/-- The exact congruence generated by the six laws.

Words of lengths one and two are literal, length-three words are classified
by support, and every word of length at least four lies in one class. -/
def ExactBasisClass (u v : Word Nat) : Prop :=
  u = v ∨
    ((u.toList.length = 3 ∧
        v.toList.length = 3 ∧ SameSupport u v) ∨
      (4 ≤ u.toList.length ∧ 4 ≤ v.toList.length))

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
  rcases sameClass with equal | tripleOrLong
  · exact Or.inl equal.symm
  · rcases tripleOrLong with
      ⟨uThree, vThree, support⟩ | ⟨uLong, vLong⟩
    · exact Or.inr <| Or.inl
        ⟨vThree, uThree, sameSupport_symm support⟩
    · exact Or.inr <| Or.inr ⟨vLong, uLong⟩

private theorem exactBasisClass_trans {u v w : Word Nat}
    (first : ExactBasisClass u v)
    (second : ExactBasisClass v w) :
    ExactBasisClass u w := by
  rcases first with equal | firstClass
  · subst v
    exact second
  · rcases second with equal | secondClass
    · subst w
      exact Or.inr firstClass
    · rcases firstClass with
        ⟨uThree, vThree, supportUV⟩ | ⟨uLong, vLong⟩
      · rcases secondClass with
          ⟨vThree', wThree, supportVW⟩ | ⟨vLong', wLong⟩
        · exact Or.inr <| Or.inl
            ⟨uThree, wThree,
              sameSupport_trans supportUV supportVW⟩
        · exact False.elim <| by omega
      · rcases secondClass with
          ⟨vThree, wThree, supportVW⟩ | ⟨vLong', wLong⟩
        · exact False.elim <| by omega
        · exact Or.inr <| Or.inr ⟨uLong, wLong⟩

private theorem exactBasisClass_prepend (p : Word Nat)
    {u v : Word Nat} (sameClass : ExactBasisClass u v) :
    ExactBasisClass (p ++ u) (p ++ v) := by
  rcases sameClass with equal | tripleOrLong
  · exact Or.inl (congrArg (fun w => p ++ w) equal)
  · rcases tripleOrLong with
      ⟨uThree, vThree, support⟩ | ⟨uLong, vLong⟩
    · exact Or.inr <| Or.inr <| by
        simp only [Word.toList_append, List.length_append]
        have pPositive : 1 ≤ p.toList.length := by
          cases p
          simp [Word.toList]
        omega
    · exact Or.inr <| Or.inr <| by
        simp only [Word.toList_append, List.length_append]
        omega

private theorem exactBasisClass_appendRight (q : Word Nat)
    {u v : Word Nat} (sameClass : ExactBasisClass u v) :
    ExactBasisClass (u ++ q) (v ++ q) := by
  rcases sameClass with equal | tripleOrLong
  · exact Or.inl (congrArg (fun w => w ++ q) equal)
  · rcases tripleOrLong with
      ⟨uThree, vThree, support⟩ | ⟨uLong, vLong⟩
    · exact Or.inr <| Or.inr <| by
        simp only [Word.toList_append, List.length_append]
        have qPositive : 1 ≤ q.toList.length := by
          cases q
          simp [Word.toList]
        omega
    · exact Or.inr <| Or.inr <| by
        simp only [Word.toList_append, List.length_append]
        omega

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

private theorem bind_preserves_length
    (w : Word Nat) (substitution : Nat → Word Nat)
    {bound : Nat} (long : bound ≤ w.toList.length) :
    bound ≤ (w.bind substitution).toList.length := by
  rw [Word.toList_bind]
  exact Nat.le_trans long
    (list_length_le_flatMap_words w.toList substitution)

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

private theorem bindTripleLength_transfer
    (a b c d e f : Nat) (substitution : Nat → Word Nat)
    (support :
      ∀ z, z ∈ [a, b, c] ↔ z ∈ [d, e, f])
    (sourceThree :
      ((wordOfCons a [b, c]).bind substitution).toList.length = 3) :
    ((wordOfCons d [e, f]).bind substitution).toList.length = 3 := by
  have imagePositive (z : Nat) :
      1 ≤ (substitution z).toList.length := by
    cases substitution z
    simp [Word.toList]
  have sourceSum :
      (substitution a).toList.length +
          (substitution b).toList.length +
          (substitution c).toList.length = 3 := by
    simpa [wordOfCons, Word.toList_bind, List.length_append,
      Nat.add_assoc] using sourceThree
  have aOne : (substitution a).toList.length = 1 := by
    have := imagePositive a
    have := imagePositive b
    have := imagePositive c
    omega
  have bOne : (substitution b).toList.length = 1 := by
    have := imagePositive a
    have := imagePositive b
    have := imagePositive c
    omega
  have cOne : (substitution c).toList.length = 1 := by
    have := imagePositive a
    have := imagePositive b
    have := imagePositive c
    omega
  have dMember : d = a ∨ d = b ∨ d = c := by
    simpa using (support d).mpr (by simp)
  have eMember : e = a ∨ e = b ∨ e = c := by
    simpa using (support e).mpr (by simp)
  have fMember : f = a ∨ f = b ∨ f = c := by
    simpa using (support f).mpr (by simp)
  have dOne : (substitution d).toList.length = 1 := by
    rcases dMember with rfl | rfl | rfl
    · exact aOne
    · exact bOne
    · exact cOne
  have eOne : (substitution e).toList.length = 1 := by
    rcases eMember with rfl | rfl | rfl
    · exact aOne
    · exact bOne
    · exact cOne
  have fOne : (substitution f).toList.length = 1 := by
    rcases fMember with rfl | rfl | rfl
    · exact aOne
    · exact bOne
    · exact cOne
  have dTail : (substitution d).tail = [] := by
    have lengthOneIff :
        (substitution d).toList.length = 1 ↔
          (substitution d).tail = [] := by
      simp [Word.toList]
    exact lengthOneIff.mp dOne
  have eTail : (substitution e).tail = [] := by
    have lengthOneIff :
        (substitution e).toList.length = 1 ↔
          (substitution e).tail = [] := by
      simp [Word.toList]
    exact lengthOneIff.mp eOne
  have fTail : (substitution f).tail = [] := by
    have lengthOneIff :
        (substitution f).toList.length = 1 ↔
          (substitution f).tail = [] := by
      simp [Word.toList]
    exact lengthOneIff.mp fOne
  rw [Word.toList_bind]
  simp [wordOfCons, Word.toList, dTail, eTail, fTail]

private theorem bind_length_three_iff_of_support
    (u v : Word Nat) (substitution : Nat → Word Nat)
    (uThree : u.toList.length = 3)
    (vThree : v.toList.length = 3)
    (support : SameSupport u v) :
    (u.bind substitution).toList.length = 3 ↔
      (v.bind substitution).toList.length = 3 := by
  cases u with
  | mk a uTail =>
      cases uTail with
      | nil =>
          simp [Word.toList] at uThree
      | cons b uRest =>
          cases uRest with
          | nil =>
              simp [Word.toList] at uThree
          | cons c uMore =>
              have uMoreNil : uMore = [] := by
                simp [Word.toList] at uThree
                omega
              subst uMore
              cases v with
              | mk d vTail =>
                  cases vTail with
                  | nil =>
                      simp [Word.toList] at vThree
                  | cons e vRest =>
                      cases vRest with
                      | nil =>
                          simp [Word.toList] at vThree
                      | cons f vMore =>
                          have vMoreNil : vMore = [] := by
                            simp [Word.toList] at vThree
                            omega
                          subst vMore
                          have listSupport :
                              ∀ z, z ∈ [a, b, c] ↔
                                z ∈ [d, e, f] := by
                            simpa [SameSupport, Word.toList] using support
                          constructor
                          · intro sourceThree
                            exact bindTripleLength_transfer
                              a b c d e f substitution listSupport <| by
                                simpa [wordOfCons] using sourceThree
                          · intro targetThree
                            exact bindTripleLength_transfer
                              d e f a b c substitution
                              (fun z => (listSupport z).symm) <| by
                                simpa [wordOfCons] using targetThree

private theorem exactBasisClass_subst
    (substitution : Nat → Word Nat)
    {u v : Word Nat} (sameClass : ExactBasisClass u v) :
    ExactBasisClass (u.bind substitution) (v.bind substitution) := by
  rcases sameClass with equal | tripleOrLong
  · exact Or.inl (congrArg (fun w => w.bind substitution) equal)
  · rcases tripleOrLong with
      ⟨uThree, vThree, support⟩ | ⟨uLong, vLong⟩
    · have boundU :
          3 ≤ (u.bind substitution).toList.length :=
        bind_preserves_length u substitution (by omega)
      have boundV :
          3 ≤ (v.bind substitution).toList.length :=
        bind_preserves_length v substitution (by omega)
      have lengthThreeIff :=
        bind_length_three_iff_of_support
          u v substitution uThree vThree support
      by_cases uStillThree :
          (u.bind substitution).toList.length = 3
      · have vStillThree := lengthThreeIff.mp uStillThree
        exact Or.inr <| Or.inl
          ⟨uStillThree, vStillThree,
            bind_preserves_support substitution support⟩
      · have uNowLong :
            4 ≤ (u.bind substitution).toList.length := by
          omega
        have vNotThree :
            (v.bind substitution).toList.length ≠ 3 := by
          intro vThree'
          exact uStillThree (lengthThreeIff.mpr vThree')
        have vNowLong :
            4 ≤ (v.bind substitution).toList.length := by
          omega
        exact Or.inr <| Or.inr ⟨uNowLong, vNowLong⟩
    · exact Or.inr <| Or.inr
        ⟨bind_preserves_length u substitution uLong,
          bind_preserves_length v substitution vLong⟩

private theorem basis_member_exact
    (e : Identity Nat) (member : e ∈ basis) :
    ExactBasisClass e.lhs e.rhs := by
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr <| Or.inl
      ⟨by simp [firstSwapLaw, xxy, Word.toList],
        by simp [firstSwapLaw, xyx, Word.toList],
        by
          intro z
          simp [SameSupport, firstSwapLaw, xxy, xyx, Word.toList,
            or_assoc, or_left_comm, or_comm]⟩
  · exact Or.inr <| Or.inl
      ⟨by simp [multiplicityTransferLaw, xxy, Word.toList],
        by simp [multiplicityTransferLaw, xyy, Word.toList],
        by
          intro z
          simp [SameSupport, multiplicityTransferLaw, xxy, xyy,
            Word.toList, or_assoc, or_left_comm, or_comm]⟩
  · exact Or.inr <| Or.inl
      ⟨by simp [prefixSwapLaw, xxy, Word.toList],
        by simp [prefixSwapLaw, yxx, Word.toList],
        by
          intro z
          simp [SameSupport, prefixSwapLaw, xxy, yxx, Word.toList,
            or_assoc, or_left_comm, or_comm]⟩
  · exact Or.inr <| Or.inl
      ⟨by simp [suffixCommutationLaw, xyz, Word.toList],
        by simp [suffixCommutationLaw, xzy, Word.toList],
        by
          intro z
          simp [SameSupport, suffixCommutationLaw, xyz, xzy,
            Word.toList, or_assoc, or_left_comm, or_comm]⟩
  · exact Or.inr <| Or.inl
      ⟨by simp [prefixCommutationLaw, xyz, Word.toList],
        by simp [prefixCommutationLaw, yxz, Word.toList],
        by
          intro z
          simp [SameSupport, prefixCommutationLaw, xyz, yxz,
            Word.toList, or_assoc, or_left_comm, or_comm]⟩
  · exact Or.inr <| Or.inr
      ⟨by simp [longCollapseLaw, xyzt, Word.toList],
        by simp [longCollapseLaw, xxxx, Word.toList]⟩

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
  | trans _ _ ih₁ ih₂ =>
      exact exactBasisClass_trans ih₁ ih₂
  | prepend p _ ih =>
      exact exactBasisClass_prepend p ih
  | appendRight _ q ih =>
      exact exactBasisClass_appendRight q ih
  | subst _ substitution ih =>
      exact exactBasisClass_subst substitution ih

/-- Complete syntactic characterization of derivability from the six laws. -/
theorem derives_iff_exactBasisClass {u v : Word Nat} :
    Derives basis u v ↔ ExactBasisClass u v := by
  constructor
  · exact derives_exact
  · intro sameClass
    rcases sameClass with equal | tripleOrLong
    · subst v
      exact Derives.refl _
    · rcases tripleOrLong with
        ⟨uThree, vThree, support⟩ | ⟨uLong, vLong⟩
      · exact derivesLengthThreeOfSupportEq
          u v uThree vThree support
      · exact derivesLongWords u v uLong vLong

/-- Assemble the exact congruence class of a semantically valid identity from
the four finite-table separation obligations. -/
theorem exactBasisClass_of_separates
    (e : Identity Nat)
    (cappedLength :
      min e.lhs.toList.length 4 =
        min e.rhs.toList.length 4)
    (singletonEq :
      e.lhs.toList.length = 1 →
        e.rhs.toList.length = 1 → e.lhs = e.rhs)
    (pairEq :
      e.lhs.toList.length = 2 →
        e.rhs.toList.length = 2 → e.lhs = e.rhs)
    (tripleSupport :
      e.lhs.toList.length = 3 →
        e.rhs.toList.length = 3 →
        SameSupport e.lhs e.rhs) :
    ExactBasisClass e.lhs e.rhs := by
  have lhsPositive : 0 < e.lhs.toList.length := by
    cases e.lhs
    simp [Word.toList]
  have rhsPositive : 0 < e.rhs.toList.length := by
    cases e.rhs
    simp [Word.toList]
  by_cases lhsOne : e.lhs.toList.length = 1
  · have rhsOne : e.rhs.toList.length = 1 := by
      omega
    exact Or.inl (singletonEq lhsOne rhsOne)
  · by_cases lhsTwo : e.lhs.toList.length = 2
    · have rhsTwo : e.rhs.toList.length = 2 := by
        omega
      exact Or.inl (pairEq lhsTwo rhsTwo)
    · by_cases lhsThree : e.lhs.toList.length = 3
      · have rhsThree : e.rhs.toList.length = 3 := by
          omega
        exact Or.inr <| Or.inl
          ⟨lhsThree, rhsThree,
            tripleSupport lhsThree rhsThree⟩
      · have lhsLong : 4 ≤ e.lhs.toList.length := by
          omega
        have rhsLong : 4 ≤ e.rhs.toList.length := by
          omega
        exact Or.inr <| Or.inr ⟨lhsLong, rhsLong⟩

/-- Equal support makes singleton words literal. -/
theorem lengthOne_eq_of_support
    (u v : Word Nat)
    (uOne : u.toList.length = 1)
    (vOne : v.toList.length = 1)
    (support : SameSupport u v) :
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

/-- A valid quadratic identity with equal support is literal once the model
contains one ordered pair whose two products differ. -/
theorem validPair_eq_of_support_and_order
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

theorem validLengthTwo_eq_of_support_and_order
    (T : FiniteTable) (left right : Fin T.order)
    (orderNe : T.mul left right ≠ T.mul right left)
    (e : Identity Nat) (valid : e.SatisfiedBy T.semigroup)
    (support : SameSupport e.lhs e.rhs)
    (lhsTwo : e.lhs.toList.length = 2)
    (rhsTwo : e.rhs.toList.length = 2) :
    e.lhs = e.rhs := by
  cases e with
  | mk lhs rhs =>
      cases lhs with
      | mk lx ltail =>
          cases ltail with
          | nil =>
              simp [Word.toList] at lhsTwo
          | cons ly lrest =>
              cases lrest with
              | nil =>
                  cases rhs with
                  | mk rx rtail =>
                      cases rtail with
                      | nil =>
                          simp [Word.toList] at rhsTwo
                      | cons ry rrest =>
                          cases rrest with
                          | nil =>
                              have coordinates :=
                                validPair_eq_of_support_and_order
                                  T left right orderNe valid <| by
                                    simpa [SameSupport, wordOfCons,
                                      Word.toList] using support
                              rcases coordinates with ⟨rfl, rfl⟩
                              rfl
                          | cons rz rzs =>
                              simp [Word.toList] at rhsTwo
              | cons lz lzs =>
                  simp [Word.toList] at lhsTwo

/-- Any exact semantic separator for the normal-form classes yields an
unrestricted basis theorem. -/
theorem basis_complete_of_exact
    (T : FiniteTable)
    (modelsT : Models T.semigroup basis)
    (exactT :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        ExactBasisClass e.lhs e.rhs) :
    BasisFor T.semigroup basis := by
  refine ⟨modelsT, ?_⟩
  intro e valid
  exact derives_iff_exactBasisClass.mpr (exactT e valid)

end SemigroupBasis.CoRoots.S5_55
