import SemigroupBasis.CoRoots.Order6LongSupportThresholdPrelude

namespace SemigroupBasis
namespace CoRoots
namespace Order6LongSupportThreshold

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
    Derives longSupportThresholdBasis ((u ++ u) ++ v) ((u ++ v) ++ v) := by
  have hbase :
      Derives longSupportThresholdBasis S5_55.xxy S5_55.xyy :=
    Derives.fromBasis (e := S5_55.multiplicityTransferLaw) <| by
      exact List.Mem.tail _ (List.Mem.head _)
  have h :=
    Derives.subst hbase (instantiateThreeWords u v v)
  simpa [longSupportThresholdBasis, S5_55.multiplicityTransferLaw, S5_55.xxy, S5_55.xyy,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

/-- Swap the last two nonempty blocks after a fixed nonempty prefix. -/
theorem derivesSuffixSwap (pre u v : Word Nat) :
    Derives longSupportThresholdBasis
      ((pre ++ u) ++ v) ((pre ++ v) ++ u) := by
  have hbase :
      Derives longSupportThresholdBasis S5_55.xyz S5_55.xzy :=
    Derives.fromBasis (e := S5_55.suffixCommutationLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.head _
  have h :=
    Derives.subst hbase (instantiateThreeWords pre u v)
  simpa [longSupportThresholdBasis, S5_55.suffixCommutationLaw, S5_55.xyz, S5_55.xzy,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

/-- Swap the first two nonempty blocks before a fixed nonempty suffix. -/
theorem derivesPrefixSwap (u v suffix : Word Nat) :
    Derives longSupportThresholdBasis
      ((u ++ v) ++ suffix) ((v ++ u) ++ suffix) := by
  have hbase :
      Derives longSupportThresholdBasis S5_55.xyz S5_55.yxz :=
    Derives.fromBasis (e := S5_55.prefixCommutationLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _
  have h :=
    Derives.subst hbase (instantiateThreeWords u v suffix)
  simpa [longSupportThresholdBasis, S5_55.prefixCommutationLaw, S5_55.xyz, S5_55.yxz,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

private inductive ListDerives : List Nat → List Nat → Prop
  | empty : ListDerives [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives longSupportThresholdBasis (wordOfCons x xs) (wordOfCons y ys) →
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
    Derives longSupportThresholdBasis u v := by
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

private theorem perm_xyx_S5_55.xxy (x y : Nat) :
    [x, y, x].Perm [x, x, y] := by
  rw [List.perm_iff_count]
  intro z
  simp only [List.count_cons, List.count_nil]
  omega

private theorem perm_yxx_S5_55.xxy (x y : Nat) :
    [y, x, x].Perm [x, x, y] := by
  rw [List.perm_iff_count]
  intro z
  simp only [List.count_cons, List.count_nil]
  omega

private theorem perm_yxy_S5_55.xyy (x y : Nat) :
    [y, x, y].Perm [x, y, y] := by
  rw [List.perm_iff_count]
  intro z
  simp only [List.count_cons, List.count_nil]
  omega

private theorem perm_yyx_S5_55.xyy (x y : Nat) :
    [y, y, x].Perm [x, y, y] := by
  rw [List.perm_iff_count]
  intro z
  simp only [List.count_cons, List.count_nil]
  omega

private theorem derivesXYYToXXY (x y : Nat) :
    Derives longSupportThresholdBasis
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
    Derives longSupportThresholdBasis
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
          simpa [wordOfCons, Word.toList] using perm_xyx_S5_55.xxy x y
      · subst c
        exact derivesXYYToXXY x y
  · subst a
    rcases hb with hbx | hby
    · subst b
      rcases hc with hcx | hcy
      · subst c
        exact derivesLongPermutation _ _
          (by simp [wordOfCons, Word.toList]) <| by
          simpa [wordOfCons, Word.toList] using perm_yxx_S5_55.xxy x y
      · subst c
        exact Derives.trans
          (derivesLongPermutation _ _
            (by simp [wordOfCons, Word.toList]) <| by
            simpa [wordOfCons, Word.toList] using perm_yxy_S5_55.xyy x y)
          (derivesXYYToXXY x y)
    · subst b
      rcases hc with hcx | hcy
      · subst c
        exact Derives.trans
          (derivesLongPermutation _ _
            (by simp [wordOfCons, Word.toList]) <| by
            simpa [wordOfCons, Word.toList] using perm_yyx_S5_55.xyy x y)
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
    Derives longSupportThresholdBasis
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
        simp [or_comm]
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
        simp [or_comm]
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
          simp [or_comm]
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
          simp [hab, hac, hbc]
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
    Derives longSupportThresholdBasis u v := by
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


private def instantiateLongWords
    (u v w q : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | 3 => q
  | n + 4 => Word.singleton (n + 4)

/-- Insert another copy of the first block after four nonempty blocks. -/
theorem derivesLongInsertion (u v w q : Word Nat) :
    Derives longSupportThresholdBasis
      (((u ++ v) ++ w) ++ q)
      ((((u ++ v) ++ w) ++ q) ++ u) := by
  have base : Derives longSupportThresholdBasis S5_55.xyzt xyztx :=
    Derives.fromBasis (e := longSupportLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <|
          List.Mem.tail _ <| List.Mem.head _
  have substituted := Derives.subst base (instantiateLongWords u v w q)
  simpa [longSupportThresholdBasis, longSupportLaw, S5_55.xyzt, xyztx,
    instantiateLongWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- A supported letter may be appended to any word of length at least four. -/
theorem derivesAppendMember
    (w : Word Nat) (x : Nat)
    (hlong : 4 ≤ w.toList.length)
    (hx : x ∈ w.toList) :
    Derives longSupportThresholdBasis w (w ++ Word.singleton x) := by
  let remaining := w.toList.erase x
  have sourcePerm : w.toList.Perm (x :: remaining) := by
    simpa [remaining] using List.perm_cons_erase hx
  have remainingLong : 3 ≤ remaining.length := by
    have lengths := sourcePerm.length_eq
    simp only [List.length_cons] at lengths
    omega
  cases hremaining : remaining with
  | nil => simp [hremaining] at remainingLong
  | cons a rest =>
    cases hrest : rest with
    | nil => simp [hremaining, hrest] at remainingLong
    | cons b more =>
      cases hmore : more with
      | nil => simp [hremaining, hrest, hmore] at remainingLong
      | cons c cs =>
        have remainingEq : remaining = a :: b :: c :: cs := by
          rw [hremaining, hrest, hmore]
        rw [remainingEq] at sourcePerm
        have arrange :
            Derives longSupportThresholdBasis w
              (wordOfCons x (a :: b :: c :: cs)) :=
          derivesLongPermutation _ _ (by omega) <| by
            simpa [wordOfCons, Word.toList] using sourcePerm
        have duplicate :
            Derives longSupportThresholdBasis
              (wordOfCons x (a :: b :: c :: cs))
              ((wordOfCons x (a :: b :: c :: cs)) ++ Word.singleton x) := by
          simpa [wordOfCons, Word.singleton, Word.append,
            Word.append_assoc] using
              derivesLongInsertion (Word.singleton x) (Word.singleton a)
                (Word.singleton b) (wordOfCons c cs)
        have finishPerm :
            ((wordOfCons x (a :: b :: c :: cs)) ++ Word.singleton x).toList.Perm
              (w ++ Word.singleton x).toList := by
          have appended := sourcePerm.symm.append_right [x]
          simpa [wordOfCons, Word.toList, Word.toList_append,
            Word.toList_singleton] using appended
        exact arrange.trans <| duplicate.trans <|
          derivesLongPermutation _ _ (by simp [wordOfCons, Word.toList]) finishPerm

/-- Append a list of letters already supported by a long word. -/
theorem derivesAppendList
    (w : Word Nat) (xs : List Nat)
    (hlong : 4 ≤ w.toList.length)
    (hcontent : ∀ x, x ∈ xs → x ∈ w.toList) :
    Derives longSupportThresholdBasis w ⟨w.head, w.tail ++ xs⟩ := by
  induction xs generalizing w with
  | nil => simpa using Derives.refl w
  | cons x xs ih =>
    have hx := hcontent x (List.Mem.head xs)
    have firstStep := derivesAppendMember w x hlong hx
    have currentLong : 4 ≤ (w ++ Word.singleton x).toList.length := by
      rw [Word.toList_append]
      simp
      omega
    have remainingContent : ∀ y, y ∈ xs → y ∈ (w ++ Word.singleton x).toList := by
      intro y hy
      rw [Word.toList_append]
      exact List.mem_append_left _ (hcontent y (List.Mem.tail x hy))
    have restStep := ih (w ++ Word.singleton x) currentLong remainingContent
    exact firstStep.trans <| by
      simpa [Word.append, Word.singleton, List.append_assoc] using restStep

/-- Long words with equal support are derivably equal. -/
theorem derivesLongOfSupport
    (u v : Word Nat)
    (uLong : 4 ≤ u.toList.length)
    (vLong : 4 ≤ v.toList.length)
    (support : S5_55.SameSupport u v) :
    Derives longSupportThresholdBasis u v := by
  have uv := derivesAppendList u v.toList uLong (fun x hx => (support x).mpr hx)
  have vu := derivesAppendList v u.toList vLong (fun x hx => (support x).mp hx)
  have uvForm : ⟨u.head, u.tail ++ v.toList⟩ = u ++ v := by
    apply Word.toList_injective
    simp [Word.toList]
  have vuForm : ⟨v.head, v.tail ++ u.toList⟩ = v ++ u := by
    apply Word.toList_injective
    simp [Word.toList]
  rw [uvForm] at uv
  rw [vuForm] at vu
  have perm : (u ++ v).toList.Perm (v ++ u).toList := by
    simp only [Word.toList_append]
    exact List.perm_append_comm
  exact uv.trans <| (derivesLongPermutation _ _ (by
    rw [Word.toList_append, List.length_append]
    omega) perm).trans vu.symm


theorem derivesOfThresholdClassAndSupport
    (e : Identity Nat)
    (threshold : S5_55.ExactBasisClass e.lhs e.rhs)
    (support : S5_55.SameSupport e.lhs e.rhs) :
    Derives longSupportThresholdBasis e.lhs e.rhs := by
  rcases threshold with equal | tripleOrLong
  · rw [equal]
    exact Derives.refl _
  · rcases tripleOrLong with triple | long
    · rcases triple with ⟨lhsThree, rhsThree, tripleSupport⟩
      exact derivesLengthThreeOfSupportEq
        e.lhs e.rhs lhsThree rhsThree tripleSupport
    · exact derivesLongOfSupport e.lhs e.rhs long.1 long.2 support

end Order6LongSupportThreshold
end CoRoots
end SemigroupBasis
