import SemigroupBasis.Examples.CommutativePeriodTwoFromTwo

namespace SemigroupBasis.Examples

open SemigroupBasis

def headSortedPeriodTwoXX : Word Nat := ⟨0, [0]⟩
def headSortedPeriodTwoXXXX : Word Nat := ⟨0, [0, 0, 0]⟩
def headSortedPeriodTwoXXY : Word Nat := ⟨0, [0, 1]⟩
def headSortedPeriodTwoXYX : Word Nat := ⟨0, [1, 0]⟩
def headSortedPeriodTwoXYZ : Word Nat := ⟨0, [1, 2]⟩
def headSortedPeriodTwoXZY : Word Nat := ⟨0, [2, 1]⟩

def headSortedPeriodTwoPowerLaw : Identity Nat :=
  ⟨headSortedPeriodTwoXX, headSortedPeriodTwoXXXX⟩

def headSortedPeriodTwoGatherLaw : Identity Nat :=
  ⟨headSortedPeriodTwoXXY, headSortedPeriodTwoXYX⟩

def headSortedPeriodTwoSuffixSwapLaw : Identity Nat :=
  ⟨headSortedPeriodTwoXYZ, headSortedPeriodTwoXZY⟩

/-- The fixed-head, commutative-suffix basis
`xx = xxxx`, `xxy = xyx`, `xyz = xzy`. -/
def headSortedPeriodTwoFromTwoBasis : List (Identity Nat) :=
  [headSortedPeriodTwoPowerLaw, headSortedPeriodTwoGatherLaw,
    headSortedPeriodTwoSuffixSwapLaw]

private def instantiateThreeWords
    (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

/-- Contract four consecutive copies of a nonempty block to two copies. -/
theorem headSortedPeriodTwoDerivesFourToTwo (u : Word Nat) :
    Derives headSortedPeriodTwoFromTwoBasis
      (((u ++ u) ++ u) ++ u) (u ++ u) := by
  have hbase :
      Derives headSortedPeriodTwoFromTwoBasis
        headSortedPeriodTwoXXXX headSortedPeriodTwoXX :=
    Derives.symm <|
      Derives.fromBasis (e := headSortedPeriodTwoPowerLaw) <|
        List.Mem.head _
  have h := Derives.subst hbase (instantiateThreeWords u u u)
  simpa [headSortedPeriodTwoFromTwoBasis,
    headSortedPeriodTwoPowerLaw, headSortedPeriodTwoXXXX,
    headSortedPeriodTwoXX, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using h

/-- Gather a later copy of a block next to its first copy. -/
theorem headSortedPeriodTwoDerivesGather (u v : Word Nat) :
    Derives headSortedPeriodTwoFromTwoBasis
      ((u ++ v) ++ u) ((u ++ u) ++ v) := by
  have hbase :
      Derives headSortedPeriodTwoFromTwoBasis
        headSortedPeriodTwoXYX headSortedPeriodTwoXXY :=
    Derives.symm <|
      Derives.fromBasis (e := headSortedPeriodTwoGatherLaw) <|
        List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateThreeWords u v u)
  simpa [headSortedPeriodTwoFromTwoBasis,
    headSortedPeriodTwoGatherLaw, headSortedPeriodTwoXYX,
    headSortedPeriodTwoXXY, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using h

/-- Swap arbitrary nonempty blocks behind a fixed nonempty prefix. -/
theorem headSortedPeriodTwoDerivesSuffixSwap
    (p u v : Word Nat) :
    Derives headSortedPeriodTwoFromTwoBasis
      ((p ++ u) ++ v) ((p ++ v) ++ u) := by
  have hbase :
      Derives headSortedPeriodTwoFromTwoBasis
        headSortedPeriodTwoXYZ headSortedPeriodTwoXZY :=
    Derives.fromBasis (e := headSortedPeriodTwoSuffixSwapLaw) <|
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  have h := Derives.subst hbase (instantiateThreeWords p u v)
  simpa [headSortedPeriodTwoFromTwoBasis,
    headSortedPeriodTwoSuffixSwapLaw, headSortedPeriodTwoXYZ,
    headSortedPeriodTwoXZY, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using h

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private def appendList (p : Word Nat) (xs : List Nat) : Word Nat :=
  ⟨p.head, p.tail ++ xs⟩

private theorem appendList_cons
    (p : Word Nat) (x : Nat) (xs : List Nat) :
    appendList p (x :: xs) = p ++ wordOfCons x xs := by
  apply Word.toList_injective
  simp [appendList, wordOfCons, Word.toList]

private theorem appendList_cons_prefix
    (p : Word Nat) (x : Nat) (xs : List Nat) :
    appendList p (x :: xs) =
      appendList (p ++ Word.singleton x) xs := by
  apply Word.toList_injective
  simp [appendList, Word.toList, List.append_assoc]

/-- Every permutation strictly behind a fixed nonempty prefix is derivable. -/
theorem headSortedPeriodTwoDerivesTailPermutation
    (p : Word Nat) {xs ys : List Nat} (h : xs.Perm ys) :
    Derives headSortedPeriodTwoFromTwoBasis
      (appendList p xs) (appendList p ys) := by
  induction h generalizing p with
  | nil =>
      exact Derives.refl _
  | cons x _ ih =>
      have h := ih (p ++ Word.singleton x)
      rw [appendList_cons_prefix, appendList_cons_prefix]
      exact h
  | swap x y xs =>
      cases xs with
      | nil =>
          rw [appendList_cons, appendList_cons]
          simpa [wordOfCons, Word.append, Word.singleton,
            Word.append_assoc] using
              headSortedPeriodTwoDerivesSuffixSwap p
                (Word.singleton y) (Word.singleton x)
      | cons z zs =>
          have h :=
            Derives.appendRight
              (headSortedPeriodTwoDerivesSuffixSwap p
                (Word.singleton y) (Word.singleton x))
              (wordOfCons z zs)
          rw [appendList_cons, appendList_cons]
          simpa [wordOfCons, Word.append_assoc] using h
  | trans _ _ ih₁ ih₂ =>
      exact Derives.trans (ih₁ p) (ih₂ p)

private theorem exponent_le_three (n : Nat) :
    periodTwoFromTwoExponent n ≤ 3 := by
  unfold periodTwoFromTwoExponent
  split <;> omega

private theorem count_replicate_of_ne
    {x z : Nat} (hzx : z ≠ x) :
    ∀ n : Nat, (List.replicate n x).count z = 0
  | 0 => rfl
  | n + 1 => by
      rw [List.replicate_succ,
        List.count_cons_of_ne (Ne.symm hzx),
        count_replicate_of_ne hzx n]

private theorem count_filter_ne_self (x : Nat) (xs : List Nat) :
    (xs.filter (fun z => decide (z ≠ x))).count x = 0 := by
  apply List.count_eq_zero.mpr
  simp

private theorem count_filter_ne_of_ne
    {x z : Nat} (hzx : z ≠ x) (xs : List Nat) :
    (xs.filter (fun a => decide (a ≠ x))).count z = xs.count z := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
      by_cases hax : a = x
      · subst a
        rw [List.filter_cons_of_neg (by simp),
          List.count_cons_of_ne (Ne.symm hzx)]
        exact ih
      · rw [List.filter_cons_of_pos (by simpa)]
        simp only [List.count_cons]
        rw [ih]

/-- First-occurrence blocks with multiplicities normalized to zero, one,
positive-even, or odd-at-least-three. -/
def headSortedPeriodTwoNormalList : List Nat → List Nat
  | [] => []
  | x :: xs =>
      let rest := headSortedPeriodTwoNormalList xs
      List.replicate
          (periodTwoFromTwoExponent ((x :: xs).count x)) x ++
        rest.filter (fun y => decide (y ≠ x))

theorem headSortedPeriodTwoNormalList_count
    (z : Nat) :
    ∀ xs : List Nat,
      (headSortedPeriodTwoNormalList xs).count z =
        periodTwoFromTwoExponent (xs.count z)
  | [] => by
      simp [headSortedPeriodTwoNormalList,
        periodTwoFromTwoExponent]
  | x :: xs => by
      simp only [headSortedPeriodTwoNormalList, List.count_append]
      by_cases hzx : z = x
      · subst z
        rw [List.count_replicate_self, count_filter_ne_self]
        omega
      · rw [count_replicate_of_ne hzx,
          count_filter_ne_of_ne hzx, Nat.zero_add,
          headSortedPeriodTwoNormalList_count]
        rw [List.count_cons_of_ne (Ne.symm hzx)]

private theorem normalList_cons_ne_nil (x : Nat) (xs : List Nat) :
    headSortedPeriodTwoNormalList (x :: xs) ≠ [] := by
  intro h
  have countEq :=
    headSortedPeriodTwoNormalList_count x (x :: xs)
  rw [h, List.count_nil, List.count_cons_self] at countEq
  exact (Nat.ne_of_gt <|
    periodTwoFromTwoExponent_pos (by omega)) countEq.symm

private theorem perm_extract (x : Nat) (xs : List Nat) :
    xs.Perm
      (List.replicate (xs.count x) x ++
        xs.filter (fun y => decide (y ≠ x))) := by
  rw [List.perm_iff_count]
  intro z
  by_cases hzx : z = x
  · subst z
    rw [List.count_append, List.count_replicate_self,
      count_filter_ne_self]
    omega
  · rw [List.count_append, count_replicate_of_ne hzx,
      count_filter_ne_of_ne hzx]
    omega

private theorem contractLeadingFour (x : Nat) (suffix : List Nat) :
    Derives headSortedPeriodTwoFromTwoBasis
      (wordOfCons x (x :: x :: x :: suffix))
      (wordOfCons x (x :: suffix)) := by
  cases suffix with
  | nil =>
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using
          headSortedPeriodTwoDerivesFourToTwo (Word.singleton x)
  | cons y ys =>
      have h :=
        Derives.appendRight
          (headSortedPeriodTwoDerivesFourToTwo (Word.singleton x))
          (wordOfCons y ys)
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using h

private theorem derivesNormalizeList :
    ∀ x xs,
      match headSortedPeriodTwoNormalList (x :: xs) with
      | [] => False
      | y :: ys =>
          Derives headSortedPeriodTwoFromTwoBasis
            (wordOfCons x xs) (wordOfCons y ys)
  | x, [] => by
      have normalEq :
          headSortedPeriodTwoNormalList [x] = [x] := by
        simp [headSortedPeriodTwoNormalList,
          periodTwoFromTwoExponent]
      rw [normalEq]
      exact Derives.refl _
  | x, y :: ys => by
      have suffixNormal := derivesNormalizeList y ys
      cases hn : headSortedPeriodTwoNormalList (y :: ys) with
      | nil =>
          exact False.elim <| normalList_cons_ne_nil y ys hn
      | cons z zs =>
          rw [hn] at suffixNormal
          have prefixed :=
            Derives.prepend (Word.singleton x) suffixNormal
          let rest := z :: zs
          let without := rest.filter (fun a => decide (a ≠ x))
          have arrangePerm :
              rest.Perm
                (List.replicate (rest.count x) x ++ without) :=
            perm_extract x rest
          have arranged :=
            headSortedPeriodTwoDerivesTailPermutation
              (Word.singleton x) arrangePerm
          have restCount :
              rest.count x =
                periodTwoFromTwoExponent ((y :: ys).count x) := by
            simpa [rest, hn] using
              headSortedPeriodTwoNormalList_count x (y :: ys)
          have restBound : rest.count x ≤ 3 := by
            rw [restCount]
            exact exponent_le_three _
          have targetExponent :
              periodTwoFromTwoExponent ((x :: y :: ys).count x) =
                if rest.count x < 3 then rest.count x + 1
                else rest.count x - 1 := by
            rw [List.count_cons_self, periodTwoFromTwoExponent_succ,
              ← restCount]
          have first :
              Derives headSortedPeriodTwoFromTwoBasis
                (wordOfCons x (y :: ys))
                (wordOfCons x
                  (List.replicate (rest.count x) x ++ without)) :=
            Derives.trans
              (by
                simpa [wordOfCons, Word.append, Word.singleton,
                  Word.append_assoc] using prefixed)
              (by
                simpa [appendList, wordOfCons, Word.singleton,
                  rest, without] using arranged)
          by_cases hsmall : rest.count x < 3
          · have normalEq :
                headSortedPeriodTwoNormalList (x :: y :: ys) =
                  x :: List.replicate (rest.count x) x ++ without := by
              change
                List.replicate
                    (periodTwoFromTwoExponent
                      ((x :: y :: ys).count x)) x ++
                    (headSortedPeriodTwoNormalList (y :: ys)).filter
                      (fun a => decide (a ≠ x)) =
                  x :: List.replicate (rest.count x) x ++ without
              rw [targetExponent, if_pos hsmall]
              rw [hn, List.replicate_succ]
            rw [normalEq]
            exact first
          · have countThree : rest.count x = 3 := by omega
            have normalEq :
                headSortedPeriodTwoNormalList (x :: y :: ys) =
                  x :: x :: without := by
              change
                List.replicate
                    (periodTwoFromTwoExponent
                      ((x :: y :: ys).count x)) x ++
                    (headSortedPeriodTwoNormalList (y :: ys)).filter
                      (fun a => decide (a ≠ x)) =
                  x :: x :: without
              rw [targetExponent, if_neg hsmall, countThree]
              rw [hn]
              simp [rest, without]
            rw [normalEq]
            exact Derives.trans first <| by
              rw [countThree]
              simpa using contractLeadingFour x without
termination_by
  _ xs => xs.length

theorem headSortedPeriodTwoDerivesNormal (w : Word Nat) :
    match headSortedPeriodTwoNormalList w.toList with
    | [] => False
    | x :: xs =>
        Derives headSortedPeriodTwoFromTwoBasis w
          (wordOfCons x xs) := by
  cases w with
  | mk head tail =>
      exact derivesNormalizeList head tail

private theorem normalList_head (x : Nat) (xs : List Nat) :
    match headSortedPeriodTwoNormalList (x :: xs) with
    | [] => False
    | y :: _ => y = x := by
  have nonempty := normalList_cons_ne_nil x xs
  cases hn : headSortedPeriodTwoNormalList (x :: xs) with
  | nil =>
      exact False.elim (nonempty hn)
  | cons y ys =>
      have positive :
          0 < periodTwoFromTwoExponent ((x :: xs).count x) :=
        periodTwoFromTwoExponent_pos (by simp)
      cases h :
          periodTwoFromTwoExponent ((x :: xs).count x) with
      | zero => omega
      | succ n =>
          simp only [headSortedPeriodTwoNormalList, h,
            List.replicate_succ, List.cons_append] at hn
          injection hn with hhead
          exact hhead.symm

private theorem normalList_word_head (w : Word Nat) :
    match headSortedPeriodTwoNormalList w.toList with
    | [] => False
    | x :: _ => x = w.head := by
  cases w with
  | mk head tail =>
      exact normalList_head head tail

/-- Equal fixed heads and equal normalized exponent states are the complete
syntactic invariants of the three-law basis. -/
theorem headSortedPeriodTwoDerivesOfInvariantEq
    (u v : Word Nat)
    (heads : u.head = v.head)
    (counts :
      ∀ z,
        periodTwoFromTwoExponent (u.toList.count z) =
          periodTwoFromTwoExponent (v.toList.count z)) :
    Derives headSortedPeriodTwoFromTwoBasis u v := by
  have uNormal := headSortedPeriodTwoDerivesNormal u
  have vNormal := headSortedPeriodTwoDerivesNormal v
  have uHeadNormal := normalList_word_head u
  have vHeadNormal := normalList_word_head v
  cases hu : headSortedPeriodTwoNormalList u.toList with
  | nil =>
      exact False.elim <| by
        rw [hu] at uNormal
        exact uNormal
  | cons ux uxs =>
      cases hv : headSortedPeriodTwoNormalList v.toList with
      | nil =>
          exact False.elim <| by
            rw [hv] at vNormal
            exact vNormal
      | cons vx vxs =>
          rw [hu] at uNormal
          rw [hv] at vNormal
          rw [hu] at uHeadNormal
          rw [hv] at vHeadNormal
          have normalizedHeads : ux = vx :=
            uHeadNormal.trans (heads.trans vHeadNormal.symm)
          have vNormal' :
              Derives headSortedPeriodTwoFromTwoBasis v
                (wordOfCons ux vxs) := by
            simpa [normalizedHeads] using vNormal
          have normalCounts :
              ∀ z, (ux :: uxs).count z = (ux :: vxs).count z := by
            intro z
            have left :=
              headSortedPeriodTwoNormalList_count z u.toList
            have right :=
              headSortedPeriodTwoNormalList_count z v.toList
            rw [hu] at left
            rw [hv] at right
            have right' :
                (ux :: vxs).count z =
                  periodTwoFromTwoExponent (v.toList.count z) := by
              simpa [normalizedHeads] using right
            exact left.trans ((counts z).trans right'.symm)
          have tailPerm : uxs.Perm vxs := by
            rw [List.perm_iff_count]
            intro z
            have h := normalCounts z
            simp only [List.count_cons] at h
            split at h <;> omega
          have middle :
              Derives headSortedPeriodTwoFromTwoBasis
                (wordOfCons ux uxs) (wordOfCons ux vxs) := by
            simpa [appendList, wordOfCons] using
              headSortedPeriodTwoDerivesTailPermutation
                (Word.singleton ux) tailPerm
          exact Derives.trans uNormal <|
            Derives.trans middle (Derives.symm vNormal')

/-- Generic unrestricted completeness theorem. A model only needs to satisfy
the three laws and separate the fixed head and all four normalized exponent
states. -/
theorem headSortedPeriodTwoFromTwoBasis_complete_of_separates
    (T : FiniteTable)
    (models : Models T.semigroup headSortedPeriodTwoFromTwoBasis)
    (separatesHead :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        e.lhs.head = e.rhs.head)
    (separatesExponent :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        ∀ z,
          periodTwoFromTwoExponent (e.lhs.toList.count z) =
            periodTwoFromTwoExponent (e.rhs.toList.count z)) :
    BasisFor T.semigroup headSortedPeriodTwoFromTwoBasis := by
  refine ⟨models, ?_⟩
  intro e valid
  exact headSortedPeriodTwoDerivesOfInvariantEq e.lhs e.rhs
    (separatesHead e valid) (separatesExponent e valid)

end SemigroupBasis.Examples
