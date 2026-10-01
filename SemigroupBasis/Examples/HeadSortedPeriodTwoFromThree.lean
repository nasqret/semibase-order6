import SemigroupBasis.Examples.CommutativePeriodTwoFromThree

namespace SemigroupBasis.Examples

open SemigroupBasis

def headSortedPeriodTwoFromThreeXXX : Word Nat := ⟨0, [0, 0]⟩
def headSortedPeriodTwoFromThreeXXXXX : Word Nat := ⟨0, [0, 0, 0, 0]⟩
def headSortedPeriodTwoFromThreeXXY : Word Nat := ⟨0, [0, 1]⟩
def headSortedPeriodTwoFromThreeXYX : Word Nat := ⟨0, [1, 0]⟩
def headSortedPeriodTwoFromThreeXYZ : Word Nat := ⟨0, [1, 2]⟩
def headSortedPeriodTwoFromThreeXZY : Word Nat := ⟨0, [2, 1]⟩

def headSortedPeriodTwoFromThreePowerLaw : Identity Nat :=
  ⟨headSortedPeriodTwoFromThreeXXX, headSortedPeriodTwoFromThreeXXXXX⟩

def headSortedPeriodTwoFromThreeGatherLaw : Identity Nat :=
  ⟨headSortedPeriodTwoFromThreeXXY, headSortedPeriodTwoFromThreeXYX⟩

def headSortedPeriodTwoFromThreeSuffixSwapLaw : Identity Nat :=
  ⟨headSortedPeriodTwoFromThreeXYZ, headSortedPeriodTwoFromThreeXZY⟩

/-- The fixed-head, commutative-suffix basis
`xxx = xxxxx`, `xxy = xyx`, `xyz = xzy`. -/
def headSortedPeriodTwoFromThreeBasis : List (Identity Nat) :=
  [headSortedPeriodTwoFromThreePowerLaw, headSortedPeriodTwoFromThreeGatherLaw,
    headSortedPeriodTwoFromThreeSuffixSwapLaw]

private def instantiateThreeWords
    (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

/-- Contract five consecutive copies of a nonempty block to three copies. -/
theorem headSortedPeriodTwoFromThreeDerivesFiveToThree (u : Word Nat) :
    Derives headSortedPeriodTwoFromThreeBasis
      ((((u ++ u) ++ u) ++ u) ++ u) ((u ++ u) ++ u) := by
  have hbase :
      Derives headSortedPeriodTwoFromThreeBasis
        headSortedPeriodTwoFromThreeXXXXX headSortedPeriodTwoFromThreeXXX :=
    Derives.symm <|
      Derives.fromBasis (e := headSortedPeriodTwoFromThreePowerLaw) <|
        List.Mem.head _
  have h := Derives.subst hbase (instantiateThreeWords u u u)
  simpa [headSortedPeriodTwoFromThreeBasis,
    headSortedPeriodTwoFromThreePowerLaw, headSortedPeriodTwoFromThreeXXXXX,
    headSortedPeriodTwoFromThreeXXX, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using h

/-- Gather a later copy of a block next to its first copy. -/
theorem headSortedPeriodTwoFromThreeDerivesGather (u v : Word Nat) :
    Derives headSortedPeriodTwoFromThreeBasis
      ((u ++ v) ++ u) ((u ++ u) ++ v) := by
  have hbase :
      Derives headSortedPeriodTwoFromThreeBasis
        headSortedPeriodTwoFromThreeXYX headSortedPeriodTwoFromThreeXXY :=
    Derives.symm <|
      Derives.fromBasis (e := headSortedPeriodTwoFromThreeGatherLaw) <|
        List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateThreeWords u v u)
  simpa [headSortedPeriodTwoFromThreeBasis,
    headSortedPeriodTwoFromThreeGatherLaw, headSortedPeriodTwoFromThreeXYX,
    headSortedPeriodTwoFromThreeXXY, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using h

/-- Swap arbitrary nonempty blocks behind a fixed nonempty prefix. -/
theorem headSortedPeriodTwoFromThreeDerivesSuffixSwap
    (p u v : Word Nat) :
    Derives headSortedPeriodTwoFromThreeBasis
      ((p ++ u) ++ v) ((p ++ v) ++ u) := by
  have hbase :
      Derives headSortedPeriodTwoFromThreeBasis
        headSortedPeriodTwoFromThreeXYZ headSortedPeriodTwoFromThreeXZY :=
    Derives.fromBasis (e := headSortedPeriodTwoFromThreeSuffixSwapLaw) <|
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  have h := Derives.subst hbase (instantiateThreeWords p u v)
  simpa [headSortedPeriodTwoFromThreeBasis,
    headSortedPeriodTwoFromThreeSuffixSwapLaw, headSortedPeriodTwoFromThreeXYZ,
    headSortedPeriodTwoFromThreeXZY, instantiateThreeWords, Word.bind,
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
theorem headSortedPeriodTwoFromThreeDerivesTailPermutation
    (p : Word Nat) {xs ys : List Nat} (h : xs.Perm ys) :
    Derives headSortedPeriodTwoFromThreeBasis
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
              headSortedPeriodTwoFromThreeDerivesSuffixSwap p
                (Word.singleton y) (Word.singleton x)
      | cons z zs =>
          have h :=
            Derives.appendRight
              (headSortedPeriodTwoFromThreeDerivesSuffixSwap p
                (Word.singleton y) (Word.singleton x))
              (wordOfCons z zs)
          rw [appendList_cons, appendList_cons]
          simpa [wordOfCons, Word.append_assoc] using h
  | trans _ _ ih₁ ih₂ =>
      exact Derives.trans (ih₁ p) (ih₂ p)

private theorem exponent_le_four (n : Nat) :
    periodTwoFromThreeExponent n ≤ 4 := by
  unfold periodTwoFromThreeExponent
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

/-- First-occurrence blocks with exact states zero, one, and two, followed by
the two parity states beginning at exponent three. -/
def headSortedPeriodTwoFromThreeNormalList : List Nat → List Nat
  | [] => []
  | x :: xs =>
      let rest := headSortedPeriodTwoFromThreeNormalList xs
      List.replicate
          (periodTwoFromThreeExponent ((x :: xs).count x)) x ++
        rest.filter (fun y => decide (y ≠ x))

theorem headSortedPeriodTwoFromThreeNormalList_count
    (z : Nat) :
    ∀ xs : List Nat,
      (headSortedPeriodTwoFromThreeNormalList xs).count z =
        periodTwoFromThreeExponent (xs.count z)
  | [] => by
      simp [headSortedPeriodTwoFromThreeNormalList,
        periodTwoFromThreeExponent]
  | x :: xs => by
      simp only [headSortedPeriodTwoFromThreeNormalList, List.count_append]
      by_cases hzx : z = x
      · subst z
        rw [List.count_replicate_self, count_filter_ne_self]
        omega
      · rw [count_replicate_of_ne hzx,
          count_filter_ne_of_ne hzx, Nat.zero_add,
          headSortedPeriodTwoFromThreeNormalList_count]
        rw [List.count_cons_of_ne (Ne.symm hzx)]

private theorem normalList_cons_ne_nil (x : Nat) (xs : List Nat) :
    headSortedPeriodTwoFromThreeNormalList (x :: xs) ≠ [] := by
  intro h
  have countEq :=
    headSortedPeriodTwoFromThreeNormalList_count x (x :: xs)
  rw [h, List.count_nil, List.count_cons_self] at countEq
  exact (Nat.ne_of_gt <|
    periodTwoFromThreeExponent_pos (by omega)) countEq.symm

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

private theorem contractLeadingFive (x : Nat) (suffix : List Nat) :
    Derives headSortedPeriodTwoFromThreeBasis
      (wordOfCons x (x :: x :: x :: x :: suffix))
      (wordOfCons x (x :: x :: suffix)) := by
  cases suffix with
  | nil =>
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using
          headSortedPeriodTwoFromThreeDerivesFiveToThree (Word.singleton x)
  | cons y ys =>
      have h :=
        Derives.appendRight
          (headSortedPeriodTwoFromThreeDerivesFiveToThree (Word.singleton x))
          (wordOfCons y ys)
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using h

private theorem derivesNormalizeList :
    ∀ x xs,
      match headSortedPeriodTwoFromThreeNormalList (x :: xs) with
      | [] => False
      | y :: ys =>
          Derives headSortedPeriodTwoFromThreeBasis
            (wordOfCons x xs) (wordOfCons y ys)
  | x, [] => by
      have normalEq :
          headSortedPeriodTwoFromThreeNormalList [x] = [x] := by
        simp [headSortedPeriodTwoFromThreeNormalList,
          periodTwoFromThreeExponent]
      rw [normalEq]
      exact Derives.refl _
  | x, y :: ys => by
      have suffixNormal := derivesNormalizeList y ys
      cases hn : headSortedPeriodTwoFromThreeNormalList (y :: ys) with
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
            headSortedPeriodTwoFromThreeDerivesTailPermutation
              (Word.singleton x) arrangePerm
          have restCount :
              rest.count x =
                periodTwoFromThreeExponent ((y :: ys).count x) := by
            simpa [rest, hn] using
              headSortedPeriodTwoFromThreeNormalList_count x (y :: ys)
          have restBound : rest.count x ≤ 4 := by
            rw [restCount]
            exact exponent_le_four _
          have targetExponent :
              periodTwoFromThreeExponent ((x :: y :: ys).count x) =
                if rest.count x < 4 then rest.count x + 1
                else rest.count x - 1 := by
            rw [List.count_cons_self, periodTwoFromThreeExponent_succ,
              ← restCount]
          have first :
              Derives headSortedPeriodTwoFromThreeBasis
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
          by_cases hsmall : rest.count x < 4
          · have normalEq :
                headSortedPeriodTwoFromThreeNormalList (x :: y :: ys) =
                  x :: List.replicate (rest.count x) x ++ without := by
              change
                List.replicate
                    (periodTwoFromThreeExponent
                      ((x :: y :: ys).count x)) x ++
                    (headSortedPeriodTwoFromThreeNormalList (y :: ys)).filter
                      (fun a => decide (a ≠ x)) =
                  x :: List.replicate (rest.count x) x ++ without
              rw [targetExponent, if_pos hsmall]
              rw [hn, List.replicate_succ]
            rw [normalEq]
            exact first
          · have countFour : rest.count x = 4 := by omega
            have normalEq :
                headSortedPeriodTwoFromThreeNormalList (x :: y :: ys) =
                  x :: x :: x :: without := by
              change
                List.replicate
                    (periodTwoFromThreeExponent
                      ((x :: y :: ys).count x)) x ++
                    (headSortedPeriodTwoFromThreeNormalList (y :: ys)).filter
                      (fun a => decide (a ≠ x)) =
                  x :: x :: x :: without
              rw [targetExponent, if_neg hsmall, countFour]
              rw [hn]
              simp [rest, without]
            rw [normalEq]
            exact Derives.trans first <| by
              rw [countFour]
              simpa using contractLeadingFive x without
termination_by
  _ xs => xs.length

theorem headSortedPeriodTwoFromThreeDerivesNormal (w : Word Nat) :
    match headSortedPeriodTwoFromThreeNormalList w.toList with
    | [] => False
    | x :: xs =>
        Derives headSortedPeriodTwoFromThreeBasis w
          (wordOfCons x xs) := by
  cases w with
  | mk head tail =>
      exact derivesNormalizeList head tail

private theorem normalList_head (x : Nat) (xs : List Nat) :
    match headSortedPeriodTwoFromThreeNormalList (x :: xs) with
    | [] => False
    | y :: _ => y = x := by
  have nonempty := normalList_cons_ne_nil x xs
  cases hn : headSortedPeriodTwoFromThreeNormalList (x :: xs) with
  | nil =>
      exact False.elim (nonempty hn)
  | cons y ys =>
      have positive :
          0 < periodTwoFromThreeExponent ((x :: xs).count x) :=
        periodTwoFromThreeExponent_pos (by simp)
      cases h :
          periodTwoFromThreeExponent ((x :: xs).count x) with
      | zero => omega
      | succ n =>
          simp only [headSortedPeriodTwoFromThreeNormalList, h,
            List.replicate_succ, List.cons_append] at hn
          injection hn with hhead
          exact hhead.symm

private theorem normalList_word_head (w : Word Nat) :
    match headSortedPeriodTwoFromThreeNormalList w.toList with
    | [] => False
    | x :: _ => x = w.head := by
  cases w with
  | mk head tail =>
      exact normalList_head head tail

/-- Equal fixed heads and equal normalized exponent states are the complete
syntactic invariants of the three-law basis. -/
theorem headSortedPeriodTwoFromThreeDerivesOfInvariantEq
    (u v : Word Nat)
    (heads : u.head = v.head)
    (counts :
      ∀ z,
        periodTwoFromThreeExponent (u.toList.count z) =
          periodTwoFromThreeExponent (v.toList.count z)) :
    Derives headSortedPeriodTwoFromThreeBasis u v := by
  have uNormal := headSortedPeriodTwoFromThreeDerivesNormal u
  have vNormal := headSortedPeriodTwoFromThreeDerivesNormal v
  have uHeadNormal := normalList_word_head u
  have vHeadNormal := normalList_word_head v
  cases hu : headSortedPeriodTwoFromThreeNormalList u.toList with
  | nil =>
      exact False.elim <| by
        rw [hu] at uNormal
        exact uNormal
  | cons ux uxs =>
      cases hv : headSortedPeriodTwoFromThreeNormalList v.toList with
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
              Derives headSortedPeriodTwoFromThreeBasis v
                (wordOfCons ux vxs) := by
            simpa [normalizedHeads] using vNormal
          have normalCounts :
              ∀ z, (ux :: uxs).count z = (ux :: vxs).count z := by
            intro z
            have left :=
              headSortedPeriodTwoFromThreeNormalList_count z u.toList
            have right :=
              headSortedPeriodTwoFromThreeNormalList_count z v.toList
            rw [hu] at left
            rw [hv] at right
            have right' :
                (ux :: vxs).count z =
                  periodTwoFromThreeExponent (v.toList.count z) := by
              simpa [normalizedHeads] using right
            exact left.trans ((counts z).trans right'.symm)
          have tailPerm : uxs.Perm vxs := by
            rw [List.perm_iff_count]
            intro z
            have h := normalCounts z
            simp only [List.count_cons] at h
            split at h <;> omega
          have middle :
              Derives headSortedPeriodTwoFromThreeBasis
                (wordOfCons ux uxs) (wordOfCons ux vxs) := by
            simpa [appendList, wordOfCons] using
              headSortedPeriodTwoFromThreeDerivesTailPermutation
                (Word.singleton ux) tailPerm
          exact Derives.trans uNormal <|
            Derives.trans middle (Derives.symm vNormal')

/-- Generic unrestricted completeness theorem. A model only needs to satisfy
the three laws and separate the fixed head and all five normalized exponent
states. -/
theorem headSortedPeriodTwoFromThreeBasis_complete_of_separates
    (T : FiniteTable)
    (models : Models T.semigroup headSortedPeriodTwoFromThreeBasis)
    (separatesHead :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        e.lhs.head = e.rhs.head)
    (separatesExponent :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        ∀ z,
          periodTwoFromThreeExponent (e.lhs.toList.count z) =
            periodTwoFromThreeExponent (e.rhs.toList.count z)) :
    BasisFor T.semigroup headSortedPeriodTwoFromThreeBasis := by
  refine ⟨models, ?_⟩
  intro e valid
  exact headSortedPeriodTwoFromThreeDerivesOfInvariantEq e.lhs e.rhs
    (separatesHead e valid) (separatesExponent e valid)

end SemigroupBasis.Examples
