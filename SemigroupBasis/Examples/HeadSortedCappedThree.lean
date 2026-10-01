import SemigroupBasis.Examples.CommutativePeriodTwoFromTwo

namespace SemigroupBasis.Examples

open SemigroupBasis

def headSortedCappedThreeXXX : Word Nat := ⟨0, [0, 0]⟩
def headSortedCappedThreeXXXX : Word Nat := ⟨0, [0, 0, 0]⟩
def headSortedCappedThreeXXY : Word Nat := ⟨0, [0, 1]⟩
def headSortedCappedThreeXYX : Word Nat := ⟨0, [1, 0]⟩
def headSortedCappedThreeXYZ : Word Nat := ⟨0, [1, 2]⟩
def headSortedCappedThreeXZY : Word Nat := ⟨0, [2, 1]⟩

def headSortedCappedThreePowerLaw : Identity Nat :=
  ⟨headSortedCappedThreeXXX, headSortedCappedThreeXXXX⟩

def headSortedCappedThreeGatherLaw : Identity Nat :=
  ⟨headSortedCappedThreeXXY, headSortedCappedThreeXYX⟩

def headSortedCappedThreeSuffixSwapLaw : Identity Nat :=
  ⟨headSortedCappedThreeXYZ, headSortedCappedThreeXZY⟩

/-- The fixed-head, commutative-suffix basis
`xxx = xxxx`, `xxy = xyx`, `xyz = xzy`. -/
def headSortedCappedThreeBasis : List (Identity Nat) :=
  [headSortedCappedThreePowerLaw, headSortedCappedThreeGatherLaw,
    headSortedCappedThreeSuffixSwapLaw]

private def instantiateThreeWords
    (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

/-- Contract four consecutive copies of a nonempty block to three copies. -/
theorem headSortedCappedThreeDerivesFourToThree (u : Word Nat) :
    Derives headSortedCappedThreeBasis
      (((u ++ u) ++ u) ++ u) ((u ++ u) ++ u) := by
  have hbase :
      Derives headSortedCappedThreeBasis
        headSortedCappedThreeXXXX headSortedCappedThreeXXX :=
    Derives.symm <|
      Derives.fromBasis (e := headSortedCappedThreePowerLaw) <|
        List.Mem.head _
  have h := Derives.subst hbase (instantiateThreeWords u u u)
  simpa [headSortedCappedThreeBasis,
    headSortedCappedThreePowerLaw, headSortedCappedThreeXXXX,
    headSortedCappedThreeXXX, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using h

/-- Gather a later copy of a block next to its first copy. -/
theorem headSortedCappedThreeDerivesGather (u v : Word Nat) :
    Derives headSortedCappedThreeBasis
      ((u ++ v) ++ u) ((u ++ u) ++ v) := by
  have hbase :
      Derives headSortedCappedThreeBasis
        headSortedCappedThreeXYX headSortedCappedThreeXXY :=
    Derives.symm <|
      Derives.fromBasis (e := headSortedCappedThreeGatherLaw) <|
        List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateThreeWords u v u)
  simpa [headSortedCappedThreeBasis,
    headSortedCappedThreeGatherLaw, headSortedCappedThreeXYX,
    headSortedCappedThreeXXY, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using h

/-- Swap arbitrary nonempty blocks behind a fixed nonempty prefix. -/
theorem headSortedCappedThreeDerivesSuffixSwap
    (p u v : Word Nat) :
    Derives headSortedCappedThreeBasis
      ((p ++ u) ++ v) ((p ++ v) ++ u) := by
  have hbase :
      Derives headSortedCappedThreeBasis
        headSortedCappedThreeXYZ headSortedCappedThreeXZY :=
    Derives.fromBasis (e := headSortedCappedThreeSuffixSwapLaw) <|
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  have h := Derives.subst hbase (instantiateThreeWords p u v)
  simpa [headSortedCappedThreeBasis,
    headSortedCappedThreeSuffixSwapLaw, headSortedCappedThreeXYZ,
    headSortedCappedThreeXZY, instantiateThreeWords, Word.bind,
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
theorem headSortedCappedThreeDerivesTailPermutation
    (p : Word Nat) {xs ys : List Nat} (h : xs.Perm ys) :
    Derives headSortedCappedThreeBasis
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
              headSortedCappedThreeDerivesSuffixSwap p
                (Word.singleton y) (Word.singleton x)
      | cons z zs =>
          have h :=
            Derives.appendRight
              (headSortedCappedThreeDerivesSuffixSwap p
                (Word.singleton y) (Word.singleton x))
              (wordOfCons z zs)
          rw [appendList_cons, appendList_cons]
          simpa [wordOfCons, Word.append_assoc] using h
  | trans _ _ ih₁ ih₂ =>
      exact Derives.trans (ih₁ p) (ih₂ p)

/-- Multiplicity zero, one, two, and at least three are represented by
`0`, `1`, `2`, and `3`. -/
def headSortedCappedThreeExponent (n : Nat) : Nat :=
  if n < 3 then n else 3

theorem headSortedCappedThreeExponent_le_three (n : Nat) :
    headSortedCappedThreeExponent n ≤ 3 := by
  unfold headSortedCappedThreeExponent
  split <;> omega

theorem headSortedCappedThreeExponent_pos
    {n : Nat} (positive : 0 < n) :
    0 < headSortedCappedThreeExponent n := by
  unfold headSortedCappedThreeExponent
  split <;> omega

theorem headSortedCappedThreeExponent_succ (n : Nat) :
    headSortedCappedThreeExponent (n + 1) =
      if headSortedCappedThreeExponent n < 3 then
        headSortedCappedThreeExponent n + 1
      else
        headSortedCappedThreeExponent n := by
  by_cases hn : n < 3 <;>
    by_cases hnext : n + 1 < 3 <;>
      simp [headSortedCappedThreeExponent, hn, hnext] <;>
        omega

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

/-- First-occurrence blocks with each multiplicity capped at three. -/
def headSortedCappedThreeNormalList : List Nat → List Nat
  | [] => []
  | x :: xs =>
      let rest := headSortedCappedThreeNormalList xs
      List.replicate
          (headSortedCappedThreeExponent ((x :: xs).count x)) x ++
        rest.filter (fun y => decide (y ≠ x))

theorem headSortedCappedThreeNormalList_count
    (z : Nat) :
    ∀ xs : List Nat,
      (headSortedCappedThreeNormalList xs).count z =
        headSortedCappedThreeExponent (xs.count z)
  | [] => by
      simp [headSortedCappedThreeNormalList,
        headSortedCappedThreeExponent]
  | x :: xs => by
      simp only [headSortedCappedThreeNormalList, List.count_append]
      by_cases hzx : z = x
      · subst z
        rw [List.count_replicate_self, count_filter_ne_self]
        omega
      · rw [count_replicate_of_ne hzx,
          count_filter_ne_of_ne hzx, Nat.zero_add,
          headSortedCappedThreeNormalList_count]
        rw [List.count_cons_of_ne (Ne.symm hzx)]

private theorem normalList_cons_ne_nil (x : Nat) (xs : List Nat) :
    headSortedCappedThreeNormalList (x :: xs) ≠ [] := by
  intro h
  have countEq :=
    headSortedCappedThreeNormalList_count x (x :: xs)
  rw [h, List.count_nil, List.count_cons_self] at countEq
  exact (Nat.ne_of_gt <|
    headSortedCappedThreeExponent_pos (by omega)) countEq.symm

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
    Derives headSortedCappedThreeBasis
      (wordOfCons x (x :: x :: x :: suffix))
      (wordOfCons x (x :: x :: suffix)) := by
  cases suffix with
  | nil =>
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using
          headSortedCappedThreeDerivesFourToThree (Word.singleton x)
  | cons y ys =>
      have h :=
        Derives.appendRight
          (headSortedCappedThreeDerivesFourToThree (Word.singleton x))
          (wordOfCons y ys)
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using h

private theorem derivesNormalizeList :
    ∀ x xs,
      match headSortedCappedThreeNormalList (x :: xs) with
      | [] => False
      | y :: ys =>
          Derives headSortedCappedThreeBasis
            (wordOfCons x xs) (wordOfCons y ys)
  | x, [] => by
      have normalEq :
          headSortedCappedThreeNormalList [x] = [x] := by
        simp [headSortedCappedThreeNormalList,
          headSortedCappedThreeExponent]
      rw [normalEq]
      exact Derives.refl _
  | x, y :: ys => by
      have suffixNormal := derivesNormalizeList y ys
      cases hn : headSortedCappedThreeNormalList (y :: ys) with
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
            headSortedCappedThreeDerivesTailPermutation
              (Word.singleton x) arrangePerm
          have restCount :
              rest.count x =
                headSortedCappedThreeExponent ((y :: ys).count x) := by
            simpa [rest, hn] using
              headSortedCappedThreeNormalList_count x (y :: ys)
          have restBound : rest.count x ≤ 3 := by
            rw [restCount]
            exact headSortedCappedThreeExponent_le_three _
          have targetExponent :
              headSortedCappedThreeExponent ((x :: y :: ys).count x) =
                if rest.count x < 3 then rest.count x + 1
                else rest.count x := by
            rw [List.count_cons_self, headSortedCappedThreeExponent_succ,
              ← restCount]
          have first :
              Derives headSortedCappedThreeBasis
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
                headSortedCappedThreeNormalList (x :: y :: ys) =
                  x :: List.replicate (rest.count x) x ++ without := by
              change
                List.replicate
                    (headSortedCappedThreeExponent
                      ((x :: y :: ys).count x)) x ++
                    (headSortedCappedThreeNormalList (y :: ys)).filter
                      (fun a => decide (a ≠ x)) =
                  x :: List.replicate (rest.count x) x ++ without
              rw [targetExponent, if_pos hsmall]
              rw [hn, List.replicate_succ]
            rw [normalEq]
            exact first
          · have countThree : rest.count x = 3 := by omega
            have normalEq :
                headSortedCappedThreeNormalList (x :: y :: ys) =
                  x :: x :: x :: without := by
              change
                List.replicate
                    (headSortedCappedThreeExponent
                      ((x :: y :: ys).count x)) x ++
                    (headSortedCappedThreeNormalList (y :: ys)).filter
                      (fun a => decide (a ≠ x)) =
                  x :: x :: x :: without
              rw [targetExponent, if_neg hsmall, countThree]
              rw [hn]
              simp [rest, without]
            rw [normalEq]
            exact Derives.trans first <| by
              rw [countThree]
              simpa using contractLeadingFour x without
termination_by
  _ xs => xs.length

theorem headSortedCappedThreeDerivesNormal (w : Word Nat) :
    match headSortedCappedThreeNormalList w.toList with
    | [] => False
    | x :: xs =>
        Derives headSortedCappedThreeBasis w
          (wordOfCons x xs) := by
  cases w with
  | mk head tail =>
      exact derivesNormalizeList head tail

private theorem normalList_head (x : Nat) (xs : List Nat) :
    match headSortedCappedThreeNormalList (x :: xs) with
    | [] => False
    | y :: _ => y = x := by
  have nonempty := normalList_cons_ne_nil x xs
  cases hn : headSortedCappedThreeNormalList (x :: xs) with
  | nil =>
      exact False.elim (nonempty hn)
  | cons y ys =>
      have positive :
          0 < headSortedCappedThreeExponent ((x :: xs).count x) :=
        headSortedCappedThreeExponent_pos (by simp)
      cases h :
          headSortedCappedThreeExponent ((x :: xs).count x) with
      | zero => omega
      | succ n =>
          simp only [headSortedCappedThreeNormalList, h,
            List.replicate_succ, List.cons_append] at hn
          injection hn with hhead
          exact hhead.symm

private theorem normalList_word_head (w : Word Nat) :
    match headSortedCappedThreeNormalList w.toList with
    | [] => False
    | x :: _ => x = w.head := by
  cases w with
  | mk head tail =>
      exact normalList_head head tail

/-- Equal fixed heads and equal capped multiplicities are the complete
syntactic invariants of the three-law basis. -/
theorem headSortedCappedThreeDerivesOfInvariantEq
    (u v : Word Nat)
    (heads : u.head = v.head)
    (counts :
      ∀ z,
        headSortedCappedThreeExponent (u.toList.count z) =
          headSortedCappedThreeExponent (v.toList.count z)) :
    Derives headSortedCappedThreeBasis u v := by
  have uNormal := headSortedCappedThreeDerivesNormal u
  have vNormal := headSortedCappedThreeDerivesNormal v
  have uHeadNormal := normalList_word_head u
  have vHeadNormal := normalList_word_head v
  cases hu : headSortedCappedThreeNormalList u.toList with
  | nil =>
      exact False.elim <| by
        rw [hu] at uNormal
        exact uNormal
  | cons ux uxs =>
      cases hv : headSortedCappedThreeNormalList v.toList with
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
              Derives headSortedCappedThreeBasis v
                (wordOfCons ux vxs) := by
            simpa [normalizedHeads] using vNormal
          have normalCounts :
              ∀ z, (ux :: uxs).count z = (ux :: vxs).count z := by
            intro z
            have left :=
              headSortedCappedThreeNormalList_count z u.toList
            have right :=
              headSortedCappedThreeNormalList_count z v.toList
            rw [hu] at left
            rw [hv] at right
            have right' :
                (ux :: vxs).count z =
                  headSortedCappedThreeExponent (v.toList.count z) := by
              simpa [normalizedHeads] using right
            exact left.trans ((counts z).trans right'.symm)
          have tailPerm : uxs.Perm vxs := by
            rw [List.perm_iff_count]
            intro z
            have h := normalCounts z
            simp only [List.count_cons] at h
            split at h <;> omega
          have middle :
              Derives headSortedCappedThreeBasis
                (wordOfCons ux uxs) (wordOfCons ux vxs) := by
            simpa [appendList, wordOfCons] using
              headSortedCappedThreeDerivesTailPermutation
                (Word.singleton ux) tailPerm
          exact Derives.trans uNormal <|
            Derives.trans middle (Derives.symm vNormal')

/-- Generic unrestricted completeness theorem. A finite model only needs to
satisfy the three laws and separate the fixed head and the four capped
multiplicity states. -/
theorem headSortedCappedThreeBasis_complete_of_separates
    (T : FiniteTable)
    (models : Models T.semigroup headSortedCappedThreeBasis)
    (separatesHead :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        e.lhs.head = e.rhs.head)
    (separatesExponent :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        ∀ z,
          headSortedCappedThreeExponent (e.lhs.toList.count z) =
            headSortedCappedThreeExponent (e.rhs.toList.count z)) :
    BasisFor T.semigroup headSortedCappedThreeBasis := by
  refine ⟨models, ?_⟩
  intro e valid
  exact headSortedCappedThreeDerivesOfInvariantEq e.lhs e.rhs
    (separatesHead e valid) (separatesExponent e valid)

end SemigroupBasis.Examples
