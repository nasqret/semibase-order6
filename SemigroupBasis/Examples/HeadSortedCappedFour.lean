import SemigroupBasis.Examples.CommutativePeriodTwoFromTwo

namespace SemigroupBasis.Examples

open SemigroupBasis

def headSortedCappedFourXXXX : Word Nat := ⟨0, [0, 0, 0]⟩
def headSortedCappedFourXXXXX : Word Nat := ⟨0, [0, 0, 0, 0]⟩
def headSortedCappedFourXXY : Word Nat := ⟨0, [0, 1]⟩
def headSortedCappedFourXYX : Word Nat := ⟨0, [1, 0]⟩
def headSortedCappedFourXYZ : Word Nat := ⟨0, [1, 2]⟩
def headSortedCappedFourXZY : Word Nat := ⟨0, [2, 1]⟩

def headSortedCappedFourPowerLaw : Identity Nat :=
  ⟨headSortedCappedFourXXXX, headSortedCappedFourXXXXX⟩

def headSortedCappedFourGatherLaw : Identity Nat :=
  ⟨headSortedCappedFourXXY, headSortedCappedFourXYX⟩

def headSortedCappedFourSuffixSwapLaw : Identity Nat :=
  ⟨headSortedCappedFourXYZ, headSortedCappedFourXZY⟩

/-- The fixed-head, commutative-suffix basis
`xxxx = xxxxx`, `xxy = xyx`, `xyz = xzy`. -/
def headSortedCappedFourBasis : List (Identity Nat) :=
  [headSortedCappedFourPowerLaw, headSortedCappedFourGatherLaw,
    headSortedCappedFourSuffixSwapLaw]

private def instantiateThreeWords
    (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

/-- Contract five consecutive copies of a nonempty block to four copies. -/
theorem headSortedCappedFourDerivesFiveToFour (u : Word Nat) :
    Derives headSortedCappedFourBasis
      ((((u ++ u) ++ u) ++ u) ++ u) (((u ++ u) ++ u) ++ u) := by
  have hbase :
      Derives headSortedCappedFourBasis
        headSortedCappedFourXXXXX headSortedCappedFourXXXX :=
    Derives.symm <|
      Derives.fromBasis (e := headSortedCappedFourPowerLaw) <|
        List.Mem.head _
  have h := Derives.subst hbase (instantiateThreeWords u u u)
  simpa [headSortedCappedFourBasis,
    headSortedCappedFourPowerLaw, headSortedCappedFourXXXXX,
    headSortedCappedFourXXXX, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using h

/-- Gather a later copy of a block next to its first copy. -/
theorem headSortedCappedFourDerivesGather (u v : Word Nat) :
    Derives headSortedCappedFourBasis
      ((u ++ v) ++ u) ((u ++ u) ++ v) := by
  have hbase :
      Derives headSortedCappedFourBasis
        headSortedCappedFourXYX headSortedCappedFourXXY :=
    Derives.symm <|
      Derives.fromBasis (e := headSortedCappedFourGatherLaw) <|
        List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateThreeWords u v u)
  simpa [headSortedCappedFourBasis,
    headSortedCappedFourGatherLaw, headSortedCappedFourXYX,
    headSortedCappedFourXXY, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using h

/-- Swap arbitrary nonempty blocks behind a fixed nonempty prefix. -/
theorem headSortedCappedFourDerivesSuffixSwap
    (p u v : Word Nat) :
    Derives headSortedCappedFourBasis
      ((p ++ u) ++ v) ((p ++ v) ++ u) := by
  have hbase :
      Derives headSortedCappedFourBasis
        headSortedCappedFourXYZ headSortedCappedFourXZY :=
    Derives.fromBasis (e := headSortedCappedFourSuffixSwapLaw) <|
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  have h := Derives.subst hbase (instantiateThreeWords p u v)
  simpa [headSortedCappedFourBasis,
    headSortedCappedFourSuffixSwapLaw, headSortedCappedFourXYZ,
    headSortedCappedFourXZY, instantiateThreeWords, Word.bind,
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
theorem headSortedCappedFourDerivesTailPermutation
    (p : Word Nat) {xs ys : List Nat} (h : xs.Perm ys) :
    Derives headSortedCappedFourBasis
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
              headSortedCappedFourDerivesSuffixSwap p
                (Word.singleton y) (Word.singleton x)
      | cons z zs =>
          have h :=
            Derives.appendRight
              (headSortedCappedFourDerivesSuffixSwap p
                (Word.singleton y) (Word.singleton x))
              (wordOfCons z zs)
          rw [appendList_cons, appendList_cons]
          simpa [wordOfCons, Word.append_assoc] using h
  | trans _ _ ih₁ ih₂ =>
      exact Derives.trans (ih₁ p) (ih₂ p)

/-- Multiplicities zero through three remain exact, while every multiplicity
at least four is represented by `4`. -/
def headSortedCappedFourExponent (n : Nat) : Nat :=
  if n < 4 then n else 4

theorem headSortedCappedFourExponent_le_four (n : Nat) :
    headSortedCappedFourExponent n ≤ 4 := by
  unfold headSortedCappedFourExponent
  split <;> omega

theorem headSortedCappedFourExponent_pos
    {n : Nat} (positive : 0 < n) :
    0 < headSortedCappedFourExponent n := by
  unfold headSortedCappedFourExponent
  split <;> omega

theorem headSortedCappedFourExponent_succ (n : Nat) :
    headSortedCappedFourExponent (n + 1) =
      if headSortedCappedFourExponent n < 4 then
        headSortedCappedFourExponent n + 1
      else
        headSortedCappedFourExponent n := by
  by_cases hn : n < 4 <;>
    by_cases hnext : n + 1 < 4 <;>
      simp [headSortedCappedFourExponent, hn, hnext] <;>
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

/-- First-occurrence blocks with each multiplicity capped at four. -/
def headSortedCappedFourNormalList : List Nat → List Nat
  | [] => []
  | x :: xs =>
      let rest := headSortedCappedFourNormalList xs
      List.replicate
          (headSortedCappedFourExponent ((x :: xs).count x)) x ++
        rest.filter (fun y => decide (y ≠ x))

theorem headSortedCappedFourNormalList_count
    (z : Nat) :
    ∀ xs : List Nat,
      (headSortedCappedFourNormalList xs).count z =
        headSortedCappedFourExponent (xs.count z)
  | [] => by
      simp [headSortedCappedFourNormalList,
        headSortedCappedFourExponent]
  | x :: xs => by
      simp only [headSortedCappedFourNormalList, List.count_append]
      by_cases hzx : z = x
      · subst z
        rw [List.count_replicate_self, count_filter_ne_self]
        omega
      · rw [count_replicate_of_ne hzx,
          count_filter_ne_of_ne hzx, Nat.zero_add,
          headSortedCappedFourNormalList_count]
        rw [List.count_cons_of_ne (Ne.symm hzx)]

private theorem normalList_cons_ne_nil (x : Nat) (xs : List Nat) :
    headSortedCappedFourNormalList (x :: xs) ≠ [] := by
  intro h
  have countEq :=
    headSortedCappedFourNormalList_count x (x :: xs)
  rw [h, List.count_nil, List.count_cons_self] at countEq
  exact (Nat.ne_of_gt <|
    headSortedCappedFourExponent_pos (by omega)) countEq.symm

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
    Derives headSortedCappedFourBasis
      (wordOfCons x (x :: x :: x :: x :: suffix))
      (wordOfCons x (x :: x :: x :: suffix)) := by
  cases suffix with
  | nil =>
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using
          headSortedCappedFourDerivesFiveToFour (Word.singleton x)
  | cons y ys =>
      have h :=
        Derives.appendRight
          (headSortedCappedFourDerivesFiveToFour (Word.singleton x))
          (wordOfCons y ys)
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using h

private theorem derivesNormalizeList :
    ∀ x xs,
      match headSortedCappedFourNormalList (x :: xs) with
      | [] => False
      | y :: ys =>
          Derives headSortedCappedFourBasis
            (wordOfCons x xs) (wordOfCons y ys)
  | x, [] => by
      have normalEq :
          headSortedCappedFourNormalList [x] = [x] := by
        simp [headSortedCappedFourNormalList,
          headSortedCappedFourExponent]
      rw [normalEq]
      exact Derives.refl _
  | x, y :: ys => by
      have suffixNormal := derivesNormalizeList y ys
      cases hn : headSortedCappedFourNormalList (y :: ys) with
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
            headSortedCappedFourDerivesTailPermutation
              (Word.singleton x) arrangePerm
          have restCount :
              rest.count x =
                headSortedCappedFourExponent ((y :: ys).count x) := by
            simpa [rest, hn] using
              headSortedCappedFourNormalList_count x (y :: ys)
          have restBound : rest.count x ≤ 4 := by
            rw [restCount]
            exact headSortedCappedFourExponent_le_four _
          have targetExponent :
              headSortedCappedFourExponent ((x :: y :: ys).count x) =
                if rest.count x < 4 then rest.count x + 1
                else rest.count x := by
            rw [List.count_cons_self, headSortedCappedFourExponent_succ,
              ← restCount]
          have first :
              Derives headSortedCappedFourBasis
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
                headSortedCappedFourNormalList (x :: y :: ys) =
                  x :: List.replicate (rest.count x) x ++ without := by
              change
                List.replicate
                    (headSortedCappedFourExponent
                      ((x :: y :: ys).count x)) x ++
                    (headSortedCappedFourNormalList (y :: ys)).filter
                      (fun a => decide (a ≠ x)) =
                  x :: List.replicate (rest.count x) x ++ without
              rw [targetExponent, if_pos hsmall]
              rw [hn, List.replicate_succ]
            rw [normalEq]
            exact first
          · have countFour : rest.count x = 4 := by omega
            have normalEq :
                headSortedCappedFourNormalList (x :: y :: ys) =
                  x :: x :: x :: x :: without := by
              change
                List.replicate
                    (headSortedCappedFourExponent
                      ((x :: y :: ys).count x)) x ++
                    (headSortedCappedFourNormalList (y :: ys)).filter
                      (fun a => decide (a ≠ x)) =
                  x :: x :: x :: x :: without
              rw [targetExponent, if_neg hsmall, countFour]
              rw [hn]
              simp [rest, without]
            rw [normalEq]
            exact Derives.trans first <| by
              rw [countFour]
              simpa using contractLeadingFive x without
termination_by
  _ xs => xs.length

theorem headSortedCappedFourDerivesNormal (w : Word Nat) :
    match headSortedCappedFourNormalList w.toList with
    | [] => False
    | x :: xs =>
        Derives headSortedCappedFourBasis w
          (wordOfCons x xs) := by
  cases w with
  | mk head tail =>
      exact derivesNormalizeList head tail

private theorem normalList_head (x : Nat) (xs : List Nat) :
    match headSortedCappedFourNormalList (x :: xs) with
    | [] => False
    | y :: _ => y = x := by
  have nonempty := normalList_cons_ne_nil x xs
  cases hn : headSortedCappedFourNormalList (x :: xs) with
  | nil =>
      exact False.elim (nonempty hn)
  | cons y ys =>
      have positive :
          0 < headSortedCappedFourExponent ((x :: xs).count x) :=
        headSortedCappedFourExponent_pos (by simp)
      cases h :
          headSortedCappedFourExponent ((x :: xs).count x) with
      | zero => omega
      | succ n =>
          simp only [headSortedCappedFourNormalList, h,
            List.replicate_succ, List.cons_append] at hn
          injection hn with hhead
          exact hhead.symm

private theorem normalList_word_head (w : Word Nat) :
    match headSortedCappedFourNormalList w.toList with
    | [] => False
    | x :: _ => x = w.head := by
  cases w with
  | mk head tail =>
      exact normalList_head head tail

/-- Equal fixed heads and equal capped multiplicities are the complete
syntactic invariants of the three-law basis. -/
theorem headSortedCappedFourDerivesOfInvariantEq
    (u v : Word Nat)
    (heads : u.head = v.head)
    (counts :
      ∀ z,
        headSortedCappedFourExponent (u.toList.count z) =
          headSortedCappedFourExponent (v.toList.count z)) :
    Derives headSortedCappedFourBasis u v := by
  have uNormal := headSortedCappedFourDerivesNormal u
  have vNormal := headSortedCappedFourDerivesNormal v
  have uHeadNormal := normalList_word_head u
  have vHeadNormal := normalList_word_head v
  cases hu : headSortedCappedFourNormalList u.toList with
  | nil =>
      exact False.elim <| by
        rw [hu] at uNormal
        exact uNormal
  | cons ux uxs =>
      cases hv : headSortedCappedFourNormalList v.toList with
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
              Derives headSortedCappedFourBasis v
                (wordOfCons ux vxs) := by
            simpa [normalizedHeads] using vNormal
          have normalCounts :
              ∀ z, (ux :: uxs).count z = (ux :: vxs).count z := by
            intro z
            have left :=
              headSortedCappedFourNormalList_count z u.toList
            have right :=
              headSortedCappedFourNormalList_count z v.toList
            rw [hu] at left
            rw [hv] at right
            have right' :
                (ux :: vxs).count z =
                  headSortedCappedFourExponent (v.toList.count z) := by
              simpa [normalizedHeads] using right
            exact left.trans ((counts z).trans right'.symm)
          have tailPerm : uxs.Perm vxs := by
            rw [List.perm_iff_count]
            intro z
            have h := normalCounts z
            simp only [List.count_cons] at h
            split at h <;> omega
          have middle :
              Derives headSortedCappedFourBasis
                (wordOfCons ux uxs) (wordOfCons ux vxs) := by
            simpa [appendList, wordOfCons] using
              headSortedCappedFourDerivesTailPermutation
                (Word.singleton ux) tailPerm
          exact Derives.trans uNormal <|
            Derives.trans middle (Derives.symm vNormal')

/-- Generic unrestricted completeness theorem. A finite model only needs to
satisfy the three laws and separate the fixed head and the five capped
multiplicity states. -/
theorem headSortedCappedFourBasis_complete_of_separates
    (T : FiniteTable)
    (models : Models T.semigroup headSortedCappedFourBasis)
    (separatesHead :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        e.lhs.head = e.rhs.head)
    (separatesExponent :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        ∀ z,
          headSortedCappedFourExponent (e.lhs.toList.count z) =
            headSortedCappedFourExponent (e.rhs.toList.count z)) :
    BasisFor T.semigroup headSortedCappedFourBasis := by
  refine ⟨models, ?_⟩
  intro e valid
  exact headSortedCappedFourDerivesOfInvariantEq e.lhs e.rhs
    (separatesHead e valid) (separatesExponent e valid)

end SemigroupBasis.Examples
