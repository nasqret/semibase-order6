import SemigroupBasis.CoRoots.S5_794Invariant
import SemigroupBasis.Examples.UniqueSeparatorFourQuadraticSwap

namespace SemigroupBasis.CoRoots.S5_794

open SemigroupBasis
open SemigroupBasis.Examples

/-- Evaluate a possibly empty list in the monoid `M14`, starting at its
identity element `4`. -/
def m14ListEval
    (valuation : Nat → Fin 5) (letters : List Nat) : Fin 5 :=
  letters.foldl
    (fun current letter => publishedM14Mul current (valuation letter)) 4

/-- Semantic equivalence for possibly empty lists. -/
def M14ListEquivalent (left right : List Nat) : Prop :=
  ∀ valuation, m14ListEval valuation left = m14ListEval valuation right

private theorem publishedM14Mul_leftIdentity (value : Fin 5) :
    publishedM14Mul 4 value = value := by
  decide +revert

private theorem m14ListEval_cons_eq_eval
    (valuation : Nat → Fin 5) (head : Nat) (tail : List Nat) :
    m14ListEval valuation (head :: tail) =
      publishedM14Table.semigroup.eval valuation
        (S5_107.listWordOfCons head tail) := by
  unfold m14ListEval S5_107.listWordOfCons
  change
    tail.foldl
        (fun current letter =>
          publishedM14Mul current (valuation letter))
        (publishedM14Mul 4 (valuation head)) =
      tail.foldl
        (fun current letter =>
          publishedM14Mul current (valuation letter))
        (valuation head)
  rw [publishedM14Mul_leftIdentity]

namespace M14ListEquivalent

theorem refl (letters : List Nat) :
    M14ListEquivalent letters letters :=
  fun _ => rfl

theorem symm {left right : List Nat}
    (equivalent : M14ListEquivalent left right) :
    M14ListEquivalent right left :=
  fun valuation => (equivalent valuation).symm

theorem trans {left middle right : List Nat}
    (first : M14ListEquivalent left middle)
    (second : M14ListEquivalent middle right) :
    M14ListEquivalent left right :=
  fun valuation => (first valuation).trans (second valuation)

theorem of_derives {left right : List Nat}
    (derivation : S5_107.ListDerives basis left right) :
    M14ListEquivalent left right := by
  cases derivation with
  | empty => exact refl []
  | @words leftHead rightHead leftTail rightTail wordDerivation =>
      intro valuation
      rw [m14ListEval_cons_eq_eval, m14ListEval_cons_eq_eval]
      exact wordDerivation.sound publishedM14Models valuation

end M14ListEquivalent

private def pairValuation (x y : Nat) : Nat → Fin 5 :=
  fun letter => if letter = x then 2 else if letter = y then 3 else 4

@[simp]
private theorem pairValuation_x (x y : Nat) :
    pairValuation x y x = 2 := by
  simp [pairValuation]

@[simp]
private theorem pairValuation_y {x y : Nat} (different : x ≠ y) :
    pairValuation x y y = 3 := by
  simp [pairValuation, Ne.symm different]

private theorem pairMul_two (x y letter : Nat) :
    publishedM14Mul 2 (pairValuation x y letter) = 2 := by
  by_cases isX : letter = x
  · simp [pairValuation, isX, publishedM14Mul]
  · by_cases isY : letter = y
    · subst letter
      simp [pairValuation, isX, publishedM14Mul]
    · simp [pairValuation, isX, isY, publishedM14Mul]

private theorem pairMul_three (x y letter : Nat) :
    publishedM14Mul 3 (pairValuation x y letter) = 3 := by
  by_cases isX : letter = x
  · simp [pairValuation, isX, publishedM14Mul]
  · by_cases isY : letter = y
    · subst letter
      simp [pairValuation, isX, publishedM14Mul]
    · simp [pairValuation, isX, isY, publishedM14Mul]

private theorem pairFold_two (x y : Nat) :
    ∀ letters : List Nat,
      letters.foldl
          (fun current letter =>
            publishedM14Mul current (pairValuation x y letter)) 2 = 2
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      rw [pairMul_two]
      exact pairFold_two x y rest

private theorem pairFold_three (x y : Nat) :
    ∀ letters : List Nat,
      letters.foldl
          (fun current letter =>
            publishedM14Mul current (pairValuation x y letter)) 3 = 3
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      rw [pairMul_three]
      exact pairFold_three x y rest

private theorem pairFold_identity_of_absent
    (x y : Nat) :
    ∀ initial : List Nat,
      x ∉ initial →
      y ∉ initial →
      initial.foldl
          (fun current letter =>
            publishedM14Mul current (pairValuation x y letter)) 4 = 4
  | [], _, _ => rfl
  | letter :: rest, xAbsent, yAbsent => by
      have letterNeX : letter ≠ x := by
        intro equal
        subst letter
        exact xAbsent (List.Mem.head rest)
      have letterNeY : letter ≠ y := by
        intro equal
        subst letter
        exact yAbsent (List.Mem.head rest)
      have restXAbsent : x ∉ rest :=
        fun member => xAbsent (List.Mem.tail letter member)
      have restYAbsent : y ∉ rest :=
        fun member => yAbsent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      rw [show pairValuation x y letter = 4 by
        simp [pairValuation, letterNeX, letterNeY]]
      rw [publishedM14Mul_leftIdentity]
      exact pairFold_identity_of_absent x y rest
        restXAbsent restYAbsent

private theorem pairEval_firstX
    {x y : Nat} (different : x ≠ y)
    (initial rest : List Nat)
    (xAbsent : x ∉ initial) (yAbsent : y ∉ initial) :
    m14ListEval (pairValuation x y) (initial ++ x :: rest) = 2 := by
  unfold m14ListEval
  rw [List.foldl_append]
  rw [pairFold_identity_of_absent x y initial xAbsent yAbsent]
  simp only [List.foldl_cons]
  rw [pairValuation_x, publishedM14Mul_leftIdentity]
  exact pairFold_two x y rest

private theorem pairEval_firstY
    {x y : Nat} (different : x ≠ y)
    (initial rest : List Nat)
    (xAbsent : x ∉ initial) (yAbsent : y ∉ initial) :
    m14ListEval (pairValuation x y) (initial ++ y :: rest) = 3 := by
  unfold m14ListEval
  rw [List.foldl_append]
  rw [pairFold_identity_of_absent x y initial xAbsent yAbsent]
  simp only [List.foldl_cons]
  rw [pairValuation_y different, publishedM14Mul_leftIdentity]
  exact pairFold_three x y rest

private theorem seen_of_equivalent_target_head
    {fixedPrefix currentPrefix currentSuffix targetSuffix : List Nat}
    {x y : Nat}
    (different : x ≠ y)
    (prefixContains :
      ∀ letter, letter ∈ fixedPrefix → letter ∈ currentPrefix)
    (equivalent :
      M14ListEquivalent
        (currentPrefix ++ x :: y :: currentSuffix)
        (fixedPrefix ++ y :: targetSuffix)) :
    x ∈ currentPrefix ∨ y ∈ currentPrefix := by
  by_cases xSeen : x ∈ currentPrefix
  · exact Or.inl xSeen
  · by_cases ySeen : y ∈ currentPrefix
    · exact Or.inr ySeen
    · have xAbsentFixed : x ∉ fixedPrefix := by
        intro member
        exact xSeen (prefixContains x member)
      have yAbsentFixed : y ∉ fixedPrefix := by
        intro member
        exact ySeen (prefixContains y member)
      have evaluated := equivalent (pairValuation x y)
      rw [pairEval_firstX different currentPrefix
            (y :: currentSuffix) xSeen ySeen,
          pairEval_firstY different fixedPrefix targetSuffix
            xAbsentFixed yAbsentFixed] at evaluated
      exact False.elim ((by decide : (2 : Fin 5) ≠ 3) evaluated)

/-- An adjacent pair of distinct quadratic letters can be swapped whenever
at least one of the pair has already occurred. These are exactly Edmunds'
four `L₇/L₈` positional cases. -/
theorem listDerivesAdjacentSeen
    {x y : Nat} {pre post : List Nat}
    (different : x ≠ y)
    (xQuadratic : (pre ++ (x :: y :: post)).count x = 2)
    (yQuadratic : (pre ++ (x :: y :: post)).count y = 2)
    (seen : x ∈ pre ∨ y ∈ pre) :
    S5_107.ListDerives basis
      (pre ++ (x :: y :: post))
      (pre ++ (y :: x :: post)) := by
  have xSideCounts : pre.count x + post.count x = 1 := by
    have count := xQuadratic
    simp only [List.count_append, List.count_cons_self,
      List.count_cons_of_ne (Ne.symm different)] at count
    omega
  have ySideCounts : pre.count y + post.count y = 1 := by
    have count := yQuadratic
    simp only [List.count_append, List.count_cons_of_ne different,
      List.count_cons_self] at count
    omega
  rcases seen with xInPre | yInPre
  · by_cases yAlsoInPre : y ∈ pre
    · rcases uniqueSeparatorDistinctOccurrencesOrdered
          different xInPre yAlsoInPre with orderedXY | orderedYX
      · rcases orderedXY with ⟨before, middle, after, shape⟩
        rw [shape]
        simpa [List.append_assoc] using
          (listDerivesL8 x y middle after).context before post
      · rcases orderedYX with ⟨before, middle, after, shape⟩
        rw [shape]
        simpa [List.append_assoc] using
          (listDerivesL8 y x middle after).symm.context before post
    · have yPreCount : pre.count y = 0 :=
        List.count_eq_zero.mpr yAlsoInPre
      have yInPost : y ∈ post := by
        apply List.count_pos_iff.mp
        omega
      rcases List.append_of_mem xInPre with
        ⟨before, left, preShape⟩
      rcases List.append_of_mem yInPost with
        ⟨right, after, postShape⟩
      rw [preShape, postShape]
      simpa [List.append_assoc] using
        (listDerivesL7 x y left right).symm.context before after
  · by_cases xAlsoInPre : x ∈ pre
    · rcases uniqueSeparatorDistinctOccurrencesOrdered
          different xAlsoInPre yInPre with orderedXY | orderedYX
      · rcases orderedXY with ⟨before, middle, after, shape⟩
        rw [shape]
        simpa [List.append_assoc] using
          (listDerivesL8 x y middle after).context before post
      · rcases orderedYX with ⟨before, middle, after, shape⟩
        rw [shape]
        simpa [List.append_assoc] using
          (listDerivesL8 y x middle after).symm.context before post
    · have xPreCount : pre.count x = 0 :=
        List.count_eq_zero.mpr xAlsoInPre
      have xInPost : x ∈ post := by
        apply List.count_pos_iff.mp
        omega
      rcases List.append_of_mem yInPre with
        ⟨before, left, preShape⟩
      rcases List.append_of_mem xInPost with
        ⟨right, after, postShape⟩
      rw [preShape, postShape]
      simpa [List.append_assoc] using
        (listDerivesL7 y x left right).context before after

private theorem listDerivesMoveMemberToFront
    (fixedPrefix targetTail sourcePost targetPost : List Nat)
    (selected : Nat) :
    ∀ (currentPrefix source : List Nat),
      (∀ letter, letter ∈ fixedPrefix → letter ∈ currentPrefix) →
      selected ∈ source →
      (∀ letter, letter ∈ source →
        (currentPrefix ++ source ++ sourcePost).count letter = 2) →
      M14ListEquivalent
        (currentPrefix ++ source ++ sourcePost)
        (fixedPrefix ++ selected :: targetTail ++ targetPost) →
      S5_107.ListDerives basis
        (currentPrefix ++ source ++ sourcePost)
        (currentPrefix ++ selected :: source.erase selected ++ sourcePost)
  | currentPrefix, [], _, member, _, _ => by
      simp at member
  | currentPrefix, head :: tail, prefixContains, member,
      quadratic, equivalent => by
      by_cases equal : head = selected
      · subst head
        simpa using
          S5_107.ListDerives.refl (basis := basis)
            (currentPrefix ++ selected :: tail ++ sourcePost)
      · have selectedInTail : selected ∈ tail := by
          simpa [Ne.symm equal] using member
        have nextPrefixContains :
            ∀ letter,
              letter ∈ fixedPrefix →
                letter ∈ currentPrefix ++ [head] := by
          intro letter fixedMember
          exact List.mem_append_left [head]
            (prefixContains letter fixedMember)
        have tailQuadratic :
            ∀ letter, letter ∈ tail →
              ((currentPrefix ++ [head]) ++ tail ++ sourcePost).count
                  letter = 2 := by
          intro letter tailMember
          simpa [List.append_assoc] using
            quadratic letter (List.Mem.tail head tailMember)
        have tailEquivalent :
            M14ListEquivalent
              ((currentPrefix ++ [head]) ++ tail ++ sourcePost)
              (fixedPrefix ++ selected :: targetTail ++ targetPost) := by
          simpa [List.append_assoc] using equivalent
        have moveTail :=
          listDerivesMoveMemberToFront
            fixedPrefix targetTail sourcePost targetPost selected
            (currentPrefix ++ [head]) tail
            nextPrefixContains selectedInTail
            tailQuadratic tailEquivalent
        have movedEquivalent :
            M14ListEquivalent
              (currentPrefix ++
                head :: selected :: tail.erase selected ++ sourcePost)
              (fixedPrefix ++ selected :: targetTail ++ targetPost) := by
          have sound := M14ListEquivalent.of_derives moveTail
          exact (by
            simpa [List.append_assoc] using sound.symm.trans tailEquivalent)
        have tailExpose :
            tail.Perm (selected :: tail.erase selected) :=
          List.perm_cons_erase selectedInTail
        have blockExpose :
            (head :: tail).Perm
              (head :: selected :: tail.erase selected) :=
          List.Perm.cons head tailExpose
        have headQuadratic :
            (currentPrefix ++
              head :: selected :: tail.erase selected ++ sourcePost).count
                head =
                2 := by
          calc
            (currentPrefix ++
                head :: selected :: tail.erase selected ++ sourcePost).count
                  head =
                (currentPrefix ++ head :: tail ++ sourcePost).count head := by
              simp only [List.count_append]
              rw [← blockExpose.count head]
            _ = 2 := quadratic head (by simp)
        have selectedQuadratic :
            (currentPrefix ++
              head :: selected :: tail.erase selected ++ sourcePost).count
                selected = 2 := by
          calc
            (currentPrefix ++
                head :: selected :: tail.erase selected ++ sourcePost).count
                selected =
                (currentPrefix ++ head :: tail ++ sourcePost).count
                  selected := by
              simp only [List.count_append]
              rw [← blockExpose.count selected]
            _ = 2 := quadratic selected member
        have seen : head ∈ currentPrefix ∨ selected ∈ currentPrefix :=
          seen_of_equivalent_target_head equal prefixContains <| by
            simpa [List.append_assoc] using movedEquivalent
        have swap :=
          listDerivesAdjacentSeen
            (pre := currentPrefix)
            (post := tail.erase selected ++ sourcePost)
            equal
            (by simpa [List.append_assoc] using headQuadratic)
            (by simpa [List.append_assoc] using selectedQuadratic)
            seen
        have complete := moveTail.trans <| by
          simpa [List.append_assoc] using swap
        simpa [equal, List.append_assoc] using complete
termination_by
  _ source => source.length

/-- General form of Edmunds' Lemma 4.4. The semantic comparison may have a
different suffix; the derivation changes only the displayed source block. -/
theorem listDerivesQuadraticBlockPermutationAgainst :
    ∀ (target source pre sourcePost targetPost : List Nat),
      source.Perm target →
      (∀ letter, letter ∈ source →
        (pre ++ source ++ sourcePost).count letter = 2) →
      M14ListEquivalent
        (pre ++ source ++ sourcePost)
        (pre ++ target ++ targetPost) →
      S5_107.ListDerives basis
        (pre ++ source ++ sourcePost)
        (pre ++ target ++ sourcePost)
  | [], source, pre, sourcePost, _, permutation, _, _ => by
      have sourceEmpty : source = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa using permutation.length_eq
      subst source
      simpa [List.append_assoc] using
        S5_107.ListDerives.refl (basis := basis) (pre ++ sourcePost)
  | selected :: targetTail, source, pre, sourcePost, targetPost,
      permutation, quadratic, equivalent => by
      have selectedInSource : selected ∈ source :=
        permutation.mem_iff.mpr (by simp)
      have move :=
        listDerivesMoveMemberToFront
          pre targetTail sourcePost targetPost selected pre source
          (fun _ member => member)
          selectedInSource quadratic <| by
            simpa [List.append_assoc] using equivalent
      have sourceExpose :
          source.Perm (selected :: source.erase selected) :=
        List.perm_cons_erase selectedInSource
      have erasedPermutation :
          (source.erase selected).Perm targetTail := by
        simpa using permutation.erase selected
      have fullExpose :
          (pre ++ source ++ sourcePost).Perm
            ((pre ++ [selected]) ++ source.erase selected ++ sourcePost) := by
        simpa [List.append_assoc] using
          List.Perm.append
            (List.Perm.append (List.Perm.refl pre) sourceExpose)
            (List.Perm.refl sourcePost)
      have erasedQuadratic :
          ∀ letter, letter ∈ source.erase selected →
            ((pre ++ [selected]) ++ source.erase selected ++ sourcePost).count
              letter = 2 := by
        intro letter erasedMember
        have sourceMember : letter ∈ source :=
          List.mem_of_mem_erase erasedMember
        calc
          ((pre ++ [selected]) ++ source.erase selected ++ sourcePost).count
              letter =
              (pre ++ source ++ sourcePost).count letter := by
            exact (fullExpose.count letter).symm
          _ = 2 := quadratic letter sourceMember
      have exposedEquivalent :
          M14ListEquivalent
            ((pre ++ [selected]) ++ source.erase selected ++ sourcePost)
            ((pre ++ [selected]) ++ targetTail ++ targetPost) := by
        have moveSound := M14ListEquivalent.of_derives move
        have exposedToTarget := moveSound.symm.trans equivalent
        simpa [List.append_assoc] using exposedToTarget
      have rest :=
        listDerivesQuadraticBlockPermutationAgainst
          targetTail (source.erase selected) (pre ++ [selected])
          sourcePost targetPost
          erasedPermutation erasedQuadratic exposedEquivalent
      exact move.trans <| by
        simpa [List.append_assoc] using rest
termination_by
  target _ _ _ _ => target.length

/-- Edmunds' Lemma 4.4: a permutation of one quadratic block is derivable
when the complete contextual identity is valid in `M14`. The validity
condition is what forbids the two first-occurrence-reversing `L₆` cases. -/
theorem listDerivesQuadraticBlockPermutation
    (target source pre post : List Nat)
    (permutation : source.Perm target)
    (quadratic :
      ∀ letter, letter ∈ source →
        (pre ++ source ++ post).count letter = 2)
    (equivalent :
      M14ListEquivalent
        (pre ++ source ++ post)
        (pre ++ target ++ post)) :
    S5_107.ListDerives basis
      (pre ++ source ++ post)
      (pre ++ target ++ post) :=
  listDerivesQuadraticBlockPermutationAgainst
    target source pre post post permutation quadratic equivalent

end SemigroupBasis.CoRoots.S5_794
