import SemigroupBasis.CoRoots.Order6SporadicSection11Canonical

namespace SemigroupBasis.CoRoots.Order6SporadicSection11

/-- A decomposition at the rightmost block containing at least two copies,
together with the normal list obtained by removing one copy from that block. -/
def RightmostRepeatedReduction (source : List Nat) : Prop :=
  ∃ before pivot right,
    source = before ++ [pivot, pivot] ++ right ∧
      pivot ∉ before ∧
      S5_530.S5_530Normal (before ++ [pivot] ++ right) ∧
      right.Nodup ∧
      (before ++ [pivot] ++ right).count pivot ≤ 2

private theorem target_mem_source
    {source before right : List Nat} {pivot tested : Nat}
    (sourceEq : source = before ++ [pivot, pivot] ++ right)
    (member : tested ∈ before ++ [pivot] ++ right) :
    tested ∈ source := by
  rw [sourceEq]
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at *
  rcases member with (beforeMem | pivotEq) | rightMem
  · exact Or.inl (Or.inl beforeMem)
  · exact Or.inl (Or.inr (Or.inl pivotEq))
  · exact Or.inr rightMem

/-- A block-normal list is duplicate-free, or has a reduction at its
rightmost repeated block. In the latter case the suffix following the removed
copy is duplicate-free. -/
theorem normal_nodup_or_rightmostRepeatedReduction
    {letters : List Nat}
    (normal : S5_530.S5_530Normal letters) :
    letters.Nodup ∨ RightmostRepeatedReduction letters := by
  induction normal with
  | nil =>
      exact Or.inl List.nodup_nil
  | single letter rest restNormal notMem induction =>
      rcases induction with restNodup | reduction
      · exact Or.inl (List.nodup_cons.mpr ⟨notMem, restNodup⟩)
      · rcases reduction with
          ⟨before, pivot, right, sourceEq, pivotNotBefore, targetNormal,
            rightNodup, pivotBound⟩
        have letterNotMemTarget :
            letter ∉ before ++ [pivot] ++ right := by
          intro member
          exact notMem (target_mem_source sourceEq member)
        have pivotMem : pivot ∈ rest := by
          rw [sourceEq]
          simp
        have pivotNeLetter : pivot ≠ letter := by
          intro equal
          subst pivot
          exact notMem pivotMem
        exact Or.inr ⟨letter :: before, pivot, right,
          by simp [sourceEq, List.append_assoc],
          by simp [pivotNeLetter, pivotNotBefore],
          by
            simpa [List.append_assoc] using
              S5_530.S5_530Normal.single
                letter _ targetNormal letterNotMemTarget,
          rightNodup,
          by
            simpa [List.count_cons_of_ne (Ne.symm pivotNeLetter),
              List.append_assoc] using pivotBound⟩
  | double letter rest restNormal notMem induction =>
      rcases induction with restNodup | reduction
      · exact Or.inr ⟨[], letter, rest,
          by simp,
          by simp,
          by
            simpa using
              S5_530.S5_530Normal.single
                letter rest restNormal notMem,
          restNodup,
          by simp [List.count_eq_zero.mpr notMem]⟩
      · rcases reduction with
          ⟨before, pivot, right, sourceEq, pivotNotBefore, targetNormal,
            rightNodup, pivotBound⟩
        have letterNotMemTarget :
            letter ∉ before ++ [pivot] ++ right := by
          intro member
          exact notMem (target_mem_source sourceEq member)
        have pivotMem : pivot ∈ rest := by
          rw [sourceEq]
          simp
        have pivotNeLetter : pivot ≠ letter := by
          intro equal
          subst pivot
          exact notMem pivotMem
        exact Or.inr ⟨[letter, letter] ++ before, pivot, right,
          by simp [sourceEq, List.append_assoc],
          by simp [pivotNeLetter, pivotNotBefore],
          by
            simpa [List.append_assoc] using
              S5_530.S5_530Normal.double
                letter _ targetNormal letterNotMemTarget,
          rightNodup,
          by
            simpa [List.count_cons_of_ne (Ne.symm pivotNeLetter),
              List.append_assoc] using pivotBound⟩
  | triple letter rest restNormal notMem induction =>
      rcases induction with restNodup | reduction
      · have rightNodup : (letter :: rest).Nodup :=
          List.nodup_cons.mpr ⟨notMem, restNodup⟩
        exact Or.inr ⟨[], letter, letter :: rest,
          by simp,
          by simp,
          by
            simpa using
              S5_530.S5_530Normal.double
                letter rest restNormal notMem,
          rightNodup,
          by simp [List.count_eq_zero.mpr notMem]⟩
      · rcases reduction with
          ⟨before, pivot, right, sourceEq, pivotNotBefore, targetNormal,
            rightNodup, pivotBound⟩
        have letterNotMemTarget :
            letter ∉ before ++ [pivot] ++ right := by
          intro member
          exact notMem (target_mem_source sourceEq member)
        have pivotMem : pivot ∈ rest := by
          rw [sourceEq]
          simp
        have pivotNeLetter : pivot ≠ letter := by
          intro equal
          subst pivot
          exact notMem pivotMem
        exact Or.inr ⟨[letter, letter, letter] ++ before, pivot, right,
          by simp [sourceEq, List.append_assoc],
          by simp [pivotNeLetter, pivotNotBefore],
          by
            simpa [List.append_assoc] using
              S5_530.S5_530Normal.triple
                letter _ targetNormal letterNotMemTarget,
          rightNodup,
          by
            simpa [List.count_cons_of_ne (Ne.symm pivotNeLetter),
              List.append_assoc] using pivotBound⟩

/-- Split a protected block-normal prefix at its current terminal owner. Either
the suffix after the first owner copy is already duplicate-free, or a later
rightmost repeated pivot is exposed together with the normal prefix obtained
after changing terminal ownership. -/
def TerminalOwnerSplit (source : List Nat) (owner : Nat) : Prop :=
  (∃ before after,
    source = before ++ [owner] ++ after ∧
      owner ∉ before ∧ after.Nodup) ∨
  ∃ before middle pivot right,
    source = before ++ [owner] ++ middle ++ [pivot, pivot] ++ right ∧
      pivot ∉ before ++ [owner, owner] ++ middle ∧
      S5_530.S5_530Normal
        (before ++ [owner, owner] ++ middle ++ [pivot] ++ right) ∧
      right.Nodup ∧
      (before ++ [owner, owner] ++ middle ++ [pivot] ++ right).count
          pivot ≤ 2

private theorem changed_target_mem_source
    {source before middle right : List Nat}
    {owner pivot tested : Nat}
    (sourceEq :
      source = before ++ [owner] ++ middle ++ [pivot, pivot] ++ right)
    (member :
      tested ∈
        before ++ [owner, owner] ++ middle ++ [pivot] ++ right) :
    tested ∈ source := by
  rw [sourceEq]
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at *
  rcases member with (((beforeOrOwners | middleMem) | pivotEq) | rightMem)
  · rcases beforeOrOwners with beforeMem | ownerEq | ownerEq
    · exact Or.inl (Or.inl (Or.inl (Or.inl beforeMem)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr ownerEq)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr ownerEq)))
  · exact Or.inl (Or.inl (Or.inr middleMem))
  · exact Or.inl (Or.inr (Or.inl pivotEq))
  · exact Or.inr rightMem

private theorem not_mem_replicate_append
    {selected letter : Nat} {rest : List Nat}
    (different : selected ≠ letter) (absent : selected ∉ rest)
    (copies : Nat) :
    selected ∉ List.replicate copies letter ++ rest := by
  induction copies with
  | zero => simpa
  | succ copies induction =>
      rw [List.replicate_succ, List.cons_append]
      intro member
      rcases List.mem_cons.mp member with equal | member
      · exact different equal
      · exact induction member

theorem normal_terminalOwnerSplit
    {source : List Nat} {owner : Nat}
    (normal : S5_530.S5_530Normal source)
    (ownerMem : owner ∈ source)
    (ownerBound : source.count owner ≤ 2) :
    TerminalOwnerSplit source owner := by
  induction normal generalizing owner with
  | nil =>
      simp at ownerMem
  | single letter rest restNormal notMem induction =>
      by_cases equal : owner = letter
      · subst owner
        rcases normal_nodup_or_rightmostRepeatedReduction restNormal with
          restNodup | reduction
        · exact Or.inl ⟨[], rest, by simp, by simp, restNodup⟩
        · rcases reduction with
            ⟨before, pivot, right, sourceEq, pivotNotBefore, targetNormal,
              rightNodup, pivotBound⟩
          have ownerNotMemTarget :
              letter ∉ before ++ [pivot] ++ right := by
            intro member
            exact notMem (target_mem_source sourceEq member)
          have pivotMem : pivot ∈ rest := by
            rw [sourceEq]
            simp
          have pivotNeOwner : pivot ≠ letter := by
            intro pivotEqual
            subst pivot
            exact notMem pivotMem
          exact Or.inr ⟨[], before, pivot, right,
            by simp [sourceEq, List.append_assoc],
            by simp [pivotNeOwner, pivotNotBefore, List.append_assoc],
            by
              simpa [List.append_assoc] using
                S5_530.S5_530Normal.double
                  letter _ targetNormal ownerNotMemTarget,
            rightNodup,
            by
              simpa [List.count_cons_of_ne (Ne.symm pivotNeOwner),
                List.append_assoc] using pivotBound⟩
      · have ownerMemRest : owner ∈ rest := by
          simpa [equal] using ownerMem
        have ownerBoundRest : rest.count owner ≤ 2 := by
          simpa [List.count_cons_of_ne (Ne.symm equal)] using ownerBound
        rcases induction ownerMemRest ownerBoundRest with
          canonical | pivoted
        · rcases canonical with
            ⟨before, after, sourceEq, ownerNotBefore, afterNodup⟩
          exact Or.inl ⟨letter :: before, after,
            by simp [sourceEq, List.append_assoc],
            by simp [equal, ownerNotBefore], afterNodup⟩
        · rcases pivoted with
            ⟨before, middle, pivot, right, sourceEq,
              pivotNotTargetBefore, targetNormal,
              rightNodup, pivotBound⟩
          have letterNotMemTarget :
              letter ∉
                before ++ [owner, owner] ++ middle ++ [pivot] ++ right := by
            intro member
            exact notMem (changed_target_mem_source sourceEq member)
          have pivotMem : pivot ∈ rest := by
            rw [sourceEq]
            simp
          have pivotNeLetter : pivot ≠ letter := by
            intro pivotEqual
            subst pivot
            exact notMem pivotMem
          exact Or.inr ⟨letter :: before, middle, pivot, right,
            by simp [sourceEq, List.append_assoc],
            by
              have absent :=
                not_mem_replicate_append
                  pivotNeLetter pivotNotTargetBefore 1
              simpa [List.append_assoc] using absent,
            by
              simpa [List.append_assoc] using
                S5_530.S5_530Normal.single
                  letter _ targetNormal letterNotMemTarget,
            rightNodup,
            by
              simpa [List.count_cons_of_ne (Ne.symm pivotNeLetter),
                List.append_assoc] using pivotBound⟩
  | double letter rest restNormal notMem induction =>
      by_cases equal : owner = letter
      · subst owner
        rcases normal_nodup_or_rightmostRepeatedReduction restNormal with
          restNodup | reduction
        · have afterNodup : (letter :: rest).Nodup :=
            List.nodup_cons.mpr ⟨notMem, restNodup⟩
          exact Or.inl ⟨[], letter :: rest, by simp, by simp, afterNodup⟩
        · rcases reduction with
            ⟨before, pivot, right, sourceEq, pivotNotBefore, targetNormal,
              rightNodup, pivotBound⟩
          have ownerNotMemTarget :
              letter ∉ before ++ [pivot] ++ right := by
            intro member
            exact notMem (target_mem_source sourceEq member)
          have pivotMem : pivot ∈ rest := by
            rw [sourceEq]
            simp
          have pivotNeOwner : pivot ≠ letter := by
            intro pivotEqual
            subst pivot
            exact notMem pivotMem
          exact Or.inr ⟨[], letter :: before, pivot, right,
            by simp [sourceEq, List.append_assoc],
            by simp [pivotNeOwner, pivotNotBefore, List.append_assoc],
            by
              simpa [List.append_assoc] using
                S5_530.S5_530Normal.triple
                  letter _ targetNormal ownerNotMemTarget,
            rightNodup,
            by
              simpa [List.count_cons_of_ne (Ne.symm pivotNeOwner),
                List.append_assoc] using pivotBound⟩
      · have ownerMemRest : owner ∈ rest := by
          simpa [equal] using ownerMem
        have ownerBoundRest : rest.count owner ≤ 2 := by
          simpa [List.count_cons_of_ne (Ne.symm equal)] using ownerBound
        rcases induction ownerMemRest ownerBoundRest with
          canonical | pivoted
        · rcases canonical with
            ⟨before, after, sourceEq, ownerNotBefore, afterNodup⟩
          exact Or.inl ⟨[letter, letter] ++ before, after,
            by simp [sourceEq, List.append_assoc],
            by simp [equal, ownerNotBefore], afterNodup⟩
        · rcases pivoted with
            ⟨before, middle, pivot, right, sourceEq,
              pivotNotTargetBefore, targetNormal,
              rightNodup, pivotBound⟩
          have letterNotMemTarget :
              letter ∉
                before ++ [owner, owner] ++ middle ++ [pivot] ++ right := by
            intro member
            exact notMem (changed_target_mem_source sourceEq member)
          have pivotMem : pivot ∈ rest := by
            rw [sourceEq]
            simp
          have pivotNeLetter : pivot ≠ letter := by
            intro pivotEqual
            subst pivot
            exact notMem pivotMem
          exact Or.inr ⟨[letter, letter] ++ before, middle, pivot, right,
            by simp [sourceEq, List.append_assoc],
            by
              have absent :=
                not_mem_replicate_append
                  pivotNeLetter pivotNotTargetBefore 2
              simpa [List.append_assoc] using absent,
            by
              simpa [List.append_assoc] using
                S5_530.S5_530Normal.double
                  letter _ targetNormal letterNotMemTarget,
            rightNodup,
            by
              simpa [List.count_cons_of_ne (Ne.symm pivotNeLetter),
                List.append_assoc] using pivotBound⟩
  | triple letter rest restNormal notMem induction =>
      by_cases equal : owner = letter
      · subst owner
        have exactCount :
            (letter :: letter :: letter :: rest).count letter = 3 := by
          simp [List.count_eq_zero.mpr notMem]
        omega
      · have ownerMemRest : owner ∈ rest := by
          simpa [equal] using ownerMem
        have ownerBoundRest : rest.count owner ≤ 2 := by
          simpa [List.count_cons_of_ne (Ne.symm equal)] using ownerBound
        rcases induction ownerMemRest ownerBoundRest with
          canonical | pivoted
        · rcases canonical with
            ⟨before, after, sourceEq, ownerNotBefore, afterNodup⟩
          exact Or.inl ⟨[letter, letter, letter] ++ before, after,
            by simp [sourceEq, List.append_assoc],
            by simp [equal, ownerNotBefore], afterNodup⟩
        · rcases pivoted with
            ⟨before, middle, pivot, right, sourceEq,
              pivotNotTargetBefore, targetNormal,
              rightNodup, pivotBound⟩
          have letterNotMemTarget :
              letter ∉
                before ++ [owner, owner] ++ middle ++ [pivot] ++ right := by
            intro member
            exact notMem (changed_target_mem_source sourceEq member)
          have pivotMem : pivot ∈ rest := by
            rw [sourceEq]
            simp
          have pivotNeLetter : pivot ≠ letter := by
            intro pivotEqual
            subst pivot
            exact notMem pivotMem
          exact Or.inr ⟨[letter, letter, letter] ++ before,
            middle, pivot, right,
            by simp [sourceEq, List.append_assoc],
            by
              have absent :=
                not_mem_replicate_append
                  pivotNeLetter pivotNotTargetBefore 3
              simpa [List.append_assoc] using absent,
            by
              simpa [List.append_assoc] using
                S5_530.S5_530Normal.triple
                  letter _ targetNormal letterNotMemTarget,
            rightNodup,
            by
              simpa [List.count_cons_of_ne (Ne.symm pivotNeLetter),
                List.append_assoc] using pivotBound⟩

end SemigroupBasis.CoRoots.Order6SporadicSection11
