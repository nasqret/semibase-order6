import SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section01.Section01Macros

/-! Terminal normal forms in the exact B23 calculus. No lower-basis period-one
contraction is used. Prefix support is retained explicitly, so prefix parity
normalization never relies on erasing the last occurrence of a letter. -/

namespace SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section01.Section01TerminalForms

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_107
open SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section01.Section01Macros

theorem insertSquare (pre : List Nat) (m p t : Nat) (member : m ∈ pre) :
    D (pre ++ [p, t]) ((pre ++ [m, m]) ++ [p, t]) := by
  apply prefixOfSupportParity
  · intro z
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_self]
    constructor
    · exact Or.inl
    · intro h
      rcases h with h | rfl
      · exact h
      · exact member
  · intro z
    simp only [List.count_append]
    by_cases equal : m = z
    · subst z
      simp only [List.count_cons_self, List.count_nil]
      omega
    · have absent : z ∉ [m, m] := by simp [Ne.symm equal]
      rw [List.count_eq_zero.mpr absent, Nat.add_zero]

/-- The entire original support is retained before the new terminal square. -/
theorem retargetSquare (pre : List Nat) (p m : Nat) (member : m ∈ pre ∨ m = p) :
    D (pre ++ [p, p]) ((pre ++ [p, p, p, p]) ++ [m, m]) := by
  have present : m ∈ pre ++ [p, p] := by simpa using member
  have pad : D (pre ++ [p, p]) ((pre ++ [p, p]) ++ [p, p]) := by
    simpa [List.append_assoc] using (squarePadding p).prepend pre
  have insert : D ((pre ++ [p, p]) ++ [p, p])
      (((pre ++ [p, p]) ++ [m, m]) ++ [p, p]) :=
    insertSquare (pre ++ [p, p]) m p p present
  have commute : D (((pre ++ [p, p]) ++ [m, m]) ++ [p, p])
      ((pre ++ [p, p, p, p]) ++ [m, m]) := by
    simpa [List.append_assoc] using (squareCommutation m p).prepend (pre ++ [p, p])
  exact pad.trans (insert.trans commute)

theorem permTailOne (pre : List Nat) (p : Nat) (member : p ∈ pre) :
    pre.Perm (pre.erase p ++ [p]) := by
  have first := List.perm_cons_erase member
  have second : (p :: pre.erase p).Perm (pre.erase p ++ [p]) := by
    exact (List.perm_append_comm : ([p] ++ pre.erase p).Perm (pre.erase p ++ [p]))
  exact first.trans second

theorem permTailPair (pre : List Nat) (p t : Nat)
    (pMember : p ∈ pre) (tMember : t ∈ pre) (distinct : p ≠ t) :
    ∃ rest, pre.Perm (rest ++ [p, t]) := by
  have tRemains : t ∈ pre.erase p := (List.mem_erase_of_ne (Ne.symm distinct)).mpr tMember
  let rest := (pre.erase p).erase t
  have first : pre.Perm (p :: t :: rest) :=
    (List.perm_cons_erase pMember).trans (List.Perm.cons p (List.perm_cons_erase tRemains))
  have second : (p :: t :: rest).Perm (rest ++ [p, t]) := by
    exact (List.perm_append_comm : ([p, t] ++ rest).Perm (rest ++ [p, t]))
  exact ⟨rest, first.trans second⟩

/-- A repeated penultimate marker may be replaced by any marker in its stem.
The final marker is untouched and the new prefix has exactly the old stem's
support. This applies in particular when the final marker is globally simple. -/
theorem repeatedPenultimateNormal (stem : List Nat) (p t m : Nat)
    (pMember : p ∈ stem) (mMember : m ∈ stem) :
    ∃ pre, D (stem ++ [p, t]) (pre ++ [m, m, t]) ∧
      (∀ z, z ∈ pre ↔ z ∈ stem) := by
  let rest := stem.erase p
  have permutation : stem.Perm (rest ++ [p]) := permTailOne stem p pMember
  have member : m ∈ rest ∨ m = p := by
    have h := permutation.mem_iff.mp mMember
    simpa using h
  have arrange : D (stem ++ [p, t]) (rest ++ [p, p, t]) := by
    simpa [List.append_assoc] using prefixPermutation permutation p t
  have retarget : D (rest ++ [p, p, t]) ((rest ++ [p, p, p, p]) ++ [m, m, t]) := by
    simpa [List.append_assoc] using (retargetSquare rest p m member).append [t]
  refine ⟨rest ++ [p, p, p, p], arrange.trans retarget, ?_⟩
  intro z
  have support : z ∈ stem ↔ z ∈ rest ++ [p] := permutation.mem_iff
  simpa using support.symm

/-- If both terminal markers repeat, expose two squares and retarget the final
one. The resulting prefix contains the FULL support of the original word. -/
theorem bothRepeatedNormal (stem : List Nat) (p t m : Nat)
    (pRepeated : p ∈ stem ∨ p = t) (tRepeated : t ∈ stem ∨ t = p)
    (mMember : m ∈ stem ++ [p, t]) :
    ∃ pre, D (stem ++ [p, t]) (pre ++ [m, m]) ∧
      (∀ z, z ∈ pre ↔ z ∈ stem ++ [p, t]) := by
  by_cases equal : p = t
  · subst t
    have member : m ∈ stem ∨ m = p := by simpa using mMember
    refine ⟨stem ++ [p, p, p, p], retargetSquare stem p m member, ?_⟩
    intro z
    simp
  · have pMember : p ∈ stem := pRepeated.resolve_right equal
    have tMember : t ∈ stem := tRepeated.resolve_right (Ne.symm equal)
    obtain ⟨rest, permutation⟩ := permTailPair stem p t pMember tMember equal
    have wholePerm : (stem ++ [p, t]).Perm ((rest ++ [p, t]) ++ [p, t]) :=
      permutation.append_right [p, t]
    have support : ∀ z, z ∈ stem ++ [p, t] ↔ z ∈ rest ++ [p, p, t, t] := by
      intro z
      have h : z ∈ stem ++ [p, t] ↔ z ∈ (rest ++ [p, t]) ++ [p, t] := wholePerm.mem_iff
      simpa [List.mem_append, or_assoc, or_left_comm, or_comm] using h
    have member : m ∈ (rest ++ [p, p]) ∨ m = t := by
      have h := (support m).mp mMember
      simpa [List.mem_append, or_assoc] using h
    have arrange : D (stem ++ [p, t]) (rest ++ [p, t, p, t]) := by
      simpa [List.append_assoc] using prefixPermutation permutation p t
    have alternate : D (rest ++ [p, t, p, t]) (rest ++ [p, p, t, t]) :=
      (alternatingSquares p t).prepend rest
    have retarget : D (rest ++ [p, p, t, t])
        (((rest ++ [p, p]) ++ [t, t, t, t]) ++ [m, m]) := by
      simpa [List.append_assoc] using retargetSquare (rest ++ [p, p]) t m member
    refine ⟨(rest ++ [p, p]) ++ [t, t, t, t],
      arrange.trans (alternate.trans retarget), ?_⟩
    intro z
    have h := (support z).symm
    simpa [List.mem_append, or_assoc] using h

/-- Cancelling counts of a common literal suffix is arithmetic, not semigroup
cancellation. Both actual derivations still retain the suffix in full. -/
theorem alignCommonSuffix (left right leftPre rightPre tail : List Nat) (p t : Nat)
    (leftNormal : D left ((leftPre ++ [p, t]) ++ tail))
    (rightNormal : D right ((rightPre ++ [p, t]) ++ tail))
    (support : ∀ z, z ∈ leftPre ↔ z ∈ rightPre)
    (parity : ∀ z, left.count z % 2 = right.count z % 2) :
    D left right := by
  have prefixParity : ∀ z, leftPre.count z % 2 = rightPre.count z % 2 := by
    intro z
    have leftCounts := derivesParity leftNormal z
    have rightCounts := derivesParity rightNormal z
    have wholeCounts := parity z
    simp only [List.count_append] at leftCounts rightCounts
    omega
  exact leftNormal.trans (((prefixOfSupportParity leftPre rightPre p t support prefixParity).append tail).trans
    rightNormal.symm)

end SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section01.Section01TerminalForms
