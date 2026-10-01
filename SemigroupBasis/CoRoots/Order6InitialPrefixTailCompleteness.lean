import SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots
import SemigroupBasis.CoRoots.S5_530Normalization
import SemigroupBasis.CoRoots.S5_107ListDerives

/-!
Unrestricted packet-normal-form completeness for the nine O6F_0095 roots.

The proof deliberately separates three reusable layers:

* transport the `S5_530` first-occurrence block normalizer into the packet
  basis;
* cap every block at two copies and identify words modulo the first two
  globally-simple initial letters and a permutation of the remaining tail;
* recover exactly those invariants from the finite target by three literal
  separator valuations.

No bounded variable search or finite-projection completeness premise occurs in
the endpoint theorem.
-/

namespace SemigroupBasis.CoRoots.Order6InitialPrefixTailCompleteness

open SemigroupBasis

abbrev ListDerives : List Nat -> List Nat -> Prop :=
  S5_107.ListDerives SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.basis

private def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

/-! ## Transported first-occurrence block normalization -/

private theorem derivesS5Power :
    Derives SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.basis SemigroupBasis.CoRoots.S5_530.s5_530XXX SemigroupBasis.CoRoots.S5_530.s5_530XXXX := by
  have expanded :=
    Derives.prepend (Word.singleton 0) SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.derivesPowerLaw
  simpa [SemigroupBasis.CoRoots.S5_530.s5_530XXX, SemigroupBasis.CoRoots.S5_530.s5_530XXXX, SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.powerLaw,
    SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.xx, SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.xxx, Word.singleton, Word.append,
    Word.append_assoc] using expanded

private theorem derivesS5Gather :
    Derives SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.basis SemigroupBasis.CoRoots.S5_530.s5_530XXY SemigroupBasis.CoRoots.S5_530.s5_530XYX := by
  simpa [SemigroupBasis.CoRoots.S5_530.s5_530XXY, SemigroupBasis.CoRoots.S5_530.s5_530XYX, SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.xxy, SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.xyx] using
    SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.derivesGatherLaw.symm

private theorem s5AxiomDerives
    (identity : Identity Nat) (member : identity ∈ SemigroupBasis.CoRoots.S5_530.s5_530Basis) :
    Derives SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.basis identity.lhs identity.rhs := by
  simp only [SemigroupBasis.CoRoots.S5_530.s5_530Basis, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl
  · exact derivesS5Power
  · exact derivesS5Gather

/-! ## Cap-two block normal forms -/

/-- A flattened block list in which each label occurs in one block of length
one or two. -/
inductive CapNormal : List Nat -> Prop
  | nil : CapNormal []
  | single (label : Nat) (tail : List Nat) :
      CapNormal tail -> label ∉ tail -> CapNormal (label :: tail)
  | double (label : Nat) (tail : List Nat) :
      CapNormal tail -> label ∉ tail ->
        CapNormal (label :: label :: tail)

private theorem CapNormal.count_le_two
    {letters : List Nat} (normal : CapNormal letters) (label : Nat) :
    letters.count label ≤ 2 := by
  induction normal with
  | nil => simp
  | single head tail _ absent induction =>
      by_cases equal : label = head
      · subst label
        simp [List.count_eq_zero.mpr absent]
      · simpa [List.count_cons_of_ne (Ne.symm equal)] using induction
  | double head tail _ absent induction =>
      by_cases equal : label = head
      · subst label
        simp [List.count_eq_zero.mpr absent]
      · simpa [List.count_cons_of_ne (Ne.symm equal)] using induction

private theorem capS5Normal
    {letters : List Nat} (normal : SemigroupBasis.CoRoots.S5_530.S5_530Normal letters) :
    ∃ capped,
      CapNormal capped ∧
      ListDerives letters capped ∧
      (∀ label, label ∈ capped ↔ label ∈ letters) := by
  induction normal with
  | nil =>
      exact ⟨[], .nil, .empty, by simp⟩
  | single label tail _ absent induction =>
      obtain ⟨capped, cappedNormal, derives, support⟩ := induction
      have cappedAbsent : label ∉ capped := by
        intro member
        exact absent ((support label).mp member)
      refine ⟨label :: capped,
        .single label capped cappedNormal cappedAbsent, ?_, ?_⟩
      · simpa using derives.prepend [label]
      · intro tested
        simp only [List.mem_cons]
        rw [support tested]
  | double label tail _ absent induction =>
      obtain ⟨capped, cappedNormal, derives, support⟩ := induction
      have cappedAbsent : label ∉ capped := by
        intro member
        exact absent ((support label).mp member)
      refine ⟨label :: label :: capped,
        .double label capped cappedNormal cappedAbsent, ?_, ?_⟩
      · simpa using derives.prepend [label, label]
      · intro tested
        simp only [List.mem_cons]
        rw [support tested]
  | triple label tail _ absent induction =>
      obtain ⟨capped, cappedNormal, derives, support⟩ := induction
      have cappedAbsent : label ∉ capped := by
        intro member
        exact absent ((support label).mp member)
      have normalizedTail :
          ListDerives
            (label :: label :: label :: tail)
            (label :: label :: label :: capped) := by
        simpa using derives.prepend [label, label, label]
      have contracted :
          ListDerives
            (label :: label :: label :: capped)
            (label :: label :: capped) := by
        have base := S5_107.ListDerives.ofWord
          (SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.derivesThreeToTwo (Word.singleton label))
        simpa [Word.singleton, Word.append, Word.append_assoc] using
          base.append capped
      refine ⟨label :: label :: capped,
        .double label capped cappedNormal cappedAbsent,
        normalizedTail.trans contracted, ?_⟩
      intro tested
      simp [support tested]

/-- Every word reaches a cap-two first-occurrence block normal form. -/
theorem exists_capNormal (input : Word Nat) :
    ∃ head tail,
      CapNormal (head :: tail) ∧
      Derives SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.basis input (wordOfCons head tail) := by
  have sourceNormal := SemigroupBasis.CoRoots.S5_530.s5_530DerivesNormal input
  cases normalEq : SemigroupBasis.CoRoots.S5_530.s5_530NormalList input.toList with
  | nil =>
      rw [normalEq] at sourceNormal
      exact False.elim sourceNormal
  | cons normalHead normalTail =>
      rw [normalEq] at sourceNormal
      have packetNormal :
          Derives SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.basis input
            (SemigroupBasis.CoRoots.S5_530.s5_530WordOfCons normalHead normalTail) :=
        sourceNormal.transport s5AxiomDerives
      have normalProof :
          SemigroupBasis.CoRoots.S5_530.S5_530Normal (normalHead :: normalTail) := by
        rw [← normalEq]
        exact SemigroupBasis.CoRoots.S5_530.s5_530NormalList_normal input.toList
      obtain ⟨capped, cappedNormal, capDerivation, _⟩ :=
        capS5Normal normalProof
      have cappedNonempty : capped ≠ [] :=
        capDerivation.target_ne_nil
      cases capped with
      | nil => exact False.elim (cappedNonempty rfl)
      | cons head tail =>
          have capWordDerivation :
              Derives SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.basis
                (SemigroupBasis.CoRoots.S5_530.s5_530WordOfCons normalHead normalTail)
                (wordOfCons head tail) := by
            simpa [SemigroupBasis.CoRoots.S5_530.s5_530WordOfCons, wordOfCons] using
              S5_107.ListDerives.toWord capDerivation
          exact ⟨head, tail, cappedNormal,
            packetNormal.trans capWordDerivation⟩

/-! ## Permutations behind two protected nonempty prefixes -/

private theorem listDerivesSwapAfterTwo
    (first second : Nat) (prefixTail : List Nat)
    (left right : Nat) (suffix : List Nat) :
    ListDerives
      ((first :: second :: prefixTail) ++ left :: right :: suffix)
      ((first :: second :: prefixTail) ++ right :: left :: suffix) := by
  let secondPrefix := S5_107.listWordOfCons second prefixTail
  have swapped := SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.derivesTailSwap
    (Word.singleton first) secondPrefix
    (Word.singleton left) (Word.singleton right)
  have withSuffix :=
    (S5_107.ListDerives.ofWord swapped).append suffix
  simpa [secondPrefix, S5_107.listWordOfCons, Word.singleton,
    Word.append, List.append_assoc] using withSuffix

private theorem listDerivesPermutationAfterTwo
    (first second : Nat) (prefixTail : List Nat)
    {source target : List Nat} (permutation : source.Perm target) :
    ListDerives
      ((first :: second :: prefixTail) ++ source)
      ((first :: second :: prefixTail) ++ target) := by
  induction permutation generalizing prefixTail with
  | nil =>
      exact S5_107.ListDerives.refl _
  | cons head permutation induction =>
      simpa [List.append_assoc] using
        induction (prefixTail := prefixTail ++ [head])
  | swap left right suffix =>
      exact listDerivesSwapAfterTwo
        first second prefixTail right left suffix
  | trans firstPerm secondPerm firstInduction secondInduction =>
      exact (firstInduction prefixTail).trans
        (secondInduction prefixTail)

private theorem twoCopiesPerm
    (label : Nat) (letters : List Nat)
    (count : letters.count label = 2) :
    letters.Perm
      (label :: label :: (letters.erase label).erase label) := by
  have member : label ∈ letters :=
    List.count_pos_iff.mp (by omega)
  have first := List.perm_cons_erase member
  have erasedCount : (letters.erase label).count label = 1 := by
    rw [List.count_erase_self, count]
  have erasedMember : label ∈ letters.erase label :=
    List.count_pos_iff.mp (by omega)
  exact first.trans <|
    List.Perm.cons label (List.perm_cons_erase erasedMember)

private theorem countEraseTwiceSelf
    (label : Nat) (letters : List Nat)
    (count : letters.count label = 2) :
    ((letters.erase label).erase label).count label = 0 := by
  rw [List.count_erase_self, List.count_erase_self, count]

private theorem countEraseTwiceOfNe
    {removed tested : Nat} (different : tested ≠ removed)
    (letters : List Nat) :
    ((letters.erase removed).erase removed).count tested =
      letters.count tested := by
  rw [List.count_erase_of_ne different,
    List.count_erase_of_ne different]

/-! ## The protected-prefix quotient of cap-normal words -/

/-- The maximal initial globally-simple block, truncated after two letters,
for a cap-normal block list. The definition is total because it is also used
by the finite separator theorem before normality is supplied. -/
def protectedPrefix : List Nat -> List Nat
  | [] => []
  | [first] => [first]
  | first :: second :: [] =>
      if first = second then [] else [first, second]
  | first :: second :: third :: rest =>
      if first = second then []
      else if second = third then [first]
      else [first, second]

private theorem tailPermOfCommonPrefix
    (commonPrefix : List Nat) {left right : List Nat}
    (counts : ∀ label,
      (commonPrefix ++ left).count label =
        (commonPrefix ++ right).count label) :
    left.Perm right := by
  rw [List.perm_iff_count]
  intro label
  have equal := counts label
  simp only [List.count_append] at equal
  exact Nat.add_left_cancel equal

private theorem retargetInitialDouble
    (old new : Nat) (oldTail newTail : List Nat)
    (different : old ≠ new)
    (oldNormal : CapNormal oldTail)
    (oldAbsent : old ∉ oldTail)
    (newNormal : CapNormal newTail)
    (newAbsent : new ∉ newTail)
    (counts : ∀ label,
      (old :: old :: oldTail).count label =
        (new :: new :: newTail).count label) :
    ListDerives
      (old :: old :: oldTail)
      (new :: new :: newTail) := by
  have newCount : oldTail.count new = 2 := by
    have equal := counts new
    simp [different, Ne.symm different,
      List.count_eq_zero.mpr newAbsent] at equal
    omega
  let rest := (oldTail.erase new).erase new
  have expose : oldTail.Perm (new :: new :: rest) := by
    simpa [rest] using twoCopiesPerm new oldTail newCount
  have firstStep :=
    listDerivesPermutationAfterTwo old old [] expose
  have commute :=
    (S5_107.ListDerives.ofWord
      (SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.derivesSquareCommutation
        (Word.singleton old) (Word.singleton new))).append rest
  have commuteStep :
      ListDerives
        (old :: old :: new :: new :: rest)
        (new :: new :: old :: old :: rest) := by
    simpa [Word.singleton, Word.append, Word.append_assoc] using commute
  have postPerm : (old :: old :: rest).Perm newTail := by
    rw [List.perm_iff_count]
    intro tested
    by_cases testedNew : tested = new
    · subst tested
      simp [rest, different, Ne.symm different,
        countEraseTwiceSelf new oldTail newCount,
        List.count_eq_zero.mpr newAbsent]
    · have equal := counts tested
      rw [List.count_cons_of_ne (Ne.symm testedNew),
        List.count_cons_of_ne (Ne.symm testedNew)] at equal
      have restCount : rest.count tested = oldTail.count tested := by
        simpa [rest] using countEraseTwiceOfNe testedNew oldTail
      simpa only [List.count_cons, restCount] using equal
  have finalStep :=
    listDerivesPermutationAfterTwo new new [] postPerm
  exact firstStep.trans (commuteStep.trans finalStep)

private theorem retargetSecondDouble
    (guard old new : Nat) (oldTail newTail : List Nat)
    (different : old ≠ new)
    (oldNormal : CapNormal oldTail)
    (oldAbsent : old ∉ oldTail)
    (newNormal : CapNormal newTail)
    (newAbsent : new ∉ newTail)
    (counts : ∀ label,
      (guard :: old :: old :: oldTail).count label =
        (guard :: new :: new :: newTail).count label) :
    ListDerives
      (guard :: old :: old :: oldTail)
      (guard :: new :: new :: newTail) := by
  have tailCounts : ∀ label,
      (old :: old :: oldTail).count label =
        (new :: new :: newTail).count label :=
    List.perm_iff_count.mp
      (tailPermOfCommonPrefix [guard]
        (left := old :: old :: oldTail)
        (right := new :: new :: newTail) counts)
  have newCount : oldTail.count new = 2 := by
    simpa [different, List.count_eq_zero.mpr newAbsent] using
      tailCounts new
  let rest := (oldTail.erase new).erase new
  have expose : (old :: oldTail).Perm
      (old :: new :: new :: rest) :=
    List.Perm.cons old <| by
      simpa [rest] using twoCopiesPerm new oldTail newCount
  have firstStep :=
    listDerivesPermutationAfterTwo guard old [] expose
  have commute := Derives.prepend (Word.singleton guard) <|
    SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.derivesSquareCommutation
      (Word.singleton old) (Word.singleton new)
  have commuteStep :
      ListDerives
        (guard :: old :: old :: new :: new :: rest)
        (guard :: new :: new :: old :: old :: rest) := by
    have withRest := (S5_107.ListDerives.ofWord commute).append rest
    simpa [Word.singleton, Word.append, Word.append_assoc] using withRest
  have postPerm : (old :: old :: rest).Perm newTail := by
    rw [List.perm_iff_count]
    intro tested
    by_cases testedNew : tested = new
    · subst tested
      simp [rest, different, Ne.symm different,
        countEraseTwiceSelf new oldTail newCount,
        List.count_eq_zero.mpr newAbsent]
    · have equal := tailCounts tested
      rw [List.count_cons_of_ne (Ne.symm testedNew),
        List.count_cons_of_ne (Ne.symm testedNew)] at equal
      have restCount : rest.count tested = oldTail.count tested := by
        simpa [rest] using countEraseTwiceOfNe testedNew oldTail
      simpa only [List.count_cons, restCount] using equal
  have finalTail : (new :: old :: old :: rest).Perm
      (new :: newTail) := List.Perm.cons new postPerm
  have finalStep :=
    listDerivesPermutationAfterTwo guard new [] finalTail
  exact firstStep.trans (commuteStep.trans finalStep)

private theorem protectedPrefix_double
    (label : Nat) (tail : List Nat) :
    protectedPrefix (label :: label :: tail) = [] := by
  cases tail <;> simp [protectedPrefix]

private theorem protectedPrefix_single_single
    (first second : Nat) (tail : List Nat)
    (firstAbsent : first ∉ second :: tail)
    (secondAbsent : second ∉ tail) :
    protectedPrefix (first :: second :: tail) = [first, second] := by
  have firstNe : first ≠ second := by
    intro equal
    subst second
    exact firstAbsent (by simp)
  cases tail with
  | nil => simp [protectedPrefix, firstNe]
  | cons third rest =>
      have secondNe : second ≠ third := by
        intro equal
        subst third
        exact secondAbsent (by simp)
      simp [protectedPrefix, firstNe, secondNe]

private theorem protectedPrefix_single_double
    (first second : Nat) (tail : List Nat)
    (firstAbsent : first ∉ second :: second :: tail) :
    protectedPrefix (first :: second :: second :: tail) = [first] := by
  have firstNe : first ≠ second := by
    intro equal
    subst second
    exact firstAbsent (by simp)
  simp [protectedPrefix, firstNe]

private theorem protectedPrefix_single_head
    {first : Nat} {tail : List Nat}
    (tailNormal : CapNormal tail) (firstAbsent : first ∉ tail) :
    (protectedPrefix (first :: tail)).head? = some first := by
  cases tailNormal with
  | nil => simp [protectedPrefix]
  | single second rest _ secondAbsent =>
      rw [protectedPrefix_single_single first second rest
        firstAbsent secondAbsent]
      rfl
  | double second rest _ secondAbsent =>
      rw [protectedPrefix_single_double first second rest firstAbsent]
      rfl

/-- Cap-normal lists with equal multiplicities and equal protected prefixes
are derivably equal in the packet basis. -/
theorem capNormal_derives_of_invariants
    {left right : List Nat}
    (leftNormal : CapNormal left) (rightNormal : CapNormal right)
    (counts : ∀ label, left.count label = right.count label)
    (prefixEq : protectedPrefix left = protectedPrefix right) :
    ListDerives left right := by
  cases leftNormal with
  | nil =>
      cases rightNormal with
      | nil => exact .empty
      | single label tail _ absent =>
          have equal := counts label
          simp [List.count_eq_zero.mpr absent] at equal
      | double label tail _ absent =>
          have equal := counts label
          simp [List.count_eq_zero.mpr absent] at equal
  | double old oldTail oldNormal oldAbsent =>
      cases rightNormal with
      | nil =>
          have equal := counts old
          simp [List.count_eq_zero.mpr oldAbsent] at equal
      | single new newTail newNormal newAbsent =>
          have heads := congrArg List.head? prefixEq
          rw [protectedPrefix_double,
            protectedPrefix_single_head newNormal newAbsent] at heads
          simp at heads
      | double new newTail newNormal newAbsent =>
          by_cases equal : old = new
          · subst new
            have tailPerm := tailPermOfCommonPrefix [old, old] counts
            exact listDerivesPermutationAfterTwo old old [] tailPerm
          · exact retargetInitialDouble old new oldTail newTail equal
              oldNormal oldAbsent newNormal newAbsent counts
  | single first leftTail leftTailNormal firstAbsent =>
      cases rightNormal with
      | nil =>
          have equal := counts first
          simp [List.count_eq_zero.mpr firstAbsent] at equal
      | double label tail tailNormal absent =>
          have heads := congrArg List.head? prefixEq
          rw [protectedPrefix_single_head leftTailNormal firstAbsent,
            protectedPrefix_double] at heads
          simp at heads
      | single second rightTail rightTailNormal secondAbsent =>
          have firstEq : first = second := by
            have heads := congrArg List.head? prefixEq
            rw [protectedPrefix_single_head leftTailNormal firstAbsent,
              protectedPrefix_single_head rightTailNormal secondAbsent]
              at heads
            simpa using heads
          subst second
          cases leftTailNormal with
          | nil =>
              cases rightTailNormal with
              | nil => exact S5_107.ListDerives.refl _
              | single rightNext rightRest rightRestNormal rightNextAbsent =>
                  have rightNextNe : rightNext ≠ first := by
                    intro equal
                    subst rightNext
                    exact secondAbsent (by simp)
                  have equal := counts rightNext
                  simp [rightNextNe, Ne.symm rightNextNe,
                    List.count_eq_zero.mpr rightNextAbsent] at equal
              | double rightNext rightRest rightRestNormal rightNextAbsent =>
                  have rightNextNe : rightNext ≠ first := by
                    intro equal
                    subst rightNext
                    exact secondAbsent (by simp)
                  have equal := counts rightNext
                  simp [rightNextNe, Ne.symm rightNextNe,
                    List.count_eq_zero.mpr rightNextAbsent] at equal
          | single leftNext leftRest leftRestNormal leftNextAbsent =>
              cases rightTailNormal with
              | nil =>
                  have leftNextNe : leftNext ≠ first := by
                    intro equal
                    subst leftNext
                    exact firstAbsent (by simp)
                  have equal := counts leftNext
                  simp [leftNextNe, Ne.symm leftNextNe,
                    List.count_eq_zero.mpr leftNextAbsent] at equal
              | single rightNext rightRest rightRestNormal rightNextAbsent =>
                  have secondEq : leftNext = rightNext := by
                    rw [protectedPrefix_single_single first leftNext leftRest
                        firstAbsent leftNextAbsent,
                      protectedPrefix_single_single first rightNext rightRest
                        secondAbsent rightNextAbsent] at prefixEq
                    exact (List.cons.inj (List.cons.inj prefixEq).2).1
                  subst rightNext
                  have tailPerm :=
                    tailPermOfCommonPrefix [first, leftNext] counts
                  exact listDerivesPermutationAfterTwo
                    first leftNext [] tailPerm
              | double rightNext rightRest rightRestNormal rightNextAbsent =>
                  rw [protectedPrefix_single_single first leftNext leftRest
                      firstAbsent leftNextAbsent,
                    protectedPrefix_single_double first rightNext rightRest
                      secondAbsent] at prefixEq
                  simp at prefixEq
          | double old oldTail oldNormal oldAbsent =>
              cases rightTailNormal with
              | nil =>
                  have oldNe : old ≠ first := by
                    intro equal
                    subst old
                    exact firstAbsent (by simp)
                  have equal := counts old
                  simp [oldNe, Ne.symm oldNe,
                    List.count_eq_zero.mpr oldAbsent] at equal
              | single rightNext rightRest rightRestNormal rightNextAbsent =>
                  rw [protectedPrefix_single_double first old oldTail
                      firstAbsent,
                    protectedPrefix_single_single first rightNext rightRest
                      secondAbsent rightNextAbsent] at prefixEq
                  simp at prefixEq
              | double new newTail newNormal newAbsent =>
                  by_cases equal : old = new
                  · subst new
                    have tailPerm :=
                      tailPermOfCommonPrefix [first, old, old] counts
                    have lifted :=
                      listDerivesPermutationAfterTwo first old [old]
                        tailPerm
                    simpa [List.append_assoc] using lifted
                  · exact retargetSecondDouble first old new
                      oldTail newTail equal oldNormal oldAbsent
                      newNormal newAbsent counts

/-! ## Finite separator contract -/

/-- The concrete transition equations required from an opposite-oriented
order-six target. -/
structure SeparatorContract (candidate : Semigroup (Fin 6)) where
  capSelected : Fin 6
  secondHead : Fin 6
  secondSelected : Fin 6
  secondFiller : Fin 6
  secondAfterImmediate : Fin 6
  secondAfterLate : Fin 6
  secondAfterFiller : Fin 6
  capSelected_ne_absent : capSelected ≠ 5
  capSelected_ne_repeated : capSelected ≠ 0
  cap_absent_filler : candidate.mul 5 5 = 5
  cap_single_filler : candidate.mul capSelected 5 = capSelected
  cap_repeated_filler : candidate.mul 0 5 = 0
  cap_absent_selected : candidate.mul 5 capSelected = capSelected
  cap_single_selected : candidate.mul capSelected capSelected = 0
  cap_repeated_selected : candidate.mul 0 capSelected = 0
  head_filler_filler : candidate.mul 5 5 = 5
  head_selected_filler : candidate.mul 1 5 = 1
  head_filler_selected : candidate.mul 5 1 = 0
  head_late_filler : candidate.mul 0 5 = 0
  second_filler_filler : candidate.mul secondFiller secondFiller = secondFiller
  second_head_filler : candidate.mul secondHead secondFiller = secondAfterFiller
  second_after_filler_filler :
    candidate.mul secondAfterFiller secondFiller = secondAfterFiller
  second_head_selected :
    candidate.mul secondHead secondSelected = secondAfterImmediate
  second_after_filler_selected :
    candidate.mul secondAfterFiller secondSelected = secondAfterLate
  second_immediate_filler :
    candidate.mul secondAfterImmediate secondFiller = secondAfterImmediate
  second_late_filler :
    candidate.mul secondAfterLate secondFiller = secondAfterLate
  second_outputs_ne : secondAfterImmediate ≠ secondAfterLate

namespace SeparatorContract

private def capCode
    {candidate : Semigroup (Fin 6)}
    (contract : SeparatorContract candidate) : Nat -> Fin 6
  | 0 => 5
  | 1 => contract.capSelected
  | _ + 2 => 0

private def capValuation
    {candidate : Semigroup (Fin 6)}
    (contract : SeparatorContract candidate)
    (selected : Nat) : Nat -> Fin 6 :=
  fun value => if value = selected then contract.capSelected else 5

private theorem capStep
    {candidate : Semigroup (Fin 6)}
    (contract : SeparatorContract candidate)
    (selected value count : Nat) :
    candidate.mul (contract.capCode count)
        (contract.capValuation selected value) =
      contract.capCode
        (count + if value = selected then 1 else 0) := by
  by_cases equal : value = selected
  · subst value
    simp only [capValuation, if_pos]
    cases count with
    | zero => exact contract.cap_absent_selected
    | succ count =>
        cases count with
        | zero => exact contract.cap_single_selected
        | succ count => exact contract.cap_repeated_selected
  · simp only [capValuation, if_neg equal, Nat.add_zero]
    cases count with
    | zero => exact contract.cap_absent_filler
    | succ count =>
        cases count with
        | zero => exact contract.cap_single_filler
        | succ count => exact contract.cap_repeated_filler

private theorem capFold
    {candidate : Semigroup (Fin 6)}
    (contract : SeparatorContract candidate) (selected : Nat) :
    ∀ (letters : List Nat) (count : Nat),
      letters.foldl
          (fun state value =>
            candidate.mul state (contract.capValuation selected value))
          (contract.capCode count) =
        contract.capCode (count + letters.count selected)
  | [], count => by simp
  | value :: rest, count => by
      rw [List.foldl_cons, contract.capStep selected value count,
        contract.capFold selected rest]
      by_cases equal : value = selected
      · subst value
        simp [List.count_cons_self, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm]
      · simp [equal, List.count_cons_of_ne equal]

theorem eval_capValuation
    {candidate : Semigroup (Fin 6)}
    (contract : SeparatorContract candidate)
    (selected : Nat) (word : Word Nat) :
    candidate.eval (contract.capValuation selected) word =
      contract.capCode (word.toList.count selected) := by
  cases word with
  | mk head tail =>
      unfold Semigroup.eval
      by_cases equal : head = selected
      · subst head
        rw [show contract.capValuation selected selected =
            contract.capCode 1 by simp [capValuation, capCode],
          contract.capFold selected tail 1]
        simp [Word.toList, Nat.add_comm]
      · rw [show contract.capValuation selected head =
            contract.capCode 0 by simp [capValuation, capCode, equal],
          contract.capFold selected tail 0]
        simp [Word.toList, equal]

private theorem capCode_injective_of_le_two
    {candidate : Semigroup (Fin 6)}
    (contract : SeparatorContract candidate)
    {left right : Nat} (leftBound : left ≤ 2) (rightBound : right ≤ 2)
    (equal : contract.capCode left = contract.capCode right) :
    left = right := by
  have leftCases : left = 0 ∨ left = 1 ∨ left = 2 := by omega
  have rightCases : right = 0 ∨ right = 1 ∨ right = 2 := by omega
  rcases leftCases with rfl | rfl | rfl <;>
    rcases rightCases with rfl | rfl | rfl <;>
    simp only [capCode] at equal ⊢
  · exact False.elim (contract.capSelected_ne_absent equal.symm)
  · exact False.elim ((by decide : (5 : Fin 6) ≠ 0) equal)
  · exact False.elim (contract.capSelected_ne_absent equal)
  · exact False.elim (contract.capSelected_ne_repeated equal)
  · exact False.elim ((by decide : (0 : Fin 6) ≠ 5) equal)
  · exact False.elim (contract.capSelected_ne_repeated equal.symm)

theorem valid_counts_eq
    {candidate : Semigroup (Fin 6)}
    (contract : SeparatorContract candidate)
    {left right : Word Nat}
    (leftNormal : CapNormal left.toList)
    (rightNormal : CapNormal right.toList)
    (valid : ∀ valuation : Nat -> Fin 6,
      candidate.eval valuation left = candidate.eval valuation right) :
    ∀ label, left.toList.count label = right.toList.count label := by
  intro label
  have evaluated := valid (contract.capValuation label)
  rw [contract.eval_capValuation, contract.eval_capValuation] at evaluated
  exact contract.capCode_injective_of_le_two
    (leftNormal.count_le_two label) (rightNormal.count_le_two label)
    evaluated

private theorem exists_unique_split
    (selected : Nat) : ∀ letters : List Nat,
    letters.count selected = 1 ->
      ∃ before after,
        letters = before ++ selected :: after ∧
        selected ∉ before ∧ selected ∉ after
  | [], count => by simp at count
  | value :: rest, count => by
      by_cases equal : value = selected
      · subst value
        have restCount : rest.count selected = 0 := by
          simp only [List.count_cons_self] at count
          omega
        exact ⟨[], rest, by simp, by simp,
          List.count_eq_zero.mp restCount⟩
      · have restCount : rest.count selected = 1 := by
          simpa [List.count_cons_of_ne equal] using count
        obtain ⟨before, after, shape, beforeAbsent, afterAbsent⟩ :=
          exists_unique_split selected rest restCount
        refine ⟨value :: before, after, ?_, ?_, afterAbsent⟩
        · simp [shape]
        · simp [Ne.symm equal, beforeAbsent]

private def headValuation (selected : Nat) : Nat -> Fin 6 :=
  fun value => if value = selected then 1 else 5

private theorem foldHeadSelected
    {candidate : Semigroup (Fin 6)}
    (contract : SeparatorContract candidate) (selected : Nat) :
    ∀ letters : List Nat, selected ∉ letters ->
      letters.foldl
          (fun state value =>
            candidate.mul state (headValuation selected value)) 1 = 1
  | [], _ => rfl
  | value :: rest, absent => by
      have valueNe : value ≠ selected := by
        intro equal
        subst value
        exact absent (by simp)
      have restAbsent : selected ∉ rest := by
        exact fun member => absent (by simp [member])
      rw [List.foldl_cons]
      simp only [headValuation, if_neg valueNe]
      rw [contract.head_selected_filler]
      exact contract.foldHeadSelected selected rest restAbsent

private theorem foldHeadFiller
    {candidate : Semigroup (Fin 6)}
    (contract : SeparatorContract candidate) (selected : Nat) :
    ∀ letters : List Nat, selected ∉ letters ->
      letters.foldl
          (fun state value =>
            candidate.mul state (headValuation selected value)) 5 = 5
  | [], _ => rfl
  | value :: rest, absent => by
      have valueNe : value ≠ selected := by
        intro equal
        subst value
        exact absent (by simp)
      have restAbsent : selected ∉ rest := by
        exact fun member => absent (by simp [member])
      rw [List.foldl_cons]
      simp only [headValuation, if_neg valueNe]
      rw [contract.head_filler_filler]
      exact contract.foldHeadFiller selected rest restAbsent

private theorem foldHeadLate
    {candidate : Semigroup (Fin 6)}
    (contract : SeparatorContract candidate) (selected : Nat) :
    ∀ letters : List Nat, selected ∉ letters ->
      letters.foldl
          (fun state value =>
            candidate.mul state (headValuation selected value)) 0 = 0
  | [], _ => rfl
  | value :: rest, absent => by
      have valueNe : value ≠ selected := by
        intro equal
        subst value
        exact absent (by simp)
      have restAbsent : selected ∉ rest := by
        exact fun member => absent (by simp [member])
      rw [List.foldl_cons]
      simp only [headValuation, if_neg valueNe]
      rw [contract.head_late_filler]
      exact contract.foldHeadLate selected rest restAbsent

theorem eval_headValuation_of_simple
    {candidate : Semigroup (Fin 6)}
    (contract : SeparatorContract candidate)
    (selected : Nat) (word : Word Nat)
    (simple : word.toList.count selected = 1) :
    candidate.eval (headValuation selected) word =
      if word.head = selected then 1 else 0 := by
  cases word with
  | mk head tail =>
      by_cases headEq : head = selected
      · subst head
        have tailCount : tail.count selected = 0 := by
          simp only [Word.toList, List.count_cons_self] at simple
          omega
        have tailAbsent := List.count_eq_zero.mp tailCount
        simp only [if_pos]
        change tail.foldl
          (fun state value =>
            candidate.mul state (headValuation selected value))
          (headValuation selected selected) = 1
        rw [show headValuation selected selected = (1 : Fin 6) by
          simp [headValuation]]
        exact contract.foldHeadSelected selected tail tailAbsent
      · have tailCount : tail.count selected = 1 := by
          simpa [Word.toList, List.count_cons_of_ne headEq] using simple
        obtain ⟨before, after, shape, beforeAbsent, afterAbsent⟩ :=
          exists_unique_split selected tail tailCount
        simp only [if_neg headEq]
        change tail.foldl
          (fun state value =>
            candidate.mul state (headValuation selected value))
          (headValuation selected head) = 0
        rw [show headValuation selected head = (5 : Fin 6) by
          simp [headValuation, headEq], shape, List.foldl_append,
          contract.foldHeadFiller selected before beforeAbsent,
          List.foldl_cons]
        rw [show headValuation selected selected = (1 : Fin 6) by
          simp [headValuation], contract.head_filler_selected]
        exact contract.foldHeadLate selected after afterAbsent

private def secondValuation
    {candidate : Semigroup (Fin 6)}
    (contract : SeparatorContract candidate)
    (head selected : Nat) : Nat -> Fin 6 :=
  fun value =>
    if value = head then contract.secondHead
    else if value = selected then contract.secondSelected
    else contract.secondFiller

private theorem secondValuation_eq_filler
    {candidate : Semigroup (Fin 6)}
    (contract : SeparatorContract candidate)
    {head selected value : Nat}
    (headNe : value ≠ head) (selectedNe : value ≠ selected) :
    contract.secondValuation head selected value =
      contract.secondFiller := by
  simp [secondValuation, headNe, selectedNe]

private theorem foldSecondAfterFiller
    {candidate : Semigroup (Fin 6)}
    (contract : SeparatorContract candidate)
    (head selected : Nat) :
    ∀ letters : List Nat,
      (∀ value ∈ letters, value ≠ head ∧ value ≠ selected) ->
      letters.foldl
          (fun state value => candidate.mul state
            (contract.secondValuation head selected value))
          contract.secondAfterFiller = contract.secondAfterFiller
  | [], _ => rfl
  | value :: rest, onlyFiller => by
      have valueOther := onlyFiller value (by simp)
      have restOther :
          ∀ tested ∈ rest, tested ≠ head ∧ tested ≠ selected := by
        intro tested member
        exact onlyFiller tested (by simp [member])
      rw [List.foldl_cons,
        contract.secondValuation_eq_filler valueOther.1 valueOther.2,
        contract.second_after_filler_filler]
      exact contract.foldSecondAfterFiller head selected rest restOther

private theorem foldSecondImmediate
    {candidate : Semigroup (Fin 6)}
    (contract : SeparatorContract candidate)
    (head selected : Nat) :
    ∀ letters : List Nat,
      (∀ value ∈ letters, value ≠ head ∧ value ≠ selected) ->
      letters.foldl
          (fun state value => candidate.mul state
            (contract.secondValuation head selected value))
          contract.secondAfterImmediate = contract.secondAfterImmediate
  | [], _ => rfl
  | value :: rest, onlyFiller => by
      have valueOther := onlyFiller value (by simp)
      have restOther :
          ∀ tested ∈ rest, tested ≠ head ∧ tested ≠ selected := by
        intro tested member
        exact onlyFiller tested (by simp [member])
      rw [List.foldl_cons,
        contract.secondValuation_eq_filler valueOther.1 valueOther.2,
        contract.second_immediate_filler]
      exact contract.foldSecondImmediate head selected rest restOther

private theorem foldSecondLate
    {candidate : Semigroup (Fin 6)}
    (contract : SeparatorContract candidate)
    (head selected : Nat) :
    ∀ letters : List Nat,
      (∀ value ∈ letters, value ≠ head ∧ value ≠ selected) ->
      letters.foldl
          (fun state value => candidate.mul state
            (contract.secondValuation head selected value))
          contract.secondAfterLate = contract.secondAfterLate
  | [], _ => rfl
  | value :: rest, onlyFiller => by
      have valueOther := onlyFiller value (by simp)
      have restOther :
          ∀ tested ∈ rest, tested ≠ head ∧ tested ≠ selected := by
        intro tested member
        exact onlyFiller tested (by simp [member])
      rw [List.foldl_cons,
        contract.secondValuation_eq_filler valueOther.1 valueOther.2,
        contract.second_late_filler]
      exact contract.foldSecondLate head selected rest restOther

private theorem foldSecondHeadNonempty
    {candidate : Semigroup (Fin 6)}
    (contract : SeparatorContract candidate)
    (head selected : Nat) {letters : List Nat}
    (nonempty : letters ≠ [])
    (onlyFiller :
      ∀ value ∈ letters, value ≠ head ∧ value ≠ selected) :
    letters.foldl
        (fun state value => candidate.mul state
          (contract.secondValuation head selected value))
        contract.secondHead = contract.secondAfterFiller := by
  cases letters with
  | nil => exact False.elim (nonempty rfl)
  | cons value rest =>
      have valueOther := onlyFiller value (by simp)
      have restOther :
          ∀ tested ∈ rest, tested ≠ head ∧ tested ≠ selected := by
        intro tested member
        exact onlyFiller tested (by simp [member])
      rw [List.foldl_cons,
        contract.secondValuation_eq_filler valueOther.1 valueOther.2,
        contract.second_head_filler]
      exact contract.foldSecondAfterFiller head selected rest restOther

theorem eval_secondValuation_of_simple
    {candidate : Semigroup (Fin 6)}
    (contract : SeparatorContract candidate)
    (head selected : Nat) (word : Word Nat)
    (wordHead : word.head = head)
    (different : head ≠ selected)
    (headSimple : word.toList.count head = 1)
    (selectedSimple : word.toList.count selected = 1) :
    candidate.eval (contract.secondValuation head selected) word =
      if word.tail.head? = some selected then
        contract.secondAfterImmediate
      else contract.secondAfterLate := by
  cases word with
  | mk actualHead tail =>
      simp only at wordHead
      subst actualHead
      have headTailCount : tail.count head = 0 := by
        simp only [Word.toList, List.count_cons_self] at headSimple
        omega
      have headTailAbsent : head ∉ tail :=
        List.count_eq_zero.mp headTailCount
      have selectedTailCount : tail.count selected = 1 := by
        rw [Word.toList, List.count_cons_of_ne different] at selectedSimple
        exact selectedSimple
      cases tail with
      | nil => simp at selectedTailCount
      | cons first rest =>
          by_cases firstEq : first = selected
          · subst first
            have restSelectedCount : rest.count selected = 0 := by
              simp only [List.count_cons_self] at selectedTailCount
              omega
            have restSelectedAbsent : selected ∉ rest :=
              List.count_eq_zero.mp restSelectedCount
            have restOther :
                ∀ value ∈ rest, value ≠ head ∧ value ≠ selected := by
              intro value member
              refine ⟨?_, ?_⟩
              · intro equal
                subst value
                exact headTailAbsent (by simp [member])
              · intro equal
                subst value
                exact restSelectedAbsent member
            simp only [List.head?_cons, if_pos]
            change (selected :: rest).foldl
              (fun state value => candidate.mul state
                (contract.secondValuation head selected value))
              (contract.secondValuation head selected head) =
                contract.secondAfterImmediate
            rw [show contract.secondValuation head selected head =
                contract.secondHead by
                  simp [secondValuation],
              List.foldl_cons,
              show contract.secondValuation head selected selected =
                  contract.secondSelected by
                simp [secondValuation, Ne.symm different],
              contract.second_head_selected]
            exact contract.foldSecondImmediate head selected rest restOther
          · obtain ⟨before, after, shape, beforeSelectedAbsent,
                afterSelectedAbsent⟩ :=
              exists_unique_split selected (first :: rest)
                selectedTailCount
            have beforeNonempty : before ≠ [] := by
              intro empty
              subst before
              simp only [List.nil_append, List.cons.injEq] at shape
              exact firstEq shape.1
            have beforeOther :
                ∀ value ∈ before, value ≠ head ∧ value ≠ selected := by
              intro value member
              refine ⟨?_, ?_⟩
              · intro equal
                subst value
                exact headTailAbsent <| by
                  rw [shape]
                  simp [member]
              · intro equal
                subst value
                exact beforeSelectedAbsent member
            have afterOther :
                ∀ value ∈ after, value ≠ head ∧ value ≠ selected := by
              intro value member
              refine ⟨?_, ?_⟩
              · intro equal
                subst value
                exact headTailAbsent <| by
                  rw [shape]
                  simp [member]
              · intro equal
                subst value
                exact afterSelectedAbsent member
            have headOptionNe : some first ≠ some selected := by
              simpa using firstEq
            simp only [List.head?_cons, if_neg headOptionNe]
            change (first :: rest).foldl
              (fun state value => candidate.mul state
                (contract.secondValuation head selected value))
              (contract.secondValuation head selected head) =
                contract.secondAfterLate
            rw [show contract.secondValuation head selected head =
                contract.secondHead by simp [secondValuation],
              shape, List.foldl_append,
              contract.foldSecondHeadNonempty head selected
                (letters := before) beforeNonempty beforeOther,
              List.foldl_cons,
              show contract.secondValuation head selected selected =
                  contract.secondSelected by
                simp [secondValuation, Ne.symm different],
              contract.second_after_filler_selected]
            exact contract.foldSecondLate head selected after afterOther

private theorem simpleHeadsEq
    {candidate : Semigroup (Fin 6)}
    (contract : SeparatorContract candidate)
    (left right : Word Nat)
    (valid : ∀ valuation : Nat -> Fin 6,
      candidate.eval valuation left = candidate.eval valuation right)
    (counts : ∀ label,
      left.toList.count label = right.toList.count label)
    (leftSimple : left.toList.count left.head = 1)
    (rightSimple : right.toList.count right.head = 1) :
    left.head = right.head := by
  have rightCount : right.toList.count left.head = 1 := by
    rw [← counts left.head]
    exact leftSimple
  have evaluated := valid (headValuation left.head)
  rw [contract.eval_headValuation_of_simple left.head left leftSimple,
    contract.eval_headValuation_of_simple left.head right rightCount]
    at evaluated
  apply Decidable.byContradiction
  intro different
  simp [different, Ne.symm different] at evaluated

private theorem simpleSecondEq
    {candidate : Semigroup (Fin 6)}
    (contract : SeparatorContract candidate)
    (head selected : Nat) (left right : Word Nat)
    (valid : ∀ valuation : Nat -> Fin 6,
      candidate.eval valuation left = candidate.eval valuation right)
    (heads : left.head = head ∧ right.head = head)
    (different : head ≠ selected)
    (leftHeadSimple : left.toList.count head = 1)
    (rightHeadSimple : right.toList.count head = 1)
    (leftSelectedSimple : left.toList.count selected = 1)
    (rightSelectedSimple : right.toList.count selected = 1)
    (leftSecond : left.tail.head? = some selected) :
    right.tail.head? = some selected := by
  have evaluated := valid (contract.secondValuation head selected)
  rw [contract.eval_secondValuation_of_simple head selected left
      heads.1 different leftHeadSimple leftSelectedSimple,
    contract.eval_secondValuation_of_simple head selected right
      heads.2 different rightHeadSimple rightSelectedSimple,
    leftSecond, if_pos rfl] at evaluated
  apply Decidable.byContradiction
  intro rightSecond
  rw [if_neg rightSecond] at evaluated
  exact contract.second_outputs_ne evaluated

theorem valid_protectedPrefix_eq
    {candidate : Semigroup (Fin 6)}
    (contract : SeparatorContract candidate)
    (left right : Word Nat)
    (leftNormal : CapNormal left.toList)
    (rightNormal : CapNormal right.toList)
    (valid : ∀ valuation : Nat -> Fin 6,
      candidate.eval valuation left = candidate.eval valuation right) :
    protectedPrefix left.toList = protectedPrefix right.toList := by
  have counts := contract.valid_counts_eq leftNormal rightNormal valid
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simp only [Word.toList] at leftNormal rightNormal counts ⊢
          cases leftNormal with
          | single leftHead leftTail leftTailNormal leftAbsent =>
              cases rightNormal with
              | single rightHead rightTail rightTailNormal rightAbsent =>
                  have leftSimple :
                      (leftHead :: leftTail).count leftHead = 1 := by
                    simp [List.count_eq_zero.mpr leftAbsent]
                  have rightSimple :
                      (rightHead :: rightTail).count rightHead = 1 := by
                    simp [List.count_eq_zero.mpr rightAbsent]
                  have heads : leftHead = rightHead :=
                    contract.simpleHeadsEq
                      (wordOfCons leftHead leftTail)
                      (wordOfCons rightHead rightTail) valid counts
                      leftSimple rightSimple
                  subst rightHead
                  cases leftTailNormal with
                  | nil =>
                      cases rightTailNormal with
                      | nil => rfl
                      | single next tail tailNormal nextAbsent =>
                          have nextNe : next ≠ leftHead := by
                            intro equal
                            subst next
                            exact rightAbsent (by simp)
                          have equal := counts next
                          simp [nextNe, Ne.symm nextNe,
                            List.count_eq_zero.mpr nextAbsent] at equal
                      | double next tail tailNormal nextAbsent =>
                          have nextNe : next ≠ leftHead := by
                            intro equal
                            subst next
                            exact rightAbsent (by simp)
                          have equal := counts next
                          simp [nextNe, Ne.symm nextNe,
                            List.count_eq_zero.mpr nextAbsent] at equal
                  | single leftSecond leftRest leftRestNormal leftSecondAbsent =>
                      have leftSecondNe : leftHead ≠ leftSecond := by
                        intro equal
                        subst leftSecond
                        exact leftAbsent (by simp)
                      have leftSecondSimple :
                          (leftHead :: leftSecond :: leftRest).count
                              leftSecond = 1 := by
                        simp [leftSecondNe,
                          List.count_eq_zero.mpr leftSecondAbsent]
                      have rightSecondSimple :
                          (leftHead :: rightTail).count leftSecond = 1 := by
                        rw [← counts leftSecond]
                        exact leftSecondSimple
                      cases rightTailNormal with
                      | nil =>
                          have equal := counts leftSecond
                          simp [leftSecondNe, Ne.symm leftSecondNe,
                            List.count_eq_zero.mpr leftSecondAbsent] at equal
                      | single rightSecond rightRest rightRestNormal rightSecondAbsent =>
                          have validWords :
                              ∀ valuation,
                                candidate.eval valuation
                                    (wordOfCons leftHead
                                      (leftSecond :: leftRest)) =
                                  candidate.eval valuation
                                    (wordOfCons leftHead
                                      (rightSecond :: rightRest)) := by
                            intro valuation
                            exact valid valuation
                          have leftSecondAtHead :
                              (wordOfCons leftHead
                                (leftSecond :: leftRest)).tail.head? =
                                  some leftSecond := rfl
                          have secondEq : rightSecond = leftSecond := by
                            have detected := contract.simpleSecondEq
                              leftHead leftSecond
                              (wordOfCons leftHead (leftSecond :: leftRest))
                              (wordOfCons leftHead (rightSecond :: rightRest))
                              validWords ⟨rfl, rfl⟩ leftSecondNe
                              leftSimple rightSimple leftSecondSimple
                              rightSecondSimple leftSecondAtHead
                            change some rightSecond = some leftSecond at detected
                            exact Option.some.inj detected
                          subst rightSecond
                          exact (protectedPrefix_single_single
                            leftHead leftSecond leftRest leftAbsent
                              leftSecondAbsent).trans <|
                            (protectedPrefix_single_single
                              leftHead leftSecond rightRest rightAbsent
                                rightSecondAbsent).symm
                      | double rightSecond rightRest rightRestNormal rightSecondAbsent =>
                          have validWords :
                              ∀ valuation,
                                candidate.eval valuation
                                    (wordOfCons leftHead
                                      (leftSecond :: leftRest)) =
                                  candidate.eval valuation
                                    (wordOfCons leftHead
                                      (rightSecond :: rightSecond ::
                                        rightRest)) := by
                            intro valuation
                            exact valid valuation
                          have leftSecondAtHead :
                              (wordOfCons leftHead
                                (leftSecond :: leftRest)).tail.head? =
                                  some leftSecond := rfl
                          have detected := contract.simpleSecondEq
                            leftHead leftSecond
                            (wordOfCons leftHead (leftSecond :: leftRest))
                            (wordOfCons leftHead
                              (rightSecond :: rightSecond :: rightRest))
                            validWords ⟨rfl, rfl⟩ leftSecondNe
                            leftSimple rightSimple leftSecondSimple
                            rightSecondSimple leftSecondAtHead
                          have secondEq : rightSecond = leftSecond := by
                            change some rightSecond = some leftSecond at detected
                            exact Option.some.inj detected
                          subst rightSecond
                          have equal := counts leftSecond
                          simp [leftSecondNe, Ne.symm leftSecondNe,
                            List.count_eq_zero.mpr leftSecondAbsent,
                            List.count_eq_zero.mpr rightSecondAbsent] at equal
                  | double leftSecond leftRest leftRestNormal leftSecondAbsent =>
                      cases rightTailNormal with
                      | nil =>
                          have leftSecondNe : leftSecond ≠ leftHead := by
                            intro equal
                            subst leftSecond
                            exact leftAbsent (by simp)
                          have equal := counts leftSecond
                          simp [leftSecondNe, Ne.symm leftSecondNe,
                            List.count_eq_zero.mpr leftSecondAbsent] at equal
                      | single rightSecond rightRest rightRestNormal rightSecondAbsent =>
                          have rightSecondNe : leftHead ≠ rightSecond := by
                            intro equal
                            subst rightSecond
                            exact rightAbsent (by simp)
                          have rightSecondSimple :
                              (leftHead :: rightSecond :: rightRest).count
                                  rightSecond = 1 := by
                            simp [rightSecondNe,
                              List.count_eq_zero.mpr rightSecondAbsent]
                          have leftRightSecondSimple :
                              (leftHead :: leftSecond :: leftSecond ::
                                leftRest).count rightSecond = 1 := by
                            rw [counts rightSecond]
                            exact rightSecondSimple
                          have validWords :
                              ∀ valuation,
                                candidate.eval valuation
                                    (wordOfCons leftHead
                                      (rightSecond :: rightRest)) =
                                  candidate.eval valuation
                                    (wordOfCons leftHead
                                      (leftSecond :: leftSecond ::
                                        leftRest)) := by
                            intro valuation
                            exact (valid valuation).symm
                          have rightSecondAtHead :
                              (wordOfCons leftHead
                                (rightSecond :: rightRest)).tail.head? =
                                  some rightSecond := rfl
                          have detected := contract.simpleSecondEq
                            leftHead rightSecond
                            (wordOfCons leftHead
                              (rightSecond :: rightRest))
                            (wordOfCons leftHead
                              (leftSecond :: leftSecond :: leftRest))
                            validWords
                            ⟨rfl, rfl⟩ rightSecondNe
                            rightSimple leftSimple rightSecondSimple
                            leftRightSecondSimple rightSecondAtHead
                          have secondEq : leftSecond = rightSecond := by
                            change some leftSecond = some rightSecond at detected
                            exact Option.some.inj detected
                          subst rightSecond
                          have equal := counts leftSecond
                          simp [rightSecondNe, Ne.symm rightSecondNe,
                            List.count_eq_zero.mpr leftSecondAbsent,
                            List.count_eq_zero.mpr rightSecondAbsent] at equal
                      | double rightSecond rightRest rightRestNormal rightSecondAbsent =>
                          exact (protectedPrefix_single_double
                            leftHead leftSecond leftRest leftAbsent).trans <|
                            (protectedPrefix_single_double
                              leftHead rightSecond rightRest rightAbsent).symm
              | double rightHead rightTail rightTailNormal rightAbsent =>
                  have rightRepeated :
                      (rightHead :: rightHead :: rightTail).count rightHead = 2 := by
                    simp [List.count_eq_zero.mpr rightAbsent]
                  have leftRightHeadCount :
                      (leftHead :: leftTail).count rightHead = 2 := by
                    rw [counts rightHead]
                    exact rightRepeated
                  have rightHeadSimpleInLeft :
                      (leftHead :: leftTail).count leftHead = 1 := by
                    simp [List.count_eq_zero.mpr leftAbsent]
                  have rightHeadSimpleInRight :
                      (rightHead :: rightHead :: rightTail).count leftHead = 1 := by
                    rw [← counts leftHead]
                    exact rightHeadSimpleInLeft
                  have evaluatedWords :
                      candidate.eval (headValuation leftHead)
                          (wordOfCons leftHead leftTail) =
                        candidate.eval (headValuation leftHead)
                          (wordOfCons rightHead
                            (rightHead :: rightTail)) := by
                    exact valid (headValuation leftHead)
                  have leftEvaluation :=
                    contract.eval_headValuation_of_simple leftHead
                      (wordOfCons leftHead leftTail) rightHeadSimpleInLeft
                  have rightEvaluation :=
                    contract.eval_headValuation_of_simple leftHead
                      (wordOfCons rightHead (rightHead :: rightTail))
                      rightHeadSimpleInRight
                  have evaluatedHeads :
                      (if leftHead = leftHead then (1 : Fin 6) else 0) =
                        if rightHead = leftHead then 1 else 0 :=
                    leftEvaluation.symm.trans
                      (evaluatedWords.trans rightEvaluation)
                  rw [if_pos rfl] at evaluatedHeads
                  have heads : rightHead = leftHead := by
                    apply Decidable.byContradiction
                    intro different
                    rw [if_neg different] at evaluatedHeads
                    exact (by decide : (1 : Fin 6) ≠ 0) evaluatedHeads
                  subst rightHead
                  exact False.elim ((by decide : (2 : Nat) ≠ 1)
                    (leftRightHeadCount.symm.trans rightHeadSimpleInLeft))
          | double leftHead leftTail leftTailNormal leftAbsent =>
              cases rightNormal with
              | double rightHead rightTail rightTailNormal rightAbsent =>
                  rw [protectedPrefix_double, protectedPrefix_double]
              | single rightHead rightTail rightTailNormal rightAbsent =>
                  have leftRepeated :
                      (leftHead :: leftHead :: leftTail).count leftHead = 2 := by
                    simp [List.count_eq_zero.mpr leftAbsent]
                  have rightSimple :
                      (rightHead :: rightTail).count rightHead = 1 := by
                    simp [List.count_eq_zero.mpr rightAbsent]
                  have leftRightHeadSimple :
                      (leftHead :: leftHead :: leftTail).count rightHead = 1 := by
                    rw [counts rightHead]
                    exact rightSimple
                  have rightLeftHeadRepeated :
                      (rightHead :: rightTail).count leftHead = 2 := by
                    rw [← counts leftHead]
                    exact leftRepeated
                  have evaluatedWords :
                      candidate.eval (headValuation rightHead)
                          (wordOfCons leftHead (leftHead :: leftTail)) =
                        candidate.eval (headValuation rightHead)
                          (wordOfCons rightHead rightTail) := by
                    exact valid (headValuation rightHead)
                  have leftEvaluation :=
                    contract.eval_headValuation_of_simple rightHead
                      (wordOfCons leftHead (leftHead :: leftTail))
                      leftRightHeadSimple
                  have rightEvaluation :=
                    contract.eval_headValuation_of_simple rightHead
                      (wordOfCons rightHead rightTail) rightSimple
                  have evaluatedHeads :
                      (if leftHead = rightHead then (1 : Fin 6) else 0) =
                        if rightHead = rightHead then 1 else 0 :=
                    leftEvaluation.symm.trans
                      (evaluatedWords.trans rightEvaluation)
                  rw [if_pos rfl] at evaluatedHeads
                  have heads : leftHead = rightHead := by
                    apply Decidable.byContradiction
                    intro different
                    rw [if_neg different] at evaluatedHeads
                    exact (by decide : (0 : Fin 6) ≠ 1) evaluatedHeads
                  subst rightHead
                  exact False.elim ((by decide : (2 : Nat) ≠ 1)
                    (rightLeftHeadRepeated.symm.trans rightSimple))

end SeparatorContract

/-! ## Shared unrestricted endpoint -/

theorem basisFor_of_separatorContract
    (candidate : Semigroup (Fin 6))
    (models : Models candidate SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.basis)
    (contract : SeparatorContract candidate) :
    BasisFor candidate SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  obtain ⟨leftHead, leftTail, leftNormal, leftDerives⟩ :=
    exists_capNormal identity.lhs
  obtain ⟨rightHead, rightTail, rightNormal, rightDerives⟩ :=
    exists_capNormal identity.rhs
  let leftWord := wordOfCons leftHead leftTail
  let rightWord := wordOfCons rightHead rightTail
  have normalizedValid :
      ∀ valuation : Nat -> Fin 6,
        candidate.eval valuation leftWord =
          candidate.eval valuation rightWord := by
    intro valuation
    have leftSound := leftDerives.sound models valuation
    have rightSound := rightDerives.sound models valuation
    exact leftSound.symm.trans ((valid valuation).trans rightSound)
  have normalCounts := contract.valid_counts_eq
    (left := leftWord) (right := rightWord)
    (by simpa [leftWord, wordOfCons, Word.toList] using leftNormal)
    (by simpa [rightWord, wordOfCons, Word.toList] using rightNormal)
    normalizedValid
  have normalPrefix := contract.valid_protectedPrefix_eq
    leftWord rightWord
    (by simpa [leftWord, wordOfCons, Word.toList] using leftNormal)
    (by simpa [rightWord, wordOfCons, Word.toList] using rightNormal)
    normalizedValid
  have middleList := capNormal_derives_of_invariants
    leftNormal rightNormal
    (by simpa [leftWord, rightWord, wordOfCons, Word.toList] using
      normalCounts)
    (by simpa [leftWord, rightWord, wordOfCons, Word.toList] using
      normalPrefix)
  have middle : Derives SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.basis leftWord rightWord := by
    simpa [leftWord, rightWord, wordOfCons] using
      S5_107.ListDerives.toWord middleList
  exact leftDerives.trans (middle.trans rightDerives.symm)

namespace S6_1041

open SemigroupBasis.Generated.Order6InitialPrefixTailTargets.S6_1041

def separators : SeparatorContract table.semigroup.opposite where
  capSelected := capSelected
  secondHead := secondHead
  secondSelected := secondSelected
  secondFiller := secondFiller
  secondAfterImmediate := secondAfterImmediate
  secondAfterLate := secondAfterLate
  secondAfterFiller := secondAfterFiller
  capSelected_ne_absent := by decide
  capSelected_ne_repeated := by decide
  cap_absent_filler := by decide
  cap_single_filler := by decide
  cap_repeated_filler := by decide
  cap_absent_selected := by decide
  cap_single_selected := by decide
  cap_repeated_selected := by decide
  head_filler_filler := by decide
  head_selected_filler := by decide
  head_filler_selected := by decide
  head_late_filler := by decide
  second_filler_filler := by decide
  second_head_filler := by decide
  second_after_filler_filler := by decide
  second_head_selected := by decide
  second_after_filler_selected := by decide
  second_immediate_filler := by decide
  second_late_filler := by decide
  second_outputs_ne := by decide

theorem opposite_basis_complete_aristotle :
    BasisFor table.semigroup.opposite SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.basis :=
  basisFor_of_separatorContract _ SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.S6_1041.opposite_models separators

theorem basis_complete_aristotle :
    BasisFor table.semigroup SemigroupBasis.Generated.Order6InitialPrefixTailTargets.basis := by
  have reversed := opposite_basis_complete_aristotle.oppositeReversed
  simpa [SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.basis_eq_reversedTarget] using reversed

end S6_1041

namespace S6_1043

open SemigroupBasis.Generated.Order6InitialPrefixTailTargets.S6_1043

def separators : SeparatorContract table.semigroup.opposite where
  capSelected := capSelected
  secondHead := secondHead
  secondSelected := secondSelected
  secondFiller := secondFiller
  secondAfterImmediate := secondAfterImmediate
  secondAfterLate := secondAfterLate
  secondAfterFiller := secondAfterFiller
  capSelected_ne_absent := by decide
  capSelected_ne_repeated := by decide
  cap_absent_filler := by decide
  cap_single_filler := by decide
  cap_repeated_filler := by decide
  cap_absent_selected := by decide
  cap_single_selected := by decide
  cap_repeated_selected := by decide
  head_filler_filler := by decide
  head_selected_filler := by decide
  head_filler_selected := by decide
  head_late_filler := by decide
  second_filler_filler := by decide
  second_head_filler := by decide
  second_after_filler_filler := by decide
  second_head_selected := by decide
  second_after_filler_selected := by decide
  second_immediate_filler := by decide
  second_late_filler := by decide
  second_outputs_ne := by decide

theorem opposite_basis_complete_aristotle :
    BasisFor table.semigroup.opposite SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.basis :=
  basisFor_of_separatorContract _ SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.S6_1043.opposite_models separators

theorem basis_complete_aristotle :
    BasisFor table.semigroup SemigroupBasis.Generated.Order6InitialPrefixTailTargets.basis := by
  have reversed := opposite_basis_complete_aristotle.oppositeReversed
  simpa [SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.basis_eq_reversedTarget] using reversed

end S6_1043

namespace S6_1045

open SemigroupBasis.Generated.Order6InitialPrefixTailTargets.S6_1045

def separators : SeparatorContract table.semigroup.opposite where
  capSelected := capSelected
  secondHead := secondHead
  secondSelected := secondSelected
  secondFiller := secondFiller
  secondAfterImmediate := secondAfterImmediate
  secondAfterLate := secondAfterLate
  secondAfterFiller := secondAfterFiller
  capSelected_ne_absent := by decide
  capSelected_ne_repeated := by decide
  cap_absent_filler := by decide
  cap_single_filler := by decide
  cap_repeated_filler := by decide
  cap_absent_selected := by decide
  cap_single_selected := by decide
  cap_repeated_selected := by decide
  head_filler_filler := by decide
  head_selected_filler := by decide
  head_filler_selected := by decide
  head_late_filler := by decide
  second_filler_filler := by decide
  second_head_filler := by decide
  second_after_filler_filler := by decide
  second_head_selected := by decide
  second_after_filler_selected := by decide
  second_immediate_filler := by decide
  second_late_filler := by decide
  second_outputs_ne := by decide

theorem opposite_basis_complete_aristotle :
    BasisFor table.semigroup.opposite SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.basis :=
  basisFor_of_separatorContract _ SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.S6_1045.opposite_models separators

theorem basis_complete_aristotle :
    BasisFor table.semigroup SemigroupBasis.Generated.Order6InitialPrefixTailTargets.basis := by
  have reversed := opposite_basis_complete_aristotle.oppositeReversed
  simpa [SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.basis_eq_reversedTarget] using reversed

end S6_1045

namespace S6_1046

open SemigroupBasis.Generated.Order6InitialPrefixTailTargets.S6_1046

def separators : SeparatorContract table.semigroup.opposite where
  capSelected := capSelected
  secondHead := secondHead
  secondSelected := secondSelected
  secondFiller := secondFiller
  secondAfterImmediate := secondAfterImmediate
  secondAfterLate := secondAfterLate
  secondAfterFiller := secondAfterFiller
  capSelected_ne_absent := by decide
  capSelected_ne_repeated := by decide
  cap_absent_filler := by decide
  cap_single_filler := by decide
  cap_repeated_filler := by decide
  cap_absent_selected := by decide
  cap_single_selected := by decide
  cap_repeated_selected := by decide
  head_filler_filler := by decide
  head_selected_filler := by decide
  head_filler_selected := by decide
  head_late_filler := by decide
  second_filler_filler := by decide
  second_head_filler := by decide
  second_after_filler_filler := by decide
  second_head_selected := by decide
  second_after_filler_selected := by decide
  second_immediate_filler := by decide
  second_late_filler := by decide
  second_outputs_ne := by decide

theorem opposite_basis_complete_aristotle :
    BasisFor table.semigroup.opposite SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.basis :=
  basisFor_of_separatorContract _ SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.S6_1046.opposite_models separators

theorem basis_complete_aristotle :
    BasisFor table.semigroup SemigroupBasis.Generated.Order6InitialPrefixTailTargets.basis := by
  have reversed := opposite_basis_complete_aristotle.oppositeReversed
  simpa [SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.basis_eq_reversedTarget] using reversed

end S6_1046

namespace S6_1062

open SemigroupBasis.Generated.Order6InitialPrefixTailTargets.S6_1062

def separators : SeparatorContract table.semigroup.opposite where
  capSelected := capSelected
  secondHead := secondHead
  secondSelected := secondSelected
  secondFiller := secondFiller
  secondAfterImmediate := secondAfterImmediate
  secondAfterLate := secondAfterLate
  secondAfterFiller := secondAfterFiller
  capSelected_ne_absent := by decide
  capSelected_ne_repeated := by decide
  cap_absent_filler := by decide
  cap_single_filler := by decide
  cap_repeated_filler := by decide
  cap_absent_selected := by decide
  cap_single_selected := by decide
  cap_repeated_selected := by decide
  head_filler_filler := by decide
  head_selected_filler := by decide
  head_filler_selected := by decide
  head_late_filler := by decide
  second_filler_filler := by decide
  second_head_filler := by decide
  second_after_filler_filler := by decide
  second_head_selected := by decide
  second_after_filler_selected := by decide
  second_immediate_filler := by decide
  second_late_filler := by decide
  second_outputs_ne := by decide

theorem opposite_basis_complete_aristotle :
    BasisFor table.semigroup.opposite SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.basis :=
  basisFor_of_separatorContract _ SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.S6_1062.opposite_models separators

theorem basis_complete_aristotle :
    BasisFor table.semigroup SemigroupBasis.Generated.Order6InitialPrefixTailTargets.basis := by
  have reversed := opposite_basis_complete_aristotle.oppositeReversed
  simpa [SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.basis_eq_reversedTarget] using reversed

end S6_1062

namespace S6_1063

open SemigroupBasis.Generated.Order6InitialPrefixTailTargets.S6_1063

def separators : SeparatorContract table.semigroup.opposite where
  capSelected := capSelected
  secondHead := secondHead
  secondSelected := secondSelected
  secondFiller := secondFiller
  secondAfterImmediate := secondAfterImmediate
  secondAfterLate := secondAfterLate
  secondAfterFiller := secondAfterFiller
  capSelected_ne_absent := by decide
  capSelected_ne_repeated := by decide
  cap_absent_filler := by decide
  cap_single_filler := by decide
  cap_repeated_filler := by decide
  cap_absent_selected := by decide
  cap_single_selected := by decide
  cap_repeated_selected := by decide
  head_filler_filler := by decide
  head_selected_filler := by decide
  head_filler_selected := by decide
  head_late_filler := by decide
  second_filler_filler := by decide
  second_head_filler := by decide
  second_after_filler_filler := by decide
  second_head_selected := by decide
  second_after_filler_selected := by decide
  second_immediate_filler := by decide
  second_late_filler := by decide
  second_outputs_ne := by decide

theorem opposite_basis_complete_aristotle :
    BasisFor table.semigroup.opposite SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.basis :=
  basisFor_of_separatorContract _ SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.S6_1063.opposite_models separators

theorem basis_complete_aristotle :
    BasisFor table.semigroup SemigroupBasis.Generated.Order6InitialPrefixTailTargets.basis := by
  have reversed := opposite_basis_complete_aristotle.oppositeReversed
  simpa [SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.basis_eq_reversedTarget] using reversed

end S6_1063

namespace S6_1100

open SemigroupBasis.Generated.Order6InitialPrefixTailTargets.S6_1100

def separators : SeparatorContract table.semigroup.opposite where
  capSelected := capSelected
  secondHead := secondHead
  secondSelected := secondSelected
  secondFiller := secondFiller
  secondAfterImmediate := secondAfterImmediate
  secondAfterLate := secondAfterLate
  secondAfterFiller := secondAfterFiller
  capSelected_ne_absent := by decide
  capSelected_ne_repeated := by decide
  cap_absent_filler := by decide
  cap_single_filler := by decide
  cap_repeated_filler := by decide
  cap_absent_selected := by decide
  cap_single_selected := by decide
  cap_repeated_selected := by decide
  head_filler_filler := by decide
  head_selected_filler := by decide
  head_filler_selected := by decide
  head_late_filler := by decide
  second_filler_filler := by decide
  second_head_filler := by decide
  second_after_filler_filler := by decide
  second_head_selected := by decide
  second_after_filler_selected := by decide
  second_immediate_filler := by decide
  second_late_filler := by decide
  second_outputs_ne := by decide

theorem opposite_basis_complete_aristotle :
    BasisFor table.semigroup.opposite SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.basis :=
  basisFor_of_separatorContract _ SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.S6_1100.opposite_models separators

theorem basis_complete_aristotle :
    BasisFor table.semigroup SemigroupBasis.Generated.Order6InitialPrefixTailTargets.basis := by
  have reversed := opposite_basis_complete_aristotle.oppositeReversed
  simpa [SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.basis_eq_reversedTarget] using reversed

end S6_1100

namespace S6_1102

open SemigroupBasis.Generated.Order6InitialPrefixTailTargets.S6_1102

def separators : SeparatorContract table.semigroup.opposite where
  capSelected := capSelected
  secondHead := secondHead
  secondSelected := secondSelected
  secondFiller := secondFiller
  secondAfterImmediate := secondAfterImmediate
  secondAfterLate := secondAfterLate
  secondAfterFiller := secondAfterFiller
  capSelected_ne_absent := by decide
  capSelected_ne_repeated := by decide
  cap_absent_filler := by decide
  cap_single_filler := by decide
  cap_repeated_filler := by decide
  cap_absent_selected := by decide
  cap_single_selected := by decide
  cap_repeated_selected := by decide
  head_filler_filler := by decide
  head_selected_filler := by decide
  head_filler_selected := by decide
  head_late_filler := by decide
  second_filler_filler := by decide
  second_head_filler := by decide
  second_after_filler_filler := by decide
  second_head_selected := by decide
  second_after_filler_selected := by decide
  second_immediate_filler := by decide
  second_late_filler := by decide
  second_outputs_ne := by decide

theorem opposite_basis_complete_aristotle :
    BasisFor table.semigroup.opposite SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.basis :=
  basisFor_of_separatorContract _ SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.S6_1102.opposite_models separators

theorem basis_complete_aristotle :
    BasisFor table.semigroup SemigroupBasis.Generated.Order6InitialPrefixTailTargets.basis := by
  have reversed := opposite_basis_complete_aristotle.oppositeReversed
  simpa [SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.basis_eq_reversedTarget] using reversed

end S6_1102

namespace S6_1134

open SemigroupBasis.Generated.Order6InitialPrefixTailTargets.S6_1134

def separators : SeparatorContract table.semigroup.opposite where
  capSelected := capSelected
  secondHead := secondHead
  secondSelected := secondSelected
  secondFiller := secondFiller
  secondAfterImmediate := secondAfterImmediate
  secondAfterLate := secondAfterLate
  secondAfterFiller := secondAfterFiller
  capSelected_ne_absent := by decide
  capSelected_ne_repeated := by decide
  cap_absent_filler := by decide
  cap_single_filler := by decide
  cap_repeated_filler := by decide
  cap_absent_selected := by decide
  cap_single_selected := by decide
  cap_repeated_selected := by decide
  head_filler_filler := by decide
  head_selected_filler := by decide
  head_filler_selected := by decide
  head_late_filler := by decide
  second_filler_filler := by decide
  second_head_filler := by decide
  second_after_filler_filler := by decide
  second_head_selected := by decide
  second_after_filler_selected := by decide
  second_immediate_filler := by decide
  second_late_filler := by decide
  second_outputs_ne := by decide

theorem opposite_basis_complete_aristotle :
    BasisFor table.semigroup.opposite SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.basis :=
  basisFor_of_separatorContract _ SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.S6_1134.opposite_models separators

theorem basis_complete_aristotle :
    BasisFor table.semigroup SemigroupBasis.Generated.Order6InitialPrefixTailTargets.basis := by
  have reversed := opposite_basis_complete_aristotle.oppositeReversed
  simpa [SemigroupBasis.CoRoots.Order6InitialPrefixTailRoots.basis_eq_reversedTarget] using reversed

end S6_1134

end SemigroupBasis.CoRoots.Order6InitialPrefixTailCompleteness
