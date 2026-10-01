import SemigroupBasis.FiniteNilpotentDecisionDAG
import SemigroupBasis.FiniteNilpotentRestrictedGrowthEnumerator

namespace SemigroupBasis
namespace FiniteNilpotentCounterexample

open FiniteNilpotentRestrictedGrowthEnumerator

/-- Exhaustively check that a finite-variable word has one fixed table value. -/
def checkWordValue (T : FiniteTable) (word : Word (Fin variables))
    (value : Fin T.order) : Bool :=
  (FiniteTable.assignments variables T.order).all fun valuation =>
    decide (T.semigroup.eval valuation word = value)

/-- Fused exhaustive fixed-value check, avoiding a flattened valuation list. -/
def checkWordValueFused (T : FiniteTable) (word : Word (Fin variables))
    (value : Fin T.order) : Bool :=
  FiniteTable.checkAssignmentsFused variables T.order fun valuation =>
    decide (T.semigroup.eval valuation word = value)

/-- Soundness of the fixed-value word checker. -/
theorem checkWordValue_sound (T : FiniteTable)
    (word : Word (Fin variables)) (value : Fin T.order)
    (checked : checkWordValue T word value = true) :
    ∀ valuation, T.semigroup.eval valuation word = value := by
  intro valuation
  have row :=
    (List.all_eq_true.mp checked) valuation
      (FiniteTable.assignment_mem valuation)
  exact of_decide_eq_true row

theorem checkWordValueFused_sound (T : FiniteTable)
    (word : Word (Fin variables)) (value : Fin T.order)
    (checked : checkWordValueFused T word value = true) :
    ∀ valuation, T.semigroup.eval valuation word = value := by
  intro valuation
  exact of_decide_eq_true
    (FiniteTable.checkAssignmentsFused_sound
      (fun candidate => decide (T.semigroup.eval candidate word = value))
      checked valuation)

/-- Transport one exact finite-support identity check back to natural variable
names through an explicitly checked encoder/decoder round trip. -/
theorem identitySatisfiedByNat_of_check (T : FiniteTable)
    (identity : Identity Nat) (toFinite : Nat → Fin variables)
    (fromFinite : Fin variables → Nat)
    (roundTrip : (identity.map toFinite).map fromFinite = identity)
    (checked : T.checkIdentity (identity.map toFinite) = true) :
    identity.SatisfiedBy T.semigroup := by
  have finiteValid :=
    T.checkIdentity_sound (identity.map toFinite) checked
  have reconstructed :=
    (identity.map toFinite).satisfiedBy_map
      fromFinite T.semigroup finiteValid
  rw [roundTrip] at reconstructed
  exact reconstructed

/-- Transport the fused finite-assignment identity check back to natural
variable names through the same explicit encoder/decoder round trip. -/
theorem identitySatisfiedByNat_of_fused_check (T : FiniteTable)
    (identity : Identity Nat) (toFinite : Nat → Fin variables)
    (fromFinite : Fin variables → Nat)
    (roundTrip : (identity.map toFinite).map fromFinite = identity)
    (checked : T.checkIdentityFused (identity.map toFinite) = true) :
    identity.SatisfiedBy T.semigroup := by
  have finiteValid :=
    T.checkIdentityFused_sound (identity.map toFinite) checked
  have reconstructed :=
    (identity.map toFinite).satisfiedBy_map
      fromFinite T.semigroup finiteValid
  rw [roundTrip] at reconstructed
  exact reconstructed

/-- Transport a checked fixed word value back through an exact finite support. -/
theorem wordValueNat_of_check (T : FiniteTable) (word : Word Nat)
    (toFinite : Nat → Fin variables) (fromFinite : Fin variables → Nat)
    (roundTrip : (word.map toFinite).map fromFinite = word)
    (value : Fin T.order)
    (checked : checkWordValue T (word.map toFinite) value = true) :
    ∀ valuation, T.semigroup.eval valuation word = value := by
  intro valuation
  have finiteValue :=
    checkWordValue_sound T (word.map toFinite) value checked
      (fun index => valuation (fromFinite index))
  rw [← roundTrip]
  simpa only [Semigroup.eval_map] using finiteValue

/-- Transport a fused fixed-word value check through an exact finite support. -/
theorem wordValueNat_of_fused_check (T : FiniteTable) (word : Word Nat)
    (toFinite : Nat → Fin variables) (fromFinite : Fin variables → Nat)
    (roundTrip : (word.map toFinite).map fromFinite = word)
    (value : Fin T.order)
    (checked : checkWordValueFused T (word.map toFinite) value = true) :
    ∀ valuation, T.semigroup.eval valuation word = value := by
  intro valuation
  have finiteValue :=
    checkWordValueFused_sound T (word.map toFinite) value checked
      (fun index => valuation (fromFinite index))
  rw [← roundTrip]
  simpa only [Semigroup.eval_map] using finiteValue

/-- Assemble model validity without asking `decide` to reduce one large basis
check in a single kernel computation. -/
theorem models_nil (G : Semigroup S) : Models G ([] : List (Identity α)) := by
  intro identity member
  simp at member

theorem models_cons {G : Semigroup S} {identity : Identity α}
    {identities : List (Identity α)}
    (head : identity.SatisfiedBy G) (tail : Models G identities) :
    Models G (identity :: identities) := by
  intro candidate member
  rcases List.mem_cons.mp member with rfl | member
  · exact head
  · exact tail candidate member

theorem models_append {G : Semigroup S}
    {left right : List (Identity α)}
    (leftModels : Models G left) (rightModels : Models G right) :
    Models G (left ++ right) := by
  intro identity member
  rcases List.mem_append.mp member with member | member
  · exact leftModels identity member
  · exact rightModels identity member

/-- Lift a finite family of derivations along inclusion of its basis. -/
theorem derivesAll_mono {source target identities : List (Identity Nat)}
    (subset : ∀ identity, identity ∈ source → identity ∈ target)
    (sourceDerives : FiniteCertificate.DerivesAll source identities) :
    FiniteCertificate.DerivesAll target identities := by
  intro identity member
  exact (sourceDerives identity member).transport fun sourceIdentity sourceMember =>
    Derives.fromBasis (subset sourceIdentity sourceMember)

/-- Assemble derivations for two consecutive inventory chunks. -/
theorem derivesAll_append {basis left right : List (Identity Nat)}
    (leftDerives : FiniteCertificate.DerivesAll basis left)
    (rightDerives : FiniteCertificate.DerivesAll basis right) :
    FiniteCertificate.DerivesAll basis (left ++ right) := by
  intro identity member
  rcases List.mem_append.mp member with member | member
  · exact leftDerives identity member
  · exact rightDerives identity member

/-- Assemble a restricted-growth inventory from explicit row proofs. -/
theorem allRestrictedGrowth_nil :
    FiniteCertificate.AllRestrictedGrowth ([] : List (Identity Nat)) := by
  intro identity member
  simp at member

theorem allRestrictedGrowth_cons {identity : Identity Nat}
    {identities : List (Identity Nat)}
    (head : FiniteVariableRenaming.IsRestrictedGrowth
      (identity.lhs.toList ++ identity.rhs.toList))
    (tail : FiniteCertificate.AllRestrictedGrowth identities) :
    FiniteCertificate.AllRestrictedGrowth (identity :: identities) := by
  intro candidate member
  rcases List.mem_cons.mp member with rfl | member
  · exact head
  · exact tail candidate member

theorem allRestrictedGrowth_append
    {left right : List (Identity Nat)}
    (leftRestricted : FiniteCertificate.AllRestrictedGrowth left)
    (rightRestricted : FiniteCertificate.AllRestrictedGrowth right) :
    FiniteCertificate.AllRestrictedGrowth (left ++ right) := by
  intro identity member
  rcases List.mem_append.mp member with member | member
  · exact leftRestricted identity member
  · exact rightRestricted identity member

/-- Decode one base-six digit of a packed finite valuation. -/
def unpackFinSix (packed index : Nat) : Fin 6 :=
  ⟨(packed / 6 ^ index) % 6, Nat.mod_lt _ (by decide)⟩

/-- One checked counterexample row.  The explicit values make accidental
candidate-index or valuation drift fail closed. -/
structure Row where
  candidateIndex : Nat
  identity : Identity Nat
  packedValuation : Nat
  leftValue : Fin 6
  rightValue : Fin 6
deriving Repr, DecidableEq

/-- The proposition reflected by one counterexample row. -/
def Row.Valid (G : Semigroup (Fin 6))
    (candidates : List (Identity Nat)) (row : Row) : Prop :=
  FiniteNilpotentDecisionDAG.lookup candidates row.candidateIndex =
      some row.identity ∧
    G.eval (unpackFinSix row.packedValuation) row.identity.lhs =
      row.leftValue ∧
    G.eval (unpackFinSix row.packedValuation) row.identity.rhs =
      row.rightValue ∧
    row.leftValue ≠ row.rightValue

private instance instDecidableRowValid
    (G : Semigroup (Fin 6)) (candidates : List (Identity Nat)) (row : Row) :
    Decidable (row.Valid G candidates) := by
  unfold Row.Valid
  infer_instance

/-- Executable row checker. -/
def checkRow (G : Semigroup (Fin 6))
    (candidates : List (Identity Nat)) (row : Row) : Bool :=
  decide (row.Valid G candidates)

/-- A checked row really refutes its recorded identity. -/
theorem Row.not_satisfied {G : Semigroup (Fin 6)}
    {candidates : List (Identity Nat)} {row : Row}
    (checked : checkRow G candidates row = true) :
    ¬ row.identity.SatisfiedBy G := by
  have valid : row.Valid G candidates := by
    apply of_decide_eq_true
    simpa only [checkRow] using checked
  apply Identity.not_satisfiedBy_of_failsAt
    (valuation := unpackFinSix row.packedValuation)
  intro equalValues
  exact valid.2.2.2
    (valid.2.1.symm.trans (equalValues.trans valid.2.2.1))

/-- The three derivational routes accepted before consulting counterexamples. -/
def HasRoute (inventory : List (Identity Nat))
    (identity : Identity Nat) : Prop :=
  identity.lhs = identity.rhs ∨
    identity ∈ inventory ∨
      FiniteVariableRenaming.normalizeIdentity
        identity.rhs identity.lhs ∈ inventory

private instance instDecidableHasRoute
    (inventory : List (Identity Nat)) (identity : Identity Nat) :
    Decidable (HasRoute inventory identity) := by
  unfold HasRoute
  infer_instance

/-- Boolean reflection of `HasRoute`. -/
def routeCheck (inventory : List (Identity Nat))
    (identity : Identity Nat) : Bool :=
  decide (HasRoute inventory identity)

/-- The ordered complement for which class-specific rows are mandatory. -/
def expectedCounterexamples (candidates inventory : List (Identity Nat)) :
    List (Identity Nat) :=
  candidates.filter fun identity => !routeCheck inventory identity

/-- Check exact complement coverage and every packed valuation. -/
def check (G : Semigroup (Fin 6))
    (candidates inventory : List (Identity Nat)) (rows : List Row) : Bool :=
  decide (rows.map Row.identity =
      expectedCounterexamples candidates inventory) &&
    rows.all (checkRow G candidates)

/-- A candidate valid in the table cannot lie in the checked counterexample
complement, so it must have one of the three derivational routes. -/
theorem valid_hasRoute {G : Semigroup (Fin 6)}
    {candidates inventory : List (Identity Nat)} {rows : List Row}
    (checked : check G candidates inventory rows = true)
    {identity : Identity Nat} (candidate : identity ∈ candidates)
    (valid : identity.SatisfiedBy G) :
    HasRoute inventory identity := by
  change
    (decide (rows.map Row.identity =
        expectedCounterexamples candidates inventory) &&
      rows.all (checkRow G candidates)) = true at checked
  simp only [Bool.and_eq_true] at checked
  have identities :
      rows.map Row.identity = expectedCounterexamples candidates inventory :=
    of_decide_eq_true checked.1
  by_cases hasRoute : HasRoute inventory identity
  · exact hasRoute
  · have complement :
        identity ∈ expectedCounterexamples candidates inventory := by
      apply List.mem_filter.mpr
      refine ⟨candidate, ?_⟩
      simp [routeCheck, hasRoute]
    rw [← identities] at complement
    rcases List.mem_map.mp complement with ⟨row, rowMember, rowIdentity⟩
    have rowChecked :=
      (List.all_eq_true.mp checked.2) row rowMember
    have invalid := Row.not_satisfied rowChecked
    rw [rowIdentity] at invalid
    exact False.elim (invalid valid)

/-- Swapping an already normalized pair and normalizing again gives the same
representative as normalizing the original pair in swapped order. -/
private theorem normalizeIdentity_swap_normalized (left right : Word Nat) :
    FiniteVariableRenaming.normalizeIdentity
        (FiniteVariableRenaming.normalizeIdentity left right).rhs
        (FiniteVariableRenaming.normalizeIdentity left right).lhs =
      FiniteVariableRenaming.normalizeIdentity right left := by
  have restrictedGrowthFrom_eq_of_maps :
      ∀ {next leftFinal rightFinal : Nat}
        {leftCodes rightCodes : List Nat},
        FiniteVariableRenaming.RestrictedGrowthFrom
            next leftCodes leftFinal →
          FiniteVariableRenaming.RestrictedGrowthFrom
            next rightCodes rightFinal →
          ∀ (forward backward : Nat → Nat),
            (∀ code, code < next → forward code = code) →
            (∀ code, code < next → backward code = code) →
            leftCodes.map forward = rightCodes →
            rightCodes.map backward = leftCodes →
            leftCodes = rightCodes := by
    intro next leftFinal rightFinal leftCodes rightCodes
      leftGrowth rightGrowth forward backward
      forwardFixes backwardFixes mapsForward mapsBackward
    induction leftGrowth generalizing
        rightCodes rightFinal forward backward with
    | nil =>
        simpa only [List.map_nil] using mapsForward
    | seen smaller restGrowth induction =>
        cases rightGrowth with
        | nil =>
            simp at mapsForward
        | seen rightSmaller rightRestGrowth =>
            simp only [List.map_cons, List.cons.injEq] at mapsForward mapsBackward
            have headEq := mapsForward.1
            rw [forwardFixes _ smaller] at headEq
            cases headEq
            apply congrArg (List.cons _)
            exact induction rightRestGrowth forward backward
              forwardFixes backwardFixes mapsForward.2 mapsBackward.2
        | fresh rightRestGrowth =>
            simp only [List.map_cons, List.cons.injEq] at mapsForward
            have impossible :=
              (forwardFixes _ smaller).symm.trans mapsForward.1
            exact (Nat.ne_of_lt smaller impossible).elim
    | fresh restGrowth induction =>
        cases rightGrowth with
        | nil =>
            simp at mapsForward
        | seen rightSmaller rightRestGrowth =>
            simp only [List.map_cons, List.cons.injEq] at mapsBackward
            have impossible :=
              (backwardFixes _ rightSmaller).symm.trans mapsBackward.1
            exact (Nat.ne_of_lt rightSmaller impossible).elim
        | fresh rightRestGrowth =>
            simp only [List.map_cons, List.cons.injEq] at mapsForward mapsBackward
            apply congrArg (List.cons _)
            exact induction rightRestGrowth forward backward
              (by
                intro code codeLess
                rcases Nat.lt_or_eq_of_le
                    (Nat.lt_succ_iff.mp codeLess) with codeLt | rfl
                · exact forwardFixes code codeLt
                · exact mapsForward.1)
              (by
                intro code codeLess
                rcases Nat.lt_or_eq_of_le
                    (Nat.lt_succ_iff.mp codeLess) with codeLt | rfl
                · exact backwardFixes code codeLt
                · exact mapsBackward.1)
              mapsForward.2 mapsBackward.2
  have restrictedGrowth_eq_of_maps :
      ∀ {leftCodes rightCodes : List Nat},
        FiniteVariableRenaming.IsRestrictedGrowth leftCodes →
          FiniteVariableRenaming.IsRestrictedGrowth rightCodes →
          ∀ (forward backward : Nat → Nat),
            leftCodes.map forward = rightCodes →
            rightCodes.map backward = leftCodes →
            leftCodes = rightCodes := by
    intro leftCodes rightCodes leftGrowth rightGrowth
      forward backward mapsForward mapsBackward
    rcases leftGrowth with ⟨leftFinal, leftGrowth⟩
    rcases rightGrowth with ⟨rightFinal, rightGrowth⟩
    exact restrictedGrowthFrom_eq_of_maps leftGrowth rightGrowth
      forward backward
      (by intro code smaller; simp at smaller)
      (by intro code smaller; simp at smaller)
      mapsForward mapsBackward
  have wordMap_map :
      ∀ (word : Word Nat) (first second : Nat → Nat),
        (word.map first).map second =
          word.map (fun letter => second (first letter)) := by
    intro word first second
    cases word
    simp [Word.map, List.map_map]
  have wordToList_map :
      ∀ (word : Word Nat) (rename : Nat → Nat),
        (word.map rename).toList = word.toList.map rename := by
    intro word rename
    cases word
    rfl
  have pairListsMap :
      ∀ (leftWord rightWord mappedLeft mappedRight : Word Nat)
        (rename : Nat → Nat),
        leftWord.map rename = mappedLeft →
          rightWord.map rename = mappedRight →
          (leftWord.toList ++ rightWord.toList).map rename =
            mappedLeft.toList ++ mappedRight.toList := by
    intro leftWord rightWord mappedLeft mappedRight rename
      leftMap rightMap
    simp only [List.map_append, ← wordToList_map, leftMap, rightMap]
  have append_eq_append_of_length_eq :
      ∀ {firstLeft firstRight secondLeft secondRight : List Nat},
        firstLeft.length = secondLeft.length →
          firstLeft ++ firstRight = secondLeft ++ secondRight →
          firstLeft = secondLeft ∧ firstRight = secondRight := by
    intro firstLeft firstRight secondLeft secondRight
      lengthEq appendEq
    induction firstLeft generalizing secondLeft with
    | nil =>
        cases secondLeft with
        | nil =>
            constructor
            · rfl
            · simpa only [List.nil_append] using appendEq
        | cons head tail =>
            simp at lengthEq
    | cons head tail induction =>
        cases secondLeft with
        | nil =>
            simp at lengthEq
        | cons secondHead secondTail =>
            simp only [List.length_cons, Nat.succ.injEq] at lengthEq
            change
              head :: (tail ++ firstRight) =
                secondHead :: (secondTail ++ secondRight) at appendEq
            simp only [List.cons.injEq] at appendEq
            cases appendEq.1
            rcases induction lengthEq appendEq.2 with
              ⟨leftEq, rightEq⟩
            exact ⟨congrArg (List.cons head) leftEq, rightEq⟩
  let initial := FiniteVariableRenaming.normalize left right
  let nested :=
    FiniteVariableRenaming.normalize initial.right initial.left
  let direct := FiniteVariableRenaming.normalize right left
  have initialNormalizes :=
    FiniteVariableRenaming.normalize_normalizes left right
  change left.map initial.forward = initial.left ∧
    right.map initial.forward = initial.right at initialNormalizes
  have initialReconstructs :=
    FiniteVariableRenaming.normalize_reconstructs left right
  change initial.left.map initial.inverse = left ∧
    initial.right.map initial.inverse = right at initialReconstructs
  have nestedNormalizes :=
    FiniteVariableRenaming.normalize_normalizes
      initial.right initial.left
  change initial.right.map nested.forward = nested.left ∧
    initial.left.map nested.forward = nested.right at nestedNormalizes
  have nestedReconstructs :=
    FiniteVariableRenaming.normalize_reconstructs
      initial.right initial.left
  change nested.left.map nested.inverse = initial.right ∧
    nested.right.map nested.inverse = initial.left at nestedReconstructs
  have directNormalizes :=
    FiniteVariableRenaming.normalize_normalizes right left
  change right.map direct.forward = direct.left ∧
    left.map direct.forward = direct.right at directNormalizes
  have directReconstructs :=
    FiniteVariableRenaming.normalize_reconstructs right left
  change direct.left.map direct.inverse = right ∧
    direct.right.map direct.inverse = left at directReconstructs
  have nestedGrowth :=
    FiniteVariableRenaming.normalize_isRestrictedGrowth
      initial.right initial.left
  change FiniteVariableRenaming.IsRestrictedGrowth
    (nested.left.toList ++ nested.right.toList) at nestedGrowth
  have directGrowth :=
    FiniteVariableRenaming.normalize_isRestrictedGrowth right left
  change FiniteVariableRenaming.IsRestrictedGrowth
    (direct.left.toList ++ direct.right.toList) at directGrowth
  let forward : Nat → Nat := fun code =>
    direct.forward (initial.inverse (nested.inverse code))
  let backward : Nat → Nat := fun code =>
    nested.forward (initial.forward (direct.inverse code))
  have forwardLeft : nested.left.map forward = direct.left := by
    calc
      nested.left.map forward =
          ((nested.left.map nested.inverse).map initial.inverse).map
            direct.forward := by
        simp only [forward, wordMap_map]
      _ = ((initial.right.map initial.inverse).map direct.forward) := by
        rw [nestedReconstructs.1]
      _ = right.map direct.forward := by
        rw [initialReconstructs.2]
      _ = direct.left := directNormalizes.1
  have forwardRight : nested.right.map forward = direct.right := by
    calc
      nested.right.map forward =
          ((nested.right.map nested.inverse).map initial.inverse).map
            direct.forward := by
        simp only [forward, wordMap_map]
      _ = ((initial.left.map initial.inverse).map direct.forward) := by
        rw [nestedReconstructs.2]
      _ = left.map direct.forward := by
        rw [initialReconstructs.1]
      _ = direct.right := directNormalizes.2
  have backwardLeft : direct.left.map backward = nested.left := by
    calc
      direct.left.map backward =
          ((direct.left.map direct.inverse).map initial.forward).map
            nested.forward := by
        simp only [backward, wordMap_map]
      _ = ((right.map initial.forward).map nested.forward) := by
        rw [directReconstructs.1]
      _ = initial.right.map nested.forward := by
        rw [initialNormalizes.2]
      _ = nested.left := nestedNormalizes.1
  have backwardRight : direct.right.map backward = nested.right := by
    calc
      direct.right.map backward =
          ((direct.right.map direct.inverse).map initial.forward).map
            nested.forward := by
        simp only [backward, wordMap_map]
      _ = ((left.map initial.forward).map nested.forward) := by
        rw [directReconstructs.2]
      _ = initial.left.map nested.forward := by
        rw [initialNormalizes.1]
      _ = nested.right := nestedNormalizes.2
  have patternsEq :
      nested.left.toList ++ nested.right.toList =
        direct.left.toList ++ direct.right.toList :=
    restrictedGrowth_eq_of_maps nestedGrowth directGrowth
      forward backward
      (pairListsMap _ _ _ _ forward forwardLeft forwardRight)
      (pairListsMap _ _ _ _ backward backwardLeft backwardRight)
  have leftLength :
      nested.left.toList.length = direct.left.toList.length := by
    have mappedLength :=
      congrArg (fun word : Word Nat => word.toList.length) forwardLeft
    simpa only [wordToList_map, List.length_map] using mappedLength
  rcases append_eq_append_of_length_eq leftLength patternsEq with
    ⟨leftEq, rightEq⟩
  have leftWordEq := Word.toList_injective leftEq
  have rightWordEq := Word.toList_injective rightEq
  change (⟨nested.left, nested.right⟩ : Identity Nat) =
    ⟨direct.left, direct.right⟩
  calc
    (⟨nested.left, nested.right⟩ : Identity Nat) =
        ⟨direct.left, nested.right⟩ :=
      congrArg (fun lhs => (⟨lhs, nested.right⟩ : Identity Nat)) leftWordEq
    _ = ⟨direct.left, direct.right⟩ :=
      congrArg (fun rhs => (⟨direct.left, rhs⟩ : Identity Nat)) rightWordEq

/-- Any sound route classifier on the normalized finite candidate domain
discharges the `complete` field of a finite-nilpotent inventory.  Keeping this
step independent of a particular executable classifier lets larger cutoffs use
a linear decision partition instead of repeated list membership searches. -/
theorem inventoryCompleteOfValidHasRoute {G : Semigroup (Fin 6)}
    {inventory : List (Identity Nat)}
    {cutoff : Nat} {common : Word Nat}
    (commonLength : common.toList.length = cutoff)
    (commonNodup : common.toList.Nodup)
    (classify :
      ∀ {identity : Identity Nat},
        identity ∈ candidateDomain cutoff →
          identity.SatisfiedBy G → HasRoute inventory identity)
    (left right : Word Nat) (distinct : left ≠ right)
    (shape : FiniteNilpotentCertificate.ShortShape cutoff common left right)
    (valid : (⟨left, right⟩ : Identity Nat).SatisfiedBy G) :
    FiniteVariableRenaming.normalizeIdentity left right ∈ inventory ∨
      FiniteVariableRenaming.normalizeIdentity right left ∈ inventory := by
  have candidate := normalize_mem_candidateDomain
    commonLength commonNodup shape
  have normalizedValid :=
    FiniteVariableRenaming.normalizeIdentity_valid G left right valid
  rcases classify candidate normalizedValid with
    reflexive | direct | swapped
  · exfalso
    apply distinct
    let result := FiniteVariableRenaming.normalize left right
    have reconstructs :=
      FiniteVariableRenaming.normalize_reconstructs left right
    change result.left.map result.inverse = left ∧
      result.right.map result.inverse = right at reconstructs
    change result.left = result.right at reflexive
    calc
      left = result.left.map result.inverse := reconstructs.1.symm
      _ = result.right.map result.inverse :=
        congrArg (fun word : Word Nat => word.map result.inverse) reflexive
      _ = right := reconstructs.2
  · exact Or.inl direct
  · exact Or.inr (normalizeIdentity_swap_normalized left right ▸ swapped)

/-- A checked candidate partition discharges the `complete` field of a
finite-nilpotent restricted-growth inventory.

The other inventory fields remain separate: the partition does not assert
that its listed identities are restricted-growth or valid in the table. -/
theorem inventoryCompleteOfCheck {G : Semigroup (Fin 6)}
    {inventory : List (Identity Nat)} {rows : List Row}
    {cutoff : Nat} {common : Word Nat}
    (commonLength : common.toList.length = cutoff)
    (commonNodup : common.toList.Nodup)
    (checked :
      check G (candidateDomain cutoff) inventory rows = true)
    (left right : Word Nat) (distinct : left ≠ right)
    (shape : FiniteNilpotentCertificate.ShortShape cutoff common left right)
    (valid : (⟨left, right⟩ : Identity Nat).SatisfiedBy G) :
    FiniteVariableRenaming.normalizeIdentity left right ∈ inventory ∨
      FiniteVariableRenaming.normalizeIdentity right left ∈ inventory := by
  apply inventoryCompleteOfValidHasRoute commonLength commonNodup
  · intro identity candidate valid
    exact valid_hasRoute checked candidate valid
  · exact distinct
  · exact shape
  · exact valid

/-- Checked route coverage plus a checked listed derivation DAG derives every
valid candidate identity. -/
theorem derivesCandidate {G : Semigroup (Fin 6)}
    {basis candidates inventory : List (Identity Nat)} {rows : List Row}
    (listed : FiniteCertificate.DerivesAll basis inventory)
    (checked : check G candidates inventory rows = true)
    {identity : Identity Nat} (candidate : identity ∈ candidates)
    (valid : identity.SatisfiedBy G) :
    Derives basis identity.lhs identity.rhs := by
  rcases valid_hasRoute checked candidate valid with
    reflexive | direct | swapped
  · rw [reflexive]
    exact Derives.refl identity.rhs
  · exact listed identity direct
  · exact FiniteVariableRenaming.derives_of_normalize_swapped
      identity.lhs identity.rhs (listed _ swapped)

/-- Normalize an arbitrary short-shape pair, use the finite checked partition,
and reconstruct the original variable names. -/
theorem derivesShape {G : Semigroup (Fin 6)}
    {basis inventory : List (Identity Nat)} {rows : List Row}
    {cutoff : Nat} {common left right : Word Nat}
    (commonLength : common.toList.length = cutoff)
    (commonNodup : common.toList.Nodup)
    (listed : FiniteCertificate.DerivesAll basis inventory)
    (checked :
      check G (candidateDomain cutoff) inventory rows = true)
    (shape : FiniteNilpotentCertificate.ShortShape cutoff common left right)
    (valid : (⟨left, right⟩ : Identity Nat).SatisfiedBy G) :
    Derives basis left right := by
  have candidate := normalize_mem_candidateDomain
    commonLength commonNodup shape
  have normalizedValid :=
    FiniteVariableRenaming.normalizeIdentity_valid G left right valid
  have normalizedDerivation :=
    derivesCandidate listed checked candidate normalizedValid
  exact FiniteVariableRenaming.derives_of_normalize
    left right normalizedDerivation

/-- End-to-end assembly from checked models, long collapse, listed roots, and
the exact candidate/counterexample partition. -/
theorem basisForOfCheck {G : Semigroup (Fin 6)}
    {basis inventory : List (Identity Nat)} {rows : List Row}
    {cutoff : Nat} {common : Word Nat}
    (models : Models G basis)
    (toCommon :
      ∀ word : Word Nat,
        cutoff ≤ word.toList.length → Derives basis word common)
    (commonLength : common.toList.length = cutoff)
    (commonNodup : common.toList.Nodup)
    (listed : FiniteCertificate.DerivesAll basis inventory)
    (checked :
      check G (candidateDomain cutoff) inventory rows = true) :
    BasisFor G basis := by
  apply BasisFor.ofNilpotentLengthCutoff models toCommon
  · intro left right leftShort rightShort valid
    exact derivesShape commonLength commonNodup listed checked
      (Or.inl ⟨leftShort, rightShort⟩) valid
  · intro short shortLength valid
    exact derivesShape commonLength commonNodup listed checked
      (Or.inr ⟨shortLength, rfl⟩) valid

end FiniteNilpotentCounterexample

namespace FiniteNilpotentDecisionPartition

open FiniteNilpotentRestrictedGrowthEnumerator

/-- A local explanation for one normalized candidate.  Inventory routes use
indices, so checking an accepted row does not scan the complete inventory.
Counterexamples carry only the finite valuation needed to refute the row. -/
inductive Evidence where
  | reflexive
  | direct (inventoryIndex : Nat)
  | swapped (inventoryIndex : Nat)
  | counterexample (packedValuation : Nat)
      (leftValue rightValue : Fin 6)
deriving Repr, DecidableEq

/-- One row in an ordered, exhaustive decision partition. -/
structure Row where
  identity : Identity Nat
  evidence : Evidence
deriving Repr, DecidableEq

/-- The proposition reflected by one local decision. -/
def Evidence.Valid (G : Semigroup (Fin 6))
    (inventory : List (Identity Nat)) (identity : Identity Nat) :
    Evidence → Prop
  | .reflexive => identity.lhs = identity.rhs
  | .direct inventoryIndex =>
      FiniteNilpotentDecisionDAG.lookup inventory inventoryIndex =
        some identity
  | .swapped inventoryIndex =>
      FiniteNilpotentDecisionDAG.lookup inventory inventoryIndex =
        some (FiniteVariableRenaming.normalizeIdentity
          identity.rhs identity.lhs)
  | .counterexample packedValuation leftValue rightValue =>
      G.eval (FiniteNilpotentCounterexample.unpackFinSix packedValuation)
          identity.lhs = leftValue ∧
        G.eval (FiniteNilpotentCounterexample.unpackFinSix packedValuation)
          identity.rhs = rightValue ∧
        leftValue ≠ rightValue

private instance instDecidableEvidenceValid
    (G : Semigroup (Fin 6)) (inventory : List (Identity Nat))
    (identity : Identity Nat) (evidence : Evidence) :
    Decidable (evidence.Valid G inventory identity) := by
  cases evidence <;> simp only [Evidence.Valid] <;> infer_instance

/-- Executable checker for one candidate-aligned evidence item. -/
def checkEvidence (G : Semigroup (Fin 6))
    (inventory : List (Identity Nat)) (identity : Identity Nat)
    (evidence : Evidence) : Bool :=
  decide (evidence.Valid G inventory identity)

/-- Executable checker for one local decision. -/
def checkRow (G : Semigroup (Fin 6))
    (inventory : List (Identity Nat)) (row : Row) : Bool :=
  checkEvidence G inventory row.identity row.evidence

private theorem lookup_mem {values : List α} {index : Nat} {value : α}
    (found : FiniteNilpotentDecisionDAG.lookup values index = some value) :
    value ∈ values := by
  induction values generalizing index with
  | nil =>
      simp [FiniteNilpotentDecisionDAG.lookup] at found
  | cons head tail induction =>
      cases index with
      | zero =>
          simp [FiniteNilpotentDecisionDAG.lookup] at found
          subst value
          exact List.Mem.head tail
      | succ index =>
          apply List.Mem.tail head
          exact induction
            (by simpa [FiniteNilpotentDecisionDAG.lookup] using found)

/-- A checked evidence item either supplies a derivational route or refutes
its aligned candidate in the target table. -/
theorem Evidence.hasRoute_or_not_satisfied {G : Semigroup (Fin 6)}
    {inventory : List (Identity Nat)} {identity : Identity Nat}
    {evidence : Evidence}
    (checked : checkEvidence G inventory identity evidence = true) :
    FiniteNilpotentCounterexample.HasRoute inventory identity ∨
      ¬ identity.SatisfiedBy G := by
  have valid : evidence.Valid G inventory identity := by
    apply of_decide_eq_true
    simpa only [checkEvidence] using checked
  cases evidence with
  | reflexive =>
      exact Or.inl (Or.inl valid)
  | direct inventoryIndex =>
      exact Or.inl (Or.inr (Or.inl (lookup_mem valid)))
  | swapped inventoryIndex =>
      exact Or.inl (Or.inr (Or.inr (lookup_mem valid)))
  | counterexample packedValuation leftValue rightValue =>
      apply Or.inr
      apply Identity.not_satisfiedBy_of_failsAt
        (valuation :=
          FiniteNilpotentCounterexample.unpackFinSix packedValuation)
      intro equalValues
      exact valid.2.2
        (valid.1.symm.trans (equalValues.trans valid.2.1))

/-- Compatibility wrapper for an identity-carrying local row. -/
theorem Row.hasRoute_or_not_satisfied {G : Semigroup (Fin 6)}
    {inventory : List (Identity Nat)} {row : Row}
    (checked : checkRow G inventory row = true) :
    FiniteNilpotentCounterexample.HasRoute inventory row.identity ∨
      ¬ row.identity.SatisfiedBy G :=
  Evidence.hasRoute_or_not_satisfied checked

/-- Traverse an evidence list in lockstep with the canonical candidate list. -/
def checkStreamAux (G : Semigroup (Fin 6))
    (inventory : List (Identity Nat)) :
    List (Identity Nat) → List Evidence → Bool
  | [], [] => true
  | identity :: identities, evidence :: evidences =>
      checkEvidence G inventory identity evidence &&
        checkStreamAux G inventory identities evidences
  | _, _ => false

/-- Check exact positional coverage and every local decision without repeating
candidate identities in generated source. -/
def checkStream (G : Semigroup (Fin 6))
    (candidates inventory : List (Identity Nat))
    (evidences : List Evidence) : Bool :=
  checkStreamAux G inventory candidates evidences

/-- Check a sequence of bounded evidence chunks against consecutive slices of
the canonical candidate list.  Slice boundaries come only from evidence chunk
lengths, so missing or surplus evidence leaves an exact-coverage check false. -/
def checkStreamChunksAux (G : Semigroup (Fin 6))
    (inventory : List (Identity Nat)) :
    List (Identity Nat) → List (List Evidence) → Bool
  | [], [] => true
  | _ :: _, [] => false
  | candidates, evidenceChunk :: evidenceChunks =>
      checkStreamAux G inventory
          (candidates.take evidenceChunk.length) evidenceChunk &&
        checkStreamChunksAux G inventory
          (candidates.drop evidenceChunk.length) evidenceChunks

/-- Number of candidate positions consumed by a sequence of evidence chunks. -/
def evidenceCount : List (List Evidence) → Nat
  | [] => 0
  | evidenceChunk :: evidenceChunks =>
      evidenceChunk.length + evidenceCount evidenceChunks

/-- Candidate suffix left after consuming a sequence of evidence chunks. -/
def dropStreamChunks (candidates : List (Identity Nat)) :
    List (List Evidence) → List (Identity Nat)
  | [] => candidates
  | evidenceChunk :: evidenceChunks =>
      dropStreamChunks
        (candidates.drop evidenceChunk.length) evidenceChunks

/-- Check a bounded prefix of the candidate stream.  Unlike
`checkStreamChunksAux`, an empty evidence suffix succeeds without requiring
the candidate suffix to be empty; exact global coverage is recovered by the
append theorem below and the final exact suffix check. -/
def checkStreamChunksPrefix (G : Semigroup (Fin 6))
    (inventory : List (Identity Nat)) :
    List (Identity Nat) → List (List Evidence) → Bool
  | _, [] => true
  | candidates, evidenceChunk :: evidenceChunks =>
      checkStreamAux G inventory
          (candidates.take evidenceChunk.length) evidenceChunk &&
        checkStreamChunksPrefix G inventory
          (candidates.drop evidenceChunk.length) evidenceChunks

/-- Consuming bounded chunks is the same as dropping their total evidence
count from the candidate stream. -/
theorem dropStreamChunks_eq_drop_evidenceCount
    (candidates : List (Identity Nat))
    (evidenceChunks : List (List Evidence)) :
    dropStreamChunks candidates evidenceChunks =
      candidates.drop (evidenceCount evidenceChunks) := by
  induction evidenceChunks generalizing candidates with
  | nil => rfl
  | cons evidenceChunk evidenceChunks induction =>
      simp only [dropStreamChunks, evidenceCount]
      rw [induction, List.drop_drop]

/-- Split an exact stream check at any evidence-chunk boundary.  This is the
compositional kernel bridge used for very large finite decision partitions:
each prefix can be reduced in its own module while the final suffix retains
the original exact-coverage condition. -/
theorem checkStreamChunksAux_append (G : Semigroup (Fin 6))
    (inventory : List (Identity Nat))
    (candidates : List (Identity Nat))
    (headChunks tailChunks : List (List Evidence)) :
    checkStreamChunksAux G inventory candidates (headChunks ++ tailChunks) =
      (checkStreamChunksPrefix G inventory candidates headChunks &&
        checkStreamChunksAux G inventory
          (dropStreamChunks candidates headChunks) tailChunks) := by
  induction headChunks generalizing candidates with
  | nil =>
      simp only [List.nil_append, checkStreamChunksPrefix, dropStreamChunks,
        Bool.true_and]
  | cons evidenceChunk headChunks induction =>
      simp only [List.cons_append, checkStreamChunksAux,
        checkStreamChunksPrefix, dropStreamChunks]
      rw [induction]
      simp only [Bool.and_assoc]

/-- Chunk-aware positional stream checker.  This retains the alignment and
exact-coverage guarantees of `checkStream` without constructing one flat
evidence reduction. -/
def checkStreamChunks (G : Semigroup (Fin 6))
    (candidates inventory : List (Identity Nat))
    (evidenceChunks : List (List Evidence)) : Bool :=
  checkStreamChunksAux G inventory candidates evidenceChunks

/-- Compose a checked chunk prefix with an exact checked suffix.  This keeps
large executable certificates in separate declarations while preserving the
same ordered, exact-coverage contract as one monolithic stream check. -/
theorem checkStreamChunks_append_of_prefix (G : Semigroup (Fin 6))
    (inventory candidates : List (Identity Nat))
    (headChunks tailChunks : List (List Evidence))
    (headChecked :
      checkStreamChunksPrefix G inventory candidates headChunks = true)
    (tailChecked :
      checkStreamChunks G (dropStreamChunks candidates headChunks)
        inventory tailChunks = true) :
    checkStreamChunks G candidates inventory (headChunks ++ tailChunks) =
      true := by
  unfold checkStreamChunks at tailChecked ⊢
  rw [checkStreamChunksAux_append, headChecked, Bool.true_and]
  exact tailChecked

/-- A valid candidate covered by a checked positional stream has a route. -/
theorem valid_hasRouteOfStreamCheck {G : Semigroup (Fin 6)}
    {candidates inventory : List (Identity Nat)}
    {evidences : List Evidence}
    (checked : checkStream G candidates inventory evidences = true)
    {identity : Identity Nat} (candidate : identity ∈ candidates)
    (valid : identity.SatisfiedBy G) :
    FiniteNilpotentCounterexample.HasRoute inventory identity := by
  unfold checkStream at checked
  induction candidates generalizing evidences identity with
  | nil =>
      simp at candidate
  | cons head tail induction =>
      cases evidences with
      | nil =>
          simp [checkStreamAux] at checked
      | cons evidence evidences =>
          simp only [checkStreamAux, Bool.and_eq_true] at checked
          rcases List.mem_cons.mp candidate with rfl | candidate
          · rcases Evidence.hasRoute_or_not_satisfied checked.1 with
              route | invalid
            · exact route
            · exact False.elim (invalid valid)
          · exact induction checked.2 candidate valid

/-- A valid candidate covered by checked positional chunks has a route. -/
theorem valid_hasRouteOfStreamChunksCheck {G : Semigroup (Fin 6)}
    {candidates inventory : List (Identity Nat)}
    {evidenceChunks : List (List Evidence)}
    (checked :
      checkStreamChunks G candidates inventory evidenceChunks = true)
    {identity : Identity Nat} (candidate : identity ∈ candidates)
    (valid : identity.SatisfiedBy G) :
    FiniteNilpotentCounterexample.HasRoute inventory identity := by
  unfold checkStreamChunks at checked
  induction evidenceChunks generalizing candidates identity with
  | nil =>
      cases candidates with
      | nil => simp at candidate
      | cons head tail => simp [checkStreamChunksAux] at checked
  | cons evidenceChunk evidenceChunks induction =>
      simp only [checkStreamChunksAux, Bool.and_eq_true] at checked
      rw [← List.take_append_drop evidenceChunk.length candidates] at candidate
      rcases List.mem_append.mp candidate with candidate | candidate
      · exact valid_hasRouteOfStreamCheck checked.1 candidate valid
      · exact induction checked.2 candidate valid

/-- Check ordered candidate coverage and every local decision.  Unlike the
cutoff-four complement checker, this traverses the candidate stream once. -/
def check (G : Semigroup (Fin 6))
    (candidates inventory : List (Identity Nat)) (rows : List Row) : Bool :=
  decide (rows.map Row.identity = candidates) &&
    rows.all (checkRow G inventory)

/-- A valid candidate in a checked decision partition has a derivational
route; its counterexample alternative contradicts validity. -/
theorem valid_hasRoute {G : Semigroup (Fin 6)}
    {candidates inventory : List (Identity Nat)} {rows : List Row}
    (checked : check G candidates inventory rows = true)
    {identity : Identity Nat} (candidate : identity ∈ candidates)
    (valid : identity.SatisfiedBy G) :
    FiniteNilpotentCounterexample.HasRoute inventory identity := by
  change
    (decide (rows.map Row.identity = candidates) &&
      rows.all (checkRow G inventory)) = true at checked
  simp only [Bool.and_eq_true] at checked
  have identities : rows.map Row.identity = candidates :=
    of_decide_eq_true checked.1
  rw [← identities] at candidate
  rcases List.mem_map.mp candidate with ⟨row, rowMember, rowIdentity⟩
  have rowChecked :=
    (List.all_eq_true.mp checked.2) row rowMember
  rcases Row.hasRoute_or_not_satisfied rowChecked with route | invalid
  · simpa only [rowIdentity] using route
  · exfalso
    apply invalid
    simpa only [rowIdentity] using valid

/-- A checked linear decision partition supplies the inventory-completeness
field used by the reusable finite-nilpotent cutoff theorem. -/
theorem inventoryCompleteOfCheck {G : Semigroup (Fin 6)}
    {inventory : List (Identity Nat)} {rows : List Row}
    {cutoff : Nat} {common : Word Nat}
    (commonLength : common.toList.length = cutoff)
    (commonNodup : common.toList.Nodup)
    (checked :
      check G (candidateDomain cutoff) inventory rows = true)
    (left right : Word Nat) (distinct : left ≠ right)
    (shape : FiniteNilpotentCertificate.ShortShape cutoff common left right)
    (valid : (⟨left, right⟩ : Identity Nat).SatisfiedBy G) :
    FiniteVariableRenaming.normalizeIdentity left right ∈ inventory ∨
      FiniteVariableRenaming.normalizeIdentity right left ∈ inventory := by
  apply FiniteNilpotentCounterexample.inventoryCompleteOfValidHasRoute
      commonLength commonNodup
  · intro identity candidate valid
    exact valid_hasRoute checked candidate valid
  · exact distinct
  · exact shape
  · exact valid

/-- Positional stream variant of the finite-inventory completeness bridge. -/
theorem inventoryCompleteOfStreamCheck {G : Semigroup (Fin 6)}
    {inventory : List (Identity Nat)} {evidences : List Evidence}
    {cutoff : Nat} {common : Word Nat}
    (commonLength : common.toList.length = cutoff)
    (commonNodup : common.toList.Nodup)
    (checked :
      checkStream G (candidateDomain cutoff) inventory evidences = true)
    (left right : Word Nat) (distinct : left ≠ right)
    (shape : FiniteNilpotentCertificate.ShortShape cutoff common left right)
    (valid : (⟨left, right⟩ : Identity Nat).SatisfiedBy G) :
    FiniteVariableRenaming.normalizeIdentity left right ∈ inventory ∨
      FiniteVariableRenaming.normalizeIdentity right left ∈ inventory := by
  apply FiniteNilpotentCounterexample.inventoryCompleteOfValidHasRoute
      commonLength commonNodup
  · intro identity candidate valid
    exact valid_hasRouteOfStreamCheck checked candidate valid
  · exact distinct
  · exact shape
  · exact valid

/-- Chunk-aware positional stream variant of the finite-inventory completeness
bridge. -/
theorem inventoryCompleteOfStreamChunksCheck {G : Semigroup (Fin 6)}
    {inventory : List (Identity Nat)}
    {evidenceChunks : List (List Evidence)}
    {cutoff : Nat} {common : Word Nat}
    (commonLength : common.toList.length = cutoff)
    (commonNodup : common.toList.Nodup)
    (checked :
      checkStreamChunks G (candidateDomain cutoff) inventory evidenceChunks =
        true)
    (left right : Word Nat) (distinct : left ≠ right)
    (shape : FiniteNilpotentCertificate.ShortShape cutoff common left right)
    (valid : (⟨left, right⟩ : Identity Nat).SatisfiedBy G) :
    FiniteVariableRenaming.normalizeIdentity left right ∈ inventory ∨
      FiniteVariableRenaming.normalizeIdentity right left ∈ inventory := by
  apply FiniteNilpotentCounterexample.inventoryCompleteOfValidHasRoute
      commonLength commonNodup
  · intro identity candidate valid
    exact valid_hasRouteOfStreamChunksCheck checked candidate valid
  · exact distinct
  · exact shape
  · exact valid

end FiniteNilpotentDecisionPartition
end SemigroupBasis
