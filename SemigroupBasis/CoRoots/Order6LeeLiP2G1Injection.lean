import SemigroupBasis.CoRoots.Order6LeeLiP2G1

/-!
# G1 finite-to-global separation

Every G1 invariant contains at most two letters.  Hence two unequal invariants
can be relabelled injectively inside `Fin 4`.  A four-variable canonical
separation check then supplies a valuation distinguishing their canonical
words.  Soundness of the shared G1 normalization transports that distinction
back to the original identity.
-/

namespace SemigroupBasis.CoRoots.Order6LeeLiP2G1.Injection

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6LeeLiP2G1

/-- Apply a letter map to the data retained by the G1 normal form. -/
def mapInvariant (rename : alpha → beta) : Invariant alpha → Invariant beta
  | .letter a => .letter (rename a)
  | .square a => .square (rename a)
  | .pair a b => .pair (rename a) (rename b)
  | .marked a b => .marked (rename a) (rename b)

/-- The canonical-word construction commutes with relabelling. -/
theorem canonical_map (rename : alpha → beta) (value : Invariant alpha) :
    (canonical value).map rename = canonical (mapInvariant rename value) := by
  cases value <;> rfl

/-- Repeat one-letter invariants so that every invariant occupies two slots. -/
private def slots : Invariant alpha → alpha × alpha
  | .letter a => (a, a)
  | .square a => (a, a)
  | .pair a b => (a, b)
  | .marked a b => (a, b)

private def slotLetters (value : Invariant alpha) : List alpha :=
  [(slots value).1, (slots value).2]

/-- Four slots cover every letter occurring in either invariant. -/
private def support (left right : Invariant Nat) : List Nat :=
  [(slots left).1, (slots left).2, (slots right).1, (slots right).2]

/-- Encode the four support slots by their first positions. -/
private def encodeFour (left right : Invariant Nat) (letter : Nat) : Fin 4 :=
  if letter = (slots left).1 then 0
  else if letter = (slots left).2 then 1
  else if letter = (slots right).1 then 2
  else 3

/-- Decode a support position. -/
private def decodeFour (left right : Invariant Nat) (index : Fin 4) : Nat :=
  match index.val with
  | 0 => (slots left).1
  | 1 => (slots left).2
  | 2 => (slots right).1
  | _ => (slots right).2

private theorem decode_encodeFour_of_mem
    (left right : Invariant Nat) {letter : Nat}
    (member : letter ∈ support left right) :
    decodeFour left right (encodeFour left right letter) = letter := by
  have slotZero :
      decodeFour left right (encodeFour left right (slots left).1) =
        (slots left).1 := by
    simp [encodeFour, decodeFour]
  have slotOne :
      decodeFour left right (encodeFour left right (slots left).2) =
        (slots left).2 := by
    by_cases equal : (slots left).2 = (slots left).1
    · rw [equal]
      exact slotZero
    · simp [encodeFour, decodeFour, equal]
  have slotTwo :
      decodeFour left right (encodeFour left right (slots right).1) =
        (slots right).1 := by
    by_cases first : (slots right).1 = (slots left).1
    · rw [first]
      exact slotZero
    · by_cases second : (slots right).1 = (slots left).2
      · rw [second]
        exact slotOne
      · simp [encodeFour, decodeFour, first, second]
  have slotThree :
      decodeFour left right (encodeFour left right (slots right).2) =
        (slots right).2 := by
    by_cases first : (slots right).2 = (slots left).1
    · rw [first]
      exact slotZero
    · by_cases second : (slots right).2 = (slots left).2
      · rw [second]
        exact slotOne
      · by_cases third : (slots right).2 = (slots right).1
        · rw [third]
          exact slotTwo
        · simp [encodeFour, decodeFour, first, second, third]
  simp [support] at member
  rcases member with equality | equality | equality | equality <;>
    subst letter
  · exact slotZero
  · exact slotOne
  · exact slotTwo
  · exact slotThree

private theorem mapInvariant_roundTrip_of_slots
    (left right value : Invariant Nat)
    (covered : ∀ letter, letter ∈ slotLetters value →
      letter ∈ support left right) :
    mapInvariant (decodeFour left right)
        (mapInvariant (encodeFour left right) value) = value := by
  cases value with
  | letter a =>
      simp only [mapInvariant]
      rw [decode_encodeFour_of_mem left right
        (covered a (by simp [slotLetters, slots]))]
  | square a =>
      simp only [mapInvariant]
      rw [decode_encodeFour_of_mem left right
        (covered a (by simp [slotLetters, slots]))]
  | pair a b =>
      simp only [mapInvariant]
      rw [decode_encodeFour_of_mem left right
          (covered a (by simp [slotLetters, slots])),
        decode_encodeFour_of_mem left right
          (covered b (by simp [slotLetters, slots]))]
  | marked a b =>
      simp only [mapInvariant]
      rw [decode_encodeFour_of_mem left right
          (covered a (by simp [slotLetters, slots])),
        decode_encodeFour_of_mem left right
          (covered b (by simp [slotLetters, slots]))]

private theorem mapInvariant_roundTrip_left
    (left right : Invariant Nat) :
    mapInvariant (decodeFour left right)
        (mapInvariant (encodeFour left right) left) = left := by
  apply mapInvariant_roundTrip_of_slots left right left
  intro letter member
  simp [slotLetters] at member
  rcases member with equality | equality <;>
    subst letter <;> simp [support]

private theorem mapInvariant_roundTrip_right
    (left right : Invariant Nat) :
    mapInvariant (decodeFour left right)
        (mapInvariant (encodeFour left right) right) = right := by
  apply mapInvariant_roundTrip_of_slots left right right
  intro letter member
  simp [slotLetters] at member
  rcases member with equality | equality <;>
    subst letter <;> simp [support]

/-- Relabelling into the four support slots is injective on the two invariants. -/
private theorem mapInvariant_encodeFour_injective
    (left right : Invariant Nat) :
    mapInvariant (encodeFour left right) left =
        mapInvariant (encodeFour left right) right →
      left = right := by
  intro same
  have decoded := congrArg (mapInvariant (decodeFour left right)) same
  rw [mapInvariant_roundTrip_left, mapInvariant_roundTrip_right] at decoded
  exact decoded

/-- Pair and marked classes only arise with distinct displayed letters. -/
private def Admissible : Invariant alpha → Prop
  | .letter _ => True
  | .square _ => True
  | .pair a b => a ≠ b
  | .marked a b => a ≠ b

private theorem invariant_admissible (word : Word Nat) :
    Admissible (invariant word) := by
  cases word with
  | mk head tail =>
      cases reversed : tail.reverse with
      | nil => simp [invariant, reversed, Admissible]
      | cons final rest =>
          cases rest with
          | nil =>
              by_cases equal : head = final
              · simp [invariant, reversed, equal, Admissible]
              · simp [invariant, reversed, equal, Admissible]
          | cons penultimate remainder =>
              by_cases equal : penultimate = final
              · simp [invariant, reversed, equal, Admissible]
              · simp [invariant, reversed, equal, Admissible]

private theorem encodeFour_injective_of_mem
    (left right : Invariant Nat) {a b : Nat}
    (aMember : a ∈ support left right)
    (bMember : b ∈ support left right)
    (same : encodeFour left right a = encodeFour left right b) :
    a = b := by
  have decodedSame := congrArg (decodeFour left right) same
  rw [decode_encodeFour_of_mem left right aMember,
    decode_encodeFour_of_mem left right bMember] at decodedSame
  exact decodedSame

private theorem mapped_admissible_of_slots
    (left right value : Invariant Nat)
    (covered : ∀ letter, letter ∈ slotLetters value →
      letter ∈ support left right)
    (admissible : Admissible value) :
    Admissible (mapInvariant (encodeFour left right) value) := by
  cases value with
  | letter a => trivial
  | square a => trivial
  | pair a b =>
      simp only [Admissible, mapInvariant] at admissible ⊢
      intro same
      exact admissible <| encodeFour_injective_of_mem left right
        (covered a (by simp [slotLetters, slots]))
        (covered b (by simp [slotLetters, slots])) same
  | marked a b =>
      simp only [Admissible, mapInvariant] at admissible ⊢
      intro same
      exact admissible <| encodeFour_injective_of_mem left right
        (covered a (by simp [slotLetters, slots]))
        (covered b (by simp [slotLetters, slots])) same

private theorem mapped_left_admissible
    (left right : Invariant Nat) (admissible : Admissible left) :
    Admissible (mapInvariant (encodeFour left right) left) := by
  apply mapped_admissible_of_slots left right left
  · intro letter member
    simp [slotLetters] at member
    rcases member with equality | equality <;>
      subst letter <;> simp [support]
  · exact admissible

private theorem mapped_right_admissible
    (left right : Invariant Nat) (admissible : Admissible right) :
    Admissible (mapInvariant (encodeFour left right) right) := by
  apply mapped_admissible_of_slots left right right
  · intro letter member
    simp [slotLetters] at member
    rcases member with equality | equality <;>
      subst letter <;> simp [support]
  · exact admissible

private theorem admissible_mem_finiteInvariants
    (value : Invariant (Fin n)) (admissible : Admissible value) :
    value ∈ finiteInvariants n := by
  cases value <;> simp_all [finiteInvariants, Admissible]

/-- Soundness of the executable four-variable separation sweep. -/
theorem canonicalSeparation_of_check
    (table : FiniteTable)
    (checked : checkCanonicalSeparationFour table = true) :
    CanonicalSeparation table 4 := by
  intro left leftMember right rightMember different
  have leftChecked :=
    (List.all_eq_true.mp checked) left leftMember
  have rightChecked :=
    (List.all_eq_true.mp leftChecked) right rightMember
  have separatedCheck :
      (FiniteTable.assignments 4 table.order).any (fun valuation =>
          decide
            (table.semigroup.eval valuation (canonical left) ≠
              table.semigroup.eval valuation (canonical right))) = true := by
    simpa [checkCanonicalSeparationFour, different] using rightChecked
  rcases List.any_eq_true.mp separatedCheck with
    ⟨valuation, _, separated⟩
  exact ⟨valuation, of_decide_eq_true separated⟩

/-- Four-variable canonical separation implies separation for all identities. -/
theorem invariantSeparation_of_canonicalSeparation
    (table : FiniteTable) (models : Models table.semigroup basis)
    (separates : CanonicalSeparation table 4) :
    InvariantSeparation table.semigroup := by
  intro identity valid
  apply Classical.byContradiction
  intro different
  let leftInv := invariant identity.lhs
  let rightInv := invariant identity.rhs
  let rename := encodeFour leftInv rightInv
  have mappedDifferent :
      mapInvariant rename leftInv ≠ mapInvariant rename rightInv := by
    intro same
    apply different
    exact mapInvariant_encodeFour_injective leftInv rightInv same
  have leftMember :
      mapInvariant rename leftInv ∈ finiteInvariants 4 := by
    apply admissible_mem_finiteInvariants
    exact mapped_left_admissible leftInv rightInv
      (invariant_admissible identity.lhs)
  have rightMember :
      mapInvariant rename rightInv ∈ finiteInvariants 4 := by
    apply admissible_mem_finiteInvariants
    exact mapped_right_admissible leftInv rightInv
      (invariant_admissible identity.rhs)
  obtain ⟨valuation, canonicalDifferent⟩ :=
    separates (mapInvariant rename leftInv) leftMember
      (mapInvariant rename rightInv) rightMember mappedDifferent
  have mappedValid := Identity.satisfiedBy_map identity rename
    table.semigroup valid
  have validAt :
      table.semigroup.eval valuation (identity.lhs.map rename) =
        table.semigroup.eval valuation (identity.rhs.map rename) :=
    mappedValid valuation
  have leftNormalization := Derives.sound models
    (derivesCanonical identity.lhs) (fun letter => valuation (rename letter))
  have rightNormalization := Derives.sound models
    (derivesCanonical identity.rhs) (fun letter => valuation (rename letter))
  have leftSound :
      table.semigroup.eval valuation (identity.lhs.map rename) =
        table.semigroup.eval valuation
          (canonical (mapInvariant rename leftInv)) := by
    calc
      table.semigroup.eval valuation (identity.lhs.map rename) =
          table.semigroup.eval (fun letter => valuation (rename letter))
            identity.lhs :=
        table.semigroup.eval_map valuation rename identity.lhs
      _ = table.semigroup.eval (fun letter => valuation (rename letter))
            (canonical leftInv) := leftNormalization
      _ = table.semigroup.eval valuation ((canonical leftInv).map rename) :=
        (table.semigroup.eval_map valuation rename (canonical leftInv)).symm
      _ = table.semigroup.eval valuation
            (canonical (mapInvariant rename leftInv)) := by
        rw [canonical_map]
  have rightSound :
      table.semigroup.eval valuation (identity.rhs.map rename) =
        table.semigroup.eval valuation
          (canonical (mapInvariant rename rightInv)) := by
    calc
      table.semigroup.eval valuation (identity.rhs.map rename) =
          table.semigroup.eval (fun letter => valuation (rename letter))
            identity.rhs :=
        table.semigroup.eval_map valuation rename identity.rhs
      _ = table.semigroup.eval (fun letter => valuation (rename letter))
            (canonical rightInv) := rightNormalization
      _ = table.semigroup.eval valuation ((canonical rightInv).map rename) :=
        (table.semigroup.eval_map valuation rename (canonical rightInv)).symm
      _ = table.semigroup.eval valuation
            (canonical (mapInvariant rename rightInv)) := by
        rw [canonical_map]
  exact canonicalDifferent (leftSound.symm.trans (validAt.trans rightSound))

/-- A member endpoint needs only the two executable table checks. -/
theorem basisFor_of_checks
    (table : FiniteTable)
    (modelsChecked : checkModels table = true)
    (separationChecked : checkCanonicalSeparationFour table = true) :
    BasisFor table.semigroup basis := by
  have models := modelsOfCheckModels table modelsChecked
  exact basisForOfInvariantSeparation table.semigroup models
    (invariantSeparation_of_canonicalSeparation table models
      (canonicalSeparation_of_check table separationChecked))

end SemigroupBasis.CoRoots.Order6LeeLiP2G1.Injection
