import SemigroupBasis.FiniteReflection
import SemigroupBasis.FiniteNilpotent
import SemigroupBasis.FiniteVariableRenaming

namespace SemigroupBasis

namespace FiniteVariableRenaming

/-- The normalized words packaged as an identity over `Nat`. -/
def normalizeIdentity [DecidableEq α] (left right : Word α) : Identity Nat :=
  let result := normalize left right
  ⟨result.left, result.right⟩

/-- A normalized identity has the expected restricted-growth pattern. -/
theorem normalizeIdentity_isRestrictedGrowth [DecidableEq α]
    (left right : Word α) :
    IsRestrictedGrowth
      ((normalizeIdentity left right).lhs.toList ++
        (normalizeIdentity left right).rhs.toList) := by
  simpa only [normalizeIdentity, Result.pattern] using
    normalize_isRestrictedGrowth left right

/-- Validity is preserved when a word pair is simultaneously normalized. -/
theorem normalize_valid [DecidableEq α] (G : Semigroup S)
    (left right : Word α)
    (valid :
      ∀ valuation : α → S,
        G.eval valuation left = G.eval valuation right) :
    let result := normalize left right
    ∀ valuation : Nat → S,
      G.eval valuation result.left = G.eval valuation result.right := by
  let result := normalize left right
  change ∀ valuation : Nat → S,
    G.eval valuation result.left = G.eval valuation result.right
  have normalizes := normalize_normalizes left right
  intro valuation
  rw [← normalizes.1, ← normalizes.2]
  simpa only [Semigroup.eval_map] using
    valid (fun letter => valuation (result.forward letter))

/-- Validity packaged for the normalized `Identity`. -/
theorem normalizeIdentity_valid [DecidableEq α] (G : Semigroup S)
    (left right : Word α)
    (valid : (⟨left, right⟩ : Identity α).SatisfiedBy G) :
    (normalizeIdentity left right).SatisfiedBy G := by
  simpa only [normalizeIdentity, Identity.SatisfiedBy] using
    normalize_valid G left right valid

/-- Reconstruct a derivation from the normalized representative. -/
theorem derives_of_normalize {basis : List (Identity Nat)}
    (left right : Word Nat)
    (derivation :
      Derives basis
        (normalizeIdentity left right).lhs
        (normalizeIdentity left right).rhs) :
    Derives basis left right := by
  let result := normalize left right
  have normalized : Derives basis result.left result.right := by
    simpa only [normalizeIdentity, result] using derivation
  have reconstructs :
      result.left.map result.inverse = left ∧
        result.right.map result.inverse = right := by
    simpa only [result] using normalize_reconstructs left right
  have renamed := Derives.rename normalized result.inverse
  rw [reconstructs.1, reconstructs.2] at renamed
  exact renamed

/-- Reconstruct a derivation when the stored representative has swapped sides. -/
theorem derives_of_normalize_swapped {basis : List (Identity Nat)}
    (left right : Word Nat)
    (derivation :
      Derives basis
        (normalizeIdentity right left).lhs
        (normalizeIdentity right left).rhs) :
    Derives basis left right :=
  Derives.symm (derives_of_normalize right left derivation)

end FiniteVariableRenaming

namespace FiniteTable

/-- Exhaustive finite-table checking is complete as well as sound. -/
theorem checkIdentity_complete (T : FiniteTable)
    (e : Identity (Fin variables)) (h : e.SatisfiedBy T.semigroup) :
    T.checkIdentity e = true := by
  unfold checkIdentity
  apply List.all_eq_true.mpr
  intro valuation _
  exact decide_eq_true (h valuation)

theorem checkIdentity_eq_true_iff (T : FiniteTable)
    (e : Identity (Fin variables)) :
    T.checkIdentity e = true ↔ e.SatisfiedBy T.semigroup :=
  ⟨T.checkIdentity_sound e, T.checkIdentity_complete e⟩

end FiniteTable

namespace FiniteCertificate

/-- A predicate selecting the bounded identity pairs covered by an inventory. -/
abbrev PairShape := Word Nat → Word Nat → Prop

/-- Every listed identity has a restricted-growth variable pattern. -/
def AllRestrictedGrowth (identities : List (Identity Nat)) : Prop :=
  ∀ identity, identity ∈ identities →
    FiniteVariableRenaming.IsRestrictedGrowth
      (identity.lhs.toList ++ identity.rhs.toList)

/-- Every listed identity is valid in the exact finite table. -/
def AllTableValid (T : FiniteTable)
    (identities : List (Identity Nat)) : Prop :=
  ∀ identity, identity ∈ identities →
    identity.SatisfiedBy T.semigroup

/-- Every listed identity has a derivation from `basis`. -/
def DerivesAll (basis identities : List (Identity Nat)) : Prop :=
  ∀ identity, identity ∈ identities →
    Derives basis identity.lhs identity.rhs

/--
Check a list of natural-variable identities by mapping it into a finite
variable type.  The round-trip conjunct is essential: without it, collapsing
two natural variable names to the same finite name would prove the wrong
identity.
-/
def checkModels (T : FiniteTable) (basis : List (Identity Nat))
    (toFinite : Nat → Fin variables) : Bool :=
  basis.all fun identity =>
    decide ((identity.map toFinite).map Fin.val = identity) &&
      T.checkIdentity (identity.map toFinite)

/-- Exhaustive finite checks plus the checked variable-name round trip imply
that the exact natural-variable basis is sound for the table. -/
theorem checkModels_sound (T : FiniteTable) (basis : List (Identity Nat))
    (toFinite : Nat → Fin variables)
    (checked : checkModels T basis toFinite = true) :
    Models T.semigroup basis := by
  intro identity member
  have identityChecked :=
    (List.all_eq_true.mp checked) identity member
  simp only [Bool.and_eq_true] at identityChecked
  have roundTrip :
      (identity.map toFinite).map Fin.val = identity :=
    of_decide_eq_true identityChecked.1
  have finiteValid :=
    T.checkIdentityNat_sound (identity.map toFinite) identityChecked.2
  rw [roundTrip] at finiteValid
  exact finiteValid

/--
An exact finite-table inventory of nonreflexive bounded identities, modulo
simultaneous variable renaming and equality-side symmetry. Literal reflexive
pairs are discharged generically by `RestrictedGrowthInventory.derives` and
therefore need no inventory row.

The two alternatives in `complete` independently normalize the two
orientations. This matches canonical inventories that choose one representative
after comparing `u = v` with a separately normalized `v = u`.
-/
structure RestrictedGrowthInventory (T : FiniteTable) (shape : PairShape) where
  identities : List (Identity Nat)
  restrictedGrowth : AllRestrictedGrowth identities
  tableValid : AllTableValid T identities
  complete :
    ∀ left right,
      left ≠ right →
      shape left right →
      (⟨left, right⟩ : Identity Nat).SatisfiedBy T.semigroup →
      FiniteVariableRenaming.normalizeIdentity left right ∈ identities ∨
        FiniteVariableRenaming.normalizeIdentity right left ∈ identities

namespace RestrictedGrowthInventory

/-- The inventory itself is a sound list of identities for the finite table. -/
theorem models (inventory : RestrictedGrowthInventory T shape) :
    Models T.semigroup inventory.identities :=
  inventory.tableValid

/--
Reduce every valid bounded identity to the finite family of listed derivation
obligations. The direct case uses the normalizer's inverse renaming; the other
case additionally uses symmetry.
-/
theorem derives (inventory : RestrictedGrowthInventory T shape)
    {basis : List (Identity Nat)}
    (listed : DerivesAll basis inventory.identities)
    {left right : Word Nat} (bounded : shape left right)
    (valid : (⟨left, right⟩ : Identity Nat).SatisfiedBy T.semigroup) :
    Derives basis left right := by
  by_cases reflexive : left = right
  · subst right
    exact Derives.refl left
  · rcases inventory.complete left right reflexive bounded valid with
      direct | swapped
    · exact FiniteVariableRenaming.derives_of_normalize left right
        (listed _ direct)
    · exact FiniteVariableRenaming.derives_of_normalize_swapped left right
        (listed _ swapped)

end RestrictedGrowthInventory

end FiniteCertificate

end SemigroupBasis
