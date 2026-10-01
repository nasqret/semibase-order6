import SemigroupBasis.CoRoots.Order6Day7.S2_2.SeedS5_803
import SemigroupBasis.CoRoots.Order6Day7.S2_2.SeedS5_402ParitySuccessorBridge
import SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040
import SemigroupBasis.CoRoots.S5_415Semantics

/-!
# Exact rank-040 cyclic-parity / Brandt-endpoint owner boundary

The actual five-element Brandt factor has an unrestricted semantic word
problem: support, endpoint-assignment compatibility, and the exposed initial
and final matrix-unit coordinates.  The actual cyclic-two factor supplies
independent per-letter occurrence parity, with an unrestricted converse.

The three complete lower Brandt axioms all possess displayed whole-square
lifts.  The sandwich lift needs the genuine seven-letter target sandwich
followed by the frozen middle switch.  Unlike rank 039, however, whole-word
squaring is NOT multiplicative in the actual Brandt factor: `(uv)^2 = u^2v^2`
fails at the immutable matrix units `e12,e21`.  Thus the prior structural
square-transport induction cannot be silently reused.

Both previously kernel-green cyclic-family source normalizers are also
unsound on the actual Brandt factor, and unrestricted transport of the
complete lower basis is impossible because its power and sandwich axioms
change cyclic parity.  The genuine owner obligation is therefore precisely
the unrestricted Brandt-signature-plus-parity lift; both classes retain that
explicit premise, and no unconditional class or carrier is asserted.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.BrandtParityBridge

open SemigroupBasis

abbrev SameOccurrenceParity :=
  SemigroupBasis.CoRoots.S5_441Invariant.SameOccurrenceParity

/-- Exactly the independent invariants supplied by the ACTUAL two factors. -/
structure SameFactorSignature (left right : Word Nat) : Prop where
  brandt : SemigroupBasis.CoRoots.S5_415.SameBrandtSignature left right
  parity : SameOccurrenceParity left right

/-- Pair validity yields unrestricted Brandt endpoint connectivity and parity. -/
theorem sameFactorSignature_of_factorValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    SameFactorSignature identity.lhs identity.rhs where
  brandt := SemigroupBasis.CoRoots.S5_415.valid_sameBrandtSignature
    (by exact rightValid)
  parity := SemigroupBasis.CoRoots.S5_441Invariant.sameOccurrenceParity_of_s2_2_valid
    identity leftValid

/-- Independent cyclic completeness reconstructs its genuine factor validity. -/
theorem leftValid_of_sameOccurrenceParity
    (identity : Identity Nat)
    (parity : SameOccurrenceParity identity.lhs identity.rhs) :
    identity.SatisfiedBy leftTable.semigroup :=
  SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank039.ParitySuccessorBridge.leftValid_of_sameOccurrenceParity
    identity parity

/-- The independent matrix-unit semantic theorem reconstructs Brandt validity. -/
theorem rightValid_of_sameBrandtSignature
    (identity : Identity Nat)
    (same : SemigroupBasis.CoRoots.S5_415.SameBrandtSignature
      identity.lhs identity.rhs) :
    identity.SatisfiedBy rightTable.semigroup :=
  SemigroupBasis.CoRoots.S5_415.valid_of_sameBrandtSignature same

/-- Exact factor-pair word problem, with no finite-word-bound inference. -/
theorem factorValid_iff_sameFactorSignature
    (identity : Identity Nat) :
    (identity.SatisfiedBy leftTable.semigroup ∧
      identity.SatisfiedBy rightTable.semigroup) ↔
      SameFactorSignature identity.lhs identity.rhs := by
  constructor
  · rintro ⟨leftValid, rightValid⟩
    exact sameFactorSignature_of_factorValid identity leftValid rightValid
  · intro signature
    exact
      ⟨leftValid_of_sameOccurrenceParity identity signature.parity,
        rightValid_of_sameBrandtSignature identity signature.brandt⟩

/-- Actual `S5_415` matrix units refute the earlier rank-038 prefix law. -/
theorem rank038TriplePrefix_not_rightValid :
    ¬ SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank038.law01.SatisfiedBy
      rightTable.semigroup := by
  intro valid
  have witness := valid
    (fun letter => if letter = 0 then (1 : Fin 5) else (2 : Fin 5))
  change (0 : Fin 5) = 3 at witness
  omega

/-- The complete rank-038 owner normalizer cannot transport to rank 040. -/
theorem rank038DisplayedLawTransport_refuted :
    ¬ (∀ law : Identity Nat,
      law ∈ SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank038.basis →
        Derives basis law.lhs law.rhs) := by
  intro transport
  have derived := transport
    SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank038.law01
    (by simp [SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank038.basis])
  exact rank038TriplePrefix_not_rightValid (derived.sound rightModels)

/-- The independently green rank-001 contraction fails on the same units. -/
theorem rank001TripleSandwich_not_rightValid :
    ¬ SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank001.law01.SatisfiedBy
      rightTable.semigroup := by
  intro valid
  have witness := valid
    (fun letter => if letter = 0 then (1 : Fin 5) else (2 : Fin 5))
  change (0 : Fin 5) = 1 at witness
  omega

/-- The complete rank-001 owner normalizer also cannot transport. -/
theorem rank001DisplayedLawTransport_refuted :
    ¬ (∀ law : Identity Nat,
      law ∈ SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank001.basis →
        Derives basis law.lhs law.rhs) := by
  intro transport
  have derived := transport
    SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank001.law01
    (by simp [SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank001.basis])
  exact rank001TripleSandwich_not_rightValid (derived.sound rightModels)

/-- The first complete Brandt axiom changes actual cyclic occurrence parity. -/
theorem lowerPower_not_leftValid :
    ¬ SemigroupBasis.CoRoots.S5_415.powerLaw.SatisfiedBy
      leftTable.semigroup := by
  intro valid
  have witness := valid (fun _ => (1 : Fin 2))
  change (0 : Fin 2) = 1 at witness
  omega

/-- The second complete Brandt axiom also changes actual cyclic parity. -/
theorem lowerSandwich_not_leftValid :
    ¬ SemigroupBasis.CoRoots.S5_415.sandwichLaw.SatisfiedBy
      leftTable.semigroup := by
  intro valid
  have witness := valid
    (fun letter => if letter = 0 then (1 : Fin 2) else (0 : Fin 2))
  change (0 : Fin 2) = 1 at witness
  omega

/-- Therefore a direct complete-lower-normalizer transport is impossible. -/
theorem fullLowerLawTransport_refuted :
    ¬ (∀ law : Identity Nat,
      law ∈ SemigroupBasis.CoRoots.S5_415.basis →
        Derives basis law.lhs law.rhs) := by
  intro transport
  have derived := transport SemigroupBasis.CoRoots.S5_415.powerLaw
    (by simp [SemigroupBasis.CoRoots.S5_415.basis])
  exact lowerPower_not_leftValid (derived.sound leftModels)

private def instantiateTwo (first second : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | n + 2 => Word.singleton (n + 2)

/-- The genuine index-two/period-two joint law, for arbitrary words. -/
theorem derivesPairExpansion (source : Word Nat) :
    Derives basis
      (source ++ source)
      (((source ++ source) ++ source) ++ source) := by
  have primitive :
      Derives basis (Word.mk 0 [0]) (Word.mk 0 [0, 0, 0]) :=
    Derives.fromBasis (e := law00) (by simp [basis])
  have substituted := Derives.subst primitive
    (instantiateTwo source source)
  simpa [instantiateTwo, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The displayed seven-letter sandwich preserves both occurrence parities. -/
theorem derivesJointSandwichExpansion (first second : Word Nat) :
    Derives basis
      ((first ++ second) ++ first)
      ((((((first ++ second) ++ first) ++ second) ++ first) ++ second) ++
        first) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 0])
        (Word.mk 0 [1, 0, 1, 0, 1, 0]) :=
    Derives.fromBasis (e := law10) (by simp [basis])
  have substituted := Derives.subst primitive
    (instantiateTwo first second)
  simpa [instantiateTwo, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Frozen `xxyx = xyxx`, oriented toward the paired sandwich splice. -/
theorem derivesSandwichMiddleSwitch (first second : Word Nat) :
    Derives basis
      (((first ++ second) ++ first) ++ first)
      (((first ++ first) ++ second) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 1, 0])
        (Word.mk 0 [1, 0, 0]) :=
    Derives.fromBasis (e := law02) (by simp [basis])
  have substituted := Derives.subst primitive.symm
    (instantiateTwo first second)
  simpa [instantiateTwo, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The lower power axiom survives exactly between whole-word squares. -/
theorem derivesLowerPowerSquared (source : Word Nat) :
    Derives basis
      ((source ++ source) ++ (source ++ source))
      (((source ++ source) ++ source) ++
        ((source ++ source) ++ source)) := by
  simpa [Word.append_assoc] using
    Derives.prepend (source ++ source) (derivesPairExpansion source)

/-- The lower sandwich axiom survives between whole squares via exactly the
frozen seven-letter sandwich followed by the genuine middle switch. -/
theorem derivesLowerSandwichSquared
    (first second : Word Nat) :
    Derives basis
      (((first ++ second) ++ first) ++
        ((first ++ second) ++ first))
      (((((first ++ second) ++ first) ++ second) ++ first) ++
        ((((first ++ second) ++ first) ++ second) ++ first)) := by
  have expanded :=
    Derives.appendRight (derivesJointSandwichExpansion first second)
      ((first ++ second) ++ first)
  have expandedAligned :
      Derives basis
        (((first ++ second) ++ first) ++
          ((first ++ second) ++ first))
        (((((first ++ second) ++ first) ++ second) ++
            (((first ++ second) ++ first) ++ first)) ++
          (second ++ first)) := by
    simpa [Word.append_assoc] using expanded
  have switched :=
    Derives.appendRight
      (Derives.prepend (((first ++ second) ++ first) ++ second)
        (derivesSandwichMiddleSwitch first second))
      (second ++ first)
  simpa [Word.append_assoc] using expandedAligned.trans switched

/-- The complete lower square-commutation law is already derivable outright. -/
theorem derivesSquareCommutation (first second : Word Nat) :
    Derives basis
      ((first ++ first) ++ (second ++ second))
      ((second ++ second) ++ (first ++ first)) := by
  have firstPrimitive :
      Derives basis (Word.mk 0 [0, 1, 1])
        (Word.mk 0 [1, 1, 0]) :=
    Derives.fromBasis (e := law04) (by simp [basis])
  have secondPrimitive :
      Derives basis (Word.mk 0 [0, 1, 1])
        (Word.mk 1 [0, 0, 1]) :=
    Derives.fromBasis (e := law05) (by simp [basis])
  have firstStep := Derives.subst firstPrimitive
    (instantiateTwo first second)
  have secondStep := Derives.subst secondPrimitive
    (instantiateTwo second first)
  simpa [instantiateTwo, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using firstStep.trans secondStep.symm

/-- Any already-valid displayed derivation lifts to its whole-word square. -/
theorem squareOfDisplayedDerivation
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    Derives basis (left ++ left) (right ++ right) :=
  (Derives.appendRight derivation left).trans <|
    Derives.prepend right derivation

/-- All THREE independent complete lower Brandt axioms lift between whole
squares, including arbitrary nonempty-word substitution. -/
theorem lowerAxiomSquared
    (identity : Identity Nat)
    (member : identity ∈ SemigroupBasis.CoRoots.S5_415.basis)
    (substitution : Nat → Word Nat) :
    Derives basis
      (identity.lhs.bind substitution ++ identity.lhs.bind substitution)
      (identity.rhs.bind substitution ++ identity.rhs.bind substitution) := by
  simp only [SemigroupBasis.CoRoots.S5_415.basis,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · change
      Derives basis
        ((substitution 0 ++ substitution 0) ++
          (substitution 0 ++ substitution 0))
        (((substitution 0 ++ substitution 0) ++ substitution 0) ++
          ((substitution 0 ++ substitution 0) ++ substitution 0))
    exact derivesLowerPowerSquared (substitution 0)
  · change
      Derives basis
        (((substitution 0 ++ substitution 1) ++ substitution 0) ++
          ((substitution 0 ++ substitution 1) ++ substitution 0))
        (((((substitution 0 ++ substitution 1) ++ substitution 0) ++
              substitution 1) ++ substitution 0) ++
          ((((substitution 0 ++ substitution 1) ++ substitution 0) ++
            substitution 1) ++ substitution 0))
    exact derivesLowerSandwichSquared (substitution 0) (substitution 1)
  · change
      Derives basis
        ((((substitution 0 ++ substitution 0) ++ substitution 1) ++
            substitution 1) ++
          (((substitution 0 ++ substitution 0) ++ substitution 1) ++
            substitution 1))
        ((((substitution 1 ++ substitution 1) ++ substitution 0) ++
            substitution 0) ++
          (((substitution 1 ++ substitution 1) ++ substitution 0) ++
            substitution 0))
    simpa [Word.append_assoc] using
      squareOfDisplayedDerivation
        (derivesSquareCommutation (substitution 0) (substitution 1))

/-- Whole-square multiplicativity, which was valid for rank 039. -/
def squareFactorizationLaw : Identity Nat :=
  ⟨Word.mk 0 [1, 0, 1], Word.mk 0 [0, 1, 1]⟩

/-- Actual Brandt units `e12,e21` give `(xy)^2=e11`, but `x²y²=0`. -/
theorem squareFactorization_not_rightValid :
    ¬ squareFactorizationLaw.SatisfiedBy rightTable.semigroup := by
  intro valid
  have witness := valid
    (fun letter => if letter = 0 then (1 : Fin 5) else (2 : Fin 5))
  change (3 : Fin 5) = 0 at witness
  omega

/-- Displayed soundness forbids importing the rank-039 square factorization. -/
theorem squareFactorization_not_displayedDerivable :
    ¬ Derives basis squareFactorizationLaw.lhs squareFactorizationLaw.rhs := by
  intro derivation
  exact squareFactorization_not_rightValid (derivation.sound rightModels)

/-- Therefore the previous whole-square structural-transport induction is
mathematically unavailable for the actual Brandt target. -/
theorem rank039SquareFactorizationTransport_refuted :
    ¬ (∀ first second : Word Nat,
      Derives basis
        ((first ++ second) ++ (first ++ second))
        ((first ++ first) ++ (second ++ second))) := by
  intro transport
  have witness := transport (Word.singleton 0) (Word.singleton 1)
  exact squareFactorization_not_displayedDerivable (by
    simpa [squareFactorizationLaw, Word.singleton, Word.append] using witness)

/-- Exact missing unrestricted owner proof for the ACTUAL complete factor
signatures.  This premise is never stamped or weakened. -/
def BrandtParityLift : Prop :=
  ∀ identity : Identity Nat,
    SemigroupBasis.CoRoots.S5_415.SameBrandtSignature
      identity.lhs identity.rhs →
    SameOccurrenceParity identity.lhs identity.rhs →
      Derives basis identity.lhs identity.rhs

/-- A supplied genuine owner lift yields the collision-safe intersection. -/
def intersectionBasis_of_ownerLift
    (owner : BrandtParityLift) :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := by
    intro identity leftValid rightValid
    have signature := sameFactorSignature_of_factorValid
      identity leftValid rightValid
    exact owner identity signature.brandt signature.parity

/-- The missing lift is EQUIVALENT to genuine unrestricted pair completeness. -/
theorem targetIntersection_iff_ownerLift :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis ↔
      BrandtParityLift := by
  constructor
  · intro intersection identity brandt parity
    exact intersection.complete identity
      (leftValid_of_sameOccurrenceParity identity parity)
      (rightValid_of_sameBrandtSignature identity brandt)
  · exact intersectionBasis_of_ownerLift

/-- Reviewed quotient normalization remains strictly CONDITIONAL. -/
noncomputable def normalizer_of_ownerLift
    (owner : BrandtParityLift) :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    (intersectionBasis_of_ownerLift owner)

/-- First class, only under the explicit unrestricted Brandt/parity lift. -/
theorem s6_4103_representative_basis_of_ownerLift
    (owner : BrandtParityLift) :
    BasisFor S6_4103.table.semigroup basis :=
  S6_4103.representative_basis_of_normalizer
    (normalizer_of_ownerLift owner)

/-- Opposite of the first class, under the same explicit owner premise. -/
theorem s6_4103_opposite_basis_of_ownerLift
    (owner : BrandtParityLift) :
    BasisFor S6_4103.table.semigroup.opposite (reversedBasis basis) :=
  S6_4103.opposite_basis_of_normalizer
    (normalizer_of_ownerLift owner)

/-- Second class, still conditional on the SAME missing owner proof. -/
theorem s6_4309_representative_basis_of_ownerLift
    (owner : BrandtParityLift) :
    BasisFor S6_4309.table.semigroup basis :=
  S6_4309.representative_basis_of_normalizer
    (normalizer_of_ownerLift owner)

/-- Opposite of the second class; no acceptance or sealing is asserted. -/
theorem s6_4309_opposite_basis_of_ownerLift
    (owner : BrandtParityLift) :
    BasisFor S6_4309.table.semigroup.opposite (reversedBasis basis) :=
  S6_4309.opposite_basis_of_normalizer
    (normalizer_of_ownerLift owner)

end SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.BrandtParityBridge
