import SemigroupBasis.CoRoots.S5_804Completeness
import SemigroupBasis.CoRoots.S5_868MaximalFactors

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeA2LatticeScaffold

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xyx : Word Nat := w 0 [1, 0]
def xyxyx : Word Nat := w 0 [1, 0, 1, 0]
def xyxzx : Word Nat := w 0 [1, 0, 2, 0]
def xzxyx : Word Nat := w 0 [2, 0, 1, 0]
def xyyx : Word Nat := w 0 [1, 1, 0]

def powerContractionLaw : Identity Nat := ⟨xxx, xx⟩
def sandwichContractionLaw : Identity Nat := ⟨xyxyx, xyx⟩
def graphSwitchLaw : Identity Nat := ⟨xyxzx, xzxyx⟩
def middleContractionLaw : Identity Nat := ⟨xyyx, xyx⟩

/-- Lee's `I2, top, top` basis in the orientation recorded by the order-six
packet: `xxx = xx`, `xyxyx = xyx`, `xyxzx = xzxyx`, and `xyyx = xyx`. -/
def basis : List (Identity Nat) :=
  [powerContractionLaw, sandwichContractionLaw, graphSwitchLaw,
    middleContractionLaw]

def toFinThree : Nat -> Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

def finiteBasis : List (Identity (Fin 3)) :=
  basis.map fun identity => identity.map toFinThree

private theorem basis_roundTrip_checked :
    basis.all (fun identity =>
      decide ((identity.map toFinThree).map Fin.val = identity)) = true := by
  decide

private theorem basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ basis) :
    (identity.map toFinThree).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basis_roundTrip_checked) identity member

/-- Lift the exhaustive checks on the three displayed variables to the
repository's unrestricted natural-number variable type. -/
theorem models_of_finite_checks
    (table : FiniteTable)
    (checked : finiteBasis.all table.checkIdentity = true) :
    Models table.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinThree ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    table.checkIdentityNat_sound (identity.map toFinThree)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [basis_roundTrip identity member] at finiteValid
  exact finiteValid

/-! ## Reuse of the completed S5_868 marked-digraph theory -/

/-- Every ambient `S5_868` law is derivable from the four displayed laws. -/
theorem s5_868LawDerives
    (identity : Identity Nat)
    (member : identity ∈ SemigroupBasis.CoRoots.S5_868.basis) :
    Derives basis identity.lhs identity.rhs := by
  simp only [SemigroupBasis.CoRoots.S5_868.basis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · change Derives basis xx xxx
    exact
      (Derives.fromBasis (e := powerContractionLaw)
        (by simp [basis])).symm
  · change Derives basis xyx xyxyx
    exact
      (Derives.fromBasis (e := sandwichContractionLaw)
        (by simp [basis])).symm
  · change Derives basis xyxzx xzxyx
    exact Derives.fromBasis (e := graphSwitchLaw) (by simp [basis])

/-- Transport any completed `S5_868` derivation to the four-law theory. -/
theorem transportS5_868Derivation
    {left right : Word Nat}
    (derivation :
      Derives SemigroupBasis.CoRoots.S5_868.basis left right) :
    Derives basis left right :=
  Derives.transport s5_868LawDerives derivation

/-- Same marked directed graph is already a sufficient condition. The
missing Aristotle theorem must weaken this to the bidirectional connected-cut
signature below. -/
theorem derivesOfSameMarkedDigraph
    {left right : Word Nat}
    (same : left.SameMarkedDigraph right) :
    Derives basis left right :=
  transportS5_868Derivation
    (SemigroupBasis.CoRoots.S5_868.markedDigraphDerivationalCompleteness
      left right same)

private def instantiateThreeWords
    (u v z : Word Nat) : Nat -> Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

/-- Substitute arbitrary nonempty words into `xyyx = xyx`. -/
theorem derivesMiddleContraction (u v : Word Nat) :
    Derives basis
      (((u ++ v) ++ v) ++ u)
      ((u ++ v) ++ u) := by
  have base : Derives basis xyyx xyx :=
    Derives.fromBasis (e := middleContractionLaw) (by simp [basis])
  have substituted :=
    Derives.subst base
      (instantiateThreeWords u v (Word.singleton 2))
  simpa [middleContractionLaw, xyyx, xyx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Insert a second copy of a middle block inside matching endpoints. -/
theorem derivesMiddleExpansion (u v : Word Nat) :
    Derives basis
      ((u ++ v) ++ u)
      (((u ++ v) ++ v) ++ u) :=
  (derivesMiddleContraction u v).symm

/-! ## Exact semantic boundary of the missing theorem -/

abbrev detectorTable : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S5_804.table

/-- Equality of the direct `S5_804` connected-cut signature and its reversed
counterpart. This is the exact semantic intersection detected in the three
order-six targets below. -/
def SameBidirectionalConnectedCutSignature
    (left right : Word Nat) : Prop :=
  SemigroupBasis.CoRoots.S5_804.SameConnectedCutSignature left right ∧
    SemigroupBasis.CoRoots.S5_804.SameConnectedCutSignature
      left.reverse right.reverse

/-- Validity in the direct and opposite detector tables supplies the exact
signature consumed by the missing unrestricted derivational theorem. -/
theorem sameBidirectionalConnectedCutSignature_of_detectorValidity
    (identity : Identity Nat)
    (directValid : identity.SatisfiedBy detectorTable.semigroup)
    (oppositeValid : identity.SatisfiedBy detectorTable.semigroup.opposite) :
    SameBidirectionalConnectedCutSignature identity.lhs identity.rhs := by
  refine
    ⟨SemigroupBasis.CoRoots.S5_804.valid_sameConnectedCutSignature
      identity directValid, ?_⟩
  have reversedValid :
      identity.reversed.SatisfiedBy detectorTable.semigroup :=
    (Identity.satisfiedBy_opposite_iff_reversed
      identity detectorTable.semigroup).mp oppositeValid
  have reversedSignature :=
    SemigroupBasis.CoRoots.S5_804.valid_sameConnectedCutSignature
      identity.reversed reversedValid
  simpa [Identity.reversed] using reversedSignature

/-! ## Three exact order-six targets and finite evidence -/

private def row6
    (c0 c1 c2 c3 c4 c5 column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

namespace S6_13403

/-- Exact zero-based form of Smallsemi `(6, 13403)`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then row6 0 0 0 0 0 0 b else
    if a = 1 then row6 0 0 0 0 1 1 b else
      if a = 2 then row6 0 1 2 3 0 0 b else
        if a = 3 then row6 0 1 2 3 0 1 b else
          if a = 4 then row6 0 0 0 0 4 4 b else
            row6 0 0 0 0 5 5 b

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "76b18618fc5475756e0febee447956f3e9ec577d477f9008e0e2baff9e781574"

set_option maxHeartbeats 0 in
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide)

def directDetector :
    Embedding detectorTable.semigroup table.semigroup where
  toFun := fun value : Fin 5 =>
    if value = 0 then (0 : Fin 6) else
      if value = 1 then (1 : Fin 6) else
        if value = 2 then (2 : Fin 6) else
          if value = 3 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

def oppositeDetector :
    Embedding detectorTable.semigroup.opposite table.semigroup where
  toFun := fun value : Fin 5 =>
    if value = 0 then (0 : Fin 6) else
      if value = 1 then (1 : Fin 6) else
        if value = 2 then (4 : Fin 6) else
          if value = 3 then (5 : Fin 6) else (3 : Fin 6)
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

end S6_13403

namespace S6_13408

/-- Exact zero-based form of Smallsemi `(6, 13408)`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then row6 0 0 0 0 0 0 b else
    if a = 1 then row6 0 0 0 0 1 1 b else
      if a = 2 then row6 0 1 2 3 0 1 b else
        if a = 3 then row6 0 1 2 3 1 0 b else
          if a = 4 then row6 0 0 0 0 4 4 b else
            row6 0 0 0 0 5 5 b

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "0e42ac4ceba1ea0c0da425640042be20c0a7167731a2868fb6e959b1850f18eb"

set_option maxHeartbeats 0 in
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide)

def directDetector :
    Embedding detectorTable.semigroup table.semigroup where
  toFun := fun value : Fin 5 =>
    if value = 0 then (0 : Fin 6) else
      if value = 1 then (1 : Fin 6) else
        if value = 2 then (2 : Fin 6) else
          if value = 3 then (3 : Fin 6) else (4 : Fin 6)
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

def oppositeDetector :
    Embedding detectorTable.semigroup.opposite table.semigroup where
  toFun := fun value : Fin 5 =>
    if value = 0 then (0 : Fin 6) else
      if value = 1 then (1 : Fin 6) else
        if value = 2 then (4 : Fin 6) else
          if value = 3 then (5 : Fin 6) else (2 : Fin 6)
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

end S6_13408

namespace S6_13409

/-- Exact zero-based form of Smallsemi `(6, 13409)`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then row6 0 0 0 0 0 0 b else
    if a = 1 then row6 0 0 0 0 1 1 b else
      if a = 2 then row6 0 1 2 3 0 1 b else
        if a = 3 then row6 0 1 2 3 1 1 b else
          if a = 4 then row6 0 0 0 0 4 4 b else
            row6 0 0 0 0 5 5 b

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "5f77b2673e4e95a52a892a757092d581f71cab71d923e2555e524af1ce3f903f"

set_option maxHeartbeats 0 in
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide)

def directDetector :
    Embedding detectorTable.semigroup table.semigroup where
  toFun := fun value : Fin 5 =>
    if value = 0 then (0 : Fin 6) else
      if value = 1 then (1 : Fin 6) else
        if value = 2 then (2 : Fin 6) else
          if value = 3 then (3 : Fin 6) else (4 : Fin 6)
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

def oppositeDetector :
    Embedding detectorTable.semigroup.opposite table.semigroup where
  toFun := fun value : Fin 5 =>
    if value = 0 then (0 : Fin 6) else
      if value = 1 then (1 : Fin 6) else
        if value = 2 then (4 : Fin 6) else
          if value = 3 then (5 : Fin 6) else (2 : Fin 6)
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

end S6_13409

/-- Finite evidence accepted by the endpoint wrapper. It contains no
completeness premise or unbounded word-problem claim. -/
structure TargetEvidence (table : FiniteTable) where
  models : Models table.semigroup basis
  directDetector : Embedding detectorTable.semigroup table.semigroup
  oppositeDetector :
    Embedding detectorTable.semigroup.opposite table.semigroup

def S6_13403.evidence : TargetEvidence S6_13403.table where
  models := S6_13403.models
  directDetector := S6_13403.directDetector
  oppositeDetector := S6_13403.oppositeDetector

def S6_13408.evidence : TargetEvidence S6_13408.table where
  models := S6_13408.models
  directDetector := S6_13408.directDetector
  oppositeDetector := S6_13408.oppositeDetector

def S6_13409.evidence : TargetEvidence S6_13409.table where
  models := S6_13409.models
  directDetector := S6_13409.directDetector
  oppositeDetector := S6_13409.oppositeDetector

/-- A proof of the sole Aristotle obligation converts the finite evidence
for any target into an unrestricted `BasisFor` theorem. -/
theorem basisFor_of_targetEvidence
    (complete :
      ∀ {left right : Word Nat},
        SameBidirectionalConnectedCutSignature left right ->
          Derives basis left right)
    {table : FiniteTable} (evidence : TargetEvidence table) :
    BasisFor table.semigroup basis := by
  refine ⟨evidence.models, ?_⟩
  intro identity valid
  apply complete
  exact sameBidirectionalConnectedCutSignature_of_detectorValidity
    identity
    (evidence.directDetector.pullback_identity identity valid)
    (evidence.oppositeDetector.pullback_identity identity valid)

/-- Formal endpoint bridge for all three common-signature roots. There is no
remaining lattice-classification premise after the derivational theorem. -/
theorem signature4TargetsBasisFor_of_derivationalCompleteness
    (complete :
      ∀ {left right : Word Nat},
        SameBidirectionalConnectedCutSignature left right ->
          Derives basis left right) :
    BasisFor S6_13403.table.semigroup basis ∧
      BasisFor S6_13408.table.semigroup basis ∧
        BasisFor S6_13409.table.semigroup basis := by
  exact
    ⟨basisFor_of_targetEvidence complete S6_13403.evidence,
      basisFor_of_targetEvidence complete S6_13408.evidence,
      basisFor_of_targetEvidence complete S6_13409.evidence⟩

end SemigroupBasis.CoRoots.Order6LeeA2LatticeScaffold
