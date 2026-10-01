import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.S5_107SignatureSemantics
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.Transfer

namespace SemigroupBasis.CoRoots.S6_3944

open SemigroupBasis

/-! ## Lee--Li Proposition 4.3 basis -/

private def word (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := word 0 [0]
def xxx : Word Nat := word 0 [0, 0]
def xyx : Word Nat := word 0 [1, 0]
def xxyx : Word Nat := word 0 [0, 1, 0]
def xyxx : Word Nat := word 0 [1, 0, 0]
def xxyy : Word Nat := word 0 [0, 1, 1]
def yyxx : Word Nat := word 1 [1, 0, 0]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def leftContractionLaw : Identity Nat := ⟨xxyx, xyx⟩
def squareCommutationLaw : Identity Nat := ⟨xxyy, yyxx⟩
def rightExpansionLaw : Identity Nat := ⟨xyx, xyxx⟩

/-- The four identities printed in Lee--Li (2011), Proposition 4.3, in
the order requested by the order-six catalogue campaign. -/
def basis : List (Identity Nat) :=
  [powerLaw, leftContractionLaw, squareCommutationLaw,
    rightExpansionLaw]

/-- The literal word-reversal basis for the opposite endpoint. -/
def oppositeBasis : List (Identity Nat) :=
  [powerLaw, ⟨xyxx, xyx⟩, ⟨yyxx, xxyy⟩, ⟨xyx, xxyx⟩]

theorem reversedBasis_basis :
    reversedBasis basis = oppositeBasis := by
  decide

/-! ## Primitive derivations used by the Lee--Li normalizer -/

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

private theorem basisPower : Derives basis xx xxx :=
  Derives.fromBasis (e := powerLaw) (by simp [basis])

private theorem basisLeftContraction : Derives basis xxyx xyx :=
  Derives.fromBasis (e := leftContractionLaw) (by simp [basis])

private theorem basisSquareCommutation : Derives basis xxyy yyxx :=
  Derives.fromBasis (e := squareCommutationLaw) (by simp [basis])

private theorem basisRightExpansion : Derives basis xyx xyxx :=
  Derives.fromBasis (e := rightExpansionLaw) (by simp [basis])

/-- Duplicate a square block once. -/
theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisPower (instantiateTwoWords u u)
  simpa [xx, xxx, word, instantiateTwoWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Four adjacent copies of a nonempty block contract to two. -/
theorem derivesFourToTwo (u : Word Nat) :
    Derives basis (((u ++ u) ++ u) ++ u) (u ++ u) := by
  have first :=
    Derives.appendRight (Derives.symm (derivesPowerExpansion u)) u
  have fourToThree :
      Derives basis (((u ++ u) ++ u) ++ u) ((u ++ u) ++ u) := by
    simpa [Word.append_assoc] using first
  exact fourToThree.trans
    (Derives.symm (derivesPowerExpansion u))

/-- Duplicate the left displayed occurrence of a repeated block. -/
theorem derivesLeftDuplication (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ u) ++ v) ++ u) := by
  have substituted :=
    Derives.subst (Derives.symm basisLeftContraction)
      (instantiateTwoWords u v)
  simpa [xyx, xxyx, word, instantiateTwoWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Duplicate the right displayed occurrence of a repeated block. -/
theorem derivesRightDuplication (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ v) ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisRightExpansion (instantiateTwoWords u v)
  simpa [xyx, xyxx, word, instantiateTwoWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Commute two adjacent square blocks. -/
theorem derivesSquareBlockCommutation (u v : Word Nat) :
    Derives basis ((u ++ u) ++ (v ++ v))
      ((v ++ v) ++ (u ++ u)) := by
  have substituted :=
    Derives.subst basisSquareCommutation (instantiateTwoWords u v)
  simpa [xxyy, yyxx, word, instantiateTwoWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-! ## Exact catalogue, campaign-route, and published tables -/

private def row6
    (c0 c1 c2 c3 c4 c5 column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- The direct Smallsemi `S6_3944` multiplication. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 1 1 right else
      if left = 2 then row6 0 0 0 0 2 2 right else
        if left = 3 then row6 0 0 1 0 0 3 right else
          if left = 4 then row6 0 1 0 3 4 4 right else
            row6 0 1 2 3 4 5 right

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

/-- Catalogue-facing name for the exact direct representative. -/
abbrev catalogueTable : FiniteTable := table

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (table.mul left right).val + 1

theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 2, 2],
        [1, 1, 1, 1, 3, 3], [1, 1, 2, 1, 1, 4],
        [1, 2, 1, 4, 5, 5], [1, 2, 3, 4, 5, 6]] := by
  decide

/-- SHA-256 of the compact one-based direct catalogue table. -/
def tableSHA256 : String :=
  "075566f291579b7f0d41ba896f2441b094f622abfb330d85fcc9b78efa9bfd45"

/-- The campaign route uses the opposite orientation of `S6_3944`. -/
def routeMul (left right : Fin 6) : Fin 6 := mul right left

def routeTable : FiniteTable where
  order := 6
  mul := routeMul
  assoc := by
    intro a b c
    exact (table.semigroup.assoc c b a).symm

/-- The campaign route table is definitionally the opposite multiplication
of the exact direct catalogue representative. -/
theorem route_mul_eq_catalogue_opposite (left right : Fin 6) :
    routeTable.mul left right = table.mul right left := rfl

def routeTableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (routeTable.mul left right).val + 1

theorem routeTableRowsOneBased_certificate :
    routeTableRowsOneBased =
      [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 2, 2],
        [1, 1, 1, 2, 1, 3], [1, 1, 1, 1, 4, 4],
        [1, 2, 3, 1, 5, 5], [1, 2, 3, 4, 5, 6]] := by
  decide

/-- SHA-256 recorded for the campaign's opposite-orientation I94 source. -/
def routeTableSHA256 : String :=
  "49d03a50f2c9b0e46e016bb2de3218332fb49df453836aad26a0e37162e74742"

/-- The Q1 table printed by Lee--Li, in their element order. -/
def publishedMul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 1 2 0 4 1 right else
      if left = 2 then row6 0 0 0 4 0 2 right else
        if left = 3 then row6 0 3 0 0 0 3 right else
          if left = 4 then row6 0 4 0 0 0 4 right else
            row6 0 1 2 3 4 5 right

def publishedTable : FiniteTable where
  order := 6
  mul := publishedMul
  assoc := by decide

def publishedTableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 =>
      (publishedTable.mul left right).val + 1

theorem publishedTableRowsOneBased_certificate :
    publishedTableRowsOneBased =
      [[1, 1, 1, 1, 1, 1], [1, 2, 3, 1, 5, 2],
        [1, 1, 1, 5, 1, 3], [1, 4, 1, 1, 1, 4],
        [1, 5, 1, 1, 1, 5], [1, 2, 3, 4, 5, 6]] := by
  decide

def publishedTableSHA256 : String :=
  "a3a0df1d6aeb1e676d6714eed863d91833409a6f7995833095c018195b3aa368"

/-- Lee--Li labels to direct catalogue labels, one-based
`[1,5,4,3,2,6]`. -/
def publishedToCatalogueValue (value : Fin 6) : Fin 6 :=
  if value = 0 then 0 else
    if value = 1 then 4 else
      if value = 2 then 3 else
        if value = 3 then 2 else
          if value = 4 then 1 else 5

def catalogueToPublishedValue (value : Fin 6) : Fin 6 :=
  publishedToCatalogueValue value

def publishedToCatalogueValuesOneBased : List Nat :=
  List.ofFn fun value : Fin 6 =>
    (publishedToCatalogueValue value).val + 1

theorem publishedToCatalogueValuesOneBased_certificate :
    publishedToCatalogueValuesOneBased = [1, 5, 4, 3, 2, 6] := by
  decide

@[simp]
theorem catalogueToPublished_publishedToCatalogue (value : Fin 6) :
    catalogueToPublishedValue (publishedToCatalogueValue value) = value := by
  revert value
  decide

@[simp]
theorem publishedToCatalogue_catalogueToPublished (value : Fin 6) :
    publishedToCatalogueValue (catalogueToPublishedValue value) = value := by
  revert value
  decide

def publishedIntoCatalogue :
    Embedding publishedTable.semigroup table.semigroup where
  toFun := publishedToCatalogueValue
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right equality
    have inverseEquality :=
      congrArg catalogueToPublishedValue equality
    simpa using inverseEquality

def catalogueIntoPublished :
    Embedding table.semigroup publishedTable.semigroup where
  toFun := catalogueToPublishedValue
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right equality
    have inverseEquality :=
      congrArg publishedToCatalogueValue equality
    simpa using inverseEquality

theorem sameIdentityTheory_published :
    SameIdentityTheory publishedTable.semigroup table.semigroup := by
  intro identity
  exact ⟨catalogueIntoPublished.pullback_identity identity,
    publishedIntoCatalogue.pullback_identity identity⟩

/-- The unique direct anti-automorphism swaps one-based labels 3 and 4. -/
def selfDualValue (value : Fin 6) : Fin 6 :=
  if value = 2 then 3 else if value = 3 then 2 else value

def selfDualValuesOneBased : List Nat :=
  List.ofFn fun value : Fin 6 => (selfDualValue value).val + 1

theorem selfDualValuesOneBased_certificate :
    selfDualValuesOneBased = [1, 2, 4, 3, 5, 6] := by
  decide

@[simp]
theorem selfDualValue_involutive (value : Fin 6) :
    selfDualValue (selfDualValue value) = value := by
  revert value
  decide

/-- The route's opposite table is bound to the direct representative by an
actual multiplication-preserving bijection, not by its metadata digest. -/
def catalogueIntoRoute :
    Embedding table.semigroup routeTable.semigroup where
  toFun := selfDualValue
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right equality
    have inverseEquality := congrArg selfDualValue equality
    simpa using inverseEquality

def routeIntoCatalogue :
    Embedding routeTable.semigroup table.semigroup where
  toFun := selfDualValue
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right equality
    have inverseEquality := congrArg selfDualValue equality
    simpa using inverseEquality

theorem sameIdentityTheory_route :
    SameIdentityTheory table.semigroup routeTable.semigroup := by
  intro identity
  exact ⟨routeIntoCatalogue.pullback_identity identity,
    catalogueIntoRoute.pullback_identity identity⟩

/-! ## Soundness and the exact five-element Q ideal -/

def toFinTwo : Nat → Fin 2
  | 0 => 0
  | _ => 1

def finiteBasis : List (Identity (Fin 2)) :=
  basis.map fun identity => identity.map toFinTwo

private theorem basisRoundTripChecked :
    basis.all (fun identity =>
      decide ((identity.map toFinTwo).map Fin.val = identity)) = true := by
  decide

private theorem basisRoundTrip
    (identity : Identity Nat) (member : identity ∈ basis) :
    (identity.map toFinTwo).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basisRoundTripChecked) identity member

theorem models_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteBasis.all candidate.checkIdentity = true) :
    Models candidate.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinTwo ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityNat_sound (identity.map toFinTwo)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [basisRoundTrip identity member] at finiteValid
  exact finiteValid

/-- Exhaustive soundness for all four displayed identities on the exact
direct catalogue table. -/
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide)

/-- The first five direct labels are exactly the stored `S5_107` table. -/
def qIdealEmbedding :
    Embedding Generated.Catalogue.S5_107.table.semigroup
      table.semigroup where
  toFun := fun value =>
    ⟨value.val, Nat.lt_trans value.isLt (by decide)⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

def one : Fin 6 := 5

@[simp]
theorem one_mul (value : Fin 6) : mul one value = value := by
  revert value
  decide

@[simp]
theorem mul_one (value : Fin 6) : mul value one = value := by
  revert value
  decide

/-- Every valid identity of Q1 restricts to the public complete
simple-adjacency signature of its five-element Q ideal. -/
theorem valid_sameSimpleAdjacencySignature
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    S5_107.SameSimpleAdjacencySignature
      identity.lhs identity.rhs :=
  S5_107.valid_sameSimpleAdjacencySignature identity
    (qIdealEmbedding.pullback_identity identity valid)

/-! ## Deletion into the Q ideal -/

def evalList (valuation : Nat → Fin 6) (letters : List Nat) : Fin 6 :=
  letters.foldl
    (fun current letter => mul current (valuation letter)) one

def deletionValuation
    (keep : Nat → Bool) (valuation : Nat → Fin 6) : Nat → Fin 6 :=
  fun letter => if keep letter then valuation letter else one

private theorem evalList_toList
    (valuation : Nat → Fin 6) (word : Word Nat) :
    evalList valuation word.toList =
      table.semigroup.eval valuation word := by
  cases word with
  | mk head tail =>
      simp only [evalList, Word.toList, List.foldl_cons, Semigroup.eval]
      rw [one_mul]
      rfl

private theorem foldl_deletionValuation
    (keep : Nat → Bool) (valuation : Nat → Fin 6)
    (letters : List Nat) (initial : Fin 6) :
    letters.foldl
        (fun current letter =>
          mul current (deletionValuation keep valuation letter))
        initial =
      (letters.filter keep).foldl
        (fun current letter => mul current (valuation letter))
        initial := by
  induction letters generalizing initial with
  | nil => rfl
  | cons letter rest induction =>
      simp only [List.foldl_cons, List.filter_cons]
      by_cases kept : keep letter
      · rw [induction]
        simp [deletionValuation, kept]
      · rw [induction]
        simp [deletionValuation, kept, mul_one]

theorem eval_deletionValuation
    (keep : Nat → Bool) (valuation : Nat → Fin 6)
    (word : Word Nat) :
    table.semigroup.eval (deletionValuation keep valuation) word =
      evalList valuation (word.toList.filter keep) := by
  rw [← evalList_toList]
  simp only [evalList]
  exact foldl_deletionValuation keep valuation word.toList one

/-- Assigning the adjoined identity to deleted variables makes every
deletion projection of a valid identity evaluate equally. -/
theorem filtered_eval_equal
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup)
    (keep : Nat → Bool) (valuation : Nat → Fin 6) :
    evalList valuation (identity.lhs.toList.filter keep) =
      evalList valuation (identity.rhs.toList.filter keep) := by
  rw [← eval_deletionValuation, ← eval_deletionValuation]
  exact valid (deletionValuation keep valuation)

/-- A nonempty retained projection is a genuine identity of the embedded
five-element Q table. -/
theorem valid_filtered_s5_107
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup)
    (keep : Nat → Bool)
    (leftHead rightHead : Nat) (leftTail rightTail : List Nat)
    (leftShape :
      identity.lhs.toList.filter keep = leftHead :: leftTail)
    (rightShape :
      identity.rhs.toList.filter keep = rightHead :: rightTail) :
    (Identity.mk
      (S5_107.listWordOfCons leftHead leftTail)
      (S5_107.listWordOfCons rightHead rightTail)).SatisfiedBy
        Generated.Catalogue.S5_107.table.semigroup := by
  intro valuation
  apply qIdealEmbedding.injective
  rw [qIdealEmbedding.toHom.map_eval, qIdealEmbedding.toHom.map_eval]
  rw [← evalList_toList, ← evalList_toList]
  change
    evalList (fun letter => qIdealEmbedding.toFun (valuation letter))
        (leftHead :: leftTail) =
      evalList (fun letter => qIdealEmbedding.toFun (valuation letter))
        (rightHead :: rightTail)
  rw [← leftShape, ← rightShape]
  exact filtered_eval_equal identity valid keep
    (fun letter => qIdealEmbedding.toFun (valuation letter))

/-- Public adjacency data for every nonempty deletion projection. This is
the exact semantic lemma used in Lee--Li's gap-content argument. -/
theorem valid_filtered_sameSimpleAdjacencySignature
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup)
    (keep : Nat → Bool)
    (leftHead rightHead : Nat) (leftTail rightTail : List Nat)
    (leftShape :
      identity.lhs.toList.filter keep = leftHead :: leftTail)
    (rightShape :
      identity.rhs.toList.filter keep = rightHead :: rightTail) :
    S5_107.SameSimpleAdjacencySignature
      (S5_107.listWordOfCons leftHead leftTail)
      (S5_107.listWordOfCons rightHead rightTail) :=
  S5_107.valid_sameSimpleAdjacencySignature _ <|
    valid_filtered_s5_107 identity valid keep
      leftHead rightHead leftTail rightTail leftShape rightShape

end SemigroupBasis.CoRoots.S6_3944
