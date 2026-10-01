import SemigroupBasis.Examples.SymmetricThreeCompletenessSquareKernel

namespace SemigroupBasis.Examples.SymmetricThreeCompleteness

open SemigroupBasis

local infixl:70 " *t " => termMul.mul

/-- Toggle one letter in a canonical parity state. -/
def toggleState (state : List Nat) (letter : Nat) : List Nat :=
  canonicalParity (state ++ [letter])

/-- A transition key stores its letter in the head and the parity state before
the transition in its tail. -/
def transitionKey (state : List Nat) (letter : Nat) : Word Nat :=
  ⟨letter, state⟩

@[simp]
theorem transitionKey_head (state : List Nat) (letter : Nat) :
    (transitionKey state letter).head = letter :=
  rfl

@[simp]
theorem transitionKey_tail (state : List Nat) (letter : Nat) :
    (transitionKey state letter).tail = state :=
  rfl

/-- Scan a letter list and record every directed hypercube transition. -/
def transitionKeysFrom : List Nat → List Nat → List (Word Nat)
  | _, [] => []
  | state, letter :: rest =>
      transitionKey state letter ::
        transitionKeysFrom (toggleState state letter) rest

/-- Final parity state reached by the same scan. -/
def finalStateFrom : List Nat → List Nat → List Nat
  | state, [] => state
  | state, letter :: rest =>
      finalStateFrom (toggleState state letter) rest

/-- Reidemeister--Schreier generator attached to one directed transition. -/
def schreier (key : Word Nat) : Term :=
  let state := key.tail
  let letter := key.head
  let next := toggleState state letter
  (headProduct state *t generator letter) *t inv (headProduct next)

/-- The defining Schreier factorization of one transition. -/
theorem schreier_mul_nextHead (state : List Nat) (letter : Nat) :
    schreier (transitionKey state letter) *t
        headProduct (toggleState state letter) =
      headProduct state *t generator letter := by
  simp only [schreier, transitionKey_head, transitionKey_tail]
  exact inv_mul_cancel_right
    (headProduct state *t generator letter)
    (headProduct (toggleState state letter))

/-- Each Schreier generator lies in the square kernel. -/
theorem schreier_equivalent_one (key : Word Nat) :
    SquareEquivalent (schreier key) one := by
  let state := key.tail
  let letter := key.head
  let next := toggleState state letter
  have appendShape :
      headProduct state *t generator letter =
        headProduct (state ++ [letter]) := by
    rw [headProduct_append]
    simp only [headProduct_cons, headProduct_nil, mul_one]
  have normalized :
      SquareEquivalent
        (headProduct state *t generator letter)
        (headProduct next) := by
    rw [appendShape]
    exact headProduct_canonicalParity (state ++ [letter])
  have withInverse := normalized.mul_right (inv (headProduct next))
  change SquareEquivalent (schreier key)
    (headProduct next *t inv (headProduct next)) at withInverse
  simpa only [mul_inv] using withInverse

theorem schreier_exists_squareProduct (key : Word Nat) :
    ∃ payload, schreier key = squareProduct payload := by
  obtain ⟨payload, equality⟩ := schreier_equivalent_one key
  refine ⟨payload, ?_⟩
  simpa only [mul_one] using equality

theorem schreier_comm (left right : Word Nat) :
    schreier left *t schreier right =
      schreier right *t schreier left := by
  obtain ⟨leftPayload, leftEq⟩ :=
    schreier_exists_squareProduct left
  obtain ⟨rightPayload, rightEq⟩ :=
    schreier_exists_squareProduct right
  rw [leftEq, rightEq]
  exact squareProduct_comm leftPayload rightPayload

private theorem cube_mul_of_comm
    (left right : Term)
    (commutes : left *t right = right *t left) :
    (left *t right) *t ((left *t right) *t (left *t right)) =
      (left *t (left *t left)) *t
        (right *t (right *t right)) := by
  calc
    (left *t right) *t ((left *t right) *t (left *t right)) =
        left *t
          (right *t (left *t (right *t (left *t right)))) := by
      simp only [termMul.assoc]
    _ = left *t
          (left *t (right *t (right *t (left *t right)))) := by
      congr 1
      calc
        right *t (left *t (right *t (left *t right))) =
            (right *t left) *t (right *t (left *t right)) :=
          (termMul.assoc _ _ _).symm
        _ = (left *t right) *t (right *t (left *t right)) := by
          rw [← commutes]
        _ = left *t (right *t (right *t (left *t right))) :=
          termMul.assoc _ _ _
    _ = left *t
          (left *t (left *t (right *t (right *t right)))) := by
      congr 1
      congr 1
      calc
        right *t (right *t (left *t right)) =
            right *t ((right *t left) *t right) := by
          rw [termMul.assoc]
        _ = right *t ((left *t right) *t right) := by
          rw [← commutes]
        _ = right *t (left *t (right *t right)) := by
          rw [termMul.assoc]
        _ = (right *t left) *t (right *t right) :=
          (termMul.assoc _ _ _).symm
        _ = (left *t right) *t (right *t right) := by
          rw [← commutes]
        _ = left *t (right *t (right *t right)) :=
          termMul.assoc _ _ _
    _ = (left *t (left *t left)) *t
          (right *t (right *t right)) := by
      simp only [termMul.assoc]

theorem squareProduct_cube_eq_one (payload : List Term) :
    squareProduct payload *t
        (squareProduct payload *t squareProduct payload) = one := by
  induction payload with
  | nil =>
      simp only [squareProduct_nil, one_mul]
  | cons value rest inductionHypothesis =>
      rw [squareProduct_cons]
      rw [cube_mul_of_comm
        (square value) (squareProduct rest)
        (square_comm_squareProduct value rest)]
      rw [square_cube_eq_one, inductionHypothesis, one_mul]

theorem schreier_cube_eq_one (key : Word Nat) :
    schreier key *t (schreier key *t schreier key) = one := by
  obtain ⟨payload, equality⟩ := schreier_exists_squareProduct key
  rw [equality]
  exact squareProduct_cube_eq_one payload

/-- Product of Schreier generators in scan order. -/
def schreierProduct : List (Word Nat) → Term
  | [] => one
  | key :: rest => schreier key *t schreierProduct rest

@[simp]
theorem schreierProduct_nil : schreierProduct [] = one :=
  rfl

@[simp]
theorem schreierProduct_cons (key : Word Nat)
    (rest : List (Word Nat)) :
    schreierProduct (key :: rest) =
      schreier key *t schreierProduct rest :=
  rfl

theorem schreier_comm_product (key : Word Nat)
    (keys : List (Word Nat)) :
    schreier key *t schreierProduct keys =
      schreierProduct keys *t schreier key := by
  induction keys with
  | nil =>
      simp only [schreierProduct_nil, mul_one, one_mul]
  | cons next rest inductionHypothesis =>
      simp only [schreierProduct_cons]
      calc
        schreier key *t (schreier next *t schreierProduct rest) =
            (schreier key *t schreier next) *t
              schreierProduct rest :=
          (termMul.assoc _ _ _).symm
        _ = (schreier next *t schreier key) *t
              schreierProduct rest := by
          rw [schreier_comm]
        _ = schreier next *t
              (schreier key *t schreierProduct rest) :=
          termMul.assoc _ _ _
        _ = schreier next *t
              (schreierProduct rest *t schreier key) := by
          rw [inductionHypothesis]
        _ = (schreier next *t schreierProduct rest) *t
              schreier key :=
          (termMul.assoc _ _ _).symm

theorem schreierProduct_perm {left right : List (Word Nat)}
    (permutation : left.Perm right) :
    schreierProduct left = schreierProduct right := by
  induction permutation with
  | nil => rfl
  | cons key _ inductionHypothesis =>
      simp only [schreierProduct_cons, inductionHypothesis]
  | swap left right rest =>
      simp only [schreierProduct_cons]
      rw [← termMul.assoc, schreier_comm right left, termMul.assoc]
  | trans _ _ first second => exact first.trans second

private theorem two_key_copies_perm
    (key : Word Nat) (keys : List (Word Nat))
    (count : keys.count key = 2) :
    keys.Perm (key :: key :: (keys.erase key).erase key) := by
  have member : key ∈ keys := List.count_pos_iff.mp (by omega)
  have first := List.perm_cons_erase member
  have erasedCount : (keys.erase key).count key = 1 := by
    rw [List.count_erase_self]
    omega
  have erasedMember : key ∈ keys.erase key :=
    List.count_pos_iff.mp (by omega)
  exact first.trans
    (List.Perm.cons key (List.perm_cons_erase erasedMember))

/-- Reduce every Schreier multiplicity modulo three. -/
theorem schreierProduct_reduction :
    ∀ keys : List (Word Nat),
      schreierProduct keys =
        schreierProduct (symmetricThreeTernaryReduce keys)
  | [] => rfl
  | key :: rest => by
      rw [schreierProduct_cons,
        schreierProduct_reduction rest]
      by_cases countBound :
          (symmetricThreeTernaryReduce rest).count key < 2
      · simp [symmetricThreeTernaryReduce, countBound,
          schreierProduct_cons]
      · have reducedBound :
            (symmetricThreeTernaryReduce rest).count key < 3 := by
          rw [symmetricThreeCountTernaryReduce key rest]
          exact Nat.mod_lt _ (by decide)
        have reducedCount :
            (symmetricThreeTernaryReduce rest).count key = 2 := by
          omega
        let remainder :=
          ((symmetricThreeTernaryReduce rest).erase key).erase key
        have permutation :
            (symmetricThreeTernaryReduce rest).Perm
              (key :: key :: remainder) := by
          simpa [remainder] using
            two_key_copies_perm key
              (symmetricThreeTernaryReduce rest) reducedCount
        have reordered := schreierProduct_perm permutation
        have reduced :
            symmetricThreeTernaryReduce (key :: rest) = remainder := by
          simp [symmetricThreeTernaryReduce, countBound, remainder]
        rw [reduced, reordered]
        simp only [schreierProduct_cons]
        calc
          schreier key *t
              (schreier key *t
                (schreier key *t schreierProduct remainder)) =
              (schreier key *t schreier key) *t
                (schreier key *t schreierProduct remainder) :=
            (termMul.assoc _ _ _).symm
          _ = ((schreier key *t schreier key) *t schreier key) *t
                schreierProduct remainder :=
            (termMul.assoc _ _ _).symm
          _ = (schreier key *t
                (schreier key *t schreier key)) *t
                schreierProduct remainder := by
            exact congrArg
              (fun value => value *t schreierProduct remainder)
              (termMul.assoc (schreier key) (schreier key) (schreier key))
          _ = one *t schreierProduct remainder := by
            rw [schreier_cube_eq_one]
          _ = schreierProduct remainder := one_mul _

/-- Equal key multiplicities modulo three give equal kernel products. -/
theorem schreierProduct_eq_of_modCounts
    (left right : List (Word Nat))
    (counts : ∀ key, left.count key % 3 = right.count key % 3) :
    schreierProduct left = schreierProduct right := by
  rw [schreierProduct_reduction left,
    schreierProduct_reduction right]
  exact schreierProduct_perm
    (symmetricThreeTernaryReduce_perm_of_mod_eq counts)

/-- Exact Schreier factorization for a scan from an arbitrary parity state. -/
theorem headProduct_mul_scan :
    ∀ (state letters : List Nat),
      headProduct state *t headProduct letters =
        schreierProduct (transitionKeysFrom state letters) *t
          headProduct (finalStateFrom state letters)
  | state, [] => by
      simp only [headProduct_nil, transitionKeysFrom, finalStateFrom,
        schreierProduct_nil, mul_one, one_mul]
  | state, letter :: rest => by
      simp only [headProduct_cons, transitionKeysFrom, finalStateFrom,
        schreierProduct_cons]
      calc
        headProduct state *t
            (generator letter *t headProduct rest) =
            (headProduct state *t generator letter) *t
              headProduct rest :=
          (termMul.assoc _ _ _).symm
        _ = (schreier (transitionKey state letter) *t
              headProduct (toggleState state letter)) *t
              headProduct rest := by
          rw [schreier_mul_nextHead]
        _ = schreier (transitionKey state letter) *t
              (headProduct (toggleState state letter) *t
                headProduct rest) :=
          termMul.assoc _ _ _
        _ = schreier (transitionKey state letter) *t
              (schreierProduct
                  (transitionKeysFrom (toggleState state letter) rest) *t
                headProduct
                  (finalStateFrom (toggleState state letter) rest)) := by
          rw [headProduct_mul_scan]
        _ = (schreier (transitionKey state letter) *t
              schreierProduct
                (transitionKeysFrom (toggleState state letter) rest)) *t
              headProduct
                (finalStateFrom (toggleState state letter) rest) :=
          (termMul.assoc _ _ _).symm

theorem classOf_schreierNormalForm (word : Word Nat) :
    classOf word =
      schreierProduct (transitionKeysFrom [] word.toList) *t
        headProduct (finalStateFrom [] word.toList) := by
  rw [classOf_eq_headProduct]
  have normalized := headProduct_mul_scan [] word.toList
  simpa only [headProduct_nil, one_mul] using normalized

end SemigroupBasis.Examples.SymmetricThreeCompleteness
