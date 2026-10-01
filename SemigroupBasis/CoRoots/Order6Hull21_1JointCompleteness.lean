import SemigroupBasis.Order6Subdirect.HullFamilyTransfers
import SemigroupBasis.CoRoots.S5_831Family
import SemigroupBasis.Generated.S3_8

/-!
# Hull 21.1 joint-completeness reduction

This module develops the shared derivational route for Lee--Zhang
Proposition 21.1.  The two factor pairs

* `S5_831 x S3_8`, and
* `S5_832 x S3_8`

have the same identity theory and the same fourteen-law published system.
The generic consequences below cover all optional contexts in (21.1a-c).
The theorem `hullListDerivesRedistribute` is the unrestricted list form of
Lee--Zhang Lemma 21.2:

`x a b h x = x a x h x b` when every letter of `b` already occurs in
`x a`.

The one residual statement is named `ProfileCountNormalization`.  It is the
combinatorial canonical-form theorem saying that equality of the completed
`S5_831` phase profile and equality of capped multiplicities generate the
fourteen-law congruence.  All product and intersection endpoints in this
file retain that premise explicitly.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis
namespace CoRoots
namespace Order6Hull21_1JointCompleteness

open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_831

private abbrev basis : List (Identity Nat) :=
  SemigroupBasis.Order6Subdirect.Hull21_1_S5_831_S3_8.publishedBasis

abbrev HullListDerives : List Nat -> List Nat -> Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

/-! ## Generic consequences of the fourteen published laws -/

/-- Exchange two later occurrences after witnesses for both letters.
The three list parameters between the four displayed occurrences implement
the eight optional-context instances of Proposition 21.1(c). -/
theorem hullListDerivesExchange
    (pre post h k t : List Nat) (x y : Nat) :
    HullListDerives
      (pre ++ [x] ++ h ++ [y] ++ k ++ [x] ++ t ++ [y] ++ post)
      (pre ++ [x] ++ h ++ [y] ++ k ++ [y] ++ t ++ [x] ++ post) := by
  have core : HullListDerives
      ([x] ++ h ++ [y] ++ k ++ [x] ++ t ++ [y])
      ([x] ++ h ++ [y] ++ k ++ [y] ++ t ++ [x]) := by
    cases h with
    | nil =>
      cases k with
      | nil =>
        cases t with
        | nil =>
          have member :
              (Identity.mk (Word.mk 0 [1, 0, 1])
                (Word.mk 0 [1, 1, 0])) ∈ basis := by
            decide
          have law := Derives.fromBasis member
          let substitution : Nat -> Word Nat :=
            fun index =>
              if index = 0 then Word.singleton x
              else Word.singleton y
          exact
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (Derives.subst law substitution)
        | cons tHead tTail =>
          have member :
              (Identity.mk (Word.mk 0 [1, 0, 2, 1])
                (Word.mk 0 [1, 1, 2, 0])) ∈ basis := by
            decide
          have law := Derives.fromBasis member
          let tWord : Word Nat := Word.mk tHead tTail
          let substitution : Nat -> Word Nat :=
            fun index =>
              if index = 0 then Word.singleton x
              else if index = 1 then Word.singleton y
              else if index = 2 then tWord
              else Word.singleton y
          exact
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (Derives.subst law substitution)
      | cons kHead kTail =>
        let kWord : Word Nat := Word.mk kHead kTail
        cases t with
        | nil =>
          have member :
              (Identity.mk (Word.mk 0 [1, 2, 0, 1])
                (Word.mk 0 [1, 2, 1, 0])) ∈ basis := by
            decide
          have law := Derives.fromBasis member
          let substitution : Nat -> Word Nat :=
            fun index =>
              if index = 0 then Word.singleton x
              else if index = 1 then Word.singleton y
              else kWord
          have derived :=
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (Derives.subst law substitution)
          simpa [Word.toList, Word.bind, substitution, kWord] using
            derived
        | cons tHead tTail =>
          have member :
              (Identity.mk (Word.mk 0 [1, 2, 0, 3, 1])
                (Word.mk 0 [1, 2, 1, 3, 0])) ∈ basis := by
            decide
          have law := Derives.fromBasis member
          let tWord : Word Nat := Word.mk tHead tTail
          let substitution : Nat -> Word Nat :=
            fun index =>
              if index = 0 then Word.singleton x
              else if index = 1 then Word.singleton y
              else if index = 2 then kWord
              else tWord
          exact
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (Derives.subst law substitution)
    | cons hHead hTail =>
      let hWord : Word Nat := Word.mk hHead hTail
      cases k with
      | nil =>
        cases t with
        | nil =>
          have member :
              (Identity.mk (Word.mk 0 [1, 2, 0, 2])
                (Word.mk 0 [1, 2, 2, 0])) ∈ basis := by
            decide
          have law := Derives.fromBasis member
          let substitution : Nat -> Word Nat :=
            fun index =>
              if index = 0 then Word.singleton x
              else if index = 1 then hWord
              else if index = 2 then Word.singleton y
              else Word.singleton x
          have derived :=
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (Derives.subst law substitution)
          simpa [Word.toList, Word.bind, substitution, hWord] using
            derived
        | cons tHead tTail =>
          have member :
              (Identity.mk (Word.mk 0 [1, 2, 0, 3, 2])
                (Word.mk 0 [1, 2, 2, 3, 0])) ∈ basis := by
            decide
          have law := Derives.fromBasis member
          let tWord : Word Nat := Word.mk tHead tTail
          let substitution : Nat -> Word Nat :=
            fun index =>
              if index = 0 then Word.singleton x
              else if index = 1 then hWord
              else if index = 2 then Word.singleton y
              else if index = 3 then tWord
              else Word.singleton x
          have derived :=
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (Derives.subst law substitution)
          simpa [Word.toList, Word.bind, substitution, hWord, tWord]
            using derived
      | cons kHead kTail =>
        let kWord : Word Nat := Word.mk kHead kTail
        cases t with
        | nil =>
          have member :
              (Identity.mk (Word.mk 0 [1, 2, 3, 0, 2])
                (Word.mk 0 [1, 2, 3, 2, 0])) ∈ basis := by
            decide
          have law := Derives.fromBasis member
          let substitution : Nat -> Word Nat :=
            fun index =>
              if index = 0 then Word.singleton x
              else if index = 1 then hWord
              else if index = 2 then Word.singleton y
              else kWord
          have derived :=
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (Derives.subst law substitution)
          simpa [Word.toList, Word.bind, substitution, hWord, kWord]
            using derived
        | cons tHead tTail =>
          have member :
              (Identity.mk (Word.mk 0 [1, 2, 3, 0, 4, 2])
                (Word.mk 0 [1, 2, 3, 2, 4, 0])) ∈ basis := by
            decide
          have law := Derives.fromBasis member
          let tWord : Word Nat := Word.mk tHead tTail
          let substitution : Nat -> Word Nat :=
            fun index =>
              if index = 0 then Word.singleton x
              else if index = 1 then hWord
              else if index = 2 then Word.singleton y
              else if index = 3 then kWord
              else if index = 4 then tWord
              else Word.singleton y
          have derived :=
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (Derives.subst law substitution)
          simpa [Word.toList, Word.bind, substitution, hWord, kWord,
            tWord] using derived
  simpa only [List.append_assoc] using core.context pre post

/-- Contract a third occurrence of `x` when the final two displayed
occurrences are adjacent.  The context `h` may be empty. -/
theorem hullListDerivesPowerContract
    (pre post h : List Nat) (x : Nat) :
    HullListDerives
      (pre ++ [x] ++ h ++ [x, x] ++ post)
      (pre ++ [x] ++ h ++ [x] ++ post) := by
  have core : HullListDerives
      ([x] ++ h ++ [x, x])
      ([x] ++ h ++ [x]) := by
    cases h with
    | nil =>
      have member :
          (Identity.mk (Word.mk 0 [0, 0])
            (Word.mk 0 [0])) ∈ basis := by
        decide
      have law := Derives.fromBasis member
      let substitution : Nat -> Word Nat :=
        fun _ => Word.singleton x
      exact
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (Derives.subst law substitution)
    | cons hHead hTail =>
      have member :
          (Identity.mk (Word.mk 0 [1, 0, 0])
            (Word.mk 0 [1, 0])) ∈ basis := by
        decide
      have law := Derives.fromBasis member
      let hWord : Word Nat := Word.mk hHead hTail
      let substitution : Nat -> Word Nat :=
        fun index =>
          if index = 0 then Word.singleton x else hWord
      have derived :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (Derives.subst law substitution)
      simpa [Word.toList, Word.bind, substitution, hWord] using
        derived
  simpa [List.append_assoc] using core.context pre post

/-- Remove the final displayed `x` after two earlier `x` occurrences and a
terminal square `yy`.  The two optional contexts implement the four
instances of Proposition 21.1(b). -/
theorem hullListDerivesTerminalContract
    (pre post h k : List Nat) (x y : Nat) :
    HullListDerives
      (pre ++ [x] ++ h ++ [x] ++ k ++ [y, y, x] ++ post)
      (pre ++ [x] ++ h ++ [x] ++ k ++ [y, y] ++ post) := by
  cases h with
  | nil =>
    cases k with
    | nil =>
      have member :
          (Identity.mk (Word.mk 0 [0, 1, 1, 0])
            (Word.mk 0 [0, 1, 1])) ∈ basis := by
        decide
      have law := Derives.fromBasis member
      let substitution : Nat -> Word Nat :=
        fun index =>
          if index = 0 then Word.singleton x
          else Word.singleton y
      have derived :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (Derives.subst law substitution)
      simpa [Word.toList, Word.bind, substitution, List.append_assoc]
        using derived.context pre post
    | cons kHead kTail =>
      have member :
          (Identity.mk (Word.mk 0 [0, 1, 2, 2, 0])
            (Word.mk 0 [0, 1, 2, 2])) ∈ basis := by
        decide
      have law := Derives.fromBasis member
      let kWord : Word Nat := Word.mk kHead kTail
      let substitution : Nat -> Word Nat :=
        fun index =>
          if index = 0 then Word.singleton x
          else if index = 1 then kWord
          else Word.singleton y
      have derived :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (Derives.subst law substitution)
      simpa [Word.toList, Word.bind, substitution, kWord,
        List.append_assoc] using derived.context pre post
  | cons hHead hTail =>
    let hWord : Word Nat := Word.mk hHead hTail
    cases k with
    | nil =>
      have member :
          (Identity.mk (Word.mk 0 [1, 0, 2, 2, 0])
            (Word.mk 0 [1, 0, 2, 2])) ∈ basis := by
        decide
      have law := Derives.fromBasis member
      let substitution : Nat -> Word Nat :=
        fun index =>
          if index = 0 then Word.singleton x
          else if index = 1 then hWord
          else Word.singleton y
      have derived :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (Derives.subst law substitution)
      simpa [Word.toList, Word.bind, substitution, hWord,
        List.append_assoc] using derived.context pre post
    | cons kHead kTail =>
      have member :
          (Identity.mk (Word.mk 0 [1, 0, 2, 3, 3, 0])
            (Word.mk 0 [1, 0, 2, 3, 3])) ∈ basis := by
        decide
      have law := Derives.fromBasis member
      let kWord : Word Nat := Word.mk kHead kTail
      let substitution : Nat -> Word Nat :=
        fun index =>
          if index = 0 then Word.singleton x
          else if index = 1 then hWord
          else if index = 2 then kWord
          else Word.singleton y
      have derived :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (Derives.subst law substitution)
      simpa [Word.toList, Word.bind, substitution, hWord, kWord,
        List.append_assoc] using derived.context pre post

/-! ## Lee--Zhang Lemma 21.2 -/

/-- The one-letter case of Lemma 21.2.  A fresh terminal copy of `x` is
created with (21.1a), and the repeated `y` is exchanged with it using
(21.1c). -/
private theorem hullListDerivesRedistributeSingleton
    (pre post a middle : List Nat) (x y : Nat)
    (member : y ∈ x :: a) :
    HullListDerives
      (pre ++ [x] ++ a ++ [y] ++ middle ++ [x] ++ post)
      (pre ++ [x] ++ a ++ [x] ++ middle ++ [x, y] ++ post) := by
  have expanded :
      HullListDerives
        (pre ++ [x] ++ a ++ [y] ++ middle ++ [x] ++ post)
        (pre ++ [x] ++ a ++ [y] ++ middle ++ [x, x] ++ post) := by
    simpa [List.append_assoc] using
      (hullListDerivesPowerContract
        pre post (a ++ [y] ++ middle) x).symm
  by_cases equal : y = x
  · subst y
    simpa [List.append_assoc] using expanded
  · have memberA : y ∈ a := by
      rcases List.mem_cons.mp member with head | tail
      · exact False.elim (equal head)
      · exact tail
    rcases List.append_of_mem memberA with
      ⟨before, after, rfl⟩
    have exchanged :=
      (hullListDerivesExchange
        pre post before after (middle ++ [x]) x y).symm
    exact expanded.trans <| by
      simpa [List.append_assoc] using exchanged

/-- Unrestricted list form of Lee--Zhang Lemma 21.2.

If every letter of the nonempty block `b` already occurs in `x :: a`, the
block can be moved behind the final displayed `x`, while one extra `x` is
inserted after `a`. -/
theorem hullListDerivesRedistribute
    (pre post a middle b : List Nat) (x : Nat)
    (bNonempty : b ≠ [])
    (oldLetters : ∀ letter, letter ∈ b -> letter ∈ x :: a) :
    HullListDerives
      (pre ++ [x] ++ a ++ b ++ middle ++ [x] ++ post)
      (pre ++ [x] ++ a ++ [x] ++ middle ++ [x] ++ b ++ post) := by
  induction b generalizing a pre post middle with
  | nil =>
      exact False.elim (bNonempty rfl)
  | cons y rest ih =>
      cases rest with
      | nil =>
          have member : y ∈ x :: a :=
            oldLetters y (by simp)
          simpa [List.append_assoc] using
            hullListDerivesRedistributeSingleton
              pre post a middle x y member
      | cons z zs =>
          let tailBlock := z :: zs
          have tailNonempty : tailBlock ≠ [] := by
            simp [tailBlock]
          have tailOld :
              ∀ letter, letter ∈ tailBlock ->
                letter ∈ x :: (a ++ [y]) := by
            intro letter letterMember
            have old :
                letter ∈ x :: a :=
              oldLetters letter <| by
                simp [tailBlock, letterMember]
            rcases List.mem_cons.mp old with head | inA
            · exact List.mem_cons.mpr (Or.inl head)
            · exact List.mem_cons.mpr <|
                Or.inr (List.mem_append_left [y] inA)
          have moveTail :
              HullListDerives
                (pre ++ [x] ++ a ++ [y] ++ tailBlock ++
                  middle ++ [x] ++ post)
                (pre ++ [x] ++ a ++ [y, x] ++
                  middle ++ [x] ++ tailBlock ++ post) := by
            simpa [tailBlock, List.append_assoc] using
              ih
                (a := a ++ [y]) (pre := pre) (post := post)
                (middle := middle) tailNonempty tailOld
          have yOld : y ∈ x :: a :=
            oldLetters y (by simp)
          have moveHead :
              HullListDerives
                (pre ++ [x] ++ a ++ [y, x] ++
                  middle ++ [x] ++ tailBlock ++ post)
                (pre ++ [x] ++ a ++ [x, x] ++
                  middle ++ [x, y] ++ tailBlock ++ post) := by
            simpa [tailBlock, List.append_assoc] using
              hullListDerivesRedistributeSingleton
                pre (tailBlock ++ post) a ([x] ++ middle)
                x y yOld
          have contract :
              HullListDerives
                (pre ++ [x] ++ a ++ [x, x] ++
                  middle ++ [x, y] ++ tailBlock ++ post)
                (pre ++ [x] ++ a ++ [x] ++
                  middle ++ [x] ++ [y] ++ tailBlock ++ post) := by
            simpa [tailBlock, List.append_assoc] using
              hullListDerivesPowerContract
                pre (middle ++ [x, y] ++ tailBlock ++ post) a x
          simpa [tailBlock, List.append_assoc] using
            moveTail.trans (moveHead.trans contract)

/-! ## Exact residual and conditional endpoints -/

/-- The remaining canonical-form statement for Proposition 21.1.

The completed `S5_831` semantics supplies equality of `phaseProfileList`;
the completed `S3_8` semantics supplies equality of every multiplicity
capped at two.  Lemma 21.2 above is the block-redistribution operation used
in the published normalization proof. -/
def ProfileCountNormalization : Prop :=
  ∀ {left right : List Nat},
    left ≠ [] ->
    right ≠ [] ->
    phaseProfileList left = phaseProfileList right ->
    (∀ letter : Nat,
      min (left.count letter) 2 =
        min (right.count letter) 2) ->
    HullListDerives left right

/-- Upgrade the list-level residual to unrestricted word derivability. -/
theorem derivesOfCommonSignature
    (normalize : ProfileCountNormalization)
    {left right : Word Nat}
    (phase : SamePhaseOccupancySignature left right)
    (counts : ∀ letter : Nat,
      min (left.toList.count letter) 2 =
        min (right.toList.count letter) 2) :
    Derives basis left right := by
  have leftNonempty : left.toList ≠ [] := by
    cases left
    simp [Word.toList]
  have rightNonempty : right.toList ≠ [] := by
    cases right
    simp [Word.toList]
  have listDerivation :=
    normalize leftNonempty rightNonempty phase counts
  cases listDerivation with
  | words derivation =>
      simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons] using
        derivation

private theorem validRightCappedCounts
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemigroupBasis.Order6Subdirect.Hull21_1_S5_831_S3_8.H) :
    ∀ letter : Nat,
      min (identity.lhs.toList.count letter) 2 =
        min (identity.rhs.toList.count letter) 2 := by
  apply exponentValid_capped_count_eq identity
  have tableEq :
      Generated.Catalogue.S3_8.table =
        Generated.S3_8.table := by
    unfold Generated.Catalogue.S3_8.table Generated.S3_8.table
    congr 1
    funext left right
    exact by decide +revert
  change
    identity.SatisfiedBy
      Generated.Catalogue.S3_8.table.semigroup at valid
  rw [tableEq, Generated.S3_8.table_eq_catalogue_model] at valid
  exact valid

/-- Conditional closure of the `S5_831 x S3_8` derivational obligation. -/
theorem h831DerivationalObligation_of_profileCountNormalization
    (normalize : ProfileCountNormalization) :
    SemigroupBasis.Order6Subdirect.Hull21_1_S5_831_S3_8.DerivationalObligation := by
  intro identity validLeft validRight
  exact derivesOfCommonSignature normalize
    (valid_samePhaseOccupancySignature identity validLeft)
    (validRightCappedCounts identity validRight)

/-- The sibling `S5_832` obligation follows from the completed common
two-law identity theory of `S5_831` and `S5_832`. -/
theorem h832DerivationalObligation_of_profileCountNormalization
    (normalize : ProfileCountNormalization) :
    SemigroupBasis.Order6Subdirect.Hull21_1_S5_832_S3_8.DerivationalObligation :=
  SemigroupBasis.Order6Subdirect.HullFamilyTransfers.hull21_832_of_831
    (h831DerivationalObligation_of_profileCountNormalization normalize)

/-- Conditional intersection-basis package for `S5_831 x S3_8`. -/
def h831IntersectionBasis_of_profileCountNormalization
    (normalize : ProfileCountNormalization) :
    IntersectionBasis
      SemigroupBasis.Order6Subdirect.Hull21_1_S5_831_S3_8.G
      SemigroupBasis.Order6Subdirect.Hull21_1_S5_831_S3_8.H
      SemigroupBasis.Order6Subdirect.Hull21_1_S5_831_S3_8.publishedBasis where
  leftModels :=
    SemigroupBasis.Order6Subdirect.Hull21_1_S5_831_S3_8.models_left
  rightModels :=
    SemigroupBasis.Order6Subdirect.Hull21_1_S5_831_S3_8.models_right
  complete :=
    h831DerivationalObligation_of_profileCountNormalization normalize

/-- Conditional intersection-basis package for `S5_832 x S3_8`. -/
def h832IntersectionBasis_of_profileCountNormalization
    (normalize : ProfileCountNormalization) :
    IntersectionBasis
      SemigroupBasis.Order6Subdirect.Hull21_1_S5_832_S3_8.G
      SemigroupBasis.Order6Subdirect.Hull21_1_S5_832_S3_8.H
      SemigroupBasis.Order6Subdirect.Hull21_1_S5_832_S3_8.publishedBasis where
  leftModels :=
    SemigroupBasis.Order6Subdirect.Hull21_1_S5_832_S3_8.models_left
  rightModels :=
    SemigroupBasis.Order6Subdirect.Hull21_1_S5_832_S3_8.models_right
  complete :=
    h832DerivationalObligation_of_profileCountNormalization normalize

/-- Conditional complete basis for the first product hull. -/
theorem h831ProductBasisFor_of_profileCountNormalization
    (normalize : ProfileCountNormalization) :
    BasisFor
      SemigroupBasis.Order6Subdirect.Hull21_1_S5_831_S3_8.P
      SemigroupBasis.Order6Subdirect.Hull21_1_S5_831_S3_8.publishedBasis :=
  SemigroupBasis.Order6Subdirect.Hull21_1_S5_831_S3_8.prod_basisFor_of_obligation
    (h831DerivationalObligation_of_profileCountNormalization normalize)

/-- Conditional complete basis for the sibling product hull. -/
theorem h832ProductBasisFor_of_profileCountNormalization
    (normalize : ProfileCountNormalization) :
    BasisFor
      SemigroupBasis.Order6Subdirect.Hull21_1_S5_832_S3_8.P
      SemigroupBasis.Order6Subdirect.Hull21_1_S5_832_S3_8.publishedBasis :=
  SemigroupBasis.Order6Subdirect.Hull21_1_S5_832_S3_8.prod_basisFor_of_obligation
    (h832DerivationalObligation_of_profileCountNormalization normalize)

end Order6Hull21_1JointCompleteness
end CoRoots
end SemigroupBasis
