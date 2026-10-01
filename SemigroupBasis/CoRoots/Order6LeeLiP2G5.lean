import SemigroupBasis.CoRoots.S5_1089Normalization
import SemigroupBasis.FiniteCertificate

namespace SemigroupBasis.CoRoots.Order6LeeLiP2G5

open SemigroupBasis

/-!
All-variable syntax kernel for Lee--Li Proposition 2, group G5.

The single law is `xyx = yx`.  Its normal-form invariant is the pair formed
by the last-occurrence sequence and the bit saying that the final two letters
are equal.  A concrete order-six member still has to prove global separation
of that invariant; no bounded finite-variable check is promoted to that claim
in this module.
-/

private abbrev ListDerives :=
  SemigroupBasis.CoRoots.S5_107.ListDerives

private abbrev listWordOfCons :=
  SemigroupBasis.CoRoots.S5_107.listWordOfCons

abbrev lastOccurrenceSequence :=
  SemigroupBasis.CoRoots.S5_1089.lastOccurrenceSequence

private theorem lastOccurrenceSequence_cons (letter : Nat)
    (rest : List Nat) :
    lastOccurrenceSequence (letter :: rest) =
      if letter ∈ rest then
        lastOccurrenceSequence rest
      else
        letter :: lastOccurrenceSequence rest := by
  change
    SemigroupBasis.CoRoots.S5_1089.lastOccurrenceSequence
        (letter :: rest) =
      if letter ∈ rest then
        SemigroupBasis.CoRoots.S5_1089.lastOccurrenceSequence rest
      else
        letter ::
          SemigroupBasis.CoRoots.S5_1089.lastOccurrenceSequence rest
  rw [SemigroupBasis.CoRoots.S5_1089.lastOccurrenceSequence.eq_def]

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xyx : Word Nat := w 0 [1, 0]
def yx : Word Nat := w 1 [0]

def law : Identity Nat := ⟨xyx, yx⟩

/-- The exact one-law candidate basis `{xyx = yx}`. -/
def basis : List (Identity Nat) := [law]

private def instantiateTwoWords (x y : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | n + 2 => Word.singleton (n + 2)

private theorem basisLaw : Derives basis xyx yx :=
  Derives.fromBasis (e := law) (List.Mem.head _)

/-- Delete a repeated block when a nonempty block separates its copies. -/
theorem derivesSandwichContraction (x y : Word Nat) :
    Derives basis ((x ++ y) ++ x) (y ++ x) := by
  have substituted :=
    Derives.subst basisLaw (instantiateTwoWords x y)
  simpa [law, xyx, yx, w, instantiateTwoWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

def xxy : Word Nat := w 0 [0, 1]
def xyxy : Word Nat := w 0 [1, 0, 1]
def yxy : Word Nat := w 1 [0, 1]
def xy : Word Nat := w 0 [1]

private def swapVariables : Nat → Word Nat
  | 0 => Word.singleton 1
  | 1 => Word.singleton 0
  | n + 2 => Word.singleton (n + 2)

/-- The required exact adjacent-deletion chain
`xxy -> xyxy -> yxy -> xy`. -/
theorem derivesXxyToXy : Derives basis xxy xy := by
  have swapped : Derives basis yxy xy := by
    have substituted := Derives.subst basisLaw swapVariables
    simpa [law, xyx, yx, yxy, xy, w, swapVariables, Word.bind,
      Word.append, Word.singleton, Word.append_assoc] using substituted
  have first : Derives basis xxy xyxy := by
    have prefixed :=
      Derives.prepend (Word.singleton 0) swapped.symm
    simpa [xxy, xyxy, yxy, xy, w, Word.append, Word.singleton,
      Word.append_assoc] using prefixed
  have second : Derives basis xyxy yxy := by
    have appended :=
      Derives.appendRight basisLaw (Word.singleton 1)
    simpa [law, xyx, yx, xyxy, yxy, w, Word.append,
      Word.singleton, Word.append_assoc] using appended
  exact first.trans (second.trans swapped)

/-- Delete the first of two adjacent copies when a nonempty tail follows. -/
theorem derivesAdjacentContraction (x tail : Word Nat) :
    Derives basis ((x ++ x) ++ tail) (x ++ tail) := by
  have substituted :=
    Derives.subst derivesXxyToXy (instantiateTwoWords x tail)
  simpa [xxy, xy, w, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-! ## Invariant and canonical form -/

/-- Whether the last two positions of a list agree. -/
def finalSquareBit : List Nat → Bool
  | [] => false
  | [_] => false
  | first :: second :: [] => decide (first = second)
  | _ :: second :: third :: rest =>
      finalSquareBit (second :: third :: rest)

structure Invariant where
  lord : List Nat
  finalSquare : Bool
deriving Repr, DecidableEq

def invariant (word : Word Nat) : Invariant :=
  ⟨lastOccurrenceSequence word.toList,
    finalSquareBit word.toList⟩

/-- Render a signature as its last-occurrence word, doubling the final letter
exactly when the final-square bit is set.  The empty branch is unreachable for
signatures produced by `invariant` from a semigroup word. -/
def canonicalList : Invariant → List Nat
  | ⟨lord, false⟩ => lord
  | ⟨lord, true⟩ => lord ++ [lord.getLastD 0]

private def wordOfList : List Nat → Word Nat
  | [] => Word.singleton 0
  | head :: tail => ⟨head, tail⟩

/-- A recursion aligned with the two legal deletion cases.  Length-two words
are fixed, in particular preserving a terminal square. -/
def normalList : List Nat → List Nat
  | [] => []
  | [a] => [a]
  | [a, b] => [a, b]
  | a :: b :: c :: rest =>
      if a ∈ b :: c :: rest then
        normalList (b :: c :: rest)
      else
        a :: normalList (b :: c :: rest)

def canonical (word : Word Nat) : Word Nat :=
  wordOfList (normalList word.toList)

private theorem lastOccurrenceSequence_ne_nil :
    ∀ {letters : List Nat}, letters ≠ [] →
      lastOccurrenceSequence letters ≠ []
  | [], nonempty => by contradiction
  | letter :: rest, _ => by
      rw [lastOccurrenceSequence_cons]
      by_cases later : letter ∈ rest
      · have restNonempty : rest ≠ [] := by
          intro empty
          subst rest
          simp at later
        rw [if_pos later]
        exact lastOccurrenceSequence_ne_nil restNonempty
      · rw [if_neg later]
        simp

private theorem getLastD_cons_of_ne_nil
    (head fallback : Nat) {tail : List Nat} (nonempty : tail ≠ []) :
    (head :: tail).getLastD fallback = tail.getLastD fallback := by
  cases tail with
  | nil => contradiction
  | cons next rest => simp only [List.getLastD_cons]

/-- The recursive target is exactly the dossier's invariant renderer. -/
theorem normalList_eq_canonicalList :
    ∀ letters : List Nat,
      normalList letters =
        canonicalList
          ⟨lastOccurrenceSequence letters, finalSquareBit letters⟩
  | [] => by
      rfl
  | [a] => by
      simp [normalList, canonicalList,
        SemigroupBasis.CoRoots.S5_1089.lastOccurrenceSequence,
        finalSquareBit]
  | [a, b] => by
      by_cases equal : a = b
      · subst b
        simp [normalList, canonicalList,
          SemigroupBasis.CoRoots.S5_1089.lastOccurrenceSequence,
          finalSquareBit]
      · simp [normalList, canonicalList,
          SemigroupBasis.CoRoots.S5_1089.lastOccurrenceSequence,
          finalSquareBit, equal]
  | a :: b :: c :: rest => by
      have induction := normalList_eq_canonicalList (b :: c :: rest)
      have lordNonempty :
          lastOccurrenceSequence (b :: c :: rest) ≠ [] :=
        lastOccurrenceSequence_ne_nil (by simp)
      by_cases later : a ∈ b :: c :: rest
      · rw [normalList, if_pos later,
          lastOccurrenceSequence_cons,
          if_pos later, finalSquareBit]
        exact induction
      · cases square : finalSquareBit (b :: c :: rest) with
        | false =>
            have plain :
                normalList (b :: c :: rest) =
                  lastOccurrenceSequence (b :: c :: rest) := by
              simpa [canonicalList, square] using induction
            rw [normalList, if_neg later,
              lastOccurrenceSequence_cons,
              if_neg later, finalSquareBit, square, canonicalList]
            exact congrArg (List.cons a) plain
        | true =>
            have squared :
                normalList (b :: c :: rest) =
                  lastOccurrenceSequence (b :: c :: rest) ++
                    [(lastOccurrenceSequence
                      (b :: c :: rest)).getLastD 0] := by
              simpa [canonicalList, square] using induction
            have finalUnchanged :=
              getLastD_cons_of_ne_nil a 0 lordNonempty
            rw [normalList, if_neg later,
              lastOccurrenceSequence_cons,
              if_neg later, finalSquareBit, square, canonicalList]
            calc
              a :: normalList (b :: c :: rest) =
                  a :: (lastOccurrenceSequence (b :: c :: rest) ++
                    [(lastOccurrenceSequence
                      (b :: c :: rest)).getLastD 0]) :=
                congrArg (List.cons a) squared
              _ = (a :: lastOccurrenceSequence (b :: c :: rest)) ++
                    [(a :: lastOccurrenceSequence
                      (b :: c :: rest)).getLastD 0] := by
                simp only [List.cons_append, finalUnchanged]

/-! ## All-variable normalization -/

private theorem listDerivesDeleteLeading
    (a b c : Nat) (rest : List Nat)
    (later : a ∈ b :: c :: rest) :
    ListDerives basis
      (a :: b :: c :: rest)
      (b :: c :: rest) := by
  by_cases adjacent : a = b
  · subst b
    have core :=
      SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
        (derivesAdjacentContraction
          (Word.singleton a) (listWordOfCons c rest))
    simpa [listWordOfCons, Word.append, Word.singleton,
      List.append_assoc] using core
  · have laterInRest : a ∈ c :: rest := by
      simpa [adjacent] using later
    obtain ⟨before, after, split⟩ :=
      List.mem_iff_append.mp laterInRest
    have core :=
      SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
        (derivesSandwichContraction
          (Word.singleton a) (listWordOfCons b before))
    have appended :=
      SemigroupBasis.CoRoots.S5_107.ListDerives.append core after
    simpa [split, listWordOfCons, Word.append, Word.singleton,
      List.append_assoc] using appended

/-- Every finite list derives to its G5 normal list.  In the recursive case
only a leading occurrence with a later copy is deleted, so the final two
positions are untouched. -/
theorem listDerivesNormal :
    ∀ letters : List Nat, ListDerives basis letters (normalList letters)
  | [] => SemigroupBasis.CoRoots.S5_107.ListDerives.empty
  | [a] => SemigroupBasis.CoRoots.S5_107.ListDerives.refl [a]
  | [a, b] => SemigroupBasis.CoRoots.S5_107.ListDerives.refl [a, b]
  | a :: b :: c :: rest => by
      have induction := listDerivesNormal (b :: c :: rest)
      by_cases later : a ∈ b :: c :: rest
      · simpa [normalList, later] using
          SemigroupBasis.CoRoots.S5_107.ListDerives.trans
            (listDerivesDeleteLeading a b c rest later) induction
      · simpa [normalList, later] using
          SemigroupBasis.CoRoots.S5_107.ListDerives.prepend [a] induction

private theorem normalList_ne_nil (word : Word Nat) :
    normalList word.toList ≠ [] := by
  cases word with
  | mk head tail =>
      exact SemigroupBasis.CoRoots.S5_107.ListDerives.target_ne_nil
        (listDerivesNormal (head :: tail))

private theorem wordOfList_toList {letters : List Nat}
    (nonempty : letters ≠ []) :
    (wordOfList letters).toList = letters := by
  cases letters with
  | nil => contradiction
  | cons head tail => rfl

/-- Every word derives to the canonical representative of its invariant. -/
theorem derivesCanonical (word : Word Nat) :
    Derives basis word (canonical word) := by
  cases word with
  | mk head tail =>
      have listDerivation := listDerivesNormal (head :: tail)
      obtain ⟨targetHead, targetTail, target, wordDerivation⟩ :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.from_cons listDerivation
      simpa [canonical, wordOfList, Word.toList, target] using
        wordDerivation

/-- The canonical word is literally the last-occurrence word with its final
letter doubled exactly in the square case. -/
theorem canonical_toList (word : Word Nat) :
    (canonical word).toList = canonicalList (invariant word) := by
  rw [canonical, wordOfList_toList (normalList_ne_nil word)]
  exact normalList_eq_canonicalList word.toList

/-- Equal G5 invariants are sufficient for derivability from `xyx = yx`. -/
theorem derivesOfInvariantEq (left right : Word Nat)
    (same : invariant left = invariant right) :
    Derives basis left right := by
  have normalEqual : canonical left = canonical right := by
    apply Word.toList_injective
    rw [canonical_toList, canonical_toList, same]
  exact (derivesCanonical left).trans <| by
    rw [normalEqual]
    exact (derivesCanonical right).symm

/-! ## Concrete-table interface -/

/-- The global semantic obligation left to each concrete G5 member.  The
merge-collapse argument from the dossier is intentionally outside the generic
normalizer until it is formalized. -/
def InvariantSeparation (semigroup : Semigroup carrier) : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy semigroup →
      invariant identity.lhs = invariant identity.rhs

theorem basisForOfInvariantSeparation
    (semigroup : Semigroup carrier)
    (models : Models semigroup basis)
    (separates : InvariantSeparation semigroup) :
    BasisFor semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact derivesOfInvariantEq identity.lhs identity.rhs
    (separates identity valid)

/-- Executable finite-table soundness check for the sole two-variable law. -/
def toFinTwo : Nat → Fin 2
  | 0 => 0
  | _ => 1

def checkModels (table : FiniteTable) : Bool :=
  FiniteCertificate.checkModels table basis toFinTwo

theorem modelsOfCheckModels (table : FiniteTable)
    (checked : checkModels table = true) :
    Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinTwo checked

end SemigroupBasis.CoRoots.Order6LeeLiP2G5
