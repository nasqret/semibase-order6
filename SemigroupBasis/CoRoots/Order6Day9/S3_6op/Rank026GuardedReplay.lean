import SemigroupBasis.CoRoots.S5_1099
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.CatalogueOrder3
import SemigroupBasis.Generated.CatalogueOrder5Part09
import SemigroupBasis.Subdirect

/-!
# Rank026: exact B10 and an independent nonempty-stem lower replay

The literal word-reversed B10 of the reviewed D026 design is fixed here.
The failed historical initial-trace scanner is neither imported nor patched.
Both complete S5_1099 laws lift behind a nonempty stem: guarded
idempotence is law09, and guarded R3=Q3 follows by two guarded square
expansions followed by the reverse of the exact crossing law05.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

namespace SemigroupBasis.CoRoots.Order6Day9.S3_6op.Rank026GuardedReplay

open SemigroupBasis

/-- The actual catalogue S3_6 in the OPPOSITE orientation. -/
def leftTable : FiniteTable where
  order := 3
  mul := fun first second => Generated.Catalogue.S3_6.table.mul second first
  assoc := by decide

abbrev rightTable : FiniteTable := Generated.Catalogue.S5_1099.table
abbrev lowerBasis : List (Identity Nat) := SemigroupBasis.CoRoots.S5_1099.basis

def law00 : Identity Nat := ⟨Word.mk 0 [0, 0], Word.mk 0 [0]⟩
def law01 : Identity Nat := ⟨Word.mk 0 [0, 1, 0], Word.mk 0 [1, 0]⟩
def law02 : Identity Nat := ⟨Word.mk 0 [1, 0, 0], Word.mk 0 [1, 0]⟩
def law03 : Identity Nat := ⟨Word.mk 0 [1, 0, 1], Word.mk 0 [0, 1, 1]⟩
def law04 : Identity Nat := ⟨Word.mk 0 [1, 2, 0, 1], Word.mk 0 [0, 1, 2, 1]⟩
def law05 : Identity Nat := ⟨Word.mk 0 [1, 2, 0, 2], Word.mk 0 [0, 1, 2, 2]⟩
def law06 : Identity Nat := ⟨Word.mk 0 [1, 2, 3, 0, 2], Word.mk 0 [0, 1, 2, 3, 2]⟩
def law07 : Identity Nat := ⟨Word.mk 0 [1, 2, 1, 0], Word.mk 0 [1, 2, 0]⟩
def law08 : Identity Nat := ⟨Word.mk 0 [1, 2, 3, 2, 0], Word.mk 0 [1, 2, 3, 0]⟩
def law09 : Identity Nat := ⟨Word.mk 0 [1, 1], Word.mk 0 [1]⟩

def basis : List (Identity Nat) :=
  [law00, law01, law02, law03, law04, law05, law06, law07, law08, law09]

def displayedBasisSHA256 : String :=
  "fc7ff9917dceab6f300df1957d9153f20088229b0d5ce05ce1510d5d1ae247c8"

theorem basis_length : basis.length = 10 := by decide

private def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

theorem modelsLeft : Models leftTable.semigroup basis :=
  FiniteCertificate.checkModels_sound leftTable basis toFinFour (by decide)

theorem modelsRight : Models rightTable.semigroup basis :=
  FiniteCertificate.checkModels_sound rightTable basis toFinFour (by decide)

theorem leftFactor_eq_catalogueOpposite :
    leftTable.semigroup = Generated.Catalogue.S3_6.table.semigroup.opposite := rfl

abbrev FinitePair (target : FiniteTable) :=
  SubdirectPair target.semigroup leftTable.semigroup rightTable.semigroup

abbrev FinitePairOpposite (target : FiniteTable) :=
  SubdirectPair target.semigroup.opposite
    leftTable.semigroup.opposite rightTable.semigroup.opposite

private def instantiateThree (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

theorem derivesGuardedSquareExpansion (stem block : Word Nat) :
    Derives basis (stem ++ block) ((stem ++ block) ++ block) := by
  have primitive : Derives basis (Word.mk 0 [1]) (Word.mk 0 [1, 1]) :=
    (Derives.fromBasis (e := law09) (by decide)).symm
  have substituted := Derives.subst primitive (instantiateThree stem block block)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesCrossing (first middle last : Word Nat) :
    Derives basis
      (((((first ++ middle) ++ last) ++ first) ++ last))
      (((((first ++ first) ++ middle) ++ last) ++ last)) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 2, 0, 2]) (Word.mk 0 [0, 1, 2, 2]) :=
    Derives.fromBasis (e := law05) (by decide)
  have substituted := Derives.subst primitive (instantiateThree first middle last)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- A three-step B10 chain; the nonempty stem is essential. -/
theorem derivesGuardedR3Q3 (stem first middle last : Word Nat) :
    Derives basis
      (stem ++ ((first ++ middle) ++ last))
      (stem ++ ((((first ++ middle) ++ last) ++ first) ++ last)) := by
  have one :
      Derives basis
        (stem ++ ((first ++ middle) ++ last))
        (stem ++ (((first ++ middle) ++ last) ++ last)) := by
    simpa only [Word.append_assoc] using
      derivesGuardedSquareExpansion ((stem ++ first) ++ middle) last
  have two :
      Derives basis
        (stem ++ (((first ++ middle) ++ last) ++ last))
        (stem ++ ((((first ++ first) ++ middle) ++ last) ++ last)) := by
    simpa only [Word.append_assoc] using
      Derives.appendRight (derivesGuardedSquareExpansion stem first)
        ((middle ++ last) ++ last)
  have three :
      Derives basis
        (stem ++ ((((first ++ first) ++ middle) ++ last) ++ last))
        (stem ++ ((((first ++ middle) ++ last) ++ first) ++ last)) :=
    Derives.prepend stem (derivesCrossing first middle last).symm
  exact one.trans (two.trans three)

private theorem bind_append (left right : Word Nat) (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution =
      left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind (word : Word Nat) (first second : Nat → Word Nat) :
    (word.bind first).bind second =
      word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) : word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- Every lower derivation replays under every substitution and a nonempty
stem.  This is not a bare retarget of either false lower axiom. -/
theorem liftLowerWithPrefix {left right : Word Nat}
    (derivation : Derives lowerBasis left right)
    (stem : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis
      (stem ++ left.bind substitution) (stem ++ right.bind substitution) := by
  induction derivation generalizing stem substitution with
  | fromBasis member =>
      simp only [lowerBasis, SemigroupBasis.CoRoots.S5_1099.basis,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · change Derives basis
          (stem ++ (Word.singleton 0).bind substitution)
          (stem ++ (Word.mk 0 [0]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          derivesGuardedSquareExpansion stem (substitution 0)
      · change Derives basis
          (stem ++ (Word.mk 0 [1, 2]).bind substitution)
          (stem ++ (Word.mk 0 [1, 2, 0, 2]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          derivesGuardedR3Q3 stem (substitution 0) (substitution 1) (substitution 2)
  | refl => exact Derives.refl _
  | symm _ induction => exact (induction stem substitution).symm
  | trans _ _ first second =>
      exact (first stem substitution).trans (second stem substitution)
  | prepend first _ induction =>
      simpa [bind_append, Word.append_assoc] using
        induction (stem ++ first.bind substitution) substitution
  | appendRight _ last induction =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight (induction stem substitution) (last.bind substitution)
  | subst _ next induction =>
      simpa [bind_bind] using
        induction stem (fun letter => (next letter).bind substitution)

theorem liftLowerWithPrefixIdentity {left right : Word Nat}
    (derivation : Derives lowerBasis left right) (stem : Word Nat) :
    Derives basis (stem ++ left) (stem ++ right) := by
  simpa only [bind_singleton] using
    liftLowerWithPrefix derivation stem Word.singleton

theorem derivesSquareToCube (block : Word Nat) :
    Derives basis (block ++ block) ((block ++ block) ++ block) := by
  have primitive : Derives basis (Word.mk 0 [0]) (Word.mk 0 [0, 0]) :=
    (Derives.fromBasis (e := law00) (by decide)).symm
  have substituted := Derives.subst primitive (fun _ => block)
  simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesRepeatedHeadExpansion (first middle : Word Nat) :
    Derives basis ((first ++ middle) ++ first)
      (((first ++ first) ++ middle) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 0]) (Word.mk 0 [0, 1, 0]) :=
    (Derives.fromBasis (e := law01) (by decide)).symm
  have substituted := Derives.subst primitive (instantiateThree first middle middle)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- A globally repeated initial letter can be doubled at the front. -/
theorem expandRepeatedInitial (head : Nat) (tail : List Nat)
    (repeated : head ∈ tail) :
    Derives basis (Word.mk head tail) (Word.mk head (head :: tail)) := by
  obtain ⟨before, after, shape⟩ := List.mem_iff_append.mp repeated
  subst tail
  have core : SemigroupBasis.CoRoots.S5_107.ListDerives basis
      ((head :: before) ++ [head]) ((head :: head :: before) ++ [head]) := by
    cases before with
    | nil =>
        simpa [Word.singleton, Word.append] using
          SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
            (derivesSquareToCube (Word.singleton head))
    | cons first rest =>
        simpa [Word.singleton, Word.append, List.append_assoc] using
          SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
            (derivesRepeatedHeadExpansion (Word.singleton head) (Word.mk first rest))
  have contextual : SemigroupBasis.CoRoots.S5_107.ListDerives basis
      (head :: (before ++ head :: after))
      (head :: head :: (before ++ head :: after)) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using core.append after
  exact contextual.toWord

end SemigroupBasis.CoRoots.Order6Day9.S3_6op.Rank026GuardedReplay
