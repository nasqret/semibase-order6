import SemigroupBasis.CoRoots.Order6Day7.Level2.SeedRank109
import SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank105FiniteFanout
import SemigroupBasis.Generated.S3_15

/-!
# Exact rank127 semantics and a genuinely right-guarded lower-calculus lift

The seven laws have sigma SHA-256
`cbab95b885f4c1cc15189c62065047b7200818e1035be9f8370f8d22e4d6413a`.
The actual factors are S3_15 opposite and S5_379 direct. The extra law
xyxyz=xyyxz permits the missing lower crossing only with a nonempty right
context. Induction preserves this guard under arbitrary substitutions and
both contexts; no cancellation or unguarded lower completeness is inferred.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.Level2.Rank127

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots

def leftTable : FiniteTable := Order6Subdirect.oppositeTable Generated.Catalogue.S3_15.table
abbrev rightTable : FiniteTable := S5_379.table
abbrev rightOppositeTable : FiniteTable := S3_16.Rank105.FiniteFanout.rightOppositeTable

def law00 : Identity Nat := Rank109.law00
def law01 : Identity Nat := Rank109.law01
def law02 : Identity Nat := Rank109.law02
def law03 : Identity Nat := Rank109.law03
def law04 : Identity Nat := ⟨⟨0, [1, 0, 1, 2]⟩, ⟨0, [1, 1, 0, 2]⟩⟩
def law05 : Identity Nat := Rank109.law04
def law06 : Identity Nat := Rank109.law05

def basis : List (Identity Nat) := [law00, law01, law02, law03, law04, law05, law06]

def displayedBasisSHA256 : String :=
  "cbab95b885f4c1cc15189c62065047b7200818e1035be9f8370f8d22e4d6413a"

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem leftModels : Models leftTable.semigroup basis :=
  FiniteCertificate.checkModels_sound leftTable basis toFinThree (by decide)

theorem rightModels : Models rightTable.semigroup basis :=
  FiniteCertificate.checkModels_sound rightTable basis toFinThree (by decide)

theorem rightOppositeModels : Models rightOppositeTable.semigroup basis :=
  FiniteCertificate.checkModels_sound rightOppositeTable basis toFinThree (by decide)

theorem componentFinal_eq_reverse_head (word : Word Nat) :
    S5_804.componentFinal word.toList = word.reverse.head := by
  cases word with
  | mk head tail =>
      induction tail generalizing head with
      | nil => rfl
      | cons next rest induction =>
          simpa only [Word.toList, S5_804.componentFinal, Word.reverse, Word.reverseAux,
            Word.append_head, List.getLastD_cons] using induction next

theorem leftValid_final (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftTable.semigroup) :
    S5_804.componentFinal identity.lhs.toList = S5_804.componentFinal identity.rhs.toList := by
  have modelValid : identity.SatisfiedBy Generated.S3_15.table.semigroup.opposite := by
    rw [Generated.S3_15.table_eq_canonical_catalogue]
    exact valid
  have reversedValid := (identity.satisfiedBy_opposite_iff_reversed Generated.S3_15.table.semigroup).mp modelValid
  rw [Generated.S3_15.table_eq_catalogue_model] at reversedValid
  have heads := leftNormalBandFifteenValid_head_eq identity.reversed reversedValid
  rw [componentFinal_eq_reverse_head, componentFinal_eq_reverse_head]
  exact heads

structure SameSignature (left right : Word Nat) : Prop where
  final : S5_804.componentFinal left.toList = S5_804.componentFinal right.toList
  componentSimple : S5_379.SameComponentSimpleSignature left right

theorem sameSignature_of_factorValid (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    SameSignature identity.lhs identity.rhs :=
  ⟨leftValid_final identity leftValid, S5_379.valid_sameSignature identity rightValid⟩

abbrev ListDerives : List Nat → List Nat → Prop := S5_107.ListDerives basis

theorem rank109AxiomsDerive (identity : Identity Nat) (member : identity ∈ Rank109.basis) :
    Derives basis identity.lhs identity.rhs := by
  simp only [Rank109.basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply Derives.fromBasis
    decide

theorem transport109List {left right : List Nat} (derivation : Rank109.ListDerives left right) :
    ListDerives left right := by
  cases derivation with
  | empty => exact S5_107.ListDerives.empty
  | words proof => exact S5_107.ListDerives.words (proof.transport rank109AxiomsDerive)

private def instantiateThreeWords (left middle right : Word Nat) : Nat → Word Nat
  | 0 => left
  | 1 => middle
  | _ => right

/-- Each lower axiom, after any simultaneous nonempty substitution, has an
actual target derivation with an arbitrary nonempty right guard. -/
theorem lowerBasisUnderRight (identity : Identity Nat) (member : identity ∈ S5_379.basis)
    (substitution : Nat → Word Nat) (guard : Word Nat) :
    Derives basis (identity.lhs.bind substitution ++ guard) (identity.rhs.bind substitution ++ guard) := by
  simp only [S5_379.basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Derives.appendRight
      (Derives.subst (Derives.fromBasis (e := law00) (by simp [basis])) substitution) guard
  · exact Derives.appendRight
      (Derives.subst (Derives.fromBasis (e := law01) (by simp [basis])).symm substitution) guard
  · exact Derives.appendRight
      (Derives.subst (Derives.fromBasis (e := law02) (by simp [basis])) substitution) guard
  · have core : Derives basis law04.lhs law04.rhs := Derives.fromBasis (by simp [basis])
    have substituted := core.subst (instantiateThreeWords (substitution 0) (substitution 1) guard)
    change Derives basis
      (((((substitution 0 ++ substitution 1) ++ substitution 0) ++ substitution 1) ++ guard))
      (((((substitution 0 ++ substitution 1) ++ substitution 1) ++ substitution 0) ++ guard))
    simpa [law04, instantiateThreeWords, Word.bind, Word.append, Word.singleton,
      Word.append_assoc] using substituted
  · exact Derives.appendRight
      (Derives.subst (Derives.fromBasis (e := law03) (by simp [basis])) substitution) guard
  · exact Derives.appendRight
      (Derives.subst (Derives.fromBasis (e := law06) (by simp [basis])) substitution) guard

private theorem bind_append (left right : Word Nat) (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution = left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind (word : Word Nat) (first second : Nat → Word Nat) :
    (word.bind first).bind second = word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

/-- Structural, unrestricted lifting. The right-context case enlarges the
guard, while substitution composes nonempty word substitutions. -/
theorem lowerDerivationUnderRight {left right : Word Nat}
    (derivation : Derives S5_379.basis left right)
    (substitution : Nat → Word Nat) (guard : Word Nat) :
    Derives basis (left.bind substitution ++ guard) (right.bind substitution ++ guard) := by
  induction derivation generalizing substitution guard with
  | fromBasis member => exact lowerBasisUnderRight _ member substitution guard
  | refl => exact Derives.refl _
  | symm _ hypothesis => exact (hypothesis substitution guard).symm
  | trans _ _ first second => exact (first substitution guard).trans (second substitution guard)
  | prepend front _ hypothesis =>
      simpa [bind_append, Word.append_assoc] using
        Derives.prepend (front.bind substitution) (hypothesis substitution guard)
  | appendRight _ suffix hypothesis =>
      simpa [bind_append, Word.append_assoc] using
        hypothesis substitution (suffix.bind substitution ++ guard)
  | subst _ first hypothesis =>
      simpa [bind_bind] using hypothesis (fun letter => (first letter).bind substitution) guard

theorem lowerListUnderRight {left right : List Nat} (derivation : S5_379.ListDerives left right)
    (guard : List Nat) (nonempty : guard ≠ []) :
    ListDerives (left ++ guard) (right ++ guard) := by
  cases derivation with
  | empty => simpa using S5_107.ListDerives.refl (basis := basis) guard
  | @words leftHead rightHead leftTail rightTail proof =>
      obtain ⟨guardHead, guardTail, rfl⟩ := List.exists_cons_of_ne_nil nonempty
      exact S5_107.ListDerives.words <| by
        simpa [Word.bind_singleton, S5_107.listWordOfCons, Word.append] using
          lowerDerivationUnderRight proof Word.singleton (S5_107.listWordOfCons guardHead guardTail)

end SemigroupBasis.CoRoots.Order6Day7.Level2.Rank127
