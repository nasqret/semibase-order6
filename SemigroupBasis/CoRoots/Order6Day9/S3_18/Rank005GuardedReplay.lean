import SemigroupBasis.CoRoots.S5_1000
import SemigroupBasis.Generated.CatalogueOrder3
import SemigroupBasis.Generated.CatalogueOrder4
import SemigroupBasis.FiniteCertificate

/-!
# The original eleven-law Rank005 presentation and guarded lower replay

The raw atlas sigma is kept literally separate from the later eighteen-law
bounded presentation. Only raw laws 00, 01, 05, 07, and 09 are needed to
replay every complete S5_1000 derivation behind an arbitrary nonempty prefix.
The five-step contextual swap retains its exact nonempty final guard.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank005GuardedReplay

open SemigroupBasis

abbrev leftTable : FiniteTable := Generated.Catalogue.S3_18.table
abbrev rightTable : FiniteTable := Generated.Catalogue.S4_62.table
abbrev lowerBasis : List (Identity Nat) := SemigroupBasis.CoRoots.S5_1000.basis

def law00 : Identity Nat := ⟨Word.mk 0 [0], Word.mk 0 [0, 0, 0, 0]⟩
def law01 : Identity Nat := ⟨Word.mk 0 [0, 0, 0, 1], Word.mk 0 [1]⟩
def law02 : Identity Nat := ⟨Word.mk 0 [0, 0, 1, 0], Word.mk 0 [1, 1, 1, 1]⟩
def law03 : Identity Nat := ⟨Word.mk 0 [0, 1, 0], Word.mk 0 [1, 0, 0]⟩
def law04 : Identity Nat := ⟨Word.mk 0 [0, 1, 1], Word.mk 0 [1, 0, 1]⟩
def law05 : Identity Nat := ⟨Word.mk 0 [0, 1, 1], Word.mk 0 [1, 1, 0]⟩
def law06 : Identity Nat := ⟨Word.mk 0 [0, 1, 1, 1], Word.mk 0 [1, 1, 1, 0]⟩
def law07 : Identity Nat := ⟨Word.mk 0 [0, 1, 2], Word.mk 0 [1, 0, 2]⟩
def law08 : Identity Nat := ⟨Word.mk 0 [0, 1, 2, 1], Word.mk 0 [1, 1, 2, 0]⟩
def law09 : Identity Nat := ⟨Word.mk 0 [1, 2, 0], Word.mk 0 [2, 1, 0]⟩
def law10 : Identity Nat := ⟨Word.mk 0 [1, 2, 1], Word.mk 0 [2, 1, 1]⟩

/-- The original raw atlas list, with no bounded separator axiom added. -/
def basis : List (Identity Nat) :=
  [law00, law01, law02, law03, law04, law05, law06, law07,
    law08, law09, law10]

def displayedBasisSHA256 : String :=
  "7092fdf6d993c0bbaaf37ef17483bcac33ed0a2db72ef407f75018a122c491dc"

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem modelsLeft : Models leftTable.semigroup basis :=
  FiniteCertificate.checkModels_sound leftTable basis toFinThree (by decide)

theorem modelsRight : Models rightTable.semigroup basis :=
  FiniteCertificate.checkModels_sound rightTable basis toFinThree (by decide)

private def instantiateThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | marker + 3 => Word.singleton (marker + 3)

theorem derivesPowerExpansion (first : Word Nat) :
    Derives basis (first ++ first)
      ((((first ++ first) ++ first) ++ first) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [0]) (Word.mk 0 [0, 0, 0, 0]) :=
    Derives.fromBasis (e := law00) (by decide)
  have substituted :=
    Derives.subst primitive (instantiateThree first first first)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesPrefixExpansion (first final : Word Nat) :
    Derives basis (first ++ final)
      ((((first ++ first) ++ first) ++ first) ++ final) := by
  have primitive :
      Derives basis (Word.mk 0 [1]) (Word.mk 0 [0, 0, 0, 1]) :=
    (Derives.fromBasis (e := law01) (by decide)).symm
  have substituted :=
    Derives.subst primitive (instantiateThree first final final)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesInternalHeadExchange
    (first middle final : Word Nat) :
    Derives basis
      (((first ++ first) ++ middle) ++ final)
      (((first ++ middle) ++ first) ++ final) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 1, 2]) (Word.mk 0 [1, 0, 2]) :=
    Derives.fromBasis (e := law07) (by decide)
  have substituted :=
    Derives.subst primitive (instantiateThree first middle final)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesReturnSwap (first middle final : Word Nat) :
    Derives basis
      (((first ++ middle) ++ final) ++ first)
      (((first ++ final) ++ middle) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 2, 0]) (Word.mk 0 [2, 1, 0]) :=
    Derives.fromBasis (e := law09) (by decide)
  have substituted :=
    Derives.subst primitive (instantiateThree first middle final)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The lower head-changing swap is recovered only behind a nonempty stem
and before a nonempty final block, by five association-fixed raw-law steps. -/
theorem derivesContextualPrefixSwap
    (stem first second final : Word Nat) :
    Derives basis
      (((stem ++ first) ++ second) ++ final)
      (((stem ++ second) ++ first) ++ final) := by
  have expand :
      Derives basis
        (((stem ++ first) ++ second) ++ final)
        ((((((stem ++ stem) ++ stem) ++ stem) ++ first) ++ second) ++ final) := by
    simpa [Word.append_assoc] using
      derivesPrefixExpansion stem ((first ++ second) ++ final)
  have move :
      Derives basis
        ((((((stem ++ stem) ++ stem) ++ stem) ++ first) ++ second) ++ final)
        ((((((stem ++ stem) ++ stem) ++ first) ++ second) ++ stem) ++ final) := by
    simpa [Word.append_assoc] using
      derivesInternalHeadExchange stem
        (((stem ++ stem) ++ first) ++ second) final
  have switched :
      Derives basis
        ((((((stem ++ stem) ++ stem) ++ first) ++ second) ++ stem) ++ final)
        ((((((stem ++ stem) ++ stem) ++ second) ++ first) ++ stem) ++ final) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (Derives.prepend (stem ++ stem)
          (derivesReturnSwap stem first second)) final
  have returned :
      Derives basis
        ((((((stem ++ stem) ++ stem) ++ second) ++ first) ++ stem) ++ final)
        ((((((stem ++ stem) ++ stem) ++ stem) ++ second) ++ first) ++ final) := by
    simpa [Word.append_assoc] using
      (derivesInternalHeadExchange stem
        (((stem ++ stem) ++ second) ++ first) final).symm
  have contracted :
      Derives basis
        ((((((stem ++ stem) ++ stem) ++ stem) ++ second) ++ first) ++ final)
        (((stem ++ second) ++ first) ++ final) := by
    simpa [Word.append_assoc] using
      (derivesPrefixExpansion stem ((second ++ first) ++ final)).symm
  exact expand.trans (move.trans (switched.trans (returned.trans contracted)))

theorem derivesFinalMove (first second : Word Nat) :
    Derives basis
      ((((first ++ first) ++ first) ++ second) ++ second)
      ((((first ++ first) ++ second) ++ second) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 1, 1]) (Word.mk 0 [1, 1, 0]) :=
    Derives.fromBasis (e := law05) (by decide)
  have substituted :=
    Derives.subst primitive (instantiateThree first second second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using Derives.prepend first substituted

private theorem bind_append
    (left right : Word Nat) (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution =
      left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (word : Word Nat) (first second : Nat → Word Nat) :
    (word.bind first).bind second =
      word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- Replay every lower derivation constructor with arbitrary nonempty
substitutions and an unchanged arbitrary nonempty prefix. -/
theorem liftLowerWithPrefix
    {left right : Word Nat}
    (derivation : Derives lowerBasis left right)
    (stem : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis
      (stem ++ left.bind substitution) (stem ++ right.bind substitution) := by
  induction derivation generalizing stem substitution with
  | fromBasis member =>
      simp only [lowerBasis, SemigroupBasis.CoRoots.S5_1000.basis,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · change Derives basis
          (stem ++ (Word.mk 0 [0]).bind substitution)
          (stem ++ (Word.mk 0 [0, 0, 0, 0]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          Derives.prepend stem (derivesPowerExpansion (substitution 0))
      · change Derives basis
          (stem ++ (Word.mk 0 [1]).bind substitution)
          (stem ++ (Word.mk 0 [0, 0, 0, 1]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          Derives.prepend stem
            (derivesPrefixExpansion (substitution 0) (substitution 1))
      · change Derives basis
          (stem ++ (Word.mk 0 [1, 2]).bind substitution)
          (stem ++ (Word.mk 1 [0, 2]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          derivesContextualPrefixSwap stem
            (substitution 0) (substitution 1) (substitution 2)
      · change Derives basis
          (stem ++ (Word.mk 0 [0, 0, 1, 1]).bind substitution)
          (stem ++ (Word.mk 0 [0, 1, 1, 0]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          Derives.prepend stem
            (derivesFinalMove (substitution 0) (substitution 1))
  | refl => exact Derives.refl _
  | symm _ induction => exact (induction stem substitution).symm
  | trans _ _ first second =>
      exact (first stem substitution).trans (second stem substitution)
  | prepend left _ induction =>
      simpa [bind_append, Word.append_assoc] using
        induction (stem ++ left.bind substitution) substitution
  | appendRight _ right induction =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight
          (induction stem substitution) (right.bind substitution)
  | subst _ next induction =>
      simpa [bind_bind] using
        induction stem (fun letter => (next letter).bind substitution)

theorem liftLowerWithPrefixIdentity
    {left right : Word Nat}
    (derivation : Derives lowerBasis left right) (stem : Word Nat) :
    Derives basis (stem ++ left) (stem ++ right) := by
  simpa only [bind_singleton] using
    liftLowerWithPrefix derivation stem Word.singleton

end SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank005GuardedReplay
