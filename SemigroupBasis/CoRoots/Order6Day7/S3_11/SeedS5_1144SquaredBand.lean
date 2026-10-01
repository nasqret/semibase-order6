import SemigroupBasis.CoRoots.Order6Day7.S3_11.Rank003
import SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroupNormalizationSyntax
import SemigroupBasis.CoRoots.S5_1092Family

/-!
# Parity-preserving square lift of the complete regular-band calculus

The S5_1092/S5_1144 regular-band axiom `x = xx` is FALSE on S3_11 and
must never be transported directly.  Instead lift every complete lower-band
derivation between SQUARES, using the exact five-edge frozen rank-003
regular-band macro and the displayed square-factorization law.

Independently transport the complete two-law regular-orthogroup syntax; its
double-insertion law is a separately typed three-edge frozen path.  This
provides already-proved arbitrary two-sided guarded parity reduction.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_1144

open SemigroupBasis

private abbrev targetBasis : List (Identity Nat) := Rank003.basis

private abbrev regularBandBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.S5_1092.basis

private abbrev orthogroupBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroup.basis

private def word (first : Nat) (rest : List Nat) : Word Nat :=
  Word.mk first rest

private def instantiateThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

private def surround
    (front : Option (Word Nat)) (middle : Word Nat)
    (suffix : Option (Word Nat)) : Word Nat :=
  match front, suffix with
  | none, none => middle
  | some first, none => first ++ middle
  | none, some last => middle ++ last
  | some first, some last => (first ++ middle) ++ last

private theorem displayedForward
    (identity : Identity Nat) (member : identity ∈ targetBasis)
    (substitution : Nat → Word Nat)
    (front suffix : Option (Word Nat)) :
    Derives targetBasis
      (surround front (identity.lhs.bind substitution) suffix)
      (surround front (identity.rhs.bind substitution) suffix) := by
  have primitive := Derives.subst (Derives.fromBasis member) substitution
  cases front with
  | none =>
      cases suffix with
      | none => exact primitive
      | some last => exact Derives.appendRight primitive last
  | some first =>
      cases suffix with
      | none => exact Derives.prepend first primitive
      | some last =>
          exact Derives.appendRight (Derives.prepend first primitive) last

/-- Frozen period-two power expansion for every nonempty substituted word. -/
theorem derivesPowerExpansion
    (source : Word Nat) :
    Derives targetBasis source ((source ++ source) ++ source) := by
  have primitive :
      Derives targetBasis (word 0 []) (word 0 [0, 0]) :=
    Derives.fromBasis (e := Rank003.law00)
      (show Rank003.law00 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive (instantiateThree source source source)
  simpa [word, instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Exact frozen factorization `(uv)^2 = u^2 v^2`. -/
theorem derivesSquareFactorization
    (first second : Word Nat) :
    Derives targetBasis
      ((first ++ second) ++ (first ++ second))
      ((first ++ first) ++ (second ++ second)) := by
  have primitive :
      Derives targetBasis (word 0 [0, 1, 1]) (word 0 [1, 0, 1]) :=
    Derives.fromBasis (e := Rank003.law06)
      (show Rank003.law06 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive.symm (instantiateThree first second second)
  simpa [word, instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Three separately typed frozen edges prove `xyzx = xyxxzx`. -/
private theorem regularOrthogroupPrimitive :
    Derives targetBasis (word 0 [1, 2, 0]) (word 0 [1, 0, 0, 2, 0]) := by
  have step00 :
      Derives targetBasis (word 0 [1, 2, 0])
        (word 0 [0, 0, 1, 2, 0]) := by
    exact displayedForward Rank003.law00
      (show Rank003.law00 ∈ targetBasis by decide)
      (instantiateThree (word 0 []) (word 1 []) (word 2 []))
      none (some (word 1 [2, 0]))
  have step01 :
      Derives targetBasis (word 0 [0, 0, 1, 2, 0])
        (word 0 [0, 1, 0, 2, 0]) := by
    exact displayedForward Rank003.law07
      (show Rank003.law07 ∈ targetBasis by decide)
      (instantiateThree (word 0 []) (word 1 []) (word 2 []))
      (some (word 0 [])) none
  have step02 :
      Derives targetBasis (word 0 [0, 1, 0, 2, 0])
        (word 0 [1, 0, 0, 2, 0]) := by
    exact displayedForward Rank003.law03
      (show Rank003.law03 ∈ targetBasis by decide)
      (instantiateThree (word 0 []) (word 1 []) (word 2 []))
      none (some (word 2 [0]))
  exact step00.trans (step01.trans step02)

/-- Regular-orthogroup insertion with arbitrary nonempty blocks. -/
theorem derivesRegularOrthogroupExpansion
    (first second third : Word Nat) :
    Derives targetBasis
      (((first ++ second) ++ third) ++ first)
      (((((first ++ second) ++ first) ++ first) ++ third) ++ first) := by
  have substituted :=
    Derives.subst regularOrthogroupPrimitive
      (instantiateThree first second third)
  simpa [word, instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- The complete two-law orthogroup syntax embeds in the EXACT frozen basis. -/
theorem regularOrthogroupLawDerives
    (identity : Identity Nat) (member : identity ∈ orthogroupBasis) :
    Derives targetBasis identity.lhs identity.rhs := by
  simp only [orthogroupBasis,
    SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroup.basis,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact Derives.fromBasis (e := Rank003.law00)
      (show Rank003.law00 ∈ targetBasis by decide)
  · exact regularOrthogroupPrimitive

/-- Transport arbitrary already-proved orthogroup syntax, not semantics. -/
theorem transportRegularOrthogroupDerivation
    {left right : Word Nat}
    (derivation : Derives orthogroupBasis left right) :
    Derives targetBasis left right :=
  Derives.transport regularOrthogroupLawDerives derivation

/-- List-level transport of the completed two-sided guarded parity calculus. -/
theorem transportRegularOrthogroupList
    {left right : List Nat}
    (derivation :
      SemigroupBasis.CoRoots.S5_107.ListDerives orthogroupBasis left right) :
    SemigroupBasis.CoRoots.S5_107.ListDerives targetBasis left right := by
  cases derivation with
  | empty =>
      exact SemigroupBasis.CoRoots.S5_107.ListDerives.empty
  | words primitive =>
      exact SemigroupBasis.CoRoots.S5_107.ListDerives.words
        (transportRegularOrthogroupDerivation primitive)

/-- Five typed frozen edges prove the regular-band relation BETWEEN SQUARES.
No unguarded idempotence or period-one regular-band axiom is asserted. -/
private theorem regularBandSquaredPrimitive :
    Derives targetBasis
      (word 0 [1, 2, 0, 0, 1, 2, 0])
      (word 0 [1, 0, 2, 0, 0, 1, 0, 2, 0]) := by
  have step00 :
      Derives targetBasis
        (word 0 [1, 2, 0, 0, 1, 2, 0])
        (word 0 [0, 0, 1, 2, 0, 0, 1, 2, 0]) := by
    exact displayedForward Rank003.law00
      (show Rank003.law00 ∈ targetBasis by decide)
      (instantiateThree (word 0 []) (word 1 []) (word 2 []))
      none (some (word 1 [2, 0, 0, 1, 2, 0]))
  have step01 :
      Derives targetBasis
        (word 0 [0, 0, 1, 2, 0, 0, 1, 2, 0])
        (word 0 [0, 1, 0, 2, 0, 0, 1, 2, 0]) := by
    exact displayedForward Rank003.law07
      (show Rank003.law07 ∈ targetBasis by decide)
      (instantiateThree (word 0 []) (word 1 []) (word 2 []))
      (some (word 0 [])) (some (word 0 [1, 2, 0]))
  have step02 :
      Derives targetBasis
        (word 0 [0, 1, 0, 2, 0, 0, 1, 2, 0])
        (word 0 [0, 1, 0, 2, 0, 1, 0, 2, 0]) := by
    exact displayedForward Rank003.law07
      (show Rank003.law07 ∈ targetBasis by decide)
      (instantiateThree (word 0 []) (word 1 []) (word 2 []))
      (some (word 0 [0, 1, 0, 2])) none
  have step03 :
      Derives targetBasis
        (word 0 [0, 1, 0, 2, 0, 1, 0, 2, 0])
        (word 0 [1, 0, 0, 2, 0, 1, 0, 2, 0]) := by
    exact displayedForward Rank003.law03
      (show Rank003.law03 ∈ targetBasis by decide)
      (instantiateThree (word 0 []) (word 1 []) (word 2 []))
      none (some (word 2 [0, 1, 0, 2, 0]))
  have step04 :
      Derives targetBasis
        (word 0 [1, 0, 0, 2, 0, 1, 0, 2, 0])
        (word 0 [1, 0, 2, 0, 0, 1, 0, 2, 0]) := by
    exact displayedForward Rank003.law03
      (show Rank003.law03 ∈ targetBasis by decide)
      (instantiateThree (word 0 []) (word 2 []) (word 2 []))
      (some (word 0 [1])) (some (word 1 [0, 2, 0]))
  exact step00.trans (step01.trans (step02.trans (step03.trans step04)))

/-- The complete lower regular-band axiom is admissible only after squaring
both whole substituted words. -/
theorem derivesRegularBandSquared
    (first second third : Word Nat) :
    Derives targetBasis
      ((((first ++ second) ++ third) ++ first) ++
        (((first ++ second) ++ third) ++ first))
      (((((first ++ second) ++ first) ++ third) ++ first) ++
        ((((first ++ second) ++ first) ++ third) ++ first)) := by
  have substituted :=
    Derives.subst regularBandSquaredPrimitive
      (instantiateThree first second third)
  simpa [word, instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Idempotence is likewise transported only as `x² = x⁴`. -/
theorem derivesBandIdempotenceSquared
    (source : Word Nat) :
    Derives targetBasis
      (source ++ source)
      ((source ++ source) ++ (source ++ source)) := by
  have expanded := Derives.prepend source (derivesPowerExpansion source)
  simpa [Word.append_assoc] using expanded

private theorem bind_append
    (left right : Word Nat) (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution =
      left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (source : Word Nat) (first second : Nat → Word Nat) :
    (source.bind first).bind second =
      source.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem squareLiftPrepend
    (front : Word Nat) {left right : Word Nat}
    (middle : Derives targetBasis (left ++ left) (right ++ right)) :
    Derives targetBasis
      ((front ++ left) ++ (front ++ left))
      ((front ++ right) ++ (front ++ right)) := by
  exact (derivesSquareFactorization front left).trans
    ((Derives.prepend (front ++ front) middle).trans
      (derivesSquareFactorization front right).symm)

private theorem squareLiftAppend
    {left right : Word Nat} (suffix : Word Nat)
    (middle : Derives targetBasis (left ++ left) (right ++ right)) :
    Derives targetBasis
      ((left ++ suffix) ++ (left ++ suffix))
      ((right ++ suffix) ++ (right ++ suffix)) := by
  exact (derivesSquareFactorization left suffix).trans
    ((Derives.appendRight middle (suffix ++ suffix)).trans
      (derivesSquareFactorization right suffix).symm)

/-- Structural lift of EVERY complete regular-band derivation between whole
squares, under arbitrary nonempty substitutions and both contexts. -/
theorem liftRegularBandDerivationSquared
    {left right : Word Nat}
    (derivation : Derives regularBandBasis left right)
    (substitution : Nat → Word Nat) :
    Derives targetBasis
      (left.bind substitution ++ left.bind substitution)
      (right.bind substitution ++ right.bind substitution) := by
  induction derivation generalizing substitution with
  | fromBasis member =>
      simp only [regularBandBasis, SemigroupBasis.CoRoots.S5_1092.basis,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact derivesBandIdempotenceSquared (substitution 0)
      · exact derivesRegularBandSquared
          (substitution 0) (substitution 1) (substitution 2)
  | refl => exact Derives.refl _
  | symm _ hypothesis => exact (hypothesis substitution).symm
  | trans _ _ first second =>
      exact (first substitution).trans (second substitution)
  | prepend front _ hypothesis =>
      simpa [bind_append] using
        squareLiftPrepend (front.bind substitution) (hypothesis substitution)
  | appendRight _ suffix hypothesis =>
      simpa [bind_append] using
        squareLiftAppend (suffix.bind substitution) (hypothesis substitution)
  | subst _ first hypothesis =>
      simpa [bind_bind] using
        hypothesis (fun letter => (first letter).bind substitution)

private theorem bind_singleton (source : Word Nat) :
    source.bind Word.singleton = source := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- List-level square lift handles both the empty and nonempty lower proofs. -/
theorem liftRegularBandListSquared
    {left right : List Nat}
    (derivation :
      SemigroupBasis.CoRoots.S5_107.ListDerives
        regularBandBasis left right) :
    SemigroupBasis.CoRoots.S5_107.ListDerives targetBasis
      (left ++ left) (right ++ right) := by
  cases derivation with
  | empty =>
      exact SemigroupBasis.CoRoots.S5_107.ListDerives.empty
  | words primitive =>
      have lifted :=
        liftRegularBandDerivationSquared primitive Word.singleton
      rw [bind_singleton, bind_singleton] at lifted
      simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
        Word.toList_append] using
          SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord lifted

end SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_1144
