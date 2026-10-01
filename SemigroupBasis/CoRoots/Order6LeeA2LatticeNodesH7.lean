import SemigroupBasis.CoRoots.S5_415
import SemigroupBasis.CoRoots.S5_415EndpointConnectivity
import SemigroupBasis.CoRoots.S5_415PublishedCompletion
import SemigroupBasis.CoRoots.S5_415SemanticSplitCompleteness
import SemigroupBasis.CoRoots.S5_868MaximalFactors
import SemigroupBasis.DerivationQuotient
import SemigroupBasis.Generated.Order6LeeA2LatticeNodes
import SemigroupBasis.Opposite
import SemigroupBasis.Regular
import SemigroupBasis.Schutzenberger

/-!
# Reusable adapter layer for Lee A2 lattice system H7

This module records only consequences of the generated six-law system
`SystemH7b8c7ea4dec1`.  It does not assume the remaining rooted Brandt
normalizer needed by the order-six endpoints.

The last three laws give a useful protected commutation macro:

```text
G X²Y²
  <- G X²Y²X²Y²       (law3)
  -> G Y²X²Y²         (law4)
  <- G Y²X²Y²X²       (law5)
  -> G Y²X²            (law3)
```

Consequently every `S5_415` derivation can be replayed after a nonempty
prefix, and the completed `S5_868` marked-digraph presentation transports
directly through the first three H7 laws.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesH7

open SemigroupBasis

namespace GeneratedH7

export SemigroupBasis.Generated.Order6LeeA2LatticeNodes.SystemH7b8c7ea4dec1
  (law0 law1 law2 law3 law4 law5 basis)

end GeneratedH7

namespace Brandt

export SemigroupBasis.CoRoots.S5_415
  (CorrespondingIsolatedSplit IncomingPivotPath
    OptionalSameBrandtSignature RepeatedWord
    SquaredWalkBankAlongPivotPath brandtSupportCard
    brandtSupportCard_eq_of_sameBrandtSignature
    brandtSupportCard_lt_of_optionalWordOfList_of_missing
    correspondingIsolatedSplit_of_sameBrandtSignature
    exists_isolated_split_of_not_repeated optionalWordLetters
    optionalWordOfList squaredWalkBank)

end Brandt

namespace Marked

export SemigroupBasis.CoRoots.S5_868
  (derivesAnchoredLoopSwap derivesPowerExpansion
    derivesSandwichExpansion)

end Marked

abbrev law0 : Identity Nat := GeneratedH7.law0
abbrev law1 : Identity Nat := GeneratedH7.law1
abbrev law2 : Identity Nat := GeneratedH7.law2
abbrev law3 : Identity Nat := GeneratedH7.law3
abbrev law4 : Identity Nat := GeneratedH7.law4
abbrev law5 : Identity Nat := GeneratedH7.law5

/-- The exact generated basis shared by `S6_8562` and `S6_11276`. -/
abbrev basis : List (Identity Nat) := GeneratedH7.basis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

private def powerContractionLaw : Identity Nat :=
  ⟨w 0 [0, 0], w 0 [0]⟩

private def sandwichContractionLaw : Identity Nat :=
  ⟨w 0 [1, 0, 1, 0], w 0 [1, 0]⟩

private def graphSwitchLaw : Identity Nat :=
  ⟨w 0 [1, 0, 2, 0], w 0 [2, 0, 1, 0]⟩

private def squareCollapseLaw : Identity Nat :=
  ⟨w 0 [0, 1, 1, 0, 0, 1, 1], w 0 [0, 1, 1]⟩

private def guardedSquareSwitchLaw : Identity Nat :=
  ⟨w 0 [1, 1, 2, 2, 1, 1, 2, 2],
    w 0 [2, 2, 1, 1, 2, 2]⟩

private def squareTailContractionLaw : Identity Nat :=
  ⟨w 0 [0, 1, 1, 0, 0, 1, 1], w 0 [0, 1, 1, 0, 0]⟩

private theorem powerContractionLaw_mem :
    powerContractionLaw ∈ basis := by
  decide

private theorem sandwichContractionLaw_mem :
    sandwichContractionLaw ∈ basis := by
  decide

private theorem graphSwitchLaw_mem :
    graphSwitchLaw ∈ basis := by
  decide

private theorem squareCollapseLaw_mem :
    squareCollapseLaw ∈ basis := by
  decide

private theorem guardedSquareSwitchLaw_mem :
    guardedSquareSwitchLaw ∈ basis := by
  decide

private theorem squareTailContractionLaw_mem :
    squareTailContractionLaw ∈ basis := by
  decide

private def instantiateThreeWords
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

private theorem derivesBasisSubstitution
    (identity : Identity Nat) (member : identity ∈ basis)
    (substitution : Nat → Word Nat) :
    Derives basis
      (identity.lhs.bind substitution)
      (identity.rhs.bind substitution) :=
  Derives.subst (Derives.fromBasis member) substitution

private theorem derivesSquareCollapse (left right : Word Nat) :
    Derives basis
      (left ++ left ++ right ++ right ++ left ++ left ++ right ++ right)
      (left ++ left ++ right ++ right) := by
  have substituted :=
    derivesBasisSubstitution squareCollapseLaw
      squareCollapseLaw_mem
      (instantiateThreeWords left right right)
  simpa [squareCollapseLaw, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

private theorem derivesGuardedSquareSwitch
    (guard left right : Word Nat) :
    Derives basis
      (guard ++ left ++ left ++ right ++ right ++
        left ++ left ++ right ++ right)
      (guard ++ right ++ right ++ left ++ left ++ right ++ right) := by
  have substituted :=
    derivesBasisSubstitution guardedSquareSwitchLaw
      guardedSquareSwitchLaw_mem
      (instantiateThreeWords guard left right)
  simpa [guardedSquareSwitchLaw, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

private theorem derivesSquareTailContraction
    (left right : Word Nat) :
    Derives basis
      (left ++ left ++ right ++ right ++ left ++ left ++ right ++ right)
      (left ++ left ++ right ++ right ++ left ++ left) := by
  have substituted :=
    derivesBasisSubstitution squareTailContractionLaw
      squareTailContractionLaw_mem
      (instantiateThreeWords left right right)
  simpa [squareTailContractionLaw, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Commute two square blocks while preserving an arbitrary nonempty prefix.
This is the H7 replacement for the unguarded square-commutation axiom of
`S5_415`. -/
theorem derivesGuardedSquareCommutation
    (guard left right : Word Nat) :
    Derives basis
      (guard ++ left ++ left ++ right ++ right)
      (guard ++ right ++ right ++ left ++ left) := by
  have first :=
    Derives.prepend guard (derivesSquareCollapse left right).symm
  have second := derivesGuardedSquareSwitch guard left right
  have third :=
    Derives.prepend guard
      (derivesSquareTailContraction right left).symm
  have fourth :=
    Derives.prepend guard (derivesSquareCollapse right left)
  simp only [Word.append_assoc] at first second third fourth ⊢
  exact first.trans (second.trans (third.trans fourth))

/-- The exact semigroup-theoretic weakening of commuting idempotents supplied
by H7: idempotents commute after every nonempty left guard. -/
def LeftGuardedIdempotentsCommute (G : Semigroup S) : Prop :=
  ∀ guard {left right},
    G.IsIdempotent left →
      G.IsIdempotent right →
        G.mul (G.mul guard left) right =
          G.mul (G.mul guard right) left

/-- Pointwise form of H7 square commutation with its required nonempty
left guard retained. -/
def LeftGuardedSquaresCommute (G : Semigroup S) : Prop :=
  ∀ guard left right,
    G.mul (G.mul guard (G.mul left left)) (G.mul right right) =
      G.mul (G.mul guard (G.mul right right)) (G.mul left left)

/-- Derivably idempotent words commute after a protected H7 prefix.  This is
the precise commutation used in the middle of the regular-product and
Kublanovskii separation calculations; global idempotent commutation is not
required there. -/
theorem derivesGuardedCommuteIdempotents
    (guard left right : Word Nat)
    (leftIdempotent : Derives basis (left ++ left) left)
    (rightIdempotent : Derives basis (right ++ right) right) :
    Derives basis
      ((guard ++ left) ++ right)
      ((guard ++ right) ++ left) := by
  have expandLeft :
      Derives basis
        ((guard ++ left) ++ right)
        (((guard ++ left) ++ left) ++ right) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (Derives.prepend guard leftIdempotent.symm) right
  have expandRight :
      Derives basis
        (((guard ++ left) ++ left) ++ right)
        (((guard ++ left) ++ left) ++ (right ++ right)) :=
    Derives.prepend ((guard ++ left) ++ left)
      rightIdempotent.symm
  have commute :
      Derives basis
        (((guard ++ left) ++ left) ++ (right ++ right))
        (((guard ++ right) ++ right) ++ (left ++ left)) := by
    simpa [Word.append_assoc] using
      derivesGuardedSquareCommutation guard left right
  have contractRight :
      Derives basis
        (((guard ++ right) ++ right) ++ (left ++ left))
        ((guard ++ right) ++ (left ++ left)) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (Derives.prepend guard rightIdempotent) (left ++ left)
  have contractLeft :
      Derives basis
        ((guard ++ right) ++ (left ++ left))
        ((guard ++ right) ++ left) :=
    Derives.prepend (guard ++ right) leftIdempotent
  exact
    expandLeft.trans <| expandRight.trans <| commute.trans <|
      contractRight.trans contractLeft

/-- The presented H7 term semigroup satisfies left-guarded idempotent
commutation.  Representatives turn quotient idempotence back into word
derivations, where `derivesGuardedCommuteIdempotents` applies. -/
theorem termSemigroup_leftGuardedIdempotentsCommute :
    LeftGuardedIdempotentsCommute (termSemigroup basis) := by
  intro guard left right leftIdempotent rightIdempotent
  obtain ⟨guardWord, rfl⟩ :=
    (derivationCongruence basis).projection_surjective guard
  obtain ⟨leftWord, rfl⟩ :=
    (derivationCongruence basis).projection_surjective left
  obtain ⟨rightWord, rfl⟩ :=
    (derivationCongruence basis).projection_surjective right
  have leftDerivation :
      Derives basis (leftWord ++ leftWord) leftWord := by
    apply (termClass_eq_iff_derives basis).mp
    simpa only [termSemigroup_mul_termClass] using leftIdempotent
  have rightDerivation :
      Derives basis (rightWord ++ rightWord) rightWord := by
    apply (termClass_eq_iff_derives basis).mp
    simpa only [termSemigroup_mul_termClass] using rightIdempotent
  simpa only [termSemigroup_mul_termClass] using
    (termClass_eq_iff_derives basis).2 <|
      derivesGuardedCommuteIdempotents
        guardWord leftWord rightWord leftDerivation rightDerivation

/-- Direct term-model form of the guarded square law. -/
theorem termSemigroup_leftGuardedSquaresCommute :
    LeftGuardedSquaresCommute (termSemigroup basis) := by
  intro guard left right
  obtain ⟨guardWord, rfl⟩ :=
    (derivationCongruence basis).projection_surjective guard
  obtain ⟨leftWord, rfl⟩ :=
    (derivationCongruence basis).projection_surjective left
  obtain ⟨rightWord, rfl⟩ :=
    (derivationCongruence basis).projection_surjective right
  change
    (termSemigroup basis).mul
        ((termSemigroup basis).mul (termClass basis guardWord)
          ((termSemigroup basis).mul
            (termClass basis leftWord) (termClass basis leftWord)))
        ((termSemigroup basis).mul
          (termClass basis rightWord) (termClass basis rightWord)) =
      (termSemigroup basis).mul
        ((termSemigroup basis).mul (termClass basis guardWord)
          ((termSemigroup basis).mul
            (termClass basis rightWord) (termClass basis rightWord)))
        ((termSemigroup basis).mul
          (termClass basis leftWord) (termClass basis leftWord))
  simp only [termSemigroup_mul_termClass]
  exact (termClass_eq_iff_derives basis).2 <| by
    simpa [Word.append_assoc] using
      derivesGuardedSquareCommutation guardWord leftWord rightWord

/-- The orientation check for the Schutzenberger route.  Prefix-guarded
square commutation becomes ordinary square commutation in every right
Schutzenberger quotient of the *opposite* semigroup: the right translate in
the opposite multiplication is exactly a left guard in the original
semigroup.  No regularity assumption on `z` is needed for this step. -/
theorem oppositeRightSchutzenbergerQuotient_squaresCommute
    {G : Semigroup S}
    (guarded : LeftGuardedSquaresCommute G) (z : S) :
    let C :=
      Semigroup.rightSchutzenbergerCongruence G.opposite z
    ∀ left right : C.Quotient,
      C.quotientSemigroup.mul
          (C.quotientSemigroup.mul left left)
          (C.quotientSemigroup.mul right right) =
        C.quotientSemigroup.mul
          (C.quotientSemigroup.mul right right)
          (C.quotientSemigroup.mul left left) := by
  dsimp
  intro left right
  refine _root_.Quotient.inductionOn left ?_
  intro leftRepresentative
  refine _root_.Quotient.inductionOn right ?_
  intro rightRepresentative
  let C :=
    Semigroup.rightSchutzenbergerCongruence G.opposite z
  change
    C.classOf
        (G.opposite.mul
          (G.opposite.mul leftRepresentative leftRepresentative)
          (G.opposite.mul rightRepresentative rightRepresentative)) =
      C.classOf
        (G.opposite.mul
          (G.opposite.mul rightRepresentative rightRepresentative)
          (G.opposite.mul leftRepresentative leftRepresentative))
  apply
    (Semigroup.rightSchutzenberger_classOf_eq_iff
      G.opposite z).2
  intro translate _translateInPrincipalSandwich
  apply Or.inl
  simpa only [Semigroup.opposite_mul, G.assoc] using
    guarded translate rightRepresentative leftRepresentative

/-- Specialization of the preceding dual-orientation theorem to the H7 term
semigroup. -/
theorem termSemigroupOpposite_rightSchutzenbergerQuotient_squaresCommute
    (z : TermSemigroup basis) :
    let G := (termSemigroup basis).opposite
    let C := Semigroup.rightSchutzenbergerCongruence G z
    ∀ left right : C.Quotient,
      C.quotientSemigroup.mul
          (C.quotientSemigroup.mul left left)
          (C.quotientSemigroup.mul right right) =
        C.quotientSemigroup.mul
          (C.quotientSemigroup.mul right right)
          (C.quotientSemigroup.mul left left) :=
  oppositeRightSchutzenbergerQuotient_squaresCommute
    termSemigroup_leftGuardedSquaresCommute z

private theorem bindAppend
    (left right : Word Nat) (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution =
      left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bindBind
    (word : Word Nat)
    (first second : Nat → Word Nat) :
    (word.bind first).bind second =
      word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bindSingleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem prefixedS5_415AxiomDerivesAfterBind
    (guard : Word Nat) (substitution : Nat → Word Nat)
    (identity : Identity Nat)
    (member : identity ∈ SemigroupBasis.CoRoots.S5_415.basis) :
    Derives basis
      (guard ++ identity.lhs.bind substitution)
      (guard ++ identity.rhs.bind substitution) := by
  simp only [SemigroupBasis.CoRoots.S5_415.basis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · have contraction :=
      derivesBasisSubstitution powerContractionLaw
        powerContractionLaw_mem substitution
    have xxShape :
        SemigroupBasis.CoRoots.S5_415.xx =
          (⟨0, [0]⟩ : Word Nat) := by
      decide
    have xxxShape :
        SemigroupBasis.CoRoots.S5_415.xxx =
          (⟨0, [0, 0]⟩ : Word Nat) := by
      decide
    simpa [SemigroupBasis.CoRoots.S5_415.powerLaw,
      powerContractionLaw, xxShape, xxxShape, w] using
        Derives.prepend guard contraction.symm
  · have contraction :=
      derivesBasisSubstitution sandwichContractionLaw
        sandwichContractionLaw_mem substitution
    have xyxShape :
        SemigroupBasis.CoRoots.S5_415.xyx =
          (⟨0, [1, 0]⟩ : Word Nat) := by
      decide
    have xyxyxShape :
        SemigroupBasis.CoRoots.S5_415.xyxyx =
          (⟨0, [1, 0, 1, 0]⟩ : Word Nat) := by
      decide
    simpa [SemigroupBasis.CoRoots.S5_415.sandwichLaw,
      sandwichContractionLaw, xyxShape, xyxyxShape, w] using
        Derives.prepend guard contraction.symm
  · have xxyyShape :
        SemigroupBasis.CoRoots.S5_415.xxyy =
          (⟨0, [0, 1, 1]⟩ : Word Nat) := by
      decide
    have yyxxShape :
        SemigroupBasis.CoRoots.S5_415.yyxx =
          (⟨1, [1, 0, 0]⟩ : Word Nat) := by
      decide
    simpa [SemigroupBasis.CoRoots.S5_415.squareCommutationLaw,
      xxyyShape, yyxxShape, Word.bind, Word.append, Word.singleton,
      Word.append_assoc] using
        derivesGuardedSquareCommutation guard
          (substitution 0) (substitution 1)

/-- Replay an arbitrary `S5_415` derivation after a protected prefix and
after an arbitrary word substitution.  The prefix is what makes square
commutation derivable in H7. -/
theorem liftS5_415UnderPrefix
    {left right : Word Nat}
    (derivation :
      Derives SemigroupBasis.CoRoots.S5_415.basis left right)
    (guard : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis
      (guard ++ left.bind substitution)
      (guard ++ right.bind substitution) := by
  induction derivation generalizing guard substitution with
  | fromBasis member =>
      exact
        prefixedS5_415AxiomDerivesAfterBind
          guard substitution _ member
  | refl =>
      exact Derives.refl _
  | symm _ inductionHypothesis =>
      exact (inductionHypothesis guard substitution).symm
  | trans _ _ firstHypothesis secondHypothesis =>
      exact
        (firstHypothesis guard substitution).trans
          (secondHypothesis guard substitution)
  | prepend front _ inductionHypothesis =>
      simpa [bindAppend, Word.append_assoc] using
        inductionHypothesis
          (guard ++ front.bind substitution) substitution
  | appendRight _ suffix inductionHypothesis =>
      simpa [bindAppend, Word.append_assoc] using
        Derives.appendRight
          (inductionHypothesis guard substitution)
          (suffix.bind substitution)
  | subst _ first inductionHypothesis =>
      simpa [bindBind] using
        inductionHypothesis guard
          (fun letter => (first letter).bind substitution)

/-- Full `S5_415` completeness is available behind any protected H7 prefix.
This is the principal recursion rule for suffix subidentities. -/
theorem derivesGuardedOfSameBrandtSignature
    (guard : Word Nat) {left right : Word Nat}
    (same :
      SemigroupBasis.CoRoots.S5_415.SameBrandtSignature left right) :
    Derives basis (guard ++ left) (guard ++ right) := by
  have brandtDerivation :=
    SemigroupBasis.CoRoots.S5_415.brandtDerivationalCompleteness
      left right same
  simpa [bindSingleton] using
    liftS5_415UnderPrefix
      brandtDerivation guard Word.singleton

/-- The existing recursive Brandt normalizer may be replayed on any suffix
which already has a protected nonempty prefix. -/
theorem derivesGuardedNormalizeBrandtWord
    (guard word : Word Nat) :
    Derives basis
      (guard ++ word)
      (guard ++ SemigroupBasis.CoRoots.S5_415.normalizeBrandtWord word) :=
  derivesGuardedOfSameBrandtSignature guard
    (SemigroupBasis.CoRoots.S5_415.normalizeBrandtWord_sameBrandtSignature
      word)

/-! ## Transport of the completed marked-digraph presentation -/

/-- Each `S5_868` axiom is one of the first three H7 laws, with the first
two used in the expansion direction. -/
theorem s5_868AxiomDerives
    (identity : Identity Nat)
    (member : identity ∈ SemigroupBasis.CoRoots.S5_868.basis) :
    Derives basis identity.lhs identity.rhs := by
  simp only [SemigroupBasis.CoRoots.S5_868.basis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · change
      Derives basis
        SemigroupBasis.CoRoots.S5_868.xx
        SemigroupBasis.CoRoots.S5_868.xxx
    exact
      (Derives.fromBasis
        (e := powerContractionLaw) powerContractionLaw_mem).symm
  · change
      Derives basis
        SemigroupBasis.CoRoots.S5_868.xyx
        SemigroupBasis.CoRoots.S5_868.xyxyx
    exact
      (Derives.fromBasis
        (e := sandwichContractionLaw) sandwichContractionLaw_mem).symm
  · change
      Derives basis
        SemigroupBasis.CoRoots.S5_868.xyxzx
        SemigroupBasis.CoRoots.S5_868.xzxyx
    exact
      Derives.fromBasis
        (e := graphSwitchLaw) graphSwitchLaw_mem

/-- Transport an arbitrary derivation from the completed `S5_868`
presentation into H7. -/
theorem transportS5_868Derivation
    {left right : Word Nat}
    (derivation :
      Derives SemigroupBasis.CoRoots.S5_868.basis left right) :
    Derives basis left right :=
  Derives.transport s5_868AxiomDerives derivation

/-- The shared power expansion, transported through the first H7 law. -/
theorem derivesPowerExpansion (word : Word Nat) :
    Derives basis
      (word ++ word)
      ((word ++ word) ++ word) :=
  transportS5_868Derivation (Marked.derivesPowerExpansion word)

/-- The shared power contraction. -/
theorem derivesPowerContraction (word : Word Nat) :
    Derives basis
      ((word ++ word) ++ word)
      (word ++ word) :=
  (derivesPowerExpansion word).symm

/-- The shared sandwich expansion, transported through the second H7 law. -/
theorem derivesSandwichExpansion (anchor excursion : Word Nat) :
    Derives basis
      ((anchor ++ excursion) ++ anchor)
      ((((anchor ++ excursion) ++ anchor) ++ excursion) ++ anchor) :=
  transportS5_868Derivation
    (Marked.derivesSandwichExpansion anchor excursion)

/-- The shared sandwich contraction. -/
theorem derivesSandwichContraction (anchor excursion : Word Nat) :
    Derives basis
      ((((anchor ++ excursion) ++ anchor) ++ excursion) ++ anchor)
      ((anchor ++ excursion) ++ anchor) :=
  (derivesSandwichExpansion anchor excursion).symm

/-- The shared anchored graph switch, transported through the third H7 law. -/
theorem derivesGraphSwitch
    (anchor first second : Word Nat) :
    Derives basis
      ((((anchor ++ first) ++ anchor) ++ second) ++ anchor)
      ((((anchor ++ second) ++ anchor) ++ first) ++ anchor) :=
  transportS5_868Derivation
    (Marked.derivesAnchoredLoopSwap anchor first second)

/-- Move an empty excursion past a nonempty one using only the first three
H7 laws. -/
theorem derivesEmptyExcursionSwap
    (anchor excursion : Word Nat) :
    Derives basis
      (((anchor ++ anchor) ++ excursion) ++ anchor)
      (((anchor ++ excursion) ++ anchor) ++ anchor) := by
  have expand :=
    Derives.appendRight (derivesPowerExpansion anchor)
      (excursion ++ anchor)
  have switch := derivesGraphSwitch anchor anchor excursion
  have contract :=
    Derives.prepend (anchor ++ excursion)
      (derivesPowerContraction anchor)
  have expandAligned :
      Derives basis
        (((anchor ++ anchor) ++ excursion) ++ anchor)
        ((((anchor ++ anchor) ++ anchor) ++ excursion) ++ anchor) := by
    simpa [Word.append_assoc] using expand
  have contractAligned :
      Derives basis
        ((((anchor ++ excursion) ++ anchor) ++ anchor) ++ anchor)
        (((anchor ++ excursion) ++ anchor) ++ anchor) := by
    simpa [Word.append_assoc] using contract
  exact expandAligned.trans <| switch.trans contractAligned

/-! ## A head-preserving square-bank retarget -/

/-- The head-preserving part of the published `F(A,B)` calculation:
`A B A B² -> A² B²`.  Its three square exchanges all have an explicit
nonempty left guard, so they are valid in H7.  The omitted final
`A² B² -> B² A²` is precisely the head-changing step unavailable here. -/
theorem derivesRetargetFToOrderedSquares (A B : Word Nat) :
    Derives basis
      (((A ++ B) ++ A) ++ (B ++ B))
      ((A ++ A) ++ (B ++ B)) := by
  have step1 :
      Derives basis
        (((A ++ B) ++ A) ++ (B ++ B))
        ((((((A ++ B) ++ A) ++ B) ++ A) ++ B) ++ B) := by
    simpa [Word.append_assoc] using
      Derives.appendRight (derivesSandwichExpansion A B) (B ++ B)
  have step2 :
      Derives basis
        ((((((A ++ B) ++ A) ++ B) ++ A) ++ B) ++ B)
        ((((((A ++ B) ++ A) ++ B) ++ B) ++ A) ++ B) := by
    simpa [Word.append_assoc] using
      Derives.prepend ((A ++ B) ++ A)
        (derivesEmptyExcursionSwap B A).symm
  have step3 :
      Derives basis
        ((((((A ++ B) ++ A) ++ B) ++ B) ++ A) ++ B)
        ((((((A ++ B) ++ B) ++ A) ++ B) ++ A) ++ B) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (Derives.prepend A
          (derivesEmptyExcursionSwap B A).symm)
        (A ++ B)
  have step4 :
      Derives basis
        ((((((A ++ B) ++ B) ++ A) ++ B) ++ A) ++ B)
        ((((((A ++ A) ++ B) ++ A) ++ B) ++ B) ++ B) := by
    simpa [Word.append_assoc] using
      derivesGuardedSquareCommutation A B (A ++ B)
  have step5 :
      Derives basis
        ((((((A ++ A) ++ B) ++ A) ++ B) ++ B) ++ B)
        (((((A ++ A) ++ B) ++ A) ++ B) ++ B) := by
    simpa [Word.append_assoc] using
      Derives.prepend (((A ++ A) ++ B) ++ A)
        (derivesPowerContraction B)
  have step6 :
      Derives basis
        (((((A ++ A) ++ B) ++ A) ++ B) ++ B)
        (((((A ++ B) ++ A) ++ A) ++ B) ++ B) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (derivesEmptyExcursionSwap A B) (B ++ B)
  have step7 :
      Derives basis
        (((((A ++ B) ++ A) ++ A) ++ B) ++ B)
        (((((A ++ B) ++ B) ++ B) ++ A) ++ A) := by
    simpa [Word.append_assoc] using
      derivesGuardedSquareCommutation (A ++ B) A B
  have step8 :
      Derives basis
        (((((A ++ B) ++ B) ++ B) ++ A) ++ A)
        ((((A ++ B) ++ B) ++ A) ++ A) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (Derives.prepend A (derivesPowerContraction B))
        (A ++ A)
  have step9 :
      Derives basis
        ((((A ++ B) ++ B) ++ A) ++ A)
        ((((A ++ A) ++ A) ++ B) ++ B) := by
    simpa [Word.append_assoc] using
      derivesGuardedSquareCommutation A B A
  have step10 :
      Derives basis
        ((((A ++ A) ++ A) ++ B) ++ B)
        (((A ++ A) ++ B) ++ B) := by
    simpa [Word.append_assoc] using
      Derives.appendRight (derivesPowerContraction A) (B ++ B)
  simp only [Word.append_assoc] at step1 step2 step3 step4 step5 step6 step7 step8 step9 step10 ⊢
  exact step1.trans <| step2.trans <| step3.trans <| step4.trans <|
    step5.trans <| step6.trans <| step7.trans <| step8.trans <|
      step9.trans step10

/-- The canonical equal-head obstruction is solvable without ever changing
the literal head:

`A B² A B  ->  A² B A`.

The proof uses `F` only up to the ordered bank `A² B²`, adds one copy of the
head block as a guard, commutes the bank behind that guard, and replays the
reverse ordered calculation under the same guard. -/
theorem derivesEqualHeadRetargetG (A B : Word Nat) :
    Derives basis
      ((((A ++ B) ++ B) ++ A) ++ B)
      (((A ++ A) ++ B) ++ A) := by
  have exposeF :
      Derives basis
        ((((A ++ B) ++ B) ++ A) ++ B)
        (((A ++ B) ++ A) ++ (B ++ B)) := by
    simpa [Word.append_assoc] using
      Derives.prepend A (derivesEmptyExcursionSwap B A)
  have orderBank := derivesRetargetFToOrderedSquares A B
  have addGuard :
      Derives basis
        ((A ++ A) ++ (B ++ B))
        (((A ++ A) ++ A) ++ (B ++ B)) := by
    simpa [Word.append_assoc] using
      Derives.appendRight (derivesPowerExpansion A) (B ++ B)
  have commuteBehindGuard :
      Derives basis
        (((A ++ A) ++ A) ++ (B ++ B))
        ((A ++ (B ++ B)) ++ (A ++ A)) := by
    simpa [Word.append_assoc] using
      derivesGuardedSquareCommutation A A B
  have replayOrderedF :
      Derives basis
        ((A ++ (B ++ B)) ++ (A ++ A))
        (A ++ (((B ++ A) ++ B) ++ (A ++ A))) := by
    simpa [Word.append_assoc] using
      Derives.prepend A
        (derivesRetargetFToOrderedSquares B A).symm
  have expandTail :
      Derives basis
        (A ++ (((B ++ A) ++ B) ++ (A ++ A)))
        (A ++ ((((B ++ A) ++ B) ++ (A ++ A)) ++ A)) := by
    simpa [Word.append_assoc] using
      Derives.prepend (A ++ ((B ++ A) ++ B))
        (derivesPowerExpansion A)
  have commuteReplay :
      Derives basis
        (A ++ ((((B ++ A) ++ B) ++ (A ++ A)) ++ A))
        (A ++ (((((A ++ A) ++ B) ++ A) ++ B) ++ A)) := by
    simpa [Word.append_assoc] using
      derivesGuardedSquareCommutation A (B ++ A) A
  have contractReplay :
      Derives basis
        (A ++ (((((A ++ A) ++ B) ++ A) ++ B) ++ A))
        (A ++ (((A ++ A) ++ B) ++ A)) := by
    simpa [Word.append_assoc] using
      Derives.prepend (A ++ A)
        (derivesSandwichContraction A B)
  have removeGuardCopy :
      Derives basis
        (A ++ (((A ++ A) ++ B) ++ A))
        (((A ++ A) ++ B) ++ A) := by
    simpa [Word.append_assoc] using
      Derives.appendRight (derivesPowerContraction A) (B ++ A)
  exact exposeF.trans <| orderBank.trans <| addGuard.trans <|
    commuteBehindGuard.trans <| replayOrderedF.trans <|
      expandTail.trans <| commuteReplay.trans <|
        contractReplay.trans removeGuardCopy

/-- Move one squared walk across the head of a nonempty square bank while a
permanent H7 root remains to its left. -/
theorem derivesGuardedSwapSquaredWalkWithBankHead
    (guard first second : Word Nat) (rest : List (Word Nat)) :
    Derives basis
      (guard ++
        ((first ++ first) ++ Brandt.squaredWalkBank second rest))
      (guard ++
        Brandt.squaredWalkBank second (first :: rest)) := by
  cases rest with
  | nil =>
      simpa [Brandt.squaredWalkBank, Word.append_assoc] using
        derivesGuardedSquareCommutation guard first second
  | cons next tail =>
      simpa [Brandt.squaredWalkBank, Word.append_assoc] using
        Derives.appendRight
          (derivesGuardedSquareCommutation guard first second)
          (Brandt.squaredWalkBank next tail)

/-- The S5 pivot-path square-bank induction survives in H7 once the entire
bank is kept behind one permanent nonempty root.  Every recursive call merely
extends that root by the already traversed squared blocks. -/
theorem derivesGuardedSquaredWalkBankToPivotTarget
    (guard : Word Nat)
    {ambient : Word Nat} {startVertex endVertex : Nat}
    {path : Brandt.IncomingPivotPath ambient startVertex endVertex}
    {first : Word Nat} {rest : List (Word Nat)}
    (along :
      Brandt.SquaredWalkBankAlongPivotPath ambient path first rest) :
    ∃ targetFirst targetRest,
      targetFirst.head = endVertex ∧
        Derives basis
          (guard ++ Brandt.squaredWalkBank first rest)
          (guard ++ Brandt.squaredWalkBank targetFirst targetRest) := by
  induction along generalizing guard with
  | nil block blockHead =>
      exact ⟨block, [], blockHead, Derives.refl _⟩
  | cons block blockHead tailBank induction =>
      rcases induction (guard := guard ++ (block ++ block)) with
        ⟨targetFirst, targetRest, targetHead, moveTail⟩
      have moveTarget :=
        derivesGuardedSwapSquaredWalkWithBankHead
          guard block targetFirst targetRest
      refine
        ⟨targetFirst, block :: targetRest, targetHead, ?_⟩
      apply Derives.trans
      · simpa [Brandt.squaredWalkBank, Word.append_assoc] using
          moveTail
      · simpa [Word.append_assoc] using moveTarget

/-- Exact equality of marked directed graphs is already sufficient for an
H7 derivation.  The remaining rooted normalizer must turn the weaker Brandt
signature plus head equality into this situation. -/
theorem derivesOfSameMarkedDigraph
    {left right : Word Nat}
    (same : left.SameMarkedDigraph right) :
    Derives basis left right :=
  transportS5_868Derivation
    (SemigroupBasis.CoRoots.S5_868.markedDigraphDerivationalCompleteness
      left right same)

/-! ## Exact rooted completion boundary -/

/-- The semantic invariant detected by the `S5_415` quotient and the
left-zero quotient together. -/
structure SameRootedBrandtSignature
    (left right : Word Nat) : Prop where
  brandt :
    SemigroupBasis.CoRoots.S5_415.SameBrandtSignature left right
  head : left.head = right.head

namespace SameRootedBrandtSignature

theorem refl (word : Word Nat) :
    SameRootedBrandtSignature word word :=
  ⟨SemigroupBasis.CoRoots.S5_415.sameBrandtSignature_refl word, rfl⟩

theorem symm {left right : Word Nat}
    (same : SameRootedBrandtSignature left right) :
    SameRootedBrandtSignature right left :=
  ⟨same.brandt.symm, same.head.symm⟩

/-- Recursive Brandt normalization preserves the full rooted invariant. -/
theorem normalize {left right : Word Nat}
    (same : SameRootedBrandtSignature left right) :
    SameRootedBrandtSignature
      (SemigroupBasis.CoRoots.S5_415.normalizeBrandtWord left)
      (SemigroupBasis.CoRoots.S5_415.normalizeBrandtWord right) := by
  refine
    ⟨SemigroupBasis.CoRoots.S5_415.normalizedWords_sameBrandtSignature
        same.brandt,
      ?_⟩
  simpa using same.head

end SameRootedBrandtSignature

/-- Assemble the rooted invariant directly from the two detector
coordinates used by the order-six intersection. -/
theorem sameRootedBrandtSignature_of_valid
    (identity : Identity Nat)
    (brandtValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_415.table.semigroup)
    (head : identity.lhs.head = identity.rhs.head) :
    SameRootedBrandtSignature identity.lhs identity.rhs :=
  ⟨SemigroupBasis.CoRoots.S5_415.valid_sameBrandtSignature brandtValid,
    head⟩

/-! ## Rooted isolated-split recursion -/

/-- Empty recursive pieces match only empty pieces; nonempty pieces retain
the rooted Brandt invariant needed by H7 recursion. -/
inductive OptionalSameRootedBrandtSignature :
    Option (Word Nat) → Option (Word Nat) → Prop
  | none : OptionalSameRootedBrandtSignature none none
  | some {left right : Word Nat} :
      SameRootedBrandtSignature left right →
        OptionalSameRootedBrandtSignature (some left) (some right)

/-- Optional proof-relevant H7 derivability for the pieces on either side of
an isolated marker. -/
inductive OptionalH7Derives :
    Option (Word Nat) → Option (Word Nat) → Prop
  | none : OptionalH7Derives none none
  | some {left right : Word Nat} :
      Derives basis left right →
        OptionalH7Derives (some left) (some right)

namespace OptionalSameRootedBrandtSignature

theorem derives
    {left right : Option (Word Nat)}
    (same : OptionalSameRootedBrandtSignature left right)
    (complete :
      ∀ {source target : Word Nat},
        SameRootedBrandtSignature source target →
          Derives basis source target) :
    OptionalH7Derives left right := by
  cases same with
  | none =>
      exact OptionalH7Derives.none
  | some rooted =>
      exact OptionalH7Derives.some (complete rooted)

/-- The bounded form used by strong induction on the ambient support. -/
theorem derivesOfSmaller
    {left right : Option (Word Nat)} {larger : Word Nat}
    (same : OptionalSameRootedBrandtSignature left right)
    (leftSmaller :
      ∀ word, left = Option.some word →
        Brandt.brandtSupportCard word <
          Brandt.brandtSupportCard larger)
    (smallerDerivable :
      ∀ {source target : Word Nat},
        SameRootedBrandtSignature source target →
          Brandt.brandtSupportCard source <
              Brandt.brandtSupportCard larger →
            Derives basis source target) :
    OptionalH7Derives left right := by
  cases same with
  | none =>
      exact OptionalH7Derives.none
  | some rooted =>
      exact OptionalH7Derives.some <|
        smallerDerivable rooted (leftSmaller _ rfl)

end OptionalSameRootedBrandtSignature

/-- Rebuild a word around one mandatory isolated marker while keeping both
surrounding pieces genuinely optional. -/
def isolatedRebuild
    (marker : Nat) (leadingWord suffix : Option (Word Nat)) : Word Nat :=
  match leadingWord, suffix with
  | none, none => Word.singleton marker
  | none, some suffixWord => Word.singleton marker ++ suffixWord
  | some prefixWord, none => prefixWord ++ Word.singleton marker
  | some prefixWord, some suffixWord =>
      (prefixWord ++ Word.singleton marker) ++ suffixWord

@[simp]
theorem isolatedRebuild_toList
    (marker : Nat) (leadingWord suffix : Option (Word Nat)) :
    (isolatedRebuild marker leadingWord suffix).toList =
      Brandt.optionalWordLetters leadingWord ++ [marker] ++
        Brandt.optionalWordLetters suffix := by
  cases leadingWord <;> cases suffix <;>
    simp [isolatedRebuild, Brandt.optionalWordLetters,
      Word.toList, Word.toList_append, List.append_assoc]

/-- Recursive H7 derivability of the prefix and semantic Brandt equality of
the suffix suffice to rebuild across an isolated marker.  The marker, or the
already transformed prefix followed by the marker, protects every suffix
use of square commutation. -/
theorem derivesIsolatedRebuild
    (marker : Nat)
    {leftPrefix rightPrefix leftSuffix rightSuffix :
      Option (Word Nat)}
    (prefixDerivation :
      OptionalH7Derives leftPrefix rightPrefix)
    (suffixSame :
      Brandt.OptionalSameBrandtSignature leftSuffix rightSuffix) :
    Derives basis
      (isolatedRebuild marker leftPrefix leftSuffix)
      (isolatedRebuild marker rightPrefix rightSuffix) := by
  cases leftPrefix with
  | none =>
      cases rightPrefix with
      | none =>
          cases prefixDerivation
          cases leftSuffix with
          | none =>
              cases rightSuffix with
              | none =>
                  cases suffixSame
                  exact Derives.refl _
              | some rightSuffixWord =>
                  cases suffixSame
          | some leftSuffixWord =>
              cases rightSuffix with
              | none =>
                  cases suffixSame
              | some rightSuffixWord =>
                  cases suffixSame with
                  | some same =>
                      simpa [isolatedRebuild] using
                        derivesGuardedOfSameBrandtSignature
                          (Word.singleton marker) same
      | some rightPrefixWord =>
          cases prefixDerivation
  | some leftPrefixWord =>
      cases rightPrefix with
      | none =>
          cases prefixDerivation
      | some rightPrefixWord =>
          cases prefixDerivation with
          | some prefixWordDerivation =>
              cases leftSuffix with
              | none =>
                  cases rightSuffix with
                  | none =>
                      cases suffixSame
                      simpa [isolatedRebuild] using
                        Derives.appendRight prefixWordDerivation
                          (Word.singleton marker)
                  | some rightSuffixWord =>
                      cases suffixSame
              | some leftSuffixWord =>
                  cases rightSuffix with
                  | none =>
                      cases suffixSame
                  | some rightSuffixWord =>
                      cases suffixSame with
                      | some same =>
                          have prefixInContext :=
                            Derives.appendRight
                              (Derives.appendRight prefixWordDerivation
                                (Word.singleton marker))
                              leftSuffixWord
                          have suffixInContext :=
                            derivesGuardedOfSameBrandtSignature
                              (rightPrefixWord ++ Word.singleton marker)
                              same
                          simpa [isolatedRebuild, Word.append_assoc] using
                            prefixInContext.trans suffixInContext

private theorem optionalPrefixRootedSignature
    {left right : Word Nat}
    {leftPrefix rightPrefix leftRest rightRest : List Nat}
    (same :
      Brandt.OptionalSameBrandtSignature
        (Brandt.optionalWordOfList leftPrefix)
        (Brandt.optionalWordOfList rightPrefix))
    (leftFactorization : left.toList = leftPrefix ++ leftRest)
    (rightFactorization : right.toList = rightPrefix ++ rightRest)
    (head : left.head = right.head) :
    OptionalSameRootedBrandtSignature
      (Brandt.optionalWordOfList leftPrefix)
      (Brandt.optionalWordOfList rightPrefix) := by
  cases leftPrefix with
  | nil =>
      cases rightPrefix with
      | nil =>
          exact OptionalSameRootedBrandtSignature.none
      | cons rightHead rightTail =>
          cases same
  | cons leftHead leftTail =>
      cases rightPrefix with
      | nil =>
          cases same
      | cons rightHead rightTail =>
          cases same with
          | some brandt =>
              apply OptionalSameRootedBrandtSignature.some
              refine ⟨brandt, ?_⟩
              have leftHeadEq : left.head = leftHead := by
                have first := congrArg List.head? leftFactorization
                exact Option.some.inj <|
                  by simpa [Word.toList] using first
              have rightHeadEq : right.head = rightHead := by
                have first := congrArg List.head? rightFactorization
                exact Option.some.inj <|
                  by simpa [Word.toList] using first
              exact leftHeadEq.symm.trans (head.trans rightHeadEq)

/-- The prefix signature returned by the public semantic split theorem is
rooted whenever the ambient identity has equal literal heads. -/
theorem correspondingIsolatedSplit_prefixRootedSignature
    {left right : Word Nat}
    {leftPrefix leftSuffix : List Nat} {marker : Nat}
    (split :
      Brandt.CorrespondingIsolatedSplit
        leftPrefix marker leftSuffix right)
    (same : SameRootedBrandtSignature left right)
    (leftFactorization :
      left.toList = leftPrefix ++ [marker] ++ leftSuffix)
    (markerNotPrefix : marker ∉ leftPrefix)
    (markerNotSuffix : marker ∉ leftSuffix)
    (supportsDisjoint :
      ∀ letter, letter ∈ leftPrefix → letter ∉ leftSuffix) :
    OptionalSameRootedBrandtSignature
      (Brandt.optionalWordOfList leftPrefix)
      (Brandt.optionalWordOfList split.rightPrefix) := by
  apply optionalPrefixRootedSignature
    (split.prefixRecursiveSignature same.brandt leftFactorization
      markerNotPrefix markerNotSuffix supportsDisjoint)
  · simpa [List.append_assoc] using leftFactorization
  · simpa [List.append_assoc] using split.factorization
  · exact same.head

/-- Exact H7 recomposition boundary for an isolated semantic split.  The
suffix subidentity is discharged unconditionally behind the isolated marker;
only the rooted prefix derivation remains recursive. -/
theorem derivesOfCorrespondingIsolatedSplit
    {left right : Word Nat}
    {leftPrefix leftSuffix : List Nat} {marker : Nat}
    (split :
      Brandt.CorrespondingIsolatedSplit
        leftPrefix marker leftSuffix right)
    (same : SameRootedBrandtSignature left right)
    (leftFactorization :
      left.toList = leftPrefix ++ [marker] ++ leftSuffix)
    (markerNotPrefix : marker ∉ leftPrefix)
    (markerNotSuffix : marker ∉ leftSuffix)
    (supportsDisjoint :
      ∀ letter, letter ∈ leftPrefix → letter ∉ leftSuffix)
    (prefixDerivation :
      OptionalH7Derives
        (Brandt.optionalWordOfList leftPrefix)
        (Brandt.optionalWordOfList split.rightPrefix)) :
    Derives basis left right := by
  have recursive :=
    split.recursiveSignatures same.brandt leftFactorization
      markerNotPrefix markerNotSuffix supportsDisjoint
  have rebuilt :=
    derivesIsolatedRebuild marker prefixDerivation recursive.2
  have leftShape :
      left =
        isolatedRebuild marker
          (Brandt.optionalWordOfList leftPrefix)
          (Brandt.optionalWordOfList leftSuffix) := by
    apply Word.toList_injective
    rw [leftFactorization, isolatedRebuild_toList]
    simp
  have rightShape :
      right =
        isolatedRebuild marker
          (Brandt.optionalWordOfList split.rightPrefix)
          (Brandt.optionalWordOfList split.rightSuffix) := by
    apply Word.toList_injective
    rw [split.factorization, isolatedRebuild_toList]
    simp
  rw [← leftShape, ← rightShape] at rebuilt
  exact rebuilt

/-- A recursive solver for the single rooted prefix obligation closes the
whole isolated branch. -/
theorem derivesOfCorrespondingIsolatedSplitOfPrefixComplete
    {left right : Word Nat}
    {leftPrefix leftSuffix : List Nat} {marker : Nat}
    (split :
      Brandt.CorrespondingIsolatedSplit
        leftPrefix marker leftSuffix right)
    (same : SameRootedBrandtSignature left right)
    (leftFactorization :
      left.toList = leftPrefix ++ [marker] ++ leftSuffix)
    (markerNotPrefix : marker ∉ leftPrefix)
    (markerNotSuffix : marker ∉ leftSuffix)
    (supportsDisjoint :
      ∀ letter, letter ∈ leftPrefix → letter ∉ leftSuffix)
    (prefixComplete :
      ∀ {source target : Word Nat},
        SameRootedBrandtSignature source target →
          Derives basis source target) :
    Derives basis left right := by
  have prefixSame :=
    correspondingIsolatedSplit_prefixRootedSignature split same
      leftFactorization markerNotPrefix markerNotSuffix supportsDisjoint
  exact
    derivesOfCorrespondingIsolatedSplit split same leftFactorization
      markerNotPrefix markerNotSuffix supportsDisjoint
      (prefixSame.derives prefixComplete)

/-! ## Finite support induction and the repeated-word core -/

/-- Failure of H7 derivability at a support-minimal rooted identity forces
the left word to be repeated.  In the nonrepeated case the isolated marker is
present in the ambient support and absent from the recursive prefix, giving
the strict `brandtSupportCard` decrease used below. -/
theorem rootedRepeatedWord_left_of_minimalSupport
    {left right : Word Nat}
    (same : SameRootedBrandtSignature left right)
    (notDerivable : ¬ Derives basis left right)
    (smallerDerivable :
      ∀ {smallerLeft smallerRight : Word Nat},
        SameRootedBrandtSignature smallerLeft smallerRight →
          Brandt.brandtSupportCard smallerLeft <
              Brandt.brandtSupportCard left →
            Derives basis smallerLeft smallerRight) :
    Brandt.RepeatedWord left := by
  apply Classical.byContradiction
  intro notRepeated
  obtain ⟨marker, leftPrefix, leftSuffix, leftFactorization,
      markerNotPrefix, markerNotSuffix, supportsDisjoint⟩ :=
    Brandt.exists_isolated_split_of_not_repeated notRepeated
  let split :=
    Brandt.correspondingIsolatedSplit_of_sameBrandtSignature
      same.brandt leftFactorization markerNotPrefix markerNotSuffix
        supportsDisjoint
  have prefixSame :=
    correspondingIsolatedSplit_prefixRootedSignature split same
      leftFactorization markerNotPrefix markerNotSuffix supportsDisjoint
  have markerMember : marker ∈ left.toList := by
    rw [leftFactorization]
    simp
  have prefixSmaller :
      ∀ prefixWord,
        Brandt.optionalWordOfList leftPrefix = some prefixWord →
          Brandt.brandtSupportCard prefixWord <
            Brandt.brandtSupportCard left := by
    intro prefixWord shape
    apply
      Brandt.brandtSupportCard_lt_of_optionalWordOfList_of_missing
        (larger := left) (missing := marker) shape
    · intro letter member
      rw [leftFactorization]
      simp [member]
    · exact markerMember
    · exact markerNotPrefix
  have prefixDerivation :=
    prefixSame.derivesOfSmaller prefixSmaller smallerDerivable
  exact notDerivable <|
    derivesOfCorrespondingIsolatedSplit split same leftFactorization
      markerNotPrefix markerNotSuffix supportsDisjoint prefixDerivation

/-- A support-minimal nonderivable rooted H7 identity has repeated words on
both sides.  Signature support equality transports the same finite induction
bound to the reversed pair. -/
theorem rootedMinimalCounterexample_repeated
    {left right : Word Nat}
    (same : SameRootedBrandtSignature left right)
    (notDerivable : ¬ Derives basis left right)
    (smallerDerivable :
      ∀ {smallerLeft smallerRight : Word Nat},
        SameRootedBrandtSignature smallerLeft smallerRight →
          Brandt.brandtSupportCard smallerLeft <
              Brandt.brandtSupportCard left →
            Derives basis smallerLeft smallerRight) :
    Brandt.RepeatedWord left ∧ Brandt.RepeatedWord right := by
  have leftRepeated :=
    rootedRepeatedWord_left_of_minimalSupport same notDerivable
      smallerDerivable
  have supportCardEq :=
    Brandt.brandtSupportCard_eq_of_sameBrandtSignature same.brandt
  have reverseNotDerivable : ¬ Derives basis right left := by
    intro reverseDerivation
    exact notDerivable reverseDerivation.symm
  have rightSmallerDerivable :
      ∀ {smallerLeft smallerRight : Word Nat},
        SameRootedBrandtSignature smallerLeft smallerRight →
          Brandt.brandtSupportCard smallerLeft <
              Brandt.brandtSupportCard right →
            Derives basis smallerLeft smallerRight := by
    intro smallerLeft smallerRight smallerSame smallerBound
    apply smallerDerivable smallerSame
    rw [supportCardEq]
    exact smallerBound
  have rightRepeated :=
    rootedRepeatedWord_left_of_minimalSupport same.symm
      reverseNotDerivable rightSmallerDerivable
  exact ⟨leftRepeated, rightRepeated⟩

/-- The sole residual after the finite isolated-split recursion: prove H7
derivability when both rooted-signature words are repeated.  Unlike the
fixed-head separator/simple family, H7 cannot duplicate the initial letter
naively because doing so may add a new Brandt edge. -/
def RootedRepeatedCompleteness : Prop :=
  ∀ left right : Word Nat,
    SameRootedBrandtSignature left right →
      Brandt.RepeatedWord left →
        Brandt.RepeatedWord right →
          Derives basis left right

/-- Strong induction on the finite number of supported letters reduces full
rooted H7 completeness exactly to `RootedRepeatedCompleteness`. -/
theorem derivesOfSameRootedBrandtSignature_of_repeatedCompleteness
    (repeatedComplete : RootedRepeatedCompleteness)
    {left right : Word Nat}
    (same : SameRootedBrandtSignature left right) :
    Derives basis left right := by
  have completeAtSupport :
      ∀ bound currentLeft currentRight,
        Brandt.brandtSupportCard currentLeft = bound →
          SameRootedBrandtSignature currentLeft currentRight →
            Derives basis currentLeft currentRight := by
    intro bound
    induction bound using Nat.strongRecOn with
    | ind currentBound induction =>
        intro currentLeft currentRight supportEq currentSame
        apply Classical.byContradiction
        intro notDerivable
        have smallerDerivable :
            ∀ {smallerLeft smallerRight : Word Nat},
              SameRootedBrandtSignature smallerLeft smallerRight →
                Brandt.brandtSupportCard smallerLeft <
                    Brandt.brandtSupportCard currentLeft →
                  Derives basis smallerLeft smallerRight := by
          intro smallerLeft smallerRight smallerSame smallerSupport
          have smallerSupport' :
              Brandt.brandtSupportCard smallerLeft < currentBound := by
            simpa [supportEq] using smallerSupport
          exact
            induction (Brandt.brandtSupportCard smallerLeft)
              smallerSupport' smallerLeft smallerRight rfl smallerSame
        obtain ⟨leftRepeated, rightRepeated⟩ :=
          rootedMinimalCounterexample_repeated currentSame notDerivable
            smallerDerivable
        exact notDerivable <|
          repeatedComplete currentLeft currentRight currentSame
            leftRepeated rightRepeated
  exact
    completeAtSupport (Brandt.brandtSupportCard left)
      left right rfl same

/-- A proof-relevant two-sided reduction to the completed marked-digraph
theory.  No canonical choice of normal word is required. -/
structure RootedMarkedAlignment (left right : Word Nat) : Type where
  leftNormal : Word Nat
  rightNormal : Word Nat
  leftDerives : Derives basis left leftNormal
  rightDerives : Derives basis right rightNormal
  sameMarked : leftNormal.SameMarkedDigraph rightNormal

namespace RootedMarkedAlignment

theorem derives {left right : Word Nat}
    (alignment : RootedMarkedAlignment left right) :
    Derives basis left right :=
  alignment.leftDerives.trans <|
    (derivesOfSameMarkedDigraph alignment.sameMarked).trans
      alignment.rightDerives.symm

def ofSameMarkedDigraph {left right : Word Nat}
    (same : left.SameMarkedDigraph right) :
    RootedMarkedAlignment left right where
  leftNormal := left
  rightNormal := right
  leftDerives := Derives.refl left
  rightDerives := Derives.refl right
  sameMarked := same

end RootedMarkedAlignment

/-- The exact remaining constructive normalizer proposition.  Packaging it
separately prevents downstream code from treating the missing construction
as an axiom or as an already established theorem. -/
def RootedMarkedAlignmentCompleteness : Prop :=
  ∀ left right : Word Nat,
    SameRootedBrandtSignature left right →
      Nonempty (RootedMarkedAlignment left right)

/-- A rooted marked alignment is sufficient for the desired H7
completeness theorem. -/
theorem derivesOfSameRootedBrandtSignature_of_alignmentCompleteness
    (complete : RootedMarkedAlignmentCompleteness)
    {left right : Word Nat}
    (same : SameRootedBrandtSignature left right) :
    Derives basis left right :=
  (complete left right same).elim fun alignment => alignment.derives

/-!
The exact remaining obligation is intentionally not declared as an axiom:

```lean
theorem derivesOfSameRootedBrandtSignature
    {left right : Word Nat}
    (same : SameRootedBrandtSignature left right) :
    Derives basis left right
```

Equivalently, a rooted normalizer may first derive both words to words with
the same marked digraph and then invoke `derivesOfSameMarkedDigraph`.

After the finite isolated-split reduction above, there are two exact ways to
close this boundary:

* construct `RootedRepeatedCompleteness`, using a permanent root in every
  square-bank exposure/replay (the local `G` retarget and path-wide guarded
  bank moves are proved above); or
* bridge the Schutzenberger orientation gap.  H7's left guard supplies the
  commutation step in right-separation for the original term semigroup, while
  it supplies unguarded square commutation automatically in right quotients
  of the opposite term semigroup.  A proof relating those quotient
  orientations, or a direct right-quotient validity proof for the original
  term semigroup, would close the repeated branch.
-/

end SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesH7
