import SemigroupBasis.CoRoots.Order6Day7.S2_2.SeedS5_415RegularLoopModel

/-!
# Rank040: zero-parity closed words equal their actual idempotent anchor

Actual prefix transporters identify every supported endpoint corner with
the head corner. Chosen transporters depend on the corner VALUE, so graph
connections use the same transporter. Letter coordinates are actual
local-group elements, and telescope along each supported graph path.

The existing unrestricted cyclic-two completeness theorem handles their
zero occurrence parity. No new finite-model inference, common-inverse
assumption, or ambient-loop equality is used.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.ParityCoordinates

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_415 (BrandtEndpoint BrandtEndpointConnected)
open ExposureReplay CutConnectivity RegularizedExposure ExposureCorners RegularLoopModel
open HeadRetargetBoundary NormalizedInverse DiagonalComparison BrandtParityBridge

def LocalCarrier (anchor : Carrier) := {element : Carrier // Nonempty (Arrow G anchor anchor element)}

def localSemigroup (anchor : Carrier) : Semigroup (LocalCarrier anchor) where
  mul := fun first second => ⟨G.mul first.val second.val, by
    obtain ⟨left⟩ := first.property
    obtain ⟨right⟩ := second.property
    exact ⟨left.comp right⟩⟩
  assoc := by
    intro first second third
    apply Subtype.ext
    exact G.assoc first.val second.val third.val

def localOne (anchor : Carrier) (idempotent : G.IsIdempotent anchor) : LocalCarrier anchor :=
  ⟨anchor, ⟨Arrow.identity idempotent⟩⟩

def localProjection (anchor : Carrier) : Hom (localSemigroup anchor) G where
  toFun := Subtype.val
  map_mul := fun _ _ => rfl

theorem localCommutes (anchor : Carrier) (first second : LocalCarrier anchor) :
    (localSemigroup anchor).mul first second = (localSemigroup anchor).mul second first := by
  apply Subtype.ext
  obtain ⟨left⟩ := first.property
  obtain ⟨right⟩ := second.property
  exact cycleArrowsCommute left right

theorem localSquare (anchor : Carrier) (idempotent : G.IsIdempotent anchor) (element : LocalCarrier anchor) :
    (localSemigroup anchor).mul element element = localOne anchor idempotent := by
  apply Subtype.ext
  obtain ⟨arrow⟩ := element.property
  exact cycleSquare arrow

theorem localOne_mul (anchor : Carrier) (idempotent : G.IsIdempotent anchor) (element : LocalCarrier anchor) :
    (localSemigroup anchor).mul (localOne anchor idempotent) element = element := by
  apply Subtype.ext
  obtain ⟨arrow⟩ := element.property
  exact arrow.leftUnit

theorem localMul_one (anchor : Carrier) (idempotent : G.IsIdempotent anchor) (element : LocalCarrier anchor) :
    (localSemigroup anchor).mul element (localOne anchor idempotent) = element := by
  apply Subtype.ext
  obtain ⟨arrow⟩ := element.property
  exact arrow.rightUnit

/-- The C2 source basis is proved in the actual local group, then its
already-proved unrestricted completeness theorem may be reused. -/
theorem localModelsCyclicTwo (anchor : Carrier) (idempotent : G.IsIdempotent anchor) :
    Models (localSemigroup anchor) cyclicTwoBasis := by
  intro identity member
  simp only [cyclicTwoBasis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · intro valuation
    change (localSemigroup anchor).mul (valuation 0) (valuation 1) =
      (localSemigroup anchor).mul (valuation 1) (valuation 0)
    exact localCommutes anchor _ _
  · intro valuation
    change (localSemigroup anchor).mul
      ((localSemigroup anchor).mul (valuation 0) (valuation 0)) (valuation 1) = valuation 1
    rw [localSquare anchor idempotent, localOne_mul anchor idempotent]

theorem cyclicEvenDerivesSquare (word : Word Nat) (even : ZeroParity word) :
    Derives cyclicTwoBasis word (Word.singleton word.head ++ Word.singleton word.head) := by
  let square := Word.singleton word.head ++ Word.singleton word.head
  have parity : SameOccurrenceParity word square :=
    fun letter => (even letter).trans (zeroParitySquare (Word.singleton word.head) letter).symm
  have valid := leftValid_of_sameOccurrenceParity (Identity.mk word square) parity
  change (Identity.mk word square).SatisfiedBy
    SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup at valid
  rw [SemigroupBasis.CoRoots.S5_441Invariant.catalogueS2_2_table_eq_cyclicTwo] at valid
  exact cyclicTwoBasis_complete.2 (Identity.mk word square) valid

theorem localEval_zeroParity (anchor : Carrier) (idempotent : G.IsIdempotent anchor)
    (valuation : Nat → LocalCarrier anchor) (word : Word Nat) (even : ZeroParity word) :
    (localSemigroup anchor).eval valuation word = localOne anchor idempotent := by
  have derived := (cyclicEvenDerivesSquare word even).sound
    (localModelsCyclicTwo anchor idempotent) valuation
  simp only [Semigroup.eval_append, Semigroup.eval_singleton] at derived
  exact derived.trans (localSquare anchor idempotent (valuation word.head))

def headAnchor {word : Word Nat} (witness : InverseWitness word) : Carrier :=
  value (word ++ witness.inverse)

theorem headAnchor_idempotent {word : Word Nat} (witness : InverseWitness word) :
    G.IsIdempotent (headAnchor witness) := witness.termInverse.mul_idempotent

/-- Explicit data avoids casting either the chosen element or its inverse
when the reachable corner happens to be the head anchor. -/
structure Transporter {word : Word Nat} (witness : InverseWitness word) (target : Carrier) where
  element : Carrier
  reverse : Carrier
  inverse_laws : G.IsInverse element reverse
  range_eq : G.mul element reverse = headAnchor witness
  source_eq : G.mul reverse element = target

def Transporter.asArrow {word : Word Nat} {witness : InverseWitness word} {target : Carrier}
    (transport : Transporter witness target) : Arrow G (headAnchor witness) target transport.element :=
  ⟨transport.reverse, transport.inverse_laws, transport.range_eq, transport.source_eq⟩

def prefixTransporter {word : Word Nat} (witness : InverseWitness word) (cut : Exposure word) :
    Transporter witness (value (cornerWord witness cut)) where
  element := value (leftFlank witness cut)
  reverse := value (leftFlankInverse witness cut)
  inverse_laws := (leftFlankWitness witness cut).termInverse
  range_eq := value_of_derives (leftFlankRangeDerives witness cut)
  source_eq := value_of_derives (leftFlankSourceDerives witness cut)

def ReachableCorner {word : Word Nat} (witness : InverseWitness word) :=
  {target : Carrier // Nonempty (Transporter witness target)}

noncomputable def endpointTarget {word : Word Nat} (witness : InverseWitness word)
    (endpoint : BrandtEndpoint) : ReachableCorner witness := by
  classical
  refine ⟨endpointCorner witness endpoint, ?_⟩
  by_cases member : endpoint.letter ∈ word.toList
  · let occurrence := chosenOccurrence word endpoint.letter member
    rw [endpointCorner_atOccurrence witness endpoint occurrence]
    exact ⟨prefixTransporter witness (occurrence.cut endpoint.side)⟩
  · simp only [endpointCorner, dif_neg member]
    exact ⟨⟨headAnchor witness, headAnchor witness,
      (Arrow.identity (headAnchor_idempotent witness)).inverse_laws,
      headAnchor_idempotent witness, headAnchor_idempotent witness⟩⟩

noncomputable def selectedTransporter {word : Word Nat} (witness : InverseWitness word)
    (target : ReachableCorner witness) : Transporter witness target.val := by
  classical
  exact if same : target.val = headAnchor witness then
    ⟨headAnchor witness, headAnchor witness,
      (Arrow.identity (headAnchor_idempotent witness)).inverse_laws,
      headAnchor_idempotent witness, (headAnchor_idempotent witness).trans same.symm⟩
  else Classical.choice target.property

noncomputable def transportValue {word : Word Nat} (witness : InverseWitness word)
    (endpoint : BrandtEndpoint) : Carrier :=
  (selectedTransporter witness (endpointTarget witness endpoint)).element

noncomputable def transportInverse {word : Word Nat} (witness : InverseWitness word)
    (endpoint : BrandtEndpoint) : Carrier :=
  (selectedTransporter witness (endpointTarget witness endpoint)).reverse

noncomputable def transportArrow {word : Word Nat} (witness : InverseWitness word)
    (endpoint : BrandtEndpoint) :
    Arrow G (headAnchor witness) (endpointCorner witness endpoint) (transportValue witness endpoint) :=
  (selectedTransporter witness (endpointTarget witness endpoint)).asArrow

theorem transportValue_connected {word : Word Nat} (witness : InverseWitness word)
    {source target : BrandtEndpoint} (connected : BrandtEndpointConnected word source target) :
    transportValue witness source = transportValue witness target := by
  have targets : endpointTarget witness source = endpointTarget witness target :=
    Subtype.ext (endpointCorner_connected witness connected)
  exact congrArg (fun target => (selectedTransporter witness target).element) targets

theorem transportInverse_connected {word : Word Nat} (witness : InverseWitness word)
    {source target : BrandtEndpoint} (connected : BrandtEndpointConnected word source target) :
    transportInverse witness source = transportInverse witness target := by
  have targets : endpointTarget witness source = endpointTarget witness target :=
    Subtype.ext (endpointCorner_connected witness connected)
  exact congrArg (fun target => (selectedTransporter witness target).reverse) targets

theorem transportHeadValue {word : Word Nat} (witness : InverseWitness word) :
    transportValue witness (BrandtEndpoint.incoming word.head) = headAnchor witness := by
  classical
  have same : (endpointTarget witness (BrandtEndpoint.incoming word.head)).val = headAnchor witness :=
    endpointHeadCorner witness
  simp only [transportValue, selectedTransporter, dif_pos same]

theorem transportHeadInverse {word : Word Nat} (witness : InverseWitness word) :
    transportInverse witness (BrandtEndpoint.incoming word.head) = headAnchor witness := by
  classical
  have same : (endpointTarget witness (BrandtEndpoint.incoming word.head)).val = headAnchor witness :=
    endpointHeadCorner witness
  simp only [transportInverse, selectedTransporter, dif_pos same]

noncomputable def basedLetterArrow {word : Word Nat} (witness : InverseWitness word)
    (letter : Nat) (member : letter ∈ word.toList) :
    Arrow G (headAnchor witness) (endpointCorner witness (BrandtEndpoint.outgoing letter))
      (G.mul (transportValue witness (BrandtEndpoint.incoming letter)) (value (Word.singleton letter))) := by
  have based := (transportArrow witness (BrandtEndpoint.incoming letter)).comp (letterArrow witness letter member)
  have reduced : G.mul (transportValue witness (BrandtEndpoint.incoming letter))
      (G.mul (endpointCorner witness (BrandtEndpoint.incoming letter)) (value (Word.singleton letter))) =
      G.mul (transportValue witness (BrandtEndpoint.incoming letter)) (value (Word.singleton letter)) := by
    rw [← G.assoc, (transportArrow witness (BrandtEndpoint.incoming letter)).rightUnit]
  simpa only [reduced] using based

noncomputable def coordinate {word : Word Nat} (witness : InverseWitness word) (letter : Nat) :
    LocalCarrier (headAnchor witness) := by
  classical
  exact if member : letter ∈ word.toList then
    ⟨G.mul (G.mul (transportValue witness (BrandtEndpoint.incoming letter)) (value (Word.singleton letter)))
      (transportInverse witness (BrandtEndpoint.outgoing letter)),
      ⟨(basedLetterArrow witness letter member).comp
        (transportArrow witness (BrandtEndpoint.outgoing letter)).reverse⟩⟩
  else localOne (headAnchor witness) (headAnchor_idempotent witness)

theorem coordinateValue {word : Word Nat} (witness : InverseWitness word)
    (letter : Nat) (member : letter ∈ word.toList) :
    (coordinate witness letter).val =
      G.mul (G.mul (transportValue witness (BrandtEndpoint.incoming letter)) (value (Word.singleton letter)))
        (transportInverse witness (BrandtEndpoint.outgoing letter)) := by
  classical
  simp only [coordinate, dif_pos member]

noncomputable def coordinateEval {word : Word Nat} (witness : InverseWitness word) (path : Word Nat) : Carrier :=
  G.eval (fun letter => (coordinate witness letter).val) path

theorem coordinateEval_zeroParity {word : Word Nat} (witness : InverseWitness word)
    (path : Word Nat) (even : ZeroParity path) : coordinateEval witness path = headAnchor witness := by
  have evaluated := localEval_zeroParity (headAnchor witness) (headAnchor_idempotent witness)
    (coordinate witness) path even
  have mapped := congrArg Subtype.val evaluated
  have projection := (localProjection (headAnchor witness)).map_eval (coordinate witness) path
  exact projection.symm.trans mapped

/-- The coordinates telescope along a supported directed graph path;
only actual equality of corner values identifies its transporters. -/
theorem coordinateWordFormula {word : Word Nat} (witness : InverseWitness word) (path : Word Nat)
    (support : ∀ letter, letter ∈ path.toList → letter ∈ word.toList)
    (internal : ∀ first second, (first, second) ∈ path.adjacentPairs →
      BrandtEndpointConnected word (BrandtEndpoint.outgoing first) (BrandtEndpoint.incoming second)) :
    coordinateEval witness path =
      G.mul (G.mul (transportValue witness (BrandtEndpoint.incoming path.head)) (value path))
        (transportInverse witness (BrandtEndpoint.outgoing path.final)) := by
  cases path with
  | mk head tail =>
    induction tail generalizing head with
    | nil =>
      exact coordinateValue witness head (support head (by simp [Word.toList]))
    | cons next rest ih =>
      let suffix := Word.mk next rest
      have member := support head (by simp [Word.toList])
      have suffixSupport : ∀ letter, letter ∈ suffix.toList → letter ∈ word.toList :=
        fun letter member => support letter (List.mem_cons_of_mem head member)
      have suffixInternal : ∀ first second, (first, second) ∈ suffix.adjacentPairs →
          BrandtEndpointConnected word (BrandtEndpoint.outgoing first) (BrandtEndpoint.incoming second) :=
        fun first second edge => internal first second (List.mem_cons_of_mem (head, next) edge)
      have connected := internal head next (by simp [Word.adjacentPairs, Word.adjacentPairsFrom])
      have bases := transportValue_connected witness connected
      have cancel : G.mul (transportInverse witness (BrandtEndpoint.outgoing head))
          (transportValue witness (BrandtEndpoint.incoming next)) =
          endpointCorner witness (BrandtEndpoint.outgoing head) := by
        rw [← bases]
        exact (transportArrow witness (BrandtEndpoint.outgoing head)).source_eq
      have split : coordinateEval witness (Word.mk head (next :: rest)) =
          G.mul (coordinate witness head).val (coordinateEval witness suffix) := by
        simpa only [coordinateEval, Semigroup.eval_singleton] using
          G.eval_append (fun letter => (coordinate witness letter).val) (Word.singleton head) suffix
      have tailFormula := ih next suffixSupport suffixInternal
      rw [split, coordinateValue witness head member, tailFormula]
      have telescoped :
          G.mul
            (G.mul (G.mul (transportValue witness (BrandtEndpoint.incoming head)) (value (Word.singleton head)))
              (transportInverse witness (BrandtEndpoint.outgoing head)))
            (G.mul (G.mul (transportValue witness (BrandtEndpoint.incoming next)) (value suffix))
              (transportInverse witness (BrandtEndpoint.outgoing suffix.final))) =
          G.mul (G.mul (transportValue witness (BrandtEndpoint.incoming head))
            (value (Word.mk head (next :: rest))))
              (transportInverse witness (BrandtEndpoint.outgoing suffix.final)) := by
        calc
          _ = G.mul
              (G.mul
                (G.mul (G.mul (transportValue witness (BrandtEndpoint.incoming head)) (value (Word.singleton head)))
                  (G.mul (transportInverse witness (BrandtEndpoint.outgoing head))
                    (transportValue witness (BrandtEndpoint.incoming next)))) (value suffix))
              (transportInverse witness (BrandtEndpoint.outgoing suffix.final)) := by simp only [G.assoc]
          _ = G.mul
              (G.mul
                (G.mul (G.mul (transportValue witness (BrandtEndpoint.incoming head)) (value (Word.singleton head)))
                  (endpointCorner witness (BrandtEndpoint.outgoing head))) (value suffix))
              (transportInverse witness (BrandtEndpoint.outgoing suffix.final)) := by rw [cancel]
          _ = G.mul
              (G.mul (G.mul (transportValue witness (BrandtEndpoint.incoming head)) (value (Word.singleton head)))
                (value suffix))
              (transportInverse witness (BrandtEndpoint.outgoing suffix.final)) := by
                rw [(basedLetterArrow witness head member).rightUnit]
          _ = G.mul (G.mul (transportValue witness (BrandtEndpoint.incoming head))
              (G.mul (value (Word.singleton head)) (value suffix)))
              (transportInverse witness (BrandtEndpoint.outgoing suffix.final)) := by simp only [G.assoc]
          _ = _ := rfl
      simpa only [suffix, Word.final, List.getLastD_cons] using telescoped

/-- The remaining parity step is now discharged for every genuinely
regular word that is closed in its OWN graph. -/
theorem zeroParityClosedWord_anchor {word : Word Nat} (witness : InverseWitness word)
    (closed : ClosedReturnWord word word) (even : ZeroParity word) :
    value word = headAnchor witness := by
  have final := endpointCorner_connected witness closed.returns
  obtain ⟨pathArrow⟩ := wordPathArrow witness word closed.support closed.internal
  have leftUnit : G.mul (headAnchor witness) (value word) = value word := witness.termInverse.1
  have rangeUnit : G.mul (value (word ++ witness.inverse)) (value word) = value word := leftUnit
  have cycle : Arrow G (headAnchor witness) (headAnchor witness) (value word) := by
    simpa only [final, endpointHeadCorner, rangeUnit] using pathArrow
  have endTransport := transportInverse_connected witness closed.returns
  have reconstruction := coordinateWordFormula witness word closed.support closed.internal
  rw [transportHeadValue, endTransport, transportHeadInverse, leftUnit, cycle.rightUnit] at reconstruction
  exact reconstruction.symm.trans (coordinateEval_zeroParity witness word even)

theorem zeroParityClosedWord_idempotent {word : Word Nat} (witness : InverseWitness word)
    (closed : ClosedReturnWord word word) (even : ZeroParity word) : G.IsIdempotent (value word) := by
  rw [zeroParityClosedWord_anchor witness closed even]
  exact headAnchor_idempotent witness

theorem zeroParityClosedWord_idempotentDerives {word : Word Nat} (witness : InverseWitness word)
    (closed : ClosedReturnWord word word) (even : ZeroParity word) :
    Derives Rank040.basis (word ++ word) word :=
  (termClass_eq_iff_derives Rank040.basis).mp (zeroParityClosedWord_idempotent witness closed even)

end SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.ParityCoordinates
