import SemigroupBasis.CoRoots.S5_868Semantics

namespace SemigroupBasis.CoRoots.S5_868

open SemigroupBasis

/-! ## Published graph-normalization vocabulary -/

/-- A nonempty path word uses only vertices and directed edges of the
ambient word's adjacency graph. -/
def DirectedPathIn (ambient path : Word Nat) : Prop :=
  (∀ letter, letter ∈ path.toList → letter ∈ ambient.toList) ∧
    ∀ source target,
      (source, target) ∈ path.adjacentPairs →
        (source, target) ∈ ambient.adjacentPairs

/-- Directed reachability in the adjacency graph, represented by a nonempty
path word so no empty-word encoding is required. -/
def ReachableIn (ambient : Word Nat) (source target : Nat) : Prop :=
  ∃ path : Word Nat,
    path.head = source ∧
      path.final = target ∧
      DirectedPathIn ambient path

/-- Trahtman's indecomposability condition: every ordered pair of supported
vertices is connected by a directed path. Quantifying over ordered pairs
also supplies the reverse path, hence an oriented cycle through each pair. -/
def TrahtmanIndecomposable (word : Word Nat) : Prop :=
  ∀ source, source ∈ word.toList →
    ∀ target, target ∈ word.toList →
      ReachableIn word source target

/-- A nonempty word occurs contiguously inside another word. -/
def OccursAsFactor (factor ambient : Word Nat) : Prop :=
  ∃ stem suffix : List Nat,
    ambient.toList = stem ++ factor.toList ++ suffix

/-- A complete word contains every simple directed path in its adjacency
graph as a contiguous factor. This is the paper's completion predicate. -/
def TrahtmanComplete (word : Word Nat) : Prop :=
  ∀ path : Word Nat,
    path.toList.Nodup →
      DirectedPathIn word path →
        OccursAsFactor path word

theorem sameMarkedDigraph_symm
    {left right : Word Nat}
    (same : left.SameMarkedDigraph right) :
    right.SameMarkedDigraph left :=
  ⟨same.1.symm, same.2.1.symm,
    fun letter => (same.2.2.1 letter).symm,
    fun source target => (same.2.2.2 source target).symm⟩

theorem sameMarkedDigraph_trans
    {left middle right : Word Nat}
    (leftMiddle : left.SameMarkedDigraph middle)
    (middleRight : middle.SameMarkedDigraph right) :
    left.SameMarkedDigraph right :=
  ⟨leftMiddle.1.trans middleRight.1,
    leftMiddle.2.1.trans middleRight.2.1,
    fun letter =>
      (leftMiddle.2.2.1 letter).trans (middleRight.2.2.1 letter),
    fun source target =>
      (leftMiddle.2.2.2 source target).trans
        (middleRight.2.2.2 source target)⟩

/-- Directed paths depend only on the marked graph's support and edge set. -/
theorem directedPathIn_iff_of_sameMarkedDigraph
    {left right path : Word Nat}
    (same : left.SameMarkedDigraph right) :
    DirectedPathIn left path ↔ DirectedPathIn right path := by
  constructor
  · rintro ⟨vertices, edges⟩
    refine ⟨?_, ?_⟩
    · intro letter member
      exact (same.support letter).mp (vertices letter member)
    · intro source target member
      exact (same.edge source target).mp (edges source target member)
  · rintro ⟨vertices, edges⟩
    refine ⟨?_, ?_⟩
    · intro letter member
      exact (same.support letter).mpr (vertices letter member)
    · intro source target member
      exact (same.edge source target).mpr (edges source target member)

/-- Reachability is invariant under equality of marked directed graphs. -/
theorem reachableIn_iff_of_sameMarkedDigraph
    {left right : Word Nat} {source target : Nat}
    (same : left.SameMarkedDigraph right) :
    ReachableIn left source target ↔ ReachableIn right source target := by
  constructor
  · rintro ⟨path, initial, final, pathIn⟩
    exact
      ⟨path, initial, final,
        (directedPathIn_iff_of_sameMarkedDigraph same).mp pathIn⟩
  · rintro ⟨path, initial, final, pathIn⟩
    exact
      ⟨path, initial, final,
        (directedPathIn_iff_of_sameMarkedDigraph same).mpr pathIn⟩

/-- Indecomposability is a marked-graph invariant. -/
theorem trahtmanIndecomposable_iff_of_sameMarkedDigraph
    {left right : Word Nat}
    (same : left.SameMarkedDigraph right) :
    TrahtmanIndecomposable left ↔ TrahtmanIndecomposable right := by
  constructor
  · intro indecomposable source sourceMember target targetMember
    have leftSource := (same.support source).mpr sourceMember
    have leftTarget := (same.support target).mpr targetMember
    exact
      (reachableIn_iff_of_sameMarkedDigraph same).mp
        (indecomposable source leftSource target leftTarget)
  · intro indecomposable source sourceMember target targetMember
    have rightSource := (same.support source).mp sourceMember
    have rightTarget := (same.support target).mp targetMember
    exact
      (reachableIn_iff_of_sameMarkedDigraph same).mpr
        (indecomposable source rightSource target rightTarget)

/-- The one remaining global word-problem theorem in Trahtman's published
argument: words with the same augmented adjacency graph must be connected by
the three displayed equational rewrites.

This is a proposition, not an axiom or an assumed theorem. Keeping the
obligation explicit prevents finite table checking from being mistaken for
an unbounded equational completeness proof.
-/
def MarkedDigraphDerivationalCompleteness : Prop :=
  ∀ left right : Word Nat,
    left.SameMarkedDigraph right →
      Derives basis left right

/-! ## Exact dependency boundary of the published proof -/

/-- Every indecomposable marked-graph class has a complete representative.
This is the finite graph-completion construction asserted in the paper. -/
def CompleteRepresentativeExistence : Prop :=
  ∀ word : Word Nat,
    TrahtmanIndecomposable word →
      ∃ complete : Word Nat,
        word.SameMarkedDigraph complete ∧
          TrahtmanComplete complete

/-- Prefix-alignment step of the paper: a complete representative can be
made the prefix of a word derivable from any indecomposable member of its
marked-graph class. -/
def CompletePrefixReachability : Prop :=
  ∀ source complete : Word Nat,
    TrahtmanIndecomposable source →
      source.SameMarkedDigraph complete →
        TrahtmanComplete complete →
          ∃ expanded : Word Nat, ∃ suffix : List Nat,
            Derives basis source expanded ∧
              expanded.toList = complete.toList ++ suffix

/-- Suffix-removal step of the paper. The explicit suffix parameter records
the prefix shape produced by `CompletePrefixReachability`; the marked-graph
hypothesis records that no new support or edge survives outside the complete
prefix. -/
def CompleteSuffixContraction : Prop :=
  ∀ complete expanded : Word Nat, ∀ suffix : List Nat,
    TrahtmanIndecomposable complete →
      TrahtmanComplete complete →
        expanded.toList = complete.toList ++ suffix →
          complete.SameMarkedDigraph expanded →
            Derives basis expanded complete

/-- The graph-normalization theorem restricted to one indecomposable
component. -/
def IndecomposableMarkedDigraphDerivationalCompleteness : Prop :=
  ∀ left right : Word Nat,
    TrahtmanIndecomposable left →
      left.SameMarkedDigraph right →
        Derives basis left right

/-- Final maximal-factor assembly step: normalization on indecomposable
components implies normalization of arbitrary words. -/
def MaximalIndecomposableFactorReduction : Prop :=
  IndecomposableMarkedDigraphDerivationalCompleteness →
    MarkedDigraphDerivationalCompleteness

/-- The three indecomposable-word steps in the published argument really do
reduce every equal-graph indecomposable pair to a common complete word. -/
theorem indecomposableMarkedDigraphDerivationalCompleteness_of_publishedSteps
    (representative : CompleteRepresentativeExistence)
    (prefixReachability : CompletePrefixReachability)
    (suffixContraction : CompleteSuffixContraction) :
    IndecomposableMarkedDigraphDerivationalCompleteness := by
  intro left right leftIndecomposable same
  rcases representative left leftIndecomposable with
    ⟨complete, leftCompleteGraph, completeWord⟩
  have completeIndecomposable : TrahtmanIndecomposable complete :=
    (trahtmanIndecomposable_iff_of_sameMarkedDigraph
      leftCompleteGraph).mp leftIndecomposable
  rcases prefixReachability left complete leftIndecomposable
      leftCompleteGraph completeWord with
    ⟨leftExpanded, leftSuffix, leftExpansion, leftShape⟩
  have leftExpandedGraph : left.SameMarkedDigraph leftExpanded :=
    derives_sameMarkedDigraph leftExpansion
  have completeLeftExpandedGraph :
      complete.SameMarkedDigraph leftExpanded :=
    sameMarkedDigraph_trans
      (sameMarkedDigraph_symm leftCompleteGraph) leftExpandedGraph
  have leftContraction : Derives basis leftExpanded complete :=
    suffixContraction complete leftExpanded leftSuffix
      completeIndecomposable completeWord leftShape
      completeLeftExpandedGraph
  have leftToComplete : Derives basis left complete :=
    leftExpansion.trans leftContraction

  have rightIndecomposable : TrahtmanIndecomposable right :=
    (trahtmanIndecomposable_iff_of_sameMarkedDigraph same).mp
      leftIndecomposable
  have rightCompleteGraph : right.SameMarkedDigraph complete :=
    sameMarkedDigraph_trans (sameMarkedDigraph_symm same)
      leftCompleteGraph
  rcases prefixReachability right complete rightIndecomposable
      rightCompleteGraph completeWord with
    ⟨rightExpanded, rightSuffix, rightExpansion, rightShape⟩
  have rightExpandedGraph : right.SameMarkedDigraph rightExpanded :=
    derives_sameMarkedDigraph rightExpansion
  have completeRightExpandedGraph :
      complete.SameMarkedDigraph rightExpanded :=
    sameMarkedDigraph_trans
      (sameMarkedDigraph_symm rightCompleteGraph) rightExpandedGraph
  have rightContraction : Derives basis rightExpanded complete :=
    suffixContraction complete rightExpanded rightSuffix
      completeIndecomposable completeWord rightShape
      completeRightExpandedGraph
  have rightToComplete : Derives basis right complete :=
    rightExpansion.trans rightContraction
  exact leftToComplete.trans rightToComplete.symm

/-- Fully explicit version of the four remaining nodes in Trahtman's
normalization proof. It is intentionally separate from the older one-field
architecture so all existing conditional APIs remain stable. -/
structure TrahtmanNormalizationArchitecture : Prop where
  completeRepresentative : CompleteRepresentativeExistence
  prefixReachability : CompletePrefixReachability
  suffixContraction : CompleteSuffixContraction
  maximalFactorReduction : MaximalIndecomposableFactorReduction

theorem markedDigraphDerivationalCompleteness_of_normalizationArchitecture
    (architecture : TrahtmanNormalizationArchitecture) :
    MarkedDigraphDerivationalCompleteness :=
  architecture.maximalFactorReduction
    (indecomposableMarkedDigraphDerivationalCompleteness_of_publishedSteps
      architecture.completeRepresentative
      architecture.prefixReachability
      architecture.suffixContraction)

/-- The representative `BasisFor` endpoint is logically equivalent to the
single explicit graph-normalization obligation. All finite semantics and the
reverse implication from derivability to graph equality are unconditional. -/
theorem basisFor_iff_markedDigraphDerivationalCompleteness :
    BasisFor Generated.Catalogue.S5_868.table.semigroup basis ↔
      MarkedDigraphDerivationalCompleteness := by
  constructor
  · intro complete left right same
    exact complete.2 ⟨left, right⟩
      ((satisfiedBy_iff_sameMarkedDigraph ⟨left, right⟩).mpr same)
  · intro derivesAll
    refine ⟨catalogueModels, ?_⟩
    intro identity valid
    exact derivesAll identity.lhs identity.rhs
      ((satisfiedBy_iff_sameMarkedDigraph identity).mp valid)

/-- Explicit proof architecture for the published argument. Supplying the
graph-normalization field yields both representative and opposite
`BasisFor` endpoints; every other component is already a theorem in this
packet. -/
structure TrahtmanProofArchitecture : Prop where
  graphNormalization : MarkedDigraphDerivationalCompleteness

theorem basis_complete_of_markedDigraphDerivationalCompleteness
    (complete : MarkedDigraphDerivationalCompleteness) :
    BasisFor Generated.Catalogue.S5_868.table.semigroup basis :=
  basisFor_iff_markedDigraphDerivationalCompleteness.mpr complete

theorem representative_basis_of_markedDigraphDerivationalCompleteness
    (complete : MarkedDigraphDerivationalCompleteness) :
    BasisFor Generated.Catalogue.S5_868.table.semigroup basis :=
  basis_complete_of_markedDigraphDerivationalCompleteness complete

theorem opposite_basis_complete_of_markedDigraphDerivationalCompleteness
    (complete : MarkedDigraphDerivationalCompleteness) :
    BasisFor Generated.Catalogue.S5_868.table.semigroup.opposite
      oppositeBasis := by
  simpa [oppositeBasis] using
    (basis_complete_of_markedDigraphDerivationalCompleteness
      complete).oppositeReversed

theorem opposite_basis_of_markedDigraphDerivationalCompleteness
    (complete : MarkedDigraphDerivationalCompleteness) :
    BasisFor Generated.Catalogue.S5_868.table.semigroup.opposite
      (reversedBasis basis) := by
  simpa [oppositeBasis] using
    opposite_basis_complete_of_markedDigraphDerivationalCompleteness complete

/-- The opposite endpoint has exactly the same sole proof obligation. -/
theorem oppositeBasisFor_iff_markedDigraphDerivationalCompleteness :
    BasisFor Generated.Catalogue.S5_868.table.semigroup.opposite
        oppositeBasis ↔
      MarkedDigraphDerivationalCompleteness := by
  constructor
  · intro oppositeComplete
    have representativeWithDoubleReverse :=
      oppositeComplete.oppositeReversed
    have representative :
        BasisFor Generated.Catalogue.S5_868.table.semigroup basis := by
      simpa [oppositeBasis] using representativeWithDoubleReverse
    exact
      basisFor_iff_markedDigraphDerivationalCompleteness.mp representative
  · exact
      opposite_basis_complete_of_markedDigraphDerivationalCompleteness

theorem basis_complete_of_architecture
    (architecture : TrahtmanProofArchitecture) :
    BasisFor Generated.Catalogue.S5_868.table.semigroup basis :=
  basis_complete_of_markedDigraphDerivationalCompleteness
    architecture.graphNormalization

theorem opposite_basis_complete_of_architecture
    (architecture : TrahtmanProofArchitecture) :
    BasisFor Generated.Catalogue.S5_868.table.semigroup.opposite
      oppositeBasis :=
  opposite_basis_complete_of_markedDigraphDerivationalCompleteness
    architecture.graphNormalization

end SemigroupBasis.CoRoots.S5_868
