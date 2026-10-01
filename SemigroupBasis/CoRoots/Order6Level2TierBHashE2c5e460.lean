import SemigroupBasis.ChainReplay
import SemigroupBasis.CoRoots.S5_442Completeness
import SemigroupBasis.CoRoots.S5_790Family
import SemigroupBasis.CoRoots.S5_806Completeness
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S2_4
import SemigroupBasis.Generated.S3_11
import SemigroupBasis.Subdirect

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6Level2TierBHashE2c5e460

open SemigroupBasis
open SemigroupBasis.Examples

/-!
Unrestricted completeness for the displayed-basis group with SHA-256
`e2c5e46024a280bf227db81ad90d0d287283ae4b8e28d1b2c8c1b6318c257075`.

The common invariant is the ordered `S4_70` component signature, pointwise
occurrence parity, and the first letter.  The proof replays the complete
`S5_442` parity-component normalizer behind a protected prefix.  Nine
first-letter-changing source laws are supplied by fixed, kernel-checked
guarded chains; all other source laws are direct candidate laws.
-/

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

def xx : Word Nat := w 0 [0]
def xxxx : Word Nat := w 0 [0, 0, 0]
def xxxyx : Word Nat := w 0 [0, 0, 1, 0]
def xyx : Word Nat := w 0 [1, 0]
def xxyx : Word Nat := w 0 [0, 1, 0]
def xyxx : Word Nat := w 0 [1, 0, 0]
def xxyxx : Word Nat := w 0 [0, 1, 0, 0]
def xyxxx : Word Nat := w 0 [1, 0, 0, 0]
def xyxyy : Word Nat := w 0 [1, 0, 1, 1]
def xyyxy : Word Nat := w 0 [1, 1, 0, 1]
def xyyyx : Word Nat := w 0 [1, 1, 1, 0]
def xyxy : Word Nat := w 0 [1, 0, 1]
def xyyx : Word Nat := w 0 [1, 1, 0]
def xyxzy : Word Nat := w 0 [1, 0, 2, 1]
def xyyzx : Word Nat := w 0 [1, 1, 2, 0]
def xyyzy : Word Nat := w 0 [1, 1, 2, 1]
def xzyzz : Word Nat := w 0 [2, 1, 2, 2]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xzyx : Word Nat := w 0 [2, 1, 0]
def xyzyz : Word Nat := w 0 [1, 2, 1, 2]
def xzyyz : Word Nat := w 0 [2, 1, 1, 2]

def powerLaw : Identity Nat := ⟨xx, xxxx⟩
def tripleLeftContractionLaw : Identity Nat := ⟨xxxyx, xyx⟩
def endpointTransferLaw : Identity Nat := ⟨xxyx, xyxx⟩
def splitEndpointContractionLaw : Identity Nat := ⟨xxyxx, xyx⟩
def rightTripleExpansionLaw : Identity Nat := ⟨xyx, xyxxx⟩
def xyxXYXYYLaw : Identity Nat := ⟨xyx, xyxyy⟩
def xyxXYYXYLaw : Identity Nat := ⟨xyx, xyyxy⟩
def xyxXYYYXLaw : Identity Nat := ⟨xyx, xyyyx⟩
def alternatingLaw : Identity Nat := ⟨xyxy, xyyx⟩
def attachmentLaw : Identity Nat := ⟨xyxzy, xyyzx⟩
def guardedSquareTransferLaw : Identity Nat := ⟨xyyzy, xzyzz⟩
def componentSwapLaw : Identity Nat := ⟨xyzx, xzyx⟩
def guardedAlternatingTransferLaw : Identity Nat := ⟨xyzyz, xzyyz⟩

/-- The exact thirteen-law displayed candidate. -/
def basis : List (Identity Nat) :=
  [powerLaw, tripleLeftContractionLaw, endpointTransferLaw,
    splitEndpointContractionLaw, rightTripleExpansionLaw,
    xyxXYXYYLaw, xyxXYYXYLaw, xyxXYYYXLaw, alternatingLaw,
    attachmentLaw, guardedSquareTransferLaw, componentSwapLaw,
    guardedAlternatingTransferLaw]

theorem basis_length : basis.length = 13 := by
  decide

private def instantiateThreeWords
    (first second third : Word Nat) : Nat -> Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

private theorem derivesBasisSubstitution
    (identity : Identity Nat) (member : identity ∈ basis)
    (substitution : Nat -> Word Nat) :
    Derives basis
      (identity.lhs.bind substitution)
      (identity.rhs.bind substitution) :=
  Derives.subst (Derives.fromBasis member) substitution

private theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) (((u ++ u) ++ u) ++ u) := by
  have substituted :=
    derivesBasisSubstitution powerLaw
      (by simp [basis])
      (instantiateThreeWords u u u)
  simpa [powerLaw, xx, xxxx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

private theorem derivesTripleLeftContraction (u v : Word Nat) :
    Derives basis
      ((((u ++ u) ++ u) ++ v) ++ u)
      ((u ++ v) ++ u) := by
  have substituted :=
    derivesBasisSubstitution tripleLeftContractionLaw
      (by simp [basis])
      (instantiateThreeWords u v v)
  simpa [tripleLeftContractionLaw, xxxyx, xyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-! ## Fixed guarded replay certificates -/

private def identitySubstitution : List (List Nat) :=
  [[0], [1], [2], [3]]

private def guardedXyxYxxyyChain : ChainReplay.Chain Nat :=
  [
    { lawIndex := 5
      direction := .forward
      leftContext := [3]
      rightContext := []
      substitution := identitySubstitution },
    { lawIndex := 12
      direction := .forward
      leftContext := []
      rightContext := [1]
      substitution := [[3], [0], [1], [3]] }
  ]

private theorem guardedXyxYxxyy :
    Derives basis (w 3 [0, 1, 0]) (w 3 [1, 0, 0, 1, 1]) :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := guardedXyxYxxyyChain) (by decide)

private def guardedXyxYxyxyChain : ChainReplay.Chain Nat :=
  [
    { lawIndex := 6
      direction := .forward
      leftContext := [3]
      rightContext := []
      substitution := identitySubstitution },
    { lawIndex := 12
      direction := .backward
      leftContext := []
      rightContext := [1]
      substitution := [[3], [1], [0], [3]] }
  ]

private theorem guardedXyxYxyxy :
    Derives basis (w 3 [0, 1, 0]) (w 3 [1, 0, 1, 0, 1]) :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := guardedXyxYxyxyChain) (by decide)

private def guardedXyxYxyyxChain : ChainReplay.Chain Nat :=
  [
    { lawIndex := 3
      direction := .backward
      leftContext := [3]
      rightContext := []
      substitution := identitySubstitution },
    { lawIndex := 10
      direction := .forward
      leftContext := []
      rightContext := [0]
      substitution := [[3], [0], [1], [3]] }
  ]

private theorem guardedXyxYxyyx :
    Derives basis (w 3 [0, 1, 0]) (w 3 [1, 0, 1, 1, 0]) :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := guardedXyxYxyyxChain) (by decide)

private def guardedXyxYyxxyChain : ChainReplay.Chain Nat :=
  [
    { lawIndex := 3
      direction := .backward
      leftContext := [3]
      rightContext := []
      substitution := identitySubstitution },
    { lawIndex := 0
      direction := .forward
      leftContext := [3, 0, 0, 1]
      rightContext := []
      substitution := identitySubstitution },
    { lawIndex := 10
      direction := .backward
      leftContext := []
      rightContext := []
      substitution := [[3], [1], [0, 0], [3]] }
  ]

private theorem guardedXyxYyxxy :
    Derives basis (w 3 [0, 1, 0]) (w 3 [1, 1, 0, 0, 1]) :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := guardedXyxYyxxyChain) (by decide)

private def guardedXyxYyxyxChain : ChainReplay.Chain Nat :=
  [
    { lawIndex := 4
      direction := .forward
      leftContext := [3]
      rightContext := []
      substitution := identitySubstitution },
    { lawIndex := 10
      direction := .backward
      leftContext := []
      rightContext := [0]
      substitution := [[3], [1], [0], [3]] }
  ]

private theorem guardedXyxYyxyx :
    Derives basis (w 3 [0, 1, 0]) (w 3 [1, 1, 0, 1, 0]) :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := guardedXyxYyxyxChain) (by decide)

private def guardedXxyxYxyyChain : ChainReplay.Chain Nat :=
  [
    { lawIndex := 10
      direction := .forward
      leftContext := []
      rightContext := []
      substitution := [[3], [0], [1], [3]] }
  ]

private theorem guardedXxyxYxyy :
    Derives basis (w 3 [0, 0, 1, 0]) (w 3 [1, 0, 1, 1]) :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := guardedXxyxYxyyChain) (by decide)

private def guardedXyxyYxxyChain : ChainReplay.Chain Nat :=
  [
    { lawIndex := 12
      direction := .forward
      leftContext := []
      rightContext := []
      substitution := [[3], [0], [1], [3]] }
  ]

private theorem guardedXyxyYxxy :
    Derives basis (w 3 [0, 1, 0, 1]) (w 3 [1, 0, 0, 1]) :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := guardedXyxyYxxyChain) (by decide)

private def guardedXxyzxYxyzyChain : ChainReplay.Chain Nat :=
  [
    { lawIndex := 10
      direction := .forward
      leftContext := []
      rightContext := []
      substitution := [[3], [0], [1, 2], [3]] },
    { lawIndex := 11
      direction := .forward
      leftContext := [3]
      rightContext := [2]
      substitution := [[1], [2], [0, 1, 2], [3]] },
    { lawIndex := 6
      direction := .backward
      leftContext := [3, 1, 0]
      rightContext := []
      substitution := [[1], [2], [2], [3]] }
  ]

private theorem guardedXxyzxYxyzy :
    Derives basis (w 3 [0, 0, 1, 2, 0])
      (w 3 [1, 0, 1, 2, 1]) :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := guardedXxyzxYxyzyChain) (by decide)

private def guardedXyxzyYxxzyChain : ChainReplay.Chain Nat :=
  [
    { lawIndex := 3
      direction := .backward
      leftContext := [3]
      rightContext := [2, 1]
      substitution := identitySubstitution },
    { lawIndex := 9
      direction := .backward
      leftContext := [3, 0, 0]
      rightContext := []
      substitution := [[1], [0], [2], [3]] },
    { lawIndex := 10
      direction := .forward
      leftContext := []
      rightContext := [1, 2, 0]
      substitution := [[3], [0], [1], [3]] },
    { lawIndex := 4
      direction := .backward
      leftContext := [3]
      rightContext := [2, 0]
      substitution := [[1], [0], [2], [3]] },
    { lawIndex := 9
      direction := .forward
      leftContext := [3]
      rightContext := []
      substitution := [[1], [0], [2], [3]] }
  ]

private theorem guardedXyxzyYxxzy :
    Derives basis (w 3 [0, 1, 0, 2, 1])
      (w 3 [1, 0, 0, 2, 1]) :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := guardedXyxzyYxxzyChain) (by decide)

private def guardedSubstitution
    (ctx : Word Nat) (sigma : Nat -> Word Nat) : Nat -> Word Nat
  | 0 => sigma 0
  | 1 => sigma 1
  | 2 => sigma 2
  | 3 => ctx
  | n + 4 => Word.singleton (n + 4)

private theorem bind_append
    (left right : Word Nat) (sigma : Nat -> Word Nat) :
    (left ++ right).bind sigma =
      left.bind sigma ++ right.bind sigma := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (word : Word Nat) (tau sigma : Nat -> Word Nat) :
    (word.bind tau).bind sigma =
      word.bind (fun letter => (tau letter).bind sigma) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem liftGuardedChain
    {source target : Word Nat}
    (derivation : Derives basis source target)
    (ctx : Word Nat) (sigma : Nat -> Word Nat) :
    Derives basis
      (source.bind (guardedSubstitution ctx sigma))
      (target.bind (guardedSubstitution ctx sigma)) :=
  Derives.subst derivation (guardedSubstitution ctx sigma)

/-- Replay the complete `S5_442` normalizer after an arbitrary protected
nonempty prefix. -/
theorem liftS5_442UnderPrefix
    {left right : Word Nat}
    (derivation :
      Derives SemigroupBasis.CoRoots.S5_442.basis left right)
    (ctx : Word Nat) (sigma : Nat -> Word Nat) :
    Derives basis
      (ctx ++ left.bind sigma)
      (ctx ++ right.bind sigma) := by
  induction derivation generalizing ctx sigma with
  | fromBasis member =>
      simp only [SemigroupBasis.CoRoots.S5_442.basis,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl
      · exact Derives.prepend ctx <|
          derivesBasisSubstitution powerLaw (by simp [basis]) sigma
      · exact Derives.prepend ctx <|
          (derivesBasisSubstitution tripleLeftContractionLaw
            (by simp [basis]) sigma).symm
      · exact Derives.prepend ctx <|
          (derivesBasisSubstitution splitEndpointContractionLaw
            (by simp [basis]) sigma).symm
      · exact Derives.prepend ctx <|
          derivesBasisSubstitution rightTripleExpansionLaw
            (by simp [basis]) sigma
      · exact Derives.prepend ctx <|
          derivesBasisSubstitution xyxXYXYYLaw
            (by simp [basis]) sigma
      · exact Derives.prepend ctx <|
          derivesBasisSubstitution xyxXYYXYLaw
            (by simp [basis]) sigma
      · exact Derives.prepend ctx <|
          derivesBasisSubstitution xyxXYYYXLaw
            (by simp [basis]) sigma
      · simpa [SemigroupBasis.CoRoots.S5_442.xyxYXXYYLaw,
          SemigroupBasis.CoRoots.S5_442.xyx,
          SemigroupBasis.CoRoots.S5_442.yxxyy,
          SemigroupBasis.CoRoots.S5_442.w, w, guardedSubstitution,
          Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          liftGuardedChain guardedXyxYxxyy ctx sigma
      · simpa [SemigroupBasis.CoRoots.S5_442.xyxYXYXYLaw,
          SemigroupBasis.CoRoots.S5_442.xyx,
          SemigroupBasis.CoRoots.S5_442.yxyxy,
          SemigroupBasis.CoRoots.S5_442.w, w, guardedSubstitution,
          Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          liftGuardedChain guardedXyxYxyxy ctx sigma
      · simpa [SemigroupBasis.CoRoots.S5_442.xyxYXYYXLaw,
          SemigroupBasis.CoRoots.S5_442.xyx,
          SemigroupBasis.CoRoots.S5_442.yxyyx,
          SemigroupBasis.CoRoots.S5_442.w, w, guardedSubstitution,
          Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          liftGuardedChain guardedXyxYxyyx ctx sigma
      · simpa [SemigroupBasis.CoRoots.S5_442.xyxYYXXYLaw,
          SemigroupBasis.CoRoots.S5_442.xyx,
          SemigroupBasis.CoRoots.S5_442.yyxxy,
          SemigroupBasis.CoRoots.S5_442.w, w, guardedSubstitution,
          Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          liftGuardedChain guardedXyxYyxxy ctx sigma
      · simpa [SemigroupBasis.CoRoots.S5_442.xyxYYXYXLaw,
          SemigroupBasis.CoRoots.S5_442.xyx,
          SemigroupBasis.CoRoots.S5_442.yyxyx,
          SemigroupBasis.CoRoots.S5_442.w, w, guardedSubstitution,
          Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          liftGuardedChain guardedXyxYyxyx ctx sigma
      · exact Derives.prepend ctx <|
          derivesBasisSubstitution endpointTransferLaw
            (by simp [basis]) sigma
      · simpa [SemigroupBasis.CoRoots.S5_442.xxyxYXYYLaw,
          SemigroupBasis.CoRoots.S5_442.xxyx,
          SemigroupBasis.CoRoots.S5_442.yxyy,
          SemigroupBasis.CoRoots.S5_442.w, w, guardedSubstitution,
          Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          liftGuardedChain guardedXxyxYxyy ctx sigma
      · exact Derives.prepend ctx <|
          derivesBasisSubstitution alternatingLaw
            (by simp [basis]) sigma
      · simpa [SemigroupBasis.CoRoots.S5_442.xyxyYXXYLaw,
          SemigroupBasis.CoRoots.S5_442.xyxy,
          SemigroupBasis.CoRoots.S5_442.yxxy,
          SemigroupBasis.CoRoots.S5_442.w, w, guardedSubstitution,
          Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          liftGuardedChain guardedXyxyYxxy ctx sigma
      · exact Derives.prepend ctx <|
          derivesBasisSubstitution componentSwapLaw
            (by simp [basis]) sigma
      · simpa [SemigroupBasis.CoRoots.S5_442.xxyzxYXYZYLaw,
          SemigroupBasis.CoRoots.S5_442.xxyzx,
          SemigroupBasis.CoRoots.S5_442.yxyzy,
          SemigroupBasis.CoRoots.S5_442.w, w, guardedSubstitution,
          Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          liftGuardedChain guardedXxyzxYxyzy ctx sigma
      · exact Derives.prepend ctx <|
          derivesBasisSubstitution attachmentLaw
            (by simp [basis]) sigma
      · simpa [SemigroupBasis.CoRoots.S5_442.xyxzyYXXZYLaw,
          SemigroupBasis.CoRoots.S5_442.xyxzy,
          SemigroupBasis.CoRoots.S5_442.yxxzy,
          SemigroupBasis.CoRoots.S5_442.w, w, guardedSubstitution,
          Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          liftGuardedChain guardedXyxzyYxxzy ctx sigma
  | refl =>
      exact Derives.refl _
  | symm _ inductionHypothesis =>
      exact (inductionHypothesis ctx sigma).symm
  | trans _ _ firstHypothesis secondHypothesis =>
      exact
        (firstHypothesis ctx sigma).trans
          (secondHypothesis ctx sigma)
  | prepend pre _ inductionHypothesis =>
      simpa [bind_append, Word.append_assoc] using
        inductionHypothesis (ctx ++ pre.bind sigma) sigma
  | appendRight _ post inductionHypothesis =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight
          (inductionHypothesis ctx sigma) (post.bind sigma)
  | subst _ tau inductionHypothesis =>
      simpa [bind_bind] using
        inductionHypothesis ctx
          (fun letter => (tau letter).bind sigma)

/-! ## Width-free fixed-first closure -/

/-- The exact joint invariant forced by each of the three factor pairs. -/
structure SameGuardedParityComponentSignature
    (left right : Word Nat) : Prop where
  parityComponent :
    S5_442Invariant.SameParityComponentSignature left right
  first : left.head = right.head

namespace SameGuardedParityComponentSignature

theorem refl (word : Word Nat) :
    SameGuardedParityComponentSignature word word :=
  ⟨S5_442Invariant.SameParityComponentSignature.refl word, rfl⟩

theorem symm {left right : Word Nat}
    (same : SameGuardedParityComponentSignature left right) :
    SameGuardedParityComponentSignature right left :=
  ⟨same.parityComponent.symm, same.first.symm⟩

theorem trans {left middle right : Word Nat}
    (first : SameGuardedParityComponentSignature left middle)
    (second : SameGuardedParityComponentSignature middle right) :
    SameGuardedParityComponentSignature left right :=
  ⟨first.parityComponent.trans second.parityComponent,
    first.first.trans second.first⟩

end SameGuardedParityComponentSignature

private theorem connectedComponentSignaturesList_canonical
    (letters : List Nat) :
    connectedComponentFourCanonicalSignatures
      (connectedComponentSignaturesList letters) := by
  let components := connectedComponentDecomposeList letters
  have nonempty :=
    connectedComponentDecomposeList_nonempty_components letters
  have pairwise :=
    connectedComponentDecomposeList_pairwiseDisjoint letters
  constructor
  · intro signature signatureMember
    rw [connectedComponentSignaturesList] at signatureMember
    rcases List.mem_map.mp signatureMember with
      ⟨component, componentMember, rfl⟩
    exact connectedComponentSignatureOfList_valid
      (nonempty component componentMember)
  · rw [connectedComponentSignaturesList, List.pairwise_map]
    apply pairwise.imp
    intro left right disjoint
    intro letter leftMember rightMember
    apply disjoint letter
    · rw [connectedComponentSignatureOfList_support,
        connectedComponentSortedSupport_mem_iff] at leftMember
      exact leftMember
    · rw [connectedComponentSignatureOfList_support,
        connectedComponentSortedSupport_mem_iff] at rightMember
      exact rightMember

private def singletonComponentSignature
    (letter : Nat) : connectedComponentSignature :=
  ⟨[letter], false⟩

private theorem singleton_cons_signatures_canonical
    (head : Nat) (tail : List Nat)
    (headAbsent : head ∉ tail) :
    connectedComponentFourCanonicalSignatures
      (singletonComponentSignature head ::
        connectedComponentSignaturesList tail) := by
  have tailCanonical :=
    connectedComponentSignaturesList_canonical tail
  constructor
  · intro signature member
    rcases List.mem_cons.mp member with rfl | member
    · simp [singletonComponentSignature,
        connectedComponentSignatureValid]
    · exact tailCanonical.1 signature member
  · rw [List.pairwise_cons]
    refine ⟨?_, tailCanonical.2⟩
    intro signature signatureMember tested singletonMember supportMember
    have testedEq : tested = head := by
      simpa [singletonComponentSignature] using singletonMember
    subst tested
    have renderedMember :
        head ∈ connectedComponentRenderSignature signature :=
      (connectedComponentRenderSignature_mem_iff
        (tailCanonical.1 signature signatureMember).1 head).2
        supportMember
    have allRenderedMember :
        head ∈ connectedComponentRenderSignatures
          (connectedComponentSignaturesList tail) := by
      rw [connectedComponentRenderSignatures, List.mem_flatMap]
      exact ⟨signature, signatureMember, renderedMember⟩
    have canonicalMember :
        head ∈ connectedComponentCanonicalRenderList tail := by
      simpa [connectedComponentCanonicalRenderList] using
        allRenderedMember
    exact headAbsent <|
      (connectedComponentCanonicalRenderList_mem_iff head tail).1
        canonicalMember

private theorem canonicalRenderList_cons_of_head_absent
    (head : Nat) (tail : List Nat)
    (headAbsent : head ∉ tail) :
    connectedComponentCanonicalRenderList (head :: tail) =
      head :: connectedComponentCanonicalRenderList tail := by
  let source : Word Nat := ⟨head, tail⟩
  let target : Word Nat :=
    ⟨head, connectedComponentCanonicalRenderList tail⟩
  have sourceCanonical :=
    connectedComponentFourSignaturesWord_canonical source
  have targetCanonical :=
    singleton_cons_signatures_canonical head tail headAbsent
  have sourceDerivation :=
    connectedComponentFour_derivesCanonical source
  have targetDerivation :
      Derives connectedComponentFourBasis source target := by
    have tailDerivation :=
      connectedComponentCanonicalRenderList_derives tail
    have prefixed :=
      tailDerivation.prepend [head]
    simpa [source, target, connectedComponentWordOfCons] using
      prefixed.toWord
  have equalEval :
      ∀ valuation : Nat -> Fin 4,
        connectedComponentFour.semigroup.eval valuation
            (connectedComponentCanonicalRender source) =
          connectedComponentFour.semigroup.eval valuation target := by
    intro valuation
    have sourceSound :=
      sourceDerivation.sound connectedComponentFourBasis_models valuation
    have targetSound :=
      targetDerivation.sound connectedComponentFourBasis_models valuation
    exact sourceSound.symm.trans targetSound
  have signaturesEqual :
      connectedComponentSignaturesWord source =
        singletonComponentSignature head ::
          connectedComponentSignaturesList tail := by
    apply connectedComponentCanonical_eq_of_equalEval
      sourceCanonical targetCanonical
      (connectedComponentCanonicalRender source) target
    · exact connectedComponentCanonicalRender_toList source
    · simp [target, Word.toList, singletonComponentSignature,
        connectedComponentRenderSignatures,
        connectedComponentCanonicalRenderList]
    · exact equalEval
  change
    connectedComponentRenderSignatures
        (connectedComponentSignaturesWord source) =
      head ::
        connectedComponentRenderSignatures
          (connectedComponentSignaturesList tail)
  rw [signaturesEqual]
  rfl

private theorem unaryCut_empty_head_iff_count_one
    (word : Word Nat) :
    connectedComponentFourUnaryCut [] word.head word.toList ↔
      word.toList.count word.head = 1 := by
  cases word with
  | mk head tail =>
      constructor
      · rintro
          ⟨actualLeft, actualRight, shape,
            leftExact, headNotRight, _⟩
        have headNotLeft : head ∉ actualLeft := by
          intro member
          have impossible := (leftExact head).1 member
          simpa using impossible
        rw [shape, List.count_append]
        simp [List.count_eq_zero.mpr headNotLeft,
          List.count_eq_zero.mpr headNotRight]
      · intro countOne
        have headNotTail : head ∉ tail := by
          intro member
          have positive : 0 < tail.count head :=
            List.count_pos_iff.mpr member
          simp only [Word.toList, List.count_cons_self] at countOne
          omega
        refine ⟨[], tail, rfl, ?_, headNotTail, ?_⟩
        · intro letter
          simp
        · intro letter member
          simp at member

private theorem headCountOne_iff_of_sameSignature
    {left right : Word Nat}
    (same : SameGuardedParityComponentSignature left right) :
    left.toList.count left.head = 1 ↔
      right.toList.count right.head = 1 := by
  have equalEval :=
    S5_442Invariant.connectedComponentFour_equalEval_of_sameComponentSignature
      left right same.parityComponent.components
  have cutIff :=
    connectedComponentFourEqualEval_unaryCut_iff
      left right equalEval [] left.head (by simp)
      (by cases left <;> simp [Word.toList])
      (by simp)
  have rightCutIff :
      connectedComponentFourUnaryCut [] left.head right.toList ↔
        right.toList.count right.head = 1 := by
    rw [same.first]
    exact unaryCut_empty_head_iff_count_one right
  exact
    (unaryCut_empty_head_iff_count_one left).symm.trans <|
      cutIff.trans rightCutIff

private theorem headNotMemTailOfCountOne
    (word : Word Nat)
    (countOne : word.toList.count word.head = 1) :
    word.head ∉ word.tail := by
  intro member
  have positive : 0 < word.tail.count word.head :=
    List.count_pos_iff.mpr member
  simp only [Word.toList, List.count_cons_self] at countOne
  omega

private theorem headMemTailOfCountNeOne
    (word : Word Nat)
    (countNotOne : word.toList.count word.head ≠ 1) :
    word.head ∈ word.tail := by
  apply Decidable.byContradiction
  intro absent
  apply countNotOne
  cases word with
  | mk head tail =>
      simp [Word.toList, List.count_eq_zero.mpr absent]

private theorem tailNilOfSameSignature
    {left right : Word Nat}
    (same : SameGuardedParityComponentSignature left right)
    (rightHeadSimple :
      right.toList.count right.head = 1)
    (leftTailEmpty : left.tail = []) :
    right.tail = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro letter member
  have rightMember : letter ∈ right.toList := by
    cases right
    simp [Word.toList, member]
  have leftMember : letter ∈ left.toList :=
    (S5_442Invariant.sameSupport_of_sameComponentSignature
      same.parityComponent.components letter).2 rightMember
  have letterIsLeftHead : letter = left.head := by
    have headOrTail :
        letter = left.head ∨ letter ∈ left.tail := by
      simpa [Word.toList] using leftMember
    rcases headOrTail with equal | inTail
    · exact equal
    · simp [leftTailEmpty] at inTail
  have letterIsRightHead : letter = right.head :=
    letterIsLeftHead.trans same.first
  have rightHeadInTail : right.head ∈ right.tail := by
    simpa [letterIsRightHead] using member
  exact
    (headNotMemTailOfCountOne right rightHeadSimple)
      rightHeadInTail

private abbrev ListDerives :=
  S5_107.ListDerives basis

private theorem listDerivesAddInitialPair
    (head : Nat) (tail : List Nat)
    (headInTail : head ∈ tail) :
    ListDerives
      (head :: tail)
      ([head, head] ++ head :: tail) := by
  rcases List.append_of_mem headInTail with
    ⟨before, after, rfl⟩
  cases before with
  | nil =>
      have expanded :=
        S5_107.ListDerives.ofWord
          (derivesPowerExpansion (Word.singleton head))
      simpa [Word.toList_append, List.append_assoc] using
        expanded.append after
  | cons middleHead middleTail =>
      let middle :=
        S5_107.listWordOfCons middleHead middleTail
      have expanded :=
        S5_107.ListDerives.ofWord
          (derivesTripleLeftContraction
            (Word.singleton head) middle).symm
      simpa [middle, S5_107.listWordOfCons,
        Word.toList_append, List.append_assoc] using
        expanded.append after

private theorem derivesAddInitialPair
    (word : Word Nat)
    (headInTail : word.head ∈ word.tail) :
    Derives basis word
      ((Word.singleton word.head ++ Word.singleton word.head) ++ word) := by
  cases word with
  | mk head tail =>
      have listDerivation :=
        listDerivesAddInitialPair head tail headInTail
      simpa [S5_107.listWordOfCons, Word.singleton,
        Word.append, List.append_assoc] using
        S5_107.ListDerives.toWord listDerivation

private theorem suffixSameParityComponent
    (head : Nat)
    (left right : Word Nat)
    (headAbsentLeft : head ∉ left.toList)
    (headAbsentRight : head ∉ right.toList)
    (whole :
      SameGuardedParityComponentSignature
        (Word.singleton head ++ left)
        (Word.singleton head ++ right)) :
    S5_442Invariant.SameParityComponentSignature left right := by
  have leftSplit :=
    canonicalRenderList_cons_of_head_absent
      head left.toList headAbsentLeft
  have rightSplit :=
    canonicalRenderList_cons_of_head_absent
      head right.toList headAbsentRight
  have wholeCanonical :
      connectedComponentCanonicalRenderList
          (head :: left.toList) =
        connectedComponentCanonicalRenderList
          (head :: right.toList) :=
    connectedComponentCanonicalRenderList_eq_of_signature_eq
      whole.parityComponent.components
  rw [leftSplit, rightSplit] at wholeCanonical
  have suffixCanonical :
      connectedComponentCanonicalRenderList left.toList =
        connectedComponentCanonicalRenderList right.toList :=
    (List.cons.inj wholeCanonical).2
  have canonicalWordEq :
      connectedComponentCanonicalRender left =
        connectedComponentCanonicalRender right := by
    apply Word.toList_injective
    simpa [connectedComponentCanonicalRender_toList] using
      suffixCanonical
  have componentDerivation :
      Derives connectedComponentFourBasis left right := by
    exact (connectedComponentFour_derivesCanonical left).trans <| by
      rw [canonicalWordEq]
      exact (connectedComponentFour_derivesCanonical right).symm
  have components :
      S5_442Invariant.SameComponentSignature left right :=
    S5_442Invariant.sameComponentSignature_of_connectedComponentFour_equalEval
      left right
      (fun valuation =>
        componentDerivation.sound
          connectedComponentFourBasis_models valuation)
  have parity :
      S5_442Invariant.SameOccurrenceParity left right := by
    intro letter
    by_cases letterEq : letter = head
    · subst letter
      simp [List.count_eq_zero.mpr headAbsentLeft,
        List.count_eq_zero.mpr headAbsentRight]
    · have headNe : head ≠ letter := Ne.symm letterEq
      simpa [Word.toList, letterEq, headNe] using
        whole.parityComponent.parity letter
  exact ⟨components, parity⟩

/-- Unrestricted syntactic completeness of component signature, occurrence
parity, and fixed first letter. -/
theorem derivesOfSameGuardedParityComponentSignature
    {left right : Word Nat}
    (same : SameGuardedParityComponentSignature left right) :
    Derives basis left right := by
  have countIff :=
    headCountOne_iff_of_sameSignature same
  by_cases leftHeadSimple :
      left.toList.count left.head = 1
  · have rightHeadSimple :
        right.toList.count right.head = 1 :=
      countIff.mp leftHeadSimple
    have tailsEmpty :
        left.tail = [] ↔ right.tail = [] := by
      constructor
      · exact tailNilOfSameSignature same rightHeadSimple
      · exact tailNilOfSameSignature same.symm leftHeadSimple
    cases left with
    | mk leftHead leftTail =>
        cases right with
        | mk rightHead rightTail =>
            simp only at same leftHeadSimple rightHeadSimple tailsEmpty
            have heads : leftHead = rightHead := same.first
            subst rightHead
            cases leftTail with
            | nil =>
                have rightEmpty : rightTail = [] :=
                  tailsEmpty.mp rfl
                subst rightTail
                exact Derives.refl _
            | cons leftSecond leftRest =>
                cases rightTail with
                | nil =>
                    have impossible :
                        leftSecond :: leftRest = [] :=
                      tailsEmpty.mpr rfl
                    contradiction
                | cons rightSecond rightRest =>
                    let leftSuffix : Word Nat :=
                      Word.mk leftSecond leftRest
                    let rightSuffix : Word Nat :=
                      Word.mk rightSecond rightRest
                    have leftHeadAbsent :
                        leftHead ∉ leftSuffix.toList := by
                      change leftHead ∉ leftSecond :: leftRest
                      exact headNotMemTailOfCountOne
                        (Word.mk leftHead (leftSecond :: leftRest))
                        leftHeadSimple
                    have rightHeadAbsent :
                        leftHead ∉ rightSuffix.toList := by
                      change leftHead ∉ rightSecond :: rightRest
                      exact headNotMemTailOfCountOne
                        (Word.mk leftHead (rightSecond :: rightRest))
                        rightHeadSimple
                    have whole :
                        SameGuardedParityComponentSignature
                          (Word.singleton leftHead ++ leftSuffix)
                          (Word.singleton leftHead ++ rightSuffix) := by
                      simpa [leftSuffix, rightSuffix, Word.singleton,
                        Word.append] using same
                    have suffixSame :=
                      suffixSameParityComponent
                        leftHead leftSuffix rightSuffix
                        leftHeadAbsent rightHeadAbsent whole
                    have suffixDerivation :=
                      SemigroupBasis.CoRoots.S5_442.derives_of_sameParityComponentSignature
                        suffixSame
                    have lifted :=
                      liftS5_442UnderPrefix suffixDerivation
                        (Word.singleton leftHead) Word.singleton
                    rw [bind_singleton, bind_singleton] at lifted
                    simpa [leftSuffix, rightSuffix, Word.singleton,
                      Word.append] using lifted
  · have rightHeadNotSimple :
        right.toList.count right.head ≠ 1 := by
      intro rightSimple
      exact leftHeadSimple (countIff.mpr rightSimple)
    have leftHeadInTail :
        left.head ∈ left.tail :=
      headMemTailOfCountNeOne left leftHeadSimple
    have rightHeadInTail :
        right.head ∈ right.tail :=
      headMemTailOfCountNeOne right rightHeadNotSimple
    have leftExpanded :=
      derivesAddInitialPair left leftHeadInTail
    have rightExpanded :=
      derivesAddInitialPair right rightHeadInTail
    have commonDerivation :=
      SemigroupBasis.CoRoots.S5_442.derives_of_sameParityComponentSignature
        same.parityComponent
    let guardPrefix :=
      Word.singleton left.head ++ Word.singleton left.head
    have lifted :=
      liftS5_442UnderPrefix
        commonDerivation guardPrefix Word.singleton
    rw [bind_singleton, bind_singleton] at lifted
    have guarded :
        Derives basis
          (guardPrefix ++ left) (guardPrefix ++ right) := by
      simpa [guardPrefix, same.first] using lifted
    have rightContracted :
        Derives basis (guardPrefix ++ right) right := by
      simpa [guardPrefix, same.first] using rightExpanded.symm
    exact leftExpanded.trans <|
      guarded.trans rightContracted

/-! ## The three factor intersections -/

private def toFinThree : Nat -> Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private theorem modelsS2_2 :
    Models SemigroupBasis.Generated.S2_2.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S2_2.table basis toFinThree (by decide)

private theorem modelsS5_798 :
    Models
      SemigroupBasis.Generated.Catalogue.S5_798.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.Catalogue.S5_798.table
    basis toFinThree (by decide)

private theorem modelsS2_4 :
    Models SemigroupBasis.Generated.S2_4.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S2_4.table basis toFinThree (by decide)

private theorem modelsS5_613 :
    Models
      SemigroupBasis.Generated.Catalogue.S5_613.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.Catalogue.S5_613.table
    basis toFinThree (by decide)

private theorem modelsS3_11 :
    Models SemigroupBasis.Generated.S3_11.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S3_11.table basis toFinThree (by decide)

private def oppositeFiniteTable (table : FiniteTable) : FiniteTable where
  order := table.order
  mul := fun left right => table.mul right left
  assoc := fun left middle right =>
    (table.assoc right middle left).symm

private theorem oppositeFiniteTable_semigroup (table : FiniteTable) :
    (oppositeFiniteTable table).semigroup =
      table.semigroup.opposite :=
  rfl

private theorem modelsS5_806Opposite :
    Models
      SemigroupBasis.Generated.Catalogue.S5_806.table.semigroup.opposite
      basis := by
  rw [← oppositeFiniteTable_semigroup]
  exact
    FiniteCertificate.checkModels_sound
      (oppositeFiniteTable
        SemigroupBasis.Generated.Catalogue.S5_806.table)
      basis toFinThree (by decide)

theorem sameSignatureOfS2_2S5_798Valid
    (identity : Identity Nat)
    (cyclicValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_2.table.semigroup)
    (s5Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_798.table.semigroup) :
    SameGuardedParityComponentSignature
      identity.lhs identity.rhs := by
  have componentFirst :=
    S5_790FamilyInvariant.S5_798.valid_sameSignature identity s5Valid
  have cyclicValid' :
      identity.SatisfiedBy cyclicTwo.semigroup := by
    simpa [SemigroupBasis.Generated.S2_2.table_eq_catalogue_model] using
      cyclicValid
  have parity :=
    S5_442Invariant.sameOccurrenceParity_of_cyclicTwo_equalEval
      identity.lhs identity.rhs cyclicValid'
  exact
    ⟨⟨componentFirst.components, parity⟩, componentFirst.first⟩

theorem sameSignatureOfS2_4S5_613Valid
    (identity : Identity Nat)
    (markerValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_4.table.semigroup)
    (s5Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_613.table.semigroup) :
    SameGuardedParityComponentSignature
      identity.lhs identity.rhs := by
  have parityComponent :=
    SemigroupBasis.CoRoots.S5_613.valid_sameParityComponentSignature
      identity s5Valid
  have markerValid' :
      identity.SatisfiedBy leftZeroTwo.semigroup := by
    simpa [SemigroupBasis.Generated.S2_4.table_eq_catalogue_model] using
      markerValid
  exact
    ⟨parityComponent,
      S5_790Invariant.leftZeroValid_head_eq identity markerValid'⟩

private def componentIntoS5_806Opposite
    (value : Fin 4) : Fin 5 :=
  if value = 0 then 0 else
    if value = 1 then 1 else
      if value = 2 then 4 else 3

private def componentEmbeddingS5_806Opposite :
    Embedding connectedComponentFour.semigroup
      SemigroupBasis.Generated.Catalogue.S5_806.table.semigroup.opposite where
  toFun := componentIntoS5_806Opposite
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

private def leftZeroIntoS5_806Opposite
    (value : Fin 2) : Fin 5 :=
  if value = 0 then 2 else 3

private def leftZeroEmbeddingS5_806Opposite :
    Embedding leftZeroTwo.semigroup
      SemigroupBasis.Generated.Catalogue.S5_806.table.semigroup.opposite where
  toFun := leftZeroIntoS5_806Opposite
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

theorem sameSignatureOfS3_11S5_806OppositeValid
    (identity : Identity Nat)
    (parityValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_11.table.semigroup)
    (s5Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_806.table.semigroup.opposite) :
    SameGuardedParityComponentSignature
      identity.lhs identity.rhs := by
  have componentValid :
      identity.SatisfiedBy connectedComponentFour.semigroup :=
    componentEmbeddingS5_806Opposite.pullback_identity identity s5Valid
  have markerValid :
      identity.SatisfiedBy leftZeroTwo.semigroup :=
    leftZeroEmbeddingS5_806Opposite.pullback_identity identity s5Valid
  have parityValid' :
      identity.SatisfiedBy parityZeroThree.semigroup := by
    simpa [SemigroupBasis.Generated.S3_11.table_eq_catalogue_model] using
      parityValid
  exact
    ⟨⟨S5_442Invariant.sameComponentSignature_of_connectedComponentFour_equalEval
          identity.lhs identity.rhs componentValid,
        S5_442Invariant.sameOccurrenceParity_of_parityZeroThree_equalEval
          identity.lhs identity.rhs parityValid'⟩,
      S5_790Invariant.leftZeroValid_head_eq identity markerValid⟩

theorem derivesOfS2_2S5_798Valid
    (identity : Identity Nat)
    (cyclicValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_2.table.semigroup)
    (s5Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_798.table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfSameGuardedParityComponentSignature
    (sameSignatureOfS2_2S5_798Valid identity cyclicValid s5Valid)

theorem derivesOfS2_4S5_613Valid
    (identity : Identity Nat)
    (markerValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_4.table.semigroup)
    (s5Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_613.table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfSameGuardedParityComponentSignature
    (sameSignatureOfS2_4S5_613Valid identity markerValid s5Valid)

theorem derivesOfS3_11S5_806OppositeValid
    (identity : Identity Nat)
    (parityValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_11.table.semigroup)
    (s5Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_806.table.semigroup.opposite) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfSameGuardedParityComponentSignature
    (sameSignatureOfS3_11S5_806OppositeValid
      identity parityValid s5Valid)

/-- Unrestricted basis for
`V(S2_2) intersection V(S5_798)`. -/
def intersectionBasisS2_2S5_798 :
    IntersectionBasis
      SemigroupBasis.Generated.S2_2.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_798.table.semigroup
      basis where
  leftModels := modelsS2_2
  rightModels := modelsS5_798
  complete := derivesOfS2_2S5_798Valid

/-- Unrestricted basis for
`V(S2_4) intersection V(S5_613)`. -/
def intersectionBasisS2_4S5_613 :
    IntersectionBasis
      SemigroupBasis.Generated.S2_4.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_613.table.semigroup
      basis where
  leftModels := modelsS2_4
  rightModels := modelsS5_613
  complete := derivesOfS2_4S5_613Valid

/-- Unrestricted basis for
`V(S3_11) intersection V(S5_806^op)`. -/
def intersectionBasisS3_11S5_806Opposite :
    IntersectionBasis
      SemigroupBasis.Generated.S3_11.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_806.table.semigroup.opposite
      basis where
  leftModels := modelsS3_11
  rightModels := modelsS5_806Opposite
  complete := derivesOfS3_11S5_806OppositeValid

end SemigroupBasis.CoRoots.Order6Level2TierBHashE2c5e460
