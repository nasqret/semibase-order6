import SemigroupBasis.Generated.Order6LeeA2LatticeNodes
import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.S5_441ExactCutAlignment
import SemigroupBasis.CoRoots.S5_806Canonical
import SemigroupBasis.TransferPower

/-!
# Shared normalizer for the Lee A2 lattice-node systems: trio pilot

The descriptor for `SystemHebf52dbf4ddc` (classes `S6_12952`, `S6_12954`,
`S6_13404`) is the direct connected-cut signature together with the word
head. This module proves the descriptor complete for every basis containing
the four scaffold laws and the guarded switch `a·x²y²x²y² = a·y²x²y²`, then
assembles the six unconditional endpoints.

The lemma layer is parametrized by a `SwitchLawEnvironment`, so systems 2-5
of the msg-0094 design can instantiate the same derivations with their own
law lists and add their coarsening steps on top.

Proof route (msg-0094 / msg-0295 design): equal direct signatures and equal
heads are upgraded per component to equal bidirectional signatures via the
switch law: a component with head `h` derives to the block
`X_h²Y²X_h²Y²`, one guarded-switch application lands on `Y²X_h²Y²` whose
head is the canonical letter of `Y`, and two components with equal datum
and equal (canonical) head are connected by the kernel-verified
`derivationalCompleteness`.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesNormal

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_868 (maximalFactorWord maximalFactorWord_toList
  maximalFactorWord_eq_of_toList)
open SemigroupBasis.CoRoots.S5_804 (ConnectedCutComponentSignature
  connectedCutComponentSignatureOfList connectedCutSignaturesList
  connectedCutSignaturesWord SameConnectedCutSignature componentFinal
  componentFinal_mem)

/-! ## The shared descriptor -/

/-- The exact class descriptor of the trio system: the direct connected-cut
signature together with the head letter. -/
def SameDirectSignatureAndHead (left right : Word Nat) : Prop :=
  SameConnectedCutSignature left right ∧ left.head = right.head

/-- The system-2 descriptor: the ordered component supports and unary-repeat
states, the final letter of the whole word, and the word head.  This is
exactly the S5_806 signature with the head marker adjoined. -/
def SameBaseChainFinalAndHead (left right : Word Nat) : Prop :=
  SemigroupBasis.CoRoots.S5_806.SameConnectedCutSignature left right ∧
    left.head = right.head

/-- The system-3 descriptor in the exact-cut-skeleton presentation.

The globally simple exact-cut separators are precisely the bare connected
components, hence the support-only gaps between them are the maximal runs of
collapsible components.  Equality of support and exact cuts therefore records
the coalesced component chain.  The two endpoint fields retain exactly the
word head and the final letter of the last coalesced block. -/
structure SameCoalescedChainFinalAndHead
    (left right : Word Nat) : Prop where
  support :
    SemigroupBasis.CoRoots.S5_441Invariant.SameSupport left right
  exactCuts :
    SemigroupBasis.CoRoots.S5_441Invariant.SameExactCutSignature left right
  final :
    SemigroupBasis.CoRoots.S5_806.componentFinal left.toList =
      SemigroupBasis.CoRoots.S5_806.componentFinal right.toList
  head : left.head = right.head

namespace SameCoalescedChainFinalAndHead

theorem refl (word : Word Nat) :
    SameCoalescedChainFinalAndHead word word :=
  ⟨SemigroupBasis.CoRoots.S5_441Invariant.SameSupport.refl word,
    SemigroupBasis.CoRoots.S5_441Invariant.SameExactCutSignature.refl word,
    rfl, rfl⟩

theorem symm {left right : Word Nat}
    (same : SameCoalescedChainFinalAndHead left right) :
    SameCoalescedChainFinalAndHead right left :=
  ⟨SemigroupBasis.CoRoots.S5_441Invariant.SameSupport.symm same.support,
    SemigroupBasis.CoRoots.S5_441Invariant.SameExactCutSignature.symm
      same.exactCuts,
    same.final.symm, same.head.symm⟩

theorem trans {left middle right : Word Nat}
    (first : SameCoalescedChainFinalAndHead left middle)
    (second : SameCoalescedChainFinalAndHead middle right) :
    SameCoalescedChainFinalAndHead left right :=
  ⟨SemigroupBasis.CoRoots.S5_441Invariant.SameSupport.trans
      first.support second.support,
    SemigroupBasis.CoRoots.S5_441Invariant.SameExactCutSignature.trans
      first.exactCuts second.exactCuts,
    first.final.trans second.final,
    first.head.trans second.head⟩

/-- The established support skeleton is the canonical coalesced-chain datum
carried by the system-3 descriptor. -/
theorem exactCutSupportSkeleton_eq {left right : Word Nat}
    (same : SameCoalescedChainFinalAndHead left right) :
    SemigroupBasis.CoRoots.S5_441.exactCutSupportSkeleton left.toList =
      SemigroupBasis.CoRoots.S5_441.exactCutSupportSkeleton right.toList :=
  SemigroupBasis.CoRoots.S5_441.exactCutSupportSkeleton_eq_of_sameSupport_sameExactCutSignature
    same.support same.exactCuts

/-- Assemble the system-3 descriptor from the `S4_69` separator detector
and the independently extracted endpoint coordinates. -/
theorem of_s4_69_valid_final_head
    (identity : Identity Nat)
    (separatorValid :
      identity.SatisfiedBy
        Generated.Catalogue.S4_69.table.semigroup)
    (final :
      SemigroupBasis.CoRoots.S5_806.componentFinal identity.lhs.toList =
        SemigroupBasis.CoRoots.S5_806.componentFinal identity.rhs.toList)
    (head : identity.lhs.head = identity.rhs.head) :
    SameCoalescedChainFinalAndHead identity.lhs identity.rhs :=
  ⟨SemigroupBasis.CoRoots.S5_441Invariant.sameSupport_of_s4_69_valid
      identity separatorValid,
    SemigroupBasis.CoRoots.S5_441Invariant.sameExactCutSignature_of_s4_69_valid
      identity separatorValid,
    final, head⟩

end SameCoalescedChainFinalAndHead

/-- Assemble the system-2 descriptor from its three independent semantic
coordinates: the ordered `S4_70` component signatures, the literal final
letter, and the literal head letter. -/
theorem sameBaseChainFinalAndHead_of_components_final_head
    {left right : Word Nat}
    (components :
      connectedComponentSignaturesWord left =
        connectedComponentSignaturesWord right)
    (final :
      SemigroupBasis.CoRoots.S5_806.componentFinal left.toList =
        SemigroupBasis.CoRoots.S5_806.componentFinal right.toList)
    (head : left.head = right.head) :
    SameBaseChainFinalAndHead left right := by
  refine ⟨?_, head⟩
  change
    SemigroupBasis.CoRoots.S5_806.ConnectedCutSignature.mk
        (connectedComponentSignaturesWord left)
        (SemigroupBasis.CoRoots.S5_806.componentFinal left.toList) =
      SemigroupBasis.CoRoots.S5_806.ConnectedCutSignature.mk
        (connectedComponentSignaturesWord right)
        (SemigroupBasis.CoRoots.S5_806.componentFinal right.toList)
  rw [components, final]

/-- The guarded head switch, stated exactly as the generated `law4` of
`SystemHebf52dbf4ddc` (and of the other lattice-node systems that carry
it): `a·x²y²x²y² = a·y²x²y²`. -/
def guardedSwitchLaw : Identity Nat :=
  ⟨⟨0, [1, 1, 2, 2, 1, 1, 2, 2]⟩, ⟨0, [2, 2, 1, 1, 2, 2]⟩⟩

/-- A law list rich enough for the shared normalizer: the four scaffold laws
plus the guarded switch. Systems 2-5 provide their own instances. -/
structure SwitchLawEnvironment (laws : List (Identity Nat)) : Prop where
  power : Order6LeeA2LatticeScaffold.powerContractionLaw ∈ laws
  sandwich : Order6LeeA2LatticeScaffold.sandwichContractionLaw ∈ laws
  graph : Order6LeeA2LatticeScaffold.graphSwitchLaw ∈ laws
  middle : Order6LeeA2LatticeScaffold.middleContractionLaw ∈ laws
  switch : guardedSwitchLaw ∈ laws

/-- The guarded interior-final erasure carried by system 2:
`a²b²a²b²h = a²b²a²h`. -/
def guardedFinalEraseLaw : Identity Nat :=
  ⟨⟨0, [0, 1, 1, 0, 0, 1, 1, 2]⟩,
    ⟨0, [0, 1, 1, 0, 0, 2]⟩⟩

/-- The system-2 normalizer needs the frozen switch environment and one
additional law, which erases the final marker of every non-last component. -/
structure FinalEraseLawEnvironment
    (laws : List (Identity Nat)) extends SwitchLawEnvironment laws : Prop where
  erase : guardedFinalEraseLaw ∈ laws

/-- The unguarded coalescing law carried by system 3:
`x²y²x²y² = x²y²`.  Used backwards, it turns two adjacent square blocks
into one connected square block. -/
def collapseLaw : Identity Nat :=
  ⟨⟨0, [0, 1, 1, 0, 0, 1, 1]⟩, ⟨0, [0, 1, 1]⟩⟩

/-- The system-3 normalizer consists of the complete system-2 environment
plus the one law which coalesces adjacent collapsible components. -/
structure CollapseLawEnvironment
    (laws : List (Identity Nat)) extends FinalEraseLawEnvironment laws : Prop
    where
  collapse : collapseLaw ∈ laws

/-! ## Transporting the kernel-verified sig-4 engine -/

theorem scaffoldDerives {laws : List (Identity Nat)}
    (env : SwitchLawEnvironment laws) :
    ∀ e ∈ Order6LeeA2LatticeScaffold.basis, Derives laws e.lhs e.rhs := by
  intro e member
  simp only [Order6LeeA2LatticeScaffold.basis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact Derives.fromBasis env.power
  · exact Derives.fromBasis env.sandwich
  · exact Derives.fromBasis env.graph
  · exact Derives.fromBasis env.middle

theorem derivesOfBidirectional {laws : List (Identity Nat)}
    (env : SwitchLawEnvironment laws) {left right : Word Nat}
    (same :
      Order6LeeA2LatticeScaffold.SameBidirectionalConnectedCutSignature
        left right) :
    Derives laws left right :=
  (Order6LeeA2LatticeScaffold.derivationalCompleteness same).transport
    (scaffoldDerives env)

private def instantiateSwitch (a X Y : Word Nat) : Nat → Word Nat
  | 0 => a
  | 1 => X
  | 2 => Y
  | n + 3 => Word.singleton (n + 3)

/-- Word-substituted guarded switch: `a·X²Y²X²Y² = a·Y²X²Y²`. -/
theorem derivesGuardedSwitch {laws : List (Identity Nat)}
    (env : SwitchLawEnvironment laws) (a X Y : Word Nat) :
    Derives laws
      (a ++ X ++ X ++ Y ++ Y ++ X ++ X ++ Y ++ Y)
      (a ++ Y ++ Y ++ X ++ X ++ Y ++ Y) := by
  have base : Derives laws guardedSwitchLaw.lhs guardedSwitchLaw.rhs :=
    Derives.fromBasis env.switch
  have substituted := Derives.subst base (instantiateSwitch a X Y)
  simpa [guardedSwitchLaw, instantiateSwitch, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private def instantiateFinalErase (X Y H : Word Nat) : Nat → Word Nat
  | 0 => X
  | 1 => Y
  | 2 => H
  | n + 3 => Word.singleton (n + 3)

/-- Word-substituted final erasure.  The final word is the nonempty guard
which places the erased component strictly before the end of the word. -/
theorem derivesFinalErase {laws : List (Identity Nat)}
    (env : FinalEraseLawEnvironment laws)
    (X Y H : Word Nat) :
    Derives laws
      (X ++ X ++ Y ++ Y ++ X ++ X ++ Y ++ Y ++ H)
      (X ++ X ++ Y ++ Y ++ X ++ X ++ H) := by
  have base :
      Derives laws guardedFinalEraseLaw.lhs guardedFinalEraseLaw.rhs :=
    Derives.fromBasis env.erase
  have substituted :=
    Derives.subst base (instantiateFinalErase X Y H)
  simpa [guardedFinalEraseLaw, instantiateFinalErase, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Word-substituted guarded final erasure in an arbitrary left context. -/
theorem derivesGuardedFinalErase {laws : List (Identity Nat)}
    (env : FinalEraseLawEnvironment laws)
    (pre X Y H : Word Nat) :
    Derives laws
      (pre ++ X ++ X ++ Y ++ Y ++ X ++ X ++ Y ++ Y ++ H)
      (pre ++ X ++ X ++ Y ++ Y ++ X ++ X ++ H) := by
  have prefixed :=
    Derives.prepend pre (derivesFinalErase env X Y H)
  simpa [Word.append_assoc] using prefixed

private def instantiateCollapse (X Y : Word Nat) : Nat → Word Nat
  | 0 => X
  | 1 => Y
  | n + 2 => Word.singleton (n + 2)

/-- Word-substituted coalescing:
`X²Y²X²Y² = X²Y²`. -/
theorem derivesCollapse {laws : List (Identity Nat)}
    (env : CollapseLawEnvironment laws) (X Y : Word Nat) :
    Derives laws
      (X ++ X ++ Y ++ Y ++ X ++ X ++ Y ++ Y)
      (X ++ X ++ Y ++ Y) := by
  have base : Derives laws collapseLaw.lhs collapseLaw.rhs :=
    Derives.fromBasis env.collapse
  have substituted := Derives.subst base (instantiateCollapse X Y)
  simpa [collapseLaw, instantiateCollapse, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Coalescing under an arbitrary nonempty left context. -/
theorem derivesGuardedCollapse {laws : List (Identity Nat)}
    (env : CollapseLawEnvironment laws) (pre X Y : Word Nat) :
    Derives laws
      (pre ++ X ++ X ++ Y ++ Y ++ X ++ X ++ Y ++ Y)
      (pre ++ X ++ X ++ Y ++ Y) := by
  have prefixed := Derives.prepend pre (derivesCollapse env X Y)
  simpa [Word.append_assoc] using prefixed

/-- Coalescing before an arbitrary nonempty right context. -/
theorem derivesCollapseBeforeSuffix {laws : List (Identity Nat)}
    (env : CollapseLawEnvironment laws) (X Y suffix : Word Nat) :
    Derives laws
      (X ++ X ++ Y ++ Y ++ X ++ X ++ Y ++ Y ++ suffix)
      (X ++ X ++ Y ++ Y ++ suffix) := by
  have suffixed :=
    Derives.appendRight (derivesCollapse env X Y) suffix
  simpa [Word.append_assoc] using suffixed

/-- Coalescing in a two-sided nonempty context. -/
theorem derivesCollapseInContext {laws : List (Identity Nat)}
    (env : CollapseLawEnvironment laws)
    (pre X Y suffix : Word Nat) :
    Derives laws
      (pre ++ X ++ X ++ Y ++ Y ++ X ++ X ++ Y ++ Y ++ suffix)
      (pre ++ X ++ X ++ Y ++ Y ++ suffix) := by
  have contextual :=
    Derives.appendRight (derivesGuardedCollapse env pre X Y) suffix
  simpa [Word.append_assoc] using contextual

/-- The reverse use of the collapse law merges two adjacent squares into
one larger square. -/
theorem derivesMergeSquares {laws : List (Identity Nat)}
    (env : CollapseLawEnvironment laws) (X Y : Word Nat) :
    Derives laws
      (X ++ X ++ Y ++ Y)
      ((X ++ X ++ Y ++ Y) ++ (X ++ X ++ Y ++ Y)) := by
  simpa [Word.append_assoc] using (derivesCollapse env X Y).symm

/-- Contextual square merging, the direction used while scanning a maximal
run of collapsible connected components. -/
theorem derivesMergeSquaresInContext {laws : List (Identity Nat)}
    (env : CollapseLawEnvironment laws)
    (pre X Y suffix : Word Nat) :
    Derives laws
      (pre ++ X ++ X ++ Y ++ Y ++ suffix)
      (pre ++ X ++ X ++ Y ++ Y ++ X ++ X ++ Y ++ Y ++ suffix) :=
  (derivesCollapseInContext env pre X Y suffix).symm

/-! ## Decomposition glue -/

private theorem decomposeList_of_supportConnected
    {component : List Nat} (nonempty : component ≠ [])
    (connected : ConnectedComponentSupportConnected component) :
    connectedComponentDecomposeList component = [component] := by
  rcases shape :
      connectedComponentDecomposeList component with _ | ⟨first, rest⟩
  · exact absurd shape (connectedComponentDecomposeList_nonempty nonempty)
  · rcases rest with _ | ⟨second, more⟩
    · have flattened := connectedComponentDecomposeList_flatten component
      rw [shape] at flattened
      simp only [List.flatten_cons, List.flatten_nil,
        List.append_nil] at flattened
      rw [flattened]
    · have flattened := connectedComponentDecomposeList_flatten component
      rw [shape] at flattened
      simp only [List.flatten_cons] at flattened
      have firstNonempty : first ≠ [] :=
        connectedComponentDecomposeList_nonempty_components component first
          (by rw [shape]; simp)
      have secondNonempty : second ≠ [] :=
        connectedComponentDecomposeList_nonempty_components component second
          (by rw [shape]; simp)
      have tailNonempty : second ++ more.flatten ≠ [] := by
        intro tailEmpty
        exact secondNonempty (List.append_eq_nil_iff.mp tailEmpty).1
      have intersect :=
        connected first (second ++ more.flatten) flattened.symm
          firstNonempty tailNonempty
      rcases intersect with ⟨letter, firstMember, tailMember⟩
      have pairwise :=
        connectedComponentDecomposeList_pairwiseDisjoint component
      rw [shape] at pairwise
      rcases List.mem_append.mp tailMember with secondMember | moreMember
      · exact ((List.pairwise_cons.mp pairwise).1 second (by simp)
          letter firstMember secondMember).elim
      · rcases List.mem_flatten.mp moreMember with
          ⟨block, blockMember, letterMember⟩
        exact ((List.pairwise_cons.mp pairwise).1 block
          (by simp [blockMember]) letter firstMember letterMember).elim

private theorem supportConnected_reverse
    {component : List Nat}
    (connected : ConnectedComponentSupportConnected component) :
    ConnectedComponentSupportConnected component.reverse := by
  intro left right shape leftNonempty rightNonempty
  have originalShape : component = right.reverse ++ left.reverse := by
    have reversed := congrArg List.reverse shape
    simpa [List.reverse_append] using reversed
  have intersect :=
    connected right.reverse left.reverse originalShape
      (by simpa using rightNonempty) (by simpa using leftNonempty)
  rcases intersect with ⟨letter, rightMember, leftMember⟩
  exact ⟨letter, by simpa using leftMember, by simpa using rightMember⟩

private theorem sorted_nodup_ext
    {left right : List Nat}
    (leftSorted : left.Pairwise (· ≤ ·))
    (rightSorted : right.Pairwise (· ≤ ·))
    (leftNodup : left.Nodup) (rightNodup : right.Nodup)
    (sameMembers : ∀ letter, letter ∈ left ↔ letter ∈ right) :
    left = right := by
  have permutation : left.Perm right := by
    rw [List.perm_iff_count]
    intro letter
    rw [leftNodup.count, rightNodup.count]
    simp only [sameMembers letter]
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ leftLe rightLe => Nat.le_antisymm leftLe rightLe)
    leftSorted rightSorted permutation

private theorem sortedSupport_reverse (component : List Nat) :
    connectedComponentSortedSupport component.reverse =
      connectedComponentSortedSupport component := by
  apply sorted_nodup_ext
    (connectedComponentSortedSupport_sorted _)
    (connectedComponentSortedSupport_sorted _)
    (connectedComponentSortedSupport_nodup _)
    (connectedComponentSortedSupport_nodup _)
  intro letter
  rw [connectedComponentSortedSupport_mem_iff,
    connectedComponentSortedSupport_mem_iff, List.mem_reverse]

private theorem signatureOfList_reverse (component : List Nat) :
    connectedComponentSignatureOfList component.reverse =
      connectedComponentSignatureOfList component := by
  simp only [connectedComponentSignatureOfList, sortedSupport_reverse,
    List.length_reverse]

private theorem getLastD_append
    (left right : List Nat) (fallback : Nat) :
    (left ++ right).getLastD fallback =
      right.getLastD (left.getLastD fallback) := by
  induction left generalizing fallback with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.cons_append, List.getLastD_cons]
      exact induction head

private theorem componentFinal_append_singleton
    (letters : List Nat) (letter : Nat) :
    componentFinal (letters ++ [letter]) = letter := by
  cases letters with
  | nil => rfl
  | cons head tail =>
      simp only [List.cons_append, componentFinal]
      rw [getLastD_append]
      rfl

private theorem componentFinal_append_of_right_nonempty
    (left right : List Nat) (rightNonempty : right ≠ []) :
    componentFinal (left ++ right) = componentFinal right := by
  obtain ⟨rightHead, rightTail, rfl⟩ :=
    List.exists_cons_of_ne_nil rightNonempty
  cases left with
  | nil => rfl
  | cons leftHead leftTail =>
      simp only [List.cons_append, componentFinal]
      rw [getLastD_append]
      simpa only [List.getLastD_cons]

private theorem componentFinal_reverse (head : Nat) (tail : List Nat) :
    componentFinal (head :: tail).reverse = head := by
  rw [List.reverse_cons]
  exact componentFinal_append_singleton tail.reverse head

private theorem cutSignaturesList_of_supportConnected
    {component : List Nat} (nonempty : component ≠ [])
    (connected : ConnectedComponentSupportConnected component) :
    connectedCutSignaturesList component =
      [connectedCutComponentSignatureOfList component] := by
  rw [connectedCutSignaturesList,
    decomposeList_of_supportConnected nonempty connected]
  rfl

/-! ## The per-component connector -/

/-- Two support-connected components with the same cut signature and the
same head have the same bidirectional signature as standalone words, so the
kernel-verified engine connects them. -/
theorem derivesComponentWords {laws : List (Identity Nat)}
    (env : SwitchLawEnvironment laws)
    {chead dhead : Nat} {ctail dtail : List Nat}
    (cConnected : ConnectedComponentSupportConnected (chead :: ctail))
    (dConnected : ConnectedComponentSupportConnected (dhead :: dtail))
    (signature :
      connectedCutComponentSignatureOfList (chead :: ctail) =
        connectedCutComponentSignatureOfList (dhead :: dtail))
    (heads : chead = dhead) :
    Derives laws
      (maximalFactorWord (chead :: ctail))
      (maximalFactorWord (dhead :: dtail)) := by
  apply derivesOfBidirectional env
  constructor
  · show connectedCutSignaturesWord _ = connectedCutSignaturesWord _
    rw [connectedCutSignaturesWord, connectedCutSignaturesWord,
      maximalFactorWord_toList (by simp), maximalFactorWord_toList (by simp),
      cutSignaturesList_of_supportConnected (by simp) cConnected,
      cutSignaturesList_of_supportConnected (by simp) dConnected,
      signature]
  · show connectedCutSignaturesWord _ = connectedCutSignaturesWord _
    have baseEq :
        connectedComponentSignatureOfList (chead :: ctail) =
          connectedComponentSignatureOfList (dhead :: dtail) :=
      congrArg ConnectedCutComponentSignature.base signature
    rw [connectedCutSignaturesWord, connectedCutSignaturesWord,
      Word.toList_reverse, Word.toList_reverse,
      maximalFactorWord_toList (by simp), maximalFactorWord_toList (by simp),
      cutSignaturesList_of_supportConnected (by simp)
        (supportConnected_reverse cConnected),
      cutSignaturesList_of_supportConnected (by simp)
        (supportConnected_reverse dConnected)]
    congr 1
    rw [connectedCutComponentSignatureOfList,
      connectedCutComponentSignatureOfList,
      signatureOfList_reverse, signatureOfList_reverse,
      componentFinal_reverse, componentFinal_reverse, baseEq, heads]

/-! ## Switch blocks -/

section SwitchBlocks

variable {supportOne supportTwo : Nat} {supportRest : List Nat}

private def blockX (h : Nat) (S : List Nat) : List Nat :=
  h :: S.erase h

private def blockY (f : Nat) (S : List Nat) : List Nat :=
  S.erase f ++ [f]

private theorem blockX_nonempty (h : Nat) (S : List Nat) :
    blockX h S ≠ [] := by simp [blockX]

private theorem blockY_nonempty (f : Nat) (S : List Nat) :
    blockY f S ≠ [] := by simp [blockY]

private theorem blockX_subset {h : Nat} {S : List Nat} (hMem : h ∈ S) :
    ∀ x ∈ blockX h S, x ∈ S := by
  intro x member
  rcases List.mem_cons.mp member with rfl | erased
  · exact hMem
  · exact List.mem_of_mem_erase erased

private theorem blockY_subset {f : Nat} {S : List Nat} (fMem : f ∈ S) :
    ∀ x ∈ blockY f S, x ∈ S := by
  intro x member
  rcases List.mem_append.mp member with erased | last
  · exact List.mem_of_mem_erase erased
  · simp only [List.mem_singleton] at last
    exact last ▸ fMem

private theorem blockX_full {h : Nat} {S : List Nat} :
    ∀ s ∈ S, s ∈ blockX h S := by
  intro s member
  by_cases equal : s = h
  · subst s
    simp [blockX]
  · exact List.mem_cons_of_mem h (List.mem_erase_of_ne equal |>.mpr member)

private theorem blockY_full {f : Nat} {S : List Nat} :
    ∀ s ∈ S, s ∈ blockY f S := by
  intro s member
  by_cases equal : s = f
  · exact List.mem_append_right _ (by simp [equal])
  · exact List.mem_append_left _ (List.mem_erase_of_ne equal |>.mpr member)

private theorem suffix_of_suffix_length_le
    {short long whole : List Nat}
    (shortSuffix : short <:+ whole) (longSuffix : long <:+ whole)
    (lengthLe : short.length ≤ long.length) :
    short <:+ long := by
  rw [← List.reverse_prefix] at shortSuffix longSuffix ⊢
  exact List.prefix_of_prefix_length_le shortSuffix longSuffix
    (by simpa using lengthLe)

/-- A word all of whose letters lie in `S`, with a full-support prefix and a
full-support suffix, is support-connected. -/
private theorem supportConnected_of_full_ends
    {S l xpre ysuf : List Nat}
    (prefixShape : xpre <+: l) (suffixShape : ysuf <:+ l)
    (lengthBound : xpre.length + ysuf.length ≤ l.length)
    (xpreFull : ∀ s ∈ S, s ∈ xpre) (ysufFull : ∀ s ∈ S, s ∈ ysuf)
    (subset : ∀ x ∈ l, x ∈ S) :
    ConnectedComponentSupportConnected l := by
  intro left right shape leftNonempty rightNonempty
  by_cases lengthCase : ysuf.length ≤ right.length
  · have rightSuffix : right <:+ l := ⟨left, shape.symm⟩
    have inner : ysuf <:+ right :=
      suffix_of_suffix_length_le suffixShape rightSuffix lengthCase
    rcases List.exists_mem_of_ne_nil left leftNonempty with ⟨x, xLeft⟩
    have xWhole : x ∈ l := by
      rw [shape]; exact List.mem_append_left right xLeft
    exact ⟨x, xLeft, inner.subset (ysufFull x (subset x xWhole))⟩
  · have leftPrefix : left <+: l := ⟨right, shape.symm⟩
    have lengths : left.length + right.length = l.length := by
      rw [shape, List.length_append]
    have prefixLe : xpre.length ≤ left.length := by omega
    have inner : xpre <+: left :=
      List.prefix_of_prefix_length_le prefixShape leftPrefix prefixLe
    rcases List.exists_mem_of_ne_nil right rightNonempty with ⟨x, xRight⟩
    have xWhole : x ∈ l := by
      rw [shape]; exact List.mem_append_right left xRight
    exact ⟨x, inner.subset (xpreFull x (subset x xWhole)), xRight⟩

/-- The eight-factor switch block `X X Y Y X X Y Y`. -/
private def longBlock (h f : Nat) (S : List Nat) : List Nat :=
  blockX h S ++ (blockX h S ++ (blockY f S ++ (blockY f S ++
    (blockX h S ++ (blockX h S ++ (blockY f S ++ blockY f S))))))

/-- The six-factor switch block `Y Y X X Y Y`. -/
private def shortBlock (h f : Nat) (S : List Nat) : List Nat :=
  blockY f S ++ (blockY f S ++ (blockX h S ++ (blockX h S ++
    (blockY f S ++ blockY f S))))

/-- The six-factor right side `X X Y Y X X` of the final-erasure law. -/
private def erasedBlock (h f : Nat) (S : List Nat) : List Nat :=
  blockX h S ++ (blockX h S ++ (blockY f S ++ (blockY f S ++
    (blockX h S ++ blockX h S))))

private theorem longBlock_subset {h f : Nat} {S : List Nat}
    (hMem : h ∈ S) (fMem : f ∈ S) :
    ∀ x ∈ longBlock h f S, x ∈ S := by
  intro x member
  simp only [longBlock, List.mem_append] at member
  rcases member with m | m | m | m | m | m | m | m
  all_goals
    first
      | exact blockX_subset hMem x m
      | exact blockY_subset fMem x m

private theorem shortBlock_subset {h f : Nat} {S : List Nat}
    (hMem : h ∈ S) (fMem : f ∈ S) :
    ∀ x ∈ shortBlock h f S, x ∈ S := by
  intro x member
  simp only [shortBlock, List.mem_append] at member
  rcases member with m | m | m | m | m | m
  all_goals
    first
      | exact blockX_subset hMem x m
      | exact blockY_subset fMem x m

private theorem erasedBlock_subset {h f : Nat} {S : List Nat}
    (hMem : h ∈ S) (fMem : f ∈ S) :
    ∀ x ∈ erasedBlock h f S, x ∈ S := by
  intro x member
  simp only [erasedBlock, List.mem_append] at member
  rcases member with m | m | m | m | m | m
  all_goals
    first
      | exact blockX_subset hMem x m
      | exact blockY_subset fMem x m

private theorem longBlock_connected {h f : Nat} {S : List Nat}
    (hMem : h ∈ S) (fMem : f ∈ S) :
    ConnectedComponentSupportConnected (longBlock h f S) := by
  apply supportConnected_of_full_ends
    (xpre := blockX h S) (ysuf := blockY f S) (S := S)
  · exact ⟨_, rfl⟩
  · refine ⟨blockX h S ++ (blockX h S ++ (blockY f S ++ (blockY f S ++
      (blockX h S ++ (blockX h S ++ blockY f S))))), ?_⟩
    simp [longBlock, List.append_assoc]
  · simp only [longBlock, List.length_append]
    omega
  · exact blockX_full
  · exact blockY_full
  · exact longBlock_subset hMem fMem

private theorem shortBlock_connected {h f : Nat} {S : List Nat}
    (hMem : h ∈ S) (fMem : f ∈ S) :
    ConnectedComponentSupportConnected (shortBlock h f S) := by
  apply supportConnected_of_full_ends
    (xpre := blockY f S) (ysuf := blockY f S) (S := S)
  · exact ⟨_, rfl⟩
  · refine ⟨blockY f S ++ (blockY f S ++ (blockX h S ++ (blockX h S ++
      blockY f S))), ?_⟩
    simp [shortBlock, List.append_assoc]
  · simp only [shortBlock, List.length_append]
    omega
  · exact blockY_full
  · exact blockY_full
  · exact shortBlock_subset hMem fMem

private theorem erasedBlock_connected {h f : Nat} {S : List Nat}
    (hMem : h ∈ S) (fMem : f ∈ S) :
    ConnectedComponentSupportConnected (erasedBlock h f S) := by
  apply supportConnected_of_full_ends
    (xpre := blockX h S) (ysuf := blockX h S) (S := S)
  · exact ⟨_, rfl⟩
  · refine ⟨blockX h S ++ (blockX h S ++ (blockY f S ++
      (blockY f S ++ blockX h S))), ?_⟩
    simp [erasedBlock, List.append_assoc]
  · simp only [erasedBlock, List.length_append]
    omega
  · exact blockX_full
  · exact blockX_full
  · exact erasedBlock_subset hMem fMem

private theorem block_sortedSupport {h f : Nat} {S : List Nat}
    (sorted : S.Pairwise (· ≤ ·)) (nodup : S.Nodup)
    (hMem : h ∈ S) (fMem : f ∈ S)
    {l : List Nat}
    (subset : ∀ x ∈ l, x ∈ S)
    (full : ∀ s ∈ S, s ∈ l) :
    connectedComponentSortedSupport l = S := by
  apply sorted_nodup_ext
    (connectedComponentSortedSupport_sorted _) sorted
    (connectedComponentSortedSupport_nodup _) nodup
  intro letter
  rw [connectedComponentSortedSupport_mem_iff]
  exact ⟨fun m => subset letter m, fun m => full letter m⟩

private theorem longBlock_final {h f : Nat} {S : List Nat} :
    componentFinal (longBlock h f S) = f := by
  have shape : longBlock h f S =
      (blockX h S ++ (blockX h S ++ (blockY f S ++ (blockY f S ++
        (blockX h S ++ (blockX h S ++ (blockY f S ++ S.erase f))))))) ++
        [f] := by
    simp [longBlock, blockY, List.append_assoc]
  rw [shape]
  exact componentFinal_append_singleton _ f

private theorem shortBlock_final {h f : Nat} {S : List Nat} :
    componentFinal (shortBlock h f S) = f := by
  have shape : shortBlock h f S =
      (blockY f S ++ (blockY f S ++ (blockX h S ++ (blockX h S ++
        (blockY f S ++ S.erase f))))) ++ [f] := by
    simp [shortBlock, blockY, List.append_assoc]
  rw [shape]
  exact componentFinal_append_singleton _ f

private theorem erasedBlock_final_eq
    {h f g : Nat} {S : List Nat} :
    componentFinal (erasedBlock h f S) =
      componentFinal (erasedBlock h g S) := by
  have shape : ∀ marker : Nat,
      erasedBlock h marker S =
        (blockX h S ++ (blockX h S ++ (blockY marker S ++
          (blockY marker S ++ blockX h S)))) ++ blockX h S := by
    intro marker
    simp [erasedBlock, List.append_assoc]
  rw [shape f, shape g,
    componentFinal_append_of_right_nonempty _ _
      (blockX_nonempty h S),
    componentFinal_append_of_right_nonempty _ _
      (blockX_nonempty h S)]

private theorem multi_cutSignature
    {S : List Nat} {one two : Nat} {rest : List Nat}
    (shape : S = one :: two :: rest)
    {l : List Nat}
    (supportEq : connectedComponentSortedSupport l = S)
    {f : Nat} (finalEq : componentFinal l = f) :
    connectedCutComponentSignatureOfList l =
      ⟨⟨S, false⟩, f⟩ := by
  rw [connectedCutComponentSignatureOfList, finalEq]
  congr 1
  rw [connectedComponentSignatureOfList, supportEq, shape]

private theorem maximalFactorWord_longBlock (h f : Nat) (S : List Nat) :
    maximalFactorWord (longBlock h f S) =
      maximalFactorWord (blockX h S) ++
      maximalFactorWord (blockX h S) ++
      maximalFactorWord (blockY f S) ++
      maximalFactorWord (blockY f S) ++
      maximalFactorWord (blockX h S) ++
      maximalFactorWord (blockX h S) ++
      maximalFactorWord (blockY f S) ++
      maximalFactorWord (blockY f S) := by
  apply Word.toList_injective
  rw [maximalFactorWord_toList (by
    simp [longBlock, blockX])]
  simp only [Word.toList_append,
    maximalFactorWord_toList (blockX_nonempty h S),
    maximalFactorWord_toList (blockY_nonempty f S)]
  simp [longBlock, List.append_assoc]

private theorem maximalFactorWord_erasedBlock
    (h f : Nat) (S : List Nat) :
    maximalFactorWord (erasedBlock h f S) =
      maximalFactorWord (blockX h S) ++
      maximalFactorWord (blockX h S) ++
      maximalFactorWord (blockY f S) ++
      maximalFactorWord (blockY f S) ++
      maximalFactorWord (blockX h S) ++
      maximalFactorWord (blockX h S) := by
  apply Word.toList_injective
  rw [maximalFactorWord_toList (by
    simp [erasedBlock, blockX])]
  simp only [Word.toList_append,
    maximalFactorWord_toList (blockX_nonempty h S),
    maximalFactorWord_toList (blockY_nonempty f S)]
  simp [erasedBlock, List.append_assoc]

end SwitchBlocks

/-! ## The guarded component switch -/

/-- Behind any guard word, two support-connected components with the same
cut signature derive to each other even when their heads differ. -/
theorem derivesComponentSwitchWords {laws : List (Identity Nat)}
    (env : SwitchLawEnvironment laws) (guard : Word Nat)
    {chead dhead : Nat} {ctail dtail : List Nat}
    (cConnected : ConnectedComponentSupportConnected (chead :: ctail))
    (dConnected : ConnectedComponentSupportConnected (dhead :: dtail))
    (signature :
      connectedCutComponentSignatureOfList (chead :: ctail) =
        connectedCutComponentSignatureOfList (dhead :: dtail)) :
    Derives laws
      (guard ++ maximalFactorWord (chead :: ctail))
      (guard ++ maximalFactorWord (dhead :: dtail)) := by
  have baseEq :
      connectedComponentSignatureOfList (chead :: ctail) =
        connectedComponentSignatureOfList (dhead :: dtail) :=
    congrArg ConnectedCutComponentSignature.base signature
  have supportEq :
      connectedComponentSortedSupport (chead :: ctail) =
        connectedComponentSortedSupport (dhead :: dtail) := by
    have projected := congrArg connectedComponentSignature.support baseEq
    rwa [connectedComponentSignatureOfList_support,
      connectedComponentSignatureOfList_support] at projected
  have cheadSupport :
      chead ∈ connectedComponentSortedSupport (chead :: ctail) :=
    (connectedComponentSortedSupport_mem_iff chead _).mpr (by simp)
  have dheadSupport :
      dhead ∈ connectedComponentSortedSupport (dhead :: dtail) :=
    (connectedComponentSortedSupport_mem_iff dhead _).mpr (by simp)
  rcases supportShape :
      connectedComponentSortedSupport (chead :: ctail) with
    _ | ⟨one, rest⟩
  · exact absurd supportShape
      (connectedComponentSortedSupport_nonempty (by simp))
  rcases rest with _ | ⟨two, rest⟩
  · -- unary support: both heads equal the unique support letter
    have cheadEq : chead = one := by
      rw [supportShape] at cheadSupport
      simpa using cheadSupport
    have dheadEq : dhead = one := by
      rw [← supportEq, supportShape] at dheadSupport
      simpa using dheadSupport
    exact Derives.prepend guard
      (derivesComponentWords env cConnected dConnected signature
        (cheadEq.trans dheadEq.symm))
  · -- multi-letter support: switch through the guarded blocks
    let S : List Nat := one :: two :: rest
    have SDef : S = one :: two :: rest := rfl
    have sorted : S.Pairwise (· ≤ ·) := by
      have sortedSupport :=
        connectedComponentSortedSupport_sorted (chead :: ctail)
      rw [supportShape] at sortedSupport
      exact sortedSupport
    have nodup : S.Nodup := by
      have nodupSupport :=
        connectedComponentSortedSupport_nodup (chead :: ctail)
      rw [supportShape] at nodupSupport
      exact nodupSupport
    have cheadMem : chead ∈ S := by
      change chead ∈ one :: two :: rest
      rw [← supportShape]
      exact cheadSupport
    have dheadMem : dhead ∈ S := by
      rw [← supportEq, supportShape] at dheadSupport
      exact dheadSupport
    let f : Nat := componentFinal (chead :: ctail)
    have fDef : f = componentFinal (chead :: ctail) := rfl
    have fMem : f ∈ S := by
      have inList := SemigroupBasis.CoRoots.S5_804.componentFinal_mem chead ctail
      have inSupport :
          f ∈ connectedComponentSortedSupport (chead :: ctail) :=
        (connectedComponentSortedSupport_mem_iff f _).mpr inList
      rw [supportShape] at inSupport
      exact inSupport
  -- signatures of the four blocks
    have cSignature :
        connectedCutComponentSignatureOfList (chead :: ctail) =
          ⟨⟨S, false⟩, f⟩ :=
      multi_cutSignature SDef (supportShape) rfl
    have dSignature :
        connectedCutComponentSignatureOfList (dhead :: dtail) =
          ⟨⟨S, false⟩, f⟩ := signature.symm.trans cSignature
    have longCSupport :
        connectedComponentSortedSupport (longBlock chead f S) = S :=
      block_sortedSupport sorted nodup cheadMem fMem
        (longBlock_subset cheadMem fMem)
        (fun s sMem => by
          simp only [longBlock, List.mem_append]
          exact Or.inl (blockX_full s sMem))
    have longDSupport :
        connectedComponentSortedSupport (longBlock dhead f S) = S :=
      block_sortedSupport sorted nodup dheadMem fMem
        (longBlock_subset dheadMem fMem)
        (fun s sMem => by
          simp only [longBlock, List.mem_append]
          exact Or.inl (blockX_full s sMem))
    have shortCSupport :
        connectedComponentSortedSupport (shortBlock chead f S) = S :=
      block_sortedSupport sorted nodup cheadMem fMem
        (shortBlock_subset cheadMem fMem)
        (fun s sMem => by
          simp only [shortBlock, List.mem_append]
          exact Or.inl (blockY_full s sMem))
    have shortDSupport :
        connectedComponentSortedSupport (shortBlock dhead f S) = S :=
      block_sortedSupport sorted nodup dheadMem fMem
        (shortBlock_subset dheadMem fMem)
        (fun s sMem => by
          simp only [shortBlock, List.mem_append]
          exact Or.inl (blockY_full s sMem))
    have longCSig :
        connectedCutComponentSignatureOfList (longBlock chead f S) =
          ⟨⟨S, false⟩, f⟩ :=
      multi_cutSignature SDef longCSupport longBlock_final
    have longDSig :
        connectedCutComponentSignatureOfList (longBlock dhead f S) =
          ⟨⟨S, false⟩, f⟩ :=
      multi_cutSignature SDef longDSupport longBlock_final
    have shortCSig :
        connectedCutComponentSignatureOfList (shortBlock chead f S) =
          ⟨⟨S, false⟩, f⟩ :=
      multi_cutSignature SDef shortCSupport shortBlock_final
    have shortDSig :
        connectedCutComponentSignatureOfList (shortBlock dhead f S) =
          ⟨⟨S, false⟩, f⟩ :=
      multi_cutSignature SDef shortDSupport shortBlock_final
  -- cons shapes of the blocks
    have longCCons : longBlock chead f S =
        chead :: (S.erase chead ++ (blockX chead S ++ (blockY f S ++
          (blockY f S ++ (blockX chead S ++ (blockX chead S ++
            (blockY f S ++ blockY f S))))))) := by
      simp [longBlock, blockX, List.cons_append]
    have longDCons : longBlock dhead f S =
        dhead :: (S.erase dhead ++ (blockX dhead S ++ (blockY f S ++
          (blockY f S ++ (blockX dhead S ++ (blockX dhead S ++
            (blockY f S ++ blockY f S))))))) := by
      simp [longBlock, blockX, List.cons_append]
  -- Y in cons shape for the short blocks
    have eraseNonempty : S.erase f ≠ [] := by
      intro eraseEmpty
      have twoLetters : (2 : Nat) ≤ S.length := by
        rw [SDef]; simp
      have eraseLength := List.length_erase_of_mem fMem
      rw [eraseEmpty] at eraseLength
      simp at eraseLength
      omega
    rcases eraseShape : S.erase f with _ | ⟨y0, yrest⟩
    · exact absurd eraseShape eraseNonempty
    have shortCCons : shortBlock chead f S =
        y0 :: (yrest ++ ([f] ++ (blockY f S ++ (blockX chead S ++
          (blockX chead S ++ (blockY f S ++ blockY f S)))))) := by
      simp [shortBlock, blockY, eraseShape, List.cons_append,
        List.append_assoc]
    have shortDCons : shortBlock dhead f S =
        y0 :: (yrest ++ ([f] ++ (blockY f S ++ (blockX dhead S ++
          (blockX dhead S ++ (blockY f S ++ blockY f S)))))) := by
      simp [shortBlock, blockY, eraseShape, List.cons_append,
        List.append_assoc]
  -- five hops
    have hopOne : Derives laws
        (guard ++ maximalFactorWord (chead :: ctail))
        (guard ++ maximalFactorWord (longBlock chead f S)) := by
      apply Derives.prepend guard
      rw [longCCons]
      exact derivesComponentWords env cConnected
        (longCCons ▸ longBlock_connected cheadMem fMem)
        (by rw [← longCCons, longCSig, cSignature]) rfl
    have hopFive : Derives laws
        (guard ++ maximalFactorWord (longBlock dhead f S))
        (guard ++ maximalFactorWord (dhead :: dtail)) := by
      apply Derives.prepend guard
      rw [longDCons]
      exact derivesComponentWords env
        (longDCons ▸ longBlock_connected dheadMem fMem) dConnected
        (by rw [← longDCons, longDSig, dSignature]) rfl
    have hopThree : Derives laws
        (guard ++ maximalFactorWord (shortBlock chead f S))
        (guard ++ maximalFactorWord (shortBlock dhead f S)) := by
      apply Derives.prepend guard
      rw [shortCCons, shortDCons]
      exact derivesComponentWords env
        (shortCCons ▸ shortBlock_connected cheadMem fMem)
        (shortDCons ▸ shortBlock_connected dheadMem fMem)
        (by rw [← shortCCons, ← shortDCons, shortCSig, shortDSig]) rfl
  -- block words split into X and Y factors
    have wordSplitLong : ∀ h : Nat,
        maximalFactorWord (longBlock h f S) =
          maximalFactorWord (blockX h S) ++ maximalFactorWord (blockX h S) ++
          maximalFactorWord (blockY f S) ++ maximalFactorWord (blockY f S) ++
          maximalFactorWord (blockX h S) ++ maximalFactorWord (blockX h S) ++
          maximalFactorWord (blockY f S) ++ maximalFactorWord (blockY f S) := by
      intro h
      apply Word.toList_injective
      rw [maximalFactorWord_toList (by
        simp [longBlock, blockX])]
      simp only [Word.toList_append,
        maximalFactorWord_toList (blockX_nonempty h S),
        maximalFactorWord_toList (blockY_nonempty f S)]
      simp [longBlock, List.append_assoc]
    have wordSplitShort : ∀ h : Nat,
        maximalFactorWord (shortBlock h f S) =
          maximalFactorWord (blockY f S) ++ maximalFactorWord (blockY f S) ++
          maximalFactorWord (blockX h S) ++ maximalFactorWord (blockX h S) ++
          maximalFactorWord (blockY f S) ++ maximalFactorWord (blockY f S) := by
      intro h
      apply Word.toList_injective
      rw [maximalFactorWord_toList (by
        simp [shortBlock, blockY])]
      simp only [Word.toList_append,
        maximalFactorWord_toList (blockX_nonempty h S),
        maximalFactorWord_toList (blockY_nonempty f S)]
      simp [shortBlock, List.append_assoc]
    have hopTwo : Derives laws
        (guard ++ maximalFactorWord (longBlock chead f S))
        (guard ++ maximalFactorWord (shortBlock chead f S)) := by
      rw [wordSplitLong chead, wordSplitShort chead]
      simpa [Word.append_assoc] using
        derivesGuardedSwitch env guard
          (maximalFactorWord (blockX chead S))
          (maximalFactorWord (blockY f S))
    have hopFour : Derives laws
        (guard ++ maximalFactorWord (shortBlock dhead f S))
        (guard ++ maximalFactorWord (longBlock dhead f S)) := by
      rw [wordSplitLong dhead, wordSplitShort dhead]
      have switched :=
        (derivesGuardedSwitch env guard
          (maximalFactorWord (blockX dhead S))
          (maximalFactorWord (blockY f S))).symm
      simpa [Word.append_assoc] using switched
    exact hopOne.trans (hopTwo.trans (hopThree.trans
      (hopFour.trans hopFive)))

/-! ## Interior-final erasure -/

/-- Components with equal base data and equal heads can differ in their final
letters when followed by a nonempty suffix.  The final-erasure law connects
them through two exact-signature switch blocks. -/
theorem derivesInteriorComponentSameHead
    {laws : List (Identity Nat)}
    (env : FinalEraseLawEnvironment laws) (suffix : Word Nat)
    {chead dhead : Nat} {ctail dtail : List Nat}
    (cConnected : ConnectedComponentSupportConnected (chead :: ctail))
    (dConnected : ConnectedComponentSupportConnected (dhead :: dtail))
    (baseSignature :
      connectedComponentSignatureOfList (chead :: ctail) =
        connectedComponentSignatureOfList (dhead :: dtail))
    (heads : chead = dhead) :
    Derives laws
      (maximalFactorWord (chead :: ctail) ++ suffix)
      (maximalFactorWord (dhead :: dtail) ++ suffix) := by
  subst dhead
  have supportEq :
      connectedComponentSortedSupport (chead :: ctail) =
        connectedComponentSortedSupport (chead :: dtail) := by
    have projected :=
      congrArg connectedComponentSignature.support baseSignature
    rwa [connectedComponentSignatureOfList_support,
      connectedComponentSignatureOfList_support] at projected
  rcases supportShape :
      connectedComponentSortedSupport (chead :: ctail) with
    _ | ⟨one, rest⟩
  · exact absurd supportShape
      (connectedComponentSortedSupport_nonempty (by simp))
  rcases rest with _ | ⟨two, rest⟩
  · have cFinalSupport :
        componentFinal (chead :: ctail) ∈
          connectedComponentSortedSupport (chead :: ctail) :=
      (connectedComponentSortedSupport_mem_iff _ _).mpr
        (componentFinal_mem chead ctail)
    have dFinalSupport :
        componentFinal (chead :: dtail) ∈
          connectedComponentSortedSupport (chead :: dtail) :=
      (connectedComponentSortedSupport_mem_iff _ _).mpr
        (componentFinal_mem chead dtail)
    have cFinal :
        componentFinal (chead :: ctail) = one := by
      rw [supportShape] at cFinalSupport
      simpa using cFinalSupport
    have dFinal :
        componentFinal (chead :: dtail) = one := by
      rw [← supportEq, supportShape] at dFinalSupport
      simpa using dFinalSupport
    have exactSignature :
        connectedCutComponentSignatureOfList (chead :: ctail) =
          connectedCutComponentSignatureOfList (chead :: dtail) := by
      simp only [connectedCutComponentSignatureOfList]
      rw [baseSignature, cFinal, dFinal]
    exact Derives.appendRight
      (derivesComponentWords env.toSwitchLawEnvironment
        cConnected dConnected exactSignature rfl) suffix
  · let S : List Nat := one :: two :: rest
    have SDef : S = one :: two :: rest := rfl
    have cSupport :
        connectedComponentSortedSupport (chead :: ctail) = S := by
      simpa [S] using supportShape
    have dSupport :
        connectedComponentSortedSupport (chead :: dtail) = S := by
      rw [← supportEq]
      exact cSupport
    have sorted : S.Pairwise (· ≤ ·) := by
      have source :=
        connectedComponentSortedSupport_sorted (chead :: ctail)
      rw [cSupport] at source
      exact source
    have nodup : S.Nodup := by
      have source :=
        connectedComponentSortedSupport_nodup (chead :: ctail)
      rw [cSupport] at source
      exact source
    have headMem : chead ∈ S := by
      rw [← cSupport, connectedComponentSortedSupport_mem_iff]
      simp
    let cf : Nat := componentFinal (chead :: ctail)
    let df : Nat := componentFinal (chead :: dtail)
    have cfMem : cf ∈ S := by
      rw [← cSupport, connectedComponentSortedSupport_mem_iff]
      exact componentFinal_mem chead ctail
    have dfMem : df ∈ S := by
      rw [← dSupport, connectedComponentSortedSupport_mem_iff]
      exact componentFinal_mem chead dtail
    have cSignature :
        connectedCutComponentSignatureOfList (chead :: ctail) =
          ⟨⟨S, false⟩, cf⟩ :=
      multi_cutSignature SDef cSupport rfl
    have dSignature :
        connectedCutComponentSignatureOfList (chead :: dtail) =
          ⟨⟨S, false⟩, df⟩ :=
      multi_cutSignature SDef dSupport rfl
    have longCSupport :
        connectedComponentSortedSupport (longBlock chead cf S) = S :=
      block_sortedSupport sorted nodup headMem cfMem
        (longBlock_subset headMem cfMem)
        (fun s sMem => by
          simp only [longBlock, List.mem_append]
          exact Or.inl (blockX_full s sMem))
    have longDSupport :
        connectedComponentSortedSupport (longBlock chead df S) = S :=
      block_sortedSupport sorted nodup headMem dfMem
        (longBlock_subset headMem dfMem)
        (fun s sMem => by
          simp only [longBlock, List.mem_append]
          exact Or.inl (blockX_full s sMem))
    have erasedCSupport :
        connectedComponentSortedSupport (erasedBlock chead cf S) = S :=
      block_sortedSupport sorted nodup headMem cfMem
        (erasedBlock_subset headMem cfMem)
        (fun s sMem => by
          simp only [erasedBlock, List.mem_append]
          exact Or.inl (blockX_full s sMem))
    have erasedDSupport :
        connectedComponentSortedSupport (erasedBlock chead df S) = S :=
      block_sortedSupport sorted nodup headMem dfMem
        (erasedBlock_subset headMem dfMem)
        (fun s sMem => by
          simp only [erasedBlock, List.mem_append]
          exact Or.inl (blockX_full s sMem))
    have longCSignature :
        connectedCutComponentSignatureOfList (longBlock chead cf S) =
          ⟨⟨S, false⟩, cf⟩ :=
      multi_cutSignature SDef longCSupport longBlock_final
    have longDSignature :
        connectedCutComponentSignatureOfList (longBlock chead df S) =
          ⟨⟨S, false⟩, df⟩ :=
      multi_cutSignature SDef longDSupport longBlock_final
    have erasedSignature :
        connectedCutComponentSignatureOfList (erasedBlock chead cf S) =
          connectedCutComponentSignatureOfList
            (erasedBlock chead df S) := by
      have left :
          connectedCutComponentSignatureOfList
              (erasedBlock chead cf S) =
            ⟨⟨S, false⟩,
              componentFinal (erasedBlock chead cf S)⟩ :=
        multi_cutSignature SDef erasedCSupport rfl
      have right :
          connectedCutComponentSignatureOfList
              (erasedBlock chead df S) =
            ⟨⟨S, false⟩,
              componentFinal (erasedBlock chead df S)⟩ :=
        multi_cutSignature SDef erasedDSupport rfl
      rw [left, right,
        erasedBlock_final_eq
          (h := chead) (f := cf) (g := df) (S := S)]
    have longCCons : longBlock chead cf S =
        chead :: (S.erase chead ++ (blockX chead S ++
          (blockY cf S ++ (blockY cf S ++
            (blockX chead S ++ (blockX chead S ++
              (blockY cf S ++ blockY cf S))))))) := by
      simp [longBlock, blockX, List.cons_append]
    have longDCons : longBlock chead df S =
        chead :: (S.erase chead ++ (blockX chead S ++
          (blockY df S ++ (blockY df S ++
            (blockX chead S ++ (blockX chead S ++
              (blockY df S ++ blockY df S))))))) := by
      simp [longBlock, blockX, List.cons_append]
    have erasedCCons : erasedBlock chead cf S =
        chead :: (S.erase chead ++ (blockX chead S ++
          (blockY cf S ++ (blockY cf S ++
            (blockX chead S ++ blockX chead S))))) := by
      simp [erasedBlock, blockX, List.cons_append]
    have erasedDCons : erasedBlock chead df S =
        chead :: (S.erase chead ++ (blockX chead S ++
          (blockY df S ++ (blockY df S ++
            (blockX chead S ++ blockX chead S))))) := by
      simp [erasedBlock, blockX, List.cons_append]
    have hopOneBase : Derives laws
        (maximalFactorWord (chead :: ctail))
        (maximalFactorWord (longBlock chead cf S)) := by
      rw [longCCons]
      exact derivesComponentWords env.toSwitchLawEnvironment cConnected
        (longCCons ▸ longBlock_connected headMem cfMem)
        (by rw [← longCCons, longCSignature, cSignature]) rfl
    have hopOne := Derives.appendRight hopOneBase suffix
    have hopTwo : Derives laws
        (maximalFactorWord (longBlock chead cf S) ++ suffix)
        (maximalFactorWord (erasedBlock chead cf S) ++ suffix) := by
      rw [maximalFactorWord_longBlock,
        maximalFactorWord_erasedBlock]
      simpa [Word.append_assoc] using
        derivesFinalErase env
          (maximalFactorWord (blockX chead S))
          (maximalFactorWord (blockY cf S)) suffix
    have hopThreeBase : Derives laws
        (maximalFactorWord (erasedBlock chead cf S))
        (maximalFactorWord (erasedBlock chead df S)) := by
      rw [erasedCCons, erasedDCons]
      exact derivesComponentWords env.toSwitchLawEnvironment
        (erasedCCons ▸ erasedBlock_connected headMem cfMem)
        (erasedDCons ▸ erasedBlock_connected headMem dfMem)
        (by
          rw [← erasedCCons, ← erasedDCons]
          exact erasedSignature) rfl
    have hopThree := Derives.appendRight hopThreeBase suffix
    have hopFour : Derives laws
        (maximalFactorWord (erasedBlock chead df S) ++ suffix)
        (maximalFactorWord (longBlock chead df S) ++ suffix) := by
      rw [maximalFactorWord_longBlock,
        maximalFactorWord_erasedBlock]
      have erased :=
        derivesFinalErase env
          (maximalFactorWord (blockX chead S))
          (maximalFactorWord (blockY df S)) suffix
      simpa [Word.append_assoc] using erased.symm
    have hopFiveBase : Derives laws
        (maximalFactorWord (longBlock chead df S))
        (maximalFactorWord (chead :: dtail)) := by
      rw [longDCons]
      exact derivesComponentWords env.toSwitchLawEnvironment
        (longDCons ▸ longBlock_connected headMem dfMem) dConnected
        (by rw [← longDCons, longDSignature, dSignature]) rfl
    have hopFive := Derives.appendRight hopFiveBase suffix
    exact hopOne.trans (hopTwo.trans (hopThree.trans
      (hopFour.trans hopFive)))

/-- Behind a nonempty left guard, the switch normalizer first aligns the
component head; the final-erasure bridge then forgets the interior final. -/
theorem derivesInteriorComponentBehindGuard
    {laws : List (Identity Nat)}
    (env : FinalEraseLawEnvironment laws) (guard suffix : Word Nat)
    {chead dhead : Nat} {ctail dtail : List Nat}
    (cConnected : ConnectedComponentSupportConnected (chead :: ctail))
    (dConnected : ConnectedComponentSupportConnected (dhead :: dtail))
    (baseSignature :
      connectedComponentSignatureOfList (chead :: ctail) =
        connectedComponentSignatureOfList (dhead :: dtail)) :
    Derives laws
      ((guard ++ maximalFactorWord (chead :: ctail)) ++ suffix)
      ((guard ++ maximalFactorWord (dhead :: dtail)) ++ suffix) := by
  have supportEq :
      connectedComponentSortedSupport (chead :: ctail) =
        connectedComponentSortedSupport (dhead :: dtail) := by
    have projected :=
      congrArg connectedComponentSignature.support baseSignature
    rwa [connectedComponentSignatureOfList_support,
      connectedComponentSignatureOfList_support] at projected
  rcases supportShape :
      connectedComponentSortedSupport (chead :: ctail) with
    _ | ⟨one, rest⟩
  · exact absurd supportShape
      (connectedComponentSortedSupport_nonempty (by simp))
  rcases rest with _ | ⟨two, rest⟩
  · have cheadSupport :
        chead ∈ connectedComponentSortedSupport (chead :: ctail) :=
      (connectedComponentSortedSupport_mem_iff _ _).mpr (by simp)
    have dheadSupport :
        dhead ∈ connectedComponentSortedSupport (dhead :: dtail) :=
      (connectedComponentSortedSupport_mem_iff _ _).mpr (by simp)
    have cheadEq : chead = one := by
      rw [supportShape] at cheadSupport
      simpa using cheadSupport
    have dheadEq : dhead = one := by
      rw [← supportEq, supportShape] at dheadSupport
      simpa using dheadSupport
    have core :=
      derivesInteriorComponentSameHead env suffix cConnected dConnected
        baseSignature (cheadEq.trans dheadEq.symm)
    have prefixed := Derives.prepend guard core
    simpa [Word.append_assoc] using prefixed
  · let S : List Nat := one :: two :: rest
    have SDef : S = one :: two :: rest := rfl
    have cSupport :
        connectedComponentSortedSupport (chead :: ctail) = S := by
      simpa [S] using supportShape
    have dSupport :
        connectedComponentSortedSupport (dhead :: dtail) = S := by
      rw [← supportEq]
      exact cSupport
    have sorted : S.Pairwise (· ≤ ·) := by
      have source :=
        connectedComponentSortedSupport_sorted (chead :: ctail)
      rw [cSupport] at source
      exact source
    have nodup : S.Nodup := by
      have source :=
        connectedComponentSortedSupport_nodup (chead :: ctail)
      rw [cSupport] at source
      exact source
    have cheadMem : chead ∈ S := by
      rw [← cSupport, connectedComponentSortedSupport_mem_iff]
      simp
    let df : Nat := componentFinal (dhead :: dtail)
    have dfMem : df ∈ S := by
      rw [← dSupport, connectedComponentSortedSupport_mem_iff]
      exact componentFinal_mem dhead dtail
    have proxySupport :
        connectedComponentSortedSupport (longBlock chead df S) = S :=
      block_sortedSupport sorted nodup cheadMem dfMem
        (longBlock_subset cheadMem dfMem)
        (fun s sMem => by
          simp only [longBlock, List.mem_append]
          exact Or.inl (blockX_full s sMem))
    have proxySignature :
        connectedCutComponentSignatureOfList (longBlock chead df S) =
          ⟨⟨S, false⟩, df⟩ :=
      multi_cutSignature SDef proxySupport longBlock_final
    have dSignature :
        connectedCutComponentSignatureOfList (dhead :: dtail) =
          ⟨⟨S, false⟩, df⟩ :=
      multi_cutSignature SDef dSupport rfl
    have exactProxySignature :
        connectedCutComponentSignatureOfList (longBlock chead df S) =
          connectedCutComponentSignatureOfList (dhead :: dtail) :=
      proxySignature.trans dSignature.symm
    have proxyBase :
        connectedComponentSignatureOfList (longBlock chead df S) =
          connectedComponentSignatureOfList (dhead :: dtail) :=
      congrArg ConnectedCutComponentSignature.base exactProxySignature
    have sourceToProxyBase :
        connectedComponentSignatureOfList (chead :: ctail) =
          connectedComponentSignatureOfList (longBlock chead df S) :=
      baseSignature.trans proxyBase.symm
    have proxyCons : longBlock chead df S =
        chead :: (S.erase chead ++ (blockX chead S ++
          (blockY df S ++ (blockY df S ++
            (blockX chead S ++ (blockX chead S ++
              (blockY df S ++ blockY df S))))))) := by
      simp [longBlock, blockX, List.cons_append]
    have sourceToProxy : Derives laws
        (maximalFactorWord (chead :: ctail) ++ suffix)
        (maximalFactorWord (longBlock chead df S) ++ suffix) := by
      rw [proxyCons]
      exact derivesInteriorComponentSameHead env suffix cConnected
        (proxyCons ▸ longBlock_connected cheadMem dfMem)
        (by rw [← proxyCons]; exact sourceToProxyBase) rfl
    have sourceToProxyGuarded :
        Derives laws
          ((guard ++ maximalFactorWord (chead :: ctail)) ++ suffix)
          ((guard ++ maximalFactorWord (longBlock chead df S)) ++
            suffix) := by
      have prefixed := Derives.prepend guard sourceToProxy
      simpa [Word.append_assoc] using prefixed
    have proxyToTargetBase : Derives laws
        (guard ++ maximalFactorWord (longBlock chead df S))
        (guard ++ maximalFactorWord (dhead :: dtail)) := by
      rw [proxyCons]
      exact derivesComponentSwitchWords env.toSwitchLawEnvironment guard
        (proxyCons ▸ longBlock_connected cheadMem dfMem) dConnected
        (by rw [← proxyCons]; exact exactProxySignature)
    have proxyToTarget :=
      Derives.appendRight proxyToTargetBase suffix
    exact sourceToProxyGuarded.trans proxyToTarget

/-! ## Chain assembly -/

private theorem flatten_cons_word
    {first : List Nat} {rest : List (List Nat)}
    (firstNonempty : first ≠ [])
    (restNonempty : rest.flatten ≠ []) :
    maximalFactorWord (first ++ rest.flatten) =
      maximalFactorWord first ++ maximalFactorWord rest.flatten := by
  apply Word.toList_injective
  rw [Word.toList_append,
    maximalFactorWord_toList (by
      intro appendEmpty
      exact firstNonempty (List.append_eq_nil_iff.mp appendEmpty).1),
    maximalFactorWord_toList firstNonempty,
    maximalFactorWord_toList restNonempty]

private theorem derivesChain {laws : List (Identity Nat)}
    (env : SwitchLawEnvironment laws) :
    ∀ (leftChain rightChain : List (List Nat)) (guard : Word Nat),
      leftChain ≠ [] →
      (∀ component ∈ leftChain, component ≠ []) →
      (∀ component ∈ rightChain, component ≠ []) →
      (∀ component ∈ leftChain,
        ConnectedComponentSupportConnected component) →
      (∀ component ∈ rightChain,
        ConnectedComponentSupportConnected component) →
      leftChain.map connectedCutComponentSignatureOfList =
        rightChain.map connectedCutComponentSignatureOfList →
      Derives laws
        (guard ++ maximalFactorWord leftChain.flatten)
        (guard ++ maximalFactorWord rightChain.flatten)
  | [], _, _, absurdEmpty, _, _, _, _, _ => absurd rfl absurdEmpty
  | first :: rest, [], _, _, _, _, _, _, mapsEq => by
      simp at mapsEq
  | first :: rest, second :: rest', guard, _, leftNonempty,
      rightNonempty, leftConnected, rightConnected, mapsEq => by
      simp only [List.map_cons, List.cons.injEq] at mapsEq
      obtain ⟨headSig, tailSig⟩ := mapsEq
      have firstNonempty : first ≠ [] := leftNonempty first (by simp)
      have secondNonempty : second ≠ [] := rightNonempty second (by simp)
      rcases firstShape : first with _ | ⟨fhead, ftail⟩
      · exact absurd firstShape firstNonempty
      rcases secondShape : second with _ | ⟨shead, stail⟩
      · exact absurd secondShape secondNonempty
      have firstConnected := leftConnected first (by simp)
      have secondConnected := rightConnected second (by simp)
      rw [firstShape] at firstConnected headSig
      rw [secondShape] at secondConnected headSig
      have headStep : Derives laws
          (guard ++ maximalFactorWord (fhead :: ftail))
          (guard ++ maximalFactorWord (shead :: stail)) :=
        derivesComponentSwitchWords env guard firstConnected
          secondConnected headSig
      rcases rest with _ | ⟨next, more⟩
      · -- single component on the left forces single on the right
        rcases rest' with _ | ⟨next', more'⟩
        · simpa [firstShape, secondShape] using headStep
        · simp at tailSig
      · rcases rest' with _ | ⟨next', more'⟩
        · simp at tailSig
        · -- both tails nonempty
          have restFlatNonempty : (next :: more).flatten ≠ [] := by
            have nextNonempty : next ≠ [] :=
              leftNonempty next (by simp)
            intro flatEmpty
            rw [List.flatten_cons] at flatEmpty
            exact nextNonempty (List.append_eq_nil_iff.mp flatEmpty).1
          have restFlatNonempty' : (next' :: more').flatten ≠ [] := by
            have nextNonempty' : next' ≠ [] :=
              rightNonempty next' (by simp)
            intro flatEmpty
            rw [List.flatten_cons] at flatEmpty
            exact nextNonempty' (List.append_eq_nil_iff.mp flatEmpty).1
          have tailStep := derivesChain env (next :: more) (next' :: more')
            (guard ++ maximalFactorWord (shead :: stail))
            (by simp)
            (fun component member =>
              leftNonempty component (List.mem_cons_of_mem first member))
            (fun component member =>
              rightNonempty component (List.mem_cons_of_mem second member))
            (fun component member =>
              leftConnected component (List.mem_cons_of_mem first member))
            (fun component member =>
              rightConnected component (List.mem_cons_of_mem second member))
            tailSig
          have headInContext : Derives laws
              (guard ++ (maximalFactorWord (fhead :: ftail) ++
                maximalFactorWord (next :: more).flatten))
              (guard ++ (maximalFactorWord (shead :: stail) ++
                maximalFactorWord (next :: more).flatten)) := by
            have shifted :=
              Derives.appendRight headStep
                (maximalFactorWord (next :: more).flatten)
            simpa [Word.append_assoc] using shifted
          have tailInContext : Derives laws
              (guard ++ (maximalFactorWord (shead :: stail) ++
                maximalFactorWord (next :: more).flatten))
              (guard ++ (maximalFactorWord (shead :: stail) ++
                maximalFactorWord (next' :: more').flatten)) := by
            simpa [Word.append_assoc] using tailStep
          have combined := headInContext.trans tailInContext
          change Derives laws
            (guard ++ maximalFactorWord
              ((fhead :: ftail) ++ (next :: more).flatten))
            (guard ++ maximalFactorWord
              ((shead :: stail) ++ (next' :: more').flatten))
          rw [flatten_cons_word
                (first := fhead :: ftail) (rest := next :: more)
                (by simp) restFlatNonempty,
            flatten_cons_word
                (first := shead :: stail) (rest := next' :: more')
                (by simp) restFlatNonempty']
          simpa [Word.append_assoc] using combined

private theorem exactCutSignature_of_base_and_final
    {left right : List Nat}
    (base :
      connectedComponentSignatureOfList left =
        connectedComponentSignatureOfList right)
    (final : componentFinal left = componentFinal right) :
    connectedCutComponentSignatureOfList left =
      connectedCutComponentSignatureOfList right := by
  change
    ConnectedCutComponentSignature.mk
        (connectedComponentSignatureOfList left) (componentFinal left) =
      ConnectedCutComponentSignature.mk
        (connectedComponentSignatureOfList right) (componentFinal right)
  rw [base, final]

private theorem componentFinal_flatten_cons_of_tail
    (first : List Nat) {tail : List (List Nat)}
    (tailNonempty : tail.flatten ≠ []) :
    componentFinal (first :: tail).flatten =
      componentFinal tail.flatten := by
  simp only [List.flatten_cons]
  exact componentFinal_append_of_right_nonempty
    first tail.flatten tailNonempty

/-- Tail-chain completeness behind an already-normalized nonempty prefix.
Component finals may vary except at the end of the chain. -/
private theorem derivesBaseChainBehindGuard
    {laws : List (Identity Nat)}
    (env : FinalEraseLawEnvironment laws) :
    ∀ (leftChain rightChain : List (List Nat)) (guard : Word Nat),
      leftChain ≠ [] →
      (∀ component ∈ leftChain, component ≠ []) →
      (∀ component ∈ rightChain, component ≠ []) →
      (∀ component ∈ leftChain,
        ConnectedComponentSupportConnected component) →
      (∀ component ∈ rightChain,
        ConnectedComponentSupportConnected component) →
      leftChain.map connectedComponentSignatureOfList =
        rightChain.map connectedComponentSignatureOfList →
      componentFinal leftChain.flatten =
        componentFinal rightChain.flatten →
      Derives laws
        (guard ++ maximalFactorWord leftChain.flatten)
        (guard ++ maximalFactorWord rightChain.flatten)
  | [], _, _, absurdEmpty, _, _, _, _, _, _ => absurd rfl absurdEmpty
  | first :: rest, [], _, _, _, _, _, _, mapsEq, _ => by
      simp at mapsEq
  | first :: rest, second :: rest', guard, _, leftNonempty,
      rightNonempty, leftConnected, rightConnected, mapsEq, finalEq => by
      simp only [List.map_cons, List.cons.injEq] at mapsEq
      obtain ⟨headBase, tailBase⟩ := mapsEq
      have firstNonempty : first ≠ [] := leftNonempty first (by simp)
      have secondNonempty : second ≠ [] := rightNonempty second (by simp)
      rcases firstShape : first with _ | ⟨fhead, ftail⟩
      · exact absurd firstShape firstNonempty
      rcases secondShape : second with _ | ⟨shead, stail⟩
      · exact absurd secondShape secondNonempty
      have firstConnected := leftConnected first (by simp)
      have secondConnected := rightConnected second (by simp)
      rw [firstShape] at firstConnected headBase
      rw [secondShape] at secondConnected headBase
      rcases rest with _ | ⟨next, more⟩
      · rcases rest' with _ | ⟨next', more'⟩
        · have componentFinalEq :
              componentFinal (fhead :: ftail) =
                componentFinal (shead :: stail) := by
            simpa [firstShape, secondShape] using finalEq
          have exactSignature :=
            exactCutSignature_of_base_and_final headBase componentFinalEq
          simpa [firstShape, secondShape, List.flatten_cons] using
            derivesComponentSwitchWords env.toSwitchLawEnvironment guard
              firstConnected secondConnected exactSignature
        · simp at tailBase
      · rcases rest' with _ | ⟨next', more'⟩
        · simp at tailBase
        · have leftTailNonempty : (next :: more).flatten ≠ [] := by
            have nextNonempty : next ≠ [] :=
              leftNonempty next (by simp)
            intro flatEmpty
            rw [List.flatten_cons] at flatEmpty
            exact nextNonempty
              (List.append_eq_nil_iff.mp flatEmpty).1
          have rightTailNonempty : (next' :: more').flatten ≠ [] := by
            have nextNonempty : next' ≠ [] :=
              rightNonempty next' (by simp)
            intro flatEmpty
            rw [List.flatten_cons] at flatEmpty
            exact nextNonempty
              (List.append_eq_nil_iff.mp flatEmpty).1
          have tailFinalEq :
              componentFinal (next :: more).flatten =
                componentFinal (next' :: more').flatten := by
            have leftDrop :=
              componentFinal_flatten_cons_of_tail first leftTailNonempty
            have rightDrop :=
              componentFinal_flatten_cons_of_tail second rightTailNonempty
            exact leftDrop.symm.trans (finalEq.trans rightDrop)
          have headStep :=
            derivesInteriorComponentBehindGuard env guard
              (maximalFactorWord (next :: more).flatten)
              firstConnected secondConnected headBase
          have tailStep :=
            derivesBaseChainBehindGuard env (next :: more)
              (next' :: more')
              (guard ++ maximalFactorWord (shead :: stail))
              (by simp)
              (fun component member =>
                leftNonempty component
                  (List.mem_cons_of_mem first member))
              (fun component member =>
                rightNonempty component
                  (List.mem_cons_of_mem second member))
              (fun component member =>
                leftConnected component
                  (List.mem_cons_of_mem first member))
              (fun component member =>
                rightConnected component
                  (List.mem_cons_of_mem second member))
              tailBase tailFinalEq
          have combined := headStep.trans tailStep
          change Derives laws
            (guard ++ maximalFactorWord
              ((fhead :: ftail) ++ (next :: more).flatten))
            (guard ++ maximalFactorWord
              ((shead :: stail) ++ (next' :: more').flatten))
          rw [flatten_cons_word
                (first := fhead :: ftail) (rest := next :: more)
                (by simp) leftTailNonempty,
            flatten_cons_word
                (first := shead :: stail) (rest := next' :: more')
                (by simp) rightTailNonempty]
          simpa [Word.append_assoc] using combined

/-! ## The completeness theorem -/

private theorem head_of_flatten
    {word : Word Nat} {first : List Nat} {rest : List (List Nat)}
    (decomposition :
      connectedComponentDecomposeWord word = first :: rest) :
    ∃ tail, first = word.head :: tail := by
  have flattened := connectedComponentDecomposeWord_flatten word
  rw [decomposition] at flattened
  have firstNonempty : first ≠ [] :=
    connectedComponentDecomposeWord_nonempty_components word first
      (by rw [decomposition]; simp)
  rcases firstShape : first with _ | ⟨fhead, ftail⟩
  · exact absurd firstShape firstNonempty
  refine ⟨ftail, ?_⟩
  rw [firstShape] at flattened
  have headEq : fhead = word.head := by
    have listShape : word.toList = fhead :: (ftail ++ rest.flatten) := by
      rw [← flattened]
      simp [List.flatten_cons]
    cases word with
    | mk head tail =>
        simpa [Word.toList] using congrArg (List.headD · 0) listShape.symm
  rw [headEq]

/-- Equal direct connected-cut signatures with equal heads derive, for every
law list carrying the four scaffold laws and the guarded switch. -/
theorem derivesOfSameSignatureAndHead {laws : List (Identity Nat)}
    (env : SwitchLawEnvironment laws) {u v : Word Nat}
    (same : SameDirectSignatureAndHead u v) :
    Derives laws u v := by
  obtain ⟨signatures, heads⟩ := same
  have signaturesList :
      (connectedComponentDecomposeWord u).map
          connectedCutComponentSignatureOfList =
        (connectedComponentDecomposeWord v).map
          connectedCutComponentSignatureOfList := by
    have unfolded := signatures
    rwa [SameConnectedCutSignature, connectedCutSignaturesWord,
      connectedCutSignaturesWord, connectedCutSignaturesList,
      connectedCutSignaturesList] at unfolded
  rcases uShape :
      connectedComponentDecomposeWord u with _ | ⟨ufirst, urest⟩
  · exact absurd uShape (connectedComponentDecomposeWord_nonempty u)
  rcases vShape :
      connectedComponentDecomposeWord v with _ | ⟨vfirst, vrest⟩
  · exact absurd vShape (connectedComponentDecomposeWord_nonempty v)
  obtain ⟨utail, ufirstShape⟩ := head_of_flatten uShape
  obtain ⟨vtail, vfirstShape⟩ := head_of_flatten vShape
  rw [uShape, vShape] at signaturesList
  simp only [List.map_cons, List.cons.injEq] at signaturesList
  obtain ⟨headSig, tailSig⟩ := signaturesList
  have uFirstConnected :
      ConnectedComponentSupportConnected ufirst :=
    connectedComponentDecomposeWord_supportConnected u ufirst
      (by rw [uShape]; simp)
  have vFirstConnected :
      ConnectedComponentSupportConnected vfirst :=
    connectedComponentDecomposeWord_supportConnected v vfirst
      (by rw [vShape]; simp)
  have headDerivation : Derives laws
      (maximalFactorWord ufirst) (maximalFactorWord vfirst) := by
    rw [ufirstShape] at uFirstConnected headSig ⊢
    rw [vfirstShape] at vFirstConnected headSig ⊢
    exact derivesComponentWords env uFirstConnected vFirstConnected
      headSig heads
  have uWordEq : maximalFactorWord (ufirst :: urest).flatten = u := by
    apply maximalFactorWord_eq_of_toList
    rw [← uShape]
    exact (connectedComponentDecomposeWord_flatten u).symm
  have vWordEq : maximalFactorWord (vfirst :: vrest).flatten = v := by
    apply maximalFactorWord_eq_of_toList
    rw [← vShape]
    exact (connectedComponentDecomposeWord_flatten v).symm
  rcases urest with _ | ⟨unext, umore⟩
  · rcases vrest with _ | ⟨vnext, vmore⟩
    · rw [← uWordEq, ← vWordEq]
      simpa [List.flatten_cons] using headDerivation
    · simp at tailSig
  · rcases vrest with _ | ⟨vnext, vmore⟩
    · simp at tailSig
    · have uRestFlatNonempty : (unext :: umore).flatten ≠ [] := by
        have nextNonempty : unext ≠ [] :=
          connectedComponentDecomposeWord_nonempty_components u unext
            (by rw [uShape]; simp)
        intro flatEmpty
        rw [List.flatten_cons] at flatEmpty
        exact nextNonempty (List.append_eq_nil_iff.mp flatEmpty).1
      have vRestFlatNonempty : (vnext :: vmore).flatten ≠ [] := by
        have nextNonempty : vnext ≠ [] :=
          connectedComponentDecomposeWord_nonempty_components v vnext
            (by rw [vShape]; simp)
        intro flatEmpty
        rw [List.flatten_cons] at flatEmpty
        exact nextNonempty (List.append_eq_nil_iff.mp flatEmpty).1
      have ufirstNonempty : ufirst ≠ [] := by
        rw [ufirstShape]; simp
      have vfirstNonempty : vfirst ≠ [] := by
        rw [vfirstShape]; simp
      have tailDerivation := derivesChain env (unext :: umore)
        (vnext :: vmore) (maximalFactorWord vfirst)
        (by simp)
        (fun component member =>
          connectedComponentDecomposeWord_nonempty_components u component
            (by rw [uShape]; exact List.mem_cons_of_mem ufirst member))
        (fun component member =>
          connectedComponentDecomposeWord_nonempty_components v component
            (by rw [vShape]; exact List.mem_cons_of_mem vfirst member))
        (fun component member =>
          connectedComponentDecomposeWord_supportConnected u component
            (by rw [uShape]; exact List.mem_cons_of_mem ufirst member))
        (fun component member =>
          connectedComponentDecomposeWord_supportConnected v component
            (by rw [vShape]; exact List.mem_cons_of_mem vfirst member))
        tailSig
      have headInContext :=
        Derives.appendRight headDerivation
          (maximalFactorWord (unext :: umore).flatten)
      rw [← uWordEq, ← vWordEq]
      change Derives laws
        (maximalFactorWord (ufirst ++ (unext :: umore).flatten))
        (maximalFactorWord (vfirst ++ (vnext :: vmore).flatten))
      rw [flatten_cons_word
            (first := ufirst) (rest := unext :: umore)
            ufirstNonempty uRestFlatNonempty,
        flatten_cons_word
            (first := vfirst) (rest := vnext :: vmore)
            vfirstNonempty vRestFlatNonempty]
      exact headInContext.trans tailDerivation

private theorem s5_806_componentFinal_eq (letters : List Nat) :
    SemigroupBasis.CoRoots.S5_806.componentFinal letters =
      componentFinal letters := by
  cases letters <;> rfl

/-- Equal system-2 descriptors derive for every law list carrying the frozen
switch environment and the guarded interior-final erasure. -/
theorem derivesOfBaseChainFinalAndHead
    {laws : List (Identity Nat)}
    (env : FinalEraseLawEnvironment laws) {u v : Word Nat}
    (same : SameBaseChainFinalAndHead u v) :
    Derives laws u v := by
  obtain ⟨signature, heads⟩ := same
  change
    SemigroupBasis.CoRoots.S5_806.connectedCutSignatureOfWord u =
      SemigroupBasis.CoRoots.S5_806.connectedCutSignatureOfWord v
    at signature
  have baseSignatures :=
    congrArg
      SemigroupBasis.CoRoots.S5_806.ConnectedCutSignature.components
      signature
  have wholeFinals :=
    congrArg SemigroupBasis.CoRoots.S5_806.ConnectedCutSignature.final
      signature
  have baseMaps :
      (connectedComponentDecomposeWord u).map
          connectedComponentSignatureOfList =
        (connectedComponentDecomposeWord v).map
          connectedComponentSignatureOfList := by
    change
      connectedComponentSignaturesWord u =
        connectedComponentSignaturesWord v at baseSignatures
    simpa [connectedComponentSignaturesWord,
      connectedComponentSignaturesList, connectedComponentDecomposeWord]
      using baseSignatures
  have wholeFinalEq :
      componentFinal u.toList = componentFinal v.toList := by
    change
      SemigroupBasis.CoRoots.S5_806.componentFinal u.toList =
        SemigroupBasis.CoRoots.S5_806.componentFinal v.toList
      at wholeFinals
    simpa only [s5_806_componentFinal_eq] using wholeFinals
  rcases uShape :
      connectedComponentDecomposeWord u with _ | ⟨ufirst, urest⟩
  · exact absurd uShape (connectedComponentDecomposeWord_nonempty u)
  rcases vShape :
      connectedComponentDecomposeWord v with _ | ⟨vfirst, vrest⟩
  · exact absurd vShape (connectedComponentDecomposeWord_nonempty v)
  obtain ⟨utail, ufirstShape⟩ := head_of_flatten uShape
  obtain ⟨vtail, vfirstShape⟩ := head_of_flatten vShape
  rw [uShape, vShape] at baseMaps
  simp only [List.map_cons, List.cons.injEq] at baseMaps
  obtain ⟨headBase, tailBase⟩ := baseMaps
  have uFirstConnected :
      ConnectedComponentSupportConnected ufirst :=
    connectedComponentDecomposeWord_supportConnected u ufirst
      (by rw [uShape]; simp)
  have vFirstConnected :
      ConnectedComponentSupportConnected vfirst :=
    connectedComponentDecomposeWord_supportConnected v vfirst
      (by rw [vShape]; simp)
  have uFlatten := connectedComponentDecomposeWord_flatten u
  have vFlatten := connectedComponentDecomposeWord_flatten v
  rw [uShape] at uFlatten
  rw [vShape] at vFlatten
  have chainFinalEq :
      componentFinal (ufirst :: urest).flatten =
        componentFinal (vfirst :: vrest).flatten := by
    rw [uFlatten, vFlatten]
    exact wholeFinalEq
  have uWordEq : maximalFactorWord (ufirst :: urest).flatten = u := by
    apply maximalFactorWord_eq_of_toList
    exact uFlatten.symm
  have vWordEq : maximalFactorWord (vfirst :: vrest).flatten = v := by
    apply maximalFactorWord_eq_of_toList
    exact vFlatten.symm
  rcases urest with _ | ⟨unext, umore⟩
  · rcases vrest with _ | ⟨vnext, vmore⟩
    · have firstFinalEq :
          componentFinal ufirst = componentFinal vfirst := by
        simpa [List.flatten_cons] using chainFinalEq
      have exactSignature :=
        exactCutSignature_of_base_and_final headBase firstFinalEq
      have firstStep : Derives laws
          (maximalFactorWord ufirst) (maximalFactorWord vfirst) := by
        rw [ufirstShape] at uFirstConnected exactSignature ⊢
        rw [vfirstShape] at vFirstConnected exactSignature ⊢
        exact derivesComponentWords env.toSwitchLawEnvironment
          uFirstConnected vFirstConnected exactSignature heads
      rw [← uWordEq, ← vWordEq]
      simpa [List.flatten_cons] using firstStep
    · simp at tailBase
  · rcases vrest with _ | ⟨vnext, vmore⟩
    · simp at tailBase
    · have uTailNonempty : (unext :: umore).flatten ≠ [] := by
        have nextNonempty : unext ≠ [] :=
          connectedComponentDecomposeWord_nonempty_components u unext
            (by rw [uShape]; simp)
        intro flatEmpty
        rw [List.flatten_cons] at flatEmpty
        exact nextNonempty (List.append_eq_nil_iff.mp flatEmpty).1
      have vTailNonempty : (vnext :: vmore).flatten ≠ [] := by
        have nextNonempty : vnext ≠ [] :=
          connectedComponentDecomposeWord_nonempty_components v vnext
            (by rw [vShape]; simp)
        intro flatEmpty
        rw [List.flatten_cons] at flatEmpty
        exact nextNonempty (List.append_eq_nil_iff.mp flatEmpty).1
      have tailFinalEq :
          componentFinal (unext :: umore).flatten =
            componentFinal (vnext :: vmore).flatten := by
        have leftDrop :=
          componentFinal_flatten_cons_of_tail ufirst uTailNonempty
        have rightDrop :=
          componentFinal_flatten_cons_of_tail vfirst vTailNonempty
        exact leftDrop.symm.trans (chainFinalEq.trans rightDrop)
      have headStep : Derives laws
          (maximalFactorWord ufirst ++
            maximalFactorWord (unext :: umore).flatten)
          (maximalFactorWord vfirst ++
            maximalFactorWord (unext :: umore).flatten) := by
        rw [ufirstShape] at uFirstConnected headBase ⊢
        rw [vfirstShape] at vFirstConnected headBase ⊢
        exact derivesInteriorComponentSameHead env
          (maximalFactorWord (unext :: umore).flatten)
          uFirstConnected vFirstConnected headBase heads
      have tailStep :=
        derivesBaseChainBehindGuard env (unext :: umore)
          (vnext :: vmore) (maximalFactorWord vfirst)
          (by simp)
          (fun component member =>
            connectedComponentDecomposeWord_nonempty_components u component
              (by
                rw [uShape]
                exact List.mem_cons_of_mem ufirst member))
          (fun component member =>
            connectedComponentDecomposeWord_nonempty_components v component
              (by
                rw [vShape]
                exact List.mem_cons_of_mem vfirst member))
          (fun component member =>
            connectedComponentDecomposeWord_supportConnected u component
              (by
                rw [uShape]
                exact List.mem_cons_of_mem ufirst member))
          (fun component member =>
            connectedComponentDecomposeWord_supportConnected v component
              (by
                rw [vShape]
                exact List.mem_cons_of_mem vfirst member))
          tailBase tailFinalEq
      have combined := headStep.trans tailStep
      rw [← uWordEq, ← vWordEq]
      change Derives laws
        (maximalFactorWord
          (ufirst ++ (unext :: umore).flatten))
        (maximalFactorWord
          (vfirst ++ (vnext :: vmore).flatten))
      rw [flatten_cons_word
            (first := ufirst) (rest := unext :: umore)
            (by rw [ufirstShape]; simp) uTailNonempty,
        flatten_cons_word
            (first := vfirst) (rest := vnext :: vmore)
            (by rw [vfirstShape]; simp) vTailNonempty]
      exact combined

/-! ## Coalescing exact-cut gaps -/

/-- Once both lists have length at least two, the base component datum is
determined by support alone.  The only extra coordinate in the base datum
distinguishes a singleton unary component from a repeated unary component. -/
private theorem baseSignature_eq_of_support_length_ge_two
    {left right : List Nat}
    (leftLength : 2 ≤ left.length)
    (rightLength : 2 ≤ right.length)
    (supportEq :
      connectedComponentSortedSupport left =
        connectedComponentSortedSupport right) :
    connectedComponentSignatureOfList left =
      connectedComponentSignatureOfList right := by
  cases supportShape :
      connectedComponentSortedSupport right with
  | nil =>
      have leftSupport :
          connectedComponentSortedSupport left = [] :=
        supportEq.trans supportShape
      simp [connectedComponentSignatureOfList,
        leftSupport, supportShape]
  | cons first remaining =>
      cases remaining with
      | nil =>
          have leftSupport :
              connectedComponentSortedSupport left = [first] :=
            supportEq.trans supportShape
          have leftNotOne : left.length ≠ 1 := by omega
          have rightNotOne : right.length ≠ 1 := by omega
          simp [connectedComponentSignatureOfList,
            leftSupport, supportShape, leftNotOne, rightNotOne]
      | cons second rest =>
          have leftSupport :
              connectedComponentSortedSupport left =
                first :: second :: rest :=
            supportEq.trans supportShape
          simp [connectedComponentSignatureOfList,
            leftSupport, supportShape]

private theorem longBlock_length_ge_two
    (h f : Nat) (S : List Nat) :
    2 ≤ (longBlock h f S).length := by
  have positive : 0 < (blockX h S).length :=
    List.length_pos_iff.mpr (blockX_nonempty h S)
  simp only [longBlock, List.length_append]
  omega

private theorem longBlock_sortedSupport
    {h f : Nat} {S : List Nat}
    (sorted : S.Pairwise (· ≤ ·))
    (nodup : S.Nodup)
    (hMem : h ∈ S) (fMem : f ∈ S) :
    connectedComponentSortedSupport (longBlock h f S) = S :=
  block_sortedSupport sorted nodup hMem fMem
    (longBlock_subset hMem fMem)
    (fun s sMem => by
      simp only [longBlock, List.mem_append]
      exact Or.inl (blockX_full s sMem))

/-- A support-connected component of length at least two derives to the
eight-factor square block with the same support, head, and final letter. -/
private theorem derivesComponentToLongBlock
    {laws : List (Identity Nat)}
    (env : CollapseLawEnvironment laws)
    {head : Nat} {tail : List Nat}
    (connected :
      ConnectedComponentSupportConnected (head :: tail))
    (lengthAtLeastTwo : 2 ≤ (head :: tail).length) :
    Derives laws
      (maximalFactorWord (head :: tail))
      (maximalFactorWord
        (longBlock head (componentFinal (head :: tail))
          (connectedComponentSortedSupport (head :: tail)))) := by
  let S := connectedComponentSortedSupport (head :: tail)
  let f := componentFinal (head :: tail)
  have sorted : S.Pairwise (· ≤ ·) :=
    connectedComponentSortedSupport_sorted _
  have nodup : S.Nodup :=
    connectedComponentSortedSupport_nodup _
  have headMem : head ∈ S := by
    change head ∈ connectedComponentSortedSupport (head :: tail)
    rw [connectedComponentSortedSupport_mem_iff]
    simp
  have finalMem : f ∈ S := by
    change f ∈ connectedComponentSortedSupport (head :: tail)
    rw [connectedComponentSortedSupport_mem_iff]
    exact componentFinal_mem head tail
  have targetSupport :
      connectedComponentSortedSupport (longBlock head f S) = S :=
    longBlock_sortedSupport sorted nodup headMem finalMem
  have baseSignature :
      connectedComponentSignatureOfList (head :: tail) =
        connectedComponentSignatureOfList (longBlock head f S) := by
    apply baseSignature_eq_of_support_length_ge_two
      lengthAtLeastTwo (longBlock_length_ge_two head f S)
    rw [targetSupport]
  have exactSignature :
      connectedCutComponentSignatureOfList (head :: tail) =
        connectedCutComponentSignatureOfList (longBlock head f S) :=
    exactCutSignature_of_base_and_final baseSignature
      (by simp [f, longBlock_final])
  have targetShape :
      longBlock head f S =
        head :: (S.erase head ++
          (blockX head S ++ (blockY f S ++
            (blockY f S ++ (blockX head S ++
              (blockX head S ++
                (blockY f S ++ blockY f S))))))) := by
    simp [longBlock, blockX, List.cons_append]
  rw [targetShape]
  exact
    derivesComponentWords
      env.toFinalEraseLawEnvironment.toSwitchLawEnvironment
      connected
      (targetShape ▸ longBlock_connected headMem finalMem)
      (by
        rw [← targetShape]
        exact exactSignature)
      rfl

/-- One half of a `longBlock`.  Thus a long block is literally the square
of this four-factor word. -/
private def halfBlock (h f : Nat) (S : List Nat) : List Nat :=
  blockX h S ++
    (blockX h S ++ (blockY f S ++ blockY f S))

private theorem halfBlock_nonempty
    (h f : Nat) (S : List Nat) :
    halfBlock h f S ≠ [] := by
  simp [halfBlock, blockX]

private theorem longBlock_eq_halfBlock_square
    (h f : Nat) (S : List Nat) :
    longBlock h f S =
      halfBlock h f S ++ halfBlock h f S := by
  simp [longBlock, halfBlock, List.append_assoc]

private theorem maximalFactorWord_append_of_nonempty
    {left right : List Nat}
    (leftNonempty : left ≠ [])
    (rightNonempty : right ≠ []) :
    maximalFactorWord (left ++ right) =
      maximalFactorWord left ++ maximalFactorWord right := by
  have appendNonempty : left ++ right ≠ [] := by
    intro appendEmpty
    exact leftNonempty (List.append_eq_nil_iff.mp appendEmpty).1
  apply Word.toList_injective
  rw [Word.toList_append,
    maximalFactorWord_toList appendNonempty,
    maximalFactorWord_toList leftNonempty,
    maximalFactorWord_toList rightNonempty]

/-- Reverse use of the collapse law merges two adjacent square-normal
components.  The doubled intermediate is support-connected, so the frozen
component engine retargets it to the square-normal block on the union
support while retaining the outer head and final. -/
private theorem derivesMergeLongBlocks
    {laws : List (Identity Nat)}
    (env : CollapseLawEnvironment laws)
    {leftHead leftFinal rightHead rightFinal : Nat}
    {leftSupport rightSupport : List Nat}
    (leftSorted : leftSupport.Pairwise (· ≤ ·))
    (leftNodup : leftSupport.Nodup)
    (leftHeadMem : leftHead ∈ leftSupport)
    (leftFinalMem : leftFinal ∈ leftSupport)
    (rightSorted : rightSupport.Pairwise (· ≤ ·))
    (rightNodup : rightSupport.Nodup)
    (rightHeadMem : rightHead ∈ rightSupport)
    (rightFinalMem : rightFinal ∈ rightSupport) :
    Derives laws
      (maximalFactorWord
          (longBlock leftHead leftFinal leftSupport) ++
        maximalFactorWord
          (longBlock rightHead rightFinal rightSupport))
      (maximalFactorWord
        (longBlock leftHead rightFinal
          (connectedComponentSortedSupport
            (leftSupport ++ rightSupport)))) := by
  let leftHalf := halfBlock leftHead leftFinal leftSupport
  let rightHalf := halfBlock rightHead rightFinal rightSupport
  let leftBlock := longBlock leftHead leftFinal leftSupport
  let rightBlock := longBlock rightHead rightFinal rightSupport
  let pair := leftBlock ++ rightBlock
  let merged := pair ++ pair
  let unionSupport :=
    connectedComponentSortedSupport
      (leftSupport ++ rightSupport)
  have leftHalfNonempty : leftHalf ≠ [] :=
    halfBlock_nonempty leftHead leftFinal leftSupport
  have rightHalfNonempty : rightHalf ≠ [] :=
    halfBlock_nonempty rightHead rightFinal rightSupport
  have leftBlockNonempty : leftBlock ≠ [] := by
    simp [leftBlock, longBlock, blockX]
  have rightBlockNonempty : rightBlock ≠ [] := by
    simp [rightBlock, longBlock, blockX]
  have pairNonempty : pair ≠ [] := by
    intro pairEmpty
    exact leftBlockNonempty
      (List.append_eq_nil_iff.mp pairEmpty).1
  have leftWordSplit :
      maximalFactorWord leftBlock =
        maximalFactorWord leftHalf ++
          maximalFactorWord leftHalf := by
    change
      maximalFactorWord
          (longBlock leftHead leftFinal leftSupport) =
        maximalFactorWord
            (halfBlock leftHead leftFinal leftSupport) ++
          maximalFactorWord
            (halfBlock leftHead leftFinal leftSupport)
    rw [longBlock_eq_halfBlock_square]
    exact maximalFactorWord_append_of_nonempty
      leftHalfNonempty leftHalfNonempty
  have rightWordSplit :
      maximalFactorWord rightBlock =
        maximalFactorWord rightHalf ++
          maximalFactorWord rightHalf := by
    change
      maximalFactorWord
          (longBlock rightHead rightFinal rightSupport) =
        maximalFactorWord
            (halfBlock rightHead rightFinal rightSupport) ++
          maximalFactorWord
            (halfBlock rightHead rightFinal rightSupport)
    rw [longBlock_eq_halfBlock_square]
    exact maximalFactorWord_append_of_nonempty
      rightHalfNonempty rightHalfNonempty
  have pairWordSplit :
      maximalFactorWord pair =
        maximalFactorWord leftBlock ++
          maximalFactorWord rightBlock := by
    exact maximalFactorWord_append_of_nonempty
      leftBlockNonempty rightBlockNonempty
  have mergedWordSplit :
      maximalFactorWord merged =
        maximalFactorWord pair ++ maximalFactorWord pair := by
    exact maximalFactorWord_append_of_nonempty
      pairNonempty pairNonempty
  have expansion : Derives laws
      (maximalFactorWord leftBlock ++
        maximalFactorWord rightBlock)
      (maximalFactorWord merged) := by
    simpa only [mergedWordSplit, pairWordSplit, leftWordSplit,
      rightWordSplit, Word.append_assoc] using
      derivesMergeSquares env
        (maximalFactorWord leftHalf)
        (maximalFactorWord rightHalf)
  have leftBlockMem :
      ∀ tested, tested ∈ leftBlock ↔ tested ∈ leftSupport := by
    intro tested
    constructor
    · exact longBlock_subset leftHeadMem leftFinalMem tested
    · intro member
      change tested ∈
        longBlock leftHead leftFinal leftSupport
      simp only [longBlock, List.mem_append]
      exact Or.inl (blockX_full tested member)
  have rightBlockMem :
      ∀ tested, tested ∈ rightBlock ↔ tested ∈ rightSupport := by
    intro tested
    constructor
    · exact longBlock_subset rightHeadMem rightFinalMem tested
    · intro member
      change tested ∈
        longBlock rightHead rightFinal rightSupport
      simp only [longBlock, List.mem_append]
      exact Or.inl (blockX_full tested member)
  have pairMem :
      ∀ tested,
        tested ∈ pair ↔
          tested ∈ leftSupport ∨ tested ∈ rightSupport := by
    intro tested
    change
      tested ∈ leftBlock ++ rightBlock ↔
        tested ∈ leftSupport ∨ tested ∈ rightSupport
    rw [List.mem_append,
      leftBlockMem tested, rightBlockMem tested]
  have unionMem :
      ∀ tested,
        tested ∈ unionSupport ↔
          tested ∈ leftSupport ∨ tested ∈ rightSupport := by
    intro tested
    change
      tested ∈ connectedComponentSortedSupport
          (leftSupport ++ rightSupport) ↔
        tested ∈ leftSupport ∨ tested ∈ rightSupport
    rw [connectedComponentSortedSupport_mem_iff,
      List.mem_append]
  have pairFull :
      ∀ tested, tested ∈ unionSupport → tested ∈ pair := by
    intro tested member
    exact (pairMem tested).2 ((unionMem tested).1 member)
  have pairSubset :
      ∀ tested, tested ∈ pair → tested ∈ unionSupport := by
    intro tested member
    exact (unionMem tested).2 ((pairMem tested).1 member)
  have unionSorted : unionSupport.Pairwise (· ≤ ·) :=
    connectedComponentSortedSupport_sorted _
  have unionNodup : unionSupport.Nodup :=
    connectedComponentSortedSupport_nodup _
  have leftHeadUnion : leftHead ∈ unionSupport :=
    (unionMem leftHead).2 (Or.inl leftHeadMem)
  have rightFinalUnion : rightFinal ∈ unionSupport :=
    (unionMem rightFinal).2 (Or.inr rightFinalMem)
  have mergedSubset :
      ∀ tested, tested ∈ merged → tested ∈ unionSupport := by
    intro tested member
    rcases List.mem_append.mp member with inFirst | inSecond
    · exact pairSubset tested inFirst
    · exact pairSubset tested inSecond
  have mergedFull :
      ∀ tested, tested ∈ unionSupport → tested ∈ merged := by
    intro tested member
    exact List.mem_append_left pair (pairFull tested member)
  have mergedConnected :
      ConnectedComponentSupportConnected merged := by
    apply supportConnected_of_full_ends
      (S := unionSupport) (xpre := pair) (ysuf := pair)
    · exact ⟨pair, rfl⟩
    · exact ⟨pair, rfl⟩
    · simp only [merged, List.length_append]
      omega
    · exact pairFull
    · exact pairFull
    · exact mergedSubset
  have mergedSupport :
      connectedComponentSortedSupport merged = unionSupport :=
    block_sortedSupport unionSorted unionNodup
      leftHeadUnion rightFinalUnion mergedSubset mergedFull
  have targetSupport :
      connectedComponentSortedSupport
          (longBlock leftHead rightFinal unionSupport) =
        unionSupport :=
    longBlock_sortedSupport unionSorted unionNodup
      leftHeadUnion rightFinalUnion
  have mergedFinal :
      componentFinal merged = rightFinal := by
    change componentFinal (pair ++ pair) = rightFinal
    rw [componentFinal_append_of_right_nonempty
      pair pair pairNonempty]
    change componentFinal (leftBlock ++ rightBlock) = rightFinal
    rw [componentFinal_append_of_right_nonempty
      leftBlock rightBlock rightBlockNonempty]
    change componentFinal
      (longBlock rightHead rightFinal rightSupport) = rightFinal
    exact longBlock_final
  have mergedLength : 2 ≤ merged.length := by
    have pairPositive : 0 < pair.length :=
      List.length_pos_iff.mpr pairNonempty
    simp only [merged, List.length_append]
    omega
  have baseSignature :
      connectedComponentSignatureOfList merged =
        connectedComponentSignatureOfList
          (longBlock leftHead rightFinal unionSupport) :=
    baseSignature_eq_of_support_length_ge_two
      mergedLength
      (longBlock_length_ge_two
        leftHead rightFinal unionSupport)
      (mergedSupport.trans targetSupport.symm)
  have exactSignature :
      connectedCutComponentSignatureOfList merged =
        connectedCutComponentSignatureOfList
          (longBlock leftHead rightFinal unionSupport) :=
    exactCutSignature_of_base_and_final baseSignature
      (by rw [mergedFinal, longBlock_final])
  have mergedShape : ∃ tail, merged = leftHead :: tail := by
    refine ⟨leftSupport.erase leftHead ++
      (blockX leftHead leftSupport ++
        (blockY leftFinal leftSupport ++
          (blockY leftFinal leftSupport ++
            (blockX leftHead leftSupport ++
              (blockX leftHead leftSupport ++
                (blockY leftFinal leftSupport ++
                  blockY leftFinal leftSupport)))))) ++
      rightBlock ++ pair, ?_⟩
    simp [merged, pair, leftBlock, longBlock, blockX,
      List.cons_append, List.append_assoc]
  have targetShape :
      ∃ tail,
        longBlock leftHead rightFinal unionSupport =
          leftHead :: tail := by
    refine ⟨unionSupport.erase leftHead ++
      (blockX leftHead unionSupport ++
        (blockY rightFinal unionSupport ++
          (blockY rightFinal unionSupport ++
            (blockX leftHead unionSupport ++
              (blockX leftHead unionSupport ++
                (blockY rightFinal unionSupport ++
                  blockY rightFinal unionSupport)))))), ?_⟩
    simp [longBlock, blockX, List.cons_append]
  obtain ⟨mergedTail, mergedShape⟩ := mergedShape
  obtain ⟨targetTail, targetShape⟩ := targetShape
  have connector : Derives laws
      (maximalFactorWord merged)
      (maximalFactorWord
        (longBlock leftHead rightFinal unionSupport)) := by
    rw [mergedShape, targetShape]
    exact
      derivesComponentWords
        env.toFinalEraseLawEnvironment.toSwitchLawEnvironment
        (mergedShape ▸ mergedConnected)
        (targetShape ▸
          longBlock_connected leftHeadUnion rightFinalUnion)
        (by
          rw [← mergedShape, ← targetShape]
          exact exactSignature)
        rfl
  exact expansion.trans connector

private theorem headD_mem_of_nonempty
    {letters : List Nat} (nonempty : letters ≠ []) :
    letters.headD 0 ∈ letters := by
  obtain ⟨head, tail, rfl⟩ :=
    List.exists_cons_of_ne_nil nonempty
  simp

private theorem componentFinal_mem_of_nonempty
    {letters : List Nat} (nonempty : letters ≠ []) :
    componentFinal letters ∈ letters := by
  obtain ⟨head, tail, rfl⟩ :=
    List.exists_cons_of_ne_nil nonempty
  exact componentFinal_mem head tail

/-- Fold a nonempty chain of length-at-least-two support-connected
components to one square-normal block.  The outer head and final are those
of the whole flattened chain, while the support is the union support. -/
private theorem listDerivesComponentChainToLongBlock
    {laws : List (Identity Nat)}
    (env : CollapseLawEnvironment laws) :
    ∀ (components : List (List Nat)),
      components ≠ [] →
      (∀ component ∈ components, component ≠ []) →
      (∀ component ∈ components,
        ConnectedComponentSupportConnected component) →
      (∀ component ∈ components, 2 ≤ component.length) →
      S5_107.ListDerives laws components.flatten
        (longBlock (components.flatten.headD 0)
          (componentFinal components.flatten)
          (connectedComponentSortedSupport components.flatten))
  | [], componentsNonempty, _, _, _ =>
      False.elim (componentsNonempty rfl)
  | component :: rest, _, allNonempty, allConnected, allLength => by
      have componentNonempty : component ≠ [] :=
        allNonempty component (by simp)
      obtain ⟨head, tail, componentShape⟩ :=
        List.exists_cons_of_ne_nil componentNonempty
      subst component
      have componentConnected :
          ConnectedComponentSupportConnected (head :: tail) :=
        allConnected (head :: tail) (by simp)
      have componentLength :
          2 ≤ (head :: tail).length :=
        allLength (head :: tail) (by simp)
      have componentWordDerivation :=
        derivesComponentToLongBlock env
          componentConnected componentLength
      have componentListDerivation :=
        S5_107.ListDerives.ofWord componentWordDerivation
      rw [maximalFactorWord_toList (by simp),
        maximalFactorWord_toList
          (by simp [longBlock, blockX])]
        at componentListDerivation
      cases rest with
      | nil =>
          simpa [List.flatten_cons] using
            componentListDerivation
      | cons next remaining =>
          let restComponents := next :: remaining
          let restLetters := restComponents.flatten
          have restComponentsNonempty : restComponents ≠ [] := by
            simp [restComponents]
          have nextNonempty : next ≠ [] :=
            allNonempty next (by simp)
          have restLettersNonempty : restLetters ≠ [] := by
            intro restEmpty
            change (next :: remaining).flatten = [] at restEmpty
            rw [List.flatten_cons] at restEmpty
            exact
              nextNonempty
                (List.append_eq_nil_iff.mp restEmpty).1
          have restDerivation :=
            listDerivesComponentChainToLongBlock env
              restComponents restComponentsNonempty
              (fun current member => by
                change
                  List.Mem current (next :: remaining) at member
                exact
                  allNonempty current
                    (List.Mem.tail (head :: tail) member))
              (fun current member => by
                change
                  List.Mem current (next :: remaining) at member
                exact
                  allConnected current
                    (List.Mem.tail (head :: tail) member))
              (fun current member => by
                change
                  List.Mem current (next :: remaining) at member
                exact
                  allLength current
                    (List.Mem.tail (head :: tail) member))
          let leftSupport :=
            connectedComponentSortedSupport (head :: tail)
          let rightSupport :=
            connectedComponentSortedSupport restLetters
          let leftFinal := componentFinal (head :: tail)
          let rightHead := restLetters.headD 0
          let rightFinal := componentFinal restLetters
          let leftBlock :=
            longBlock head leftFinal leftSupport
          let rightBlock :=
            longBlock rightHead rightFinal rightSupport
          have leftSorted : leftSupport.Pairwise (· ≤ ·) :=
            connectedComponentSortedSupport_sorted _
          have leftNodup : leftSupport.Nodup :=
            connectedComponentSortedSupport_nodup _
          have rightSorted : rightSupport.Pairwise (· ≤ ·) :=
            connectedComponentSortedSupport_sorted _
          have rightNodup : rightSupport.Nodup :=
            connectedComponentSortedSupport_nodup _
          have headMem : head ∈ leftSupport := by
            change
              head ∈
                connectedComponentSortedSupport (head :: tail)
            exact
              (connectedComponentSortedSupport_mem_iff
                head (head :: tail)).2 (by simp)
          have leftFinalMem : leftFinal ∈ leftSupport := by
            change
              componentFinal (head :: tail) ∈
                connectedComponentSortedSupport (head :: tail)
            exact
              (connectedComponentSortedSupport_mem_iff
                (componentFinal (head :: tail))
                (head :: tail)).2
                  (componentFinal_mem_of_nonempty (by simp))
          have rightHeadMem : rightHead ∈ rightSupport := by
            change
              restLetters.headD 0 ∈
                connectedComponentSortedSupport restLetters
            exact
              (connectedComponentSortedSupport_mem_iff
                (restLetters.headD 0) restLetters).2
                  (headD_mem_of_nonempty restLettersNonempty)
          have rightFinalMem : rightFinal ∈ rightSupport := by
            change
              componentFinal restLetters ∈
                connectedComponentSortedSupport restLetters
            exact
              (connectedComponentSortedSupport_mem_iff
                (componentFinal restLetters) restLetters).2
                  (componentFinal_mem_of_nonempty
                    restLettersNonempty)
          have normalizeFirst :
              S5_107.ListDerives laws
                ((head :: tail) ++ restLetters)
                (leftBlock ++ restLetters) := by
            simpa [leftBlock, leftSupport, leftFinal] using
              S5_107.ListDerives.append
                componentListDerivation restLetters
          have normalizeRest :
              S5_107.ListDerives laws
                (leftBlock ++ restLetters)
                (leftBlock ++ rightBlock) := by
            simpa [rightBlock, rightSupport,
              rightHead, rightFinal] using
              S5_107.ListDerives.prepend
                leftBlock restDerivation
          have mergeWord :=
            derivesMergeLongBlocks env
              leftSorted leftNodup headMem leftFinalMem
              rightSorted rightNodup
              rightHeadMem rightFinalMem
          have leftBlockNonempty : leftBlock ≠ [] := by
            simp [leftBlock, longBlock, blockX]
          have rightBlockNonempty : rightBlock ≠ [] := by
            simp [rightBlock, longBlock, blockX]
          have unionBlockNonempty :
              longBlock head rightFinal
                  (connectedComponentSortedSupport
                    (leftSupport ++ rightSupport)) ≠ [] := by
            simp [longBlock, blockX]
          have merge :
              S5_107.ListDerives laws
                (leftBlock ++ rightBlock)
                (longBlock head rightFinal
                  (connectedComponentSortedSupport
                    (leftSupport ++ rightSupport))) := by
            have asLists :=
              S5_107.ListDerives.ofWord mergeWord
            simpa only [Word.toList_append,
              maximalFactorWord_toList leftBlockNonempty,
              maximalFactorWord_toList rightBlockNonempty,
              maximalFactorWord_toList unionBlockNonempty]
              using asLists
          have unionSupportEq :
              connectedComponentSortedSupport
                  (leftSupport ++ rightSupport) =
                connectedComponentSortedSupport
                  ((head :: tail) ++ restLetters) := by
            apply sorted_nodup_ext
              (connectedComponentSortedSupport_sorted _)
              (connectedComponentSortedSupport_sorted _)
              (connectedComponentSortedSupport_nodup _)
              (connectedComponentSortedSupport_nodup _)
            intro tested
            change
              tested ∈
                  connectedComponentSortedSupport
                    (connectedComponentSortedSupport
                        (head :: tail) ++
                      connectedComponentSortedSupport
                        restLetters) ↔
                tested ∈
                  connectedComponentSortedSupport
                    ((head :: tail) ++ restLetters)
            simp only [
              connectedComponentSortedSupport_mem_iff,
              List.mem_append]
          have finalEq :
              componentFinal ((head :: tail) ++ restLetters) =
                rightFinal := by
            change
              componentFinal ((head :: tail) ++ restLetters) =
                componentFinal restLetters
            exact
              componentFinal_append_of_right_nonempty
                (head :: tail) restLetters
                restLettersNonempty
          have combined :=
            normalizeFirst.trans (normalizeRest.trans merge)
          change
            S5_107.ListDerives laws
              ((head :: tail) ++ restLetters)
              (longBlock head
                (componentFinal
                  ((head :: tail) ++ restLetters))
                (connectedComponentSortedSupport
                  ((head :: tail) ++ restLetters)))
          rw [finalEq, ← unionSupportEq]
          exact combined

/-- Every nonempty deterministic exact-cut gap derives to one square-normal
component with the same whole-gap support, head, and final.  The scanner's
no-exact-cut theorem supplies the essential length-at-least-two hypothesis
for every connected component in the gap. -/
private theorem listDerivesExactCutGapToLongBlock
    {laws : List (Identity Nat)}
    (env : CollapseLawEnvironment laws)
    {letters : List Nat}
    {segment : SemigroupBasis.CoRoots.S5_441.ExactCutSegment}
    (segmentMember :
      segment ∈
        SemigroupBasis.CoRoots.S5_441.exactCutDecomposition
          letters)
    (gapNonempty : segment.gap ≠ []) :
    S5_107.ListDerives laws segment.gap
      (longBlock (segment.gap.headD 0)
        (componentFinal segment.gap)
        (connectedComponentSortedSupport segment.gap)) := by
  let components :=
    connectedComponentDecomposeList segment.gap
  have componentsNonempty : components ≠ [] := by
    simpa [components] using
      connectedComponentDecomposeList_nonempty gapNonempty
  rcases componentsShape : components with _ | ⟨first, rest⟩
  · exact False.elim (componentsNonempty componentsShape)
  have allNonempty :
      ∀ component ∈ first :: rest, component ≠ [] := by
    intro component member
    apply
      connectedComponentDecomposeList_nonempty_components
        segment.gap component
    change component ∈ components
    rw [componentsShape]
    exact member
  have allConnected :
      ∀ component ∈ first :: rest,
        ConnectedComponentSupportConnected component := by
    intro component member
    apply
      connectedComponentDecomposeList_supportConnected
        segment.gap component
    change component ∈ components
    rw [componentsShape]
    exact member
  have allLength :
      ∀ component ∈ first :: rest,
        2 ≤ component.length := by
    intro component member
    apply
      SemigroupBasis.CoRoots.S5_441.exactCutDecomposition_gap_component_length_ge_two
        segmentMember
    change component ∈ components
    rw [componentsShape]
    exact member
  have chain :=
    listDerivesComponentChainToLongBlock env
      (first :: rest) (by simp)
      allNonempty allConnected allLength
  have flattenEq : (first :: rest).flatten = segment.gap := by
    rw [← componentsShape]
    simpa [components] using
      connectedComponentDecomposeList_flatten segment.gap
  rw [flattenEq] at chain
  exact chain

/-- Retarget one square-normal gap inside arbitrary list contexts.  At the
left boundary its head must be preserved, and at the right boundary its
final must be preserved; in the three contextual cases the switch and
final-erasure bridges forget exactly the available endpoint coordinates. -/
private theorem listDerivesRetargetLongBlockInContext
    {laws : List (Identity Nat)}
    (env : CollapseLawEnvironment laws)
    {pre suffix support : List Nat}
    {sourceHead sourceFinal targetHead targetFinal : Nat}
    (sorted : support.Pairwise (· ≤ ·))
    (nodup : support.Nodup)
    (sourceHeadMem : sourceHead ∈ support)
    (sourceFinalMem : sourceFinal ∈ support)
    (targetHeadMem : targetHead ∈ support)
    (targetFinalMem : targetFinal ∈ support)
    (headBoundary :
      pre = [] → sourceHead = targetHead)
    (finalBoundary :
      suffix = [] → sourceFinal = targetFinal) :
  S5_107.ListDerives laws
      (pre ++
        longBlock sourceHead sourceFinal support ++ suffix)
      (pre ++
        longBlock targetHead targetFinal support ++ suffix) := by
  let sourceBlock :=
    longBlock sourceHead sourceFinal support
  let targetBlock :=
    longBlock targetHead targetFinal support
  have sourceNonempty : sourceBlock ≠ [] := by
    simp [sourceBlock, longBlock, blockX]
  have targetNonempty : targetBlock ≠ [] := by
    simp [targetBlock, longBlock, blockX]
  have sourceSupport :
      connectedComponentSortedSupport sourceBlock = support := by
    exact
      longBlock_sortedSupport sorted nodup
        sourceHeadMem sourceFinalMem
  have targetSupport :
      connectedComponentSortedSupport targetBlock = support := by
    exact
      longBlock_sortedSupport sorted nodup
        targetHeadMem targetFinalMem
  have baseSignature :
      connectedComponentSignatureOfList sourceBlock =
        connectedComponentSignatureOfList targetBlock :=
    baseSignature_eq_of_support_length_ge_two
      (longBlock_length_ge_two
        sourceHead sourceFinal support)
      (longBlock_length_ge_two
        targetHead targetFinal support)
      (sourceSupport.trans targetSupport.symm)
  have exactSignatureOfFinal
      (finalEq : sourceFinal = targetFinal) :
      connectedCutComponentSignatureOfList sourceBlock =
        connectedCutComponentSignatureOfList targetBlock :=
    exactCutSignature_of_base_and_final baseSignature
      (by
        simpa only [sourceBlock, targetBlock, longBlock_final]
          using finalEq)
  have sourceConnected :
      ConnectedComponentSupportConnected sourceBlock :=
    longBlock_connected sourceHeadMem sourceFinalMem
  have targetConnected :
      ConnectedComponentSupportConnected targetBlock :=
    longBlock_connected targetHeadMem targetFinalMem
  have sourceShape : ∃ tail, sourceBlock = sourceHead :: tail := by
    refine ⟨support.erase sourceHead ++
      (blockX sourceHead support ++
        (blockY sourceFinal support ++
          (blockY sourceFinal support ++
            (blockX sourceHead support ++
              (blockX sourceHead support ++
                (blockY sourceFinal support ++
                  blockY sourceFinal support)))))), ?_⟩
    simp [sourceBlock, longBlock, blockX, List.cons_append]
  have targetShape : ∃ tail, targetBlock = targetHead :: tail := by
    refine ⟨support.erase targetHead ++
      (blockX targetHead support ++
        (blockY targetFinal support ++
          (blockY targetFinal support ++
            (blockX targetHead support ++
              (blockX targetHead support ++
                (blockY targetFinal support ++
                  blockY targetFinal support)))))), ?_⟩
    simp [targetBlock, longBlock, blockX, List.cons_append]
  obtain ⟨sourceTail, sourceShape⟩ := sourceShape
  obtain ⟨targetTail, targetShape⟩ := targetShape
  cases pre with
  | nil =>
      have heads : sourceHead = targetHead :=
        headBoundary rfl
      cases suffix with
      | nil =>
          have finals : sourceFinal = targetFinal :=
            finalBoundary rfl
          have wordDerivation :
              Derives laws
                (maximalFactorWord sourceBlock)
                (maximalFactorWord targetBlock) := by
            rw [sourceShape, targetShape]
            exact
              derivesComponentWords
                env.toFinalEraseLawEnvironment.toSwitchLawEnvironment
                (sourceShape ▸ sourceConnected)
                (targetShape ▸ targetConnected)
                (by
                  rw [← sourceShape, ← targetShape]
                  exact exactSignatureOfFinal finals)
                heads
          have asLists :=
            S5_107.ListDerives.ofWord wordDerivation
          simpa only [List.nil_append, List.append_nil,
            maximalFactorWord_toList sourceNonempty,
            maximalFactorWord_toList targetNonempty] using asLists
      | cons suffixHead suffixTail =>
          let suffixWord :=
            S5_107.listWordOfCons suffixHead suffixTail
          have wordDerivation :
              Derives laws
                (maximalFactorWord sourceBlock ++ suffixWord)
                (maximalFactorWord targetBlock ++ suffixWord) := by
            rw [sourceShape, targetShape]
            exact
              derivesInteriorComponentSameHead
                env.toFinalEraseLawEnvironment suffixWord
                (sourceShape ▸ sourceConnected)
                (targetShape ▸ targetConnected)
                (by
                  rw [← sourceShape, ← targetShape]
                  exact baseSignature)
                heads
          have asLists :=
            S5_107.ListDerives.ofWord wordDerivation
          simpa [sourceBlock, targetBlock, suffixWord,
            S5_107.listWordOfCons, Word.toList_append,
            maximalFactorWord_toList sourceNonempty,
            maximalFactorWord_toList targetNonempty,
            List.append_assoc] using asLists
  | cons prefixHead prefixTail =>
      let prefixWord :=
        S5_107.listWordOfCons prefixHead prefixTail
      cases suffix with
      | nil =>
          have finals : sourceFinal = targetFinal :=
            finalBoundary rfl
          have wordDerivation :
              Derives laws
                (prefixWord ++ maximalFactorWord sourceBlock)
                (prefixWord ++ maximalFactorWord targetBlock) := by
            rw [sourceShape, targetShape]
            exact
              derivesComponentSwitchWords
                env.toFinalEraseLawEnvironment.toSwitchLawEnvironment
                prefixWord
                (sourceShape ▸ sourceConnected)
                (targetShape ▸ targetConnected)
                (by
                  rw [← sourceShape, ← targetShape]
                  exact exactSignatureOfFinal finals)
          have asLists :=
            S5_107.ListDerives.ofWord wordDerivation
          simpa [sourceBlock, targetBlock, prefixWord,
            S5_107.listWordOfCons, Word.toList_append,
            maximalFactorWord_toList sourceNonempty,
            maximalFactorWord_toList targetNonempty,
            List.append_assoc] using asLists
      | cons suffixHead suffixTail =>
          let suffixWord :=
            S5_107.listWordOfCons suffixHead suffixTail
          have wordDerivation :
              Derives laws
                ((prefixWord ++ maximalFactorWord sourceBlock) ++
                  suffixWord)
                ((prefixWord ++ maximalFactorWord targetBlock) ++
                  suffixWord) := by
            rw [sourceShape, targetShape]
            exact
              derivesInteriorComponentBehindGuard
                env.toFinalEraseLawEnvironment
                prefixWord suffixWord
                (sourceShape ▸ sourceConnected)
                (targetShape ▸ targetConnected)
                (by
                  rw [← sourceShape, ← targetShape]
                  exact baseSignature)
          have asLists :=
            S5_107.ListDerives.ofWord wordDerivation
          simpa [sourceBlock, targetBlock,
            prefixWord, suffixWord,
            S5_107.listWordOfCons, Word.toList_append,
            maximalFactorWord_toList sourceNonempty,
            maximalFactorWord_toList targetNonempty,
            List.append_assoc] using asLists

private abbrev C06CutSegment :=
  SemigroupBasis.CoRoots.S5_441.ExactCutSegment

private def c06RetainCutSegment
    (segment : C06CutSegment) : Bool :=
  decide (¬ (segment.gap = [] ∧ segment.separator = none))

private def c06RetainedCutSegments
    (segments : List C06CutSegment) : List C06CutSegment :=
  segments.filter c06RetainCutSegment

private theorem render_c06RetainedCutSegments
    (segments : List C06CutSegment) :
    SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
        (c06RetainedCutSegments segments) =
      SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
        segments := by
  induction segments with
  | nil => rfl
  | cons segment remaining induction =>
      unfold c06RetainedCutSegments at induction
      by_cases omitted :
          segment.gap = [] ∧ segment.separator = none
      · simp [c06RetainedCutSegments, c06RetainCutSegment,
          omitted,
          SemigroupBasis.CoRoots.S5_441.ExactCutSegment.render,
          induction]
      · simp [c06RetainedCutSegments, c06RetainCutSegment,
          omitted, induction]

private theorem c06SupportSegments_eq_map_retained
    (segments : List C06CutSegment) :
    SemigroupBasis.CoRoots.S5_441.exactCutSupportSegments
        segments =
      (c06RetainedCutSegments segments).map
        SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment := by
  induction segments with
  | nil => rfl
  | cons segment remaining induction =>
      unfold c06RetainedCutSegments at induction
      unfold
        SemigroupBasis.CoRoots.S5_441.exactCutSupportSegments
        at induction
      by_cases omitted :
          segment.gap = [] ∧ segment.separator = none
      · simp [c06RetainedCutSegments, c06RetainCutSegment,
          SemigroupBasis.CoRoots.S5_441.exactCutSupportSegments,
          SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment?,
          omitted, induction]
      · simp [c06RetainedCutSegments, c06RetainCutSegment,
          SemigroupBasis.CoRoots.S5_441.exactCutSupportSegments,
          SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment?,
          omitted, induction]

private theorem c06RetainedCutSegments_member
    {segment : C06CutSegment}
    {segments : List C06CutSegment}
    (member : segment ∈ c06RetainedCutSegments segments) :
    segment ∈ segments :=
  (List.mem_filter.mp member).1

private theorem c06RetainedCutSegments_retained
    {segment : C06CutSegment}
    {segments : List C06CutSegment}
    (member : segment ∈ c06RetainedCutSegments segments) :
    ¬ (segment.gap = [] ∧ segment.separator = none) :=
  of_decide_eq_true (List.mem_filter.mp member).2

private theorem c06CutSegment_render_nonempty_of_retained
    {segment : C06CutSegment}
    (retained :
      ¬ (segment.gap = [] ∧ segment.separator = none)) :
    segment.render ≠ [] := by
  intro renderEmpty
  change segment.gap ++ segment.separator.toList = [] at renderEmpty
  have emptyParts := List.append_eq_nil_iff.mp renderEmpty
  have gapEmpty : segment.gap = [] := emptyParts.1
  have separatorEmpty : segment.separator.toList = [] := emptyParts.2
  have separatorNone : segment.separator = none := by
    cases separatorShape : segment.separator with
    | none => rfl
    | some separator =>
        simp [separatorShape] at separatorEmpty
  exact retained ⟨gapEmpty, separatorNone⟩

private theorem c06RetainedSegment_render_nonempty
    {segment : C06CutSegment}
    {segments : List C06CutSegment}
    (member : segment ∈ c06RetainedCutSegments segments) :
    segment.render ≠ [] :=
  c06CutSegment_render_nonempty_of_retained
    (c06RetainedCutSegments_retained member)

private theorem exactCutGap_final_eq_whole
    {letters : List Nat} {segment : C06CutSegment}
    (segmentMember :
      segment ∈
        SemigroupBasis.CoRoots.S5_441.exactCutDecomposition
          letters)
    (gapNonempty : segment.gap ≠ [])
    (separatorNone : segment.separator = none) :
    componentFinal segment.gap = componentFinal letters := by
  obtain ⟨before, after, decompositionEq⟩ :=
    List.mem_iff_append.mp segmentMember
  have afterEmpty :
      after = [] :=
    (SemigroupBasis.CoRoots.S5_441.exactCutDecomposition_separator_none_iff_after_nil
        decompositionEq).mp separatorNone
  have rendered :=
    SemigroupBasis.CoRoots.S5_441.render_exactCutDecomposition
      letters
  rw [decompositionEq, afterEmpty] at rendered
  have renderedFinal :
      SemigroupBasis.CoRoots.S5_441.renderExactCutSegments before ++
          segment.gap =
        letters := by
    simpa [
      SemigroupBasis.CoRoots.S5_441.renderExactCutSegments,
      SemigroupBasis.CoRoots.S5_441.ExactCutSegment.render,
      List.flatMap_append, separatorNone] using rendered
  rw [← renderedFinal]
  exact componentFinal_append_of_right_nonempty
    (SemigroupBasis.CoRoots.S5_441.renderExactCutSegments before)
    segment.gap gapNonempty |>.symm

private theorem word_head_eq_toList_headD (word : Word Nat) :
    word.head = word.toList.headD 0 := by
  cases word
  rfl

private theorem renderExactCutSegments_cons_headD
    {segment : C06CutSegment} {remaining : List C06CutSegment}
    (gapNonempty : segment.gap ≠ []) :
    (SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
        (segment :: remaining)).headD 0 =
      segment.gap.headD 0 := by
  cases segment with
  | mk gap separator =>
      obtain ⟨head, tail, rfl⟩ :=
        List.exists_cons_of_ne_nil gapNonempty
      simp [
        SemigroupBasis.CoRoots.S5_441.renderExactCutSegments_cons,
        SemigroupBasis.CoRoots.S5_441.ExactCutSegment.render]

private theorem option_eq_none_of_toList_eq_nil
    {value : Option Nat} (empty : value.toList = []) :
    value = none := by
  cases value with
  | none => rfl
  | some entry =>
      simp at empty

/-- Align retained exact-cut segments from left to right.  The already
aligned prefix provides the left guard; the current separator and unaligned
tail provide the right guard.  Thus only the first gap needs the global
head coordinate and only the final gap needs the global final coordinate. -/
private theorem assembleC06RetainedSegments
    {laws : List (Identity Nat)}
    (env : CollapseLawEnvironment laws)
    (left right : Word Nat)
    (wholeHeads : left.head = right.head)
    (wholeFinals :
      componentFinal left.toList = componentFinal right.toList) :
    ∀ (leftSegments rightSegments : List C06CutSegment)
      (pre : List Nat),
      (∀ segment, segment ∈ leftSegments →
        segment ∈
          SemigroupBasis.CoRoots.S5_441.exactCutDecomposition
            left.toList) →
      (∀ segment, segment ∈ rightSegments →
        segment ∈
          SemigroupBasis.CoRoots.S5_441.exactCutDecomposition
            right.toList) →
      (∀ segment, segment ∈ leftSegments →
        ¬ (segment.gap = [] ∧ segment.separator = none)) →
      (∀ segment, segment ∈ rightSegments →
        ¬ (segment.gap = [] ∧ segment.separator = none)) →
      leftSegments.map
          SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment =
        rightSegments.map
          SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment →
      (pre = [] →
        left.toList =
            SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
              leftSegments ∧
          right.toList =
            SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
              rightSegments) →
      S5_107.ListDerives laws
        (pre ++
          SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
            leftSegments)
        (pre ++
          SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
            rightSegments)
  | [], [], pre, _, _, _, _, _, _ => by
      simpa using
        (S5_107.ListDerives.refl (basis := laws) pre)
  | [], _ :: _, _, _, _, _, _, supportEq, _ => by
      simp at supportEq
  | _ :: _, [], _, _, _, _, _, supportEq, _ => by
      simp at supportEq
  | leftSegment :: leftRemaining,
      rightSegment :: rightRemaining,
      pre, leftMembers, rightMembers,
      leftRetained, rightRetained,
      supportSegmentsEq, fullRender => by
      simp only [List.map_cons, List.cons.injEq]
        at supportSegmentsEq
      have supportSegmentEq := supportSegmentsEq.1
      have tailSupportSegmentsEq := supportSegmentsEq.2
      have leftSegmentMember :=
        leftMembers leftSegment (by simp)
      have rightSegmentMember :=
        rightMembers rightSegment (by simp)
      have leftSegmentRetained :=
        leftRetained leftSegment (by simp)
      have rightSegmentRetained :=
        rightRetained rightSegment (by simp)
      have supportEq :
          connectedComponentSortedSupport leftSegment.gap =
            connectedComponentSortedSupport rightSegment.gap :=
        congrArg
          UniqueSeparatorCanonicalSegment.quadratic
          supportSegmentEq
      have separatorEq :
          leftSegment.separator = rightSegment.separator :=
        congrArg
          UniqueSeparatorCanonicalSegment.separator
          supportSegmentEq
      by_cases leftGapEmpty : leftSegment.gap = []
      · have rightGapEmpty : rightSegment.gap = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro tested rightGapMember
          have rightSupportMember :
              tested ∈
                connectedComponentSortedSupport
                  rightSegment.gap :=
            (connectedComponentSortedSupport_mem_iff
              tested rightSegment.gap).2 rightGapMember
          rw [← supportEq] at rightSupportMember
          have leftGapMember : tested ∈ leftSegment.gap :=
            (connectedComponentSortedSupport_mem_iff
              tested leftSegment.gap).1 rightSupportMember
          simpa [leftGapEmpty] using leftGapMember
        have segmentRenderEq :
            leftSegment.render = rightSegment.render := by
          simp [
            SemigroupBasis.CoRoots.S5_441.ExactCutSegment.render,
            leftGapEmpty, rightGapEmpty, separatorEq]
        have rightRenderNonempty :
            rightSegment.render ≠ [] :=
          c06CutSegment_render_nonempty_of_retained
            rightSegmentRetained
        have tailDerivation :=
          assembleC06RetainedSegments env left right
            wholeHeads wholeFinals
            leftRemaining rightRemaining
            (pre ++ rightSegment.render)
            (fun segment member =>
              leftMembers segment
                (List.Mem.tail leftSegment member))
            (fun segment member =>
              rightMembers segment
                (List.Mem.tail rightSegment member))
            (fun segment member =>
              leftRetained segment
                (List.Mem.tail leftSegment member))
            (fun segment member =>
              rightRetained segment
                (List.Mem.tail rightSegment member))
            tailSupportSegmentsEq
            (fun prefixedEmpty =>
              False.elim <|
                rightRenderNonempty
                  (List.append_eq_nil_iff.mp prefixedEmpty).2)
        simpa [
          SemigroupBasis.CoRoots.S5_441.renderExactCutSegments_cons,
          segmentRenderEq, List.append_assoc] using tailDerivation
      · have rightGapNonempty : rightSegment.gap ≠ [] := by
          intro rightGapEmpty
          obtain ⟨tested, testedMember⟩ :=
            List.exists_mem_of_ne_nil
              leftSegment.gap leftGapEmpty
          have leftSupportMember :
              tested ∈
                connectedComponentSortedSupport
                  leftSegment.gap :=
            (connectedComponentSortedSupport_mem_iff
              tested leftSegment.gap).2 testedMember
          rw [supportEq] at leftSupportMember
          have rightGapMember : tested ∈ rightSegment.gap :=
            (connectedComponentSortedSupport_mem_iff
              tested rightSegment.gap).1 leftSupportMember
          exact (List.ne_nil_of_mem rightGapMember)
            rightGapEmpty
        have supportSorted :
            (connectedComponentSortedSupport
              leftSegment.gap).Pairwise (· ≤ ·) :=
          connectedComponentSortedSupport_sorted _
        have supportNodup :
            (connectedComponentSortedSupport
              leftSegment.gap).Nodup :=
          connectedComponentSortedSupport_nodup _
        have leftHeadMem :
            leftSegment.gap.headD 0 ∈
              connectedComponentSortedSupport
                leftSegment.gap := by
          rw [connectedComponentSortedSupport_mem_iff]
          exact headD_mem_of_nonempty leftGapEmpty
        have leftFinalMem :
            componentFinal leftSegment.gap ∈
              connectedComponentSortedSupport
                leftSegment.gap := by
          rw [connectedComponentSortedSupport_mem_iff]
          exact componentFinal_mem_of_nonempty leftGapEmpty
        have rightHeadMem :
            rightSegment.gap.headD 0 ∈
              connectedComponentSortedSupport
                leftSegment.gap := by
          rw [supportEq,
            connectedComponentSortedSupport_mem_iff]
          exact headD_mem_of_nonempty rightGapNonempty
        have rightFinalMem :
            componentFinal rightSegment.gap ∈
              connectedComponentSortedSupport
                leftSegment.gap := by
          rw [supportEq,
            connectedComponentSortedSupport_mem_iff]
          exact componentFinal_mem_of_nonempty
            rightGapNonempty
        have leftGapNormalization :=
          listDerivesExactCutGapToLongBlock env
            leftSegmentMember leftGapEmpty
        have rightGapNormalization :=
          listDerivesExactCutGapToLongBlock env
            rightSegmentMember rightGapNonempty
        have rightGapNormalizationCommon :
            S5_107.ListDerives laws rightSegment.gap
              (longBlock
                (rightSegment.gap.headD 0)
                (componentFinal rightSegment.gap)
                (connectedComponentSortedSupport
                  leftSegment.gap)) := by
          simpa only [supportEq] using
            rightGapNormalization
        let suffix :=
          leftSegment.separator.toList ++
            SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
              leftRemaining
        have normalizeLeft :
            S5_107.ListDerives laws
              (pre ++ leftSegment.gap ++ suffix)
              (pre ++
                longBlock
                  (leftSegment.gap.headD 0)
                  (componentFinal leftSegment.gap)
                  (connectedComponentSortedSupport
                    leftSegment.gap) ++ suffix) :=
          S5_107.ListDerives.context pre suffix
            leftGapNormalization
        have retarget :
            S5_107.ListDerives laws
              (pre ++
                longBlock
                  (leftSegment.gap.headD 0)
                  (componentFinal leftSegment.gap)
                  (connectedComponentSortedSupport
                    leftSegment.gap) ++ suffix)
              (pre ++
                longBlock
                  (rightSegment.gap.headD 0)
                  (componentFinal rightSegment.gap)
                  (connectedComponentSortedSupport
                    leftSegment.gap) ++ suffix) := by
          apply
            listDerivesRetargetLongBlockInContext env
              supportSorted supportNodup
              leftHeadMem leftFinalMem
              rightHeadMem rightFinalMem
          · intro prefixEmpty
            have renders := fullRender prefixEmpty
            have leftGapHead :
                leftSegment.gap.headD 0 = left.head := by
              calc
                leftSegment.gap.headD 0 =
                    (SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
                      (leftSegment :: leftRemaining)).headD 0 :=
                  (renderExactCutSegments_cons_headD
                    leftGapEmpty).symm
                _ = left.toList.headD 0 :=
                  congrArg (fun letters => letters.headD 0)
                    renders.1.symm
                _ = left.head :=
                  (word_head_eq_toList_headD left).symm
            have rightGapHead :
                rightSegment.gap.headD 0 = right.head := by
              calc
                rightSegment.gap.headD 0 =
                    (SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
                      (rightSegment :: rightRemaining)).headD 0 :=
                  (renderExactCutSegments_cons_headD
                    rightGapNonempty).symm
                _ = right.toList.headD 0 :=
                  congrArg (fun letters => letters.headD 0)
                    renders.2.symm
                _ = right.head :=
                  (word_head_eq_toList_headD right).symm
            exact leftGapHead.trans <|
              wholeHeads.trans rightGapHead.symm
          · intro suffixEmpty
            have separatorListEmpty :
                leftSegment.separator.toList = [] :=
              (List.append_eq_nil_iff.mp (by
                simpa [suffix] using suffixEmpty)).1
            have leftSeparatorNone :
                leftSegment.separator = none :=
              option_eq_none_of_toList_eq_nil
                separatorListEmpty
            have rightSeparatorNone :
                rightSegment.separator = none := by
              rw [← separatorEq]
              exact leftSeparatorNone
            have leftGapFinal :
                componentFinal leftSegment.gap =
                  componentFinal left.toList :=
              exactCutGap_final_eq_whole
                leftSegmentMember leftGapEmpty
                leftSeparatorNone
            have rightGapFinal :
                componentFinal rightSegment.gap =
                  componentFinal right.toList :=
              exactCutGap_final_eq_whole
                rightSegmentMember rightGapNonempty
                rightSeparatorNone
            exact leftGapFinal.trans <|
              wholeFinals.trans rightGapFinal.symm
        have denormalizeRight :
            S5_107.ListDerives laws
              (pre ++
                longBlock
                  (rightSegment.gap.headD 0)
                  (componentFinal rightSegment.gap)
                  (connectedComponentSortedSupport
                    leftSegment.gap) ++ suffix)
              (pre ++ rightSegment.gap ++ suffix) :=
          S5_107.ListDerives.context pre suffix
            rightGapNormalizationCommon.symm
        have currentSegmentStep :
            S5_107.ListDerives laws
              (pre ++
                leftSegment.render ++
                SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
                  leftRemaining)
              (pre ++
                rightSegment.render ++
                SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
                  leftRemaining) := by
          have combined :=
            normalizeLeft.trans
              (retarget.trans denormalizeRight)
          simpa [suffix,
            SemigroupBasis.CoRoots.S5_441.ExactCutSegment.render,
            separatorEq, List.append_assoc] using combined
        have rightRenderNonempty :
            rightSegment.render ≠ [] :=
          c06CutSegment_render_nonempty_of_retained
            rightSegmentRetained
        have tailDerivation :=
          assembleC06RetainedSegments env left right
            wholeHeads wholeFinals
            leftRemaining rightRemaining
            (pre ++ rightSegment.render)
            (fun segment member =>
              leftMembers segment
                (List.Mem.tail leftSegment member))
            (fun segment member =>
              rightMembers segment
                (List.Mem.tail rightSegment member))
            (fun segment member =>
              leftRetained segment
                (List.Mem.tail leftSegment member))
            (fun segment member =>
              rightRetained segment
                (List.Mem.tail rightSegment member))
            tailSupportSegmentsEq
            (fun prefixedEmpty =>
              False.elim <|
                rightRenderNonempty
                  (List.append_eq_nil_iff.mp prefixedEmpty).2)
        have combined :=
          currentSegmentStep.trans tailDerivation
        simpa [
          SemigroupBasis.CoRoots.S5_441.renderExactCutSegments_cons,
          List.append_assoc] using combined
termination_by leftSegments rightSegments =>
  leftSegments.length + rightSegments.length

/-- Equality of the coalesced exact-cut chain and the two exposed endpoint
coordinates is sufficient for every basis carrying the collapse
environment. -/
theorem listDerivesOfCoalescedChainFinalAndHead
    {laws : List (Identity Nat)}
    (env : CollapseLawEnvironment laws)
    {left right : Word Nat}
    (same : SameCoalescedChainFinalAndHead left right) :
    S5_107.ListDerives laws left.toList right.toList := by
  let leftSegments :=
    SemigroupBasis.CoRoots.S5_441.exactCutDecomposition
      left.toList
  let rightSegments :=
    SemigroupBasis.CoRoots.S5_441.exactCutDecomposition
      right.toList
  let leftRetained :=
    c06RetainedCutSegments leftSegments
  let rightRetained :=
    c06RetainedCutSegments rightSegments
  have supportSkeletonEq :=
    SameCoalescedChainFinalAndHead.exactCutSupportSkeleton_eq
      same
  have supportSegmentsEq :
      SemigroupBasis.CoRoots.S5_441.exactCutSupportSegments
          leftSegments =
        SemigroupBasis.CoRoots.S5_441.exactCutSupportSegments
          rightSegments := by
    simpa [leftSegments, rightSegments,
      SemigroupBasis.CoRoots.S5_441.exactCutSupportSkeleton]
      using supportSkeletonEq
  have retainedSupportEq :
      leftRetained.map
          SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment =
        rightRetained.map
          SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment := by
    rw [← c06SupportSegments_eq_map_retained,
      ← c06SupportSegments_eq_map_retained]
    exact supportSegmentsEq
  have leftMembers :
      ∀ segment, segment ∈ leftRetained →
        segment ∈
          SemigroupBasis.CoRoots.S5_441.exactCutDecomposition
            left.toList := by
    intro segment member
    exact c06RetainedCutSegments_member member
  have rightMembers :
      ∀ segment, segment ∈ rightRetained →
        segment ∈
          SemigroupBasis.CoRoots.S5_441.exactCutDecomposition
            right.toList := by
    intro segment member
    exact c06RetainedCutSegments_member member
  have leftRetainedProof :
      ∀ segment, segment ∈ leftRetained →
        ¬ (segment.gap = [] ∧ segment.separator = none) := by
    intro segment member
    exact c06RetainedCutSegments_retained member
  have rightRetainedProof :
      ∀ segment, segment ∈ rightRetained →
        ¬ (segment.gap = [] ∧ segment.separator = none) := by
    intro segment member
    exact c06RetainedCutSegments_retained member
  have wholeFinals :
      componentFinal left.toList =
        componentFinal right.toList := by
    simpa only [s5_806_componentFinal_eq] using same.final
  have leftRenderEq :
      SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
          leftRetained = left.toList := by
    calc
      SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
          leftRetained =
          SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
            leftSegments :=
        render_c06RetainedCutSegments leftSegments
      _ = left.toList := by
        simpa [leftSegments] using
          SemigroupBasis.CoRoots.S5_441.render_exactCutDecomposition
            left.toList
  have rightRenderEq :
      SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
          rightRetained = right.toList := by
    calc
      SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
          rightRetained =
          SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
            rightSegments :=
        render_c06RetainedCutSegments rightSegments
      _ = right.toList := by
        simpa [rightSegments] using
          SemigroupBasis.CoRoots.S5_441.render_exactCutDecomposition
            right.toList
  have derivation :=
    assembleC06RetainedSegments env left right
      same.head wholeFinals
      leftRetained rightRetained []
      leftMembers rightMembers
      leftRetainedProof rightRetainedProof
      retainedSupportEq
      (fun _ => ⟨leftRenderEq.symm, rightRenderEq.symm⟩)
  simpa [leftRenderEq, rightRenderEq] using derivation

/-- Word-level completeness of the coalesced-chain descriptor for a
collapse-law environment. -/
theorem derivesOfCoalescedChainFinalAndHead
    {laws : List (Identity Nat)}
    (env : CollapseLawEnvironment laws)
    {left right : Word Nat}
    (same : SameCoalescedChainFinalAndHead left right) :
    Derives laws left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simpa [S5_107.listWordOfCons, Word.toList] using
            S5_107.ListDerives.toWord
              (listDerivesOfCoalescedChainFinalAndHead
                env same)

/-! ## Semantic extraction -/

section Extraction

variable {G : Semigroup (Fin 6)}

private theorem foldl_band {p q : Fin 6}
    (pp : G.mul p p = p) (pq : G.mul p q = p)
    (qp : G.mul q p = q) (qq : G.mul q q = q)
    (valuation : Nat → Fin 6)
    (range : ∀ x, valuation x = p ∨ valuation x = q) :
    ∀ (letters : List Nat) (acc : Fin 6), acc = p ∨ acc = q →
      letters.foldl (fun current x => G.mul current (valuation x)) acc =
        acc := by
  intro letters
  induction letters with
  | nil => intro acc _; rfl
  | cons x rest ih =>
      intro acc accRange
      have step : G.mul acc (valuation x) = acc := by
        rcases accRange with rfl | rfl <;>
          rcases range x with hx | hx <;> rw [hx] <;> assumption
      rw [List.foldl_cons, step]
      exact ih acc accRange

/-- Two mutually left-zero idempotents make evaluation return the image of
the head letter; validity therefore forces equal heads. -/
theorem head_eq_of_band_valid {p q : Fin 6}
    (pp : G.mul p p = p) (pq : G.mul p q = p)
    (qp : G.mul q p = q) (qq : G.mul q q = q)
    (distinct : p ≠ q)
    (e : Identity Nat) (valid : e.SatisfiedBy G) :
    e.lhs.head = e.rhs.head := by
  by_cases same : e.lhs.head = e.rhs.head
  · exact same
  have range : ∀ x : Nat,
      (if x = e.lhs.head then p else q) = p ∨
        (if x = e.lhs.head then p else q) = q := by
    intro x
    by_cases hx : x = e.lhs.head <;> simp [hx]
  have evalWord : ∀ w : Word Nat,
      G.eval (fun x => if x = e.lhs.head then p else q) w =
        (if w.head = e.lhs.head then p else q) := by
    intro w
    exact foldl_band pp pq qp qq _ range w.tail _ (range w.head)
  have evaluated := valid (fun x => if x = e.lhs.head then p else q)
  rw [evalWord e.lhs, evalWord e.rhs, if_pos rfl,
    if_neg (fun equal => same equal.symm)] at evaluated
  exact (distinct evaluated).elim

private theorem reverseAux_head_eq_s5_806_componentFinal (head : Nat) :
    ∀ tail : List Nat,
      (Word.reverseAux head tail).head =
        SemigroupBasis.CoRoots.S5_806.componentFinal (head :: tail)
  | [] => rfl
  | next :: rest => by
      change
        (Word.reverseAux next rest).head =
          (next :: rest).getLastD head
      rw [List.getLastD_cons]
      exact reverseAux_head_eq_s5_806_componentFinal next rest

private theorem reverse_head_eq_s5_806_componentFinal (word : Word Nat) :
    word.reverse.head =
      SemigroupBasis.CoRoots.S5_806.componentFinal word.toList := by
  cases word with
  | mk head tail =>
      exact reverseAux_head_eq_s5_806_componentFinal head tail

/-- Two mutually right-zero idempotents make evaluation return the image of
the final letter; validity therefore forces equal literal finals. -/
theorem final_eq_of_band_valid {p q : Fin 6}
    (pp : G.mul p p = p) (pq : G.mul p q = q)
    (qp : G.mul q p = p) (qq : G.mul q q = q)
    (distinct : p ≠ q)
    (e : Identity Nat) (valid : e.SatisfiedBy G) :
    SemigroupBasis.CoRoots.S5_806.componentFinal e.lhs.toList =
      SemigroupBasis.CoRoots.S5_806.componentFinal e.rhs.toList := by
  have reversedValid :
      e.reversed.SatisfiedBy G.opposite := by
    rw [Identity.satisfiedBy_opposite_iff_reversed,
      Identity.reversed_reversed]
    exact valid
  have reversedHeads :=
    head_eq_of_band_valid (G := G.opposite) (p := p) (q := q)
      pp qp pq qq distinct e.reversed reversedValid
  change e.lhs.reverse.head = e.rhs.reverse.head at reversedHeads
  simpa only [reverse_head_eq_s5_806_componentFinal] using reversedHeads

end Extraction

/-! ## The system-2 instance -/

theorem defaEnvironment :
    FinalEraseLawEnvironment
      Generated.Order6LeeA2LatticeNodes.SystemHdefa5ab58c7c.basis where
  toSwitchLawEnvironment := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide
  erase := by decide

/-- Descriptor completeness for the six-member system-2 basis. -/
theorem derivesOfDefaDescriptorEq {u v : Word Nat}
    (same : SameBaseChainFinalAndHead u v) :
    Derives
      Generated.Order6LeeA2LatticeNodes.SystemHdefa5ab58c7c.basis u v :=
  derivesOfBaseChainFinalAndHead defaEnvironment same

/-! ## The system-3 collapse environment -/

theorem c06Environment :
    CollapseLawEnvironment
      Generated.Order6LeeA2LatticeNodes.SystemHc06cb5d53d74.basis where
  toFinalEraseLawEnvironment := by
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide
    · decide
  collapse := by decide

/-- Descriptor completeness for the system-3 collapse basis. -/
theorem derivesOfC06DescriptorEq {u v : Word Nat}
    (same : SameCoalescedChainFinalAndHead u v) :
    Derives
      Generated.Order6LeeA2LatticeNodes.SystemHc06cb5d53d74.basis u v :=
  derivesOfCoalescedChainFinalAndHead c06Environment same

/-! ## The trio instance -/

theorem trioEnvironment :
    SwitchLawEnvironment
      Generated.Order6LeeA2LatticeNodes.SystemHebf52dbf4ddc.basis := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Descriptor completeness for the trio basis. -/
theorem derivesOfDescriptorEq {u v : Word Nat}
    (same : SameDirectSignatureAndHead u v) :
    Derives Generated.Order6LeeA2LatticeNodes.SystemHebf52dbf4ddc.basis u v :=
  derivesOfSameSignatureAndHead trioEnvironment same

namespace S6_12952

abbrev table : FiniteTable :=
  Generated.Order6LeeA2LatticeNodes.S6_12952.table

/-- The unique surjection onto the `S5_804` detector. -/
def detectorSurjection :
    SplitSurjection table.semigroup
      Order6LeeA2LatticeScaffold.detectorTable.semigroup where
  toFun := fun a : Fin 6 =>
    (if a = 0 then 0 else
      if a = 1 then 1 else
        if a = 2 then 2 else
          if a = 3 then 0 else
            if a = 4 then 3 else 4 : Fin 5)
  map_mul := by decide
  preimage := fun b : Fin 5 =>
    (if b = 0 then 0 else
      if b = 1 then 1 else
        if b = 2 then 2 else
          if b = 3 then 4 else 5 : Fin 6)
  right_inverse := by decide

theorem representative_basis :
    BasisFor table.semigroup
      Generated.Order6LeeA2LatticeNodes.SystemHebf52dbf4ddc.basis := by
  refine ⟨Generated.Order6LeeA2LatticeNodes.S6_12952.models, ?_⟩
  intro e valid
  refine derivesOfDescriptorEq ⟨?_, ?_⟩
  · exact
      SemigroupBasis.CoRoots.S5_804.valid_sameConnectedCutSignature e
        (detectorSurjection.pushforwardIdentity e valid)
  · exact
      head_eq_of_band_valid (p := (0 : Fin 6)) (q := (3 : Fin 6))
        (by decide) (by decide) (by decide) (by decide) (by decide) e valid

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis
        Generated.Order6LeeA2LatticeNodes.SystemHebf52dbf4ddc.basis) :=
  representative_basis.oppositeReversed

end S6_12952

namespace S6_12954

abbrev table : FiniteTable :=
  Generated.Order6LeeA2LatticeNodes.S6_12954.table

/-- The unique surjection onto the `S5_804` detector. There is no detector
subsemigroup in this table (every homomorphism from the detector collapses
its two least elements), so the quotient route is the only one. -/
def detectorSurjection :
    SplitSurjection table.semigroup
      Order6LeeA2LatticeScaffold.detectorTable.semigroup where
  toFun := fun a : Fin 6 =>
    (if a = 0 then 0 else
      if a = 1 then 1 else
        if a = 2 then 2 else
          if a = 3 then 0 else
            if a = 4 then 3 else 4 : Fin 5)
  map_mul := by decide
  preimage := fun b : Fin 5 =>
    (if b = 0 then 0 else
      if b = 1 then 1 else
        if b = 2 then 2 else
          if b = 3 then 4 else 5 : Fin 6)
  right_inverse := by decide

theorem representative_basis :
    BasisFor table.semigroup
      Generated.Order6LeeA2LatticeNodes.SystemHebf52dbf4ddc.basis := by
  refine ⟨Generated.Order6LeeA2LatticeNodes.S6_12954.models, ?_⟩
  intro e valid
  refine derivesOfDescriptorEq ⟨?_, ?_⟩
  · exact
      SemigroupBasis.CoRoots.S5_804.valid_sameConnectedCutSignature e
        (detectorSurjection.pushforwardIdentity e valid)
  · exact
      head_eq_of_band_valid (p := (0 : Fin 6)) (q := (3 : Fin 6))
        (by decide) (by decide) (by decide) (by decide) (by decide) e valid

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis
        Generated.Order6LeeA2LatticeNodes.SystemHebf52dbf4ddc.basis) :=
  representative_basis.oppositeReversed

end S6_12954

namespace S6_13404

abbrev table : FiniteTable :=
  Generated.Order6LeeA2LatticeNodes.S6_13404.table

/-- The unique surjection onto the `S5_804` detector. -/
def detectorSurjection :
    SplitSurjection table.semigroup
      Order6LeeA2LatticeScaffold.detectorTable.semigroup where
  toFun := fun a : Fin 6 =>
    (if a = 0 then 0 else
      if a = 1 then 1 else
        if a = 2 then 2 else
          if a = 3 then 3 else 4 : Fin 5)
  map_mul := by decide
  preimage := fun b : Fin 5 =>
    (if b = 0 then 0 else
      if b = 1 then 1 else
        if b = 2 then 2 else
          if b = 3 then 3 else 4 : Fin 6)
  right_inverse := by decide

theorem representative_basis :
    BasisFor table.semigroup
      Generated.Order6LeeA2LatticeNodes.SystemHebf52dbf4ddc.basis := by
  refine ⟨Generated.Order6LeeA2LatticeNodes.S6_13404.models, ?_⟩
  intro e valid
  refine derivesOfDescriptorEq ⟨?_, ?_⟩
  · exact
      SemigroupBasis.CoRoots.S5_804.valid_sameConnectedCutSignature e
        (detectorSurjection.pushforwardIdentity e valid)
  · exact
      head_eq_of_band_valid (p := (4 : Fin 6)) (q := (5 : Fin 6))
        (by decide) (by decide) (by decide) (by decide) (by decide) e valid

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis
        Generated.Order6LeeA2LatticeNodes.SystemHebf52dbf4ddc.basis) :=
  representative_basis.oppositeReversed

end S6_13404

end SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesNormal
