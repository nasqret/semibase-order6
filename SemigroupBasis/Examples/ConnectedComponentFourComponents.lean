import SemigroupBasis.Examples.ConnectedComponentFourEnvelopeCombinatorics

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- Executable support-disjointness test used by the scanner. -/
private def connectedComponentListsDisjointBool
    (left right : List Nat) : Bool :=
  left.all fun letter => decide (letter ∉ right)

private theorem connectedComponentListsDisjointBool_eq_true_iff
    {left right : List Nat} :
    connectedComponentListsDisjointBool left right = true ↔
      ConnectedComponentSupportsDisjoint left right := by
  rw [connectedComponentListsDisjointBool, List.all_eq_true]
  constructor
  · intro tested letter member
    exact of_decide_eq_true (tested letter member)
  · intro disjoint letter member
    exact decide_eq_true (disjoint letter member)

private theorem connectedComponentListsDisjointBool_eq_false_iff
    {left right : List Nat} :
    connectedComponentListsDisjointBool left right = false ↔
      ConnectedComponentSupportsIntersect left right := by
  constructor
  · intro tested
    rcases List.all_eq_false.mp tested with
      ⟨letter, leftMember, notAbsent⟩
    by_cases rightMember : letter ∈ right
    · exact ⟨letter, leftMember, rightMember⟩
    · exact False.elim (notAbsent (decide_eq_true rightMember))
  · rintro ⟨letter, leftMember, rightMember⟩
    apply List.all_eq_false.mpr
    refine ⟨letter, leftMember, ?_⟩
    intro absent
    exact of_decide_eq_true absent rightMember

/-- While a component is being scanned, every already-passed cut is crossed
somewhere before the end of the unscanned suffix. -/
private def connectedComponentOpenPrefix
    (current remaining : List Nat) : Prop :=
  ∀ cut, 0 < cut → cut < current.length →
    ConnectedComponentSupportsIntersect
      (current.take cut) (current.drop cut ++ remaining)

private theorem connectedComponentOpenPrefix_singleton
    (letter : Nat) (remaining : List Nat) :
    connectedComponentOpenPrefix [letter] remaining := by
  intro cut positive small
  simp at small
  omega

private theorem connectedComponentOpenPrefix_append_singleton
    {current remaining : List Nat} {next : Nat}
    (openPrefix :
      connectedComponentOpenPrefix current (next :: remaining))
    (crossing :
      ConnectedComponentSupportsIntersect current (next :: remaining)) :
    connectedComponentOpenPrefix (current ++ [next]) remaining := by
  intro cut positive small
  by_cases beforeEnd : cut < current.length
  · have crossed := openPrefix cut positive beforeEnd
    rw [List.take_append_of_le_length (Nat.le_of_lt beforeEnd),
      List.drop_append_of_le_length (Nat.le_of_lt beforeEnd)]
    simpa [List.append_assoc] using crossed
  · have atEnd : cut = current.length := by
      simp only [List.length_append, List.length_singleton] at small
      omega
    subst cut
    simpa using crossing

private theorem connectedComponentSupportConnected_of_openPrefix
    {current remaining : List Nat}
    (_currentNonempty : current ≠ [])
    (openPrefix : connectedComponentOpenPrefix current remaining)
    (disjoint : ConnectedComponentSupportsDisjoint current remaining) :
    ConnectedComponentSupportConnected current := by
  intro left right shape leftNonempty rightNonempty
  have positive : 0 < left.length :=
    List.length_pos_iff.mpr leftNonempty
  have proper : left.length < current.length := by
    rw [shape, List.length_append]
    have rightPositive : 0 < right.length :=
      List.length_pos_iff.mpr rightNonempty
    omega
  rcases openPrefix left.length positive proper with
    ⟨letter, leftMember, rightMember⟩
  have takeEq : current.take left.length = left := by
    rw [shape, List.take_append_of_le_length (Nat.le_refl _),
      List.take_length]
  have dropEq : current.drop left.length = right := by
    rw [shape, List.drop_append_of_le_length (Nat.le_refl _),
      List.drop_length, List.nil_append]
  rw [takeEq] at leftMember
  rw [dropEq] at rightMember
  rw [List.mem_append] at rightMember
  rcases rightMember with rightMember | remainingMember
  · exact ⟨letter, leftMember, rightMember⟩
  · have currentMember : letter ∈ current := by
      rw [shape]
      exact List.mem_append_left right leftMember
    exact False.elim <|
      disjoint letter currentMember remainingMember

/-- Scan a nonempty current factor against the unprocessed suffix. A factor is
emitted exactly when its support is disjoint from the whole suffix. -/
private def connectedComponentScan
    (current : List Nat) : List Nat → List (List Nat)
  | [] => [current]
  | next :: remaining =>
      if connectedComponentListsDisjointBool current (next :: remaining) then
        current :: connectedComponentScan [next] remaining
      else
        connectedComponentScan (current ++ [next]) remaining

private theorem connectedComponentScan_flatten
    (current remaining : List Nat) :
    (connectedComponentScan current remaining).flatten =
      current ++ remaining := by
  induction remaining generalizing current with
  | nil =>
      simp [connectedComponentScan]
  | cons next remaining ih =>
      simp only [connectedComponentScan]
      split
      · simp [ih]
      · simpa [List.append_assoc] using ih (current ++ [next])

private theorem connectedComponentScan_nonempty
    {current remaining : List Nat}
    (currentNonempty : current ≠ []) :
    ∀ component ∈ connectedComponentScan current remaining,
      component ≠ [] := by
  induction remaining generalizing current with
  | nil =>
      simpa [connectedComponentScan] using currentNonempty
  | cons next remaining ih =>
      simp only [connectedComponentScan]
      split
      · intro component member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact currentNonempty
        · exact ih (by simp) component member
      · exact ih (by simp)

private theorem connectedComponentScan_pairwiseDisjoint
    (current remaining : List Nat) :
    (connectedComponentScan current remaining).Pairwise
      ConnectedComponentSupportsDisjoint := by
  induction remaining generalizing current with
  | nil =>
      simp [connectedComponentScan]
  | cons next remaining ih =>
      simp only [connectedComponentScan]
      split <;> rename_i disjoint
      · rw [List.pairwise_cons]
        refine ⟨?_, ih [next]⟩
        intro component componentMember letter currentMember componentMember'
        apply
          (connectedComponentListsDisjointBool_eq_true_iff.mp
            disjoint) letter currentMember
        have flattenedMember :
            letter ∈ (connectedComponentScan [next] remaining).flatten :=
          List.mem_flatten_of_mem componentMember componentMember'
        rwa [connectedComponentScan_flatten] at flattenedMember
      · exact ih (current ++ [next])

private theorem connectedComponentScan_supportConnected
    {current remaining : List Nat}
    (currentNonempty : current ≠ [])
    (openPrefix : connectedComponentOpenPrefix current remaining) :
    ∀ component ∈ connectedComponentScan current remaining,
      ConnectedComponentSupportConnected component := by
  induction remaining generalizing current with
  | nil =>
      intro component member
      simp only [connectedComponentScan, List.mem_singleton] at member
      subst component
      apply connectedComponentSupportConnected_of_openPrefix
        currentNonempty openPrefix
      intro letter _ member
      simp at member
  | cons next remaining ih =>
      simp only [connectedComponentScan]
      split <;> rename_i disjoint
      · intro component member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact connectedComponentSupportConnected_of_openPrefix
            currentNonempty openPrefix
            (connectedComponentListsDisjointBool_eq_true_iff.mp
              disjoint)
        · exact ih (by simp)
            (connectedComponentOpenPrefix_singleton next remaining)
            component member
      · have crossing :
            ConnectedComponentSupportsIntersect current (next :: remaining) :=
          connectedComponentListsDisjointBool_eq_false_iff.mp
            (Bool.eq_false_iff.mpr disjoint)
        exact ih (by simp)
          (connectedComponentOpenPrefix_append_singleton
            openPrefix crossing)

/-- Deterministically cut a list at every support-disjoint boundary. -/
def connectedComponentDecomposeList :
    List Nat → List (List Nat)
  | [] => []
  | first :: remaining =>
      connectedComponentScan [first] remaining

/-- Deterministically cut a nonempty semigroup word into support components. -/
def connectedComponentDecomposeWord
    (word : Word Nat) : List (List Nat) :=
  connectedComponentDecomposeList word.toList

@[simp]
theorem connectedComponentDecomposeList_nil :
    connectedComponentDecomposeList [] = [] :=
  rfl

theorem connectedComponentDecomposeList_flatten
    (letters : List Nat) :
    (connectedComponentDecomposeList letters).flatten = letters := by
  cases letters with
  | nil => rfl
  | cons first remaining =>
      simpa [connectedComponentDecomposeList] using
        connectedComponentScan_flatten [first] remaining

theorem connectedComponentDecomposeWord_flatten
    (word : Word Nat) :
    (connectedComponentDecomposeWord word).flatten = word.toList :=
  connectedComponentDecomposeList_flatten word.toList

theorem connectedComponentDecomposeList_nonempty
    {letters : List Nat} (nonempty : letters ≠ []) :
    connectedComponentDecomposeList letters ≠ [] := by
  intro decompositionEmpty
  have flattened :=
    connectedComponentDecomposeList_flatten letters
  rw [decompositionEmpty] at flattened
  exact nonempty flattened.symm

theorem connectedComponentDecomposeWord_nonempty
    (word : Word Nat) :
    connectedComponentDecomposeWord word ≠ [] :=
  connectedComponentDecomposeList_nonempty (by
    simp [Word.toList])

theorem connectedComponentDecomposeList_nonempty_components
    (letters : List Nat) :
    ∀ component ∈ connectedComponentDecomposeList letters,
      component ≠ [] := by
  cases letters with
  | nil =>
      simp [connectedComponentDecomposeList]
  | cons first remaining =>
      exact connectedComponentScan_nonempty (by simp)

theorem connectedComponentDecomposeWord_nonempty_components
    (word : Word Nat) :
    ∀ component ∈ connectedComponentDecomposeWord word,
      component ≠ [] :=
  connectedComponentDecomposeList_nonempty_components word.toList

theorem connectedComponentDecomposeList_pairwiseDisjoint
    (letters : List Nat) :
    (connectedComponentDecomposeList letters).Pairwise
      ConnectedComponentSupportsDisjoint := by
  cases letters with
  | nil =>
      simp [connectedComponentDecomposeList]
  | cons first remaining =>
      exact connectedComponentScan_pairwiseDisjoint [first] remaining

theorem connectedComponentDecomposeWord_pairwiseDisjoint
    (word : Word Nat) :
    (connectedComponentDecomposeWord word).Pairwise
      ConnectedComponentSupportsDisjoint :=
  connectedComponentDecomposeList_pairwiseDisjoint word.toList

theorem connectedComponentDecomposeList_supportConnected
    (letters : List Nat) :
    ∀ component ∈ connectedComponentDecomposeList letters,
      ConnectedComponentSupportConnected component := by
  cases letters with
  | nil =>
      simp [connectedComponentDecomposeList]
  | cons first remaining =>
      exact connectedComponentScan_supportConnected (by simp)
        (connectedComponentOpenPrefix_singleton first remaining)

theorem connectedComponentDecomposeWord_supportConnected
    (word : Word Nat) :
    ∀ component ∈ connectedComponentDecomposeWord word,
      ConnectedComponentSupportConnected component :=
  connectedComponentDecomposeList_supportConnected word.toList

/-- The complete structural contract supplied by the deterministic
decomposition. -/
structure connectedComponentDecompositionSpec
    (letters : List Nat) (components : List (List Nat)) : Prop where
  flatten_eq : components.flatten = letters
  nonempty :
    ∀ component ∈ components, component ≠ []
  pairwiseDisjoint :
    components.Pairwise ConnectedComponentSupportsDisjoint
  supportConnected :
    ∀ component ∈ components,
      ConnectedComponentSupportConnected component

theorem connectedComponentDecomposeList_spec
    (letters : List Nat) :
    connectedComponentDecompositionSpec letters
      (connectedComponentDecomposeList letters) where
  flatten_eq := connectedComponentDecomposeList_flatten letters
  nonempty := connectedComponentDecomposeList_nonempty_components letters
  pairwiseDisjoint :=
    connectedComponentDecomposeList_pairwiseDisjoint letters
  supportConnected :=
    connectedComponentDecomposeList_supportConnected letters

theorem connectedComponentDecomposeWord_spec
    (word : Word Nat) :
    connectedComponentDecompositionSpec word.toList
      (connectedComponentDecomposeWord word) :=
  connectedComponentDecomposeList_spec word.toList

theorem connectedComponentAppend_not_supportConnected
    {left right : List Nat}
    (leftNonempty : left ≠ []) (rightNonempty : right ≠ [])
    (disjoint : ConnectedComponentSupportsDisjoint left right) :
    ¬ConnectedComponentSupportConnected (left ++ right) := by
  intro connected
  rcases connected left right rfl leftNonempty rightNonempty with
    ⟨letter, leftMember, rightMember⟩
  exact disjoint letter leftMember rightMember

/-- Consecutive emitted components cannot be merged into a larger
support-connected factor; this is the maximality form used by later modules. -/
theorem connectedComponentDecomposeList_adjacent_maximal
    {letters : List Nat} {before after : List (List Nat)}
    {left right : List Nat}
    (shape :
      connectedComponentDecomposeList letters =
        before ++ left :: right :: after) :
    ¬ConnectedComponentSupportConnected (left ++ right) := by
  have nonempty :=
    connectedComponentDecomposeList_nonempty_components letters
  have pairwise :=
    connectedComponentDecomposeList_pairwiseDisjoint letters
  rw [shape] at pairwise
  have tailPairwise :
      (left :: right :: after).Pairwise
        ConnectedComponentSupportsDisjoint :=
    (List.pairwise_append.mp pairwise).2.1
  have disjoint :
      ConnectedComponentSupportsDisjoint left right :=
    (List.pairwise_cons.mp tailPairwise).1 right (by simp)
  apply connectedComponentAppend_not_supportConnected
  · apply nonempty left
    rw [shape]
    simp
  · apply nonempty right
    rw [shape]
    simp
  · exact disjoint

theorem connectedComponentDecomposeWord_adjacent_maximal
    {word : Word Nat} {before after : List (List Nat)}
    {left right : List Nat}
    (shape :
      connectedComponentDecomposeWord word =
        before ++ left :: right :: after) :
    ¬ConnectedComponentSupportConnected (left ++ right) :=
  connectedComponentDecomposeList_adjacent_maximal shape

/-- Retain one representative of every letter. The eventual sort makes the
choice of representative order irrelevant. -/
def connectedComponentDistinctSupport :
    List Nat → List Nat
  | [] => []
  | letter :: remaining =>
      let rest := connectedComponentDistinctSupport remaining
      if letter ∈ rest then rest else letter :: rest

theorem connectedComponentDistinctSupport_mem_iff
    (tested : Nat) (letters : List Nat) :
    tested ∈ connectedComponentDistinctSupport letters ↔
      tested ∈ letters := by
  induction letters with
  | nil =>
      simp [connectedComponentDistinctSupport]
  | cons letter remaining ih =>
      simp only [connectedComponentDistinctSupport]
      split <;> rename_i present
      · constructor
        · intro member
          exact List.Mem.tail letter (ih.mp member)
        · intro member
          rcases List.mem_cons.mp member with rfl | member
          · exact present
          · exact ih.mpr member
      · simp [ih]

theorem connectedComponentDistinctSupport_nodup
    (letters : List Nat) :
    (connectedComponentDistinctSupport letters).Nodup := by
  induction letters with
  | nil =>
      simp [connectedComponentDistinctSupport]
  | cons letter remaining ih =>
      simp only [connectedComponentDistinctSupport]
      split <;> simp_all

/-- The support as a deterministic ascending list without repetitions. -/
def connectedComponentSortedSupport
    (letters : List Nat) : List Nat :=
  (connectedComponentDistinctSupport letters).mergeSort
    (fun left right : Nat => decide (left ≤ right))

theorem connectedComponentSortedSupport_mem_iff
    (tested : Nat) (letters : List Nat) :
    tested ∈ connectedComponentSortedSupport letters ↔
      tested ∈ letters := by
  rw [connectedComponentSortedSupport, List.mem_mergeSort,
    connectedComponentDistinctSupport_mem_iff]

theorem connectedComponentSortedSupport_nodup
    (letters : List Nat) :
    (connectedComponentSortedSupport letters).Nodup := by
  apply (List.mergeSort_perm
    (connectedComponentDistinctSupport letters)
    (fun left right : Nat => decide (left ≤ right))).symm.nodup
  exact connectedComponentDistinctSupport_nodup letters

theorem connectedComponentSortedSupport_sorted
    (letters : List Nat) :
    (connectedComponentSortedSupport letters).Pairwise (· ≤ ·) := by
  have transitive :
      ∀ left middle right : Nat,
        decide (left ≤ middle) = true →
        decide (middle ≤ right) = true →
        decide (left ≤ right) = true := by
    intro left middle right leftMiddle middleRight
    exact decide_eq_true
      (Nat.le_trans
        (of_decide_eq_true leftMiddle)
        (of_decide_eq_true middleRight))
  have total :
      ∀ left right : Nat,
        (decide (left ≤ right) ||
          decide (right ≤ left)) = true := by
    intro left right
    rcases Nat.le_total left right with leftRight | rightLeft
    · simp [leftRight]
    · simp [rightLeft]
  exact
    (List.pairwise_mergeSort transitive total
      (connectedComponentDistinctSupport letters)).imp
        (fun relation => of_decide_eq_true relation)

theorem connectedComponentSortedSupport_nonempty
    {letters : List Nat} (nonempty : letters ≠ []) :
    connectedComponentSortedSupport letters ≠ [] := by
  cases letters with
  | nil => contradiction
  | cons first remaining =>
      apply List.ne_nil_of_mem
      exact
        (connectedComponentSortedSupport_mem_iff
          first (first :: remaining)).2 (by simp)

private theorem connectedComponentSortedNodup_eq_of_mem_iff
    {left right : List Nat}
    (leftSorted : left.Pairwise (· ≤ ·))
    (rightSorted : right.Pairwise (· ≤ ·))
    (leftNodup : left.Nodup) (rightNodup : right.Nodup)
    (sameSupport : ∀ letter, letter ∈ left ↔ letter ∈ right) :
    left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons head tail =>
          have := (sameSupport head).2 (by simp)
          contradiction
  | cons leftHead leftTail ih =>
      cases right with
      | nil =>
          have := (sameSupport leftHead).1 (by simp)
          contradiction
      | cons rightHead rightTail =>
          have leftHeadInRight :=
            (sameSupport leftHead).1 (by simp)
          have rightHeadInLeft :=
            (sameSupport rightHead).2 (by simp)
          have rightHeadLeLeftHead : rightHead ≤ leftHead := by
            by_cases equal : leftHead = rightHead
            · omega
            · have tailMember : leftHead ∈ rightTail := by
                simpa [equal] using leftHeadInRight
              exact List.rel_of_pairwise_cons rightSorted tailMember
          have leftHeadLeRightHead : leftHead ≤ rightHead := by
            by_cases equal : rightHead = leftHead
            · omega
            · have tailMember : rightHead ∈ leftTail := by
                simpa [equal] using rightHeadInLeft
              exact List.rel_of_pairwise_cons leftSorted tailMember
          have headsEqual : leftHead = rightHead := by omega
          subst rightHead
          congr 1
          apply ih leftSorted.tail rightSorted.tail
            leftNodup.tail rightNodup.tail
          intro letter
          by_cases equal : letter = leftHead
          · subst letter
            have leftAbsent : leftHead ∉ leftTail := by
              simpa using (List.nodup_cons.mp leftNodup).1
            have rightAbsent : leftHead ∉ rightTail := by
              simpa using (List.nodup_cons.mp rightNodup).1
            simp [leftAbsent, rightAbsent]
          · simpa [equal] using sameSupport letter

/-- The exact S4_70 datum of one component: its sorted support, plus the
distinction between `x` and a repeated unary component. -/
structure connectedComponentSignature where
  support : List Nat
  repeatedUnary : Bool
deriving DecidableEq, Repr

/-- Structural well-formedness of a component signature. -/
def connectedComponentSignatureValid
    (signature : connectedComponentSignature) : Prop :=
  signature.support ≠ [] ∧
    signature.support.Nodup ∧
    signature.support.Pairwise (· ≤ ·) ∧
    (signature.support.length ≠ 1 →
      signature.repeatedUnary = false)

/-- Extract the canonical S4_70 signature of one possibly empty list. The
empty case is totalized by the empty support and is never emitted by the word
decomposition. -/
def connectedComponentSignatureOfList
    (component : List Nat) : connectedComponentSignature :=
  let support := connectedComponentSortedSupport component
  match support with
  | [letter] =>
      ⟨[letter], decide (component.length ≠ 1)⟩
  | _ =>
      ⟨support, false⟩

theorem connectedComponentSignatureOfList_support
    (component : List Nat) :
    (connectedComponentSignatureOfList component).support =
      connectedComponentSortedSupport component := by
  simp only [connectedComponentSignatureOfList]
  split <;> rename_i supportShape
  · exact supportShape.symm
  · rfl

theorem connectedComponentSignatureOfList_valid
    {component : List Nat} (nonempty : component ≠ []) :
    connectedComponentSignatureValid
      (connectedComponentSignatureOfList component) := by
  rw [connectedComponentSignatureValid]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [connectedComponentSignatureOfList_support]
    exact connectedComponentSortedSupport_nonempty nonempty
  · rw [connectedComponentSignatureOfList_support]
    exact connectedComponentSortedSupport_nodup component
  · rw [connectedComponentSignatureOfList_support]
    exact connectedComponentSortedSupport_sorted component
  · simp only [connectedComponentSignatureOfList]
    split <;> simp_all

/-- Render a signature. Unary support gives `x` or `xx`; a multi-support
signature gives the least support letter as an envelope around the sorted
remaining support. -/
def connectedComponentRenderSignature
    (signature : connectedComponentSignature) : List Nat :=
  match signature.support with
  | [] => []
  | [letter] =>
      if signature.repeatedUnary then [letter, letter] else [letter]
  | least :: next :: remaining =>
      least :: (next :: remaining) ++ [least]

@[simp]
theorem connectedComponentRenderSignature_unarySimple
    (letter : Nat) :
    connectedComponentRenderSignature ⟨[letter], false⟩ =
      [letter] :=
  rfl

@[simp]
theorem connectedComponentRenderSignature_unaryRepeated
    (letter : Nat) :
    connectedComponentRenderSignature ⟨[letter], true⟩ =
      [letter, letter] :=
  rfl

@[simp]
theorem connectedComponentRenderSignature_multi
    (least next : Nat) (remaining : List Nat)
    (repeatedUnary : Bool) :
    connectedComponentRenderSignature
        ⟨least :: next :: remaining, repeatedUnary⟩ =
      least :: (next :: remaining) ++ [least] :=
  rfl

theorem connectedComponentRenderSignature_nonempty
    {signature : connectedComponentSignature}
    (valid : connectedComponentSignatureValid signature) :
    connectedComponentRenderSignature signature ≠ [] := by
  cases signature with
  | mk support repeatedUnary =>
      cases support with
      | nil =>
          exact False.elim (valid.1 rfl)
      | cons first remaining =>
          cases remaining with
          | nil =>
              cases repeatedUnary <;>
                simp [connectedComponentRenderSignature]
          | cons next remaining =>
              simp [connectedComponentRenderSignature]

theorem connectedComponentRenderSignature_mem_iff
    {signature : connectedComponentSignature}
    (supportNonempty : signature.support ≠ [])
    (tested : Nat) :
    tested ∈ connectedComponentRenderSignature signature ↔
      tested ∈ signature.support := by
  cases signature with
  | mk support repeatedUnary =>
      cases support with
      | nil => contradiction
      | cons first remaining =>
          cases remaining with
          | nil =>
              cases repeatedUnary <;>
                simp [connectedComponentRenderSignature]
          | cons next remaining =>
              simp [connectedComponentRenderSignature,
                or_left_comm, or_comm]

/-- The canonical list representative of one component. -/
def connectedComponentCanonicalComponent
    (component : List Nat) : List Nat :=
  connectedComponentRenderSignature
    (connectedComponentSignatureOfList component)

theorem connectedComponentCanonicalComponent_nonempty
    {component : List Nat} (nonempty : component ≠ []) :
    connectedComponentCanonicalComponent component ≠ [] :=
  connectedComponentRenderSignature_nonempty
    (connectedComponentSignatureOfList_valid nonempty)

theorem connectedComponentCanonicalComponent_mem_iff
    {component : List Nat} (nonempty : component ≠ [])
    (tested : Nat) :
    tested ∈ connectedComponentCanonicalComponent component ↔
      tested ∈ component := by
  rw [connectedComponentCanonicalComponent,
    connectedComponentRenderSignature_mem_iff
      (connectedComponentSignatureOfList_valid nonempty).1,
    connectedComponentSignatureOfList_support,
    connectedComponentSortedSupport_mem_iff]

theorem connectedComponentSignature_render_consistent
    {signature : connectedComponentSignature}
    (valid : connectedComponentSignatureValid signature) :
    connectedComponentSignatureOfList
        (connectedComponentRenderSignature signature) =
      signature := by
  have supportEq :
      connectedComponentSortedSupport
          (connectedComponentRenderSignature signature) =
        signature.support := by
    apply connectedComponentSortedNodup_eq_of_mem_iff
      (connectedComponentSortedSupport_sorted _)
      valid.2.2.1
      (connectedComponentSortedSupport_nodup _)
      valid.2.1
    intro letter
    rw [connectedComponentSortedSupport_mem_iff,
      connectedComponentRenderSignature_mem_iff valid.1]
  cases signature with
  | mk support repeatedUnary =>
      simp only at supportEq valid
      unfold connectedComponentSignatureOfList
      rw [supportEq]
      cases support with
      | nil =>
          exact False.elim (valid.1 rfl)
      | cons first remaining =>
          cases remaining with
          | nil =>
              cases repeatedUnary <;>
                simp [connectedComponentRenderSignature]
          | cons next remaining =>
              have notUnary :
                  (first :: next :: remaining).length ≠ 1 := by
                simp
              have repeatedFalse := valid.2.2.2 notUnary
              change repeatedUnary = false at repeatedFalse
              simpa using repeatedFalse

theorem connectedComponentCanonicalComponent_signature
    {component : List Nat} (nonempty : component ≠ []) :
    connectedComponentSignatureOfList
        (connectedComponentCanonicalComponent component) =
      connectedComponentSignatureOfList component :=
  connectedComponentSignature_render_consistent
    (connectedComponentSignatureOfList_valid nonempty)

/-- The ordered S4_70 component signature of a list. -/
def connectedComponentSignaturesList
    (letters : List Nat) : List connectedComponentSignature :=
  (connectedComponentDecomposeList letters).map
    connectedComponentSignatureOfList

/-- The ordered S4_70 component signature of a word. -/
def connectedComponentSignaturesWord
    (word : Word Nat) : List connectedComponentSignature :=
  connectedComponentSignaturesList word.toList

theorem connectedComponentSignaturesList_valid
    (letters : List Nat) :
    ∀ signature ∈ connectedComponentSignaturesList letters,
      connectedComponentSignatureValid signature := by
  intro signature member
  rcases List.mem_map.mp member with
    ⟨component, componentMember, rfl⟩
  exact connectedComponentSignatureOfList_valid
    (connectedComponentDecomposeList_nonempty_components letters
      component componentMember)

theorem connectedComponentSignaturesWord_valid
    (word : Word Nat) :
    ∀ signature ∈ connectedComponentSignaturesWord word,
      connectedComponentSignatureValid signature :=
  connectedComponentSignaturesList_valid word.toList

/-- Render an ordered list of component signatures. -/
def connectedComponentRenderSignatures
    (signatures : List connectedComponentSignature) : List Nat :=
  signatures.flatMap connectedComponentRenderSignature

/-- Canonically render every maximal support component of a list. -/
def connectedComponentCanonicalRenderList
    (letters : List Nat) : List Nat :=
  connectedComponentRenderSignatures
    (connectedComponentSignaturesList letters)

theorem connectedComponentCanonicalRenderList_eq_flatMap
    (letters : List Nat) :
    connectedComponentCanonicalRenderList letters =
      (connectedComponentDecomposeList letters).flatMap
        connectedComponentCanonicalComponent := by
  unfold connectedComponentCanonicalRenderList
    connectedComponentRenderSignatures
    connectedComponentSignaturesList
  rw [List.flatMap_map]
  rfl

theorem connectedComponentCanonicalRenderList_nonempty
    {letters : List Nat} (nonempty : letters ≠ []) :
    connectedComponentCanonicalRenderList letters ≠ [] := by
  intro renderedEmpty
  have decompositionNonempty :=
    connectedComponentDecomposeList_nonempty nonempty
  rcases List.exists_cons_of_ne_nil decompositionNonempty with
    ⟨first, rest, decompositionEq⟩
  have firstNonempty :
      first ≠ [] :=
    connectedComponentDecomposeList_nonempty_components letters
      first (by rw [decompositionEq]; simp)
  have firstRenderedNonempty :=
    connectedComponentCanonicalComponent_nonempty firstNonempty
  rw [connectedComponentCanonicalRenderList_eq_flatMap,
    decompositionEq] at renderedEmpty
  simp only [List.flatMap_cons] at renderedEmpty
  exact firstRenderedNonempty
    (List.append_eq_nil_iff.mp renderedEmpty).1

theorem connectedComponentCanonicalRenderList_mem_iff
    (tested : Nat) (letters : List Nat) :
    tested ∈ connectedComponentCanonicalRenderList letters ↔
      tested ∈ letters := by
  rw [connectedComponentCanonicalRenderList_eq_flatMap,
    List.mem_flatMap]
  constructor
  · rintro ⟨component, componentMember, testedMember⟩
    have componentNonempty :=
      connectedComponentDecomposeList_nonempty_components letters
        component componentMember
    have testedInComponent :=
      (connectedComponentCanonicalComponent_mem_iff
        componentNonempty tested).1 testedMember
    have testedInFlatten :
        tested ∈ (connectedComponentDecomposeList letters).flatten :=
      List.mem_flatten_of_mem componentMember testedInComponent
    rwa [connectedComponentDecomposeList_flatten] at testedInFlatten
  · intro testedMember
    have testedInFlatten :
        tested ∈ (connectedComponentDecomposeList letters).flatten := by
      rwa [connectedComponentDecomposeList_flatten]
    rcases List.mem_flatten.mp testedInFlatten with
      ⟨component, componentMember, testedInComponent⟩
    refine ⟨component, componentMember, ?_⟩
    exact
      (connectedComponentCanonicalComponent_mem_iff
        (connectedComponentDecomposeList_nonempty_components letters
          component componentMember)
        tested).2 testedInComponent

theorem connectedComponentCanonicalRenderList_eq_of_signature_eq
    {left right : List Nat}
    (same :
      connectedComponentSignaturesList left =
        connectedComponentSignaturesList right) :
    connectedComponentCanonicalRenderList left =
      connectedComponentCanonicalRenderList right := by
  simp only [connectedComponentCanonicalRenderList]
  rw [same]

def connectedComponentWordOfNonempty
    (letters : List Nat) (nonempty : letters ≠ []) : Word Nat :=
  match letters with
  | [] => False.elim (nonempty rfl)
  | first :: remaining => ⟨first, remaining⟩

@[simp]
theorem connectedComponentWordOfNonempty_toList
    (letters : List Nat) (nonempty : letters ≠ []) :
    (connectedComponentWordOfNonempty letters nonempty).toList =
      letters := by
  cases letters with
  | nil => contradiction
  | cons first remaining => rfl

/-- The canonical nonempty-word render of the ordered S4_70 component
signature. -/
def connectedComponentCanonicalRender
    (word : Word Nat) : Word Nat :=
  connectedComponentWordOfNonempty
    (connectedComponentCanonicalRenderList word.toList)
    (connectedComponentCanonicalRenderList_nonempty (by
      simp [Word.toList]))

@[simp]
theorem connectedComponentCanonicalRender_toList
    (word : Word Nat) :
    (connectedComponentCanonicalRender word).toList =
      connectedComponentCanonicalRenderList word.toList :=
  connectedComponentWordOfNonempty_toList _ _

theorem connectedComponentCanonicalRender_mem_iff
    (tested : Nat) (word : Word Nat) :
    tested ∈ (connectedComponentCanonicalRender word).toList ↔
      tested ∈ word.toList := by
  rw [connectedComponentCanonicalRender_toList,
    connectedComponentCanonicalRenderList_mem_iff]

theorem connectedComponentCanonicalRender_eq_of_signature_eq
    {left right : Word Nat}
    (same :
      connectedComponentSignaturesWord left =
        connectedComponentSignaturesWord right) :
    connectedComponentCanonicalRender left =
      connectedComponentCanonicalRender right := by
  apply Word.toList_injective
  rw [connectedComponentCanonicalRender_toList,
    connectedComponentCanonicalRender_toList]
  exact connectedComponentCanonicalRenderList_eq_of_signature_eq same

end SemigroupBasis.Examples
