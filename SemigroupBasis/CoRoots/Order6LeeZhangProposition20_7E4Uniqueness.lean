import SemigroupBasis.CoRoots.Order6LeeZhangProposition20_7E4Canonical

namespace SemigroupBasis.CoRoots.Order6LeeZhangProposition20_7E4

open SemigroupBasis

/-!
# Lee--Zhang Proposition 20.7: canonical uniqueness

The literal canonical form printed in (20.7)--(20.8) is not unique under
the four invariants of Lemma 20.8: a later block can move its first nonempty
simple segment across the leading copy of its marker while adjusting the
final marker exponent.  The concrete `00121`/`00211` witness is recorded
below.

Consequently, the non-simple uniqueness theorem in this file is stated only
for `CanonicalForm.ReducedValid`, which retains all printed conditions and
adds the deterministic later-block convention `RigidBlock.LeftNormalized`.
No target semantics or derivability is used here.
-/

/-! ## Generic reconstruction of a duplicate-free adjacent chain -/

theorem adjacent_source_mem
    {letters : List Nat} {source target : Nat}
    (adjacent :
      (source, target) ∈ S5_107.listAdjacentPairs letters) :
    source ∈ letters := by
  rcases
      (S5_107.mem_listAdjacentPairs_iff_exists_split
        source target letters).1 adjacent with
    ⟨before, after, shape⟩
  rw [shape]
  simp

theorem adjacent_target_mem
    {letters : List Nat} {source target : Nat}
    (adjacent :
      (source, target) ∈ S5_107.listAdjacentPairs letters) :
    target ∈ letters := by
  rcases
      (S5_107.mem_listAdjacentPairs_iff_exists_split
        source target letters).1 adjacent with
    ⟨before, after, shape⟩
  rw [shape]
  simp

theorem mem_adjacentPairs_cons_iff_of_source_ne
    (head source target : Nat) (tail : List Nat)
    (different : source ≠ head) :
    (source, target) ∈
          S5_107.listAdjacentPairs (head :: tail) ↔
      (source, target) ∈ S5_107.listAdjacentPairs tail := by
  cases tail with
  | nil => simp
  | cons second rest =>
      simp [different]

theorem tail_head?_eq_some_of_adjacent_from_unique_head
    {head next : Nat} {tail : List Nat}
    (headAbsent : head ∉ tail)
    (adjacent :
      (head, next) ∈ S5_107.listAdjacentPairs (head :: tail)) :
    tail.head? = some next := by
  cases tail with
  | nil =>
      simp at adjacent
  | cons second rest =>
      simp only [S5_107.listAdjacentPairs_cons_cons,
        List.mem_cons] at adjacent
      rcases adjacent with firstEdge | laterEdge
      · have nextEq : next = second :=
          congrArg Prod.snd firstEdge
        simp only at nextEq
        simpa [nextEq]
      · have headMember : head ∈ second :: rest :=
          adjacent_source_mem laterEdge
        exact (headAbsent headMember).elim

/-- A duplicate-free list is reconstructed by its support, head, and directed
adjacency relation. -/
theorem nodup_list_eq_of_same_head_support_adjacent :
    ∀ (left right : List Nat),
      left.Nodup →
      right.Nodup →
      left.head? = right.head? →
      (∀ letter, letter ∈ left ↔ letter ∈ right) →
      (∀ source target,
        (source, target) ∈ S5_107.listAdjacentPairs left ↔
          (source, target) ∈ S5_107.listAdjacentPairs right) →
      left = right
  | [], right, _, _, _, sameSupport, _ => by
      have rightEmpty : right = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro letter member
        exact List.not_mem_nil ((sameSupport letter).mpr member)
      exact rightEmpty.symm
  | head :: leftTail, right, leftNodup, rightNodup, sameHead,
      sameSupport, sameAdjacent => by
      cases right with
      | nil =>
          have headRight : head ∈ ([] : List Nat) :=
            (sameSupport head).mp (by simp)
          simp at headRight
      | cons rightHead rightTail =>
          have headEq : head = rightHead := by
            simpa using sameHead
          subst rightHead
          have leftParts := List.nodup_cons.mp leftNodup
          have rightParts := List.nodup_cons.mp rightNodup
          have tailSupport :
              ∀ letter,
                letter ∈ leftTail ↔ letter ∈ rightTail := by
            intro letter
            constructor
            · intro leftMember
              have rightMember :=
                (sameSupport letter).mp (by simp [leftMember])
              rcases List.mem_cons.mp rightMember with equal | inTail
              · subst letter
                exact (leftParts.1 leftMember).elim
              · exact inTail
            · intro rightMember
              have leftMember :=
                (sameSupport letter).mpr (by simp [rightMember])
              rcases List.mem_cons.mp leftMember with equal | inTail
              · subst letter
                exact (rightParts.1 rightMember).elim
              · exact inTail
          have tailHead : leftTail.head? = rightTail.head? := by
            cases leftTail with
            | nil =>
                have rightEmpty : rightTail = [] := by
                  apply List.eq_nil_iff_forall_not_mem.mpr
                  intro letter member
                  exact List.not_mem_nil ((tailSupport letter).mpr member)
                simp [rightEmpty]
            | cons next more =>
                have leftEdge :
                    (head, next) ∈
                      S5_107.listAdjacentPairs (head :: next :: more) := by
                  simp
                have rightEdge :=
                  (sameAdjacent head next).mp leftEdge
                have rightTailHead :=
                  tail_head?_eq_some_of_adjacent_from_unique_head
                    rightParts.1 rightEdge
                simpa using rightTailHead.symm
          have tailAdjacent :
              ∀ source target,
                (source, target) ∈
                      S5_107.listAdjacentPairs leftTail ↔
                  (source, target) ∈
                    S5_107.listAdjacentPairs rightTail := by
            intro source target
            by_cases sourceEq : source = head
            · subst source
              constructor
              · intro edge
                exact (leftParts.1 (adjacent_source_mem edge)).elim
              · intro edge
                exact (rightParts.1 (adjacent_source_mem edge)).elim
            · rw [← mem_adjacentPairs_cons_iff_of_source_ne
                  head source target leftTail sourceEq,
                ← mem_adjacentPairs_cons_iff_of_source_ne
                  head source target rightTail sourceEq]
              exact sameAdjacent source target
          have tailEq :=
            nodup_list_eq_of_same_head_support_adjacent
              leftTail rightTail leftParts.2 rightParts.2 tailHead
              tailSupport tailAdjacent
          rw [tailEq]

theorem SameInvariant.symm
    {left right : List Nat} (same : SameInvariant left right) :
    SameInvariant right left := by
  constructor
  · intro letter
    rcases same.multiplicity letter with small | large
    · exact Or.inl ⟨small.1.symm, by omega⟩
    · exact Or.inr ⟨large.2, large.1⟩
  · exact same.firstLetter.symm
  · intro x y
    exact (same.fsn x y).symm
  · intro x y
    exact (same.fss x y).symm

/-! ## The simple-word branch -/

/-- Every letter occurring in the list is globally simple. -/
def AllSimple (letters : List Nat) : Prop :=
  ∀ letter ∈ letters, Simple letters letter

theorem AllSimple.nodup
    {letters : List Nat} (allSimple : AllSimple letters) :
    letters.Nodup := by
  rw [List.nodup_iff_count]
  intro letter
  by_cases member : letter ∈ letters
  · have simple := allSimple letter member
    unfold Simple at simple
    omega
  · rw [List.count_eq_zero.mpr member]
    omega

theorem adjacent_iff_fss_of_allSimple
    {letters : List Nat} (allSimple : AllSimple letters)
    (source target : Nat) :
    (source, target) ∈ S5_107.listAdjacentPairs letters ↔
      FSS letters source target := by
  constructor
  · intro adjacent
    exact
      ⟨allSimple source (adjacent_source_mem adjacent),
        allSimple target (adjacent_target_mem adjacent), adjacent⟩
  · exact fun factor => factor.2.2

/-- Completeness's simple-word branch: Lemma 20.8(ii),(iv), together with
support/count alignment from part (i), force literal equality. -/
theorem list_eq_of_allSimple_sameInvariant
    {left right : List Nat}
    (leftSimple : AllSimple left)
    (rightSimple : AllSimple right)
    (same : SameInvariant left right) :
    left = right := by
  apply nodup_list_eq_of_same_head_support_adjacent
    left right leftSimple.nodup rightSimple.nodup
    same.firstLetter same.support
  intro source target
  rw [adjacent_iff_fss_of_allSimple leftSimple,
    adjacent_iff_fss_of_allSimple rightSimple]
  exact same.fss source target

/-! ## Simple chains terminating at a non-simple marker -/

/-- A globally simple occurrence has at most one adjacent successor. -/
theorem adjacent_target_eq_of_simple_source
    {source leftTarget rightTarget : Nat} :
    ∀ {whole : List Nat},
      Simple whole source →
      (source, leftTarget) ∈ S5_107.listAdjacentPairs whole →
      (source, rightTarget) ∈ S5_107.listAdjacentPairs whole →
      leftTarget = rightTarget
  | [], _, leftEdge, _ => by
      simp at leftEdge
  | head :: tail, simple, leftEdge, rightEdge => by
      by_cases atHead : head = source
      · subst head
        have sourceAbsent : source ∉ tail := by
          intro member
          have positive : 0 < tail.count source :=
            List.count_pos_iff.mpr member
          unfold Simple at simple
          simp only [List.count_cons_self] at simple
          omega
        have leftHead :=
          tail_head?_eq_some_of_adjacent_from_unique_head
            sourceAbsent leftEdge
        have rightHead :=
          tail_head?_eq_some_of_adjacent_from_unique_head
            sourceAbsent rightEdge
        rw [leftHead] at rightHead
        injection rightHead
      · have tailSimple : Simple tail source := by
          unfold Simple at simple ⊢
          simpa only [List.count_cons_of_ne atHead] using simple
        have leftTail :=
          (mem_adjacentPairs_cons_iff_of_source_ne
            head source leftTarget tail (Ne.symm atHead)).1 leftEdge
        have rightTail :=
          (mem_adjacentPairs_cons_iff_of_source_ne
            head source rightTarget tail (Ne.symm atHead)).1 rightEdge
        exact adjacent_target_eq_of_simple_source
          tailSimple leftTail rightTail

/-- Reversal exchanges the source and target of every adjacent factor. -/
theorem mem_adjacentPairs_reverse_iff
    (letters : List Nat) (source target : Nat) :
    (source, target) ∈ S5_107.listAdjacentPairs letters.reverse ↔
      (target, source) ∈ S5_107.listAdjacentPairs letters := by
  constructor
  · intro member
    rcases
        (S5_107.mem_listAdjacentPairs_iff_exists_split
          source target letters.reverse).1 member with
      ⟨before, after, shape⟩
    apply
      (S5_107.mem_listAdjacentPairs_iff_exists_split
        target source letters).2
    refine ⟨after.reverse, before.reverse, ?_⟩
    have reversed := congrArg List.reverse shape
    simpa [List.reverse_append] using reversed
  · intro member
    rcases
        (S5_107.mem_listAdjacentPairs_iff_exists_split
          target source letters).1 member with
      ⟨before, after, shape⟩
    apply
      (S5_107.mem_listAdjacentPairs_iff_exists_split
        source target letters.reverse).2
    refine ⟨after.reverse, before.reverse, ?_⟩
    rw [shape]
    simp [List.reverse_append]

/-- A globally simple occurrence has at most one adjacent predecessor. -/
theorem adjacent_source_eq_of_simple_target
    {whole : List Nat} {target leftSource rightSource : Nat}
    (simple : Simple whole target)
    (leftEdge :
      (leftSource, target) ∈ S5_107.listAdjacentPairs whole)
    (rightEdge :
      (rightSource, target) ∈ S5_107.listAdjacentPairs whole) :
    leftSource = rightSource := by
  have reverseSimple : Simple whole.reverse target := by
    unfold Simple at simple ⊢
    simpa using simple
  exact adjacent_target_eq_of_simple_source reverseSimple
    ((mem_adjacentPairs_reverse_iff whole target leftSource).2 leftEdge)
    ((mem_adjacentPairs_reverse_iff whole target rightSource).2 rightEdge)

/-- A nonempty chain of simple letters whose final letter is immediately
followed by the displayed non-simple marker. -/
inductive SimpleChainTo (whole : List Nat) (marker : Nat) :
    List Nat → Prop
  | singleton (letter : Nat)
      (simple : Simple whole letter)
      (terminal : FSN whole letter marker) :
      SimpleChainTo whole marker [letter]
  | cons (letter next : Nat) (rest : List Nat)
      (simple : Simple whole letter)
      (edge : FSS whole letter next)
      (tail : SimpleChainTo whole marker (next :: rest)) :
      SimpleChainTo whole marker (letter :: next :: rest)

namespace SimpleChainTo

theorem nonempty
    {whole : List Nat} {marker : Nat} {chain : List Nat}
    (path : SimpleChainTo whole marker chain) :
    chain ≠ [] := by
  cases path <;> simp

theorem head_simple
    {whole : List Nat} {marker : Nat} {chain : List Nat}
    (path : SimpleChainTo whole marker chain) :
    Simple whole (chain.headD 0) := by
  cases path with
  | singleton letter simple _ => simpa using simple
  | cons letter next rest simple _ _ => simpa using simple

theorem transport
    {left right : List Nat} (same : SameInvariant left right)
    {marker : Nat} {chain : List Nat}
    (path : SimpleChainTo left marker chain) :
    SimpleChainTo right marker chain := by
  induction path with
  | singleton letter simple terminal =>
      exact .singleton letter
        ((same.simple letter).mp simple)
        ((same.fsn letter marker).mp terminal)
  | cons letter next rest simple edge tail induction =>
      exact .cons letter next rest
        ((same.simple letter).mp simple)
        ((same.fss letter next).mp edge) induction

/-- In one ambient word, a simple chain is determined by its head; its
terminal marker is determined at the same time. -/
theorem eq_and_marker_eq_of_head_eq
    {whole : List Nat}
    {leftMarker rightMarker : Nat}
    {leftChain rightChain : List Nat}
    (left : SimpleChainTo whole leftMarker leftChain)
    (right : SimpleChainTo whole rightMarker rightChain)
    (sameHead : leftChain.head? = rightChain.head?) :
    leftChain = rightChain ∧ leftMarker = rightMarker := by
  induction left generalizing rightChain rightMarker with
  | singleton letter leftSimple leftTerminal =>
      cases right with
      | singleton rightLetter rightSimple rightTerminal =>
          have letterEq : letter = rightLetter := by
            simpa using sameHead
          subst rightLetter
          have markerEq :=
            adjacent_target_eq_of_simple_source leftSimple
              leftTerminal.2.2 rightTerminal.2.2
          exact ⟨rfl, markerEq⟩
      | cons rightLetter next rest rightSimple rightEdge rightTail =>
          have letterEq : letter = rightLetter := by
            simpa using sameHead
          subst rightLetter
          have targetEq :=
            adjacent_target_eq_of_simple_source leftSimple
              leftTerminal.2.2 rightEdge.2.2
          have nextSimple := rightEdge.2.1
          have markerMultiple := leftTerminal.2.1
          rw [targetEq] at markerMultiple
          exact (nextSimple.not_nonSimple markerMultiple).elim
  | cons letter next rest leftSimple leftEdge leftTail induction =>
      cases right with
      | singleton rightLetter rightSimple rightTerminal =>
          have letterEq : letter = rightLetter := by
            simpa using sameHead
          subst rightLetter
          have targetEq :=
            adjacent_target_eq_of_simple_source leftSimple
              leftEdge.2.2 rightTerminal.2.2
          have nextSimple := leftEdge.2.1
          have markerMultiple := rightTerminal.2.1
          rw [← targetEq] at markerMultiple
          exact (nextSimple.not_nonSimple markerMultiple).elim
      | cons rightLetter rightNext rightRest rightSimple rightEdge
          rightTail =>
          have letterEq : letter = rightLetter := by
            simpa using sameHead
          subst rightLetter
          have nextEq :=
            adjacent_target_eq_of_simple_source leftSimple
              leftEdge.2.2 rightEdge.2.2
          subst rightNext
          have tailResult := induction rightTail rfl
          exact ⟨by rw [tailResult.1], tailResult.2⟩

end SimpleChainTo

/-- A literal nonempty simple factor immediately before a non-simple marker
is a `SimpleChainTo`. -/
theorem simpleChainTo_of_factor
    {whole before segment after : List Nat} {marker : Nat}
    (shape : whole = before ++ segment ++ marker :: after)
    (segmentNonempty : segment ≠ [])
    (allSimple : ∀ letter ∈ segment, Simple whole letter)
    (markerMultiple : NonSimple whole marker) :
    SimpleChainTo whole marker segment := by
  induction segment generalizing before with
  | nil => contradiction
  | cons letter rest induction =>
      cases rest with
      | nil =>
          apply SimpleChainTo.singleton letter
          · exact allSimple letter (by simp)
          · refine ⟨allSimple letter (by simp), markerMultiple, ?_⟩
            apply
              (S5_107.mem_listAdjacentPairs_iff_exists_split
                letter marker whole).2
            exact ⟨before, after, by simpa [List.append_assoc] using shape⟩
      | cons next more =>
          apply SimpleChainTo.cons letter next more
          · exact allSimple letter (by simp)
          · refine
              ⟨allSimple letter (by simp),
                allSimple next (by simp), ?_⟩
            apply
              (S5_107.mem_listAdjacentPairs_iff_exists_split
                letter next whole).2
            refine
              ⟨before, more ++ marker :: after, ?_⟩
            simpa [List.append_assoc] using shape
          · apply induction (before := before ++ [letter])
            · simpa [List.append_assoc] using shape
            · simp
            · intro tested member
              exact allSimple tested (by simp [member])

/-! ## Literal segment reconstruction inside a canonical renderer -/

theorem renderRigidTail_split_of_mem
    (marker : Nat) :
    ∀ {segments : List (List Nat)} {selected : List Nat},
      selected ∈ segments →
      ∃ before after,
        renderRigidTail marker segments =
          before ++ selected ++ marker :: after
  | [], _, member => by
      simp at member
  | segment :: rest, selected, member => by
      rcases List.mem_cons.mp member with selectedFirst | selectedRest
      · subst selected
        exact ⟨[], renderRigidTail marker rest, by simp⟩
      · rcases
          renderRigidTail_split_of_mem marker selectedRest with
          ⟨before, after, shape⟩
        refine ⟨segment ++ [marker] ++ before, after, ?_⟩
        simp [shape, List.append_assoc]

theorem renderRigidBlock_split_segment
    {block : RigidBlock} {segment : List Nat}
    (member : segment ∈ block.segments) :
    ∃ before after,
      renderRigidBlock block =
        before ++ segment ++ block.marker :: after := by
  change segment ∈ block.first :: block.rest at member
  rcases List.mem_cons.mp member with first | inRest
  · subst segment
    refine
      ⟨[],
        renderRigidTail block.marker block.rest ++
          List.replicate (block.exponent - 1) block.marker,
        ?_⟩
    simp [renderRigidBlock, List.append_assoc]
  · rcases renderRigidTail_split_of_mem block.marker inRest with
      ⟨before, after, tailShape⟩
    refine
      ⟨block.first ++ [block.marker] ++ before,
        after ++ List.replicate (block.exponent - 1) block.marker,
        ?_⟩
    simp [renderRigidBlock, tailShape, List.append_assoc]

theorem flatten_split_of_mem
    {selected : List Nat} :
    ∀ {parts : List (List Nat)},
      selected ∈ parts →
      ∃ before after,
        parts.flatten = before ++ selected ++ after
  | [], member => by
      simp at member
  | part :: rest, member => by
      rcases List.mem_cons.mp member with selectedFirst | selectedRest
      · subst selected
        exact ⟨[], rest.flatten, by simp⟩
      · rcases flatten_split_of_mem selectedRest with
          ⟨before, after, shape⟩
        exact ⟨part ++ before, after, by simp [shape, List.append_assoc]⟩

theorem renderCanonical_split_block
    {form : CanonicalForm} {block : RigidBlock}
    (member : block ∈ form.blocks) :
    ∃ before after,
      renderCanonical form =
        before ++ renderRigidBlock block ++ after := by
  have renderMember :
      renderRigidBlock block ∈ form.blockRenders :=
    List.mem_map.mpr ⟨block, member, rfl⟩
  rcases flatten_split_of_mem renderMember with
    ⟨before, after, shape⟩
  exact
    ⟨before, after ++ form.suffix,
      by simp [renderCanonical, shape, List.append_assoc]⟩

theorem renderCanonical_split_segment
    {form : CanonicalForm} {block : RigidBlock}
    (blockMember : block ∈ form.blocks)
    {segment : List Nat} (segmentMember : segment ∈ block.segments) :
    ∃ before after,
      renderCanonical form =
        before ++ segment ++ block.marker :: after := by
  rcases renderCanonical_split_block blockMember with
    ⟨blockBefore, blockAfter, blockShape⟩
  rcases renderRigidBlock_split_segment segmentMember with
    ⟨segmentBefore, segmentAfter, segmentShape⟩
  refine
    ⟨blockBefore ++ segmentBefore,
      segmentAfter ++ blockAfter, ?_⟩
  rw [blockShape, segmentShape]
  simp [List.append_assoc]

/-- Every nonempty stored segment is exactly a simple chain terminating at
the marker of its containing block. -/
theorem CanonicalForm.Valid.segment_chain
    {form : CanonicalForm} (valid : form.Valid)
    {block : RigidBlock} (blockMember : block ∈ form.blocks)
    {segment : List Nat} (segmentMember : segment ∈ block.segments)
    (segmentNonempty : segment ≠ []) :
    SimpleChainTo (renderCanonical form) block.marker segment := by
  rcases renderCanonical_split_segment blockMember segmentMember with
    ⟨before, after, shape⟩
  apply simpleChainTo_of_factor shape segmentNonempty
  · intro letter letterMember
    exact valid.block_segment_simple blockMember segmentMember letterMember
  · exact valid.block_marker_nonSimple blockMember

theorem renderCanonical_head?_eq_marker_of_first_empty
    {form : CanonicalForm}
    (firstEmpty : form.first.first = []) :
    (renderCanonical form).head? = some form.first.marker := by
  simp [renderCanonical_eq, renderRigidBlock, firstEmpty]

theorem renderCanonical_head?_eq_first_head_of_first_nonempty
    {form : CanonicalForm}
    (firstNonempty : form.first.first ≠ []) :
    (renderCanonical form).head? = form.first.first.head? := by
  cases firstShape : form.first.first with
  | nil => exact (firstNonempty firstShape).elim
  | cons head tail =>
      simp [renderCanonical_eq, renderRigidBlock, firstShape]

/-- The first-letter invariant distinguishes the empty-`s₁` case of the
first block.  In the nonempty case, FSN/FSS reconstruct the entire `s₁`
chain and its terminal marker. -/
theorem first_marker_and_segment_eq_of_sameInvariant
    {left right : CanonicalForm}
    (leftValid : left.Valid) (rightValid : right.Valid)
    (same : SameInvariant
      (renderCanonical left) (renderCanonical right)) :
    left.first.marker = right.first.marker ∧
      left.first.first = right.first.first := by
  by_cases leftEmpty : left.first.first = []
  · have leftHead :=
      renderCanonical_head?_eq_marker_of_first_empty leftEmpty
    by_cases rightEmpty : right.first.first = []
    · have rightHead :=
        renderCanonical_head?_eq_marker_of_first_empty rightEmpty
      have markerEq : left.first.marker = right.first.marker := by
        have := leftHead.symm.trans <| same.firstLetter.trans rightHead
        injection this
      exact ⟨markerEq, leftEmpty.trans rightEmpty.symm⟩
    · have rightHead :=
        renderCanonical_head?_eq_first_head_of_first_nonempty rightEmpty
      have markerHeadEq :
          some left.first.marker = right.first.first.head? := by
        exact leftHead.symm.trans <| same.firstLetter.trans rightHead
      have rightFirstMember :
          right.first.first.headD 0 ∈ right.first.first := by
        cases firstShape : right.first.first with
        | nil => exact (rightEmpty firstShape).elim
        | cons head tail => simp
      have rightHeadSimple :=
        rightValid.block_segment_simple
          (block := right.first) (by simp [CanonicalForm.blocks])
          (segment := right.first.first)
          (by simp [RigidBlock.segments]) rightFirstMember
      have leftMarkerMultiple :=
        leftValid.block_marker_nonSimple
          (block := left.first) (by simp [CanonicalForm.blocks])
      have transportedMultiple :=
        (same.nonSimple left.first.marker).mp leftMarkerMultiple
      have headValue :
          right.first.first.headD 0 = left.first.marker := by
        cases firstShape : right.first.first with
        | nil => exact (rightEmpty firstShape).elim
        | cons head tail =>
            simp [firstShape] at markerHeadEq ⊢
            exact markerHeadEq.symm
      rw [headValue] at rightHeadSimple
      exact (rightHeadSimple.not_nonSimple transportedMultiple).elim
  · have leftHead :=
      renderCanonical_head?_eq_first_head_of_first_nonempty leftEmpty
    by_cases rightEmpty : right.first.first = []
    · have rightHead :=
        renderCanonical_head?_eq_marker_of_first_empty rightEmpty
      have leftFirstMember :
          left.first.first.headD 0 ∈ left.first.first := by
        cases firstShape : left.first.first with
        | nil => exact (leftEmpty firstShape).elim
        | cons head tail => simp
      have leftHeadSimple :=
        leftValid.block_segment_simple
          (block := left.first) (by simp [CanonicalForm.blocks])
          (segment := left.first.first)
          (by simp [RigidBlock.segments]) leftFirstMember
      have transportedSimple :=
        (same.simple (left.first.first.headD 0)).mp leftHeadSimple
      have rightMarkerMultiple :=
        rightValid.block_marker_nonSimple
          (block := right.first) (by simp [CanonicalForm.blocks])
      have markerHeadEq :
          left.first.first.head? = some right.first.marker := by
        exact leftHead.symm.trans <| same.firstLetter.trans rightHead
      have headValue :
          left.first.first.headD 0 = right.first.marker := by
        cases firstShape : left.first.first with
        | nil => exact (leftEmpty firstShape).elim
        | cons head tail =>
            simp [firstShape] at markerHeadEq ⊢
            exact markerHeadEq
      rw [headValue] at transportedSimple
      exact (transportedSimple.not_nonSimple rightMarkerMultiple).elim
    · have rightHead :=
        renderCanonical_head?_eq_first_head_of_first_nonempty rightEmpty
      have segmentHeadEq :
          left.first.first.head? = right.first.first.head? := by
        exact leftHead.symm.trans <| same.firstLetter.trans rightHead
      have leftChain := leftValid.segment_chain
        (block := left.first) (by simp [CanonicalForm.blocks])
        (segment := left.first.first) (by simp [RigidBlock.segments])
        leftEmpty
      have transportedChain := leftChain.transport same
      have rightChain := rightValid.segment_chain
        (block := right.first) (by simp [CanonicalForm.blocks])
        (segment := right.first.first) (by simp [RigidBlock.segments])
        rightEmpty
      have aligned :=
        transportedChain.eq_and_marker_eq_of_head_eq
          rightChain segmentHeadEq
      exact ⟨aligned.2, aligned.1⟩

/-! ## Reconstruction and ordering of the non-simple markers -/

theorem mem_renderCanonical_iff
    (form : CanonicalForm) (letter : Nat) :
    letter ∈ renderCanonical form ↔
      (∃ block ∈ form.blocks,
        letter ∈ renderRigidBlock block) ∨
        letter ∈ form.suffix := by
  simp only [renderCanonical, CanonicalForm.blockRenders,
    List.mem_append, List.mem_flatten, List.mem_map]
  constructor
  · rintro (⟨rendered, ⟨block, blockMember, rfl⟩, letterMember⟩ | inSuffix)
    · exact Or.inl ⟨block, blockMember, letterMember⟩
    · exact Or.inr inSuffix
  · rintro (⟨block, blockMember, letterMember⟩ | inSuffix)
    · exact Or.inl ⟨renderRigidBlock block, ⟨block, blockMember, rfl⟩,
        letterMember⟩
    · exact Or.inr inSuffix

/-- Conditions (I),(II),(IV),(V) identify the non-simple support with the
list of block markers. -/
theorem CanonicalForm.Valid.nonSimple_iff_mem_markers
    {form : CanonicalForm} (valid : form.Valid) (letter : Nat) :
    NonSimple (renderCanonical form) letter ↔
      letter ∈ form.markers := by
  constructor
  · intro multiple
    have member := multiple.mem
    rcases (mem_renderCanonical_iff form letter).1 member with
        ⟨block, blockMember, letterMember⟩ | suffixMember
    · have withinMultiple :
          NonSimple (renderRigidBlock block) letter := by
        unfold NonSimple at multiple ⊢
        rw [valid.count_block_letter blockMember letterMember] at multiple
        exact multiple
      have markerEq :=
        (valid.block_valid blockMember).eq_marker_of_nonSimple
          letterMember withinMultiple
      rw [markerEq]
      exact List.mem_map.mpr ⟨block, blockMember, rfl⟩
    · have simple := valid.conditionIV letter suffixMember
      exact (simple.not_nonSimple multiple).elim
  · intro markerMember
    rcases List.mem_map.mp markerMember with
      ⟨block, blockMember, markerEq⟩
    subst letter
    exact valid.block_marker_nonSimple blockMember

theorem CanonicalForm.Valid.mem_tailMarkers_iff
    {form : CanonicalForm} (valid : form.Valid) (marker : Nat) :
    marker ∈ form.tailMarkers ↔
      marker ∈ form.markers ∧ marker ≠ form.first.marker := by
  have markerNodup := valid.markers_nodup
  have firstAbsent :
      form.first.marker ∉ form.tailMarkers := by
    simpa [CanonicalForm.markers, CanonicalForm.blocks,
      CanonicalForm.tailMarkers] using
      (List.nodup_cons.mp markerNodup).1
  constructor
  · intro tailMember
    constructor
    · change marker ∈ form.first.marker :: form.tailMarkers
      exact List.Mem.tail form.first.marker tailMember
    · intro equal
      subst marker
      exact firstAbsent tailMember
  · rintro ⟨markerMember, different⟩
    change marker ∈ form.first.marker :: form.tailMarkers at markerMember
    exact (List.mem_cons.mp markerMember).resolve_left different

/-- Strictly increasing lists of naturals are determined by membership. -/
theorem pairwise_lt_list_eq_of_same_mem
    {left right : List Nat}
    (leftSorted : left.Pairwise (fun x y => x < y))
    (rightSorted : right.Pairwise (fun x y => x < y))
    (sameMem : ∀ letter, letter ∈ left ↔ letter ∈ right) :
    left = right := by
  have leftNodup : left.Nodup :=
    leftSorted.imp fun {_ _} less => Nat.ne_of_lt less
  have rightNodup : right.Nodup :=
    rightSorted.imp fun {_ _} less => Nat.ne_of_lt less
  have permutation : left.Perm right := by
    rw [List.perm_iff_count]
    intro letter
    rw [leftNodup.count, rightNodup.count]
    simp only [sameMem letter]
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ leftLe rightLe => Nat.le_antisymm leftLe rightLe)
    (leftSorted.imp fun {_ _} less => Nat.le_of_lt less)
    (rightSorted.imp fun {_ _} less => Nat.le_of_lt less)
    permutation

theorem tailMarkers_eq_of_sameInvariant
    {left right : CanonicalForm}
    (leftValid : left.Valid) (rightValid : right.Valid)
    (same : SameInvariant
      (renderCanonical left) (renderCanonical right))
    (firstMarkerEq : left.first.marker = right.first.marker) :
    left.tailMarkers = right.tailMarkers := by
  apply pairwise_lt_list_eq_of_same_mem
    leftValid.conditionIII rightValid.conditionIII
  intro marker
  rw [leftValid.mem_tailMarkers_iff,
    rightValid.mem_tailMarkers_iff, firstMarkerEq]
  have leftMarker :=
    leftValid.nonSimple_iff_mem_markers marker
  have rightMarker :=
    rightValid.nonSimple_iff_mem_markers marker
  rw [← leftMarker, ← rightMarker, same.nonSimple marker]

/-! ## Maximal simple-component heads -/

/-- There is no adjacent factor entering the unique initial occurrence. -/
theorem no_adjacent_into_simple_initial
    {head : Nat} {tail : List Nat}
    (simple : Simple (head :: tail) head) (source : Nat) :
    (source, head) ∉
      S5_107.listAdjacentPairs (head :: tail) := by
  have headAbsent : head ∉ tail := by
    intro member
    have positive : 0 < tail.count head :=
      List.count_pos_iff.mpr member
    unfold Simple at simple
    simp only [List.count_cons_self] at simple
    omega
  cases tail with
  | nil => simp
  | cons next rest =>
      intro edge
      simp only [S5_107.listAdjacentPairs_cons_cons,
        List.mem_cons] at edge
      rcases edge with firstEdge | laterEdge
      · have targetEq : head = next :=
          congrArg Prod.snd firstEdge
        exact headAbsent (by simp [targetEq])
      · exact headAbsent (adjacent_target_mem laterEdge)

/-- A prefix is either empty or ends in a globally non-simple letter. -/
def SimpleLeftBoundary (whole before : List Nat) : Prop :=
  before = [] ∨
    ∃ prefixPart marker,
      before = prefixPart ++ [marker] ∧ NonSimple whole marker

/-- A simple factor beginning immediately after a non-simple boundary (or at
the start of the whole word) has no incoming FSS edge. -/
theorem no_fss_into_head_of_simple_factor
    {whole before rest : List Nat} {head : Nat}
    (shape : whole = before ++ head :: rest)
    (simple : Simple whole head)
    (boundary : SimpleLeftBoundary whole before) :
    ∀ source, ¬ FSS whole source head := by
  intro source factor
  rcases boundary with empty | ⟨prefixPart, marker, beforeShape, multiple⟩
  · subst before
    have wholeShape : whole = head :: rest := by simpa using shape
    subst whole
    exact no_adjacent_into_simple_initial simple source factor.2.2
  · have markerEdge :
        (marker, head) ∈ S5_107.listAdjacentPairs whole := by
      apply
        (S5_107.mem_listAdjacentPairs_iff_exists_split
          marker head whole).2
      refine ⟨prefixPart, rest, ?_⟩
      simpa [beforeShape, List.append_assoc] using shape
    have sourceEq :=
      adjacent_source_eq_of_simple_target simple
        factor.2.2 markerEdge
    have sourceSimple := factor.1
    rw [sourceEq] at sourceSimple
    exact sourceSimple.not_nonSimple multiple

/-- Every nonempty list has a last-element decomposition. -/
theorem exists_eq_append_singleton_of_ne_nil {α : Type} :
    ∀ {letters : List α},
      letters ≠ [] →
      ∃ prefixPart final, letters = prefixPart ++ [final]
  | [], nonempty => by contradiction
  | head :: tail, _ => by
      cases tail with
      | nil => exact ⟨[], head, rfl⟩
      | cons next rest =>
          rcases exists_eq_append_singleton_of_ne_nil
              (letters := next :: rest) (by simp) with
            ⟨prefixPart, final, shape⟩
          exact ⟨head :: prefixPart, final, by simp [shape]⟩

theorem renderRigidTail_eq_append_marker_of_nonempty
    (marker : Nat) :
    ∀ {segments : List (List Nat)},
      segments ≠ [] →
      ∃ prefixPart,
        renderRigidTail marker segments = prefixPart ++ [marker]
  | [], nonempty => by contradiction
  | segment :: rest, _ => by
      cases rest with
      | nil =>
          exact ⟨segment, by simp⟩
      | cons next more =>
          rcases renderRigidTail_eq_append_marker_of_nonempty marker
              (segments := next :: more) (by simp) with
            ⟨prefixPart, shape⟩
          exact
            ⟨segment ++ marker :: prefixPart,
              by simp [shape, List.append_assoc]⟩

/-- Every valid rigid block ends in its marker. -/
theorem RigidBlock.Valid.render_eq_append_marker
    {block : RigidBlock} (valid : block.Valid) :
    ∃ prefixPart,
      renderRigidBlock block = prefixPart ++ [block.marker] := by
  rcases valid.exponentRange with exponent | exponent | exponent
  · by_cases restEmpty : block.rest = []
    · exact
        ⟨block.first,
          by simp [renderRigidBlock, exponent, restEmpty]⟩
    · rcases renderRigidTail_eq_append_marker_of_nonempty
          block.marker restEmpty with ⟨tailPrefix, tailShape⟩
      exact
        ⟨block.first ++ [block.marker] ++ tailPrefix,
          by simp [renderRigidBlock, exponent, tailShape, List.append_assoc]⟩
  · exact
      ⟨block.first ++ [block.marker] ++
          renderRigidTail block.marker block.rest,
        by simp [renderRigidBlock, exponent, List.append_assoc]⟩
  · exact
      ⟨block.first ++ [block.marker] ++
          renderRigidTail block.marker block.rest ++ [block.marker],
        by simp [renderRigidBlock, exponent, List.append_assoc]⟩

/-- Accumulator form of the fact that each tail segment is bracketed on the
left and right by the block marker. -/
theorem renderRigidTail_split_with_left_marker
    (marker : Nat) :
    ∀ (prefixPart : List Nat) {segments : List (List Nat)}
        {selected : List Nat},
      selected ∈ segments →
      ∃ before after base,
        prefixPart ++ [marker] ++ renderRigidTail marker segments =
          before ++ selected ++ marker :: after ∧
        before = base ++ [marker]
  | prefixPart, [], _, member => by
      simp at member
  | prefixPart, segment :: rest, selected, member => by
      rcases List.mem_cons.mp member with selectedFirst | selectedRest
      · subst selected
        exact
          ⟨prefixPart ++ [marker], renderRigidTail marker rest, prefixPart,
            by simp [List.append_assoc], rfl⟩
      · rcases
          renderRigidTail_split_with_left_marker marker
            (prefixPart ++ [marker] ++ segment) selectedRest with
          ⟨before, after, base, shape, boundary⟩
        exact
          ⟨before, after, base,
            by simpa [List.append_assoc] using shape, boundary⟩

/-- A stored segment has a canonical occurrence whose left boundary is
empty or globally non-simple. -/
theorem CanonicalForm.Valid.segment_occurrence_with_boundary
    {form : CanonicalForm} (valid : form.Valid)
    {block : RigidBlock} (blockMember : block ∈ form.blocks)
    {segment : List Nat} (segmentMember : segment ∈ block.segments) :
    ∃ before after,
      renderCanonical form =
          before ++ segment ++ block.marker :: after ∧
        SimpleLeftBoundary (renderCanonical form) before := by
  have blocksShape :
      ∃ beforeBlocks afterBlocks,
        form.blocks = beforeBlocks ++ block :: afterBlocks :=
    List.mem_iff_append.mp blockMember
  rcases blocksShape with ⟨beforeBlocks, afterBlocks, blocksEq⟩
  let beforeRenders := beforeBlocks.map renderRigidBlock
  let afterRenders := afterBlocks.map renderRigidBlock
  have rendersEq :
      form.blockRenders =
        beforeRenders ++ renderRigidBlock block :: afterRenders := by
    simp [CanonicalForm.blockRenders, blocksEq, beforeRenders,
      afterRenders]
  have wholeBlockShape :
      renderCanonical form =
        beforeRenders.flatten ++ renderRigidBlock block ++
          afterRenders.flatten ++ form.suffix := by
    simp [renderCanonical, rendersEq, List.append_assoc]
  rcases List.mem_cons.mp segmentMember with firstSegment | restSegment
  · subst segment
    refine
      ⟨beforeRenders.flatten,
        renderRigidTail block.marker block.rest ++
          List.replicate (block.exponent - 1) block.marker ++
          afterRenders.flatten ++ form.suffix,
        ?_, ?_⟩
    · rw [wholeBlockShape]
      simp [renderRigidBlock, List.append_assoc]
    · by_cases noEarlier : beforeBlocks = []
      · left
        simp [beforeRenders, noEarlier]
      · right
        rcases exists_eq_append_singleton_of_ne_nil noEarlier with
          ⟨initialBlocks, previous, beforeShape⟩
        have previousMember : previous ∈ form.blocks := by
          rw [blocksEq, beforeShape]
          simp
        rcases
            (valid.block_valid previousMember).render_eq_append_marker with
          ⟨previousPrefix, previousShape⟩
        refine
          ⟨(initialBlocks.map renderRigidBlock).flatten ++ previousPrefix,
            previous.marker, ?_, valid.block_marker_nonSimple previousMember⟩
        simp [beforeRenders, beforeShape, previousShape,
          List.append_assoc]
  · rcases
        renderRigidTail_split_with_left_marker block.marker
          block.first restSegment with
        ⟨innerBefore, innerAfter, base, innerShape, innerBoundary⟩
    refine
      ⟨beforeRenders.flatten ++ innerBefore,
        innerAfter ++
          List.replicate (block.exponent - 1) block.marker ++
          afterRenders.flatten ++ form.suffix,
        ?_, ?_⟩
    · rw [wholeBlockShape]
      simp [renderRigidBlock, innerShape, List.append_assoc]
    · right
      refine
        ⟨beforeRenders.flatten ++ base, block.marker, ?_,
          valid.block_marker_nonSimple blockMember⟩
      simp [innerBoundary, List.append_assoc]

/-- The head of every nonempty stored segment is a maximal FSS-component
head. -/
theorem CanonicalForm.Valid.no_fss_into_segment_head
    {form : CanonicalForm} (valid : form.Valid)
    {block : RigidBlock} (blockMember : block ∈ form.blocks)
    {segment : List Nat} (segmentMember : segment ∈ block.segments)
    (segmentNonempty : segment ≠ []) :
    ∀ source, ¬ FSS (renderCanonical form) source (segment.headD 0) := by
  rcases valid.segment_occurrence_with_boundary blockMember segmentMember with
    ⟨before, after, shape, boundary⟩
  cases segmentShape : segment with
  | nil => exact (segmentNonempty segmentShape).elim
  | cons head tail =>
      have headSimple := valid.block_segment_simple blockMember segmentMember
        (letter := head) (by simp [segmentShape])
      have factorShape :
          renderCanonical form = before ++ head :: (tail ++ block.marker :: after) := by
        simpa [segmentShape, List.append_assoc] using shape
      simpa [segmentShape] using
        no_fss_into_head_of_simple_factor factorShape headSimple boundary

/-! ## Invariant recognition of the stored simple components -/

/-- A simple-component head attached to `marker`, expressed entirely in
terms of `FSN` and `FSS` of the ambient list. -/
def AttachedHead (whole : List Nat) (marker head : Nat) : Prop :=
  ∃ chain : List Nat,
    chain.head? = some head ∧
      SimpleChainTo whole marker chain ∧
        ∀ source, ¬ FSS whole source head

namespace AttachedHead

theorem transport
    {left right : List Nat} (same : SameInvariant left right)
    {marker head : Nat} (attached : AttachedHead left marker head) :
    AttachedHead right marker head := by
  rcases attached with ⟨chain, chainHead, path, noIncoming⟩
  exact
    ⟨chain, chainHead, path.transport same,
      fun source incoming =>
        noIncoming source ((same.fss source head).mpr incoming)⟩

theorem simple
    {whole : List Nat} {marker head : Nat}
    (attached : AttachedHead whole marker head) :
    Simple whole head := by
  rcases attached with ⟨chain, chainHead, path, _⟩
  cases chain with
  | nil => simp at chainHead
  | cons first rest =>
      simp only [List.head?_cons, Option.some.injEq] at chainHead
      simpa [chainHead] using path.head_simple

theorem mem
    {whole : List Nat} {marker head : Nat}
    (attached : AttachedHead whole marker head) :
    head ∈ whole :=
  attached.simple.mem

end AttachedHead

/-- A simple occurrence at the final position has no adjacent successor. -/
theorem no_adjacent_from_simple_final
    {whole prefixPart : List Nat} {source : Nat}
    (shape : whole = prefixPart ++ [source])
    (simple : Simple whole source) (target : Nat) :
    (source, target) ∉ S5_107.listAdjacentPairs whole := by
  have reverseSimple : Simple whole.reverse source := by
    unfold Simple at simple ⊢
    simpa using simple
  have reverseShape : whole.reverse = source :: prefixPart.reverse := by
    rw [shape]
    simp [List.reverse_append]
  intro edge
  have reverseEdge :
      (target, source) ∈
        S5_107.listAdjacentPairs whole.reverse :=
    (mem_adjacentPairs_reverse_iff whole target source).2 edge
  rw [reverseShape] at reverseSimple reverseEdge
  exact no_adjacent_into_simple_initial reverseSimple target reverseEdge

/-- Once a globally simple source is known to lie in a final suffix, every
adjacent successor lies in the same suffix. -/
theorem adjacent_target_mem_suffix_of_simple_source
    {whole prefixPart suffix : List Nat} {source target : Nat}
    (shape : whole = prefixPart ++ suffix)
    (simple : Simple whole source)
    (sourceMember : source ∈ suffix)
    (edge : (source, target) ∈ S5_107.listAdjacentPairs whole) :
    target ∈ suffix := by
  rcases List.mem_iff_append.mp sourceMember with
    ⟨suffixBefore, suffixAfter, suffixShape⟩
  cases suffixAfter with
  | nil =>
      have finalShape :
          whole = (prefixPart ++ suffixBefore) ++ [source] := by
        rw [shape, suffixShape]
        simp [List.append_assoc]
      exact (no_adjacent_from_simple_final finalShape simple target edge).elim
  | cons actualTarget suffixRest =>
      have actualEdge :
          (source, actualTarget) ∈
            S5_107.listAdjacentPairs whole := by
        apply
          (S5_107.mem_listAdjacentPairs_iff_exists_split
            source actualTarget whole).2
        refine ⟨prefixPart ++ suffixBefore, suffixRest, ?_⟩
        rw [shape, suffixShape]
        simp [List.append_assoc]
      have targetEq :=
        adjacent_target_eq_of_simple_source simple edge actualEdge
      subst target
      rw [suffixShape]
      simp

/-- A simple chain ending at a non-simple marker cannot start in the final
all-simple suffix of a canonical word. -/
theorem SimpleChainTo.head_not_mem_simple_suffix
    {whole prefixPart suffix : List Nat} {marker : Nat}
    {chain : List Nat} (path : SimpleChainTo whole marker chain)
    (shape : whole = prefixPart ++ suffix)
    (suffixSimple : ∀ letter ∈ suffix, Simple whole letter) :
    chain.headD 0 ∉ suffix := by
  induction path with
  | singleton letter simple terminal =>
      intro letterMember
      have markerMember :=
        adjacent_target_mem_suffix_of_simple_source
          shape simple letterMember terminal.2.2
      have markerSimple := suffixSimple marker markerMember
      exact markerSimple.not_nonSimple terminal.2.1
  | cons letter next rest simple edge tail induction =>
      intro letterMember
      have nextMember :=
        adjacent_target_mem_suffix_of_simple_source
          shape simple letterMember edge.2.2
      exact induction nextMember

/-- If a member of a stored simple segment has no incoming `FSS`, it is the
literal head of that segment. -/
theorem segment_head?_eq_some_of_no_fss_into
    {whole before segment after : List Nat}
    {marker head : Nat}
    (shape : whole = before ++ segment ++ marker :: after)
    (headMember : head ∈ segment)
    (segmentSimple : ∀ letter ∈ segment, Simple whole letter)
    (noIncoming : ∀ source, ¬ FSS whole source head) :
    segment.head? = some head := by
  rcases List.mem_iff_append.mp headMember with
    ⟨initial, trailing, segmentShape⟩
  by_cases initialEmpty : initial = []
  · subst initial
    simp at segmentShape
    simp [segmentShape]
  · rcases exists_eq_append_singleton_of_ne_nil initialEmpty with
      ⟨earlier, previous, initialShape⟩
    have previousMember : previous ∈ segment := by
      rw [segmentShape, initialShape]
      simp
    have previousSimple := segmentSimple previous previousMember
    have headSimple := segmentSimple head headMember
    have adjacent :
        (previous, head) ∈
          S5_107.listAdjacentPairs whole := by
      apply
        (S5_107.mem_listAdjacentPairs_iff_exists_split
          previous head whole).2
      refine ⟨before ++ earlier, trailing ++ marker :: after, ?_⟩
      rw [shape, segmentShape, initialShape]
      simp [List.append_assoc]
    exact (noIncoming previous ⟨previousSimple, headSimple, adjacent⟩).elim

theorem headD_eq_of_head?_eq_some
    {letters : List Nat} {head : Nat}
    (sameHead : letters.head? = some head) :
    letters.headD 0 = head := by
  cases letters with
  | nil => simp at sameHead
  | cons first rest => simpa using sameHead

/-- Every nonempty stored segment is recognized by one invariant-defined
attached head. -/
theorem CanonicalForm.Valid.attachedHead_of_segment
    {form : CanonicalForm} (valid : form.Valid)
    {block : RigidBlock} (blockMember : block ∈ form.blocks)
    {segment : List Nat} (segmentMember : segment ∈ block.segments)
    (segmentNonempty : segment ≠ []) :
    AttachedHead (renderCanonical form) block.marker
      (segment.headD 0) := by
  refine
    ⟨segment, ?_, valid.segment_chain blockMember segmentMember
      segmentNonempty,
      valid.no_fss_into_segment_head blockMember segmentMember
        segmentNonempty⟩
  cases segment with
  | nil => contradiction
  | cons head tail => simp

/-- Conversely, every invariant-defined attached head in a canonical word
is the head of a nonempty stored segment of the uniquely corresponding
marker block. -/
theorem CanonicalForm.Valid.exists_segment_of_attachedHead
    {form : CanonicalForm} (valid : form.Valid)
    {marker head : Nat}
    (attached : AttachedHead (renderCanonical form) marker head) :
    ∃ block ∈ form.blocks,
      block.marker = marker ∧
        ∃ segment ∈ block.segments,
          segment ≠ [] ∧ segment.headD 0 = head := by
  rcases attached with ⟨chain, chainHead, path, noIncoming⟩
  have headSimple : Simple (renderCanonical form) head := by
    cases chain with
    | nil => simp at chainHead
    | cons first rest =>
        simp only [List.head?_cons, Option.some.injEq] at chainHead
        simpa [chainHead] using path.head_simple
  have headMember := headSimple.mem
  rcases (mem_renderCanonical_iff form head).1 headMember with
      ⟨block, blockMember, inBlock⟩ | inSuffix
  · rcases (mem_renderRigidBlock_iff block head).1 inBlock with
        isMarker | inFirst | inRest
    · subst head
      exact
        (headSimple.not_nonSimple
          (valid.block_marker_nonSimple blockMember)).elim
    · let segment := block.first
      have segmentMember : segment ∈ block.segments := by
        simp [segment, RigidBlock.segments]
      have segmentNonempty : segment ≠ [] := by
        intro empty
        have impossible : head ∈ segment := by
          simpa [segment] using inFirst
        rw [empty] at impossible
        simp at impossible
      rcases valid.segment_occurrence_with_boundary
          blockMember segmentMember with
        ⟨before, after, occurrence, _⟩
      have segmentHead :=
        segment_head?_eq_some_of_no_fss_into occurrence inFirst
          (fun letter member =>
            valid.block_segment_simple blockMember segmentMember member)
          noIncoming
      have storedPath := valid.segment_chain blockMember segmentMember
        segmentNonempty
      have aligned :=
        storedPath.eq_and_marker_eq_of_head_eq path
          (segmentHead.trans chainHead.symm)
      exact
        ⟨block, blockMember, aligned.2, segment, segmentMember,
          segmentNonempty, headD_eq_of_head?_eq_some segmentHead⟩
    · rcases inRest with ⟨segment, inRest, headInSegment⟩
      have segmentMember : segment ∈ block.segments := by
        simp [RigidBlock.segments, inRest]
      have segmentNonempty : segment ≠ [] := by
        intro empty
        rw [empty] at headInSegment
        simp at headInSegment
      rcases valid.segment_occurrence_with_boundary
          blockMember segmentMember with
        ⟨before, after, occurrence, _⟩
      have segmentHead :=
        segment_head?_eq_some_of_no_fss_into occurrence headInSegment
          (fun letter member =>
            valid.block_segment_simple blockMember segmentMember member)
          noIncoming
      have storedPath := valid.segment_chain blockMember segmentMember
        segmentNonempty
      have aligned :=
        storedPath.eq_and_marker_eq_of_head_eq path
          (segmentHead.trans chainHead.symm)
      exact
        ⟨block, blockMember, aligned.2, segment, segmentMember,
          segmentNonempty, headD_eq_of_head?_eq_some segmentHead⟩
  · let prefixPart := form.blockRenders.flatten
    have wholeShape :
        renderCanonical form = prefixPart ++ form.suffix := by
      rfl
    have chainHeadD : chain.headD 0 = head := by
      cases chain with
      | nil => simp at chainHead
      | cons first rest => simpa using chainHead
    have forbidden :=
      path.head_not_mem_simple_suffix wholeShape valid.conditionIV
    rw [chainHeadD] at forbidden
    exact (forbidden inSuffix).elim

theorem CanonicalForm.Valid.attachedHead_iff
    {form : CanonicalForm} (valid : form.Valid)
    (marker head : Nat) :
    AttachedHead (renderCanonical form) marker head ↔
      ∃ block ∈ form.blocks,
        block.marker = marker ∧
          ∃ segment ∈ block.segments,
            segment ≠ [] ∧ segment.headD 0 = head := by
  constructor
  · exact valid.exists_segment_of_attachedHead
  · rintro ⟨block, blockMember, rfl, segment, segmentMember,
        segmentNonempty, rfl⟩
    exact valid.attachedHead_of_segment
      blockMember segmentMember segmentNonempty

/-- A pairwise key-distinct list contains at most one element with a given
key. -/
theorem eq_of_mem_of_mem_of_pairwise_key_ne
    {α : Type} (key : α → Nat) :
    ∀ {items : List α} {left right : α},
      items.Pairwise (fun a b => key a ≠ key b) →
      left ∈ items → right ∈ items → key left = key right →
      left = right
  | [], _, _, _, leftMember, _, _ => by simp at leftMember
  | first :: rest, left, right, pairwise, leftMember, rightMember,
      sameKey => by
      have firstRelations := (List.pairwise_cons.mp pairwise).1
      have restPairwise := (List.pairwise_cons.mp pairwise).2
      rcases List.mem_cons.mp leftMember with leftFirst | leftRest
      · subst left
        rcases List.mem_cons.mp rightMember with rightFirst | rightRest
        · exact rightFirst.symm
        · exact (firstRelations right rightRest sameKey).elim
      · rcases List.mem_cons.mp rightMember with rightFirst | rightRest
        · subst right
          exact
            (firstRelations left leftRest sameKey.symm).elim
        · exact
            eq_of_mem_of_mem_of_pairwise_key_ne key
              restPairwise leftRest rightRest sameKey

theorem CanonicalForm.Valid.block_eq_of_mem_of_marker_eq
    {form : CanonicalForm} (valid : form.Valid)
    {left right : RigidBlock}
    (leftMember : left ∈ form.blocks)
    (rightMember : right ∈ form.blocks)
    (sameMarker : left.marker = right.marker) :
    left = right :=
  eq_of_mem_of_mem_of_pairwise_key_ne
    RigidBlock.marker valid.block_markers_pairwise_ne
      leftMember rightMember sameMarker

/-- A selected tail segment contributes its full multiplicity to the
rendered rigid tail. -/
theorem count_le_count_renderRigidTail_of_mem
    (marker letter : Nat) :
    ∀ {segments : List (List Nat)} {selected : List Nat},
      selected ∈ segments →
      selected.count letter ≤
        (renderRigidTail marker segments).count letter
  | [], _, member => by simp at member
  | segment :: rest, selected, member => by
      rcases List.mem_cons.mp member with selectedFirst | selectedRest
      · subst selected
        simp [renderRigidTail, List.count_append]
      · have induction :=
          count_le_count_renderRigidTail_of_mem
            marker letter selectedRest
        simp only [renderRigidTail_cons, List.count_append,
          List.count_cons]
        omega

/-- The head of a nonempty first segment cannot also be the head of a tail
segment; otherwise (Ri1) would declare a twice-occurring letter simple. -/
theorem RigidBlock.Valid.first_headD_ne_rest_headD
    {block : RigidBlock} (valid : block.Valid)
    (firstNonempty : block.first ≠ [])
    {segment : List Nat} (segmentMember : segment ∈ block.rest) :
    block.first.headD 0 ≠ segment.headD 0 := by
  have segmentNonempty := valid.positiveSegments segment segmentMember
  have firstHeadMember : block.first.headD 0 ∈ block.first := by
    cases firstShape : block.first with
    | nil => exact (firstNonempty firstShape).elim
    | cons head tail => simp
  have segmentHeadMember : segment.headD 0 ∈ segment := by
    cases segmentShape : segment with
    | nil => exact (segmentNonempty segmentShape).elim
    | cons head tail => simp
  intro sameHead
  have firstSimple :=
    valid.ri1 block.first (by simp [RigidBlock.segments])
      (block.first.headD 0) firstHeadMember
  have firstPositive : 0 < block.first.count (block.first.headD 0) :=
    List.count_pos_iff.mpr firstHeadMember
  have segmentPositive : 0 < segment.count (block.first.headD 0) := by
    apply List.count_pos_iff.mpr
    rw [sameHead]
    exact segmentHeadMember
  have tailLower :=
    count_le_count_renderRigidTail_of_mem
      block.marker (block.first.headD 0) segmentMember
  unfold Simple at firstSimple
  simp only [renderRigidBlock, List.count_append] at firstSimple
  omega

/-- Lists whose entries are cross-determined by a displayed key are equal
as soon as their key lists agree. -/
theorem list_eq_of_map_eq_of_cross_key
    {α β : Type} (key : α → β) :
    ∀ (left right : List α),
      left.map key = right.map key →
      (∀ a ∈ left, ∀ b ∈ right, key a = key b → a = b) →
      left = right
  | [], right, sameKeys, _ => by
      cases right with
      | nil => rfl
      | cons head tail => simp at sameKeys
  | head :: tail, right, sameKeys, cross => by
      cases right with
      | nil => simp at sameKeys
      | cons rightHead rightTail =>
          have headKey : key head = key rightHead := by
            simpa using congrArg List.head? sameKeys
          have headEq := cross head (by simp) rightHead (by simp) headKey
          subst rightHead
          have tailKeys : tail.map key = rightTail.map key := by
            simpa using sameKeys
          have tailCross :
              ∀ a ∈ tail, ∀ b ∈ rightTail,
                key a = key b → a = b := by
            intro a aMember b bMember keyEq
            exact cross a (by simp [aMember]) b (by simp [bMember]) keyEq
          rw [list_eq_of_map_eq_of_cross_key key
            tail rightTail tailKeys tailCross]

/-- Equal component heads reconstruct equal stored simple chains; their
terminal markers are recovered simultaneously. -/
theorem segment_eq_and_marker_eq_of_headD_eq
    {left right : CanonicalForm}
    (leftValid : left.Valid) (rightValid : right.Valid)
    (same : SameInvariant
      (renderCanonical left) (renderCanonical right))
    {leftBlock rightBlock : RigidBlock}
    (leftBlockMember : leftBlock ∈ left.blocks)
    (rightBlockMember : rightBlock ∈ right.blocks)
    {leftSegment rightSegment : List Nat}
    (leftSegmentMember : leftSegment ∈ leftBlock.segments)
    (rightSegmentMember : rightSegment ∈ rightBlock.segments)
    (leftNonempty : leftSegment ≠ [])
    (rightNonempty : rightSegment ≠ [])
    (sameHead : leftSegment.headD 0 = rightSegment.headD 0) :
    leftSegment = rightSegment ∧
      leftBlock.marker = rightBlock.marker := by
  have leftPath := leftValid.segment_chain
    leftBlockMember leftSegmentMember leftNonempty
  have rightPath := rightValid.segment_chain
    rightBlockMember rightSegmentMember rightNonempty
  have headQuestion :
      leftSegment.head? = rightSegment.head? := by
    cases leftShape : leftSegment with
    | nil => exact (leftNonempty leftShape).elim
    | cons leftHead leftTail =>
        cases rightShape : rightSegment with
        | nil => exact (rightNonempty rightShape).elim
        | cons rightHead rightTail =>
            rw [leftShape, rightShape] at sameHead
            change leftHead = rightHead at sameHead
            exact congrArg some sameHead
  exact
    (leftPath.transport same).eq_and_marker_eq_of_head_eq
      rightPath headQuestion

/-- Global multiplicity alignment localizes to any pair of blocks with the
same marker. -/
theorem same_block_multiplicityClass
    {left right : CanonicalForm}
    (leftValid : left.Valid) (rightValid : right.Valid)
    (same : SameInvariant
      (renderCanonical left) (renderCanonical right))
    {leftBlock rightBlock : RigidBlock}
    (leftBlockMember : leftBlock ∈ left.blocks)
    (rightBlockMember : rightBlock ∈ right.blocks)
    (sameMarker : leftBlock.marker = rightBlock.marker) :
    SameMultiplicityClass
      (renderRigidBlock leftBlock) (renderRigidBlock rightBlock)
      leftBlock.marker := by
  have global := same.multiplicity leftBlock.marker
  have rightMarkerMember :
      leftBlock.marker ∈ renderRigidBlock rightBlock := by
    rw [sameMarker]
    exact marker_mem_renderRigidBlock rightBlock
  unfold SameMultiplicityClass at global ⊢
  rw [leftValid.count_block_letter leftBlockMember
        (marker_mem_renderRigidBlock leftBlock),
      rightValid.count_block_letter rightBlockMember rightMarkerMember]
    at global
  exact global

/-- A nonempty segment in one aligned block has a segment with the same
head in the block carrying the same marker on the other side. -/
theorem exists_matching_segment
    {left right : CanonicalForm}
    (leftValid : left.Valid) (rightValid : right.Valid)
    (same : SameInvariant
      (renderCanonical left) (renderCanonical right))
    {leftBlock rightBlock : RigidBlock}
    (leftBlockMember : leftBlock ∈ left.blocks)
    (rightBlockMember : rightBlock ∈ right.blocks)
    (sameMarker : leftBlock.marker = rightBlock.marker)
    {leftSegment : List Nat}
    (leftSegmentMember : leftSegment ∈ leftBlock.segments)
    (leftNonempty : leftSegment ≠ []) :
    ∃ rightSegment ∈ rightBlock.segments,
      rightSegment ≠ [] ∧
        rightSegment.headD 0 = leftSegment.headD 0 := by
  have leftAttached := leftValid.attachedHead_of_segment
    leftBlockMember leftSegmentMember leftNonempty
  have rightAttached := leftAttached.transport same
  rcases rightValid.exists_segment_of_attachedHead rightAttached with
    ⟨foundBlock, foundBlockMember, foundMarker,
      foundSegment, foundSegmentMember, foundNonempty, foundHead⟩
  have foundEq : foundBlock = rightBlock :=
    rightValid.block_eq_of_mem_of_marker_eq
      foundBlockMember rightBlockMember
        (foundMarker.trans sameMarker)
  subst foundBlock
  exact
    ⟨foundSegment, foundSegmentMember, foundNonempty, foundHead⟩

/-! ## Exponent reconstruction once the rigid segments agree -/

/-- Conditions (Ri3)--(Ri5) and the capped-at-three multiplicity invariant
determine `e` once the segment count is fixed. -/
theorem rigid_exponent_eq_of_same_rest_length_and_count_class
    {left right : RigidBlock}
    (leftValid : left.Valid) (rightValid : right.Valid)
    (sameRestLength : left.rest.length = right.rest.length)
    (sameCount :
      SameMultiplicityClass
        (renderRigidBlock left) (renderRigidBlock right) left.marker)
    (sameMarker : left.marker = right.marker) :
    left.exponent = right.exponent := by
  have rightCount :
      (renderRigidBlock right).count left.marker =
        right.rest.length + right.exponent := by
    simpa [sameMarker] using rightValid.count_marker
  have leftCount := leftValid.count_marker
  rcases sameCount with small | large
  · rw [leftCount, rightCount] at small
    omega
  · rw [leftCount] at large
    rw [rightCount] at large
    by_cases noRest : left.rest.length = 0
    · have rightNoRest : right.rest.length = 0 := by omega
      have leftRank : left.rank = 1 := by
        simp [RigidBlock.rank, noRest]
      have rightRank : right.rank = 1 := by
        simp [RigidBlock.rank, rightNoRest]
      rcases leftValid.ri3 leftRank with leftExponent | leftExponent <;>
        rcases rightValid.ri3 rightRank with rightExponent | rightExponent <;>
          omega
    · by_cases oneRest : left.rest.length = 1
      · have rightOneRest : right.rest.length = 1 := by omega
        have leftRank : left.rank = 2 := by
          simp [RigidBlock.rank, oneRest]
        have rightRank : right.rank = 2 := by
          simp [RigidBlock.rank, rightOneRest]
        rcases leftValid.ri4 leftRank with leftExponent | leftExponent <;>
          rcases rightValid.ri4 rightRank with rightExponent | rightExponent <;>
            omega
      · have leftRank : 3 ≤ left.rank := by
          unfold RigidBlock.rank
          omega
        have rightRank : 3 ≤ right.rank := by
          unfold RigidBlock.rank
          omega
        rw [leftValid.ri5 leftRank, rightValid.ri5 rightRank]

/-! ## Reconstruction of the distinguished first block -/

theorem first_rest_head_mem_of_sameInvariant
    {left right : CanonicalForm}
    (leftValid : left.Valid) (rightValid : right.Valid)
    (same : SameInvariant
      (renderCanonical left) (renderCanonical right))
    (sameMarker : left.first.marker = right.first.marker)
    (sameFirst : left.first.first = right.first.first)
    {head : Nat} (headMember : head ∈ left.first.heads) :
    head ∈ right.first.heads := by
  rcases List.mem_map.mp headMember with
    ⟨leftSegment, leftSegmentMember, leftSegmentHead⟩
  have leftNonempty :=
    leftValid.conditionI.positiveSegments
      leftSegment leftSegmentMember
  rcases exists_matching_segment
      leftValid rightValid same
      (leftBlock := left.first) (rightBlock := right.first)
      (by simp [CanonicalForm.blocks])
      (by simp [CanonicalForm.blocks]) sameMarker
      (leftSegment := leftSegment)
      (by simp [RigidBlock.segments, leftSegmentMember])
      leftNonempty with
    ⟨rightSegment, rightSegmentMember, rightNonempty,
      rightSegmentHead⟩
  change rightSegment ∈ right.first.first :: right.first.rest at rightSegmentMember
  rcases List.mem_cons.mp rightSegmentMember with
      isRightFirst | inRightRest
  · subst rightSegment
    have leftFirstNonempty : left.first.first ≠ [] := by
      simpa [sameFirst] using rightNonempty
    have distinct :=
      leftValid.conditionI.first_headD_ne_rest_headD
        leftFirstNonempty leftSegmentMember
    have forbidden :
        left.first.first.headD 0 = leftSegment.headD 0 := by
      rw [sameFirst]
      exact rightSegmentHead
    exact (distinct forbidden).elim
  · apply List.mem_map.mpr
    refine ⟨rightSegment, inRightRest, ?_⟩
    exact rightSegmentHead.trans leftSegmentHead

theorem first_rest_heads_eq_of_sameInvariant
    {left right : CanonicalForm}
    (leftValid : left.Valid) (rightValid : right.Valid)
    (same : SameInvariant
      (renderCanonical left) (renderCanonical right))
    (sameMarker : left.first.marker = right.first.marker)
    (sameFirst : left.first.first = right.first.first) :
    left.first.heads = right.first.heads := by
  apply pairwise_lt_list_eq_of_same_mem
    leftValid.conditionI.ri2 rightValid.conditionI.ri2
  intro head
  constructor
  · exact first_rest_head_mem_of_sameInvariant
      leftValid rightValid same sameMarker sameFirst
  · exact first_rest_head_mem_of_sameInvariant
      rightValid leftValid same.symm sameMarker.symm sameFirst.symm

theorem first_rest_eq_of_sameInvariant
    {left right : CanonicalForm}
    (leftValid : left.Valid) (rightValid : right.Valid)
    (same : SameInvariant
      (renderCanonical left) (renderCanonical right))
    (sameMarker : left.first.marker = right.first.marker)
    (sameFirst : left.first.first = right.first.first) :
    left.first.rest = right.first.rest := by
  apply list_eq_of_map_eq_of_cross_key
    (fun segment : List Nat => segment.headD 0)
      left.first.rest right.first.rest
  · simpa [RigidBlock.heads] using
      first_rest_heads_eq_of_sameInvariant
        leftValid rightValid same sameMarker sameFirst
  · intro leftSegment leftMember rightSegment rightMember sameHead
    have leftNonempty :=
      leftValid.conditionI.positiveSegments leftSegment leftMember
    have rightNonempty :=
      rightValid.conditionI.positiveSegments rightSegment rightMember
    exact
      (segment_eq_and_marker_eq_of_headD_eq
        leftValid rightValid same
        (leftBlock := left.first) (rightBlock := right.first)
        (by simp [CanonicalForm.blocks])
        (by simp [CanonicalForm.blocks])
        (by simp [RigidBlock.segments, leftMember])
        (by simp [RigidBlock.segments, rightMember])
        leftNonempty rightNonempty sameHead).1

private theorem rigidBlock_eq_of_fields_eq
    {left right : RigidBlock}
    (markerEq : left.marker = right.marker)
    (firstEq : left.first = right.first)
    (restEq : left.rest = right.rest)
    (exponentEq : left.exponent = right.exponent) : left = right := by
  cases left
  cases right
  cases markerEq
  cases firstEq
  cases restEq
  cases exponentEq
  rfl

/-- The first block is uniquely reconstructed from the four invariants and
the printed first-block conditions. -/
theorem first_block_eq_of_sameInvariant
    {left right : CanonicalForm}
    (leftValid : left.Valid) (rightValid : right.Valid)
    (same : SameInvariant
      (renderCanonical left) (renderCanonical right)) :
    left.first = right.first := by
  have firstData :=
    first_marker_and_segment_eq_of_sameInvariant
      leftValid rightValid same
  have restEq :=
    first_rest_eq_of_sameInvariant
      leftValid rightValid same firstData.1 firstData.2
  have localMultiplicity :=
    same_block_multiplicityClass leftValid rightValid same
      (leftBlock := left.first) (rightBlock := right.first)
      (by simp [CanonicalForm.blocks])
      (by simp [CanonicalForm.blocks]) firstData.1
  have exponentEq :=
    rigid_exponent_eq_of_same_rest_length_and_count_class
      leftValid.conditionI rightValid.conditionI
      (by simpa [restEq]) localMultiplicity firstData.1
  exact rigidBlock_eq_of_fields_eq firstData.1 firstData.2 restEq exponentEq

/-! ## Reconstruction of the later fully rigid blocks -/

/-- Ordered heads of all nonempty segments in a left-normalized later
block. -/
def RigidBlock.allSegmentHeads (block : RigidBlock) : List Nat :=
  if block.first = [] then []
  else block.first.headD 0 :: block.heads

theorem RigidBlock.FullyRigid.allSegmentHeads_pairwise
    {block : RigidBlock} (fully : block.FullyRigid) :
    block.allSegmentHeads.Pairwise (fun left right => left < right) := by
  by_cases firstEmpty : block.first = []
  · simp [RigidBlock.allSegmentHeads, firstEmpty]
  · simpa [RigidBlock.allSegmentHeads, firstEmpty] using fully.ri6 firstEmpty

theorem RigidBlock.segment_nonempty_of_mem
    {block : RigidBlock} (valid : block.Valid)
    (firstNonempty : block.first ≠ [])
    {segment : List Nat} (segmentMember : segment ∈ block.segments) :
    segment ≠ [] := by
  change segment ∈ block.first :: block.rest at segmentMember
  rcases List.mem_cons.mp segmentMember with isFirst | inRest
  · simpa [isFirst] using firstNonempty
  · exact valid.positiveSegments segment inRest

theorem RigidBlock.mem_allSegmentHeads_iff
    {block : RigidBlock} (fully : block.FullyRigid)
    (normalized : block.LeftNormalized) (head : Nat) :
    head ∈ block.allSegmentHeads ↔
      ∃ segment ∈ block.segments,
        segment ≠ [] ∧ segment.headD 0 = head := by
  by_cases firstEmpty : block.first = []
  · have restEmpty := normalized firstEmpty
    simp [RigidBlock.allSegmentHeads, RigidBlock.segments,
      firstEmpty, restEmpty]
  · constructor
    · intro headMember
      rw [RigidBlock.allSegmentHeads, if_neg firstEmpty] at headMember
      rcases List.mem_cons.mp headMember with isFirst | inHeads
      · refine
          ⟨block.first, by simp [RigidBlock.segments], firstEmpty, ?_⟩
        exact isFirst.symm
      · rcases List.mem_map.mp inHeads with
          ⟨segment, segmentMember, segmentHead⟩
        exact
          ⟨segment, by simp [RigidBlock.segments, segmentMember],
            fully.toValid.positiveSegments segment segmentMember,
            segmentHead⟩
    · rintro ⟨segment, segmentMember, segmentNonempty, segmentHead⟩
      change segment ∈ block.first :: block.rest at segmentMember
      rw [RigidBlock.allSegmentHeads, if_neg firstEmpty]
      rcases List.mem_cons.mp segmentMember with isFirst | inRest
      · subst segment
        rw [← segmentHead]
        exact List.Mem.head _
      · exact List.Mem.tail _
          (List.mem_map.mpr ⟨segment, inRest, segmentHead⟩)

theorem later_allSegmentHead_mem_of_sameInvariant
    {left right : CanonicalForm}
    (leftValid : left.Valid) (rightValid : right.Valid)
    (same : SameInvariant
      (renderCanonical left) (renderCanonical right))
    {leftBlock rightBlock : RigidBlock}
    (leftBlockMember : leftBlock ∈ left.blocks)
    (rightBlockMember : rightBlock ∈ right.blocks)
    (leftFully : leftBlock.FullyRigid)
    (rightFully : rightBlock.FullyRigid)
    (leftNormalized : leftBlock.LeftNormalized)
    (rightNormalized : rightBlock.LeftNormalized)
    (sameMarker : leftBlock.marker = rightBlock.marker)
    {head : Nat} (headMember : head ∈ leftBlock.allSegmentHeads) :
    head ∈ rightBlock.allSegmentHeads := by
  rcases (RigidBlock.mem_allSegmentHeads_iff
      leftFully leftNormalized head).1 headMember with
    ⟨leftSegment, leftSegmentMember, leftNonempty, leftHead⟩
  rcases exists_matching_segment
      leftValid rightValid same leftBlockMember rightBlockMember
      sameMarker leftSegmentMember leftNonempty with
    ⟨rightSegment, rightSegmentMember, rightNonempty, rightHead⟩
  apply (RigidBlock.mem_allSegmentHeads_iff
    rightFully rightNormalized head).2
  exact
    ⟨rightSegment, rightSegmentMember, rightNonempty,
      rightHead.trans leftHead⟩

theorem later_allSegmentHeads_eq_of_sameInvariant
    {left right : CanonicalForm}
    (leftValid : left.Valid) (rightValid : right.Valid)
    (same : SameInvariant
      (renderCanonical left) (renderCanonical right))
    {leftBlock rightBlock : RigidBlock}
    (leftBlockMember : leftBlock ∈ left.blocks)
    (rightBlockMember : rightBlock ∈ right.blocks)
    (leftFully : leftBlock.FullyRigid)
    (rightFully : rightBlock.FullyRigid)
    (leftNormalized : leftBlock.LeftNormalized)
    (rightNormalized : rightBlock.LeftNormalized)
    (sameMarker : leftBlock.marker = rightBlock.marker) :
    leftBlock.allSegmentHeads = rightBlock.allSegmentHeads := by
  apply pairwise_lt_list_eq_of_same_mem
    leftFully.allSegmentHeads_pairwise
    rightFully.allSegmentHeads_pairwise
  intro head
  constructor
  · exact later_allSegmentHead_mem_of_sameInvariant
      leftValid rightValid same leftBlockMember rightBlockMember
      leftFully rightFully leftNormalized rightNormalized sameMarker
  · exact later_allSegmentHead_mem_of_sameInvariant
      rightValid leftValid same.symm rightBlockMember leftBlockMember
      rightFully leftFully rightNormalized leftNormalized sameMarker.symm

theorem later_block_first_rest_eq_of_sameInvariant
    {left right : CanonicalForm}
    (leftValid : left.Valid) (rightValid : right.Valid)
    (same : SameInvariant
      (renderCanonical left) (renderCanonical right))
    {leftBlock rightBlock : RigidBlock}
    (leftBlockMember : leftBlock ∈ left.blocks)
    (rightBlockMember : rightBlock ∈ right.blocks)
    (leftFully : leftBlock.FullyRigid)
    (rightFully : rightBlock.FullyRigid)
    (leftNormalized : leftBlock.LeftNormalized)
    (rightNormalized : rightBlock.LeftNormalized)
    (sameMarker : leftBlock.marker = rightBlock.marker) :
    leftBlock.first = rightBlock.first ∧
      leftBlock.rest = rightBlock.rest := by
  have allHeadsEq :=
    later_allSegmentHeads_eq_of_sameInvariant
      leftValid rightValid same leftBlockMember rightBlockMember
      leftFully rightFully leftNormalized rightNormalized sameMarker
  by_cases leftFirstEmpty : leftBlock.first = []
  · have leftRestEmpty := leftNormalized leftFirstEmpty
    have rightFirstEmpty : rightBlock.first = [] := by
      by_cases rightEmpty : rightBlock.first = []
      · exact rightEmpty
      have rightNonempty : rightBlock.first ≠ [] := rightEmpty
      exfalso
      have rightHeadMember :
          rightBlock.first.headD 0 ∈ rightBlock.allSegmentHeads := by
        simp [RigidBlock.allSegmentHeads, rightNonempty]
      rw [← allHeadsEq, RigidBlock.allSegmentHeads,
        if_pos leftFirstEmpty] at rightHeadMember
      simp at rightHeadMember
    have rightRestEmpty := rightNormalized rightFirstEmpty
    exact
      ⟨leftFirstEmpty.trans rightFirstEmpty.symm,
        leftRestEmpty.trans rightRestEmpty.symm⟩
  · have rightFirstNonempty : rightBlock.first ≠ [] := by
      intro rightFirstEmpty
      have leftHeadMember :
          leftBlock.first.headD 0 ∈ leftBlock.allSegmentHeads := by
        simp [RigidBlock.allSegmentHeads, leftFirstEmpty]
      rw [allHeadsEq, RigidBlock.allSegmentHeads,
        if_pos rightFirstEmpty] at leftHeadMember
      simp at leftHeadMember
    have segmentKeys :
        leftBlock.segments.map (fun segment => segment.headD 0) =
          rightBlock.segments.map (fun segment => segment.headD 0) := by
      simpa [RigidBlock.allSegmentHeads, RigidBlock.segments,
        RigidBlock.heads, leftFirstEmpty, rightFirstNonempty] using
        allHeadsEq
    have segmentsEq : leftBlock.segments = rightBlock.segments := by
      apply list_eq_of_map_eq_of_cross_key
        (fun segment : List Nat => segment.headD 0)
          leftBlock.segments rightBlock.segments segmentKeys
      intro leftSegment leftSegmentMember
        rightSegment rightSegmentMember sameHead
      have leftNonempty :=
        RigidBlock.segment_nonempty_of_mem leftFully.toValid
          leftFirstEmpty leftSegmentMember
      have rightNonempty :=
        RigidBlock.segment_nonempty_of_mem rightFully.toValid
          rightFirstNonempty rightSegmentMember
      exact
        (segment_eq_and_marker_eq_of_headD_eq
          leftValid rightValid same leftBlockMember rightBlockMember
          leftSegmentMember rightSegmentMember
          leftNonempty rightNonempty sameHead).1
    change
      leftBlock.first :: leftBlock.rest =
        rightBlock.first :: rightBlock.rest at segmentsEq
    simpa only [List.cons.injEq] using segmentsEq

/-- A later block is uniquely reconstructed under the deterministic
left-normalization convention. -/
theorem later_block_eq_of_sameInvariant
    {left right : CanonicalForm}
    (leftValid : left.Valid) (rightValid : right.Valid)
    (same : SameInvariant
      (renderCanonical left) (renderCanonical right))
    {leftBlock rightBlock : RigidBlock}
    (leftBlockMember : leftBlock ∈ left.blocks)
    (rightBlockMember : rightBlock ∈ right.blocks)
    (leftFully : leftBlock.FullyRigid)
    (rightFully : rightBlock.FullyRigid)
    (leftNormalized : leftBlock.LeftNormalized)
    (rightNormalized : rightBlock.LeftNormalized)
    (sameMarker : leftBlock.marker = rightBlock.marker) :
    leftBlock = rightBlock := by
  have pieces :=
    later_block_first_rest_eq_of_sameInvariant
      leftValid rightValid same leftBlockMember rightBlockMember
      leftFully rightFully leftNormalized rightNormalized sameMarker
  have localMultiplicity :=
    same_block_multiplicityClass leftValid rightValid same
      leftBlockMember rightBlockMember sameMarker
  have exponentEq :=
    rigid_exponent_eq_of_same_rest_length_and_count_class
      leftFully.toValid rightFully.toValid
      (by simpa [pieces.2]) localMultiplicity sameMarker
  exact rigidBlock_eq_of_fields_eq sameMarker pieces.1 pieces.2 exponentEq

theorem later_blocks_eq_of_sameInvariant
    {left right : CanonicalForm}
    (leftReduced : left.ReducedValid)
    (rightReduced : right.ReducedValid)
    (same : SameInvariant
      (renderCanonical left) (renderCanonical right))
    (firstEq : left.first = right.first) :
    left.rest = right.rest := by
  have markerEq : left.first.marker = right.first.marker := by
    rw [firstEq]
  have tailMarkersEq :=
    tailMarkers_eq_of_sameInvariant
      leftReduced.toValid rightReduced.toValid same markerEq
  apply list_eq_of_map_eq_of_cross_key
    RigidBlock.marker left.rest right.rest
  · simpa [CanonicalForm.tailMarkers] using tailMarkersEq
  · intro leftBlock leftMember rightBlock rightMember sameMarker
    exact later_block_eq_of_sameInvariant
      leftReduced.toValid rightReduced.toValid same
      (leftBlock := leftBlock) (rightBlock := rightBlock)
      (by simp [CanonicalForm.blocks, leftMember])
      (by simp [CanonicalForm.blocks, rightMember])
      (leftReduced.later_fullyRigid leftMember)
      (rightReduced.later_fullyRigid rightMember)
      (leftReduced.laterLeftNormalized leftBlock leftMember)
      (rightReduced.laterLeftNormalized rightBlock rightMember)
      sameMarker

/-! ## Reconstruction of the final simple suffix -/

theorem adjacent_in_suffix_lifts
    {whole prefixPart suffix : List Nat} {source target : Nat}
    (shape : whole = prefixPart ++ suffix)
    (edge : (source, target) ∈ S5_107.listAdjacentPairs suffix) :
    (source, target) ∈ S5_107.listAdjacentPairs whole := by
  rcases
      (S5_107.mem_listAdjacentPairs_iff_exists_split
        source target suffix).1 edge with
    ⟨before, after, suffixShape⟩
  apply
    (S5_107.mem_listAdjacentPairs_iff_exists_split
      source target whole).2
  exact
    ⟨prefixPart ++ before, after,
      by rw [shape, suffixShape]; simp [List.append_assoc]⟩

theorem adjacent_in_suffix_of_simple_source
    {whole prefixPart suffix : List Nat} {source target : Nat}
    (shape : whole = prefixPart ++ suffix)
    (simple : Simple whole source)
    (sourceMember : source ∈ suffix)
    (edge : (source, target) ∈ S5_107.listAdjacentPairs whole) :
    (source, target) ∈ S5_107.listAdjacentPairs suffix := by
  rcases List.mem_iff_append.mp sourceMember with
    ⟨suffixBefore, suffixAfter, suffixShape⟩
  cases suffixAfter with
  | nil =>
      have finalShape :
          whole = (prefixPart ++ suffixBefore) ++ [source] := by
        rw [shape, suffixShape]
        simp [List.append_assoc]
      exact (no_adjacent_from_simple_final finalShape simple target edge).elim
  | cons actualTarget suffixRest =>
      have actualWholeEdge :
          (source, actualTarget) ∈
            S5_107.listAdjacentPairs whole := by
        apply
          (S5_107.mem_listAdjacentPairs_iff_exists_split
            source actualTarget whole).2
        refine ⟨prefixPart ++ suffixBefore, suffixRest, ?_⟩
        rw [shape, suffixShape]
        simp [List.append_assoc]
      have targetEq :=
        adjacent_target_eq_of_simple_source simple edge actualWholeEdge
      subst target
      apply
        (S5_107.mem_listAdjacentPairs_iff_exists_split
          source actualTarget suffix).2
      exact ⟨suffixBefore, suffixRest, suffixShape⟩

theorem suffix_mem_iff_of_blocks_eq
    {left right : CanonicalForm}
    (leftValid : left.Valid) (rightValid : right.Valid)
    (same : SameInvariant
      (renderCanonical left) (renderCanonical right))
    (firstEq : left.first = right.first)
    (restEq : left.rest = right.rest)
    (letter : Nat) :
    letter ∈ left.suffix ↔ letter ∈ right.suffix := by
  have blocksEq : left.blocks = right.blocks := by
    simp [CanonicalForm.blocks, firstEq, restEq]
  constructor
  · intro leftSuffix
    have leftWhole : letter ∈ renderCanonical left :=
      (mem_renderCanonical_iff left letter).2 (Or.inr leftSuffix)
    have rightWhole := (same.support letter).mp leftWhole
    rcases (mem_renderCanonical_iff right letter).1 rightWhole with
        ⟨block, rightBlockMember, inBlock⟩ | rightSuffix
    · have leftBlockMember : block ∈ left.blocks := by
        rw [blocksEq]
        exact rightBlockMember
      exact
        ((leftValid.block_disjoint_suffix leftBlockMember)
          letter inBlock leftSuffix).elim
    · exact rightSuffix
  · intro rightSuffix
    have rightWhole : letter ∈ renderCanonical right :=
      (mem_renderCanonical_iff right letter).2 (Or.inr rightSuffix)
    have leftWhole := (same.support letter).mpr rightWhole
    rcases (mem_renderCanonical_iff left letter).1 leftWhole with
        ⟨block, leftBlockMember, inBlock⟩ | leftSuffix
    · have rightBlockMember : block ∈ right.blocks := by
        rw [← blocksEq]
        exact leftBlockMember
      exact
        ((rightValid.block_disjoint_suffix rightBlockMember)
          letter inBlock rightSuffix).elim
    · exact leftSuffix

theorem suffix_adjacent_iff_of_blocks_eq
    {left right : CanonicalForm}
    (leftValid : left.Valid) (rightValid : right.Valid)
    (same : SameInvariant
      (renderCanonical left) (renderCanonical right))
    (firstEq : left.first = right.first)
    (restEq : left.rest = right.rest)
    (source target : Nat) :
    (source, target) ∈ S5_107.listAdjacentPairs left.suffix ↔
      (source, target) ∈ S5_107.listAdjacentPairs right.suffix := by
  have suffixSupport :=
    suffix_mem_iff_of_blocks_eq
      leftValid rightValid same firstEq restEq
  constructor
  · intro leftEdge
    have sourceMember := adjacent_source_mem leftEdge
    have targetMember := adjacent_target_mem leftEdge
    have sourceSimple := leftValid.conditionIV source sourceMember
    have targetSimple := leftValid.conditionIV target targetMember
    have leftWholeEdge := adjacent_in_suffix_lifts
      (whole := renderCanonical left)
      (prefixPart := left.blockRenders.flatten)
      (suffix := left.suffix) rfl leftEdge
    have rightFactor := (same.fss source target).mp
      ⟨sourceSimple, targetSimple, leftWholeEdge⟩
    have rightSourceMember :=
      (suffixSupport source).mp sourceMember
    exact adjacent_in_suffix_of_simple_source
      (whole := renderCanonical right)
      (prefixPart := right.blockRenders.flatten)
      (suffix := right.suffix) rfl rightFactor.1
      rightSourceMember rightFactor.2.2
  · intro rightEdge
    have sourceMember := adjacent_source_mem rightEdge
    have targetMember := adjacent_target_mem rightEdge
    have sourceSimple := rightValid.conditionIV source sourceMember
    have targetSimple := rightValid.conditionIV target targetMember
    have rightWholeEdge := adjacent_in_suffix_lifts
      (whole := renderCanonical right)
      (prefixPart := right.blockRenders.flatten)
      (suffix := right.suffix) rfl rightEdge
    have leftFactor := (same.fss source target).mpr
      ⟨sourceSimple, targetSimple, rightWholeEdge⟩
    have leftSourceMember :=
      (suffixSupport source).mpr sourceMember
    exact adjacent_in_suffix_of_simple_source
      (whole := renderCanonical left)
      (prefixPart := left.blockRenders.flatten)
      (suffix := left.suffix) rfl leftFactor.1
      leftSourceMember leftFactor.2.2

theorem exists_adjacent_into_of_mem_of_head_ne
    {letters : List Nat} {head : Nat}
    (member : head ∈ letters)
    (notHead : letters.head? ≠ some head) :
    ∃ source,
      (source, head) ∈ S5_107.listAdjacentPairs letters := by
  rcases List.mem_iff_append.mp member with
    ⟨before, after, shape⟩
  have beforeNonempty : before ≠ [] := by
    intro empty
    subst before
    simp [shape] at notHead
  rcases exists_eq_append_singleton_of_ne_nil beforeNonempty with
    ⟨prefixPart, source, beforeShape⟩
  refine ⟨source, ?_⟩
  apply
    (S5_107.mem_listAdjacentPairs_iff_exists_split
      source head letters).2
  exact
    ⟨prefixPart, after,
      by rw [shape, beforeShape]; simp [List.append_assoc]⟩

/-- A duplicate-free list is reconstructed by support and adjacency alone;
the head is the unique supported letter with no incoming edge. -/
theorem nodup_list_eq_of_same_support_adjacent
    {left right : List Nat}
    (leftNodup : left.Nodup) (rightNodup : right.Nodup)
    (sameSupport : ∀ letter, letter ∈ left ↔ letter ∈ right)
    (sameAdjacent : ∀ source target,
      (source, target) ∈ S5_107.listAdjacentPairs left ↔
        (source, target) ∈ S5_107.listAdjacentPairs right) :
    left = right := by
  have sameHead : left.head? = right.head? := by
    cases left with
    | nil =>
        have rightEmpty : right = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro letter member
          exact List.not_mem_nil ((sameSupport letter).mpr member)
        simp [rightEmpty]
    | cons leftHead leftTail =>
        cases right with
        | nil =>
            have impossible : leftHead ∈ ([] : List Nat) :=
              (sameSupport leftHead).mp (by simp)
            simp at impossible
        | cons rightHead rightTail =>
            by_cases headsEq : leftHead = rightHead
            · simp only [List.head?_cons, headsEq]
            exfalso
            have leftHeadInRight :
                leftHead ∈ rightHead :: rightTail :=
              (sameSupport leftHead).mp (by simp)
            have rightHeadNotLeft :
                (rightHead :: rightTail).head? ≠ some leftHead := by
              intro equal
              have sameSome : some rightHead = some leftHead := equal
              exact headsEq (Option.some.inj sameSome).symm
            rcases exists_adjacent_into_of_mem_of_head_ne
                leftHeadInRight rightHeadNotLeft with
              ⟨source, rightEdge⟩
            have leftEdge :=
              (sameAdjacent source leftHead).mpr rightEdge
            have leftSimple : Simple (leftHead :: leftTail) leftHead := by
              have absent := (List.nodup_cons.mp leftNodup).1
              unfold Simple
              simp [List.count_eq_zero.mpr absent]
            exact
              no_adjacent_into_simple_initial
                leftSimple source leftEdge
  exact nodup_list_eq_of_same_head_support_adjacent
    left right leftNodup rightNodup sameHead
      sameSupport sameAdjacent

theorem suffix_eq_of_sameInvariant
    {left right : CanonicalForm}
    (leftValid : left.Valid) (rightValid : right.Valid)
    (same : SameInvariant
      (renderCanonical left) (renderCanonical right))
    (firstEq : left.first = right.first)
    (restEq : left.rest = right.rest) :
    left.suffix = right.suffix := by
  apply nodup_list_eq_of_same_support_adjacent
    leftValid.suffix_nodup rightValid.suffix_nodup
  · exact suffix_mem_iff_of_blocks_eq
      leftValid rightValid same firstEq restEq
  · exact suffix_adjacent_iff_of_blocks_eq
      leftValid rightValid same firstEq restEq

/-! ## Final reduced-valid uniqueness interface -/

theorem canonicalComponents_eq_of_sameInvariant
    {left right : CanonicalForm}
    (leftValid : left.ReducedValid)
    (rightValid : right.ReducedValid)
    (same : SameInvariant
      (renderCanonical left) (renderCanonical right)) :
    SameCanonicalComponents left right := by
  have firstEq :=
    first_block_eq_of_sameInvariant
      leftValid.toValid rightValid.toValid same
  have restEq :=
    later_blocks_eq_of_sameInvariant
      leftValid rightValid same firstEq
  have suffixEq :=
    suffix_eq_of_sameInvariant
      leftValid.toValid rightValid.toValid same firstEq restEq
  exact ⟨firstEq, restEq, suffixEq⟩

theorem canonicalForm_eq_of_sameInvariant
    {left right : CanonicalForm}
    (leftValid : left.ReducedValid)
    (rightValid : right.ReducedValid)
    (same : SameInvariant
      (renderCanonical left) (renderCanonical right)) :
    left = right :=
  (canonicalComponents_eq_of_sameInvariant
    leftValid rightValid same).form_eq

/-- Clean equality endpoint for completeness: two reduced canonical
renderers with the same Lemma-20.8 data are literally equal. -/
theorem renderCanonical_eq_of_sameInvariant
    {left right : CanonicalForm}
    (leftValid : left.ReducedValid)
    (rightValid : right.ReducedValid)
    (same : SameInvariant
      (renderCanonical left) (renderCanonical right)) :
    renderCanonical left = renderCanonical right :=
  (canonicalComponents_eq_of_sameInvariant
    leftValid rightValid same).render_eq

/-! ## Literal-valid ambiguity -/

def ambiguityFirstBlock : RigidBlock where
  marker := 0
  first := []
  rest := []
  exponent := 2

def ambiguityLeftLaterBlock : RigidBlock where
  marker := 1
  first := []
  rest := [[2]]
  exponent := 1

def ambiguityRightLaterBlock : RigidBlock where
  marker := 1
  first := [2]
  rest := []
  exponent := 2

def ambiguityLeftForm : CanonicalForm where
  first := ambiguityFirstBlock
  rest := [ambiguityLeftLaterBlock]
  suffix := []

def ambiguityRightForm : CanonicalForm where
  first := ambiguityFirstBlock
  rest := [ambiguityRightLaterBlock]
  suffix := []

@[simp]
theorem render_ambiguityFirstBlock :
    renderRigidBlock ambiguityFirstBlock = [0, 0] :=
  rfl

@[simp]
theorem render_ambiguityLeftLaterBlock :
    renderRigidBlock ambiguityLeftLaterBlock = [1, 2, 1] :=
  rfl

@[simp]
theorem render_ambiguityRightLaterBlock :
    renderRigidBlock ambiguityRightLaterBlock = [2, 1, 1] :=
  rfl

@[simp]
theorem render_ambiguityLeftForm :
    renderCanonical ambiguityLeftForm = [0, 0, 1, 2, 1] :=
  rfl

@[simp]
theorem render_ambiguityRightForm :
    renderCanonical ambiguityRightForm = [0, 0, 2, 1, 1] :=
  rfl

theorem ambiguityFirstBlock_valid :
    ambiguityFirstBlock.Valid := by
  constructor
  · change 2 ≤ ([0, 0] : List Nat).count 0
    decide
  · intro segment member
    exact (List.not_mem_nil member).elim
  · decide
  · intro segment member letter letterMember
    have empty : segment = [] := by
      simpa only [RigidBlock.segments, ambiguityFirstBlock,
        List.mem_singleton] using member
    subst segment
    exact (List.not_mem_nil letterMember).elim
  · decide
  · decide
  · decide
  · decide

theorem ambiguityLeftLaterBlock_fullyRigid :
    ambiguityLeftLaterBlock.FullyRigid := by
  constructor
  · constructor
    · change 2 ≤ ([1, 2, 1] : List Nat).count 1
      decide
    · intro segment member
      have selected : segment = [2] := by
        simpa only [ambiguityLeftLaterBlock, List.mem_singleton] using member
      rw [selected]
      decide
    · decide
    · intro segment member letter letterMember
      have selected : segment = [] ∨ segment = [2] := by
        simpa only [RigidBlock.segments, ambiguityLeftLaterBlock,
          List.mem_cons, List.not_mem_nil, or_false] using member
      rcases selected with rfl | rfl
      · exact (List.not_mem_nil letterMember).elim
      · have equal : letter = 2 := List.mem_singleton.mp letterMember
        subst letter
        change ([1, 2, 1] : List Nat).count 2 = 1
        decide
    · decide
    · decide
    · decide
    · decide
  · decide

theorem ambiguityRightLaterBlock_fullyRigid :
    ambiguityRightLaterBlock.FullyRigid := by
  constructor
  · constructor
    · change 2 ≤ ([2, 1, 1] : List Nat).count 1
      decide
    · intro segment member
      exact (List.not_mem_nil member).elim
    · decide
    · intro segment member letter letterMember
      have selected : segment = [2] := by
        simpa only [RigidBlock.segments, ambiguityRightLaterBlock,
          List.mem_singleton] using member
      subst segment
      have equal : letter = 2 := List.mem_singleton.mp letterMember
      subst letter
      change ([2, 1, 1] : List Nat).count 2 = 1
      decide
    · decide
    · decide
    · decide
    · decide
  · decide

theorem ambiguityLeftForm_valid :
    ambiguityLeftForm.Valid := by
  constructor
  · exact ambiguityFirstBlock_valid
  · intro block member
    simp only [ambiguityLeftForm, List.mem_singleton] at member
    subst block
    exact ambiguityLeftLaterBlock_fullyRigid
  · simp [ambiguityLeftForm, CanonicalForm.tailMarkers]
  · simp [ambiguityLeftForm]
  · constructor
    · simp [ambiguityLeftForm, CanonicalForm.blockRenders,
        CanonicalForm.blocks, ListsDisjoint]
    · intro block member
      simp [ambiguityLeftForm, CanonicalForm.blocks,
        ListsDisjoint]

theorem ambiguityRightForm_valid :
    ambiguityRightForm.Valid := by
  constructor
  · exact ambiguityFirstBlock_valid
  · intro block member
    simp only [ambiguityRightForm, List.mem_singleton] at member
    subst block
    exact ambiguityRightLaterBlock_fullyRigid
  · simp [ambiguityRightForm, CanonicalForm.tailMarkers]
  · simp [ambiguityRightForm]
  · constructor
    · simp [ambiguityRightForm, CanonicalForm.blockRenders,
        CanonicalForm.blocks, ListsDisjoint]
    · intro block member
      simp [ambiguityRightForm, CanonicalForm.blocks,
        ListsDisjoint]

private theorem ambiguity_count_eq (letter : Nat) :
    [0, 0, 1, 2, 1].count letter =
      [0, 0, 2, 1, 1].count letter := by
  by_cases zero : letter = 0
  · subst letter
    decide
  by_cases one : letter = 1
  · subst letter
    decide
  by_cases two : letter = 2
  · subst letter
    decide
  have leftAbsent : letter ∉ [0, 0, 1, 2, 1] := by
    simp only [List.mem_cons, List.not_mem_nil, zero, one, two,
      false_or, not_false_eq_true]
  have rightAbsent : letter ∉ [0, 0, 2, 1, 1] := by
    simp only [List.mem_cons, List.not_mem_nil, zero, one, two,
      false_or, not_false_eq_true]
  rw [List.count_eq_zero.mpr leftAbsent, List.count_eq_zero.mpr rightAbsent]

private theorem ambiguity_count_le_two (letter : Nat) :
    [0, 0, 1, 2, 1].count letter ≤ 2 := by
  by_cases zero : letter = 0
  · subst letter
    decide
  by_cases one : letter = 1
  · subst letter
    decide
  by_cases two : letter = 2
  · subst letter
    decide
  have absent : letter ∉ [0, 0, 1, 2, 1] := by
    simp only [List.mem_cons, List.not_mem_nil, zero, one, two,
      false_or, not_false_eq_true]
  rw [List.count_eq_zero.mpr absent]
  decide

/-- The two distinct printed canonical forms have exactly the same four
Lemma-20.8 invariants. -/
theorem ambiguity_sameInvariant :
    SameInvariant
      (renderCanonical ambiguityLeftForm)
      (renderCanonical ambiguityRightForm) := by
  rw [render_ambiguityLeftForm, render_ambiguityRightForm]
  constructor
  · intro letter
    exact Or.inl
      ⟨ambiguity_count_eq letter, ambiguity_count_le_two letter⟩
  · rfl
  · intro x y
    by_cases xZero : x = 0
    · subst x
      simp [FSN, Simple, NonSimple]
    by_cases xOne : x = 1
    · subst x
      simp [FSN, Simple, NonSimple]
    by_cases xTwo : x = 2
    · subst x
      by_cases yZero : y = 0
      · subst y
        unfold FSN Simple NonSimple
        decide
      by_cases yOne : y = 1
      · subst y
        unfold FSN Simple NonSimple
        decide
      by_cases yTwo : y = 2
      · subst y
        unfold FSN Simple NonSimple
        decide
      simp [FSN, Simple, NonSimple, yZero, yOne, yTwo]
    simp [FSN, Simple, NonSimple, xZero, xOne, xTwo]
  · intro x y
    by_cases xZero : x = 0
    · subst x
      simp [FSS, Simple]
    by_cases xOne : x = 1
    · subst x
      simp [FSS, Simple]
    by_cases xTwo : x = 2
    · subst x
      by_cases yZero : y = 0
      · subst y
        unfold FSS Simple
        decide
      by_cases yOne : y = 1
      · subst y
        unfold FSS Simple
        decide
      by_cases yTwo : y = 2
      · subst y
        unfold FSS Simple
        decide
      simp [FSS, Simple, yZero, yOne, yTwo]
    simp [FSS, Simple, xZero, xOne, xTwo]

theorem ambiguity_render_ne :
    renderCanonical ambiguityLeftForm ≠
      renderCanonical ambiguityRightForm := by
  decide

theorem ambiguityLeft_not_reduced :
    ¬ ambiguityLeftForm.ReducedValid := by
  intro reduced
  have normalized :=
    reduced.laterLeftNormalized ambiguityLeftLaterBlock
      (List.mem_singleton_self ambiguityLeftLaterBlock)
  have firstEmpty : ambiguityLeftLaterBlock.first = [] := rfl
  have restEmpty := normalized firstEmpty
  simp [ambiguityLeftLaterBlock] at restEmpty

theorem ambiguityRightForm_reducedValid :
    ambiguityRightForm.ReducedValid := by
  constructor
  · exact ambiguityRightForm_valid
  · intro block member
    simp only [ambiguityRightForm, List.mem_singleton] at member
    subst block
    intro firstEmpty
    simp [ambiguityRightLaterBlock] at firstEmpty

end SemigroupBasis.CoRoots.Order6LeeZhangProposition20_7E4
