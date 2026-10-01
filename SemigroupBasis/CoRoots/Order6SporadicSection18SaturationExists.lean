import SemigroupBasis.CoRoots.Order6SporadicSection18SaturationSteps

/-! An unrestricted existence proof for canonical C7 block chains.
The actual derivation moves preserve gaps and terminate by a proved finite
support bound; no externally supplied normalizer or tested word bound occurs. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
open SemigroupBasis

inductive Reach (alphabet : List Nat) (initial : List Slot) : List Slot → Prop where
  | refl : Reach alphabet initial initial
  | tail {middle final : List Slot} : Reach alphabet initial middle →
      Step alphabet middle final → Reach alphabet initial final

theorem Reach.valid {alphabet : List Nat} {input output : List Slot}
    (reached : Reach alphabet input output) (valid : Valid alphabet input) : Valid alphabet output := by
  induction reached with
  | refl => exact valid
  | tail previous move ih => exact move.valid ih

theorem Reach.sound {alphabet : List Nat} {input output : List Slot}
    (reached : Reach alphabet input output) (valid : Valid alphabet input) :
    ListDerives (render input) (render output) := by
  induction reached with
  | refl => exact S5_107.ListDerives.refl _
  | tail previous move ih => exact ih.trans (move.sound (previous.valid valid))

theorem Reach.gaps {alphabet : List Nat} {input output : List Slot}
    (reached : Reach alphabet input output) : input.map Slot.gap = output.map Slot.gap := by
  induction reached with
  | refl => rfl
  | tail previous move ih => exact ih.trans move.gaps

theorem Reach.length {alphabet : List Nat} {input output : List Slot}
    (reached : Reach alphabet input output) : input.length = output.length := by
  have equal := congrArg List.length reached.gaps
  simpa only [List.length_map] using equal

theorem Reach.score_bound {alphabet : List Nat} {input output : List Slot}
    (reached : Reach alphabet input output) (valid : Valid alphabet input) :
    score output ≤ input.length * alphabet.length := by
  calc
    score output ≤ output.length * alphabet.length :=
      SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.score_bound alphabet output (reached.valid valid)
    _ = input.length * alphabet.length := congrArg (fun n => n * alphabet.length) reached.length.symm

def Terminal (alphabet : List Nat) (chain : List Slot) : Prop :=
  ∀ next, ¬ Step alphabet chain next

theorem exists_terminal (alphabet : List Nat) (input : List Slot) (valid : Valid alphabet input) :
    ∃ output, Reach alphabet input output ∧ Valid alphabet output ∧
      ListDerives (render input) (render output) ∧ input.map Slot.gap = output.map Slot.gap ∧
      Terminal alphabet output := by
  let property : Nat → Prop := fun n => ∃ chain, Reach alphabet input chain ∧ score chain = n
  have inhabited : ∃ n, property n := ⟨score input, input, Reach.refl, rfl⟩
  have bounded : ∀ n, property n → n ≤ input.length * alphabet.length := by
    rintro n ⟨chain, reached, equal⟩
    calc
      n = score chain := equal.symm
      _ ≤ input.length * alphabet.length := reached.score_bound valid
  obtain ⟨top, reachedTop, maximal⟩ := bounded_maximum property inhabited (input.length * alphabet.length) bounded
  obtain ⟨output, reached, level⟩ := reachedTop
  refine ⟨output, reached, reached.valid valid, reached.sound valid, reached.gaps, ?_⟩
  intro next move
  have reachedNext : Reach alphabet input next := Reach.tail reached move
  have upper := maximal (score next) ⟨next, reachedNext, rfl⟩
  have lower := move.growth (reached.valid valid)
  omega

def OverlapClosed (chain : List Slot) : Prop :=
  ∀ (before middle after : List Slot) (g1 g2 left right : List Nat) (x : Nat),
    chain = before ++ (⟨g1, left⟩ :: (middle ++ (⟨g2, right⟩ :: after))) →
    x ∈ left → x ∈ right → left = right

def CrossingClosed (chain : List Slot) : Prop :=
  ∀ (before middle1 middle2 middle3 after : List Slot) (g1 g2 g3 g4 left right : List Nat),
    chain = before ++ (⟨g1, left⟩ :: (middle1 ++ (⟨g2, right⟩ ::
      (middle2 ++ (⟨g3, left⟩ :: (middle3 ++ (⟨g4, right⟩ :: after))))))) →
    left = right

theorem Terminal.overlapClosed {alphabet : List Nat} {chain : List Slot}
    (terminal : Terminal alphabet chain) : OverlapClosed chain := by
  intro before middle after g1 g2 left right x shape inLeft inRight
  by_cases equal : left = right
  · exact equal
  · have move : Step alphabet chain
        (before ++ (⟨g1, joinBlock alphabet left right⟩ ::
          (middle ++ (⟨g2, joinBlock alphabet left right⟩ :: after)))) := by
      rw [shape]
      exact Step.overlap before middle after g1 g2 left right x inLeft inRight equal
    exact False.elim (terminal _ move)

theorem Terminal.crossingClosed {alphabet : List Nat} {chain : List Slot}
    (terminal : Terminal alphabet chain) : CrossingClosed chain := by
  intro before middle1 middle2 middle3 after g1 g2 g3 g4 left right shape
  by_cases equal : left = right
  · exact equal
  · have move : Step alphabet chain
        (before ++ (⟨g1, joinBlock alphabet left right⟩ ::
          (middle1 ++ (⟨g2, joinBlock alphabet left right⟩ ::
          (middle2 ++ (⟨g3, joinBlock alphabet left right⟩ ::
          (middle3 ++ (⟨g4, joinBlock alphabet left right⟩ :: after)))))))) := by
      rw [shape]
      exact Step.crossing before middle1 middle2 middle3 after g1 g2 g3 g4 left right equal
    exact False.elim (terminal _ move)

theorem terminal_of_closed {alphabet : List Nat} {chain : List Slot}
    (overlap : OverlapClosed chain) (crossing : CrossingClosed chain) : Terminal alphabet chain := by
  intro next move
  cases move with
  | overlap before middle after g1 g2 left right x inLeft inRight different =>
      exact different (overlap before middle after g1 g2 left right x rfl inLeft inRight)
  | crossing before middle1 middle2 middle3 after g1 g2 g3 g4 left right different =>
      exact different (crossing before middle1 middle2 middle3 after g1 g2 g3 g4 left right rfl)

def CanonicalChain (alphabet : List Nat) (chain : List Slot) : Prop :=
  Valid alphabet chain ∧ OverlapClosed chain ∧ CrossingClosed chain

theorem exists_canonicalChain (alphabet : List Nat) (input : List Slot) (valid : Valid alphabet input) :
    ∃ output, CanonicalChain alphabet output ∧ ListDerives (render input) (render output) ∧
      input.map Slot.gap = output.map Slot.gap ∧ Reach alphabet input output := by
  obtain ⟨output, reached, outputValid, derivation, gaps, terminal⟩ := exists_terminal alphabet input valid
  exact ⟨output, ⟨outputValid, terminal.overlapClosed, terminal.crossingClosed⟩, derivation, gaps, reached⟩

def BoundedNonempty (alphabet : List Nat) (chain : List Slot) : Prop :=
  ∀ slot ∈ chain, slot.block ≠ [] ∧ ∀ x ∈ slot.block, x ∈ alphabet

def normalizeChain (alphabet : List Nat) (chain : List Slot) : List Slot :=
  chain.map (fun slot => ⟨slot.gap, normalizeBlock alphabet slot.block⟩)

theorem normalizeBlock_content (alphabet block : List Nat) (bounded : ∀ x ∈ block, x ∈ alphabet) (x : Nat) :
    x ∈ block ↔ x ∈ normalizeBlock alphabet block := by
  rw [normalizeBlock_mem]
  exact ⟨fun member => ⟨bounded x member, member⟩, And.right⟩

theorem normalizeBlock_good (alphabet block : List Nat) (nonempty : block ≠ [])
    (bounded : ∀ x ∈ block, x ∈ alphabet) : GoodBlock alphabet (normalizeBlock alphabet block) := by
  have witness : ∃ x, x ∈ block := by
    cases block with
    | nil => exact False.elim (nonempty rfl)
    | cons x xs => exact ⟨x, by simp⟩
  obtain ⟨x, member⟩ := witness
  have normalizedMember := (normalizeBlock_content alphabet block bounded x).mp member
  refine ⟨?_, normalize_filter alphabet _⟩
  intro empty
  rw [empty] at normalizedMember
  exact List.not_mem_nil normalizedMember

theorem normalizeChain_valid (alphabet : List Nat) (input : List Slot) (bounded : BoundedNonempty alphabet input) :
    Valid alphabet (normalizeChain alphabet input) := by
  intro slot member
  obtain ⟨original, originalMember, equal⟩ := List.mem_map.mp member
  subst slot
  have good := bounded original originalMember
  exact normalizeBlock_good alphabet original.block good.1 good.2

theorem normalizeChain_gaps (alphabet : List Nat) (input : List Slot) :
    input.map Slot.gap = (normalizeChain alphabet input).map Slot.gap := by
  simp only [normalizeChain, List.map_map, Function.comp_def]

theorem normalizeChain_sound (alphabet : List Nat) (input : List Slot) :
    BoundedNonempty alphabet input → ListDerives (render input) (render (normalizeChain alphabet input)) := by
  induction input with
  | nil => intro _; exact S5_107.ListDerives.refl []
  | cons slot rest ih =>
      intro bounded
      have headBound := bounded slot (by simp)
      have tailBound : BoundedNonempty alphabet rest := fun s member => bounded s (List.mem_cons_of_mem slot member)
      have blockDerivation := squareBlocks_same_content slot.block (normalizeBlock alphabet slot.block)
        (normalizeBlock_content alphabet slot.block headBound.2)
      have tailDerivation := ih tailBound
      simpa only [render, normalizeChain, List.map_cons, List.append_assoc] using
        append_derivations (blockDerivation.prepend slot.gap) tailDerivation

/-- The overlap/crossing core of Lemma18.5, starting with arbitrary nonempty
square blocks over any finite alphabet and preserving every gap verbatim. -/
theorem exists_saturated_squareChain (alphabet : List Nat) (input : List Slot)
    (bounded : BoundedNonempty alphabet input) :
    ∃ output, CanonicalChain alphabet output ∧ ListDerives (render input) (render output) ∧
      input.map Slot.gap = output.map Slot.gap := by
  obtain ⟨output, canonical, derivation, gaps, _⟩ :=
    exists_canonicalChain alphabet (normalizeChain alphabet input) (normalizeChain_valid alphabet input bounded)
  exact ⟨output, canonical, (normalizeChain_sound alphabet input bounded).trans derivation,
    (normalizeChain_gaps alphabet input).trans gaps⟩

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.Reach.sound
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.exists_terminal
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.Terminal.overlapClosed
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.Terminal.crossingClosed
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.exists_canonicalChain
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.normalizeChain_sound
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.exists_saturated_squareChain

end SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
