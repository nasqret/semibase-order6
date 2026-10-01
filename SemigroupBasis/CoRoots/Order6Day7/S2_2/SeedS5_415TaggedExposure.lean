import SemigroupBasis.CoRoots.Order6Day7.S2_2.SeedS5_415CutConnectivity

/-!
# Rank040: square insertion across arbitrary derivational representatives

Tag every occurrence of one letter by the same square, on a specified
incoming or outgoing side. The frozen slides move two tags together and
law00 coalesces them. A structural induction proves that the simultaneous
substitution is derivably equal to one insertion at ANY actual occurrence.

Substitution of an already-proved Derives equality then transports square
insertion across its two representatives. This is not factor completeness,
not arbitrary closed-walk absorption, and not a proof that graph paths have
literal exposures. No restriction is imposed on letters inside the tag:
the substitution is simultaneous, not recursively applied to its images.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.TaggedExposure

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_415
open ClosedReturnReplay ExposureReplay CutConnectivity

def tagSubstitution (side : BrandtEndpointSide) (letter : Nat) (loop : Word Nat)
    (candidate : Nat) : Word Nat :=
  if candidate = letter then
    match side with
    | .incoming => (loop ++ loop) ++ Word.singleton candidate
    | .outgoing => Word.singleton candidate ++ (loop ++ loop)
  else Word.singleton candidate

private theorem tagSelf (side : BrandtEndpointSide) (letter : Nat) (loop : Word Nat) :
    tagSubstitution side letter loop letter =
      match side with
      | .incoming => (loop ++ loop) ++ Word.singleton letter
      | .outgoing => Word.singleton letter ++ (loop ++ loop) := by
  unfold tagSubstitution
  rw [if_pos rfl]

private theorem tagOther (side : BrandtEndpointSide) (letter candidate : Nat) (loop : Word Nat)
    (different : candidate ≠ letter) :
    tagSubstitution side letter loop candidate = Word.singleton candidate := by
  unfold tagSubstitution
  rw [if_neg different]

private theorem derives_of_toList_eq {source target source' target' : Word Nat}
    (derivation : Derives Rank040.basis source target)
    (sourceEq : source.toList = source'.toList)
    (targetEq : target.toList = target'.toList) :
    Derives Rank040.basis source' target' := by
  have sourceWordEq := Word.toList_injective sourceEq
  have targetWordEq := Word.toList_injective targetEq
  simpa only [sourceWordEq, targetWordEq] using derivation

private theorem derives_of_equal_lists {source target : Word Nat}
    (same : source.toList = target.toList) : Derives Rank040.basis source target := by
  rw [Word.toList_injective same]
  exact Derives.refl _

private theorem bind_cons (head next : Nat) (rest : List Nat) (sigma : Nat → Word Nat) :
    (Word.mk head (next :: rest)).bind sigma =
      sigma head ++ (Word.mk next rest).bind sigma := by
  apply Word.toList_injective
  rw [Word.toList_bind, Word.toList_append, Word.toList_bind]
  simp only [Word.toList, List.flatMap_cons]

private theorem bind_single (letter : Nat) (sigma : Nat → Word Nat) :
    (Word.singleton letter).bind sigma = sigma letter := rfl

private theorem tagListAbsent (side : BrandtEndpointSide) (letter : Nat) (loop : Word Nat) :
    ∀ letters : List Nat, letter ∉ letters →
      letters.flatMap (fun candidate => (tagSubstitution side letter loop candidate).toList) = letters
  | [], _ => rfl
  | head :: tail, absent => by
      have different : head ≠ letter := fun same => absent (by simp only [same, List.mem_cons_self])
      have later : letter ∉ tail := fun member => absent (List.mem_cons_of_mem _ member)
      rw [List.flatMap_cons, tagOther side letter head loop different,
        Word.toList_singleton, List.singleton_append, tagListAbsent side letter loop tail later]

theorem tagAbsent (side : BrandtEndpointSide) (letter : Nat) (loop word : Word Nat)
    (absent : letter ∉ word.toList) : word.bind (tagSubstitution side letter loop) = word := by
  apply Word.toList_injective
  rw [Word.toList_bind, tagListAbsent side letter loop word.toList absent]

theorem squareCoalescence (loop : Word Nat) :
    Derives Rank040.basis ((loop ++ loop) ++ (loop ++ loop)) (loop ++ loop) := by
  simpa only [Word.append_assoc] using (BrandtParityBridge.derivesPairExpansion loop).symm

/-- Merge two incoming copies without changing the intervening letters. -/
theorem incomingTagsCoalesce (letter : Nat) (gap after : List Nat) (loop : Word Nat) :
    Derives Rank040.basis
      (ChainReplay.Context.wrap ((loop ++ loop).toList ++ letter :: gap)
        (loop ++ loop) (letter :: after))
      (ChainReplay.Context.wrap [] (loop ++ loop) (letter :: (gap ++ letter :: after))) := by
  have slide := (derivesIncomingSlide letter gap (loop ++ loop).toList after loop).symm
  have moved : Derives Rank040.basis
      (ChainReplay.Context.wrap ((loop ++ loop).toList ++ letter :: gap)
        (loop ++ loop) (letter :: after))
      (ChainReplay.Context.wrap [] ((loop ++ loop) ++ (loop ++ loop))
        (letter :: (gap ++ letter :: after))) := by
    apply derives_of_toList_eq slide
    · rfl
    · simp only [ChainReplay.Context.wrap_toList, Word.toList_append,
        List.nil_append, List.append_assoc]
  exact moved.trans (ChainReplay.Context.derives_wrap (squareCoalescence loop)
    [] (letter :: (gap ++ letter :: after)))

/-- The outgoing version retains a square after the first anchor. -/
theorem outgoingTagsCoalesce (letter : Nat) (gap after : List Nat) (loop : Word Nat) :
    Derives Rank040.basis
      (ChainReplay.Context.wrap (((letter :: (loop ++ loop).toList) ++ gap) ++ [letter])
        (loop ++ loop) after)
      (ChainReplay.Context.wrap [letter] (loop ++ loop) (gap ++ letter :: after)) := by
  have slide := (derivesOutgoingSlide letter ((loop ++ loop).toList ++ gap) [] after loop).symm
  have moved : Derives Rank040.basis
      (ChainReplay.Context.wrap (((letter :: (loop ++ loop).toList) ++ gap) ++ [letter])
        (loop ++ loop) after)
      (ChainReplay.Context.wrap [letter] ((loop ++ loop) ++ (loop ++ loop))
        (gap ++ letter :: after)) := by
    apply derives_of_toList_eq slide
    all_goals simp only [ChainReplay.Context.wrap_toList, Word.toList_append,
      List.nil_append, List.append_assoc, List.cons_append]
  exact moved.trans (ChainReplay.Context.derives_wrap (squareCoalescence loop)
    [letter] (gap ++ letter :: after))

private theorem coalesceHeadAndLater
    (side : BrandtEndpointSide) (letter : Nat) (loop tailWord : Word Nat)
    (later : Occurrence tailWord letter) :
    Derives Rank040.basis
      (tagSubstitution side letter loop letter ++ (later.cut side).insert loop)
      ((show Occurrence (Word.singleton letter ++ tailWord) letter from
        ⟨[], tailWord.toList, rfl⟩).cut side |>.insert loop) := by
  cases side with
  | incoming =>
      apply derives_of_toList_eq (incomingTagsCoalesce letter later.before later.after loop)
      all_goals simp only [tagSelf, Occurrence.cut, Exposure.insert,
        ChainReplay.Context.wrap_toList, Word.toList_append, Word.toList_singleton]
      all_goals simp only [later.partition, List.append_assoc, List.cons_append, List.nil_append]
  | outgoing =>
      apply derives_of_toList_eq (outgoingTagsCoalesce letter later.before later.after loop)
      all_goals simp only [tagSelf, Occurrence.cut, Exposure.insert,
        ChainReplay.Context.wrap_toList, Word.toList_append, Word.toList_singleton]
      all_goals simp only [later.partition, List.append_assoc, List.cons_append, List.nil_append]

/-- The tag at EVERY occurrence coalesces to ONE tag at ANY chosen occurrence.
Both endpoint sides, all word lengths and arbitrary tag alphabets are covered. -/
theorem tagNormalizesAtOccurrence
    (word : Word Nat) (letter : Nat) (side : BrandtEndpointSide) (loop : Word Nat)
    (occurrence : Occurrence word letter) :
    Derives Rank040.basis (word.bind (tagSubstitution side letter loop))
      ((occurrence.cut side).insert loop) := by
  cases word with
  | mk head tail =>
      induction tail generalizing head with
      | nil =>
          have same : letter = head := by simpa only [Word.toList, List.mem_singleton] using occurrence.member
          subst head
          let one : Occurrence (Word.singleton letter) letter := ⟨[], [], rfl⟩
          have normalized : Derives Rank040.basis
              ((Word.singleton letter).bind (tagSubstitution side letter loop))
              ((one.cut side).insert loop) := by
            cases side <;> apply derives_of_equal_lists
            all_goals rw [bind_single]
            all_goals simp only [one, tagSelf, Occurrence.cut, Exposure.insert,
              ChainReplay.Context.wrap_toList, Word.toList_append, Word.toList_singleton,
              List.append_nil, List.nil_append]
          exact normalized.trans (sameEndpointInsertions one occurrence side loop)
      | cons next rest ih =>
          by_cases same : head = letter
          · subst head
            let one : Occurrence (Word.mk letter (next :: rest)) letter := ⟨[], next :: rest, rfl⟩
            have normalized : Derives Rank040.basis
                ((Word.mk letter (next :: rest)).bind (tagSubstitution side letter loop))
                ((one.cut side).insert loop) := by
              by_cases remains : letter ∈ (Word.mk next rest).toList
              · obtain ⟨later⟩ := occurrence_exists remains
                have tailNormalized := ih next later
                have first := Derives.prepend (tagSubstitution side letter loop letter) tailNormalized
                rw [← bind_cons] at first
                exact first.trans (coalesceHeadAndLater side letter loop (Word.mk next rest) later)
              · rw [bind_cons, tagAbsent side letter loop (Word.mk next rest) remains]
                cases side <;> apply derives_of_equal_lists
                all_goals simp only [one, tagSelf, Occurrence.cut, Exposure.insert,
                  ChainReplay.Context.wrap_toList, Word.toList_append, Word.toList_singleton]
                all_goals simp only [Word.toList, List.append_assoc, List.cons_append, List.nil_append]
            exact normalized.trans (sameEndpointInsertions one occurrence side loop)
          · have remains : letter ∈ (Word.mk next rest).toList := by
              have member := occurrence.member
              change letter ∈ head :: next :: rest at member
              rcases List.mem_cons.mp member with first | later
              · exact False.elim (same first.symm)
              · exact later
            obtain ⟨later⟩ := occurrence_exists remains
            let one : Occurrence (Word.mk head (next :: rest)) letter :=
              ⟨head :: later.before, later.after, by
                change head :: (Word.mk next rest).toList = _
                rw [later.partition]
                rfl⟩
            have lifted := Derives.prepend (Word.singleton head) (ih next later)
            have normalized : Derives Rank040.basis
                ((Word.mk head (next :: rest)).bind (tagSubstitution side letter loop))
                ((one.cut side).insert loop) := by
              apply derives_of_toList_eq lifted
              · rw [bind_cons]
                simp only [tagSubstitution, if_neg same]
              · cases side <;>
                  simp only [one, Occurrence.cut, Exposure.insert, ChainReplay.Context.wrap_toList,
                    Word.toList_append, Word.toList_singleton,
                    List.append_assoc, List.cons_append, List.nil_append]
            exact normalized.trans (sameEndpointInsertions one occurrence side loop)

/-- Lift a genuine existing derivation with a square inserted at any chosen
occurrence of the same endpoint on each side. -/
theorem insertionDerivesAcrossRepresentatives
    {source target : Word Nat} (equivalent : Derives Rank040.basis source target)
    (letter : Nat) (side : BrandtEndpointSide) (loop : Word Nat)
    (first : Occurrence source letter) (second : Occurrence target letter) :
    Derives Rank040.basis ((first.cut side).insert loop) ((second.cut side).insert loop) :=
  (tagNormalizesAtOccurrence source letter side loop first).symm.trans
    ((Derives.subst equivalent (tagSubstitution side letter loop)).trans
      (tagNormalizesAtOccurrence target letter side loop second))

/-- The quantified insertion invariant is exactly the fixed-point equation
for the explicit nonempty substitution. Absent endpoints cause no exception:
both sides are trivially true, without inventing an occurrence. -/
theorem endpointAbsorbs_iff_tagFixed (word : Word Nat) (endpoint : BrandtEndpoint) (loop : Word Nat) :
    EndpointAbsorbs word endpoint loop ↔
      Derives Rank040.basis word
        (word.bind (tagSubstitution endpoint.side endpoint.letter loop)) := by
  constructor
  · intro absorbs
    by_cases member : endpoint.letter ∈ word.toList
    · obtain ⟨one⟩ := occurrence_exists member
      exact (absorbs one).trans
        (tagNormalizesAtOccurrence word endpoint.letter endpoint.side loop one).symm
    · rw [tagAbsent endpoint.side endpoint.letter loop word member]
      exact Derives.refl _
  · intro fixed one
    exact fixed.trans (tagNormalizesAtOccurrence word endpoint.letter endpoint.side loop one)

/-- No regularity or semantic-completeness premise: arbitrary actual Derives
equivalence transports absorption, on either directed endpoint side. -/
theorem endpointAbsorbs_of_derives
    {source target : Word Nat} {endpoint : BrandtEndpoint} {loop : Word Nat}
    (equivalent : Derives Rank040.basis source target)
    (absorbs : EndpointAbsorbs source endpoint loop) : EndpointAbsorbs target endpoint loop := by
  apply (endpointAbsorbs_iff_tagFixed target endpoint loop).mpr
  exact equivalent.symm.trans
    (((endpointAbsorbs_iff_tagFixed source endpoint loop).mp absorbs).trans
      (Derives.subst equivalent (tagSubstitution endpoint.side endpoint.letter loop)))

theorem endpointAbsorbs_derives_iff
    {source target : Word Nat} (equivalent : Derives Rank040.basis source target)
    (endpoint : BrandtEndpoint) (loop : Word Nat) :
    EndpointAbsorbs source endpoint loop ↔ EndpointAbsorbs target endpoint loop :=
  ⟨endpointAbsorbs_of_derives equivalent, endpointAbsorbs_of_derives equivalent.symm⟩

theorem endpointAbsorbs_derives_transport
    {source target : Word Nat} {first second : BrandtEndpoint} {loop : Word Nat}
    (equivalent : Derives Rank040.basis source target)
    (connected : BrandtEndpointConnected target first second)
    (absorbs : EndpointAbsorbs source first loop) : EndpointAbsorbs target second loop :=
  endpointAbsorbs_transport connected (endpointAbsorbs_of_derives equivalent absorbs)

/-- All literal exposures of ALL representatives linked by a real derivation. -/
def DerivationalExposureAbsorbs (word : Word Nat) (endpoint : BrandtEndpoint) (loop : Word Nat) : Prop :=
  ∀ target : Word Nat, Derives Rank040.basis word target → EndpointAbsorbs target endpoint loop

theorem derivationalExposureAbsorbs_iff (word : Word Nat) (endpoint : BrandtEndpoint) (loop : Word Nat) :
    DerivationalExposureAbsorbs word endpoint loop ↔ EndpointAbsorbs word endpoint loop :=
  ⟨fun absorbs => absorbs word (Derives.refl _),
    fun absorbs _ equivalent => endpointAbsorbs_of_derives equivalent absorbs⟩

theorem derivationalExposureAbsorbs_head_iff (word loop : Word Nat) :
    DerivationalExposureAbsorbs word (BrandtEndpoint.incoming word.head) loop ↔ SquareAbsorbs word loop :=
  (derivationalExposureAbsorbs_iff word _ loop).trans (endpointAbsorbs_head_iff word loop)

end SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.TaggedExposure
