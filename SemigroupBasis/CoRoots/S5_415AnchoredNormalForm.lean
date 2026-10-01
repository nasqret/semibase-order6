import SemigroupBasis.CoRoots.S5_415Semantics

namespace SemigroupBasis.CoRoots.S5_415

open SemigroupBasis

/-- A walk assembled from excursions that all start and end at the same
nonempty anchor block. -/
def anchoredWalk (anchor : Word Nat) : List (Word Nat) → Word Nat
  | [] => anchor
  | excursion :: rest =>
      (anchor ++ excursion) ++ anchoredWalk anchor rest

/-- Two adjacent excursions may be exchanged. This is the list-level form of
the derived Brandt graph-switch identity. -/
theorem derivesAnchoredWalkAdjacentSwap
    (anchor first second : Word Nat)
    (suffix : List (Word Nat)) :
    Derives basis
      (anchoredWalk anchor (first :: second :: suffix))
      (anchoredWalk anchor (second :: first :: suffix)) := by
  cases suffix with
  | nil =>
      simpa [anchoredWalk, Word.append_assoc] using
        derivesGraphSwitch anchor first second
  | cons next rest =>
      have swapped :=
        Derives.appendRight
          (derivesGraphSwitch anchor first second)
          (next ++ anchoredWalk anchor rest)
      simpa [anchoredWalk, Word.append_assoc] using swapped

/-- An excursion may be repeated next to itself. -/
theorem derivesAnchoredWalkDuplicateHead
    (anchor excursion : Word Nat) (rest : List (Word Nat)) :
    Derives basis
      (anchoredWalk anchor (excursion :: rest))
      (anchoredWalk anchor (excursion :: excursion :: rest)) := by
  cases rest with
  | nil =>
      simpa [anchoredWalk, Word.append_assoc] using
        derivesSandwichExpansion anchor excursion
  | cons next suffix =>
      have expanded :=
        Derives.appendRight
          (derivesSandwichExpansion anchor excursion)
          (next ++ anchoredWalk anchor suffix)
      simpa [anchoredWalk, Word.append_assoc] using expanded

/-- Every permutation of a finite family of anchored excursions is
derivable. -/
theorem derivesAnchoredWalkPermutation
    {source target : List (Word Nat)}
    (permutation : source.Perm target) (anchor : Word Nat) :
    Derives basis
      (anchoredWalk anchor source)
      (anchoredWalk anchor target) := by
  induction permutation with
  | nil =>
      exact Derives.refl _
  | cons excursion _ ih =>
      simpa [anchoredWalk, Word.append_assoc] using
        Derives.prepend (anchor ++ excursion) ih
  | swap first second rest =>
      exact derivesAnchoredWalkAdjacentSwap
        anchor second first rest
  | trans _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂

private theorem anchoredPermConsToEnd
    (excursion : Word Nat) :
    ∀ excursions : List (Word Nat),
      (excursion :: excursions).Perm
        (excursions ++ [excursion])
  | [] => List.Perm.refl _
  | next :: rest =>
      (List.Perm.swap next excursion rest).trans <|
        List.Perm.cons next
          (anchoredPermConsToEnd excursion rest)

private theorem anchoredPermAppendComm :
    ∀ source target : List (Word Nat),
      (source ++ target).Perm (target ++ source)
  | [], target => by simp
  | excursion :: rest, target => by
      have reordered :=
        List.Perm.cons excursion
          (anchoredPermAppendComm rest target)
      have moved :=
        (anchoredPermConsToEnd excursion target).append_right rest
      exact reordered.trans <| by
        simpa [List.append_assoc] using moved

/-- Any excursion already represented by an anchored walk may be appended
once more. -/
theorem derivesAnchoredWalkAppendMember
    (anchor : Word Nat) (excursions : List (Word Nat))
    (excursion : Word Nat) (member : excursion ∈ excursions) :
    Derives basis
      (anchoredWalk anchor excursions)
      (anchoredWalk anchor (excursions ++ [excursion])) := by
  have expose :
      excursions.Perm
        (excursion :: excursions.erase excursion) :=
    List.perm_cons_erase member
  have restore :
      (excursion :: excursion :: excursions.erase excursion).Perm
        (excursions ++ [excursion]) :=
    (List.Perm.cons excursion expose.symm).trans
      (anchoredPermConsToEnd excursion excursions)
  exact
    (derivesAnchoredWalkPermutation expose anchor).trans <|
      (derivesAnchoredWalkDuplicateHead anchor excursion
        (excursions.erase excursion)).trans <|
          derivesAnchoredWalkPermutation restore anchor

/-- An anchored walk may be expanded by a finite list of excursions already
present in its excursion support. -/
theorem derivesAnchoredWalkAppendList
    (anchor : Word Nat) (excursions extra : List (Word Nat))
    (available :
      ∀ excursion, excursion ∈ extra → excursion ∈ excursions) :
    Derives basis
      (anchoredWalk anchor excursions)
      (anchoredWalk anchor (excursions ++ extra)) := by
  induction extra generalizing excursions with
  | nil =>
      simpa using Derives.refl (anchoredWalk anchor excursions)
  | cons excursion rest ih =>
      have present : excursion ∈ excursions :=
        available excursion (List.Mem.head rest)
      have firstStep :=
        derivesAnchoredWalkAppendMember
          anchor excursions excursion present
      have remaining :
          ∀ candidate, candidate ∈ rest →
            candidate ∈ excursions ++ [excursion] := by
        intro candidate member
        exact List.mem_append_left [excursion] <|
          available candidate (List.Mem.tail excursion member)
      have restStep := ih (excursions ++ [excursion]) remaining
      exact firstStep.trans <| by
        simpa [List.append_assoc] using restStep

/-- For a fixed anchor, the generated congruence depends only on which
excursion blocks occur, not on their order or positive multiplicity. -/
theorem derivesAnchoredWalkOfSameSupport
    (anchor : Word Nat) {left right : List (Word Nat)}
    (sameSupport :
      ∀ excursion, excursion ∈ left ↔ excursion ∈ right) :
    Derives basis
      (anchoredWalk anchor left)
      (anchoredWalk anchor right) := by
  have leftExpanded :=
    derivesAnchoredWalkAppendList anchor left right
      (fun excursion member => (sameSupport excursion).mpr member)
  have reordered :=
    derivesAnchoredWalkPermutation
      (anchoredPermAppendComm left right) anchor
  have rightExpanded :=
    derivesAnchoredWalkAppendList anchor right left
      (fun excursion member => (sameSupport excursion).mp member)
  exact leftExpanded.trans <|
    reordered.trans rightExpanded.symm

/-! ## Empty excursions and a total anchored normalizer -/

/-- Move an empty excursion past a nonempty excursion. The proof first
creates a third anchor block, applies graph switch, then contracts the final
anchor power. -/
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
  exact expandAligned.trans (switch.trans contractAligned)

/-- `none` represents an empty excursion between two copies of the anchor;
`some excursion` represents a nonempty excursion block. -/
def anchoredGapWalk
    (anchor : Word Nat) : List (Option (Word Nat)) → Word Nat
  | [] => anchor
  | none :: rest => anchor ++ anchoredGapWalk anchor rest
  | some excursion :: rest =>
      (anchor ++ excursion) ++ anchoredGapWalk anchor rest

@[simp]
theorem anchoredGapWalk_head
    (anchor : Word Nat) :
    ∀ gaps : List (Option (Word Nat)),
      (anchoredGapWalk anchor gaps).head = anchor.head
  | [] => rfl
  | none :: rest => rfl
  | some excursion :: rest => rfl

private def anchoredGapSuffix
    (anchor : Word Nat) : Option (Word Nat) →
      List (Option (Word Nat)) → Word Nat
  | none, rest => anchoredGapWalk anchor rest
  | some excursion, rest =>
      excursion ++ anchoredGapWalk anchor rest

private theorem derivesAnchoredGapWalkBaseSwap
    (anchor : Word Nat) (first second : Option (Word Nat)) :
    Derives basis
      (anchoredGapWalk anchor [first, second])
      (anchoredGapWalk anchor [second, first]) := by
  cases first with
  | none =>
      cases second with
      | none => exact Derives.refl _
      | some excursion =>
          simpa [anchoredGapWalk, Word.append_assoc] using
            derivesEmptyExcursionSwap anchor excursion
  | some excursion =>
      cases second with
      | none =>
          simpa [anchoredGapWalk, Word.append_assoc] using
            (derivesEmptyExcursionSwap anchor excursion).symm
      | some other =>
          simpa [anchoredGapWalk, Word.append_assoc] using
            derivesGraphSwitch anchor excursion other

/-- Adjacent optional excursions may be exchanged, including the cases in
which either excursion is empty. -/
theorem derivesAnchoredGapWalkAdjacentSwap
    (anchor : Word Nat) (first second : Option (Word Nat))
    (suffix : List (Option (Word Nat))) :
    Derives basis
      (anchoredGapWalk anchor (first :: second :: suffix))
      (anchoredGapWalk anchor (second :: first :: suffix)) := by
  cases suffix with
  | nil =>
      exact derivesAnchoredGapWalkBaseSwap anchor first second
  | cons next rest =>
      have swapped :=
        Derives.appendRight
          (derivesAnchoredGapWalkBaseSwap anchor first second)
          (anchoredGapSuffix anchor next rest)
      cases first <;>
        cases second <;>
          cases next <;>
            simpa [anchoredGapWalk, anchoredGapSuffix,
              Word.append_assoc] using swapped

private theorem derivesAnchoredGapWalkDuplicateBase
    (anchor : Word Nat) (gap : Option (Word Nat)) :
    Derives basis
      (anchoredGapWalk anchor [gap])
      (anchoredGapWalk anchor [gap, gap]) := by
  cases gap with
  | none =>
      simpa [anchoredGapWalk, Word.append_assoc] using
        derivesPowerExpansion anchor
  | some excursion =>
      simpa [anchoredGapWalk, Word.append_assoc] using
        derivesSandwichExpansion anchor excursion

/-- The first optional excursion may be duplicated. -/
theorem derivesAnchoredGapWalkDuplicateHead
    (anchor : Word Nat) (gap : Option (Word Nat))
    (rest : List (Option (Word Nat))) :
    Derives basis
      (anchoredGapWalk anchor (gap :: rest))
      (anchoredGapWalk anchor (gap :: gap :: rest)) := by
  cases rest with
  | nil =>
      exact derivesAnchoredGapWalkDuplicateBase anchor gap
  | cons next suffix =>
      have expanded :=
        Derives.appendRight
          (derivesAnchoredGapWalkDuplicateBase anchor gap)
          (anchoredGapSuffix anchor next suffix)
      cases gap <;>
        cases next <;>
          simpa [anchoredGapWalk, anchoredGapSuffix,
            Word.append_assoc] using expanded

/-- Every permutation of optional anchored excursions is derivable. -/
theorem derivesAnchoredGapWalkPermutation
    {source target : List (Option (Word Nat))}
    (permutation : source.Perm target) (anchor : Word Nat) :
    Derives basis
      (anchoredGapWalk anchor source)
      (anchoredGapWalk anchor target) := by
  induction permutation with
  | nil =>
      exact Derives.refl _
  | cons gap _ ih =>
      cases gap with
      | none =>
          simpa [anchoredGapWalk, Word.append_assoc] using
            Derives.prepend anchor ih
      | some excursion =>
          simpa [anchoredGapWalk, Word.append_assoc] using
            Derives.prepend (anchor ++ excursion) ih
  | swap first second rest =>
      exact derivesAnchoredGapWalkAdjacentSwap
        anchor second first rest
  | trans _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂

private theorem anchoredGapPermConsToEnd
    (gap : Option (Word Nat)) :
    ∀ gaps : List (Option (Word Nat)),
      (gap :: gaps).Perm (gaps ++ [gap])
  | [] => List.Perm.refl _
  | next :: rest =>
      (List.Perm.swap next gap rest).trans <|
        List.Perm.cons next
          (anchoredGapPermConsToEnd gap rest)

private theorem anchoredGapPermAppendComm :
    ∀ source target : List (Option (Word Nat)),
      (source ++ target).Perm (target ++ source)
  | [], target => by simp
  | gap :: rest, target => by
      have reordered :=
        List.Perm.cons gap
          (anchoredGapPermAppendComm rest target)
      have moved :=
        (anchoredGapPermConsToEnd gap target).append_right rest
      exact reordered.trans <| by
        simpa [List.append_assoc] using moved

theorem derivesAnchoredGapWalkAppendMember
    (anchor : Word Nat) (gaps : List (Option (Word Nat)))
    (gap : Option (Word Nat)) (member : gap ∈ gaps) :
    Derives basis
      (anchoredGapWalk anchor gaps)
      (anchoredGapWalk anchor (gaps ++ [gap])) := by
  have expose : gaps.Perm (gap :: gaps.erase gap) :=
    List.perm_cons_erase member
  have restore :
      (gap :: gap :: gaps.erase gap).Perm (gaps ++ [gap]) :=
    (List.Perm.cons gap expose.symm).trans
      (anchoredGapPermConsToEnd gap gaps)
  exact
    (derivesAnchoredGapWalkPermutation expose anchor).trans <|
      (derivesAnchoredGapWalkDuplicateHead
        anchor gap (gaps.erase gap)).trans <|
          derivesAnchoredGapWalkPermutation restore anchor

theorem derivesAnchoredGapWalkAppendList
    (anchor : Word Nat) (gaps extra : List (Option (Word Nat)))
    (available : ∀ gap, gap ∈ extra → gap ∈ gaps) :
    Derives basis
      (anchoredGapWalk anchor gaps)
      (anchoredGapWalk anchor (gaps ++ extra)) := by
  induction extra generalizing gaps with
  | nil =>
      simpa using Derives.refl (anchoredGapWalk anchor gaps)
  | cons gap rest ih =>
      have present : gap ∈ gaps :=
        available gap (List.Mem.head rest)
      have firstStep :=
        derivesAnchoredGapWalkAppendMember
          anchor gaps gap present
      have remaining :
          ∀ candidate, candidate ∈ rest →
            candidate ∈ gaps ++ [gap] := by
        intro candidate member
        exact List.mem_append_left [gap] <|
          available candidate (List.Mem.tail gap member)
      have restStep := ih (gaps ++ [gap]) remaining
      exact firstStep.trans <| by
        simpa [List.append_assoc] using restStep

/-- Optional anchored walks with the same excursion support are derivably
equal. -/
theorem derivesAnchoredGapWalkOfSameSupport
    (anchor : Word Nat)
    {left right : List (Option (Word Nat))}
    (sameSupport : ∀ gap, gap ∈ left ↔ gap ∈ right) :
    Derives basis
      (anchoredGapWalk anchor left)
      (anchoredGapWalk anchor right) := by
  have leftExpanded :=
    derivesAnchoredGapWalkAppendList anchor left right
      (fun gap member => (sameSupport gap).mpr member)
  have reordered :=
    derivesAnchoredGapWalkPermutation
      (anchoredGapPermAppendComm left right) anchor
  have rightExpanded :=
    derivesAnchoredGapWalkAppendList anchor right left
      (fun gap member => (sameSupport gap).mp member)
  exact leftExpanded.trans <|
    reordered.trans rightExpanded.symm

/-- Pointwise derivations of nonempty excursions lift through a fixed
optional anchored-walk skeleton. -/
theorem derivesAnchoredGapWalkMap
    (anchor : Word Nat) (transform : Word Nat → Word Nat)
    (sound : ∀ word, Derives basis word (transform word)) :
    ∀ gaps : List (Option (Word Nat)),
      Derives basis
        (anchoredGapWalk anchor gaps)
        (anchoredGapWalk anchor (gaps.map (Option.map transform)))
  | [] => Derives.refl _
  | none :: rest => by
      simpa [anchoredGapWalk] using
        Derives.prepend anchor
          (derivesAnchoredGapWalkMap anchor transform sound rest)
  | some excursion :: rest => by
      have normalizeHead :=
        Derives.appendRight
          (Derives.prepend anchor (sound excursion))
          (anchoredGapWalk anchor rest)
      have normalizeRest :=
        Derives.prepend (anchor ++ transform excursion)
          (derivesAnchoredGapWalkMap anchor transform sound rest)
      have normalized := normalizeHead.trans normalizeRest
      simpa [anchoredGapWalk, Word.append_assoc] using normalized

/-- Keep the final occurrence of every optional excursion. This structural
recursion is the duplicate-elimination phase of the anchored normalizer. -/
def deduplicateAnchoredGaps :
    List (Option (Word Nat)) → List (Option (Word Nat))
  | [] => []
  | gap :: gaps =>
      if gap ∈ gaps then
        deduplicateAnchoredGaps gaps
      else
        gap :: deduplicateAnchoredGaps gaps

theorem mem_deduplicateAnchoredGaps
    (tested : Option (Word Nat)) :
    ∀ gaps : List (Option (Word Nat)),
      tested ∈ deduplicateAnchoredGaps gaps ↔ tested ∈ gaps
  | [] => by simp [deduplicateAnchoredGaps]
  | gap :: gaps => by
      by_cases present : gap ∈ gaps
      · rw [deduplicateAnchoredGaps, if_pos present,
          mem_deduplicateAnchoredGaps tested gaps]
        constructor
        · exact List.Mem.tail gap
        · intro member
          rcases List.mem_cons.mp member with equal | inGaps
          · subst tested
            exact present
          · exact inGaps
      · simpa [deduplicateAnchoredGaps, present,
          mem_deduplicateAnchoredGaps tested gaps]

theorem deduplicateAnchoredGaps_nodup :
    ∀ gaps : List (Option (Word Nat)),
      (deduplicateAnchoredGaps gaps).Nodup
  | [] => by simp [deduplicateAnchoredGaps]
  | gap :: gaps => by
      by_cases present : gap ∈ gaps
      · simpa [deduplicateAnchoredGaps, present] using
          deduplicateAnchoredGaps_nodup gaps
      · simp [deduplicateAnchoredGaps, present,
          mem_deduplicateAnchoredGaps,
          deduplicateAnchoredGaps_nodup gaps]

theorem deduplicateAnchoredGaps_eq_self_of_nodup :
    ∀ gaps : List (Option (Word Nat)),
      gaps.Nodup → deduplicateAnchoredGaps gaps = gaps
  | [], _ => rfl
  | gap :: gaps, nodup => by
      have parts := List.nodup_cons.mp nodup
      have absent : gap ∉ gaps := parts.1
      have tailNodup : gaps.Nodup := parts.2
      simp [deduplicateAnchoredGaps, absent,
        deduplicateAnchoredGaps_eq_self_of_nodup gaps tailNodup]

/-- A natural-valued progress measure for duplicate elimination. -/
def anchoredGapDuplicateMeasure
    (gaps : List (Option (Word Nat))) : Nat :=
  gaps.length - (deduplicateAnchoredGaps gaps).length

/-- The total anchored normalizer. At this stage its canonical operation is
duplicate elimination; arbitrary reordering is already derivable above. -/
def normalizeAnchoredGaps
    (gaps : List (Option (Word Nat))) : List (Option (Word Nat)) :=
  deduplicateAnchoredGaps gaps

theorem normalizeAnchoredGaps_nodup
    (gaps : List (Option (Word Nat))) :
    (normalizeAnchoredGaps gaps).Nodup :=
  deduplicateAnchoredGaps_nodup gaps

theorem anchoredGapDuplicateMeasure_normalized
    (gaps : List (Option (Word Nat))) :
    anchoredGapDuplicateMeasure (normalizeAnchoredGaps gaps) = 0 := by
  simp [anchoredGapDuplicateMeasure, normalizeAnchoredGaps,
    deduplicateAnchoredGaps_eq_self_of_nodup,
    deduplicateAnchoredGaps_nodup]

/-- Soundness of the total duplicate-eliminating anchored normalizer. -/
theorem derivesNormalizeAnchoredGaps
    (anchor : Word Nat) (gaps : List (Option (Word Nat))) :
    Derives basis
      (anchoredGapWalk anchor gaps)
      (anchoredGapWalk anchor (normalizeAnchoredGaps gaps)) :=
  derivesAnchoredGapWalkOfSameSupport anchor <| by
    intro gap
    exact (mem_deduplicateAnchoredGaps gap gaps).symm

end SemigroupBasis.CoRoots.S5_415
