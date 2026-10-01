import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395SectorCut

/-! Executable selection of an earlier NONFIRST occurrence in the same
simple-marker sector. Soundness and completeness refer to actual positions. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395Absorber

open SemigroupBasis
open Msg0457S11395SectorPairs

def clear (whole block : List Nat) : Bool :=
  block.all (fun tested => decide (whole.count tested ≠ 1))

theorem clear_spec (whole block : List Nat) : clear whole block = true ↔ SimpleFree whole block := by
  simp [clear, List.all_eq_true, SimpleFree]

def scan (whole : List Nat) (letter : Nat) : Bool → List Nat → Option (List Nat × List Nat)
  | _, [] => none
  | seen, head :: rest =>
      if head = letter ∧ seen = true ∧ clear whole rest = true then some ([],rest)
      else (scan whole letter (seen || head == letter) rest).map
        (fun parts => (head :: parts.1, parts.2))

theorem scan_sound (whole prefixWords : List Nat) (letter : Nat) (seen : Bool)
    (before after : List Nat) (found : scan whole letter seen prefixWords = some (before,after)) :
    prefixWords = before ++ letter :: after ∧
    (seen = true ∨ letter ∈ before) ∧ SimpleFree whole after := by
  induction prefixWords generalizing seen before after with
  | nil => simp [scan] at found
  | cons head rest ih =>
      by_cases eligible : head = letter ∧ seen = true ∧ clear whole rest = true
      · have matched : ([],rest) = (before,after) :=
          Option.some.inj (by simpa only [scan, if_pos eligible] using found)
        have left : before = [] := (congrArg Prod.fst matched).symm
        have right : after = rest := (congrArg Prod.snd matched).symm
        subst before
        subst after
        exact ⟨by simp [eligible.1], Or.inl eligible.2.1, (clear_spec whole rest).1 eligible.2.2⟩
      · cases tailShape : scan whole letter (seen || head == letter) rest with
        | none => simp [scan, eligible, tailShape] at found
        | some parts =>
            rcases parts with ⟨small, remaining⟩
            have matched : (head :: small,remaining) = (before,after) :=
              Option.some.inj (by simpa only [scan, if_neg eligible, tailShape, Option.map_some] using found)
            have left : before = head :: small := (congrArg Prod.fst matched).symm
            have right : after = remaining := (congrArg Prod.snd matched).symm
            subst before
            subst after
            have parts := ih (seen || head == letter) small remaining tailShape
            refine ⟨by simp [parts.1], ?_, parts.2.2⟩
            rcases parts.2.1 with past | inSmall
            · have alternatives : seen = true ∨ head = letter := by simpa using past
              rcases alternatives with old | equal
              · exact Or.inl old
              · exact Or.inr (by simp [equal])
            · exact Or.inr (List.mem_cons_of_mem _ inSmall)

theorem scan_complete (whole : List Nat) (letter : Nat) (seen : Bool) (before after : List Nat)
    (earlier : seen = true ∨ letter ∈ before) (free : SimpleFree whole after) :
    ∃ parts, scan whole letter seen (before ++ letter :: after) = some parts := by
  induction before generalizing seen with
  | nil =>
      have past : seen = true := by simpa using earlier
      exact ⟨([],after), by simp [scan, past, (clear_spec whole after).2 free]⟩
  | cons head before ih =>
      have nextEarlier : (seen || head == letter) = true ∨ letter ∈ before := by
        rcases earlier with old | member
        · exact Or.inl (by simp [old])
        · rcases List.mem_cons.mp member with equal | member
          · exact Or.inl (by simp [equal])
          · exact Or.inr member
      obtain ⟨parts, tailShape⟩ := ih (seen || head == letter) nextEarlier
      by_cases eligible : head = letter ∧ seen = true ∧ clear whole (before ++ letter :: after) = true
      · exact ⟨([],before ++ letter :: after), by simp only [List.cons_append, scan, if_pos eligible]⟩
      · refine ⟨(head :: parts.1,parts.2), ?_⟩
        simp only [List.cons_append, scan, if_neg eligible, tailShape, Option.map_some]

def find (whole prefixWords : List Nat) (letter : Nat) : Option (List Nat × List Nat) :=
  scan whole letter false prefixWords

theorem find_sound (whole prefixWords : List Nat) (letter : Nat) (before after : List Nat)
    (found : find whole prefixWords letter = some (before,after)) :
    prefixWords = before ++ letter :: after ∧ letter ∈ before ∧ SimpleFree whole after := by
  simpa only [Bool.false_eq_true, false_or] using scan_sound whole prefixWords letter false before after found

theorem find_exists_iff (whole prefixWords : List Nat) (letter : Nat) :
    (∃ parts, find whole prefixWords letter = some parts) ↔
    ∃ before after, prefixWords = before ++ letter :: after ∧ letter ∈ before ∧ SimpleFree whole after := by
  constructor
  · rintro ⟨⟨before,after⟩,found⟩
    exact ⟨before,after,find_sound whole prefixWords letter before after found⟩
  · rintro ⟨before,after,shape,earlier,free⟩
    rw [shape]
    exact scan_complete whole letter false before after (Or.inr earlier) free

theorem find_none_iff (whole prefixWords : List Nat) (letter : Nat) :
    find whole prefixWords letter = none ↔
    ¬ ∃ before after, prefixWords = before ++ letter :: after ∧ letter ∈ before ∧ SimpleFree whole after := by
  constructor
  · intro absent witness
    obtain ⟨parts,found⟩ := (find_exists_iff whole prefixWords letter).2 witness
    rw [absent] at found
    contradiction
  · intro absent
    cases found : find whole prefixWords letter with
    | none => rfl
    | some parts =>
        exact False.elim (absent ((find_exists_iff whole prefixWords letter).1 ⟨parts,found⟩))

theorem found_prefix_two (whole prefixWords : List Nat) (letter : Nat) (parts : List Nat × List Nat)
    (found : find whole prefixWords letter = some parts) : 2 ≤ prefixWords.count letter := by
  have witness := find_sound whole prefixWords letter parts.1 parts.2 found
  have past := member_count_positive parts.1 letter witness.2.1
  rw [witness.1, List.count_append, List.count_cons_self]
  omega

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395Absorber
