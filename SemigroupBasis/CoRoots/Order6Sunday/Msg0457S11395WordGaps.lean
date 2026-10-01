import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395FutureGap

/-! Actual first-introduction gap decomposition of arbitrary lists.
Recursion decreases the input length; there is no caller-supplied window. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395WordGaps

open SemigroupBasis
open Msg0457S11395SeenSwaps

def splitSeen (prefixWords : List Nat) : List Nat → List Nat × List Nat
  | [] => ([], [])
  | letter :: rest =>
      if letter ∈ prefixWords then
        let parts := splitSeen prefixWords rest
        (letter :: parts.1, parts.2)
      else ([], letter :: rest)

theorem splitSeen_join (prefixWords word : List Nat) :
    (splitSeen prefixWords word).1 ++ (splitSeen prefixWords word).2 = word := by
  induction word with
  | nil => rfl
  | cons letter rest ih =>
      by_cases seen : letter ∈ prefixWords
      · simpa [splitSeen, seen] using congrArg (List.cons letter) ih
      · simp [splitSeen, seen]

theorem splitSeen_seen (prefixWords word : List Nat) : AllSeen prefixWords (splitSeen prefixWords word).1 := by
  induction word with
  | nil => simp [splitSeen, AllSeen]
  | cons letter rest ih =>
      by_cases seen : letter ∈ prefixWords
      · intro tested member
        simp only [splitSeen, if_pos seen] at member
        rcases List.mem_cons.mp member with equal | later
        · simpa [equal] using seen
        · exact ih tested later
      · simp [splitSeen, seen, AllSeen]

theorem splitSeen_fresh (prefixWords word : List Nat) (fresh : Nat) (rest : List Nat)
    (shape : (splitSeen prefixWords word).2 = fresh :: rest) : fresh ∉ prefixWords := by
  induction word with
  | nil => simp [splitSeen] at shape
  | cons letter tail ih =>
      by_cases seen : letter ∈ prefixWords
      · exact ih (by simpa [splitSeen, seen] using shape)
      · have equal : letter = fresh := (List.cons.inj (by simpa [splitSeen, seen] using shape)).1
        simpa [← equal] using seen

theorem splitSeen_tail_length (prefixWords word : List Nat) (fresh : Nat) (rest : List Nat)
    (shape : (splitSeen prefixWords word).2 = fresh :: rest) : rest.length < word.length := by
  have joined := splitSeen_join prefixWords word
  rw [shape] at joined
  have lengths := congrArg List.length joined
  simp only [List.length_append, List.length_cons] at lengths
  omega

inductive Chain where
  | stop (gap : List Nat)
  | step (gap : List Nat) (fresh : Nat) (tail : Chain)
  deriving DecidableEq

def flatten : Chain → List Nat
  | .stop gap => gap
  | .step gap fresh tail => gap ++ fresh :: flatten tail

def introductions : Chain → List Nat
  | .stop _ => []
  | .step _ fresh tail => fresh :: introductions tail

def WellFormed (prefixWords : List Nat) : Chain → Prop
  | .stop gap => AllSeen prefixWords gap
  | .step gap fresh tail => AllSeen prefixWords gap ∧ fresh ∉ prefixWords ∧
      WellFormed (prefixWords ++ gap ++ [fresh]) tail

def factor (prefixWords word : List Nat) : Chain :=
  match _restShape : (splitSeen prefixWords word).2 with
  | [] => .stop (splitSeen prefixWords word).1
  | fresh :: rest => .step (splitSeen prefixWords word).1 fresh
      (factor (prefixWords ++ (splitSeen prefixWords word).1 ++ [fresh]) rest)
termination_by word.length
decreasing_by exact splitSeen_tail_length prefixWords word fresh rest _restShape

theorem factor_flatten (prefixWords word : List Nat) : flatten (factor prefixWords word) = word := by
  rw [factor]
  split
  next restShape =>
    change (splitSeen prefixWords word).1 = word
    simpa [restShape] using splitSeen_join prefixWords word
  next fresh rest restShape =>
    change (splitSeen prefixWords word).1 ++ fresh ::
      flatten (factor (prefixWords ++ (splitSeen prefixWords word).1 ++ [fresh]) rest) = word
    rw [factor_flatten (prefixWords ++ (splitSeen prefixWords word).1 ++ [fresh]) rest]
    simpa [restShape] using splitSeen_join prefixWords word
termination_by word.length
decreasing_by all_goals (apply splitSeen_tail_length; assumption)

theorem factor_wellFormed (prefixWords word : List Nat) : WellFormed prefixWords (factor prefixWords word) := by
  rw [factor]
  split
  next _ => exact splitSeen_seen prefixWords word
  next fresh rest restShape =>
    exact ⟨splitSeen_seen prefixWords word, splitSeen_fresh prefixWords word fresh rest restShape,
      factor_wellFormed (prefixWords ++ (splitSeen prefixWords word).1 ++ [fresh]) rest⟩
termination_by word.length
decreasing_by all_goals (apply splitSeen_tail_length; assumption)

theorem wellFormed_congr (chain : Chain) (left right : List Nat)
    (same : ∀ tested, tested ∈ left ↔ tested ∈ right) (good : WellFormed left chain) :
    WellFormed right chain := by
  induction chain generalizing left right with
  | stop gap => exact fun tested member => (same tested).mp (good tested member)
  | step gap fresh tail ih =>
      refine ⟨fun tested member => (same tested).mp (good.1 tested member),
        fun member => good.2.1 ((same fresh).mpr member), ?_⟩
      apply ih _ _ _ good.2.2
      intro tested
      simp only [List.mem_append, same tested]

theorem seen_prefix_extension_support (prefixWords left right : List Nat) (fresh : Nat)
    (leftSeen : AllSeen prefixWords left) (rightSeen : AllSeen prefixWords right) (tested : Nat) :
    tested ∈ prefixWords ++ left ++ [fresh] ↔ tested ∈ prefixWords ++ right ++ [fresh] := by
  simp only [List.mem_append, List.mem_singleton]
  constructor
  · intro member
    rcases member with (past | gap) | marker
    · exact Or.inl (Or.inl past)
    · exact Or.inl (Or.inl (leftSeen tested gap))
    · exact Or.inr marker
  · intro member
    rcases member with (past | gap) | marker
    · exact Or.inl (Or.inl past)
    · exact Or.inl (Or.inl (rightSeen tested gap))
    · exact Or.inr marker

theorem introductions_absent (chain : Chain) (prefixWords : List Nat) (good : WellFormed prefixWords chain) :
    ∀ tested ∈ introductions chain, tested ∉ prefixWords := by
  induction chain generalizing prefixWords with
  | stop gap => simp [introductions]
  | step gap fresh tail ih =>
      intro tested member
      rcases List.mem_cons.mp member with equal | later
      · simpa [equal] using good.2.1
      · intro past
        exact ih _ good.2.2 tested later (List.mem_append_left _ (List.mem_append_left _ past))

theorem introductions_nodup (chain : Chain) (prefixWords : List Nat) (good : WellFormed prefixWords chain) :
    (introductions chain).Nodup := by
  induction chain generalizing prefixWords with
  | stop gap => exact List.nodup_nil
  | step gap fresh tail ih =>
      apply List.nodup_cons.mpr
      refine ⟨?_, ih _ good.2.2⟩
      intro member
      exact introductions_absent tail _ good.2.2 fresh member (by simp)

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395WordGaps
