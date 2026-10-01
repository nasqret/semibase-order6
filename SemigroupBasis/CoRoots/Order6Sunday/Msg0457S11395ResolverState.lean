import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395SectorSignature

/-! The actual Absorber selector is an online nonfirst-occurrence state.
Seen gaps accumulate that state; globally simple fresh markers reset it.
All statements concern the existing selector, not an assumed substitute. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395ResolverState

open SemigroupBasis
open Msg0457S11395Absorber Msg0457S11395SectorPairs Msg0457S11395SeenSwaps
open Msg0457S11395WordGaps Msg0457S11395SectorCut

def available (whole prefixWords : List Nat) (letter : Nat) : Bool :=
  (find whole prefixWords letter).isSome

theorem clear_append (whole left right : List Nat) :
    clear whole (left ++ right) = (clear whole left && clear whole right) := by
  simp [clear, List.all_append]

theorem scan_isSome_cons (whole : List Nat) (letter head : Nat) (seen : Bool) (rest : List Nat) :
    (scan whole letter seen (head :: rest)).isSome =
      ((decide (head = letter) && seen && clear whole rest) ||
        (scan whole letter (seen || head == letter) rest).isSome) := by
  by_cases equal : head = letter <;> cases seen <;> cases free : clear whole rest <;>
    simp [scan, equal, free]

theorem scan_isSome_append (whole prefixWords suffix : List Nat) (letter : Nat) (seen : Bool) :
    (scan whole letter seen (prefixWords ++ suffix)).isSome =
      (((scan whole letter seen prefixWords).isSome && clear whole suffix) ||
        (scan whole letter (seen || decide (letter ∈ prefixWords)) suffix).isSome) := by
  induction prefixWords generalizing seen with
  | nil => simp [scan]
  | cons head rest ih =>
      rw [List.cons_append, scan_isSome_cons, clear_append, ih, scan_isSome_cons]
      have seed : ((seen || head == letter) || decide (letter ∈ rest)) =
          (seen || decide (letter ∈ head :: rest)) := by
        by_cases equal : head = letter
        · subst head; simp
        · have off : (head == letter) = false := by
            cases value : head == letter with
            | false => rfl
            | true => exact False.elim (equal (by simpa using value))
          simp [off, Ne.symm equal]
      rw [seed]
      cases free : clear whole suffix <;> simp [Bool.and_assoc, Bool.or_assoc]

theorem scan_absent (whole prefixWords : List Nat) (letter : Nat) (seen : Bool)
    (absent : letter ∉ prefixWords) : scan whole letter seen prefixWords = none := by
  cases found : scan whole letter seen prefixWords with
  | none => rfl
  | some parts =>
      have shape := (scan_sound whole prefixWords letter seen parts.1 parts.2 found).1
      exact False.elim (absent (by simp [shape]))

theorem scan_true_simpleFree (whole block : List Nat) (letter : Nat) (free : SimpleFree whole block) :
    (scan whole letter true block).isSome = decide (letter ∈ block) := by
  induction block with
  | nil => rfl
  | cons head rest ih =>
      have tailFree : SimpleFree whole rest := fun tested member => free tested (List.mem_cons_of_mem head member)
      have tailClear := (clear_spec whole rest).2 tailFree
      rw [scan_isSome_cons]
      by_cases equal : head = letter
      · subst head; simp [tailClear]
      · simp [equal, Ne.symm equal, ih tailFree]

theorem available_append (whole prefixWords suffix : List Nat) (letter : Nat) :
    available whole (prefixWords ++ suffix) letter =
      ((available whole prefixWords letter && clear whole suffix) ||
        (scan whole letter (decide (letter ∈ prefixWords)) suffix).isSome) := by
  simpa only [available, find, Bool.false_or] using
    scan_isSome_append whole prefixWords suffix letter false

theorem available_nil (whole : List Nat) (letter : Nat) : available whole [] letter = false := rfl

theorem available_singleton (whole : List Nat) (head letter : Nat) :
    available whole [head] letter = false := by
  simp [available, find, scan]

theorem available_snoc (whole prefixWords : List Nat) (letter fresh : Nat) :
    available whole (prefixWords ++ [fresh]) letter =
      ((available whole prefixWords letter && decide (whole.count fresh ≠ 1)) ||
        (decide (letter ∈ prefixWords) && decide (fresh = letter))) := by
  rw [available_append]
  by_cases earlier : letter ∈ prefixWords <;> by_cases equal : fresh = letter <;>
    simp [clear, scan, earlier, equal]

theorem available_seenGap (whole prefixWords gap : List Nat) (letter : Nat)
    (seen : AllSeen prefixWords gap) (free : SimpleFree whole gap) :
    available whole (prefixWords ++ gap) letter =
      (available whole prefixWords letter || decide (0 < gap.count letter)) := by
  rw [available_append, (clear_spec whole gap).2 free]
  by_cases earlier : letter ∈ prefixWords
  · simp only [Bool.and_true, earlier, decide_true]
    rw [scan_true_simpleFree whole gap letter free]
    simp only [List.count_pos_iff]
  · have absent : letter ∉ gap := fun member => earlier (seen letter member)
    simp [earlier, scan_absent whole gap letter false absent, List.count_eq_zero.mpr absent]

theorem available_fresh (whole prefixWords : List Nat) (letter fresh : Nat)
    (absent : fresh ∉ prefixWords) :
    available whole (prefixWords ++ [fresh]) letter =
      (available whole prefixWords letter && decide (whole.count fresh ≠ 1)) := by
  rw [available_snoc]
  by_cases equal : fresh = letter
  · subst fresh; simp [absent]
  · simp [equal]

theorem available_gap_fresh (whole prefixWords gap : List Nat) (letter fresh : Nat)
    (seen : AllSeen prefixWords gap) (free : SimpleFree whole gap) (absent : fresh ∉ prefixWords) :
    available whole (prefixWords ++ gap ++ [fresh]) letter =
      if whole.count fresh = 1 then false
      else (available whole prefixWords letter || decide (0 < gap.count letter)) := by
  have missing : fresh ∉ prefixWords ++ gap := by
    intro member
    rcases List.mem_append.mp member with past | inGap
    · exact absent past
    · exact absent (seen fresh inGap)
  rw [available_fresh whole (prefixWords ++ gap) letter fresh missing,
    available_seenGap whole prefixWords gap letter seen free]
  by_cases simple : whole.count fresh = 1 <;> simp [simple]

theorem actual_step_available (prefixWords gap : List Nat) (letter fresh : Nat) (tail : Chain)
    (good : WellFormed prefixWords (.step gap fresh tail)) :
    available (prefixWords ++ flatten (.step gap fresh tail)) (prefixWords ++ gap ++ [fresh]) letter =
      if (prefixWords ++ flatten (.step gap fresh tail)).count fresh = 1 then false
      else (available (prefixWords ++ flatten (.step gap fresh tail)) prefixWords letter ||
        decide (0 < gap.count letter)) := by
  apply available_gap_fresh _ prefixWords gap letter fresh good.1 _ good.2.1
  simpa [flatten, List.append_assoc] using
    seenGap_simpleFree prefixWords gap (fresh :: flatten tail) good.1

def step (whole : List Nat) (letter : Nat) (state : Bool × Bool) (head : Nat) : Bool × Bool :=
  (state.1 || decide (head = letter),
   (state.2 && decide (whole.count head ≠ 1)) || (state.1 && decide (head = letter)))

theorem step_summary (whole prefixWords : List Nat) (letter head : Nat) :
    step whole letter (decide (letter ∈ prefixWords), available whole prefixWords letter) head =
      (decide (letter ∈ prefixWords ++ [head]), available whole (prefixWords ++ [head]) letter) := by
  rw [available_snoc]
  unfold step
  apply Prod.ext
  · by_cases earlier : letter ∈ prefixWords <;> by_cases equal : head = letter <;>
      simp [earlier, equal, Ne.symm]
  · rfl

theorem fold_summary (whole prefixWords suffix : List Nat) (letter : Nat) :
    suffix.foldl (step whole letter) (decide (letter ∈ prefixWords), available whole prefixWords letter) =
      (decide (letter ∈ prefixWords ++ suffix), available whole (prefixWords ++ suffix) letter) := by
  induction suffix generalizing prefixWords with
  | nil => simp
  | cons head rest ih =>
      rw [List.foldl_cons, step_summary, ih]
      simp only [List.append_assoc, List.singleton_append]

def online (whole prefixWords : List Nat) (letter : Nat) : Bool :=
  (prefixWords.foldl (step whole letter) (false,false)).2

theorem online_eq_available (whole prefixWords : List Nat) (letter : Nat) :
    online whole prefixWords letter = available whole prefixWords letter := by
  have paired := fold_summary whole [] prefixWords letter
  simpa only [List.not_mem_nil, decide_false, available_nil, List.nil_append, online] using
    congrArg Prod.snd paired

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395ResolverState
