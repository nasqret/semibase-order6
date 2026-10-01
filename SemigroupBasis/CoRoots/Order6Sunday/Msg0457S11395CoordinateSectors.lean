import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395ProcessedProfiles

/-! Scalar coordinates inside a simple-marker sector. A reduced coordinate
has only parity residues before its final pair. Resolution keeps the bits,
or places a necessary even pair at the sector's end. These are arbitrary-
length scalar theorems; the actual Chain resolver bridge is separate. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395CoordinateSectors

def positive : List Nat → Bool
  | [] => false
  | count :: rest => decide (0 < count) || positive rest

def bits (counts : List Nat) : List Nat := counts.map (fun n => n % 2)

def endPair : Nat → List Nat
  | 0 => []
  | 1 => [2]
  | n + 2 => 0 :: endPair (n + 1)

def canonical (counts : List Nat) : List Nat :=
  if positive (bits counts) then bits counts
  else if positive counts then endPair counts.length else bits counts

def ReducedCounts : List Nat → Prop
  | [] => True
  | count :: rest => count ≤ (if positive rest then 1 else 2) ∧ ReducedCounts rest

def resolve (past : Bool) : List Nat → List Nat
  | [] => []
  | count :: rest =>
      if 2 ≤ count then
        if past then 0 :: rest else endPair (count :: rest).length
      else count :: resolve (past || decide (0 < count)) rest

theorem positive_append (left right : List Nat) :
    positive (left ++ right) = (positive left || positive right) := by
  induction left with
  | nil => rfl
  | cons count rest ih =>
      simp only [List.cons_append, positive, ih, Bool.or_assoc]

theorem bits_of_no_positive (counts : List Nat) (empty : positive counts = false) : bits counts = counts := by
  induction counts with
  | nil => rfl
  | cons count rest ih =>
      cases count with
      | zero => exact congrArg (List.cons 0) (ih empty)
      | succ count => simp [positive] at empty

theorem bits_of_small (counts : List Nat) (small : ∀ count ∈ counts, count ≤ 1) : bits counts = counts := by
  induction counts with
  | nil => rfl
  | cons count rest ih =>
      have bound := small count (List.mem_cons_self)
      have fixed : count % 2 = count := Nat.mod_eq_of_lt (by omega)
      have tailFixed := ih (fun n member => small n (List.mem_cons_of_mem _ member))
      change count % 2 :: bits rest = count :: rest
      rw [fixed, tailFixed]

theorem canonical_of_small (counts : List Nat) (small : ∀ count ∈ counts, count ≤ 1) :
    canonical counts = bits counts := by
  have fixed := bits_of_small counts small
  unfold canonical
  rw [fixed]
  cases active : positive counts <;> simp

theorem canonical_eq_of_observations (left right : List Nat)
    (sameBits : bits left = bits right) (samePositive : positive left = positive right) :
    canonical left = canonical right := by
  have lengths : left.length = right.length := by
    simpa only [bits, List.length_map] using congrArg List.length sameBits
  simp only [canonical, sameBits, samePositive, lengths]

theorem canonical_zero_cons (counts : List Nat) : canonical (0 :: counts) = 0 :: canonical counts := by
  change (if positive (bits counts) then 0 :: bits counts
    else if positive counts then endPair (counts.length + 1) else 0 :: bits counts) = 0 :: canonical counts
  cases odd : positive (bits counts) with
  | true => simp [canonical, odd]
  | false =>
      cases active : positive counts with
      | false => simp [canonical, odd, active]
      | true =>
          cases counts with
          | nil => simp [positive] at active
          | cons count rest => simp [canonical, odd, active, endPair]

theorem canonical_one_cons (counts : List Nat) : canonical (1 :: counts) = 1 :: bits counts := rfl

theorem canonical_pair_no_future (counts : List Nat) (empty : positive counts = false) :
    canonical (2 :: counts) = endPair (counts.length + 1) := by
  change (if positive (bits counts) then 0 :: bits counts else endPair (counts.length + 1)) = _
  rw [bits_of_no_positive counts empty, empty]
  rfl

/-- A previous nonfirst occurrence absorbs the even pair; otherwise the
closed canonical sector formula supplies precisely its deterministic end. -/
theorem resolve_eq_canonical (past : Bool) (counts : List Nat) (red : ReducedCounts counts) :
    resolve past counts = if past then bits counts else canonical counts := by
  induction counts generalizing past with
  | nil => cases past <;> rfl
  | cons count rest ih =>
      obtain ⟨bound,tailRed⟩ := red
      by_cases doubled : 2 ≤ count
      · have empty : positive rest = false := by
          cases active : positive rest with
          | false => rfl
          | true =>
              have upper : count ≤ 1 := by simpa only [active] using bound
              omega
        have two : count = 2 := by
          have upper : count ≤ 2 := by simpa only [empty] using bound
          omega
        subst count
        cases past with
        | false =>
            change endPair (rest.length + 1) = canonical (2 :: rest)
            exact (canonical_pair_no_future rest empty).symm
        | true =>
            change 0 :: rest = 0 :: bits rest
            rw [bits_of_no_positive rest empty]
      · rcases (show count = 0 ∨ count = 1 by omega) with zero | one
        · subst count
          cases past with
          | false =>
              change 0 :: resolve false rest = canonical (0 :: rest)
              have tailStep : resolve false rest = canonical rest := ih false tailRed
              rw [tailStep, canonical_zero_cons]
          | true =>
              change 0 :: resolve true rest = 0 :: bits rest
              exact congrArg (List.cons 0) (ih true tailRed)
        · subst count
          cases past <;>
            exact congrArg (List.cons 1) (ih true tailRed)

theorem resolve_false_eq (counts : List Nat) (red : ReducedCounts counts) : resolve false counts = canonical counts :=
  resolve_eq_canonical false counts red

theorem resolve_true_eq (counts : List Nat) (red : ReducedCounts counts) : resolve true counts = bits counts :=
  resolve_eq_canonical true counts red

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395CoordinateSectors
