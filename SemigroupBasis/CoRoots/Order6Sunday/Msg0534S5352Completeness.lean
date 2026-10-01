import SemigroupBasis.CoRoots.Order6Sunday.Msg0524S5352Derivations
import SemigroupBasis.Opposite

/-! Unrestricted raw4 completeness for the literal S5352 table. Equal
unsaturated terminal tags fix the endpoint. When both endpoints are
saturated, a common filtered prefix exposes the already-screened
aabbba=aaabbb switch; the capped-prefix engine handles arbitrary counts. -/
namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0534S5352Completeness

open SemigroupBasis
open Msg0524S5352Evaluator Msg0524S5352Observations Msg0524S5352SemanticKey
open Msg0524S5352Derivations
open Msg0524S9662SemanticKey (snoc toList_snoc snoc_exists)
open CoRoots.Order6Day7.LeeZhang

theorem lastWith_snoc (stem : List Nat) (terminal fallback : Nat) :
    lastWith (stem ++ [terminal]) fallback = terminal := by
  induction stem generalizing fallback with
  | nil => rfl
  | cons a rest ih => exact ih a

theorem last_snoc (stem : List Nat) (terminal : Nat) : last (snoc stem terminal) = terminal := by
  cases stem with
  | nil => rfl
  | cons a rest => exact lastWith_snoc rest terminal a

def eraseEnds (letters : List Nat) (a b : Nat) : List Nat :=
  (letters.filter (fun x => decide (x ≠ a))).filter (fun x => decide (x ≠ b))

theorem eraseEnds_count (letters : List Nat) (a b z : Nat) :
    (eraseEnds letters a b).count z = if z = b then 0 else if z = a then 0 else letters.count z := by
  simp only [eraseEnds, CappedList.count_filter_ne]

theorem bank_count (letters : List Nat) (a b : Nat) (different : a ≠ b)
    (highA : 3 ≤ letters.count a) (highB : 3 ≤ letters.count b) (z : Nat) :
    min ((eraseEnds letters a b ++ [a,a,a,b,b,b]).count z) 3 = min (letters.count z) 3 := by
  by_cases za : z = a
  · subst z
    have cap : min (letters.count a) 3 = 3 := by omega
    simp [eraseEnds_count, different, Ne.symm different, cap]
  · by_cases zb : z = b
    · subst z
      have cap : min (letters.count b) 3 = 3 := by omega
      simp [eraseEnds_count, different, cap]
    · simp [eraseEnds_count, za, zb, Ne.symm za, Ne.symm zb]

theorem switch_count (front : List Nat) (a b z : Nat) :
    (front ++ [a,a,b,b,b,a]).count z = (front ++ [a,a,a,b,b,b]).count z := by
  simp only [List.count_append, List.count_cons, List.count_nil]
  omega

theorem saturatedEnds (left right : List Nat) (a b : Nat) (different : a ≠ b)
    (counts : ∀ z, min ((left ++ [a]).count z) 3 = min ((right ++ [b]).count z) 3)
    (highA : 3 ≤ (left ++ [a]).count a) (highB : 3 ≤ (right ++ [b]).count b) :
    LD (left ++ [a]) (right ++ [b]) := by
  have leftHighB : 3 ≤ (left ++ [a]).count b := by
    have same := counts b
    omega
  let front := eraseEnds (left ++ [a]) a b
  have bank (z : Nat) : min ((front ++ [a,a,a,b,b,b]).count z) 3 = min ((left ++ [a]).count z) 3 :=
    bank_count (left ++ [a]) a b different highA leftHighB z
  have first := sameTerminal left (front ++ [a,a,b,b,b]) a (by
    intro z
    have total := bank z
    rw [← switch_count front a b z] at total
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using total.symm)
  have second := sameTerminal (front ++ [a,a,a,b,b]) right b (by
    intro z
    have total := (bank z).trans (counts z)
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using total)
  have middle := (saturatedSwitch a b).prepend front
  simp only [List.append_assoc, List.cons_append, List.nil_append] at first second middle ⊢
  exact first.trans (middle.trans second)

theorem snoc_key_derives (left right : List Nat) (a b : Nat)
    (key : SameKey (snoc left a) (snoc right b)) :
    LD (left ++ [a]) (right ++ [b]) := by
  rcases key with ⟨counts, tags⟩
  simp only [toList_snoc] at counts
  by_cases ends : a = b
  · subst b
    exact sameTerminal left right a counts
  · have observed :
        (if (left ++ [a]).count a < 3 then some a else none) =
        (if (right ++ [b]).count b < 3 then some b else none) := by
      simpa only [terminalTag, last_snoc, toList_snoc] using tags
    have high : 3 ≤ (left ++ [a]).count a ∧ 3 ≤ (right ++ [b]).count b := by
      by_cases lowA : (left ++ [a]).count a < 3
      · by_cases lowB : (right ++ [b]).count b < 3
        · have equal : a = b := by simpa only [if_pos lowA, if_pos lowB, Option.some.injEq] using observed
          exact False.elim (ends equal)
        · simp only [if_pos lowA, if_neg lowB] at observed
          cases observed
      · by_cases lowB : (right ++ [b]).count b < 3
        · simp only [if_neg lowA, if_pos lowB] at observed
          cases observed
        · exact ⟨by omega, by omega⟩
    exact saturatedEnds left right a b ends counts high.1 high.2

theorem derives_of_key (left right : Word Nat) (key : SameKey left right) :
    Derives basis left right := by
  have lists : LD left.toList right.toList := by
    obtain ⟨leftStem, a, hl⟩ := snoc_exists left
    obtain ⟨rightStem, b, hr⟩ := snoc_exists right
    rw [hl, hr, toList_snoc, toList_snoc]
    exact snoc_key_derives leftStem rightStem a b (by simpa only [hl, hr] using key)
  cases left with
  | mk head tail =>
      cases right with
      | mk other rest => exact _root_.SemigroupBasis.CoRoots.S5_107.ListDerives.toWord lists

theorem complete (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derives_of_key identity.lhs identity.rhs (key_of_valid identity.lhs identity.rhs valid)

theorem representative_basis : BasisFor table.semigroup basis := ⟨models, complete⟩

theorem opposite_basis : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.CoRoots.Order6Sunday.Msg0534S5352Completeness
