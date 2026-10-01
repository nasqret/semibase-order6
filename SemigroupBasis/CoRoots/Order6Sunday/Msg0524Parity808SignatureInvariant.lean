import SemigroupBasis.CoRoots.S5_848
import SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808Blocks

/-! Syntactic preservation of the reversed tail-square observations by the
unchanged Parity808 raw basis. This does not assert that validity in S5_808
implies those observations, or construct the stopped whole-word canonicalizer.
The last theorem compares the already-proved block normalizer's exact counts.
-/
namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808SignatureInvariant

open SemigroupBasis
open Msg0524Parity808Gather (reducedExponent)
open Msg0524Parity808Blocks (normalWord)

theorem reverse_power :
    Derives S5_848.basis Msg0524Parity808Gather.law0.reversed.lhs
      Msg0524Parity808Gather.law0.reversed.rhs := by
  change Derives S5_848.basis ⟨0,[0]⟩ ⟨0,[0,0,0]⟩
  exact (S5_848.derivesPowerExpansion (Word.singleton 0)).trans
    ((S5_848.derivesPowerExpansion (Word.singleton 0)).appendRight (Word.singleton 0))

theorem reverse_tail :
    Derives S5_848.basis Msg0524Parity808Gather.law1.reversed.lhs
      Msg0524Parity808Gather.law1.reversed.rhs := by
  change Derives S5_848.basis ⟨2,[1,1,0,0]⟩ ⟨2,[0,1,1,0]⟩
  exact S5_848.derivesTailSquarePromotion (Word.singleton 2) (Word.singleton 1) (Word.singleton 0)

theorem reverse_gather :
    Derives S5_848.basis Msg0524Parity808Gather.law2.reversed.lhs
      Msg0524Parity808Gather.law2.reversed.rhs := by
  change Derives S5_848.basis ⟨0,[1,0]⟩ ⟨0,[0,1]⟩
  exact S5_848.derivesGather (Word.singleton 0) (Word.singleton 1)

theorem reversed_axioms (identity : Identity Nat)
    (member : identity ∈ reversedBasis Msg0524Parity808Gather.basis) :
    Derives S5_848.basis identity.lhs identity.rhs := by
  change identity ∈ Msg0524Parity808Gather.basis.map Identity.reversed at member
  obtain ⟨raw, rawMember, rfl⟩ := List.mem_map.mp member
  simp only [Msg0524Parity808Gather.basis,List.mem_cons,List.not_mem_nil,or_false] at rawMember
  rcases rawMember with rfl | rfl | rfl
  · exact reverse_power
  · exact reverse_tail
  · exact reverse_gather

/-- A raw derivation translates syntactically, with no S5_808 validity premise. -/
theorem reversed_derivation {left right : Word Nat}
    (derivation : Derives Msg0524Parity808Gather.basis left right) :
    Derives S5_848.basis left.reverse right.reverse :=
  derivation.reverse.transport reversed_axioms

theorem rawDerives_tailSignature {left right : Word Nat}
    (derivation : Derives Msg0524Parity808Gather.basis left right) :
    S5_848.SameTailSquareSignature left.reverse right.reverse :=
  S5_848.derives_sameSignature (reversed_derivation derivation)

/-- The existing block reducer preserves all reversed tail-square observations. -/
theorem normalWord_tailSignature (word : Word Nat) :
    S5_848.SameTailSquareSignature word.reverse (normalWord word).reverse :=
  rawDerives_tailSignature (Msg0524Parity808Blocks.normalWord_derives word)

theorem normalWord_pair_tailSignature {left right : Word Nat}
    (same : S5_848.SameTailSquareSignature left.reverse right.reverse) :
    S5_848.SameTailSquareSignature (normalWord left).reverse (normalWord right).reverse :=
  ((normalWord_tailSignature left).symm.trans same).trans (normalWord_tailSignature right)

theorem reducedExponent_capped (n : Nat) :
    Nat.min 2 (reducedExponent n) = Nat.min 2 n := by
  change min 2 (reducedExponent n) = min 2 n
  by_cases small : n < 2
  · rw [reducedExponent,if_pos small]
  · rw [reducedExponent,if_neg small,
      Nat.min_eq_left (by omega : 2 ≤ 2 + n % 2),Nat.min_eq_left (by omega : 2 ≤ n)]

/-- The cap distinguishes absent/single/repeated; parity distinguishes 2 from 3. -/
theorem reducedExponent_eq_iff_cap_parity (n m : Nat) :
    reducedExponent n = reducedExponent m ↔
      Nat.min 2 n = Nat.min 2 m ∧ n % 2 = m % 2 := by
  constructor
  · intro same
    constructor
    · simpa only [reducedExponent_capped] using congrArg (Nat.min 2) same
    · calc
        n % 2 = reducedExponent n % 2 := (Msg0524Parity808Gather.reducedExponent_parity n).symm
        _ = reducedExponent m % 2 := congrArg (fun k : Nat => k % 2) same
        _ = m % 2 := Msg0524Parity808Gather.reducedExponent_parity m
  · rintro ⟨capped, parity⟩
    change min 2 n = min 2 m at capped
    by_cases smallN : n < 2
    · by_cases smallM : m < 2
      · rw [Nat.min_eq_right (by omega : n ≤ 2),Nat.min_eq_right (by omega : m ≤ 2)] at capped
        simpa only [reducedExponent,if_pos smallN,if_pos smallM] using capped
      · rw [Nat.min_eq_right (by omega : n ≤ 2),Nat.min_eq_left (by omega : 2 ≤ m)] at capped
        omega
    · by_cases smallM : m < 2
      · rw [Nat.min_eq_left (by omega : 2 ≤ n),Nat.min_eq_right (by omega : m ≤ 2)] at capped
        omega
      · simp only [reducedExponent,if_neg smallN,if_neg smallM,parity]

theorem reversed_signature_capped {left right : Word Nat}
    (same : S5_848.SameTailSquareSignature left.reverse right.reverse) (letter : Nat) :
    Nat.min 2 (left.toList.count letter) = Nat.min 2 (right.toList.count letter) := by
  simpa [S5_107.cappedMultiplicity] using same.capped letter

theorem normalWord_count_eq_iff (left right : Word Nat) (letter : Nat) :
    (normalWord left).toList.count letter = (normalWord right).toList.count letter ↔
      Nat.min 2 (left.toList.count letter) = Nat.min 2 (right.toList.count letter) ∧
        left.toList.count letter % 2 = right.toList.count letter % 2 := by
  rw [Msg0524Parity808Blocks.normalWord_count,Msg0524Parity808Blocks.normalWord_count]
  exact reducedExponent_eq_iff_cap_parity _ _

/-- Exact multiplicities in the block words agree for any words with equal
reversed tail-square signature and letterwise parity; no finite bound occurs. -/
theorem normalWord_counts_eq_of_signature {left right : Word Nat}
    (same : S5_848.SameTailSquareSignature left.reverse right.reverse)
    (parity : ∀ letter, left.toList.count letter % 2 = right.toList.count letter % 2) :
    ∀ letter, (normalWord left).toList.count letter = (normalWord right).toList.count letter := by
  intro letter
  exact (normalWord_count_eq_iff left right letter).2
    ⟨reversed_signature_capped same letter,parity letter⟩

end SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808SignatureInvariant
