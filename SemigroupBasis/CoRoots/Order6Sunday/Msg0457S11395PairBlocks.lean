import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395MixedPairs

/-! Actual B12 movement of an even run across a block containing no
globally simple letter. Repeated witnesses may be before the block,
inside it, or after it. This connects first-occurrence gaps, but is not
yet the global SignatureReach theorem. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395PairBlocks

open SemigroupBasis
open Msg0457S11395Semantics Msg0457S11395EvenInsertion Msg0457S11395MixedPairs

/-- Counts refer to the retained context, excluding the moved pair/run. -/
def NoSimpleInBlock (prefixWords block suffix : List Nat) : Prop :=
  ∀ tested ∈ block, 2 ≤ (prefixWords ++ block ++ suffix).count tested

theorem headWitness (prefixWords rest suffix : List Nat) (crossed : Nat)
    (guarded : NoSimpleInBlock prefixWords (crossed :: rest) suffix) :
    crossed ∈ prefixWords ∨ crossed ∈ rest ++ suffix := by
  by_cases past : crossed ∈ prefixWords
  · exact Or.inl past
  · apply Or.inr
    by_cases future : crossed ∈ rest ++ suffix
    · exact future
    · have absentRest : crossed ∉ rest := fun member => future (List.mem_append_left _ member)
      have absentSuffix : crossed ∉ suffix := fun member => future (List.mem_append_right _ member)
      have bound := guarded crossed (by simp)
      simp [List.count_append, List.count_eq_zero.mpr past,
        List.count_eq_zero.mpr absentRest, List.count_eq_zero.mpr absentSuffix] at bound

theorem noSimpleInBlock_extendPrefix (prefixWords block suffix extra : List Nat)
    (guarded : NoSimpleInBlock prefixWords block suffix) :
    NoSimpleInBlock (prefixWords ++ extra) block suffix := by
  intro tested member
  have bound := guarded tested member
  simp only [List.count_append] at bound ⊢
  omega

theorem noSimpleInBlock_extendSuffix (prefixWords block suffix extra : List Nat)
    (guarded : NoSimpleInBlock prefixWords block suffix) :
    NoSimpleInBlock prefixWords block (extra ++ suffix) := by
  intro tested member
  have bound := guarded tested member
  simp only [List.count_append] at bound ⊢
  omega

/-- A first introduction may be crossed precisely using its remaining
witness. A globally simple letter in this block is not permitted. -/
theorem movePairAcrossBlock (prefixWords block suffix : List Nat) (letter : Nat)
    (seen : letter ∈ prefixWords) (guarded : NoSimpleInBlock prefixWords block suffix) :
    LD (prefixWords ++ [letter,letter] ++ block ++ suffix)
      (prefixWords ++ block ++ [letter,letter] ++ suffix) := by
  induction block generalizing prefixWords with
  | nil => simpa using S5_107.ListDerives.refl (basis := basis) (prefixWords ++ [letter,letter] ++ suffix)
  | cons crossed rest ih =>
      have step := movePairPastWitnessed prefixWords (rest ++ suffix) letter crossed seen
        (headWitness prefixWords rest suffix crossed guarded)
      have tailGuard : NoSimpleInBlock (prefixWords ++ [crossed]) rest suffix := by
        intro tested member
        simpa [List.append_assoc] using guarded tested (List.mem_cons_of_mem crossed member)
      have tail := ih (prefixWords ++ [crossed]) (List.mem_append_left _ seen) tailGuard
      have first : LD (prefixWords ++ [letter,letter] ++ (crossed :: rest) ++ suffix)
          ((prefixWords ++ [crossed]) ++ [letter,letter] ++ rest ++ suffix) := by
        simpa [List.append_assoc] using step
      simpa [List.append_assoc] using first.trans tail

theorem moveEvenAcrossBlock (prefixWords block suffix : List Nat) (letter pairs : Nat)
    (seen : letter ∈ prefixWords) (guarded : NoSimpleInBlock prefixWords block suffix) :
    LD (prefixWords ++ List.replicate (2 * pairs) letter ++ block ++ suffix)
      (prefixWords ++ block ++ List.replicate (2 * pairs) letter ++ suffix) := by
  induction pairs generalizing prefixWords suffix with
  | zero => simpa using S5_107.ListDerives.refl (basis := basis) (prefixWords ++ block ++ suffix)
  | succ pairs ih =>
      have step := movePairAcrossBlock (prefixWords ++ List.replicate (2 * pairs) letter)
        block suffix letter (List.mem_append_left _ seen)
        (noSimpleInBlock_extendPrefix prefixWords block suffix _ guarded)
      have remaining := ih prefixWords ([letter,letter] ++ suffix) seen
        (noSimpleInBlock_extendSuffix prefixWords block suffix _ guarded)
      have first : LD (prefixWords ++ List.replicate (2 * (pairs + 1)) letter ++ block ++ suffix)
          (prefixWords ++ List.replicate (2 * pairs) letter ++ block ++ [letter,letter] ++ suffix) := by
        simpa [Nat.mul_add, replicateAdd, List.append_assoc] using step
      apply first.trans
      simpa [Nat.mul_add, replicateAdd, List.append_assoc] using remaining

theorem moveEvenBlockWord (head letter pairs : Nat) (before block suffix : List Nat)
    (seen : letter ∈ head :: before) (guarded : NoSimpleInBlock (head :: before) block suffix) :
    Derives basis
      ⟨head, before ++ List.replicate (2 * pairs) letter ++ block ++ suffix⟩
      ⟨head, before ++ block ++ List.replicate (2 * pairs) letter ++ suffix⟩ := by
  exact (show LD
    (head :: (before ++ List.replicate (2 * pairs) letter ++ block ++ suffix))
    (head :: (before ++ block ++ List.replicate (2 * pairs) letter ++ suffix)) from
      by simpa using moveEvenAcrossBlock (head :: before) block suffix letter pairs seen guarded).toWord

theorem moveEvenBlockPreservesSignature (head letter pairs : Nat) (before block suffix : List Nat)
    (seen : letter ∈ head :: before) (guarded : NoSimpleInBlock (head :: before) block suffix) :
    Msg0457S11395Observations.SameSignature
      ⟨head, before ++ List.replicate (2 * pairs) letter ++ block ++ suffix⟩
      ⟨head, before ++ block ++ List.replicate (2 * pairs) letter ++ suffix⟩ :=
  Msg0457S11395Signature.derives_preserve_signature
    (moveEvenBlockWord head letter pairs before block suffix seen guarded)

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395PairBlocks
