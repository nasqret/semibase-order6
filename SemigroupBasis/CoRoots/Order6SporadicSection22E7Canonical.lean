import SemigroupBasis.CoRoots.Order6SporadicSection22E7Derivations

/-! The actual canonical-form existence theorem of Lee-Zhang2015,
Lemma22.10. First occurrences are retained; each intervening old-letter
block retains only its last letter. The derivation is unrestricted.
The remaining semantic uniqueness theorem is not assumed here. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection22.E7
open SemigroupBasis

structure CanonicalBlock where
  letter : Nat
  extra : List Nat
deriving DecidableEq, Repr

def renderBlocks : List CanonicalBlock → List Nat
  | [] => []
  | first :: rest => first.letter :: (first.extra ++ renderBlocks rest)

def WellFormed : List Nat → List CanonicalBlock → Prop
  | _, [] => True
  | seen, first :: rest =>
      first.letter ∉ seen ∧ first.extra.length ≤ 1 ∧
      (∀ x ∈ first.extra, x ∈ first.letter :: seen) ∧
      WellFormed (first.letter :: seen) rest

def FreshHead (seen : List Nat) : List Nat → Prop
  | [] => True
  | x :: _ => x ∉ seen

theorem splitKnown (seen : List Nat) : ∀ input : List Nat,
    ∃ old rest, input = old ++ rest ∧
      (∀ x ∈ old, x ∈ seen) ∧ FreshHead seen rest
  | [] => ⟨[],[],rfl,(by simp),True.intro⟩
  | x :: xs => by
      by_cases known : x ∈ seen
      · obtain ⟨old,rest,shape,oldKnown,fresh⟩ := splitKnown seen xs
        refine ⟨x :: old,rest,?_,?_,fresh⟩
        · simp [shape]
        · intro a member
          rcases List.mem_cons.mp member with same | later
          · simpa [same] using known
          · exact oldKnown a later
      · exact ⟨[],x :: xs,rfl,(by simp),known⟩

private theorem canonicalizeBound (bound : Nat) :
    ∀ input : List Nat, input.length ≤ bound →
    ∀ stem seen : List Nat, (∀ x ∈ seen, x ∈ stem) → FreshHead seen input →
    ∃ blocks, WellFormed seen blocks ∧
      ListDerives (stem ++ input) (stem ++ renderBlocks blocks) := by
  induction bound with
  | zero =>
      intro input lengthBound stem seen seenInStem fresh
      cases input with
      | nil => exact ⟨[],True.intro,S5_107.ListDerives.refl _⟩
      | cons x xs => simp at lengthBound
  | succ bound ih =>
      intro input lengthBound stem seen seenInStem fresh
      cases input with
      | nil => exact ⟨[],True.intro,S5_107.ListDerives.refl _⟩
      | cons x xs =>
          obtain ⟨old,rest,shape,oldKnown,restFresh⟩ := splitKnown (x :: seen) xs
          have restBound : rest.length ≤ bound := by
            have sizes := congrArg List.length shape
            simp only [List.length_append] at sizes
            simp only [List.length_cons] at lengthBound
            omega
          let block : CanonicalBlock := ⟨x,lastSingleton old⟩
          let nextStem := stem ++ [x] ++ lastSingleton old
          have knownBefore : ∀ a ∈ x :: seen, a ∈ stem ++ [x] := by
            intro a member
            rcases List.mem_cons.mp member with same | prior
            · simp [same]
            · exact List.mem_append.mpr (Or.inl (seenInStem a prior))
          have knownAfter : ∀ a ∈ x :: seen, a ∈ nextStem := by
            intro a member
            exact List.mem_append.mpr (Or.inl (knownBefore a member))
          obtain ⟨blocks,blocksGood,tailDerives⟩ :=
            ih rest restBound nextStem (x :: seen) knownAfter restFresh
          have prune : ListDerives (stem ++ x :: xs) (nextStem ++ rest) := by
            have step := (pruneSeenBlock (stem ++ [x]) old
              (fun a member => knownBefore a (oldKnown a member))).append rest
            simpa [nextStem,shape,List.append_assoc] using step
          refine ⟨block :: blocks,?_,?_⟩
          · exact ⟨fresh,lastSingleton_length old,
              (fun a member => oldKnown a (lastSingleton_mem old a member)),blocksGood⟩
          · simpa [nextStem,block,renderBlocks,List.append_assoc] using prune.trans tailDerives

theorem existsCanonicalFrom (stem seen input : List Nat)
    (seenInStem : ∀ x ∈ seen, x ∈ stem) (fresh : FreshHead seen input) :
    ∃ blocks, WellFormed seen blocks ∧
      ListDerives (stem ++ input) (stem ++ renderBlocks blocks) :=
  canonicalizeBound input.length input (Nat.le_refl _) stem seen seenInStem fresh

theorem existsCanonical (input : List Nat) :
    ∃ blocks, WellFormed [] blocks ∧ ListDerives input (renderBlocks blocks) := by
  have fresh : FreshHead [] input := by cases input <;> simp [FreshHead]
  simpa using existsCanonicalFrom [] [] input (by simp) fresh

def canonicalWord (first : CanonicalBlock) (rest : List CanonicalBlock) : Word Nat :=
  ⟨first.letter,first.extra ++ renderBlocks rest⟩

theorem canonicalWord_toList (first : CanonicalBlock) (rest : List CanonicalBlock) :
    (canonicalWord first rest).toList = renderBlocks (first :: rest) := rfl

theorem existsCanonicalWord (word : Word Nat) :
    ∃ first rest, WellFormed [] (first :: rest) ∧
      Derives basis word (canonicalWord first rest) := by
  obtain ⟨blocks,good,derivation⟩ := existsCanonical word.toList
  cases blocks with
  | nil => exact False.elim (derivation.target_ne_nil rfl)
  | cons first rest =>
      refine ⟨first,rest,good,?_⟩
      cases word with
      | mk head tail => exact derivation.toWord

theorem labels_fresh (seen : List Nat) : ∀ blocks : List CanonicalBlock,
    WellFormed seen blocks → ∀ x ∈ blocks.map CanonicalBlock.letter, x ∉ seen
  | [], _, _, member => by simp at member
  | first :: rest, good, x, member => by
      rcases List.mem_cons.mp member with same | later
      · simpa [same] using good.1
      · have absent := labels_fresh (first.letter :: seen) rest good.2.2.2 x later
        intro prior
        exact absent (List.mem_cons_of_mem first.letter prior)

theorem labels_nodup (seen : List Nat) : ∀ blocks : List CanonicalBlock,
    WellFormed seen blocks → (blocks.map CanonicalBlock.letter).Nodup
  | [], _ => by simp
  | first :: rest, good => by
      have absent : first.letter ∉ rest.map CanonicalBlock.letter := by
        intro member
        exact labels_fresh (first.letter :: seen) rest good.2.2.2 first.letter member (by simp)
      exact List.nodup_cons.mpr ⟨absent,labels_nodup (first.letter :: seen) rest good.2.2.2⟩

theorem render_length_bound (seen : List Nat) : ∀ blocks : List CanonicalBlock,
    WellFormed seen blocks → (renderBlocks blocks).length ≤ 2 * blocks.length
  | [], _ => by simp [renderBlocks]
  | first :: rest, good => by
      have tailBound := render_length_bound (first.letter :: seen) rest good.2.2.2
      have extraBound := good.2.1
      simp only [renderBlocks,List.length_cons,List.length_append]
      omega

#print axioms splitKnown
#print axioms existsCanonicalFrom
#print axioms existsCanonical
#print axioms existsCanonicalWord
#print axioms labels_fresh
#print axioms labels_nodup
#print axioms render_length_bound

end SemigroupBasis.CoRoots.Order6SporadicSection22.E7
