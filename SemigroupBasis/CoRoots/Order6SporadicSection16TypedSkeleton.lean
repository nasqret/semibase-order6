import SemigroupBasis.CoRoots.Order6SporadicSection16SkeletonNormalization
import SemigroupBasis.CoRoots.Order6SporadicSection16SeparatorPruning

/-!
A typed representation of the already proved Section16 scanner. This module
does not substitute an assumed shape for its output: render_scanTokens is an
equality with normalizeAux, and the distinctness/anchor-exclusion invariant
is proved for the actual recursive computation.
Reference: Lee and Zhang (2015), Proposition16.1 / Lemma16.3, pp.49-52.
-/

namespace SemigroupBasis.CoRoots.Order6SporadicSection16

open SemigroupBasis

inductive SkeletonToken where
  | marker
  | letter (value : Nat) (doubled : Bool)
deriving Repr, DecidableEq

def renderToken (anchor : Nat) : SkeletonToken → List Nat
  | .marker => [anchor, anchor]
  | .letter value doubled => if doubled then [value, value] else [value]

def renderTokens (anchor : Nat) (tokens : List SkeletonToken) : List Nat :=
  tokens.flatMap (renderToken anchor)

def tokenLetters : List SkeletonToken → List Nat
  | [] => []
  | .marker :: tail => tokenLetters tail
  | .letter value _ :: tail => value :: tokenLetters tail

theorem renderTokens_append (anchor : Nat) (left right : List SkeletonToken) :
    renderTokens anchor (left ++ right) = renderTokens anchor left ++ renderTokens anchor right := by
  simp [renderTokens, List.flatMap_append]

theorem tokenLetters_append (left right : List SkeletonToken) :
    tokenLetters (left ++ right) = tokenLetters left ++ tokenLetters right := by
  induction left with
  | nil => rfl
  | cons head tail ih => cases head <;> simp [tokenLetters, ih]

theorem tokenLetter_mem_render {anchor value : Nat} {tokens : List SkeletonToken}
    (member : value ∈ tokenLetters tokens) : value ∈ renderTokens anchor tokens := by
  induction tokens with
  | nil => simp [tokenLetters] at member
  | cons head tail ih =>
      cases head with
      | marker =>
          have inRendered : value ∈ [anchor, anchor] ++ renderTokens anchor tail :=
            List.mem_append.mpr (Or.inr (ih member))
          simpa [renderTokens, renderToken] using inRendered
      | letter letter doubled =>
          rcases List.mem_cons.mp member with equal | inTail
          · subst value
            cases doubled <;> simp [renderTokens, renderToken]
          · have inRendered : value ∈ renderToken anchor (.letter letter doubled) ++ renderTokens anchor tail :=
              List.mem_append.mpr (Or.inr (ih inTail))
            simpa [renderTokens] using inRendered

def closeTokens (tokens : List SkeletonToken) (pending : List Nat) : List SkeletonToken :=
  if pending = [] then tokens else tokens ++ [.marker]

theorem render_closeTokens (anchor : Nat) (tokens : List SkeletonToken) (pending : List Nat) :
    renderTokens anchor (closeTokens tokens pending) = closeGap anchor (renderTokens anchor tokens) pending := by
  by_cases empty : pending = [] <;>
    simp [closeTokens, closeGap, empty, renderTokens, renderToken]

theorem letters_closeTokens (tokens : List SkeletonToken) (pending : List Nat) :
    tokenLetters (closeTokens tokens pending) = tokenLetters tokens := by
  by_cases empty : pending = [] <;> simp [closeTokens, empty, tokenLetters_append, tokenLetters]

def advanceTokens (tokens : List SkeletonToken) (pending : List Nat)
    (letter : Nat) (rest : List Nat) : List SkeletonToken :=
  closeTokens tokens pending ++ [.letter letter (decide (letter ∈ rest))]

theorem render_advanceTokens (anchor : Nat) (tokens : List SkeletonToken)
    (pending : List Nat) (letter : Nat) (rest : List Nat) :
    renderTokens anchor (advanceTokens tokens pending letter rest) =
      closeGap anchor (renderTokens anchor tokens) pending ++ nextBlock letter rest := by
  unfold advanceTokens
  rw [renderTokens_append, render_closeTokens]
  have singletonRender :
      renderTokens anchor [.letter letter (decide (letter ∈ rest))] = nextBlock letter rest := by
    by_cases again : letter ∈ rest <;> simp [renderTokens, renderToken, nextBlock, again]
  rw [singletonRender]

theorem letters_advanceTokens (tokens : List SkeletonToken)
    (pending : List Nat) (letter : Nat) (rest : List Nat) :
    tokenLetters (advanceTokens tokens pending letter rest) = tokenLetters tokens ++ [letter] := by
  simp [advanceTokens, tokenLetters_append, letters_closeTokens, tokenLetters]

def scanTokens (anchor : Nat) (tokens : List SkeletonToken) (pending : List Nat) :
    List Nat → List SkeletonToken
  | [] => closeTokens tokens pending
  | letter :: rest =>
      if letter ∈ [anchor, anchor] ++ renderTokens anchor tokens then
        scanTokens anchor tokens (pending ++ [letter]) rest
      else
        scanTokens anchor (advanceTokens tokens pending letter rest) [] rest

/-- Exact typed-to-list representation equality for the actual scanner. -/
theorem render_scanTokens (anchor : Nat) (tokens : List SkeletonToken)
    (pending rest : List Nat) :
    renderTokens anchor (scanTokens anchor tokens pending rest) =
      normalizeAux anchor (renderTokens anchor tokens) pending rest := by
  induction rest generalizing tokens pending with
  | nil => exact render_closeTokens anchor tokens pending
  | cons letter rest ih =>
      by_cases seen : letter ∈ [anchor, anchor] ++ renderTokens anchor tokens
      · rw [scanTokens, if_pos seen, normalizeAux, if_pos seen]
        exact ih tokens (pending ++ [letter])
      · rw [scanTokens, if_neg seen, ih, render_advanceTokens, normalizeAux, if_neg seen]

def TokensWellFormed (anchor : Nat) (tokens : List SkeletonToken) : Prop :=
  (tokenLetters tokens).Nodup ∧ anchor ∉ tokenLetters tokens

theorem closeTokens_wellFormed {anchor : Nat} {tokens : List SkeletonToken}
    (wellFormed : TokensWellFormed anchor tokens) (pending : List Nat) :
    TokensWellFormed anchor (closeTokens tokens pending) := by
  simpa [TokensWellFormed, letters_closeTokens] using wellFormed

theorem advanceTokens_wellFormed {anchor : Nat} {tokens : List SkeletonToken}
    (wellFormed : TokensWellFormed anchor tokens) (pending : List Nat) (letter : Nat) (rest : List Nat)
    (fresh : letter ∉ [anchor, anchor] ++ renderTokens anchor tokens) :
    TokensWellFormed anchor (advanceTokens tokens pending letter rest) := by
  have letterNew : letter ∉ tokenLetters tokens := by
    intro member
    exact fresh (List.mem_append.mpr (Or.inr (tokenLetter_mem_render member)))
  have notAnchor : anchor ≠ letter := by
    intro equal
    subst letter
    exact fresh (by simp)
  have distinct : (tokenLetters tokens ++ [letter]).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨wellFormed.1, by simp, ?_⟩
    intro x inOld y inNew equal
    have yEq : y = letter := by simpa using inNew
    subst y
    subst x
    exact letterNew inOld
  constructor
  · simpa [letters_advanceTokens] using distinct
  · simp [letters_advanceTokens, wellFormed.2, notAnchor]

/-- Distinct fresh letters and anchor exclusion are preserved by every
recursive step, not inferred from the name of the scanner. -/
theorem scanTokens_wellFormed (anchor : Nat) (tokens : List SkeletonToken)
    (pending rest : List Nat) (wellFormed : TokensWellFormed anchor tokens) :
    TokensWellFormed anchor (scanTokens anchor tokens pending rest) := by
  induction rest generalizing tokens pending with
  | nil => exact closeTokens_wellFormed wellFormed pending
  | cons letter rest ih =>
      by_cases seen : letter ∈ [anchor, anchor] ++ renderTokens anchor tokens
      · rw [scanTokens, if_pos seen]
        exact ih tokens (pending ++ [letter]) wellFormed
      · rw [scanTokens, if_neg seen]
        exact ih _ [] (advanceTokens_wellFormed wellFormed pending letter rest seen)

/-- No fresh-letter token can appear unless it was already present or occurs
in the remaining input. This is the disjoint-prefix boundary needed later. -/
theorem scanTokens_letters_subset (anchor : Nat) (tokens : List SkeletonToken)
    (pending rest : List Nat) :
    ∀ x ∈ tokenLetters (scanTokens anchor tokens pending rest),
      x ∈ tokenLetters tokens ∨ x ∈ rest := by
  induction rest generalizing tokens pending with
  | nil =>
      intro x member
      left
      simpa [scanTokens, letters_closeTokens] using member
  | cons letter rest ih =>
      intro x member
      by_cases seen : letter ∈ [anchor, anchor] ++ renderTokens anchor tokens
      · rw [scanTokens, if_pos seen] at member
        rcases ih tokens (pending ++ [letter]) x member with old | later
        · exact Or.inl old
        · exact Or.inr (List.mem_cons_of_mem letter later)
      · rw [scanTokens, if_neg seen] at member
        rcases ih (advanceTokens tokens pending letter rest) [] x member with old | later
        · rw [letters_advanceTokens] at old
          rcases List.mem_append.mp old with previous | current
          · exact Or.inl previous
          · have equal : x = letter := by simpa using current
            exact Or.inr (List.mem_cons.mpr (Or.inl equal))
        · exact Or.inr (List.mem_cons_of_mem letter later)

def skeletonTokens (anchor : Nat) (rest : List Nat) : List SkeletonToken :=
  scanTokens anchor [] [] rest

theorem skeletonTokens_render (anchor : Nat) (rest : List Nat) :
    renderTokens anchor (skeletonTokens anchor rest) = normalizeAux anchor [] [] rest :=
  render_scanTokens anchor [] [] rest

theorem skeletonTokens_wellFormed (anchor : Nat) (rest : List Nat) :
    TokensWellFormed anchor (skeletonTokens anchor rest) :=
  scanTokens_wellFormed anchor [] [] rest (by simp [TokensWellFormed, tokenLetters])

theorem skeletonTokens_letters_subset (anchor : Nat) (rest : List Nat) :
    ∀ x ∈ tokenLetters (skeletonTokens anchor rest), x ∈ rest := by
  intro x member
  have bound := scanTokens_letters_subset anchor [] [] rest x member
  simpa [tokenLetters] using bound

#print axioms render_scanTokens
#print axioms scanTokens_wellFormed
#print axioms scanTokens_letters_subset
#print axioms skeletonTokens_render
#print axioms skeletonTokens_wellFormed

end SemigroupBasis.CoRoots.Order6SporadicSection16
