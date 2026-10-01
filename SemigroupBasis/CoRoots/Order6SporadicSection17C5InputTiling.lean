import SemigroupBasis.CoRoots.Order6SporadicSection17C5CubeOnly

/-! Computable arbitrary-input tiling. All tags refer to the ORIGINAL word.
Remaining globally restricted markers retain their entire adjacent pair;
this invariant justifies consuming two positions in the square branch. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
open SemigroupBasis

inductive CubicToken where
  | simple (marker : Nat)
  | power (tile : PowerTile)
  deriving DecidableEq, Repr

def cubicTokenWord : CubicToken → List Nat
  | .simple x => [x]
  | .power tile => powerTileWord tile

def cubicTokenLabel : CubicToken → Nat
  | .simple x => x
  | .power (.square x) => x
  | .power (.cube x) => x

def CubicTokenValid (original : List Nat) : CubicToken → Prop
  | .simple x => original.count x = 1
  | .power (.square x) => Restricted x original
  | .power (.cube x) => Unrestricted x original

def cubicTokenRender (tokens : List CubicToken) : List Nat :=
  tokens.flatMap cubicTokenWord

theorem cubicTokenRender_cons (token : CubicToken) (rest : List CubicToken) :
    cubicTokenRender (token :: rest) = cubicTokenWord token ++ cubicTokenRender rest := rfl

theorem cubicTokenRender_append (left right : List CubicToken) :
    cubicTokenRender (left ++ right) = cubicTokenRender left ++ cubicTokenRender right :=
  List.flatMap_append

theorem cubicTokenWord_nonempty (token : CubicToken) : cubicTokenWord token ≠ [] := by
  cases token with
  | simple x => simp [cubicTokenWord]
  | power tile => cases tile <;> simp [cubicTokenWord,powerTileWord]

theorem cubicTokenWord_mem (token : CubicToken) (x : Nat) :
    x ∈ cubicTokenWord token ↔ x = cubicTokenLabel token := by
  cases token with
  | simple y => simp [cubicTokenWord,cubicTokenLabel]
  | power tile => cases tile <;> simp [cubicTokenWord,cubicTokenLabel,powerTileWord]

theorem cubicTokenValid_member {original : List Nat} {token : CubicToken}
    (valid : CubicTokenValid original token) : cubicTokenLabel token ∈ original := by
  cases token with
  | simple x =>
      change original.count x = 1 at valid
      change x ∈ original
      by_cases present : x ∈ original
      · exact present
      · have zero := List.count_eq_zero.mpr present
        omega
  | power tile =>
      cases tile with
      | square x =>
          have two := restricted_count_two x original valid
          change x ∈ original
          by_cases present : x ∈ original
          · exact present
          · have zero := List.count_eq_zero.mpr present
            omega
      | cube x => exact valid.1

def inputTokens (original : List Nat) : List Nat → List CubicToken
  | [] => []
  | x :: xs =>
      if unrestrictedMask original x = true then
        .power (.cube x) :: inputTokens original xs
      else if original.count x = 1 then
        .simple x :: inputTokens original xs
      else match xs with
        | [] => [.simple x]
        | _ :: rest => .power (.square x) :: inputTokens original rest

theorem inputTokens_nil (original : List Nat) : inputTokens original [] = [] := by
  rw [inputTokens.eq_def]

theorem inputTokens_cons (original : List Nat) (x : Nat) (xs : List Nat) :
    inputTokens original (x :: xs) =
      if unrestrictedMask original x = true then
        .power (.cube x) :: inputTokens original xs
      else if original.count x = 1 then
        .simple x :: inputTokens original xs
      else match xs with
        | [] => [.simple x]
        | _ :: rest => .power (.square x) :: inputTokens original rest := by
  rw [inputTokens.eq_def]

theorem restricted_tail_stable (original : List Nat) (x : Nat) (xs : List Nat)
    (preserved : ∀ y ∈ x :: xs, Restricted y original → Restricted y (x :: xs))
    (notRestricted : ¬ Restricted x original) :
    ∀ y ∈ xs, Restricted y original → Restricted y xs := by
  intro y member restricted
  have different : x ≠ y := by
    intro equal
    subst y
    exact notRestricted restricted
  exact (restricted_cons_ne y x xs different).mp
    (preserved y (List.mem_cons_of_mem x member) restricted)

theorem inputTokens_spec (original remaining : List Nat)
    (included : ∀ x ∈ remaining, x ∈ original)
    (preserved : ∀ x ∈ remaining, Restricted x original → Restricted x remaining) :
    (∀ token ∈ inputTokens original remaining, CubicTokenValid original token) ∧
    cubicTokenRender (inputTokens original remaining) =
      remaining.flatMap (cubeTile (unrestrictedMarkers original)) := by
  cases remaining with
  | nil =>
      constructor
      · intro token member; cases member
      · rfl
  | cons x xs =>
      have tailIncluded : ∀ y ∈ xs, y ∈ original :=
        fun y member => included y (List.mem_cons_of_mem x member)
      by_cases unrestricted : Unrestricted x original
      · have mask : unrestrictedMask original x = true :=
          (unrestrictedMask_true original x).mpr unrestricted
        have tailPreserved := restricted_tail_stable original x xs preserved unrestricted.2.2
        have tail := inputTokens_spec original xs tailIncluded tailPreserved
        constructor
        · intro token member
          have members : token = .power (.cube x) ∨ token ∈ inputTokens original xs := by
            simpa only [inputTokens_cons,if_pos mask,List.mem_cons] using member
          rcases members with rfl | found
          · exact unrestricted
          · exact tail.1 token found
        · rw [inputTokens_cons,if_pos mask,cubicTokenRender_cons]
          change [x,x,x] ++ cubicTokenRender (inputTokens original xs) =
            cubeTile (unrestrictedMarkers original) x ++ xs.flatMap (cubeTile (unrestrictedMarkers original))
          rw [tail.2,cubeTile_unrestricted original x unrestricted]
      · have mask : unrestrictedMask original x ≠ true :=
          fun checked => unrestricted ((unrestrictedMask_true original x).mp checked)
        by_cases simple : original.count x = 1
        · have notRestricted : ¬ Restricted x original := by
            intro restricted
            have two := restricted_count_two x original restricted
            omega
          have tailPreserved := restricted_tail_stable original x xs preserved notRestricted
          have tail := inputTokens_spec original xs tailIncluded tailPreserved
          constructor
          · intro token member
            have members : token = .simple x ∨ token ∈ inputTokens original xs := by
              simpa only [inputTokens_cons,if_neg mask,if_pos simple,List.mem_cons] using member
            rcases members with rfl | found
            · exact simple
            · exact tail.1 token found
          · rw [inputTokens_cons,if_neg mask,if_pos simple,cubicTokenRender_cons]
            change [x] ++ cubicTokenRender (inputTokens original xs) =
              cubeTile (unrestrictedMarkers original) x ++ xs.flatMap (cubeTile (unrestrictedMarkers original))
            rw [tail.2,cubeTile_simple original x simple]
        · have restricted : Restricted x original := by
            by_cases found : Restricted x original
            · exact found
            · exact False.elim (unrestricted ⟨included x List.mem_cons_self,simple,found⟩)
          have remainingRestricted := preserved x List.mem_cons_self restricted
          rcases (restricted_cons_same x xs).mp remainingRestricted with ⟨rest,rfl,absent⟩
          have restIncluded : ∀ y ∈ rest, y ∈ original := by
            intro y member
            exact included y (List.mem_cons_of_mem x (List.mem_cons_of_mem x member))
          have restPreserved : ∀ y ∈ rest, Restricted y original → Restricted y rest := by
            intro y member originalRestricted
            have different : x ≠ y := by
              intro equal
              subst y
              exact absent member
            have whole := preserved y (List.mem_cons_of_mem x (List.mem_cons_of_mem x member)) originalRestricted
            exact (restricted_cons_ne y x rest different).mp
              ((restricted_cons_ne y x (x :: rest) different).mp whole)
          have tail := inputTokens_spec original rest restIncluded restPreserved
          constructor
          · intro token member
            have members : token = .power (.square x) ∨ token ∈ inputTokens original rest := by
              simpa only [inputTokens_cons,if_neg mask,if_neg simple,List.mem_cons] using member
            rcases members with rfl | found
            · exact restricted
            · exact tail.1 token found
          · rw [inputTokens_cons,if_neg mask,if_neg simple,cubicTokenRender_cons]
            change [x,x] ++ cubicTokenRender (inputTokens original rest) =
              cubeTile (unrestrictedMarkers original) x ++
                (cubeTile (unrestrictedMarkers original) x ++ rest.flatMap (cubeTile (unrestrictedMarkers original)))
            rw [tail.2,cubeTile_restricted original x restricted]
            rfl
termination_by remaining.length
decreasing_by
  all_goals
    simp_wf
    simp_all only [List.length_cons] <;> omega

theorem inputTokens_valid (original : List Nat) :
    ∀ token ∈ inputTokens original original, CubicTokenValid original token :=
  (inputTokens_spec original original (fun _ member => member)
    (fun _ _ restricted => restricted)).1

theorem inputTokens_render (original : List Nat) :
    cubicTokenRender (inputTokens original original) = cubicForm original :=
  (inputTokens_spec original original (fun _ member => member)
    (fun _ _ restricted => restricted)).2

theorem inputTokens_derives (original : List Nat) :
    ListDerives original (cubicTokenRender (inputTokens original original)) := by
  rw [inputTokens_render]
  exact cubicForm_derives original

theorem inputTokens_noCube (original : List Nat)
    (none : ∀ x, ¬ Unrestricted x original) (x : Nat) :
    CubicToken.power (.cube x) ∉ inputTokens original original := by
  intro member
  exact none x (inputTokens_valid original (.power (.cube x)) member)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.cubicTokenRender_cons
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.cubicTokenRender_append
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.cubicTokenWord_nonempty
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.cubicTokenWord_mem
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.cubicTokenValid_member
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.inputTokens_nil
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.inputTokens_cons
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.restricted_tail_stable
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.inputTokens_spec
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.inputTokens_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.inputTokens_render
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.inputTokens_derives
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.inputTokens_noCube

end SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
