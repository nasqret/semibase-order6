import SemigroupBasis.Nonfinite
import SemigroupBasis.Nonfinite.GraphParity

namespace SemigroupBasis.Nonfinite.A2One

open SemigroupBasis

/-!
Trahtman's explicit nonfinite-basis sequence for the monoid `A₂¹`.

For `n = extra + 2`, let

`Xₙ = x₁ x₂ ... xₙ` and `Xₙʳ = xₙ ... x₂ x₁`.

The source identity is

`Xₙ y Xₙʳ y Xₙ ≈ Xₙ y Xₙʳ y Xₙ y Xₙʳ y Xₙ`.

The definitions below use variables `0, ..., extra + 1` for the `xᵢ` and
`extra + 2` for `y`.  The terminal criterion is expressed in Trahtman's exact
preimage-isoterm form; Sapir's two-fresh-variable contextualization and the
resulting bounded derivational nonredundancy are proved below.
-/

def forwardBlock : Nat → Word Nat
  | 0 => Word.singleton 0 ++ Word.singleton 1
  | extra + 1 =>
      forwardBlock extra ++ Word.singleton (extra + 2)

def reverseBlock : Nat → Word Nat
  | 0 => Word.singleton 1 ++ Word.singleton 0
  | extra + 1 =>
      Word.singleton (extra + 2) ++ reverseBlock extra

def separator (extra : Nat) : Word Nat :=
  Word.singleton (extra + 2)

def anchor (extra : Nat) : Word Nat :=
  forwardBlock extra ++ separator extra ++ reverseBlock extra ++
    separator extra ++ forwardBlock extra

def extended (extra : Nat) : Word Nat :=
  anchor extra ++ separator extra ++ reverseBlock extra ++
    separator extra ++ forwardBlock extra

def trahtmanIdentity (extra : Nat) : Identity Nat :=
  ⟨anchor extra, extended extra⟩

/-- The member used against identities whose variables have a cover of
length at most `bound`.  Sapir's contextualization may add two fresh
variables, so the preimage word uses at most `bound + 2` variables.  The
Trahtman block therefore has `3 * (bound + 2) + 2` indexed variables. -/
def obstruction (bound : Nat) : Identity Nat :=
  trahtmanIdentity (3 * (bound + 2))

theorem forwardBlock_toList : ∀ extra,
    (forwardBlock extra).toList = List.range (extra + 2)
  | 0 => by decide
  | extra + 1 => by
      rw [forwardBlock, Word.toList_append, forwardBlock_toList extra]
      simp [List.range_succ, Nat.add_assoc]

theorem reverseBlock_toList (extra : Nat) :
    (reverseBlock extra).toList = (List.range (extra + 2)).reverse := by
  induction extra with
  | zero => decide
  | succ extra ih =>
      rw [reverseBlock, Word.toList_append, ih]
      simp [List.range_succ, Nat.add_assoc]

theorem anchor_ne_extended (extra : Nat) :
    anchor extra ≠ extended extra := by
  intro equality
  have lengths := congrArg (fun word => word.toList.length) equality
  simp only [anchor, extended, separator, Word.toList_append,
    List.length_append, Word.toList_singleton, List.length_cons,
    List.length_nil] at lengths
  omega

private theorem bind_append (left right : Word Nat)
    (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution =
      left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp only [Word.toList_bind, Word.toList_append, List.flatMap_append]

private theorem bind_bind (word : Word Nat)
    (first second : Nat → Word Nat) :
    (word.bind first).bind second =
      word.bind (fun x => (first x).bind second) := by
  apply Word.toList_injective
  simp only [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  rw [Word.toList_bind]
  simp

private theorem singleton_bind
    (letter : Nat) (substitution : Nat → Word Nat) :
    (Word.singleton letter).bind substitution = substitution letter :=
  rfl

/-- The variables occurring in a single word have a cover of the stated
length. -/
def WordUsesAtMost (word : Word Nat) (bound : Nat) : Prop :=
  ∃ variables : List Nat,
    variables.length ≤ bound ∧ word.UsesOnly variables

theorem wordUsesAtMost_mono
    {word : Word Nat} {small large : Nat}
    (uses : WordUsesAtMost word small) (bound : small ≤ large) :
    WordUsesAtMost word large := by
  rcases uses with ⟨variables, lengthBound, only⟩
  exact ⟨variables, Nat.le_trans lengthBound bound, only⟩

/-- A word is an isoterm for `G` when it is not one side of any nontrivial
identity valid in `G`. -/
def Isoterm (G : Semigroup S) (word : Word Nat) : Prop :=
  ∀ other,
    (Identity.mk word other).SatisfiedBy G →
    other = word

/-- Trahtman's exact preimage-isoterm statement.

For every variable bound, every word using at most that many variables is an
isoterm whenever a nonerasing substitution maps it to
`Xₙ y Xₙʳ y Xₙ`, with `n = 3 * bound + 2`. -/
def BoundedAnchorPreimageIsoterm (G : Semigroup S) : Prop :=
  ∀ bound (word : Word Nat),
    WordUsesAtMost word bound →
    ∀ substitution,
      word.bind substitution = anchor (3 * bound) →
      Isoterm G word

private def freshAbove : List Nat → Nat
  | [] => 0
  | letter :: rest => max (letter + 1) (freshAbove rest)

private theorem lt_freshAbove_of_mem
    {letter : Nat} {variables : List Nat}
    (member : letter ∈ variables) :
    letter < freshAbove variables := by
  induction variables with
  | nil => simp at member
  | cons first rest ih =>
      simp only [List.mem_cons] at member
      simp only [freshAbove]
      rcases member with rfl | member
      · omega
      · have := ih member
        omega

private theorem freshAbove_not_mem (variables : List Nat) :
    freshAbove variables ∉ variables := by
  intro member
  exact Nat.lt_irrefl _
    (lt_freshAbove_of_mem member)

private theorem freshAbove_succ_not_mem (variables : List Nat) :
    freshAbove variables + 1 ∉ variables := by
  intro member
  have := lt_freshAbove_of_mem member
  omega

private theorem bind_congr_of_usesOnly
    {word : Word Nat} {variables : List Nat}
    (uses : word.UsesOnly variables)
    {first second : Nat → Word Nat}
    (agree :
      ∀ letter, letter ∈ variables →
        first letter = second letter) :
    word.bind first = word.bind second := by
  apply Word.toList_injective
  simp only [Word.toList_bind]
  have flatMapEquality :
      ∀ letters : List Nat,
        (∀ letter, letter ∈ letters → letter ∈ variables) →
        letters.flatMap (fun letter => (first letter).toList) =
          letters.flatMap (fun letter => (second letter).toList) := by
    intro letters contained
    induction letters with
    | nil => rfl
    | cons letter rest ih =>
        simp only [List.flatMap_cons]
        rw [agree letter (contained letter (by simp))]
        exact congrArg
          (List.append (second letter).toList)
          (ih (fun x member =>
            contained x (by simp [member])))
  exact flatMapEquality word.toList uses

private theorem append_usesOnly
    {left right : Word Nat} {variables : List Nat}
    (leftUses : left.UsesOnly variables)
    (rightUses : right.UsesOnly variables) :
    (left ++ right).UsesOnly variables := by
  intro letter member
  rw [Word.toList_append] at member
  rcases List.mem_append.mp member with member | member
  · exact leftUses letter member
  · exact rightUses letter member

private theorem singleton_usesOnly
    (letter : Nat) (variables : List Nat)
    (member : letter ∈ variables) :
    (Word.singleton letter).UsesOnly variables := by
  intro x occurrence
  have equality : x = letter := by
    simpa using occurrence
  simpa [equality] using member

private theorem prepend_valid
    {G : Semigroup S} {left right prefixWord : Word Nat}
    (valid : (Identity.mk left right).SatisfiedBy G) :
    (Identity.mk
      (prefixWord ++ left) (prefixWord ++ right)).SatisfiedBy G := by
  intro valuation
  simp only [Semigroup.eval_append]
  exact congrArg (G.mul (G.eval valuation prefixWord)) (valid valuation)

private theorem append_valid
    {G : Semigroup S} {left right suffix : Word Nat}
    (valid : (Identity.mk left right).SatisfiedBy G) :
    (Identity.mk (left ++ suffix) (right ++ suffix)).SatisfiedBy G := by
  intro valuation
  simp only [Semigroup.eval_append]
  exact congrArg (fun value => G.mul value (G.eval valuation suffix))
    (valid valuation)

private theorem identityUsesAtMost_mono
    {identity : Identity Nat} {small large : Nat}
    (uses : identity.UsesAtMost small) (bound : small ≤ large) :
    identity.UsesAtMost large := by
  rcases uses with ⟨variables, lengthBound, only⟩
  exact ⟨variables, Nat.le_trans lengthBound bound, only⟩

/-- Two words are indistinguishable by the property of becoming `target`
after an arbitrary simultaneous substitution and arbitrary (possibly empty)
left and right contexts.

This is the invariant needed to lift Trahtman's one-step occurrence-order
argument through the reflexive, symmetric, transitive, contextual, and
substitution closures in `Derives`. -/
def ContextuallyEquivalentAt
    (target left right : Word Nat) : Prop :=
  ∀ (pre post : List Nat) (substitution : Nat → Word Nat),
    pre ++ (left.bind substitution).toList ++ post = target.toList ↔
    pre ++ (right.bind substitution).toList ++ post = target.toList

def adjacentPairsList : List Nat → List (Nat × Nat)
  | [] => []
  | first :: rest => Word.adjacentPairsFrom first rest

/-- Marked-digraph equality for possibly empty deletion projections. -/
def SameMarkedDigraphList (left right : List Nat) : Prop :=
  left.head? = right.head? ∧
    left.getLast? = right.getLast? ∧
    (∀ letter, letter ∈ left ↔ letter ∈ right) ∧
    (∀ source target,
      (source, target) ∈ adjacentPairsList left ↔
        (source, target) ∈ adjacentPairsList right)

/-- Every deletion projection of two words has the same marked digraph. -/
def SameDeletionMarkedDigraph (left right : Word Nat) : Prop :=
  ∀ keep,
    SameMarkedDigraphList
      (left.toList.filter keep)
      (right.toList.filter keep)

theorem SameMarkedDigraphList.symm
    {left right : List Nat}
    (same : SameMarkedDigraphList left right) :
    SameMarkedDigraphList right left :=
  ⟨same.1.symm, same.2.1.symm,
    fun letter => (same.2.2.1 letter).symm,
    fun source target => (same.2.2.2 source target).symm⟩

theorem SameDeletionMarkedDigraph.symm
    {left right : Word Nat}
    (same : SameDeletionMarkedDigraph left right) :
    SameDeletionMarkedDigraph right left :=
  fun keep => (same keep).symm

theorem identity_not_usesAtMost_zero (identity : Identity Nat) :
    ¬identity.UsesAtMost 0 := by
  rintro ⟨variables, lengthBound, leftUses, _⟩
  have variablesEmpty : variables = [] := by
    exact List.eq_nil_of_length_eq_zero (by omega)
  have headMember : identity.lhs.head ∈ identity.lhs.toList := by
    simp [Word.toList]
  have := leftUses identity.lhs.head headMember
  simp [variablesEmpty] at this

theorem word_not_usesAtMost_zero (word : Word Nat) :
    ¬WordUsesAtMost word 0 := by
  rintro ⟨variables, lengthBound, uses⟩
  have variablesEmpty : variables = [] := by
    exact List.eq_nil_of_length_eq_zero (by omega)
  have headMember : word.head ∈ word.toList := by
    simp [Word.toList]
  have := uses word.head headMember
  simp [variablesEmpty] at this

private theorem context_direction_of_preimageIsoterm
    {G : Semigroup S}
    (preimage : BoundedAnchorPreimageIsoterm G)
    {bound : Nat} {left right : Word Nat}
    {variables : List Nat}
    (lengthBound : variables.length ≤ bound)
    (leftUses : left.UsesOnly variables)
    (rightUses : right.UsesOnly variables)
    (valid : (Identity.mk left right).SatisfiedBy G)
    (pre post : List Nat) (substitution : Nat → Word Nat)
    (leftAtTarget :
      pre ++ (left.bind substitution).toList ++ post =
        (anchor (3 * (bound + 2))).toList) :
    pre ++ (right.bind substitution).toList ++ post =
      (anchor (3 * (bound + 2))).toList := by
  cases pre with
  | nil =>
      cases post with
      | nil =>
          have leftBound :
              WordUsesAtMost left (bound + 2) :=
            ⟨variables, by omega, leftUses⟩
          have mapped :
              left.bind substitution =
                anchor (3 * (bound + 2)) := by
            apply Word.toList_injective
            simpa using leftAtTarget
          have same :=
            preimage (bound + 2) left leftBound substitution mapped
              right valid
          simpa [same] using leftAtTarget
      | cons postHead postTail =>
          let fresh := freshAbove variables
          let postWord : Word Nat := ⟨postHead, postTail⟩
          let augmented : Nat → Word Nat :=
            fun letter =>
              if letter = fresh then postWord else substitution letter
          have freshNot : fresh ∉ variables := by
            exact freshAbove_not_mem variables
          have leftBind :
              left.bind augmented = left.bind substitution := by
            apply bind_congr_of_usesOnly leftUses
            intro letter member
            have ne : letter ≠ fresh := by
              intro equality
              apply freshNot
              simpa [equality] using member
            simp [augmented, ne]
          have rightBind :
              right.bind augmented = right.bind substitution := by
            apply bind_congr_of_usesOnly rightUses
            intro letter member
            have ne : letter ≠ fresh := by
              intro equality
              apply freshNot
              simpa [equality] using member
            simp [augmented, ne]
          have leftAugmented :
              left.UsesOnly (fresh :: variables) :=
            leftUses.mono
              (fun letter member => by simp [member])
          have rightAugmented :
              right.UsesOnly (fresh :: variables) :=
            rightUses.mono
              (fun letter member => by simp [member])
          have freshUses :
              (Word.singleton fresh).UsesOnly (fresh :: variables) :=
            singleton_usesOnly fresh (fresh :: variables) (by simp)
          have sourceBound :
              WordUsesAtMost
                (left ++ Word.singleton fresh) (bound + 2) :=
            ⟨fresh :: variables, by simp; omega,
              append_usesOnly leftAugmented freshUses⟩
          have sourceMapped :
              (left ++ Word.singleton fresh).bind augmented =
                anchor (3 * (bound + 2)) := by
            rw [bind_append, leftBind, singleton_bind]
            simp only [augmented, if_pos]
            apply Word.toList_injective
            simpa [postWord] using leftAtTarget
          have wrappedValid :
              (Identity.mk
                (left ++ Word.singleton fresh)
                (right ++ Word.singleton fresh)).SatisfiedBy G :=
            append_valid valid
          have same :=
            preimage (bound + 2)
              (left ++ Word.singleton fresh) sourceBound
              augmented sourceMapped
              (right ++ Word.singleton fresh) wrappedValid
          have mappedSame :=
            congrArg (fun word => (word.bind augmented).toList) same
          have finalMap :=
            mappedSame.trans (congrArg Word.toList sourceMapped)
          change
            ((right ++ Word.singleton fresh).bind augmented).toList =
              (anchor (3 * (bound + 2))).toList at finalMap
          rw [bind_append, rightBind, singleton_bind] at finalMap
          simp only [augmented, if_pos] at finalMap
          simpa [postWord] using finalMap
  | cons preHead preTail =>
      cases post with
      | nil =>
          let fresh := freshAbove variables
          let preWord : Word Nat := ⟨preHead, preTail⟩
          let augmented : Nat → Word Nat :=
            fun letter =>
              if letter = fresh then preWord else substitution letter
          have freshNot : fresh ∉ variables := by
            exact freshAbove_not_mem variables
          have leftBind :
              left.bind augmented = left.bind substitution := by
            apply bind_congr_of_usesOnly leftUses
            intro letter member
            have ne : letter ≠ fresh := by
              intro equality
              apply freshNot
              simpa [equality] using member
            simp [augmented, ne]
          have rightBind :
              right.bind augmented = right.bind substitution := by
            apply bind_congr_of_usesOnly rightUses
            intro letter member
            have ne : letter ≠ fresh := by
              intro equality
              apply freshNot
              simpa [equality] using member
            simp [augmented, ne]
          have leftAugmented :
              left.UsesOnly (fresh :: variables) :=
            leftUses.mono
              (fun letter member => by simp [member])
          have rightAugmented :
              right.UsesOnly (fresh :: variables) :=
            rightUses.mono
              (fun letter member => by simp [member])
          have freshUses :
              (Word.singleton fresh).UsesOnly (fresh :: variables) :=
            singleton_usesOnly fresh (fresh :: variables) (by simp)
          have sourceBound :
              WordUsesAtMost
                (Word.singleton fresh ++ left) (bound + 2) :=
            ⟨fresh :: variables, by simp; omega,
              append_usesOnly freshUses leftAugmented⟩
          have sourceMapped :
              (Word.singleton fresh ++ left).bind augmented =
                anchor (3 * (bound + 2)) := by
            rw [bind_append, singleton_bind, leftBind]
            simp only [augmented, if_pos]
            apply Word.toList_injective
            simpa [preWord] using leftAtTarget
          have wrappedValid :
              (Identity.mk
                (Word.singleton fresh ++ left)
                (Word.singleton fresh ++ right)).SatisfiedBy G :=
            prepend_valid valid
          have same :=
            preimage (bound + 2)
              (Word.singleton fresh ++ left) sourceBound
              augmented sourceMapped
              (Word.singleton fresh ++ right) wrappedValid
          have mappedSame :=
            congrArg (fun word => (word.bind augmented).toList) same
          have finalMap :=
            mappedSame.trans (congrArg Word.toList sourceMapped)
          change
            ((Word.singleton fresh ++ right).bind augmented).toList =
              (anchor (3 * (bound + 2))).toList at finalMap
          rw [bind_append, singleton_bind, rightBind] at finalMap
          simp only [augmented, if_pos] at finalMap
          simpa [preWord] using finalMap
      | cons postHead postTail =>
          let leftFresh := freshAbove variables
          let rightFresh := leftFresh + 1
          let preWord : Word Nat := ⟨preHead, preTail⟩
          let postWord : Word Nat := ⟨postHead, postTail⟩
          let augmented : Nat → Word Nat :=
            fun letter =>
              if letter = leftFresh then preWord
              else if letter = rightFresh then postWord
              else substitution letter
          have leftFreshNot : leftFresh ∉ variables := by
            exact freshAbove_not_mem variables
          have rightFreshNot : rightFresh ∉ variables := by
            exact freshAbove_succ_not_mem variables
          have freshNe : rightFresh ≠ leftFresh := by
            simp [rightFresh]
          have leftBind :
              left.bind augmented = left.bind substitution := by
            apply bind_congr_of_usesOnly leftUses
            intro letter member
            have leftNe : letter ≠ leftFresh := by
              intro equality
              apply leftFreshNot
              simpa [equality] using member
            have rightNe : letter ≠ rightFresh := by
              intro equality
              apply rightFreshNot
              simpa [equality] using member
            simp [augmented, leftNe, rightNe]
          have rightBind :
              right.bind augmented = right.bind substitution := by
            apply bind_congr_of_usesOnly rightUses
            intro letter member
            have leftNe : letter ≠ leftFresh := by
              intro equality
              apply leftFreshNot
              simpa [equality] using member
            have rightNe : letter ≠ rightFresh := by
              intro equality
              apply rightFreshNot
              simpa [equality] using member
            simp [augmented, leftNe, rightNe]
          have leftAugmented :
              left.UsesOnly (leftFresh :: rightFresh :: variables) :=
            leftUses.mono
              (fun letter member => by simp [member])
          have rightAugmented :
              right.UsesOnly (leftFresh :: rightFresh :: variables) :=
            rightUses.mono
              (fun letter member => by simp [member])
          have leftFreshUses :
              (Word.singleton leftFresh).UsesOnly
                (leftFresh :: rightFresh :: variables) :=
            singleton_usesOnly _ _ (by simp)
          have rightFreshUses :
              (Word.singleton rightFresh).UsesOnly
                (leftFresh :: rightFresh :: variables) :=
            singleton_usesOnly _ _ (by simp)
          have sourceBound :
              WordUsesAtMost
                ((Word.singleton leftFresh ++ left) ++
                  Word.singleton rightFresh) (bound + 2) :=
            ⟨leftFresh :: rightFresh :: variables, by simp; omega,
              append_usesOnly
                (append_usesOnly leftFreshUses leftAugmented)
                rightFreshUses⟩
          have sourceMapped :
              ((Word.singleton leftFresh ++ left) ++
                  Word.singleton rightFresh).bind augmented =
                anchor (3 * (bound + 2)) := by
            rw [bind_append, bind_append, singleton_bind,
              singleton_bind, leftBind]
            simp [augmented, freshNe]
            apply Word.toList_injective
            simpa [preWord, postWord, List.append_assoc] using
              leftAtTarget
          have wrappedValid :
              (Identity.mk
                ((Word.singleton leftFresh ++ left) ++
                  Word.singleton rightFresh)
                ((Word.singleton leftFresh ++ right) ++
                  Word.singleton rightFresh)).SatisfiedBy G :=
            append_valid (prepend_valid valid)
          have same :=
            preimage (bound + 2)
              ((Word.singleton leftFresh ++ left) ++
                Word.singleton rightFresh)
              sourceBound augmented sourceMapped
              ((Word.singleton leftFresh ++ right) ++
                Word.singleton rightFresh)
              wrappedValid
          have mappedSame :=
            congrArg (fun word => (word.bind augmented).toList) same
          have finalMap :=
            mappedSame.trans (congrArg Word.toList sourceMapped)
          change
            (((Word.singleton leftFresh ++ right) ++
                Word.singleton rightFresh).bind augmented).toList =
              (anchor (3 * (bound + 2))).toList at finalMap
          rw [bind_append, bind_append, singleton_bind,
            singleton_bind, rightBind] at finalMap
          simp [augmented, freshNe] at finalMap
          simpa [preWord, postWord, List.append_assoc] using finalMap

/-- Sapir's `t₁ u t₂` argument: the preimage-isoterm criterion implies that
every valid identity with at most `bound` variables preserves the larger
Trahtman anchor under arbitrary contextual substitution. -/
theorem contextuallyEquivalentAt_of_preimageIsoterm
    {G : Semigroup S}
    (preimage : BoundedAnchorPreimageIsoterm G)
    {bound : Nat} {identity : Identity Nat}
    (valid : identity.SatisfiedBy G)
    (uses : identity.UsesAtMost bound) :
    ContextuallyEquivalentAt
      (anchor (3 * (bound + 2)))
      identity.lhs identity.rhs := by
  rcases uses with
    ⟨variables, lengthBound, leftUses, rightUses⟩
  intro pre post substitution
  constructor
  · exact context_direction_of_preimageIsoterm
      preimage lengthBound leftUses rightUses valid
      pre post substitution
  · exact context_direction_of_preimageIsoterm
      preimage lengthBound rightUses leftUses
      (fun valuation => (valid valuation).symm)
      pre post substitution

/-- The exact pure word-combinatorics boundary remaining after the concrete
`A₂¹` table has supplied every deletion-marked-digraph invariant.

The statement still remembers that the rewrite arises from one identity
using at most `bound` variables.  The semigroup validity hypothesis has been
removed: the only semantic information retained is deletion-graph equality,
already forced by the table. -/
def BoundedDeletionGraphAnchorRigidity : Prop :=
  ∀ bound (identity : Identity Nat),
    identity.UsesAtMost bound →
    SameDeletionMarkedDigraph identity.lhs identity.rhs →
    ContextuallyEquivalentAt
      (anchor (3 * bound)) identity.lhs identity.rhs

/-- Pure combinatorial form of Trahtman's preimage theorem.

If a word on at most `bound` variables maps to the anchor with
`n = 3 * bound + 2`, then its complete family of deletion marked digraphs
determines the word itself. -/
def BoundedDeletionGraphPreimageRigidity : Prop :=
  ∀ bound (word : Word Nat),
    WordUsesAtMost word bound →
    ∀ substitution,
      word.bind substitution = anchor (3 * bound) →
      ∀ other,
        SameDeletionMarkedDigraph word other →
        other = word

/-- The zero-variable instance of preimage rigidity is vacuous because free
semigroup words are nonempty. -/
theorem deletionGraphPreimageRigidity_bound_zero
    (word : Word Nat) :
    WordUsesAtMost word 0 →
      ∀ substitution,
        word.bind substitution = anchor 0 →
        ∀ other,
          SameDeletionMarkedDigraph word other →
          other = word := by
  intro uses
  exact False.elim (word_not_usesAtMost_zero word uses)

/-- The zero-variable case is impossible for nonempty semigroup words. -/
theorem deletionGraphAnchorRigidity_bound_zero
    (identity : Identity Nat) :
    identity.UsesAtMost 0 →
      SameDeletionMarkedDigraph identity.lhs identity.rhs →
      ContextuallyEquivalentAt (anchor 0) identity.lhs identity.rhs := by
  intro uses
  exact False.elim (identity_not_usesAtMost_zero identity uses)

namespace ContextuallyEquivalentAt

theorem refl (target word : Word Nat) :
    ContextuallyEquivalentAt target word word := by
  intro pre post substitution
  rfl

theorem symm {target left right : Word Nat}
    (equivalent : ContextuallyEquivalentAt target left right) :
    ContextuallyEquivalentAt target right left := by
  intro pre post substitution
  exact (equivalent pre post substitution).symm

theorem trans {target first second third : Word Nat}
    (firstSecond : ContextuallyEquivalentAt target first second)
    (secondThird : ContextuallyEquivalentAt target second third) :
    ContextuallyEquivalentAt target first third := by
  intro pre post substitution
  exact
    (firstSecond pre post substitution).trans
      (secondThird pre post substitution)

theorem prepend (target prefixWord : Word Nat)
    {left right : Word Nat}
    (equivalent : ContextuallyEquivalentAt target left right) :
    ContextuallyEquivalentAt target
      (prefixWord ++ left) (prefixWord ++ right) := by
  intro pre post substitution
  rw [bind_append, bind_append, Word.toList_append, Word.toList_append]
  simpa only [List.append_assoc] using
    equivalent
      (pre ++ (prefixWord.bind substitution).toList)
      post substitution

theorem appendRight (target suffixWord : Word Nat)
    {left right : Word Nat}
    (equivalent : ContextuallyEquivalentAt target left right) :
    ContextuallyEquivalentAt target
      (left ++ suffixWord) (right ++ suffixWord) := by
  intro pre post substitution
  rw [bind_append, bind_append, Word.toList_append, Word.toList_append]
  simpa only [List.append_assoc] using
    equivalent pre
      ((suffixWord.bind substitution).toList ++ post)
      substitution

theorem subst (target : Word Nat) {left right : Word Nat}
    (equivalent : ContextuallyEquivalentAt target left right)
    (first : Nat → Word Nat) :
    ContextuallyEquivalentAt target
      (left.bind first) (right.bind first) := by
  intro pre post second
  rw [bind_bind, bind_bind]
  exact equivalent pre post
    (fun x => (first x).bind second)

end ContextuallyEquivalentAt

/-- The closure rules of equational logic preserve contextual equivalence at
a fixed target as soon as every basis identity preserves it. -/
theorem contextuallyEquivalentAt_of_derives
    {basis : List (Identity Nat)} {left right target : Word Nat}
    (basisRigid :
      ∀ identity, identity ∈ basis →
        ContextuallyEquivalentAt target identity.lhs identity.rhs)
    (derivation : Derives basis left right) :
    ContextuallyEquivalentAt target left right := by
  induction derivation with
  | fromBasis membership => exact basisRigid _ membership
  | refl word => exact ContextuallyEquivalentAt.refl target word
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | prepend prefixWord _ ih =>
      exact ih.prepend target prefixWord
  | appendRight _ suffixWord ih =>
      exact ih.appendRight target suffixWord
  | subst _ substitution ih =>
      exact ih.subst target substitution

/-- The exact remaining word-combinatorics statement from Trahtman's proof.

After adding at most two fresh context variables, every valid identity using
at most `bound` variables preserves the word with
`n = 3 * (bound + 2) + 2`

`Xₙ y Xₙʳ y Xₙ`

under every nonempty-word substitution and every possibly empty surrounding
context.  This is precisely the one-step occurrence-order/isoterm assertion;
all closure under equational derivations is proved below.
-/
def TrahtmanAnchorRigidity (G : Semigroup S) : Prop :=
  ∀ bound (identity : Identity Nat),
    identity.SatisfiedBy G →
    identity.UsesAtMost bound →
    ContextuallyEquivalentAt
      (anchor (3 * (bound + 2))) identity.lhs identity.rhs

/-- A deletion-graph invariant for valid identities and pure anchor rigidity
imply the contextual formulation used by Trahtman's criterion. -/
theorem trahtmanAnchorRigidity_of_deletionGraphAnchorRigidity
    {G : Semigroup S}
    (invariant :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy G →
          SameDeletionMarkedDigraph identity.lhs identity.rhs)
    (rigid : BoundedDeletionGraphAnchorRigidity) :
    TrahtmanAnchorRigidity G := by
  intro bound identity valid uses
  exact rigid (bound + 2) identity
    (identityUsesAtMost_mono uses (by omega))
    (invariant identity valid)

/-- Exact derivational nonredundancy required from Trahtman's infinite-word
argument.  Every sound basis with at most `bound` variables per identity
fails to derive the `3 * (bound + 2) + 2` indexed-variable member of the
source family. -/
def BoundedTrahtmanUnderivability (G : Semigroup S) : Prop :=
  ∀ bound basis,
    Models G basis →
    BasisUsesAtMost basis bound →
    ¬Derives basis (obstruction bound).lhs (obstruction bound).rhs

/-- The exact preimage-isoterm formulation implies the one-step contextual
rigidity formulation used by the derivation closure. -/
theorem trahtmanAnchorRigidity_of_preimageIsoterm
    {G : Semigroup S}
    (preimage : BoundedAnchorPreimageIsoterm G) :
    TrahtmanAnchorRigidity G := by
  intro bound identity valid uses
  exact contextuallyEquivalentAt_of_preimageIsoterm
    preimage valid uses

/-- Trahtman's one-step occurrence-order statement implies the exact bounded
underivability proposition.  In particular, no additional assumption about
finite bases or arbitrary derivation chains remains. -/
theorem boundedTrahtmanUnderivability_of_anchorRigidity
    {G : Semigroup S}
    (rigid : TrahtmanAnchorRigidity G) :
    BoundedTrahtmanUnderivability G := by
  intro bound basis models bounded derivation
  have derivationRigid :
      ContextuallyEquivalentAt
        (anchor (3 * (bound + 2)))
        (obstruction bound).lhs
        (obstruction bound).rhs :=
    contextuallyEquivalentAt_of_derives
      (fun identity membership =>
        rigid bound identity
          (models identity membership)
          (bounded identity membership))
      derivation
  have leftAtTarget :
      ([] : List Nat) ++
          ((obstruction bound).lhs.bind Word.singleton).toList ++ [] =
        (anchor (3 * (bound + 2))).toList := by
    simp [obstruction, trahtmanIdentity, bind_singleton]
  have rightAtTarget :=
    (derivationRigid [] [] Word.singleton).mp leftAtTarget
  have wordEquality :
      extended (3 * (bound + 2)) =
        anchor (3 * (bound + 2)) := by
    apply Word.toList_injective
    simpa [obstruction, trahtmanIdentity, bind_singleton] using
      rightAtTarget
  exact anchor_ne_extended (3 * (bound + 2)) wordEquality.symm

/-- Sapir's preimage-isoterm criterion gives bounded underivability with all
fresh-context bookkeeping discharged in Lean. -/
theorem boundedTrahtmanUnderivability_of_preimageIsoterm
    {G : Semigroup S}
    (preimage : BoundedAnchorPreimageIsoterm G) :
    BoundedTrahtmanUnderivability G :=
  boundedTrahtmanUnderivability_of_anchorRigidity
    (trahtmanAnchorRigidity_of_preimageIsoterm preimage)

/-- Once validity of the explicit identity sequence and its bounded
nonredundancy are known, all remaining finite-basis bookkeeping is internal
to Lean. -/
theorem nonfinitelyBased_of_trahtman
    {G : Semigroup S}
    (valid : ∀ extra, (trahtmanIdentity extra).SatisfiedBy G)
    (underivable : BoundedTrahtmanUnderivability G) :
    NonfinitelyBased G := by
  apply nonfinitelyBased_of_variable_bound_obstructions obstruction
  · intro bound
    exact valid (3 * (bound + 2))
  · exact underivable

/-- Version of the criterion whose sole external input is Trahtman's exact
one-step occurrence-order statement. -/
theorem nonfinitelyBased_of_anchorRigidity
    {G : Semigroup S}
    (valid : ∀ extra, (trahtmanIdentity extra).SatisfiedBy G)
    (rigid : TrahtmanAnchorRigidity G) :
    NonfinitelyBased G :=
  nonfinitelyBased_of_trahtman valid
    (boundedTrahtmanUnderivability_of_anchorRigidity rigid)

/-- Exact Corollary-style entry point using preimage isoterms rather than a
contextual anchor predicate. -/
theorem nonfinitelyBased_of_preimageIsoterm
    {G : Semigroup S}
    (valid : ∀ extra, (trahtmanIdentity extra).SatisfiedBy G)
    (preimage : BoundedAnchorPreimageIsoterm G) :
    NonfinitelyBased G :=
  nonfinitelyBased_of_trahtman valid
    (boundedTrahtmanUnderivability_of_preimageIsoterm preimage)

end SemigroupBasis.Nonfinite.A2One
