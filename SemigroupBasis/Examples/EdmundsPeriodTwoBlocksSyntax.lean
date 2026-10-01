import SemigroupBasis.Examples.CommutativePeriodTwoFromTwo

namespace SemigroupBasis.Examples

open SemigroupBasis

def edmundsPeriodTwoBlocksXX : Word Nat := ⟨0, [0]⟩
def edmundsPeriodTwoBlocksXXXX : Word Nat := ⟨0, [0, 0, 0]⟩
def edmundsPeriodTwoBlocksXYX : Word Nat := ⟨0, [1, 0]⟩
def edmundsPeriodTwoBlocksXXY : Word Nat := ⟨0, [0, 1]⟩
def edmundsPeriodTwoBlocksYYXX : Word Nat := ⟨1, [1, 0, 0]⟩
def edmundsPeriodTwoBlocksXXYY : Word Nat := ⟨0, [0, 1, 1]⟩

def edmundsPeriodTwoBlocksPowerLaw : Identity Nat :=
  ⟨edmundsPeriodTwoBlocksXX, edmundsPeriodTwoBlocksXXXX⟩

def edmundsPeriodTwoBlocksGatherLaw : Identity Nat :=
  ⟨edmundsPeriodTwoBlocksXYX, edmundsPeriodTwoBlocksXXY⟩

def edmundsPeriodTwoBlocksCommutationLaw : Identity Nat :=
  ⟨edmundsPeriodTwoBlocksYYXX, edmundsPeriodTwoBlocksXXYY⟩

/-- The exact opposite-oriented Edmunds basis
`xx = xxxx`, `xyx = xxy`, `yyxx = xxyy`. -/
def edmundsPeriodTwoBlocksBasis : List (Identity Nat) :=
  [edmundsPeriodTwoBlocksPowerLaw, edmundsPeriodTwoBlocksGatherLaw,
    edmundsPeriodTwoBlocksCommutationLaw]

private def edmundsPeriodTwoBlocksInstantiate
    (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

/-- Four consecutive copies of a nonempty block contract to two copies. -/
theorem edmundsPeriodTwoBlocksDerivesFourToTwo (u : Word Nat) :
    Derives edmundsPeriodTwoBlocksBasis
      (((u ++ u) ++ u) ++ u) (u ++ u) := by
  have hbase :
      Derives edmundsPeriodTwoBlocksBasis
        edmundsPeriodTwoBlocksXXXX edmundsPeriodTwoBlocksXX :=
    Derives.symm <|
      Derives.fromBasis (e := edmundsPeriodTwoBlocksPowerLaw) <|
        List.Mem.head _
  have h :=
    Derives.subst hbase (edmundsPeriodTwoBlocksInstantiate u u)
  simpa [edmundsPeriodTwoBlocksBasis,
    edmundsPeriodTwoBlocksPowerLaw, edmundsPeriodTwoBlocksXXXX,
    edmundsPeriodTwoBlocksXX, edmundsPeriodTwoBlocksInstantiate,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using h

/-- Gather a later copy of a block next to its first copy. -/
theorem edmundsPeriodTwoBlocksDerivesGather (u v : Word Nat) :
    Derives edmundsPeriodTwoBlocksBasis
      ((u ++ v) ++ u) ((u ++ u) ++ v) := by
  have hbase :
      Derives edmundsPeriodTwoBlocksBasis
        edmundsPeriodTwoBlocksXYX edmundsPeriodTwoBlocksXXY :=
    Derives.fromBasis (e := edmundsPeriodTwoBlocksGatherLaw) <|
      List.Mem.tail _ (List.Mem.head _)
  have h :=
    Derives.subst hbase (edmundsPeriodTwoBlocksInstantiate u v)
  simpa [edmundsPeriodTwoBlocksBasis,
    edmundsPeriodTwoBlocksGatherLaw, edmundsPeriodTwoBlocksXYX,
    edmundsPeriodTwoBlocksXXY, edmundsPeriodTwoBlocksInstantiate,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using h

/-- Two double blocks commute. -/
theorem edmundsPeriodTwoBlocksDerivesDoubleDoubleCommutation
    (u v : Word Nat) :
    Derives edmundsPeriodTwoBlocksBasis
      ((u ++ u) ++ (v ++ v)) ((v ++ v) ++ (u ++ u)) := by
  have hbase :
      Derives edmundsPeriodTwoBlocksBasis
        edmundsPeriodTwoBlocksXXYY edmundsPeriodTwoBlocksYYXX :=
    Derives.symm <|
      Derives.fromBasis
        (e := edmundsPeriodTwoBlocksCommutationLaw) <|
          List.Mem.tail _ <|
            List.Mem.tail _ (List.Mem.head _)
  have h :=
    Derives.subst hbase (edmundsPeriodTwoBlocksInstantiate u v)
  simpa [edmundsPeriodTwoBlocksBasis,
    edmundsPeriodTwoBlocksCommutationLaw,
    edmundsPeriodTwoBlocksXXYY, edmundsPeriodTwoBlocksYYXX,
    edmundsPeriodTwoBlocksInstantiate, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using h

/-- A double block commutes past a triple block. -/
theorem edmundsPeriodTwoBlocksDerivesDoubleTripleCommutation
    (u v : Word Nat) :
    Derives edmundsPeriodTwoBlocksBasis
      ((u ++ u) ++ ((v ++ v) ++ v))
      (((v ++ v) ++ v) ++ (u ++ u)) := by
  have first :=
    Derives.appendRight
      (edmundsPeriodTwoBlocksDerivesDoubleDoubleCommutation u v) v
  have gathered :=
    Derives.prepend v <|
      edmundsPeriodTwoBlocksDerivesGather v (u ++ u)
  exact Derives.trans
    (by simpa [Word.append_assoc] using first)
    (by simpa [Word.append_assoc] using gathered)

/-- A triple block commutes past a double block. -/
theorem edmundsPeriodTwoBlocksDerivesTripleDoubleCommutation
    (u v : Word Nat) :
    Derives edmundsPeriodTwoBlocksBasis
      (((u ++ u) ++ u) ++ (v ++ v))
      ((v ++ v) ++ ((u ++ u) ++ u)) := by
  have first :=
    Derives.prepend u <|
      edmundsPeriodTwoBlocksDerivesDoubleDoubleCommutation u v
  have gathered :=
    Derives.appendRight
      (edmundsPeriodTwoBlocksDerivesGather u (v ++ v)) u
  have final :=
    Derives.appendRight
      (edmundsPeriodTwoBlocksDerivesDoubleDoubleCommutation u v) u
  exact Derives.trans
    (by simpa [Word.append_assoc] using first) <|
      Derives.trans
        (by simpa [Word.append_assoc] using gathered)
        (by simpa [Word.append_assoc] using final)

/-- Two triple blocks commute. -/
theorem edmundsPeriodTwoBlocksDerivesTripleTripleCommutation
    (u v : Word Nat) :
    Derives edmundsPeriodTwoBlocksBasis
      (((u ++ u) ++ u) ++ ((v ++ v) ++ v))
      (((v ++ v) ++ v) ++ ((u ++ u) ++ u)) := by
  have first :=
    Derives.appendRight
      (edmundsPeriodTwoBlocksDerivesTripleDoubleCommutation u v) v
  have gathered :=
    Derives.prepend v <|
      edmundsPeriodTwoBlocksDerivesGather v ((u ++ u) ++ u)
  exact Derives.trans
    (by simpa [Word.append_assoc] using first)
    (by simpa [Word.append_assoc] using gathered)

/-- A first-occurrence block carries one, two, or three copies of its label. -/
inductive EdmundsPeriodTwoBlock where
  | single : Nat → EdmundsPeriodTwoBlock
  | double : Nat → EdmundsPeriodTwoBlock
  | triple : Nat → EdmundsPeriodTwoBlock
deriving DecidableEq, Repr

namespace EdmundsPeriodTwoBlock

def label : EdmundsPeriodTwoBlock → Nat
  | .single x => x
  | .double x => x
  | .triple x => x

def exponent : EdmundsPeriodTwoBlock → Nat
  | .single _ => 1
  | .double _ => 2
  | .triple _ => 3

def render : EdmundsPeriodTwoBlock → List Nat
  | .single x => [x]
  | .double x => [x, x]
  | .triple x => [x, x, x]

end EdmundsPeriodTwoBlock

def renderEdmundsPeriodTwoBlocks
    (blocks : List EdmundsPeriodTwoBlock) : List Nat :=
  blocks.flatMap EdmundsPeriodTwoBlock.render

/-- A block known structurally to be repeated. The constructor records whether
the attached multiplicity tag is two or three. -/
inductive EdmundsPeriodTwoRepeatedBlock where
  | double : Nat → EdmundsPeriodTwoRepeatedBlock
  | triple : Nat → EdmundsPeriodTwoRepeatedBlock
deriving DecidableEq, Repr

namespace EdmundsPeriodTwoRepeatedBlock

def toBlock : EdmundsPeriodTwoRepeatedBlock → EdmundsPeriodTwoBlock
  | .double x => .double x
  | .triple x => .triple x

def label (block : EdmundsPeriodTwoRepeatedBlock) : Nat :=
  block.toBlock.label

def exponent (block : EdmundsPeriodTwoRepeatedBlock) : Nat :=
  block.toBlock.exponent

def render (block : EdmundsPeriodTwoRepeatedBlock) : List Nat :=
  block.toBlock.render

end EdmundsPeriodTwoRepeatedBlock

def renderEdmundsPeriodTwoRepeatedBlocks
    (blocks : List EdmundsPeriodTwoRepeatedBlock) : List Nat :=
  blocks.flatMap EdmundsPeriodTwoRepeatedBlock.render

def edmundsPeriodTwoBlocksWordOfCons
    (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

/-- List-level derivability, including the empty-list case that cannot itself
be represented by a free-semigroup word. -/
inductive EdmundsPeriodTwoBlocksListDerives :
    List Nat → List Nat → Prop
  | empty : EdmundsPeriodTwoBlocksListDerives [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives edmundsPeriodTwoBlocksBasis
        (edmundsPeriodTwoBlocksWordOfCons x xs)
        (edmundsPeriodTwoBlocksWordOfCons y ys) →
      EdmundsPeriodTwoBlocksListDerives (x :: xs) (y :: ys)

namespace EdmundsPeriodTwoBlocksListDerives

theorem refl :
    ∀ xs : List Nat, EdmundsPeriodTwoBlocksListDerives xs xs
  | [] => .empty
  | _ :: _ => .words (Derives.refl _)

theorem trans
    {xs ys zs : List Nat}
    (first : EdmundsPeriodTwoBlocksListDerives xs ys)
    (second : EdmundsPeriodTwoBlocksListDerives ys zs) :
    EdmundsPeriodTwoBlocksListDerives xs zs := by
  cases first with
  | empty =>
      cases second
      exact .empty
  | words hfirst =>
      cases second with
      | words hsecond =>
          exact .words (Derives.trans hfirst hsecond)

theorem symm
    {xs ys : List Nat}
    (derivation : EdmundsPeriodTwoBlocksListDerives xs ys) :
    EdmundsPeriodTwoBlocksListDerives ys xs := by
  cases derivation with
  | empty => exact .empty
  | words h => exact .words (Derives.symm h)

theorem prepend
    (pre : List Nat) {xs ys : List Nat}
    (derivation : EdmundsPeriodTwoBlocksListDerives xs ys) :
    EdmundsPeriodTwoBlocksListDerives
      (pre ++ xs) (pre ++ ys) := by
  cases pre with
  | nil => simpa using derivation
  | cons p ps =>
      cases derivation with
      | empty =>
          simpa using refl (p :: ps)
      | @words x y xs ys h =>
          exact .words <| by
            have prefixed :=
              Derives.prepend
                (edmundsPeriodTwoBlocksWordOfCons p ps) h
            simpa [edmundsPeriodTwoBlocksWordOfCons,
              Word.append, List.append_assoc] using prefixed

theorem append
    {xs ys : List Nat}
    (derivation : EdmundsPeriodTwoBlocksListDerives xs ys)
    (suffix : List Nat) :
    EdmundsPeriodTwoBlocksListDerives
      (xs ++ suffix) (ys ++ suffix) := by
  cases derivation with
  | empty =>
      exact refl suffix
  | @words x y xs ys h =>
      cases suffix with
      | nil =>
          simpa using EdmundsPeriodTwoBlocksListDerives.words h
      | cons z zs =>
          exact .words <| by
            have appended :=
              Derives.appendRight h
                (edmundsPeriodTwoBlocksWordOfCons z zs)
            simpa [edmundsPeriodTwoBlocksWordOfCons,
              Word.append, List.append_assoc] using appended

end EdmundsPeriodTwoBlocksListDerives

/-- Any two repeated blocks commute after rendering; their double/triple tags
remain attached to their labels. -/
theorem edmundsPeriodTwoBlocksDerivesRepeatedBlockCommutation
    (left right : EdmundsPeriodTwoRepeatedBlock) :
    EdmundsPeriodTwoBlocksListDerives
      (left.render ++ right.render)
      (right.render ++ left.render) := by
  cases left with
  | double x =>
      cases right with
      | double y =>
          exact .words <| by
            simpa [EdmundsPeriodTwoRepeatedBlock.render,
              EdmundsPeriodTwoRepeatedBlock.toBlock,
              EdmundsPeriodTwoBlock.render,
              edmundsPeriodTwoBlocksWordOfCons, Word.append,
              Word.singleton, Word.append_assoc] using
                edmundsPeriodTwoBlocksDerivesDoubleDoubleCommutation
                  (Word.singleton x) (Word.singleton y)
      | triple y =>
          exact .words <| by
            simpa [EdmundsPeriodTwoRepeatedBlock.render,
              EdmundsPeriodTwoRepeatedBlock.toBlock,
              EdmundsPeriodTwoBlock.render,
              edmundsPeriodTwoBlocksWordOfCons, Word.append,
              Word.singleton, Word.append_assoc] using
                edmundsPeriodTwoBlocksDerivesDoubleTripleCommutation
                  (Word.singleton x) (Word.singleton y)
  | triple x =>
      cases right with
      | double y =>
          exact .words <| by
            simpa [EdmundsPeriodTwoRepeatedBlock.render,
              EdmundsPeriodTwoRepeatedBlock.toBlock,
              EdmundsPeriodTwoBlock.render,
              edmundsPeriodTwoBlocksWordOfCons, Word.append,
              Word.singleton, Word.append_assoc] using
                edmundsPeriodTwoBlocksDerivesTripleDoubleCommutation
                  (Word.singleton x) (Word.singleton y)
      | triple y =>
          exact .words <| by
            simpa [EdmundsPeriodTwoRepeatedBlock.render,
              EdmundsPeriodTwoRepeatedBlock.toBlock,
              EdmundsPeriodTwoBlock.render,
              edmundsPeriodTwoBlocksWordOfCons, Word.append,
              Word.singleton, Word.append_assoc] using
                edmundsPeriodTwoBlocksDerivesTripleTripleCommutation
                  (Word.singleton x) (Word.singleton y)

/-- Every permutation of repeated blocks is derivable after rendering. The
permutation acts on blocks, so each label keeps its double/triple tag. -/
theorem edmundsPeriodTwoBlocksDerivesRepeatedBlockPermutation
    {source target : List EdmundsPeriodTwoRepeatedBlock}
    (permutation : source.Perm target) :
    EdmundsPeriodTwoBlocksListDerives
      (renderEdmundsPeriodTwoRepeatedBlocks source)
      (renderEdmundsPeriodTwoRepeatedBlocks target) := by
  induction permutation with
  | nil =>
      exact .empty
  | cons block _ ih =>
      simpa [renderEdmundsPeriodTwoRepeatedBlocks] using
        ih.prepend block.render
  | swap left right rest =>
      have swapped :=
        edmundsPeriodTwoBlocksDerivesRepeatedBlockCommutation
          left right
      simpa [renderEdmundsPeriodTwoRepeatedBlocks] using
        (swapped.append
          (renderEdmundsPeriodTwoRepeatedBlocks rest)).symm
  | trans _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂

/-- Move one later occurrence of the initial variable next to its first
occurrence. -/
private theorem edmundsPeriodTwoBlocksDerivesFirstRepeat
    (x : Nat) (middle suffix : List Nat) :
    Derives edmundsPeriodTwoBlocksBasis
      (edmundsPeriodTwoBlocksWordOfCons x (middle ++ x :: suffix))
      (edmundsPeriodTwoBlocksWordOfCons x (x :: middle ++ suffix)) := by
  cases middle with
  | nil =>
      exact Derives.refl _
  | cons y ys =>
      let middleWord := edmundsPeriodTwoBlocksWordOfCons y ys
      cases suffix with
      | nil =>
          simpa [edmundsPeriodTwoBlocksWordOfCons, middleWord,
            Word.append, Word.singleton, Word.append_assoc] using
              edmundsPeriodTwoBlocksDerivesGather
                (Word.singleton x) middleWord
      | cons z zs =>
          have h :=
            Derives.appendRight
              (edmundsPeriodTwoBlocksDerivesGather
                (Word.singleton x) middleWord)
              (edmundsPeriodTwoBlocksWordOfCons z zs)
          simpa [edmundsPeriodTwoBlocksWordOfCons, middleWord,
            Word.append, Word.singleton, Word.append_assoc] using h

/-- Move a third occurrence of the initial variable next to its initial
double block. -/
private theorem edmundsPeriodTwoBlocksDerivesThird
    (x : Nat) (middle suffix : List Nat) :
    Derives edmundsPeriodTwoBlocksBasis
      (edmundsPeriodTwoBlocksWordOfCons x
        (x :: middle ++ x :: suffix))
      (edmundsPeriodTwoBlocksWordOfCons x
        (x :: x :: middle ++ suffix)) := by
  cases middle with
  | nil =>
      exact Derives.refl _
  | cons y ys =>
      let middleWord := edmundsPeriodTwoBlocksWordOfCons y ys
      have moved :=
        Derives.prepend (Word.singleton x) <|
          edmundsPeriodTwoBlocksDerivesGather
            (Word.singleton x) middleWord
      cases suffix with
      | nil =>
          simpa [edmundsPeriodTwoBlocksWordOfCons, middleWord,
            Word.append, Word.singleton, Word.append_assoc] using moved
      | cons z zs =>
          have movedWithSuffix :=
            Derives.appendRight moved
              (edmundsPeriodTwoBlocksWordOfCons z zs)
          simpa [edmundsPeriodTwoBlocksWordOfCons, middleWord,
            Word.append, Word.singleton, Word.append_assoc] using
              movedWithSuffix

/-- Gather a fourth occurrence and contract the resulting initial fourth
power back to a double block. -/
private theorem edmundsPeriodTwoBlocksDerivesFourthToDouble
    (x : Nat) (middle suffix : List Nat) :
    Derives edmundsPeriodTwoBlocksBasis
      (edmundsPeriodTwoBlocksWordOfCons x
        (x :: x :: middle ++ x :: suffix))
      (edmundsPeriodTwoBlocksWordOfCons x
        (x :: middle ++ suffix)) := by
  cases middle with
  | nil =>
      cases suffix with
      | nil =>
          simpa [edmundsPeriodTwoBlocksWordOfCons, Word.append,
            Word.singleton, Word.append_assoc] using
              edmundsPeriodTwoBlocksDerivesFourToTwo
                (Word.singleton x)
      | cons z zs =>
          have h :=
            Derives.appendRight
              (edmundsPeriodTwoBlocksDerivesFourToTwo
                (Word.singleton x))
              (edmundsPeriodTwoBlocksWordOfCons z zs)
          simpa [edmundsPeriodTwoBlocksWordOfCons, Word.append,
            Word.singleton, Word.append_assoc] using h
  | cons y ys =>
      let middleWord := edmundsPeriodTwoBlocksWordOfCons y ys
      have moved :=
        Derives.prepend
          ((Word.singleton x) ++ (Word.singleton x)) <|
            edmundsPeriodTwoBlocksDerivesGather
              (Word.singleton x) middleWord
      have contracted :=
        Derives.appendRight
          (edmundsPeriodTwoBlocksDerivesFourToTwo
            (Word.singleton x))
          middleWord
      cases suffix with
      | nil =>
          exact Derives.trans
            (by
              simpa [edmundsPeriodTwoBlocksWordOfCons, middleWord,
                Word.append, Word.singleton, Word.append_assoc] using moved)
            (by
              simpa [edmundsPeriodTwoBlocksWordOfCons, middleWord,
                Word.append, Word.singleton, Word.append_assoc] using
                  contracted)
      | cons z zs =>
          have movedWithSuffix :=
            Derives.appendRight moved
              (edmundsPeriodTwoBlocksWordOfCons z zs)
          have contractedWithSuffix :=
            Derives.appendRight contracted
              (edmundsPeriodTwoBlocksWordOfCons z zs)
          exact Derives.trans
            (by
              simpa [edmundsPeriodTwoBlocksWordOfCons, middleWord,
                Word.append, Word.singleton, Word.append_assoc] using
                  movedWithSuffix)
            (by
              simpa [edmundsPeriodTwoBlocksWordOfCons, middleWord,
                Word.append, Word.singleton, Word.append_assoc] using
                  contractedWithSuffix)

private inductive EdmundsPeriodTwoGatherState where
  | one
  | two
  | three
deriving DecidableEq, Repr

private def EdmundsPeriodTwoGatherState.exponent :
    EdmundsPeriodTwoGatherState → Nat
  | .one => 1
  | .two => 2
  | .three => 3

private def EdmundsPeriodTwoGatherState.next :
    EdmundsPeriodTwoGatherState → EdmundsPeriodTwoGatherState
  | .one => .two
  | .two => .three
  | .three => .two

private def EdmundsPeriodTwoGatherState.advance :
    EdmundsPeriodTwoGatherState → Nat → EdmundsPeriodTwoGatherState
  | state, 0 => state
  | state, n + 1 => advance state.next n

private def edmundsPeriodTwoBlocksBlockTail
    (state : EdmundsPeriodTwoGatherState)
    (x : Nat) (middle suffix : List Nat) : List Nat :=
  List.replicate (state.exponent - 1) x ++ middle ++ suffix

private theorem edmundsPeriodTwoBlocksAdvance_exponent
    (state : EdmundsPeriodTwoGatherState) (n : Nat) :
    (state.advance n).exponent =
      periodTwoFromTwoExponent (state.exponent + n) := by
  induction n generalizing state with
  | zero =>
      cases state <;> rfl
  | succ n ih =>
      rw [EdmundsPeriodTwoGatherState.advance]
      rw [ih]
      cases state with
      | one =>
          simp only [EdmundsPeriodTwoGatherState.next,
            EdmundsPeriodTwoGatherState.exponent]
          congr 1
          omega
      | two =>
          simp only [EdmundsPeriodTwoGatherState.next,
            EdmundsPeriodTwoGatherState.exponent]
          congr 1
          omega
      | three =>
          simp only [EdmundsPeriodTwoGatherState.next,
            EdmundsPeriodTwoGatherState.exponent]
          unfold periodTwoFromTwoExponent
          simp only [show ¬2 + n < 2 by omega,
            show ¬3 + (n + 1) < 2 by omega, ↓reduceIte]
          congr 1
          omega

private theorem edmundsPeriodTwoBlocksExponent_le_three (n : Nat) :
    periodTwoFromTwoExponent n ≤ 3 := by
  unfold periodTwoFromTwoExponent
  split <;> omega

private theorem edmundsPeriodTwoBlocksExponent_succ_normalized (n : Nat) :
    periodTwoFromTwoExponent
        (periodTwoFromTwoExponent n + 1) =
      periodTwoFromTwoExponent (n + 1) := by
  have bound := edmundsPeriodTwoBlocksExponent_le_three n
  have cases :
      periodTwoFromTwoExponent n = 0 ∨
          periodTwoFromTwoExponent n = 1 ∨
          periodTwoFromTwoExponent n = 2 ∨
            periodTwoFromTwoExponent n = 3 := by
    have nonnegative : 0 ≤ periodTwoFromTwoExponent n := by omega
    omega
  rcases cases with h | h | h | h <;>
    rw [periodTwoFromTwoExponent_succ n] <;>
    rw [h] <;>
    decide

/-- Scan a suffix, gathering every later copy of the initial variable. The
front block moves through the states one, two, three, two, three, ... . -/
private theorem edmundsPeriodTwoBlocksDerivesGatherPeriod :
    ∀ (state : EdmundsPeriodTwoGatherState)
        (x : Nat) (middle rest : List Nat),
      Derives edmundsPeriodTwoBlocksBasis
        (edmundsPeriodTwoBlocksWordOfCons x
          (edmundsPeriodTwoBlocksBlockTail state x middle rest))
        (edmundsPeriodTwoBlocksWordOfCons x
          (edmundsPeriodTwoBlocksBlockTail
            (state.advance (rest.count x)) x middle
            (rest.filter (fun y => decide (y ≠ x)))))
  | state, x, middle, [] => by
      simp [edmundsPeriodTwoBlocksBlockTail,
        EdmundsPeriodTwoGatherState.advance]
      exact Derives.refl _
  | state, x, middle, y :: ys => by
      by_cases hy : y = x
      · subst y
        cases state with
        | one =>
            have first :=
              edmundsPeriodTwoBlocksDerivesFirstRepeat x middle ys
            have remaining :=
              edmundsPeriodTwoBlocksDerivesGatherPeriod
                .two x middle ys
            exact Derives.trans first <| by
              simpa [edmundsPeriodTwoBlocksBlockTail,
                EdmundsPeriodTwoGatherState.advance] using remaining
        | two =>
            have first :=
              edmundsPeriodTwoBlocksDerivesThird x middle ys
            have remaining :=
              edmundsPeriodTwoBlocksDerivesGatherPeriod
                .three x middle ys
            exact Derives.trans first <| by
              simpa [edmundsPeriodTwoBlocksBlockTail,
                EdmundsPeriodTwoGatherState.advance] using remaining
        | three =>
            have first :=
              edmundsPeriodTwoBlocksDerivesFourthToDouble x middle ys
            have remaining :=
              edmundsPeriodTwoBlocksDerivesGatherPeriod
                .two x middle ys
            exact Derives.trans first <| by
              simpa [edmundsPeriodTwoBlocksBlockTail,
                EdmundsPeriodTwoGatherState.advance] using remaining
      · have remaining :=
          edmundsPeriodTwoBlocksDerivesGatherPeriod
            state x (middle ++ [y]) ys
        simpa [edmundsPeriodTwoBlocksBlockTail, hy,
          List.count_cons_of_ne hy, List.append_assoc] using remaining

private theorem edmundsPeriodTwoBlocksCount_replicate_of_ne
    {x z : Nat} (hzx : z ≠ x) :
    ∀ n : Nat, (List.replicate n x).count z = 0
  | 0 => rfl
  | n + 1 => by
      rw [List.replicate_succ,
        List.count_cons_of_ne (Ne.symm hzx),
        edmundsPeriodTwoBlocksCount_replicate_of_ne hzx n]

private theorem edmundsPeriodTwoBlocksCount_filter_ne_self
    (x : Nat) (xs : List Nat) :
    (xs.filter (fun z => decide (z ≠ x))).count x = 0 := by
  apply List.count_eq_zero.mpr
  simp

private theorem edmundsPeriodTwoBlocksCount_filter_ne_of_ne
    {x z : Nat} (hzx : z ≠ x) (xs : List Nat) :
    (xs.filter (fun a => decide (a ≠ x))).count z = xs.count z := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
      by_cases hax : a = x
      · subst a
        rw [List.filter_cons_of_neg (by simp),
          List.count_cons_of_ne (Ne.symm hzx)]
        exact ih
      · rw [List.filter_cons_of_pos (by simpa)]
        simp only [List.count_cons]
        rw [ih]

/-- The unrestricted first-occurrence normal list. Each variable occurs in
one block of length one, two, or three, with length determined by
`periodTwoFromTwoExponent`. -/
def edmundsPeriodTwoBlocksNormalList : List Nat → List Nat
  | [] => []
  | x :: xs =>
      let rest := edmundsPeriodTwoBlocksNormalList xs
      List.replicate
          (periodTwoFromTwoExponent ((x :: xs).count x)) x ++
        rest.filter (fun y => decide (y ≠ x))

theorem edmundsPeriodTwoBlocksNormalList_count
    (z : Nat) :
    ∀ xs : List Nat,
      (edmundsPeriodTwoBlocksNormalList xs).count z =
        periodTwoFromTwoExponent (xs.count z)
  | [] => by
      simp [edmundsPeriodTwoBlocksNormalList,
        periodTwoFromTwoExponent]
  | x :: xs => by
      simp only [edmundsPeriodTwoBlocksNormalList, List.count_append]
      by_cases hzx : z = x
      · subst z
        rw [List.count_replicate_self,
          edmundsPeriodTwoBlocksCount_filter_ne_self]
        omega
      · rw [edmundsPeriodTwoBlocksCount_replicate_of_ne hzx,
          edmundsPeriodTwoBlocksCount_filter_ne_of_ne hzx,
          Nat.zero_add, edmundsPeriodTwoBlocksNormalList_count]
        rw [List.count_cons_of_ne (Ne.symm hzx)]

theorem edmundsPeriodTwoBlocksNormalList_cons_ne_nil
    (x : Nat) (xs : List Nat) :
    edmundsPeriodTwoBlocksNormalList (x :: xs) ≠ [] := by
  intro h
  have countEq :=
    edmundsPeriodTwoBlocksNormalList_count x (x :: xs)
  rw [h, List.count_nil, List.count_cons_self] at countEq
  exact (Nat.ne_of_gt <|
    periodTwoFromTwoExponent_pos (by omega)) countEq.symm

/-- Flattened first-occurrence block normal forms. Every variable has exactly
one block, of length one, two, or three. -/
inductive EdmundsPeriodTwoBlocksNormal : List Nat → Prop
  | nil : EdmundsPeriodTwoBlocksNormal []
  | single (x : Nat) (xs : List Nat) :
      EdmundsPeriodTwoBlocksNormal xs →
      x ∉ xs →
      EdmundsPeriodTwoBlocksNormal (x :: xs)
  | double (x : Nat) (xs : List Nat) :
      EdmundsPeriodTwoBlocksNormal xs →
      x ∉ xs →
      EdmundsPeriodTwoBlocksNormal (x :: x :: xs)
  | triple (x : Nat) (xs : List Nat) :
      EdmundsPeriodTwoBlocksNormal xs →
      x ∉ xs →
      EdmundsPeriodTwoBlocksNormal (x :: x :: x :: xs)

private theorem EdmundsPeriodTwoBlocksNormal.filter_ne
    {xs : List Nat} (normal : EdmundsPeriodTwoBlocksNormal xs) (x : Nat) :
    EdmundsPeriodTwoBlocksNormal
      (xs.filter (fun y => decide (y ≠ x))) := by
  induction normal with
  | nil =>
      exact .nil
  | single y ys _ yNotMem ih =>
      by_cases hyx : y = x
      · subst y
        have tailEq :
            ys.filter (fun z => decide (z ≠ x)) = ys := by
          apply List.filter_eq_self.mpr
          intro z hz
          simp only [decide_eq_true_eq]
          intro h
          subst z
          exact yNotMem hz
        simpa [tailEq] using ih
      · have yNotMemFilter :
            y ∉ ys.filter (fun z => decide (z ≠ x)) := by
          exact fun h => yNotMem (List.mem_filter.mp h).1
        simpa [hyx] using
          EdmundsPeriodTwoBlocksNormal.single y _ ih yNotMemFilter
  | double y ys _ yNotMem ih =>
      by_cases hyx : y = x
      · subst y
        have tailEq :
            ys.filter (fun z => decide (z ≠ x)) = ys := by
          apply List.filter_eq_self.mpr
          intro z hz
          simp only [decide_eq_true_eq]
          intro h
          subst z
          exact yNotMem hz
        simpa [tailEq] using ih
      · have yNotMemFilter :
            y ∉ ys.filter (fun z => decide (z ≠ x)) := by
          exact fun h => yNotMem (List.mem_filter.mp h).1
        simpa [hyx] using
          EdmundsPeriodTwoBlocksNormal.double y _ ih yNotMemFilter
  | triple y ys _ yNotMem ih =>
      by_cases hyx : y = x
      · subst y
        have tailEq :
            ys.filter (fun z => decide (z ≠ x)) = ys := by
          apply List.filter_eq_self.mpr
          intro z hz
          simp only [decide_eq_true_eq]
          intro h
          subst z
          exact yNotMem hz
        simpa [tailEq] using ih
      · have yNotMemFilter :
            y ∉ ys.filter (fun z => decide (z ≠ x)) := by
          exact fun h => yNotMem (List.mem_filter.mp h).1
        simpa [hyx] using
          EdmundsPeriodTwoBlocksNormal.triple y _ ih yNotMemFilter

theorem edmundsPeriodTwoBlocksNormalList_normal :
    ∀ xs : List Nat,
      EdmundsPeriodTwoBlocksNormal
        (edmundsPeriodTwoBlocksNormalList xs)
  | [] => .nil
  | x :: xs => by
      let rest := edmundsPeriodTwoBlocksNormalList xs
      have restNormal := edmundsPeriodTwoBlocksNormalList_normal xs
      have filteredNormal := restNormal.filter_ne x
      have xNotMem :
          x ∉ rest.filter (fun y => decide (y ≠ x)) := by
        simp
      have positive :
          0 < periodTwoFromTwoExponent ((x :: xs).count x) :=
        periodTwoFromTwoExponent_pos (by simp)
      have bound :=
        edmundsPeriodTwoBlocksExponent_le_three ((x :: xs).count x)
      have cases :
          periodTwoFromTwoExponent ((x :: xs).count x) = 1 ∨
            periodTwoFromTwoExponent ((x :: xs).count x) = 2 ∨
              periodTwoFromTwoExponent ((x :: xs).count x) = 3 := by
        omega
      rcases cases with h | h | h
      · change EdmundsPeriodTwoBlocksNormal
          (List.replicate
              (periodTwoFromTwoExponent ((x :: xs).count x)) x ++
            rest.filter (fun y => decide (y ≠ x)))
        rw [h]
        simpa using
          EdmundsPeriodTwoBlocksNormal.single
            x _ filteredNormal xNotMem
      · change EdmundsPeriodTwoBlocksNormal
          (List.replicate
              (periodTwoFromTwoExponent ((x :: xs).count x)) x ++
            rest.filter (fun y => decide (y ≠ x)))
        rw [h]
        simpa using
          EdmundsPeriodTwoBlocksNormal.double
            x _ filteredNormal xNotMem
      · change EdmundsPeriodTwoBlocksNormal
          (List.replicate
              (periodTwoFromTwoExponent ((x :: xs).count x)) x ++
            rest.filter (fun y => decide (y ≠ x)))
        rw [h]
        simpa using
          EdmundsPeriodTwoBlocksNormal.triple
            x _ filteredNormal xNotMem

private theorem edmundsPeriodTwoBlocksDerivesNormalizeList :
    ∀ x xs,
      match edmundsPeriodTwoBlocksNormalList (x :: xs) with
      | [] => False
      | y :: ys =>
          Derives edmundsPeriodTwoBlocksBasis
            (edmundsPeriodTwoBlocksWordOfCons x xs)
            (edmundsPeriodTwoBlocksWordOfCons y ys)
  | x, [] => by
      have normalEq :
          edmundsPeriodTwoBlocksNormalList [x] = [x] := by
        simp [edmundsPeriodTwoBlocksNormalList,
          periodTwoFromTwoExponent]
      rw [normalEq]
      exact Derives.refl _
  | x, y :: ys => by
      have suffixNormal :=
        edmundsPeriodTwoBlocksDerivesNormalizeList y ys
      cases hn : edmundsPeriodTwoBlocksNormalList (y :: ys) with
      | nil =>
          exact False.elim <|
            edmundsPeriodTwoBlocksNormalList_cons_ne_nil y ys hn
      | cons z zs =>
          rw [hn] at suffixNormal
          have prefixed :=
            Derives.prepend (Word.singleton x) suffixNormal
          have gathered :=
            edmundsPeriodTwoBlocksDerivesGatherPeriod
              .one x [] (z :: zs)
          have restCount :
              (z :: zs).count x =
                periodTwoFromTwoExponent ((y :: ys).count x) := by
            simpa [hn] using
              edmundsPeriodTwoBlocksNormalList_count x (y :: ys)
          have exponentEq :
              ((EdmundsPeriodTwoGatherState.one.advance
                  ((z :: zs).count x)).exponent) =
                periodTwoFromTwoExponent
                  ((x :: y :: ys).count x) := by
            rw [edmundsPeriodTwoBlocksAdvance_exponent]
            simp only [EdmundsPeriodTwoGatherState.exponent]
            rw [restCount, List.count_cons_self]
            simpa [Nat.add_comm] using
              edmundsPeriodTwoBlocksExponent_succ_normalized
                ((y :: ys).count x)
          have positive :
              0 <
                periodTwoFromTwoExponent
                  ((x :: y :: ys).count x) :=
            periodTwoFromTwoExponent_pos (by simp)
          have normalEq :
              edmundsPeriodTwoBlocksNormalList (x :: y :: ys) =
                x ::
                  List.replicate
                    (periodTwoFromTwoExponent
                      ((x :: y :: ys).count x) - 1) x ++
                    (z :: zs).filter
                      (fun a => decide (a ≠ x)) := by
            change
              List.replicate
                  (periodTwoFromTwoExponent
                    ((x :: y :: ys).count x)) x ++
                  (edmundsPeriodTwoBlocksNormalList
                    (y :: ys)).filter
                    (fun a => decide (a ≠ x)) =
                x ::
                  List.replicate
                    (periodTwoFromTwoExponent
                      ((x :: y :: ys).count x) - 1) x ++
                    (z :: zs).filter
                      (fun a => decide (a ≠ x))
            rw [hn]
            cases h :
                periodTwoFromTwoExponent
                  ((x :: y :: ys).count x) with
            | zero => omega
            | succ n =>
                simp [List.replicate_succ]
          rw [normalEq]
          exact Derives.trans
            (by
              simpa [edmundsPeriodTwoBlocksWordOfCons, Word.append,
                Word.singleton, Word.append_assoc] using prefixed)
            (by
              simpa [edmundsPeriodTwoBlocksBlockTail, exponentEq] using
                gathered)
termination_by
  _ xs => xs.length

/-- Every nonempty word derives to its first-occurrence block normal form,
whose block sizes are one, two, or three. -/
theorem edmundsPeriodTwoBlocksDerivesNormal (w : Word Nat) :
    match edmundsPeriodTwoBlocksNormalList w.toList with
    | [] => False
    | x :: xs =>
        Derives edmundsPeriodTwoBlocksBasis w
          (edmundsPeriodTwoBlocksWordOfCons x xs) := by
  cases w with
  | mk head tail =>
      exact edmundsPeriodTwoBlocksDerivesNormalizeList head tail

end SemigroupBasis.Examples
