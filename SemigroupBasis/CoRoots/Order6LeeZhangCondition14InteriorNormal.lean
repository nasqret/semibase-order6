import SemigroupBasis.CoRoots.Order6LeeZhangCondition14Derivations
import SemigroupBasis.Examples.ParityInitialFourSyntax

/-!
# Interior parity normalization for Lee--Zhang Condition 14

Inside matching endpoint letters, the consequences (9.2b) and (9.2d)
simulate the two-law parity-initial calculus `x = x^3`, `xyx = x^2y`.
Consequently the existing lower-order normalizer can be replayed without
reproving its recursive scan.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions.Condition14

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev ListDerives : List Nat -> List Nat -> Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

private abbrev listWordOfCons :=
  SemigroupBasis.CoRoots.S5_107.listWordOfCons

private def instantiateThreeWords
    (first second third : Word Nat) : Nat -> Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

private def instantiateFourWords
    (first second third fourth : Word Nat) : Nat -> Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | 3 => fourth
  | n + 4 => Word.singleton (n + 4)

private def instantiateFiveWords
    (first second third fourth fifth : Word Nat) : Nat -> Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | 3 => fourth
  | 4 => fifth
  | n + 5 => Word.singleton (n + 5)

private theorem derivesGatherRepeatNoContext
    (endpoint repeated middle : Word Nat) :
    Derives basis
      (((((endpoint ++ repeated) ++ middle) ++ repeated) ++ endpoint))
      (((((endpoint ++ repeated) ++ repeated) ++ middle) ++ endpoint)) := by
  have base :
      Derives basis
        (listWordOfCons 0 [1, 2, 1, 0])
        (listWordOfCons 0 [1, 1, 2, 0]) := by
    simpa [List.append_assoc] using
      SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
        (listDerivesContextGatherRepeat 0 1 2 [] [])
  have substituted :=
    Derives.subst base
      (instantiateThreeWords endpoint repeated middle)
  have sourceEq :
      (listWordOfCons 0 [1, 2, 1, 0]).bind
          (instantiateThreeWords endpoint repeated middle) =
        ((((endpoint ++ repeated) ++ middle) ++ repeated) ++ endpoint) := by
    apply Word.toList_injective
    simp [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
      instantiateThreeWords, Word.toList_bind, Word.toList_append,
      Word.bind, Word.append, Word.toList, List.append_assoc]
  have targetEq :
      (listWordOfCons 0 [1, 1, 2, 0]).bind
          (instantiateThreeWords endpoint repeated middle) =
        ((((endpoint ++ repeated) ++ repeated) ++ middle) ++ endpoint) := by
    apply Word.toList_injective
    simp [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
      instantiateThreeWords, Word.toList_bind, Word.toList_append,
      Word.bind, Word.append, Word.toList, List.append_assoc]
  rw [sourceEq, targetEq] at substituted
  exact substituted

private theorem derivesGatherRepeatLeftContext
    (endpoint repeated middle leftContext : Word Nat) :
    Derives basis
      ((((((endpoint ++ leftContext) ++ repeated) ++ middle) ++
        repeated) ++ endpoint))
      ((((((endpoint ++ leftContext) ++ repeated) ++ repeated) ++
        middle) ++ endpoint)) := by
  have base :
      Derives basis
        (listWordOfCons 0 [3, 1, 2, 1, 0])
        (listWordOfCons 0 [3, 1, 1, 2, 0]) := by
    simpa [List.append_assoc] using
      SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
        (listDerivesContextGatherRepeat 0 1 2 [3] [])
  have substituted :=
    Derives.subst base
      (instantiateFourWords endpoint repeated middle leftContext)
  have sourceEq :
      (listWordOfCons 0 [3, 1, 2, 1, 0]).bind
          (instantiateFourWords endpoint repeated middle leftContext) =
        (((((endpoint ++ leftContext) ++ repeated) ++ middle) ++
          repeated) ++ endpoint) := by
    apply Word.toList_injective
    simp [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
      instantiateFourWords, Word.toList_bind, Word.toList_append,
      Word.bind, Word.append, Word.toList, List.append_assoc]
  have targetEq :
      (listWordOfCons 0 [3, 1, 1, 2, 0]).bind
          (instantiateFourWords endpoint repeated middle leftContext) =
        (((((endpoint ++ leftContext) ++ repeated) ++ repeated) ++
          middle) ++ endpoint) := by
    apply Word.toList_injective
    simp [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
      instantiateFourWords, Word.toList_bind, Word.toList_append,
      Word.bind, Word.append, Word.toList, List.append_assoc]
  rw [sourceEq, targetEq] at substituted
  exact substituted

private theorem derivesGatherRepeatRightContext
    (endpoint repeated middle rightContext : Word Nat) :
    Derives basis
      ((((((endpoint ++ repeated) ++ middle) ++ repeated) ++
        rightContext) ++ endpoint))
      ((((((endpoint ++ repeated) ++ repeated) ++ middle) ++
        rightContext) ++ endpoint)) := by
  have base :
      Derives basis
        (listWordOfCons 0 [1, 2, 1, 3, 0])
        (listWordOfCons 0 [1, 1, 2, 3, 0]) := by
    simpa [List.append_assoc] using
      SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
        (listDerivesContextGatherRepeat 0 1 2 [] [3])
  have substituted :=
    Derives.subst base
      (instantiateFourWords endpoint repeated middle rightContext)
  have sourceEq :
      (listWordOfCons 0 [1, 2, 1, 3, 0]).bind
          (instantiateFourWords endpoint repeated middle rightContext) =
        (((((endpoint ++ repeated) ++ middle) ++ repeated) ++
          rightContext) ++ endpoint) := by
    apply Word.toList_injective
    simp [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
      instantiateFourWords, Word.toList_bind, Word.toList_append,
      Word.bind, Word.append, Word.toList, List.append_assoc]
  have targetEq :
      (listWordOfCons 0 [1, 1, 2, 3, 0]).bind
          (instantiateFourWords endpoint repeated middle rightContext) =
        (((((endpoint ++ repeated) ++ repeated) ++ middle) ++
          rightContext) ++ endpoint) := by
    apply Word.toList_injective
    simp [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
      instantiateFourWords, Word.toList_bind, Word.toList_append,
      Word.bind, Word.append, Word.toList, List.append_assoc]
  rw [sourceEq, targetEq] at substituted
  exact substituted

private theorem derivesGatherRepeatBothContexts
    (endpoint repeated middle leftContext rightContext : Word Nat) :
    Derives basis
      (((((((endpoint ++ leftContext) ++ repeated) ++ middle) ++
        repeated) ++ rightContext) ++ endpoint))
      (((((((endpoint ++ leftContext) ++ repeated) ++ repeated) ++
        middle) ++ rightContext) ++ endpoint)) := by
  have base :
      Derives basis
        (listWordOfCons 0 [3, 1, 2, 1, 4, 0])
        (listWordOfCons 0 [3, 1, 1, 2, 4, 0]) := by
    simpa [List.append_assoc] using
      SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
        (listDerivesContextGatherRepeat 0 1 2 [3] [4])
  have substituted :=
    Derives.subst base
      (instantiateFiveWords endpoint repeated middle
        leftContext rightContext)
  have sourceEq :
      (listWordOfCons 0 [3, 1, 2, 1, 4, 0]).bind
          (instantiateFiveWords endpoint repeated middle
            leftContext rightContext) =
        ((((((endpoint ++ leftContext) ++ repeated) ++ middle) ++
          repeated) ++ rightContext) ++ endpoint) := by
    apply Word.toList_injective
    simp [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
      instantiateFiveWords, Word.toList_bind, Word.toList_append,
      Word.bind, Word.append, Word.toList, List.append_assoc]
  have targetEq :
      (listWordOfCons 0 [3, 1, 1, 2, 4, 0]).bind
          (instantiateFiveWords endpoint repeated middle
            leftContext rightContext) =
        ((((((endpoint ++ leftContext) ++ repeated) ++ repeated) ++
          middle) ++ rightContext) ++ endpoint) := by
    apply Word.toList_injective
    simp [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
      instantiateFiveWords, Word.toList_bind, Word.toList_append,
      Word.bind, Word.append, Word.toList, List.append_assoc]
  rw [sourceEq, targetEq] at substituted
  exact substituted

/-- Block-substitution form of (9.2d), retaining optional list contexts.
The four context cases are obtained by substituting into four fresh-variable
instances of the already checked singleton theorem. -/
theorem listDerivesContextGatherRepeatBlock
    (endpoint : Nat) (repeated middle : Word Nat)
    (before after : List Nat) :
    ListDerives
      ([endpoint] ++ before ++ repeated.toList ++ middle.toList ++
        repeated.toList ++ after ++ [endpoint])
      ([endpoint] ++ before ++ repeated.toList ++ repeated.toList ++
        middle.toList ++ after ++ [endpoint]) := by
  cases before with
  | nil =>
      cases after with
      | nil =>
          simpa [Word.singleton, Word.toList, Word.toList_append,
            List.append_assoc] using
            (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (basis := basis)
              (derivesGatherRepeatNoContext
                (Word.singleton endpoint) repeated middle))
      | cons afterHead afterTail =>
          let rightContext := listWordOfCons afterHead afterTail
          simpa [rightContext, listWordOfCons, Word.singleton,
            Word.toList, Word.toList_append, List.append_assoc] using
            (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (basis := basis)
              (derivesGatherRepeatRightContext
                (Word.singleton endpoint) repeated middle rightContext))
  | cons beforeHead beforeTail =>
      let leftContext := listWordOfCons beforeHead beforeTail
      cases after with
      | nil =>
          simpa [leftContext, listWordOfCons, Word.singleton,
            Word.toList, Word.toList_append, List.append_assoc] using
            (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (basis := basis)
              (derivesGatherRepeatLeftContext
                (Word.singleton endpoint) repeated middle leftContext))
      | cons afterHead afterTail =>
          let rightContext := listWordOfCons afterHead afterTail
          simpa [leftContext, rightContext, listWordOfCons,
            Word.singleton, Word.toList, Word.toList_append,
            List.append_assoc] using
            (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (basis := basis)
              (derivesGatherRepeatBothContexts
                (Word.singleton endpoint) repeated middle
                leftContext rightContext))

private theorem bind_append (left right : Word Nat)
    (substitution : Nat -> Word Nat) :
    (left ++ right).bind substitution =
      left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind (word : Word Nat)
    (first second : Nat -> Word Nat) :
    (word.bind first).bind second =
      word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- Replay every derivation for `x = x^3`, `xyx = x^2y` inside fixed
matching endpoint contexts. -/
theorem liftParityInitialInterior
    {left right : Word Nat}
    (derivation : Derives parityInitialBasis left right)
    (endpoint : Nat) (before after : List Nat)
    (substitution : Nat -> Word Nat) :
    ListDerives
      ([endpoint] ++ before ++ (left.bind substitution).toList ++
        after ++ [endpoint])
      ([endpoint] ++ before ++ (right.bind substitution).toList ++
        after ++ [endpoint]) := by
  induction derivation generalizing before after substitution with
  | fromBasis member =>
      simp only [parityInitialBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simpa [parityInitialPowerLaw, parityInitialX,
          parityInitialXXX, Word.bind, Word.append, Word.singleton,
          Word.toList, List.append_assoc] using
          (listDerivesContextCubeDeletionBlock endpoint before after
            (substitution 0)).symm
      · simpa [parityInitialGatherLaw, parityInitialXYX,
          parityInitialXXY, Word.bind, Word.append, Word.singleton,
          Word.toList, List.append_assoc] using
          listDerivesContextGatherRepeatBlock endpoint
            (substitution 0) (substitution 1) before after
  | refl =>
      exact SemigroupBasis.CoRoots.S5_107.ListDerives.refl _
  | symm _ ih =>
      exact (ih before after substitution).symm
  | trans _ _ ihFirst ihSecond =>
      exact (ihFirst before after substitution).trans
        (ihSecond before after substitution)
  | prepend stem _ ih =>
      simpa [bind_append, Word.toList_append,
        List.append_assoc] using
        ih
          (before ++ (stem.bind substitution).toList)
          after substitution
  | appendRight _ suffix ih =>
      simpa [bind_append, Word.toList_append,
        List.append_assoc] using
        ih before
          ((suffix.bind substitution).toList ++ after)
          substitution
  | subst _ first ih =>
      simpa [bind_bind] using
        ih before after
          (fun letter => (first letter).bind substitution)

/-- Normalize an arbitrary interior to first-occurrence order with one copy
for odd multiplicity and two copies for positive even multiplicity, while the
two endpoint occurrences remain fixed. -/
theorem listDerivesClosedParityInitialNormal
    (endpoint : Nat) (interior : List Nat) :
    ListDerives
      ([endpoint] ++ interior ++ [endpoint])
      ([endpoint] ++ parityInitialNormalList interior ++ [endpoint]) := by
  cases interior with
  | nil =>
      exact SemigroupBasis.CoRoots.S5_107.ListDerives.refl _
  | cons head tail =>
      let source := listWordOfCons head tail
      have normalized := parityInitialDerivesNormal source
      cases normalShape : parityInitialNormalList (head :: tail) with
      | nil =>
          exact False.elim <|
            parityInitialNormalList_cons_ne_nil head tail normalShape
      | cons normalHead normalTail =>
          change
            match parityInitialNormalList source.toList with
            | [] => False
            | first :: rest =>
                Derives parityInitialBasis source
                  (parityInitialWordOfCons first rest)
            at normalized
          have selectedShape :
              parityInitialNormalList source.toList =
                normalHead :: normalTail := by
            simpa [source, listWordOfCons, Word.toList] using normalShape
          rw [selectedShape] at normalized
          have lifted :=
            liftParityInitialInterior normalized endpoint [] []
              Word.singleton
          rw [bind_singleton, bind_singleton] at lifted
          simpa [source, listWordOfCons, parityInitialWordOfCons,
            Word.singleton, Word.toList, normalShape,
            List.append_assoc] using lifted

end SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions.Condition14
