import SemigroupBasis.CoRoots.Order6Day7.S3_16.SeedS5_203OppositeInitialGuardBridge

/-!
# Safe initial padding for the exact rank-082 presentation

Raw laws01/20 and the already checked initial-pair LRB lift supply two
additional moves.  An initial return beyond the second position absorbs
two initial guards; a second letter occurring in the tail can be copied
immediately after the initial pair.  Neither move erases a unique initial
or a fresh initial doubleton.  All words and substitutions are unrestricted.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank082.InitialSeed

open SemigroupBasis
open SemigroupBasis.Examples
open InitialGuard

/-- An explicit initial pair followed by a possibly empty tail. -/
def initialWord (initial second : Nat) (tail : List Nat) : Word Nat :=
  ⟨initial, second :: tail⟩

@[simp]
theorem toList_initialWord (initial second : Nat) (tail : List Nat) :
    (initialWord initial second tail).toList = initial :: second :: tail := rfl

/-- A nonempty tail gives the literal two-initial-guard word. -/
theorem initialWord_of_word (initial second : Nat) (tail : Word Nat) :
    initialWord initial second tail.toList =
      ((Word.singleton initial ++ Word.singleton second) ++ tail) := rfl

/-- Equal tail first orders replay behind a fixed initial pair, with empty
tails treated literally rather than by an empty semigroup substitution. -/
theorem derivesSameTailFirstOrder (initial second : Nat)
    (leftTail rightTail : List Nat)
    (order : firstOccurrenceSequence leftTail = firstOccurrenceSequence rightTail) :
    Derives basis (initialWord initial second leftTail)
      (initialWord initial second rightTail) := by
  cases leftTail with
  | nil =>
      cases rightTail with
      | nil => exact Derives.refl _
      | cons first rest => simp [firstOccurrenceSequence] at order
  | cons leftFirst leftRest =>
      cases rightTail with
      | nil => simp [firstOccurrenceSequence] at order
      | cons rightFirst rightRest =>
          change Derives basis
            (initialWord initial second (Word.mk leftFirst leftRest).toList)
            (initialWord initial second (Word.mk rightFirst rightRest).toList)
          rw [initialWord_of_word, initialWord_of_word]
          exact derivesSameFirstOrderUnderInitialPair
            (Word.mk leftFirst leftRest) (Word.mk rightFirst rightRest)
            (Word.singleton initial) (Word.singleton second) order

private def substituteThree (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

/-- Literal substitution into frozen law20, `xyyz = xyzyz`. -/
theorem derivesInitialSecondTransfer (first second third : Word Nat) :
    Derives basis (((first ++ second) ++ second) ++ third)
      ((((first ++ second) ++ third) ++ second) ++ third) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 1, 2]) (Word.mk 0 [1, 2, 1, 2]) :=
    Derives.fromBasis (e := law20) (by simp [basis])
  have substituted :=
    Derives.subst primitive (substituteThree first second third)
  simpa [substituteThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- A nonempty return admits the explicit derivation
`xyx -> xxxy -> xxxyx = xx(xyx)`, not global guard cancellation. -/
theorem derivesReturnInitialGuards (initial middle : Word Nat) :
    Derives basis ((initial ++ middle) ++ initial)
      ((initial ++ initial) ++ ((initial ++ middle) ++ initial)) := by
  have first := (derivesTripleReturn initial middle).symm
  have second :=
    derivesLrbRegularUnderInitialPair initial initial initial middle
  simpa only [Word.append_assoc] using first.trans second

/-- Move a returning second block to just after the initial pair by
`xyzy -> xyzyz -> xyyz -> xyyzy`. -/
theorem derivesSeenSecondAcross (initial second middle : Word Nat) :
    Derives basis (((initial ++ second) ++ middle) ++ second)
      ((((initial ++ second) ++ second) ++ middle) ++ second) := by
  have first :=
    derivesLrbRegularUnderInitialPair initial second middle second
  have next := (derivesInitialSecondTransfer initial second middle).symm
  have finish :=
    derivesLrbRegularUnderInitialPair initial second second middle
  exact first.trans (next.trans finish)

private theorem split_at_mem (selected : Nat) :
    ∀ {letters : List Nat}, selected ∈ letters →
      ∃ before after, letters = before ++ selected :: after
  | [], present => False.elim (List.not_mem_nil present)
  | first :: rest, present => by
      rcases List.mem_cons.mp present with equal | later
      · subst first
        exact ⟨[], rest, rfl⟩
      · obtain ⟨before, after, shape⟩ := split_at_mem selected later
        exact ⟨first :: before, after, by simp [shape]⟩

private def appendList (word : Word Nat) (suffix : List Nat) : Word Nat :=
  ⟨word.head, word.tail ++ suffix⟩

private theorem toList_appendList (word : Word Nat) (suffix : List Nat) :
    (appendList word suffix).toList = word.toList ++ suffix := rfl

private theorem derivesAppendList {left right : Word Nat}
    (derivation : Derives basis left right) (suffix : List Nat) :
    Derives basis (appendList left suffix) (appendList right suffix) := by
  cases suffix with
  | nil => simpa [appendList] using derivation
  | cons first rest => exact Derives.appendRight derivation (Word.mk first rest)

private theorem derives_of_lists {left right actualLeft actualRight : Word Nat}
    (leftShape : left.toList = actualLeft.toList)
    (rightShape : right.toList = actualRight.toList)
    (derivation : Derives basis actualLeft actualRight) :
    Derives basis left right := by
  rw [Word.toList_injective leftShape, Word.toList_injective rightShape]
  exact derivation

/-- Safe initial absorption when the initial variable occurs beyond the
literal initial pair.  A fresh initial doubleton fails this premise. -/
theorem derivesGenericInitialGuards (initial second : Nat) (tail : List Nat)
    (initialSeen : initial ∈ tail) :
    Derives basis (initialWord initial second tail)
      ((Word.singleton initial ++ Word.singleton initial) ++
        initialWord initial second tail) := by
  obtain ⟨before, after, shape⟩ := split_at_mem initial initialSeen
  have core := derivesReturnInitialGuards (Word.singleton initial)
    (Word.mk second before)
  have lifted := derivesAppendList core after
  refine derives_of_lists ?_ ?_ lifted <;>
    simp only [toList_appendList, Word.toList_append, Word.toList_singleton,
      toList_initialWord, shape] <;>
    simp only [Word.toList, List.append_assoc, List.cons_append, List.nil_append]

/-- A second variable already in the tail can be copied immediately after
the initial pair, without changing any first occurrence or initial state. -/
theorem derivesSeenSecondPadding (initial second : Nat) (tail : List Nat)
    (secondSeen : second ∈ tail) :
    Derives basis (initialWord initial second tail)
      (initialWord initial second (second :: tail)) := by
  obtain ⟨before, after, shape⟩ := split_at_mem second secondSeen
  cases before with
  | nil =>
      have core := derivesSuffixDuplication (Word.singleton initial)
        (Word.singleton second) (Word.singleton second)
      have lifted := derivesAppendList core after
      refine derives_of_lists ?_ ?_ lifted <;>
        simp only [toList_appendList, Word.toList_append, Word.toList_singleton,
          toList_initialWord, shape] <;>
        simp only [List.cons_append, List.nil_append]
  | cons first rest =>
      have core := derivesSeenSecondAcross (Word.singleton initial)
        (Word.singleton second) (Word.mk first rest)
      have lifted := derivesAppendList core after
      refine derives_of_lists ?_ ?_ lifted <;>
        simp only [toList_appendList, Word.toList_append, Word.toList_singleton,
          toList_initialWord, shape] <;>
        simp only [Word.toList, List.append_assoc, List.cons_append, List.nil_append]

end SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank082.InitialSeed
