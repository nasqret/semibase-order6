import SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroupSyntax

namespace SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroup

open SemigroupBasis

def displayedSwapSameSource
    (x a y b c d : Word Nat) : Word Nat :=
  x ++ a ++ y ++ b ++ x ++ y ++ c ++ x ++ d ++ y

private def same1
    (x a y b c d : Word Nat) : Word Nat :=
  x ++ a ++ y ++ b ++ x ++ y ++ x ++ x ++ c ++ x ++ d ++ y

private def same2
    (x a y b c d : Word Nat) : Word Nat :=
  x ++ a ++ y ++ b ++ x ++ y ++ x ++ y ++ y ++ x ++ c ++ x ++ d ++ y

private def same3
    (x a y b c d : Word Nat) : Word Nat :=
  x ++ a ++ y ++ b ++ y ++ y ++ x ++ y ++ x ++ y ++ y ++ x ++
    c ++ x ++ d ++ y

private def same4
    (x a y b c d : Word Nat) : Word Nat :=
  x ++ a ++ y ++ x ++ a ++ y ++ x ++ a ++ y ++ b ++ y ++ y ++
    x ++ y ++ x ++ y ++ y ++ x ++ c ++ x ++ d ++ y

private def same5
    (x a y b c d : Word Nat) : Word Nat :=
  x ++ a ++ y ++ x ++ a ++ y ++ x ++ a ++ y ++ b ++ y ++ y ++
    y ++ x ++ c ++ x ++ d ++ y

private def same6
    (x a y b c d : Word Nat) : Word Nat :=
  x ++ a ++ y ++ b ++ y ++ y ++ y ++ x ++ c ++ x ++ d ++ y

def displayedSwapSameTarget
    (x a y b c d : Word Nat) : Word Nat :=
  x ++ a ++ y ++ b ++ y ++ x ++ c ++ x ++ d ++ y

/-- Same-orientation displayed guarded swap, with all four internal gaps
arbitrary nonempty words:
`x a y b x y c x d y = x a y b y x c x d y`. -/
theorem derivesDisplayedSwapSame
    (x a y b c d : Word Nat) :
    Derives basis
      (displayedSwapSameSource x a y b c d)
      (displayedSwapSameTarget x a y b c d) := by
  have first :
      Derives basis
        (displayedSwapSameSource x a y b c d)
        (same1 x a y b c d) := by
    simpa [displayedSwapSameSource, same1, Word.append_assoc] using
      Derives.appendRight
        (derivesRegularExpansion
          x (a ++ y ++ b ++ x ++ y) c)
        (d ++ y)
  have second :
      Derives basis (same1 x a y b c d) (same2 x a y b c d) := by
    simpa [same1, same2, Word.append_assoc] using
      Derives.prepend (x ++ a)
        (derivesRegularExpansion
          y (b ++ x ++ y ++ x) (x ++ c ++ x ++ d))
  have third :
      Derives basis (same2 x a y b c d) (same3 x a y b c d) := by
    simpa [same2, same3, Word.append_assoc] using
      Derives.appendRight
        (Derives.prepend (x ++ a)
          (derivesRegularExpansion y b x))
        (x ++ y ++ y ++ x ++ c ++ x ++ d ++ y)
  have fourth :
      Derives basis (same3 x a y b c d) (same4 x a y b c d) := by
    simpa [same3, same4, Word.append_assoc] using
      Derives.appendRight
        (derivesPowerExpansion (x ++ a ++ y))
        (b ++ y ++ y ++ x ++ y ++ x ++ y ++ y ++
          x ++ c ++ x ++ d ++ y)
  have fifth :
      Derives basis (same4 x a y b c d) (same5 x a y b c d) := by
    simpa [same4, same5, Word.append_assoc] using
      Derives.appendRight
        (Derives.prepend (x ++ a)
          (derivesRegularContraction
            (y ++ x)
            (a ++ y ++ x ++ a ++ y ++ b ++ y)
            y))
        (c ++ x ++ d ++ y)
  have sixth :
      Derives basis (same5 x a y b c d) (same6 x a y b c d) := by
    simpa [same5, same6, Word.append_assoc] using
      Derives.appendRight
        (derivesPowerContraction (x ++ a ++ y))
        (b ++ y ++ y ++ y ++ x ++ c ++ x ++ d ++ y)
  have seventh :
      Derives basis
        (same6 x a y b c d)
        (displayedSwapSameTarget x a y b c d) := by
    simpa [same6, displayedSwapSameTarget, Word.append_assoc] using
      Derives.appendRight
        (Derives.prepend (x ++ a ++ y ++ b)
          (derivesPowerContraction y))
        (x ++ c ++ x ++ d ++ y)
  exact first.trans <|
    second.trans <|
      third.trans <|
        fourth.trans <|
          fifth.trans <|
            sixth.trans seventh

def displayedSwapMixedSource
    (x a y b c d : Word Nat) : Word Nat :=
  x ++ a ++ y ++ b ++ x ++ y ++ c ++ y ++ d ++ x

private def mixed1
    (x a y b c d : Word Nat) : Word Nat :=
  x ++ a ++ y ++ b ++ x ++ y ++ x ++ x ++ c ++ y ++ d ++ x

private def mixed2
    (x a y b c d : Word Nat) : Word Nat :=
  x ++ a ++ y ++ b ++ x ++ y ++ x ++ x ++ c ++ y ++ x ++ x ++ d ++ x

private def mixed3
    (x a y b c d : Word Nat) : Word Nat :=
  x ++ a ++ y ++ b ++ y ++ y ++ x ++ y ++ x ++ x ++ c ++ y ++
    x ++ x ++ d ++ x

private def mixed4
    (x a y b c d : Word Nat) : Word Nat :=
  x ++ a ++ y ++ x ++ a ++ y ++ x ++ a ++ y ++ b ++ y ++ y ++
    x ++ y ++ x ++ x ++ c ++ y ++ x ++ x ++ d ++ x

private def mixed5
    (x a y b c d : Word Nat) : Word Nat :=
  x ++ a ++ y ++ x ++ a ++ y ++ x ++ a ++ y ++ b ++ y ++ x ++
    c ++ y ++ x ++ x ++ d ++ x

private def mixed6
    (x a y b c d : Word Nat) : Word Nat :=
  x ++ a ++ y ++ b ++ y ++ x ++ c ++ y ++ x ++ x ++ d ++ x

def displayedSwapMixedTarget
    (x a y b c d : Word Nat) : Word Nat :=
  x ++ a ++ y ++ b ++ y ++ x ++ c ++ y ++ d ++ x

/-- Mixed-orientation displayed guarded swap:
`x a y b x y c y d x = x a y b y x c y d x`. -/
theorem derivesDisplayedSwapMixed
    (x a y b c d : Word Nat) :
    Derives basis
      (displayedSwapMixedSource x a y b c d)
      (displayedSwapMixedTarget x a y b c d) := by
  have first :
      Derives basis
        (displayedSwapMixedSource x a y b c d)
        (mixed1 x a y b c d) := by
    simpa [displayedSwapMixedSource, mixed1, Word.append_assoc] using
      derivesRegularExpansion
        x (a ++ y ++ b ++ x ++ y) (c ++ y ++ d)
  have second :
      Derives basis (mixed1 x a y b c d) (mixed2 x a y b c d) := by
    simpa [mixed1, mixed2, Word.append_assoc] using
      derivesRegularExpansion
        x (a ++ y ++ b ++ x ++ y ++ x ++ x ++ c ++ y) d
  have third :
      Derives basis (mixed2 x a y b c d) (mixed3 x a y b c d) := by
    simpa [mixed2, mixed3, Word.append_assoc] using
      Derives.appendRight
        (Derives.prepend (x ++ a)
          (derivesRegularExpansion y b x))
        (x ++ x ++ c ++ y ++ x ++ x ++ d ++ x)
  have fourth :
      Derives basis (mixed3 x a y b c d) (mixed4 x a y b c d) := by
    simpa [mixed3, mixed4, Word.append_assoc] using
      Derives.appendRight
        (derivesPowerExpansion (x ++ a ++ y))
        (b ++ y ++ y ++ x ++ y ++ x ++ x ++ c ++ y ++
          x ++ x ++ d ++ x)
  have fifth :
      Derives basis (mixed4 x a y b c d) (mixed5 x a y b c d) := by
    simpa [mixed4, mixed5, Word.append_assoc] using
      Derives.appendRight
        (Derives.prepend (x ++ a)
          (derivesRegularContraction
            (y ++ x)
            (a ++ y ++ x ++ a ++ y ++ b ++ y)
            (x ++ c)))
        (x ++ d ++ x)
  have sixth :
      Derives basis (mixed5 x a y b c d) (mixed6 x a y b c d) := by
    simpa [mixed5, mixed6, Word.append_assoc] using
      Derives.appendRight
        (derivesPowerContraction (x ++ a ++ y))
        (b ++ y ++ x ++ c ++ y ++ x ++ x ++ d ++ x)
  have seventh :
      Derives basis
        (mixed6 x a y b c d)
        (displayedSwapMixedTarget x a y b c d) := by
    simpa [mixed6, displayedSwapMixedTarget, Word.append_assoc] using
      derivesRegularContraction
        x (a ++ y ++ b ++ y ++ x ++ c ++ y) d
  exact first.trans <|
    second.trans <|
      third.trans <|
        fourth.trans <|
          fifth.trans <|
            sixth.trans seventh

end SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroup
