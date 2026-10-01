import SemigroupBasis.Equational

namespace SemigroupBasis.Examples

open SemigroupBasis

def rectangularBandX : Word Nat := Word.singleton 0
def rectangularBandXX : Word Nat := ⟨0, [0]⟩
def rectangularBandXYX : Word Nat := ⟨0, [1, 0]⟩

def rectangularBandIdempotenceLaw : Identity Nat :=
  ⟨rectangularBandX, rectangularBandXX⟩

def rectangularBandSandwichLaw : Identity Nat :=
  ⟨rectangularBandX, rectangularBandXYX⟩

/-- The exact rectangular-band basis `x = xx`, `x = xyx`. -/
def rectangularBandBasis : List (Identity Nat) :=
  [rectangularBandIdempotenceLaw, rectangularBandSandwichLaw]

private def rectangularBandInstantiateTwo
    (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

theorem rectangularBandDerivesIdempotenceExpansion (u : Word Nat) :
    Derives rectangularBandBasis u (u ++ u) := by
  have hbase :
      Derives rectangularBandBasis rectangularBandX rectangularBandXX :=
    Derives.fromBasis (e := rectangularBandIdempotenceLaw) <|
      List.Mem.head _
  have h :=
    Derives.subst hbase (rectangularBandInstantiateTwo u u)
  simpa [rectangularBandBasis, rectangularBandIdempotenceLaw,
    rectangularBandX, rectangularBandXX,
    rectangularBandInstantiateTwo, Word.bind, Word.append,
    Word.singleton] using h

theorem rectangularBandDerivesIdempotenceContraction (u : Word Nat) :
    Derives rectangularBandBasis (u ++ u) u :=
  Derives.symm (rectangularBandDerivesIdempotenceExpansion u)

theorem rectangularBandDerivesSandwichExpansion
    (u v : Word Nat) :
    Derives rectangularBandBasis u ((u ++ v) ++ u) := by
  have hbase :
      Derives rectangularBandBasis rectangularBandX rectangularBandXYX :=
    Derives.fromBasis (e := rectangularBandSandwichLaw) <|
      List.Mem.tail _ (List.Mem.head _)
  have h :=
    Derives.subst hbase (rectangularBandInstantiateTwo u v)
  simpa [rectangularBandBasis, rectangularBandSandwichLaw,
    rectangularBandX, rectangularBandXYX,
    rectangularBandInstantiateTwo, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using h

theorem rectangularBandDerivesSandwichContraction
    (u v : Word Nat) :
    Derives rectangularBandBasis ((u ++ v) ++ u) u :=
  Derives.symm (rectangularBandDerivesSandwichExpansion u v)

/-- Delete an arbitrary nonempty middle block while retaining the first and
last nonempty blocks. -/
theorem rectangularBandDerivesDeleteMiddle
    (u v w : Word Nat) :
    Derives rectangularBandBasis ((u ++ v) ++ w) (u ++ w) := by
  have expandFinal :=
    Derives.prepend (u ++ v)
      (rectangularBandDerivesSandwichExpansion w u)
  have contractPrefix :=
    Derives.appendRight
      (rectangularBandDerivesSandwichContraction u (v ++ w)) w
  exact Derives.trans
    (by simpa [Word.append_assoc] using expandFinal)
    (by simpa [Word.append_assoc] using contractPrefix)

/-- The final variable of a nonempty semigroup word. -/
def rectangularBandFinal (word : Word Nat) : Nat :=
  word.tail.getLastD word.head

/-- The two-letter endpoint word. A singleton input is expanded to a square;
the canonical normal form below contracts that square again. -/
def rectangularBandEndpointPair (word : Word Nat) : Word Nat :=
  Word.singleton word.head ++
    Word.singleton (rectangularBandFinal word)

private theorem rectangularBandDerivesEndpointPairList :
    ∀ (head : Nat) (tail : List Nat),
      Derives rectangularBandBasis
        (Word.mk head tail)
        (Word.singleton head ++
          Word.singleton (tail.getLastD head))
  | head, [] => by
      simpa [Word.singleton, Word.append] using
        rectangularBandDerivesIdempotenceExpansion
          (Word.singleton head)
  | head, [final] => by
      simpa [Word.singleton, Word.append] using
        (Derives.refl (Word.mk head [final]) :
          Derives rectangularBandBasis
            (Word.mk head [final]) (Word.mk head [final]))
  | head, middle :: next :: rest => by
      have first :=
        rectangularBandDerivesDeleteMiddle
          (Word.singleton head)
          (Word.singleton middle)
          (Word.mk next rest)
      have remaining :=
        rectangularBandDerivesEndpointPairList head (next :: rest)
      exact Derives.trans
        (by
          simpa [Word.singleton, Word.append, Word.append_assoc]
            using first)
        (by
          simpa [List.getLastD_cons] using remaining)
termination_by
  _ tail => tail.length

/-- Every nonempty word derives to its ordered first/last pair. -/
theorem rectangularBandDerivesEndpointPair (word : Word Nat) :
    Derives rectangularBandBasis word
      (rectangularBandEndpointPair word) := by
  cases word with
  | mk head tail =>
      simpa [rectangularBandEndpointPair, rectangularBandFinal] using
        rectangularBandDerivesEndpointPairList head tail

/-- Canonical rectangular-band word: the first and last variables, contracted
to a singleton exactly when they coincide. -/
def rectangularBandNormal (word : Word Nat) : Word Nat :=
  if word.head = rectangularBandFinal word then
    Word.singleton word.head
  else
    rectangularBandEndpointPair word

theorem rectangularBandNormal_eq_singleton
    (word : Word Nat)
    (same : word.head = rectangularBandFinal word) :
    rectangularBandNormal word = Word.singleton word.head := by
  simp [rectangularBandNormal, same]

theorem rectangularBandNormal_eq_endpointPair
    (word : Word Nat)
    (different : word.head ≠ rectangularBandFinal word) :
    rectangularBandNormal word =
      rectangularBandEndpointPair word := by
  simp [rectangularBandNormal, different]

/-- Unconditional rectangular-band normalization for every nonempty word. -/
theorem rectangularBandDerivesNormal (word : Word Nat) :
    Derives rectangularBandBasis word (rectangularBandNormal word) := by
  have pair := rectangularBandDerivesEndpointPair word
  by_cases same : word.head = rectangularBandFinal word
  · have collapse :=
      rectangularBandDerivesIdempotenceContraction
        (Word.singleton word.head)
    exact Derives.trans pair <| by
      simpa [rectangularBandNormal, rectangularBandEndpointPair,
        same] using collapse
  · simpa [rectangularBandNormal, same] using pair

theorem rectangularBandNormal_eq_of_endpoints_eq
    (left right : Word Nat)
    (heads : left.head = right.head)
    (finals :
      rectangularBandFinal left = rectangularBandFinal right) :
    rectangularBandNormal left = rectangularBandNormal right := by
  unfold rectangularBandNormal rectangularBandEndpointPair
  rw [heads, finals]

/-- Words with equal ordered first/last pairs are equationally equivalent
under the two rectangular-band laws. -/
theorem rectangularBandDerivesSameEndpoints
    (left right : Word Nat)
    (heads : left.head = right.head)
    (finals :
      rectangularBandFinal left = rectangularBandFinal right) :
    Derives rectangularBandBasis left right := by
  have middle :
      Derives rectangularBandBasis
        (rectangularBandNormal left)
        (rectangularBandNormal right) := by
    rw [rectangularBandNormal_eq_of_endpoints_eq
      left right heads finals]
    exact Derives.refl _
  exact Derives.trans
    (rectangularBandDerivesNormal left) <|
    Derives.trans middle <|
      Derives.symm (rectangularBandDerivesNormal right)

end SemigroupBasis.Examples
