import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedMacroWitnesses

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroExpansion

open BinaryPowers OccurrenceWitnesses OccurrenceMacro MacroWitnesses
  CanonicalSquareCover BlockAlignment

/-- Duplicate only the two whole-square macros. All other codes remain literal. -/
def expansion : Nat → Word Nat
  | 0 => ⟨0, [0]⟩
  | 1 => ⟨1, [1]⟩
  | Nat.succ (Nat.succ value) => Word.singleton (value + 2)

def expandLetters (letters : List Nat) : List Nat :=
  letters.flatMap (fun value => (expansion value).toList)

def expandWord (word : Word Nat) : Word Nat := word.bind expansion

theorem expand_nil : expandLetters [] = [] := rfl

theorem expand_cons (value : Nat) (letters : List Nat) :
    expandLetters (value :: letters) = (expansion value).toList ++ expandLetters letters := rfl

theorem expand_append (first second : List Nat) :
    expandLetters (first ++ second) = expandLetters first ++ expandLetters second :=
  List.flatMap_append

theorem expandWord_toList (word : Word Nat) :
    (expandWord word).toList = expandLetters word.toList :=
  Word.toList_bind word expansion

/-- Exact complementary-code projection; this alone is not separator preservation. -/
def complementLetters : List Nat → List Nat
  | [] => []
  | 0 :: rest => complementLetters rest
  | 1 :: rest => complementLetters rest
  | Nat.succ (Nat.succ value) :: rest => (value + 2) :: complementLetters rest

theorem expansion_complement (letters : List Nat) :
    complementLetters (expandLetters letters) = complementLetters letters := by
  induction letters with
  | nil => rfl
  | cons first rest ih =>
      cases first with
      | zero => exact ih
      | succ first =>
          cases first with
          | zero => exact ih
          | succ first => exact congrArg (List.cons (first + 2)) ih

theorem original_sublist (letters : List Nat) :
    letters.Sublist (expandLetters letters) := by
  induction letters with
  | nil => exact List.Sublist.slnil
  | cons first rest ih =>
      cases first with
      | zero => exact List.Sublist.cons₂ 0 (List.Sublist.cons 0 ih)
      | succ first =>
          cases first with
          | zero => exact List.Sublist.cons₂ 1 (List.Sublist.cons 1 ih)
          | succ first => exact List.Sublist.cons₂ (first + 2) ih

/-- The last copy of y remains adjacent to the first copy of the last x. -/
theorem c1_expands (x y : Nat) (letters : List Nat)
    (doubleX : (expansion x).toList = [x, x])
    (doubleY : (expansion y).toList = [y, y])
    (related : C1 x y letters) : C1 x y (expandLetters letters) := by
  obtain ⟨before, middle, after, split⟩ := related
  refine ⟨expandLetters before, x :: (expandLetters middle ++ [y]),
    x :: expandLetters after, ?_⟩
  simp only [split, expand_append, expand_cons, doubleX, doubleY,
    List.cons_append, List.nil_append, List.append_assoc]

theorem c2_expands (x y : Nat) (letters : List Nat)
    (related : C2 x y letters) : C2 x y (expandLetters letters) := by
  exact List.Sublist.trans related (original_sublist letters)

theorem pairRelated_expands (letters : List Nat)
    (related : PairRelated 0 1 letters) : PairRelated 0 1 (expandLetters letters) := by
  have zeroImage : (expansion 0).toList = [0, 0] := rfl
  have oneImage : (expansion 1).toList = [1, 1] := rfl
  rcases related with first | second | third | fourth
  · exact Or.inl (c1_expands 0 1 letters zeroImage oneImage first)
  · exact Or.inr (Or.inl (c1_expands 1 0 letters oneImage zeroImage second))
  · exact Or.inr (Or.inr (Or.inl (c2_expands 0 1 letters third)))
  · exact Or.inr (Or.inr (Or.inr (c2_expands 1 0 letters fourth)))

theorem c1_members (x y : Nat) (letters : List Nat) (related : C1 x y letters) :
    x ∈ letters ∧ y ∈ letters := by
  obtain ⟨before, middle, after, split⟩ := related
  rw [split]
  constructor
  · exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
  · exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr
      (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

theorem c2_members (x y : Nat) (letters : List Nat) (related : C2 x y letters) :
    x ∈ letters ∧ y ∈ letters := by
  have positions : ([x, y, x, y] : List Nat).Sublist letters := related
  constructor
  · exact positions.subset (List.mem_cons.mpr (Or.inl rfl))
  · exact positions.subset (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))

theorem pairRelated_members (x y : Nat) (letters : List Nat)
    (related : PairRelated x y letters) : x ∈ letters ∧ y ∈ letters := by
  rcases related with first | second | third | fourth
  · exact c1_members x y letters first
  · exact (c1_members y x letters second).symm
  · exact c2_members x y letters third
  · exact (c2_members y x letters fourth).symm

theorem expanded_repeated (value : Nat) (letters : List Nat)
    (double : (expansion value).toList = [value, value]) (member : value ∈ letters) :
    2 ≤ (expandLetters letters).count value := by
  obtain ⟨before, after, split⟩ := split_letter value letters member
  have two : ([value, value] : List Nat).count value = 2 := by
    simp only [List.count_cons_self, List.count_nil]
  rw [split, expand_append, expand_cons, double,
    List.count_append, List.count_append, two]
  omega

/-- Multiplicities are derived from actual witnesses, including singleton G1 sides. -/
theorem expanded_ready (word : Word Nat) (related : PairRelated 0 1 word.toList) :
    PairRelated 0 1 (expandWord word).toList ∧
    2 ≤ (expandWord word).toList.count 0 ∧ 2 ≤ (expandWord word).toList.count 1 := by
  have members := pairRelated_members 0 1 word.toList related
  rw [expandWord_toList]
  exact ⟨pairRelated_expands word.toList related,
    expanded_repeated 0 word.toList rfl members.1,
    expanded_repeated 1 word.toList rfl members.2⟩

/-- u^4 -> u^3 -> u^2; the root itself may be a singleton. -/
theorem square_idempotent (root : Word Nat) :
    Derives basis ((root ++ root) ++ (root ++ root)) (root ++ root) := by
  have fourToThree : Derives basis (((root ++ root) ++ root) ++ root)
      ((root ++ root) ++ root) := Derives.appendRight (cube root) root
  have fourToTwo : Derives basis (((root ++ root) ++ root) ++ root)
      (root ++ root) := fourToThree.trans (cube root)
  rw [Word.append_assoc (root ++ root) root root] at fourToTwo
  exact fourToTwo

theorem expansion_image_derives (leftRoot rightRoot : Word Nat) (value : Nat) :
    Derives basis (image leftRoot rightRoot value)
      ((expansion value).bind (image leftRoot rightRoot)) := by
  cases value with
  | zero => exact (square_idempotent leftRoot).symm
  | succ value =>
      cases value with
      | zero => exact (square_idempotent rightRoot).symm
      | succ value => exact Derives.refl _

/-- Pointwise equational changes of nonempty substitution images lift through bind. -/
theorem bind_images_derives (first second : Nat → Word Nat)
    (steps : ∀ value : Nat, Derives basis (first value) (second value)) (word : Word Nat) :
    Derives basis (word.bind first) (word.bind second) := by
  have fold : ∀ (letters : List Nat) (u v : Word Nat), Derives basis u v →
      Derives basis
        (letters.foldl (fun acc value => acc ++ first value) u)
        (letters.foldl (fun acc value => acc ++ second value) v) := by
    intro letters
    induction letters with
    | nil => intro u v step; exact step
    | cons value rest ih =>
        intro u v step
        have next : Derives basis (u ++ first value) (v ++ second value) :=
          (Derives.appendRight step (first value)).trans (Derives.prepend v (steps value))
        exact ih (u ++ first value) (v ++ second value) next
  exact fold word.tail (first word.head) (second word.head) (steps word.head)

theorem bind_bind (word : Word Nat) (first second : Nat → Word Nat) :
    (word.bind first).bind second = word.bind (fun value => (first value).bind second) := by
  apply Word.toList_injective
  simp only [Word.toList_bind]
  generalize word.toList = letters
  induction letters with
  | nil => rfl
  | cons value rest ih =>
      simp only [List.flatMap_cons, List.flatMap_append, ih]

/-- This is an expansion AFTER square substitution, not variable idempotence. -/
theorem expansion_derives (leftRoot rightRoot word : Word Nat) :
    Derives basis (word.bind (image leftRoot rightRoot))
      ((expandWord word).bind (image leftRoot rightRoot)) := by
  rw [expandWord, bind_bind]
  exact bind_images_derives (image leftRoot rightRoot)
    (fun value => (expansion value).bind (image leftRoot rightRoot))
    (expansion_image_derives leftRoot rightRoot) word

theorem expanded_perfect (word : Word Nat) (related : PairRelated 0 1 word.toList) :
    ∃ normal : Word Nat,
      Derives basis (expandWord word) normal ∧ BinaryPerfect.Perfect 0 1 normal := by
  obtain ⟨expandedRelated, zeroRepeated, oneRepeated⟩ := expanded_ready word related
  obtain ⟨normal, step, perfect⟩ := BinaryPerfect.lemma19_2 0 1 (expandWord word)
    (by decide) zeroRepeated oneRepeated expandedRelated
  have zeroMin : min (0 : Nat) 1 = 0 := by decide
  have oneMax : max (0 : Nat) 1 = 1 := by decide
  refine ⟨normal, step, ?_⟩
  simpa only [zeroMin, oneMax] using perfect

/-- Actual disjoint square perfection plus the paper's witnesses now yields a
binary-perfect macro word and an unconditional derivation of its decoding.
Preservation of original separators is deliberately NOT asserted here. -/
theorem generalized_to_macro_perfect (leftRoot rightRoot word : Word Nat)
    (apart : ∀ value ∈ leftRoot.toList, value ∉ rightRoot.toList)
    (leftPerfect : CanonicalPerfect leftRoot word)
    (rightPerfect : CanonicalPerfect rightRoot word)
    (related : GeneralizedRelated leftRoot rightRoot word) :
    ∃ normal : Word Nat,
      Derives basis word (normal.bind (image leftRoot rightRoot)) ∧
      BinaryPerfect.Perfect 0 1 normal := by
  let codes : Word Nat := macroWord leftRoot rightRoot word apart leftPerfect rightPerfect
  have macroRelated : PairRelated 0 1 codes.toList :=
    generalized_related_macroWord leftRoot rightRoot word apart leftPerfect rightPerfect related
  obtain ⟨normal, step, perfect⟩ := expanded_perfect codes macroRelated
  have roundtrip : codes.bind (image leftRoot rightRoot) = word :=
    macroWord_bind leftRoot rightRoot word apart leftPerfect rightPerfect
  have first : Derives basis word ((expandWord codes).bind (image leftRoot rightRoot)) := by
    have raw := expansion_derives leftRoot rightRoot codes
    rw [roundtrip] at raw
    exact raw
  exact ⟨normal, first.trans (Derives.subst step (image leftRoot rightRoot)), perfect⟩

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroExpansion

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroExpansion.expand_nil
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroExpansion.expand_cons
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroExpansion.expand_append
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroExpansion.expandWord_toList
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroExpansion.expansion_complement
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroExpansion.original_sublist
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroExpansion.c1_expands
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroExpansion.c2_expands
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroExpansion.pairRelated_expands
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroExpansion.c1_members
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroExpansion.c2_members
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroExpansion.pairRelated_members
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroExpansion.expanded_repeated
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroExpansion.expanded_ready
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroExpansion.square_idempotent
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroExpansion.expansion_image_derives
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroExpansion.bind_images_derives
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroExpansion.bind_bind
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroExpansion.expansion_derives
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroExpansion.expanded_perfect
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MacroExpansion.generalized_to_macro_perfect
