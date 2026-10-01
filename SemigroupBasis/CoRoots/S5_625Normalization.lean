import SemigroupBasis.CoRoots.S5_636Normalization

namespace SemigroupBasis.CoRoots.S5_625

open SemigroupBasis
open SemigroupBasis.Examples

def s5_625XX : Word Nat := ⟨0, [0]⟩
def s5_625XXXX : Word Nat := ⟨0, [0, 0, 0]⟩
def s5_625XY : Word Nat := ⟨0, [1]⟩
def s5_625XYYY : Word Nat := ⟨0, [1, 1, 1]⟩
def s5_625XXY : Word Nat := ⟨0, [0, 1]⟩
def s5_625XYX : Word Nat := ⟨0, [1, 0]⟩

def s5_625PowerLaw : Identity Nat :=
  ⟨s5_625XX, s5_625XXXX⟩

def s5_625TailPowerLaw : Identity Nat :=
  ⟨s5_625XY, s5_625XYYY⟩

def s5_625GatherLaw : Identity Nat :=
  ⟨s5_625XXY, s5_625XYX⟩

/-- The exact S5_625 basis `xx = xxxx`, `xy = xyyy`, `xxy = xyx`. -/
def s5_625Basis : List (Identity Nat) :=
  [s5_625PowerLaw, s5_625TailPowerLaw, s5_625GatherLaw]

private def s5_625Instantiate
    (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

/-- Three copies of a nonempty block contract to one copy after any
nonempty prefix. -/
theorem s5_625DerivesTailTripleContraction
    (stem block : Word Nat) :
    Derives s5_625Basis
      (((stem ++ block) ++ block) ++ block)
      (stem ++ block) := by
  have base :
      Derives s5_625Basis s5_625XYYY s5_625XY :=
    Derives.symm <|
      Derives.fromBasis (e := s5_625TailPowerLaw) <|
        List.Mem.tail _ (List.Mem.head _)
  have instantiated :=
    Derives.subst base (s5_625Instantiate stem block)
  simpa [s5_625Basis, s5_625TailPowerLaw,
    s5_625XYYY, s5_625XY, s5_625Instantiate,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      instantiated

/-- Every axiom of the S5_636 two-law block basis occurs in S5_625. -/
theorem s5_625DerivesS5_636Axiom
    (identity : Identity Nat)
    (member :
      identity ∈
        SemigroupBasis.CoRoots.S5_636.s5_636Basis) :
    Derives s5_625Basis identity.lhs identity.rhs := by
  simp only [SemigroupBasis.CoRoots.S5_636.s5_636Basis,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact Derives.fromBasis (List.Mem.head _)
  · exact Derives.fromBasis <|
      List.Mem.tail _ <| List.Mem.tail _ (List.Mem.head _)

def s5_625WordOfCons
    (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def s5_625Initial : List Nat → Nat
  | [] => 0
  | head :: _ => head

/-- Normal forms behind the initial block have one or two copies of each
variable, in first-occurrence order. -/
inductive S5_625TailNormal : List Nat → Prop
  | nil : S5_625TailNormal []
  | single (x : Nat) (xs : List Nat) :
      S5_625TailNormal xs →
      x ∉ xs →
      S5_625TailNormal (x :: xs)
  | double (x : Nat) (xs : List Nat) :
      S5_625TailNormal xs →
      x ∉ xs →
      S5_625TailNormal (x :: x :: xs)

/-- The first block has one, two, or three copies. Every later block has one
or two copies. -/
inductive S5_625Normal : List Nat → Prop
  | single (x : Nat) (xs : List Nat) :
      S5_625TailNormal xs →
      x ∉ xs →
      S5_625Normal (x :: xs)
  | double (x : Nat) (xs : List Nat) :
      S5_625TailNormal xs →
      x ∉ xs →
      S5_625Normal (x :: x :: xs)
  | triple (x : Nat) (xs : List Nat) :
      S5_625TailNormal xs →
      x ∉ xs →
      S5_625Normal (x :: x :: x :: xs)

theorem S5_625TailNormal.toS5_636Normal
    {xs : List Nat} (normal : S5_625TailNormal xs) :
    SemigroupBasis.CoRoots.S5_636.S5_636Normal xs := by
  induction normal with
  | nil =>
      exact .nil
  | single x xs _ xNotMem induction =>
      exact .single x xs induction xNotMem
  | double x xs _ xNotMem induction =>
      exact .double x xs induction xNotMem

theorem S5_625Normal.toS5_636Normal
    {xs : List Nat} (normal : S5_625Normal xs) :
    SemigroupBasis.CoRoots.S5_636.S5_636Normal xs := by
  cases normal with
  | single x xs tailNormal xNotMem =>
      exact .single x xs tailNormal.toS5_636Normal xNotMem
  | double x xs tailNormal xNotMem =>
      exact .double x xs tailNormal.toS5_636Normal xNotMem
  | triple x xs tailNormal xNotMem =>
      exact .triple x xs tailNormal.toS5_636Normal xNotMem

private theorem s5_625ContractTailTriple
    (head x : Nat) (stem suffix : List Nat) :
    Derives s5_625Basis
      (s5_625WordOfCons head
        (stem ++ x :: x :: x :: suffix))
      (s5_625WordOfCons head
        (stem ++ x :: suffix)) := by
  let prefixWord := s5_625WordOfCons head stem
  cases suffix with
  | nil =>
      simpa [prefixWord, s5_625WordOfCons,
        Word.append, Word.singleton, Word.append_assoc] using
          s5_625DerivesTailTripleContraction
            prefixWord (Word.singleton x)
  | cons y ys =>
      have contracted :=
        Derives.appendRight
          (s5_625DerivesTailTripleContraction
            prefixWord (Word.singleton x))
          (s5_625WordOfCons y ys)
      simpa [prefixWord, s5_625WordOfCons,
        Word.append, Word.singleton, Word.append_assoc] using contracted

/-- Collapse every triple block behind a fixed nonempty prefix. The operation
preserves support and first-occurrence order. -/
private theorem s5_625CollapseTail
    {xs : List Nat}
    (normal :
      SemigroupBasis.CoRoots.S5_636.S5_636Normal xs) :
    ∀ head stem,
      ∃ ys,
        S5_625TailNormal ys ∧
        (∀ z, z ∈ ys ↔ z ∈ xs) ∧
        Derives s5_625Basis
          (s5_625WordOfCons head (stem ++ xs))
          (s5_625WordOfCons head (stem ++ ys)) := by
  induction normal with
  | nil =>
      intro head stem
      exact ⟨[], .nil, by simp, Derives.refl _⟩
  | single x xs normalTail xNotMem induction =>
      intro head stem
      obtain ⟨ys, targetNormal, support, derivation⟩ :=
        induction head (stem ++ [x])
      have xNotMemTarget : x ∉ ys := by
        intro member
        exact xNotMem ((support x).mp member)
      refine ⟨x :: ys,
        .single x ys targetNormal xNotMemTarget, ?_, ?_⟩
      · intro z
        simp only [List.mem_cons]
        rw [support z]
      · simpa [List.append_assoc] using derivation
  | double x xs normalTail xNotMem induction =>
      intro head stem
      obtain ⟨ys, targetNormal, support, derivation⟩ :=
        induction head (stem ++ [x, x])
      have xNotMemTarget : x ∉ ys := by
        intro member
        exact xNotMem ((support x).mp member)
      refine ⟨x :: x :: ys,
        .double x ys targetNormal xNotMemTarget, ?_, ?_⟩
      · intro z
        simp only [List.mem_cons]
        rw [support z]
      · simpa [List.append_assoc] using derivation
  | triple x xs normalTail xNotMem induction =>
      intro head stem
      obtain ⟨ys, targetNormal, support, derivation⟩ :=
        induction head (stem ++ [x])
      have xNotMemTarget : x ∉ ys := by
        intro member
        exact xNotMem ((support x).mp member)
      refine ⟨x :: ys,
        .single x ys targetNormal xNotMemTarget, ?_, ?_⟩
      · intro z
        simp only [List.mem_cons]
        rw [support z]
        simp
      · exact Derives.trans
          (s5_625ContractTailTriple head x stem xs)
          (by simpa [List.append_assoc] using derivation)

private theorem s5_625CollapseS5_636Normal
    {head : Nat} {tail : List Nat}
    (normal :
      SemigroupBasis.CoRoots.S5_636.S5_636Normal
        (head :: tail)) :
    ∃ targetTail,
      S5_625Normal (head :: targetTail) ∧
      Derives s5_625Basis
        (s5_625WordOfCons head tail)
        (s5_625WordOfCons head targetTail) := by
  cases normal with
  | single x xs normalTail xNotMem =>
      obtain ⟨ys, targetNormal, support, derivation⟩ :=
        s5_625CollapseTail normalTail head []
      have xNotMemTarget : head ∉ ys := by
        intro member
        exact xNotMem ((support head).mp member)
      exact ⟨ys, .single head ys targetNormal xNotMemTarget, by
        simpa using derivation⟩
  | double x xs normalTail xNotMem =>
      obtain ⟨ys, targetNormal, support, derivation⟩ :=
        s5_625CollapseTail normalTail head [head]
      have xNotMemTarget : head ∉ ys := by
        intro member
        exact xNotMem ((support head).mp member)
      exact ⟨head :: ys, .double head ys targetNormal xNotMemTarget, by
        simpa using derivation⟩
  | triple x xs normalTail xNotMem =>
      obtain ⟨ys, targetNormal, support, derivation⟩ :=
        s5_625CollapseTail normalTail head [head, head]
      have xNotMemTarget : head ∉ ys := by
        intro member
        exact xNotMem ((support head).mp member)
      exact ⟨head :: head :: ys,
        .triple head ys targetNormal xNotMemTarget, by
          simpa using derivation⟩

/-- Every nonempty word derives to a head-tail block normal form. -/
theorem s5_625DerivesNormal (word : Word Nat) :
    ∃ head tail,
      S5_625Normal (head :: tail) ∧
      Derives s5_625Basis word
        (s5_625WordOfCons head tail) := by
  have base :=
    SemigroupBasis.CoRoots.S5_636.s5_636DerivesNormal word
  cases normalEq :
      SemigroupBasis.CoRoots.S5_636.s5_636NormalList
        word.toList with
  | nil =>
      exact False.elim <|
        SemigroupBasis.CoRoots.S5_636.s5_636NormalList_cons_ne_nil
          word.head word.tail <| by
            simpa [Word.toList] using normalEq
  | cons head tail =>
      rw [normalEq] at base
      have normal :
          SemigroupBasis.CoRoots.S5_636.S5_636Normal
            (head :: tail) := by
        rw [← normalEq]
        exact
          SemigroupBasis.CoRoots.S5_636.s5_636NormalList_normal
            word.toList
      obtain ⟨targetTail, targetNormal, collapsed⟩ :=
        s5_625CollapseS5_636Normal normal
      refine ⟨head, targetTail, targetNormal, ?_⟩
      exact Derives.trans
        (base.transport s5_625DerivesS5_636Axiom) collapsed

private theorem s5_625Mem_firstOccurrenceSequence_iff
    (z : Nat) :
    ∀ xs : List Nat,
      z ∈ firstOccurrenceSequence xs ↔ z ∈ xs
  | [] => by simp [firstOccurrenceSequence]
  | x :: xs => by
      by_cases hzx : z = x
      · subst z
        simp [firstOccurrenceSequence]
      · simp [firstOccurrenceSequence, hzx,
          s5_625Mem_firstOccurrenceSequence_iff z xs]

private theorem s5_625FirstOccurrences_single
    {x : Nat} {xs : List Nat} (notMem : x ∉ xs) :
    firstOccurrenceSequence (x :: xs) =
      x :: firstOccurrenceSequence xs := by
  simp only [firstOccurrenceSequence]
  congr 1
  apply List.filter_eq_self.mpr
  intro z member
  simp only [decide_eq_true_eq]
  intro equal
  subst z
  exact notMem <|
    (s5_625Mem_firstOccurrenceSequence_iff x xs).mp member

private theorem s5_625FirstOccurrences_double
    {x : Nat} {xs : List Nat} (notMem : x ∉ xs) :
    firstOccurrenceSequence (x :: x :: xs) =
      x :: firstOccurrenceSequence xs := by
  rw [firstOccurrenceSequence,
    s5_625FirstOccurrences_single notMem]
  simp
  intro a member equal
  subst a
  exact notMem <|
    (s5_625Mem_firstOccurrenceSequence_iff x xs).mp member

private theorem s5_625FirstOccurrences_triple
    {x : Nat} {xs : List Nat} (notMem : x ∉ xs) :
    firstOccurrenceSequence (x :: x :: x :: xs) =
      x :: firstOccurrenceSequence xs := by
  rw [firstOccurrenceSequence, firstOccurrenceSequence,
    s5_625FirstOccurrences_single notMem]
  simp
  intro a member equal
  subst a
  exact notMem <|
    (s5_625Mem_firstOccurrenceSequence_iff x xs).mp member

private theorem s5_625TailParity_single
    {x : Nat} {xs ys : List Nat}
    (xNotMemXs : x ∉ xs) (xNotMemYs : x ∉ ys)
    (parity :
      ∀ z,
        (x :: xs).count z % 2 =
          (x :: ys).count z % 2) :
    ∀ z, xs.count z % 2 = ys.count z % 2 := by
  intro z
  by_cases hzx : z = x
  · subst z
    simp [List.count_eq_zero.mpr xNotMemXs,
      List.count_eq_zero.mpr xNotMemYs]
  · simpa [List.count_cons_of_ne (Ne.symm hzx)] using parity z

private theorem s5_625TailParity_double
    {x : Nat} {xs ys : List Nat}
    (xNotMemXs : x ∉ xs) (xNotMemYs : x ∉ ys)
    (parity :
      ∀ z,
        (x :: x :: xs).count z % 2 =
          (x :: x :: ys).count z % 2) :
    ∀ z, xs.count z % 2 = ys.count z % 2 := by
  intro z
  by_cases hzx : z = x
  · subst z
    simp [List.count_eq_zero.mpr xNotMemXs,
      List.count_eq_zero.mpr xNotMemYs]
  · simpa [List.count_cons_of_ne (Ne.symm hzx)] using parity z

private theorem s5_625TailParity_triple
    {x : Nat} {xs ys : List Nat}
    (xNotMemXs : x ∉ xs) (xNotMemYs : x ∉ ys)
    (parity :
      ∀ z,
        (x :: x :: x :: xs).count z % 2 =
          (x :: x :: x :: ys).count z % 2) :
    ∀ z, xs.count z % 2 = ys.count z % 2 := by
  intro z
  by_cases hzx : z = x
  · subst z
    simp [List.count_eq_zero.mpr xNotMemXs,
      List.count_eq_zero.mpr xNotMemYs]
  · simpa [List.count_cons_of_ne (Ne.symm hzx)] using parity z

theorem s5_625TailNormal_eq_of_invariants
    {xs ys : List Nat}
    (normalXs : S5_625TailNormal xs)
    (normalYs : S5_625TailNormal ys)
    (order :
      firstOccurrenceSequence xs =
        firstOccurrenceSequence ys)
    (parity :
      ∀ z, xs.count z % 2 = ys.count z % 2) :
    xs = ys := by
  induction normalXs generalizing ys with
  | nil =>
      cases normalYs with
      | nil => rfl
      | single y ys _ yNotMem =>
          rw [s5_625FirstOccurrences_single yNotMem] at order
          simp [firstOccurrenceSequence] at order
      | double y ys _ yNotMem =>
          rw [s5_625FirstOccurrences_double yNotMem] at order
          simp [firstOccurrenceSequence] at order
  | single x xs normalTail xNotMem induction =>
      cases normalYs with
      | nil =>
          rw [s5_625FirstOccurrences_single xNotMem] at order
          simp [firstOccurrenceSequence] at order
      | single y ys normalRight yNotMem =>
          rw [s5_625FirstOccurrences_single xNotMem,
            s5_625FirstOccurrences_single yNotMem] at order
          have heads := (List.cons.inj order).1
          subst y
          congr 1
          exact induction normalRight (List.cons.inj order).2 <|
            s5_625TailParity_single xNotMem yNotMem parity
      | double y ys normalRight yNotMem =>
          rw [s5_625FirstOccurrences_single xNotMem,
            s5_625FirstOccurrences_double yNotMem] at order
          have heads := (List.cons.inj order).1
          subst y
          have count := parity x
          simp [List.count_eq_zero.mpr xNotMem,
            List.count_eq_zero.mpr yNotMem] at count
  | double x xs normalTail xNotMem induction =>
      cases normalYs with
      | nil =>
          rw [s5_625FirstOccurrences_double xNotMem] at order
          simp [firstOccurrenceSequence] at order
      | single y ys normalRight yNotMem =>
          rw [s5_625FirstOccurrences_double xNotMem,
            s5_625FirstOccurrences_single yNotMem] at order
          have heads := (List.cons.inj order).1
          subst y
          have count := parity x
          simp [List.count_eq_zero.mpr xNotMem,
            List.count_eq_zero.mpr yNotMem] at count
      | double y ys normalRight yNotMem =>
          rw [s5_625FirstOccurrences_double xNotMem,
            s5_625FirstOccurrences_double yNotMem] at order
          have heads := (List.cons.inj order).1
          subst y
          congr 2
          exact induction normalRight (List.cons.inj order).2 <|
            s5_625TailParity_double xNotMem yNotMem parity

/-- Head-tail normal forms are determined by first-occurrence order, the
three-state head exponent, and the parity of every multiplicity. -/
theorem s5_625Normal_eq_of_invariants
    {xs ys : List Nat}
    (normalXs : S5_625Normal xs)
    (normalYs : S5_625Normal ys)
    (order :
      firstOccurrenceSequence xs =
        firstOccurrenceSequence ys)
    (headState :
      SemigroupBasis.CoRoots.S5_636.s5_636Exponent
          (xs.count (s5_625Initial xs)) =
        SemigroupBasis.CoRoots.S5_636.s5_636Exponent
          (ys.count (s5_625Initial ys)))
    (parity :
      ∀ z, xs.count z % 2 = ys.count z % 2) :
    xs = ys := by
  cases normalXs with
  | single x xs normalTail xNotMem =>
      cases normalYs with
      | single y ys normalRight yNotMem =>
          rw [s5_625FirstOccurrences_single xNotMem,
            s5_625FirstOccurrences_single yNotMem] at order
          have heads := (List.cons.inj order).1
          subst y
          congr 1
          exact s5_625TailNormal_eq_of_invariants
            normalTail normalRight (List.cons.inj order).2 <|
              s5_625TailParity_single xNotMem yNotMem parity
      | double y ys normalRight yNotMem =>
          rw [s5_625FirstOccurrences_single xNotMem,
            s5_625FirstOccurrences_double yNotMem] at order
          have heads := (List.cons.inj order).1
          subst y
          have count := headState
          simp [List.count_eq_zero.mpr xNotMem,
            List.count_eq_zero.mpr yNotMem,
            s5_625Initial,
            SemigroupBasis.CoRoots.S5_636.s5_636Exponent,
            periodTwoFromTwoExponent] at count
      | triple y ys normalRight yNotMem =>
          rw [s5_625FirstOccurrences_single xNotMem,
            s5_625FirstOccurrences_triple yNotMem] at order
          have heads := (List.cons.inj order).1
          subst y
          have count := headState
          simp [List.count_eq_zero.mpr xNotMem,
            List.count_eq_zero.mpr yNotMem,
            s5_625Initial,
            SemigroupBasis.CoRoots.S5_636.s5_636Exponent,
            periodTwoFromTwoExponent] at count
  | double x xs normalTail xNotMem =>
      cases normalYs with
      | single y ys normalRight yNotMem =>
          rw [s5_625FirstOccurrences_double xNotMem,
            s5_625FirstOccurrences_single yNotMem] at order
          have heads := (List.cons.inj order).1
          subst y
          have count := headState
          simp [List.count_eq_zero.mpr xNotMem,
            List.count_eq_zero.mpr yNotMem,
            s5_625Initial,
            SemigroupBasis.CoRoots.S5_636.s5_636Exponent,
            periodTwoFromTwoExponent] at count
      | double y ys normalRight yNotMem =>
          rw [s5_625FirstOccurrences_double xNotMem,
            s5_625FirstOccurrences_double yNotMem] at order
          have heads := (List.cons.inj order).1
          subst y
          congr 2
          exact s5_625TailNormal_eq_of_invariants
            normalTail normalRight (List.cons.inj order).2 <|
              s5_625TailParity_double xNotMem yNotMem parity
      | triple y ys normalRight yNotMem =>
          rw [s5_625FirstOccurrences_double xNotMem,
            s5_625FirstOccurrences_triple yNotMem] at order
          have heads := (List.cons.inj order).1
          subst y
          have count := headState
          simp [List.count_eq_zero.mpr xNotMem,
            List.count_eq_zero.mpr yNotMem,
            s5_625Initial,
            SemigroupBasis.CoRoots.S5_636.s5_636Exponent,
            periodTwoFromTwoExponent] at count
  | triple x xs normalTail xNotMem =>
      cases normalYs with
      | single y ys normalRight yNotMem =>
          rw [s5_625FirstOccurrences_triple xNotMem,
            s5_625FirstOccurrences_single yNotMem] at order
          have heads := (List.cons.inj order).1
          subst y
          have count := headState
          simp [List.count_eq_zero.mpr xNotMem,
            List.count_eq_zero.mpr yNotMem,
            s5_625Initial,
            SemigroupBasis.CoRoots.S5_636.s5_636Exponent,
            periodTwoFromTwoExponent] at count
      | double y ys normalRight yNotMem =>
          rw [s5_625FirstOccurrences_triple xNotMem,
            s5_625FirstOccurrences_double yNotMem] at order
          have heads := (List.cons.inj order).1
          subst y
          have count := headState
          simp [List.count_eq_zero.mpr xNotMem,
            List.count_eq_zero.mpr yNotMem,
            s5_625Initial,
            SemigroupBasis.CoRoots.S5_636.s5_636Exponent,
            periodTwoFromTwoExponent] at count
      | triple y ys normalRight yNotMem =>
          rw [s5_625FirstOccurrences_triple xNotMem,
            s5_625FirstOccurrences_triple yNotMem] at order
          have heads := (List.cons.inj order).1
          subst y
          congr 3
          exact s5_625TailNormal_eq_of_invariants
            normalTail normalRight (List.cons.inj order).2 <|
              s5_625TailParity_triple xNotMem yNotMem parity

/-- Generic unrestricted completeness interface for a finite table separating
the three head-tail invariants. -/
theorem s5_625Basis_complete_of_separates
    (T : FiniteTable)
    (models : Models T.semigroup s5_625Basis)
    (separatesOrder :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy T.semigroup →
          firstOccurrenceSequence identity.lhs.toList =
            firstOccurrenceSequence identity.rhs.toList)
    (separatesHeadState :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy T.semigroup →
          SemigroupBasis.CoRoots.S5_636.s5_636Exponent
              (identity.lhs.toList.count identity.lhs.head) =
            SemigroupBasis.CoRoots.S5_636.s5_636Exponent
              (identity.rhs.toList.count identity.rhs.head))
    (separatesParity :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy T.semigroup →
          ∀ z,
            identity.lhs.toList.count z % 2 =
              identity.rhs.toList.count z % 2) :
    BasisFor T.semigroup s5_625Basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  obtain ⟨leftHead, leftTail, leftNormal, leftDerivation⟩ :=
    s5_625DerivesNormal identity.lhs
  obtain ⟨rightHead, rightTail, rightNormal, rightDerivation⟩ :=
    s5_625DerivesNormal identity.rhs
  let leftWord := s5_625WordOfCons leftHead leftTail
  let rightWord := s5_625WordOfCons rightHead rightTail
  have leftValid :
      (Identity.mk identity.lhs leftWord).SatisfiedBy T.semigroup := by
    intro valuation
    exact leftDerivation.sound models valuation
  have rightValid :
      (Identity.mk identity.rhs rightWord).SatisfiedBy T.semigroup := by
    intro valuation
    exact rightDerivation.sound models valuation
  have normalOrder :
      firstOccurrenceSequence (leftHead :: leftTail) =
        firstOccurrenceSequence (rightHead :: rightTail) := by
    have leftPreserved :=
      separatesOrder (Identity.mk identity.lhs leftWord) leftValid
    have middle := separatesOrder identity valid
    have rightPreserved :=
      separatesOrder (Identity.mk identity.rhs rightWord) rightValid
    exact leftPreserved.symm.trans <| middle.trans rightPreserved
  have normalHeadState :
      SemigroupBasis.CoRoots.S5_636.s5_636Exponent
          ((leftHead :: leftTail).count leftHead) =
        SemigroupBasis.CoRoots.S5_636.s5_636Exponent
          ((rightHead :: rightTail).count rightHead) := by
    have leftPreserved :=
      separatesHeadState
        (Identity.mk identity.lhs leftWord) leftValid
    have middle := separatesHeadState identity valid
    have rightPreserved :=
      separatesHeadState
        (Identity.mk identity.rhs rightWord) rightValid
    exact leftPreserved.symm.trans <| middle.trans rightPreserved
  have normalParity :
      ∀ z,
        (leftHead :: leftTail).count z % 2 =
          (rightHead :: rightTail).count z % 2 := by
    intro z
    have leftPreserved :=
      separatesParity
        (Identity.mk identity.lhs leftWord) leftValid z
    have middle := separatesParity identity valid z
    have rightPreserved :=
      separatesParity
        (Identity.mk identity.rhs rightWord) rightValid z
    exact leftPreserved.symm.trans <| middle.trans rightPreserved
  have normalEqual :
      leftHead :: leftTail = rightHead :: rightTail :=
    s5_625Normal_eq_of_invariants
      leftNormal rightNormal normalOrder normalHeadState normalParity
  have wordEqual : leftWord = rightWord := by
    cases normalEqual
    rfl
  have bridge :
      Derives s5_625Basis
        (s5_625WordOfCons leftHead leftTail) identity.rhs := by
    change Derives s5_625Basis leftWord identity.rhs
    rw [wordEqual]
    exact Derives.symm rightDerivation
  exact Derives.trans leftDerivation bridge

end SemigroupBasis.CoRoots.S5_625
