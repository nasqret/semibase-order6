/-
Ford-Lord D_378 shared normalizer: the joint identity theory of
S3_16 x S5_378, covering the two orientation obligations of msg-0105
and the nine source-tail classes of msg-0113.

Displayed basis (seven laws, msg-0113 harness): five surviving S5_378
laws plus the middle-reduplication and cross-shuffle laws forced by
the S3_16 factor's plasma-order pinning.
-/
import SemigroupBasis.Equational

set_option maxRecDepth 4096

namespace SemigroupBasis.CoRoots.Order6FordLordD378

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

/-! ## The displayed seven-law system -/

def powerLaw : Identity Nat := ⟨w 0 [0], w 0 [0, 0]⟩
def leftDuplicationLaw : Identity Nat := ⟨w 0 [1, 0], w 0 [0, 1, 0]⟩
def rightDuplicationLaw : Identity Nat := ⟨w 0 [1, 0], w 0 [1, 0, 0]⟩
def squareInterleaveLaw : Identity Nat := ⟨w 0 [0, 1, 1], w 0 [1, 0, 1]⟩
def squareFinalSwitchLaw : Identity Nat :=
  ⟨w 0 [0, 1, 1], w 0 [1, 1, 0]⟩
def middleReduplicationLaw : Identity Nat :=
  ⟨w 0 [1, 2, 0], w 0 [1, 0, 2, 0]⟩
def crossShuffleLaw : Identity Nat :=
  ⟨w 0 [0, 1, 2, 1], w 0 [1, 1, 2, 0]⟩

def basis : List (Identity Nat) :=
  [powerLaw, leftDuplicationLaw, rightDuplicationLaw,
    squareInterleaveLaw, squareFinalSwitchLaw,
    middleReduplicationLaw, crossShuffleLaw]

theorem basis_length : basis.length = 7 := by decide

private theorem powerMem : powerLaw ∈ basis := by simp [basis]
private theorem leftDupMem : leftDuplicationLaw ∈ basis := by
  simp [basis]
private theorem rightDupMem : rightDuplicationLaw ∈ basis := by
  simp [basis]
private theorem interleaveMem : squareInterleaveLaw ∈ basis := by
  simp [basis]
private theorem finalSwitchMem : squareFinalSwitchLaw ∈ basis := by
  simp [basis]
private theorem middleRedupMem : middleReduplicationLaw ∈ basis := by
  simp [basis]
private theorem crossShuffleMem : crossShuffleLaw ∈ basis := by
  simp [basis]

private def instantiateThree (a b c : Word Nat) : Nat → Word Nat
  | 0 => a
  | 1 => b
  | 2 => c
  | n + 3 => Word.singleton (n + 3)

/-! ## Factor rewriting inside a word context -/

private theorem derivesFactor {u v : Word Nat}
    (core : Derives basis u v) :
    ∀ (left : Option (Word Nat)) (right : List Nat),
      Derives basis
        (match left with
          | none => (⟨u.head, u.tail ++ right⟩ : Word Nat)
          | some p => p ++ (⟨u.head, u.tail ++ right⟩ : Word Nat))
        (match left with
          | none => (⟨v.head, v.tail ++ right⟩ : Word Nat)
          | some p => p ++ (⟨v.head, v.tail ++ right⟩ : Word Nat)) := by
  intro left right
  have rightExtended : Derives basis
      (⟨u.head, u.tail ++ right⟩ : Word Nat)
      (⟨v.head, v.tail ++ right⟩ : Word Nat) := by
    cases right with
    | nil =>
        simpa using core
    | cons r rest =>
        have appended := Derives.appendRight core (⟨r, rest⟩ : Word Nat)
        have leftShape :
            u ++ (⟨r, rest⟩ : Word Nat) =
              (⟨u.head, u.tail ++ (r :: rest)⟩ : Word Nat) := rfl
        have rightShape :
            v ++ (⟨r, rest⟩ : Word Nat) =
              (⟨v.head, v.tail ++ (r :: rest)⟩ : Word Nat) := rfl
        rw [leftShape, rightShape] at appended
        exact appended
  cases left with
  | none => exact rightExtended
  | some p => exact Derives.prepend p rightExtended

/-! ## Block instances of the seven laws -/

/-- `X² ~ X³`. -/
theorem derivesPower (x : Word Nat) :
    Derives basis (x ++ x) ((x ++ x) ++ x) := by
  have base : Derives basis powerLaw.lhs powerLaw.rhs :=
    Derives.fromBasis powerMem
  have substituted := Derives.subst base (instantiateThree x x x)
  simpa [powerLaw, w, instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- `XYX ~ X²YX`. -/
theorem derivesLeftDuplication (x y : Word Nat) :
    Derives basis ((x ++ y) ++ x) (((x ++ x) ++ y) ++ x) := by
  have base : Derives basis leftDuplicationLaw.lhs
      leftDuplicationLaw.rhs :=
    Derives.fromBasis leftDupMem
  have substituted := Derives.subst base (instantiateThree x y y)
  simpa [leftDuplicationLaw, w, instantiateThree, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- `XYX ~ XYX²`. -/
theorem derivesRightDuplication (x y : Word Nat) :
    Derives basis ((x ++ y) ++ x) (((x ++ y) ++ x) ++ x) := by
  have base : Derives basis rightDuplicationLaw.lhs
      rightDuplicationLaw.rhs :=
    Derives.fromBasis rightDupMem
  have substituted := Derives.subst base (instantiateThree x y y)
  simpa [rightDuplicationLaw, w, instantiateThree, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- `X²Y² ~ XYXY`. -/
theorem derivesSquareInterleave (x y : Word Nat) :
    Derives basis (((x ++ x) ++ y) ++ y) (((x ++ y) ++ x) ++ y) := by
  have base : Derives basis squareInterleaveLaw.lhs
      squareInterleaveLaw.rhs :=
    Derives.fromBasis interleaveMem
  have substituted := Derives.subst base (instantiateThree x y y)
  simpa [squareInterleaveLaw, w, instantiateThree, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- `X²Y² ~ XY²X`. -/
theorem derivesSquareFinalSwitch (x y : Word Nat) :
    Derives basis (((x ++ x) ++ y) ++ y) (((x ++ y) ++ y) ++ x) := by
  have base : Derives basis squareFinalSwitchLaw.lhs
      squareFinalSwitchLaw.rhs :=
    Derives.fromBasis finalSwitchMem
  have substituted := Derives.subst base (instantiateThree x y y)
  simpa [squareFinalSwitchLaw, w, instantiateThree, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- `XYZX ~ XYXZX` (middle re-duplication). -/
theorem derivesMiddleReduplication (x y z : Word Nat) :
    Derives basis (((x ++ y) ++ z) ++ x)
      ((((x ++ y) ++ x) ++ z) ++ x) := by
  have base : Derives basis middleReduplicationLaw.lhs
      middleReduplicationLaw.rhs :=
    Derives.fromBasis middleRedupMem
  have substituted := Derives.subst base (instantiateThree x y z)
  simpa [middleReduplicationLaw, w, instantiateThree, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- `X²YZY ~ XY²ZX` (cross shuffle). -/
theorem derivesCrossShuffle (x y z : Word Nat) :
    Derives basis ((((x ++ x) ++ y) ++ z) ++ y)
      ((((x ++ y) ++ y) ++ z) ++ x) := by
  have base : Derives basis crossShuffleLaw.lhs crossShuffleLaw.rhs :=
    Derives.fromBasis crossShuffleMem
  have substituted := Derives.subst base (instantiateThree x y z)
  simpa [crossShuffleLaw, w, instantiateThree, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-! ## The D_378 signature (msg-0105 coordinates) -/

def letterCount (u : Word Nat) (x : Nat) : Nat :=
  u.toList.count x

def IsSingle (u : Word Nat) (x : Nat) : Prop :=
  letterCount u x = 1

def IsPlasma (u : Word Nat) (x : Nat) : Prop :=
  2 ≤ letterCount u x

instance (u : Word Nat) (x : Nat) : Decidable (IsSingle u x) := by
  unfold IsSingle; infer_instance

instance (u : Word Nat) (x : Nat) : Decidable (IsPlasma u x) := by
  unfold IsPlasma; infer_instance

/-- Count-one letters in word order. -/
def singlesSeq (u : Word Nat) : List Nat :=
  u.toList.filter (fun c => u.toList.count c == 1)

/-- Plasma letters in first-occurrence order. -/
def plasmaSeq (u : Word Nat) : List Nat :=
  u.toList.eraseDups.filter (fun c => 2 ≤ u.toList.count c)

/-- Index of the last occurrence of a member letter. -/
def lastIdxOf (l : List Nat) (x : Nat) : Nat :=
  l.length - 1 - l.reverse.idxOf x

/-- The four-way single-versus-region relation (quantifier form: each
condition is element-wise over the plasma sequence, which keeps every
comparison stable under position reindexings). -/
inductive Rel4 where
  | before
  | after
  | inside
  | gap
deriving DecidableEq, Repr

/- Lean 4.28 does not reduce the derived `BEq` for `Rel4` under every
Boolean connective.  These finite certificates keep component-filter
proofs mechanical. -/
@[simp] private theorem rel4_beq_before_before :
    (Rel4.before == Rel4.before) = true := by decide
@[simp] private theorem rel4_beq_before_after :
    (Rel4.before == Rel4.after) = false := by decide
@[simp] private theorem rel4_beq_before_inside :
    (Rel4.before == Rel4.inside) = false := by decide
@[simp] private theorem rel4_beq_before_gap :
    (Rel4.before == Rel4.gap) = false := by decide
@[simp] private theorem rel4_beq_after_before :
    (Rel4.after == Rel4.before) = false := by decide
@[simp] private theorem rel4_beq_after_after :
    (Rel4.after == Rel4.after) = true := by decide
@[simp] private theorem rel4_beq_after_inside :
    (Rel4.after == Rel4.inside) = false := by decide
@[simp] private theorem rel4_beq_after_gap :
    (Rel4.after == Rel4.gap) = false := by decide
@[simp] private theorem rel4_beq_inside_before :
    (Rel4.inside == Rel4.before) = false := by decide
@[simp] private theorem rel4_beq_inside_after :
    (Rel4.inside == Rel4.after) = false := by decide
@[simp] private theorem rel4_beq_inside_inside :
    (Rel4.inside == Rel4.inside) = true := by decide
@[simp] private theorem rel4_beq_inside_gap :
    (Rel4.inside == Rel4.gap) = false := by decide
@[simp] private theorem rel4_beq_gap_before :
    (Rel4.gap == Rel4.before) = false := by decide
@[simp] private theorem rel4_beq_gap_after :
    (Rel4.gap == Rel4.after) = false := by decide
@[simp] private theorem rel4_beq_gap_inside :
    (Rel4.gap == Rel4.inside) = false := by decide
@[simp] private theorem rel4_beq_gap_gap :
    (Rel4.gap == Rel4.gap) = true := by decide

def rel4 (u : Word Nat) (s : Nat) : Rel4 :=
  if (plasmaSeq u).all (fun p =>
      u.toList.idxOf s < u.toList.idxOf p) then Rel4.before
  else if (plasmaSeq u).all (fun p =>
      lastIdxOf u.toList p < u.toList.idxOf s) then Rel4.after
  else if (plasmaSeq u).any (fun p =>
      u.toList.idxOf p < u.toList.idxOf s &&
        u.toList.idxOf s < lastIdxOf u.toList p) then Rel4.inside
  else Rel4.gap

/-- The plasma letters whose first occurrence follows the single, as a
sublist of the canonical plasma sequence. -/
def beforeOpenList (u : Word Nat) (s : Nat) : List Nat :=
  (plasmaSeq u).filter (fun p => u.toList.idxOf s < u.toList.idxOf p)

/-- The full D_378 signature equality. -/
def SameD378Signature (u v : Word Nat) : Prop :=
  u.head = v.head ∧
  singlesSeq u = singlesSeq v ∧
  plasmaSeq u = plasmaSeq v ∧
  (∀ s, IsSingle u s →
    beforeOpenList u s = beforeOpenList v s ∧ rel4 u s = rel4 v s)

/-- Computable signature tuple (for oracle cross-validation and the
completeness bridge). -/
def signatureOf (u : Word Nat) :
    Nat × List Nat × List Nat × List (List Nat × Rel4) :=
  (u.head, singlesSeq u, plasmaSeq u,
    (singlesSeq u).map (fun s => (beforeOpenList u s, rel4 u s)))

/-! ## The canonical word (oracle-validated construction) -/

/-- The slot of a single: the index of the first plasma-sequence member
whose open follows it (the sequence length if none does). -/
def slotOf (u : Word Nat) (s : Nat) : Nat :=
  ((plasmaSeq u).takeWhile
    (fun p => u.toList.idxOf p < u.toList.idxOf s)).length

/-- Singles of a given slot and four-way relation, in word order. -/
def slotSingles (u : Word Nat) (i : Nat) (r : Rel4) : List Nat :=
  (singlesSeq u).filter (fun s => slotOf u s == i && rel4 u s == r)

/-- The head-stripped singles (a count-one head is placed by the head
position itself). -/
def strippedSingles (u : Word Nat) : List Nat :=
  if (singlesSeq u).take 1 = [u.head] && !decide (IsPlasma u u.head) then
    (singlesSeq u).drop 1
  else singlesSeq u

/-- One plasma block: open, nested inside-singles, close, then the
trailing gap-singles of the slot. -/
def blockOf (u : Word Nat) (i : Nat) (p : Nat) : List Nat :=
  (if i == 0 && p == u.head then
    ((strippedSingles u).filter
      (fun s => slotOf u s == i + 1 && rel4 u s == Rel4.inside)) ++ [p]
   else
    p :: ((strippedSingles u).filter
      (fun s => slotOf u s == i + 1 && rel4 u s == Rel4.inside)) ++ [p]) ++
  ((strippedSingles u).filter
    (fun s => slotOf u s == i + 1 && rel4 u s == Rel4.gap))

/-- The canonical word of a D_378 class. -/
def canonicalize (u : Word Nat) : Word Nat :=
  let pseq := plasmaSeq u
  let befores := (strippedSingles u).filter (fun s => slotOf u s == 0)
  let afters := (strippedSingles u).filter
    (fun s => slotOf u s == pseq.length && rel4 u s == Rel4.after)
  ⟨u.head,
    befores ++
      (List.range pseq.length).flatMap
        (fun i => blockOf u i (pseq.getD i 0)) ++
      afters⟩

/-! ## Ported position toolkit (proven in the ce7f module) -/

/-- Counts are stable under appending a different letter. -/
private theorem count_append_ne {l : List Nat} {c x : Nat}
    (ne : c ≠ x) : (l ++ [x]).count c = l.count c := by
  induction l with
  | nil =>
      have xc : x ≠ c := fun equal => ne equal.symm
      simp [List.count_cons, xc]
  | cons a rest ih =>
      simp [List.count_cons, ih]

/-- Appending bumps the appended letter's count by one. -/
private theorem count_append_self (l : List Nat) (x : Nat) :
    (l ++ [x]).count x = l.count x + 1 := by
  induction l with
  | nil => simp
  | cons a rest ih =>
      simp [List.count_cons, ih]
      omega

/-- First index is stable under appending when the letter is present. -/
private theorem idxOf_append_of_mem {l : List Nat} {c : Nat}
    (member : c ∈ l) (x : Nat) : (l ++ [x]).idxOf c = l.idxOf c := by
  induction l with
  | nil => simp at member
  | cons a rest ih =>
      by_cases hit : a = c
      · have hitBeq : (a == c) = true := by simp [hit]
        simp [List.cons_append, List.idxOf_cons, hitBeq]
      · have hitBeq : (a == c) = false := by simp [hit]
        have restMember : c ∈ rest := by
          rcases List.mem_cons.mp member with equal | tail
          · exact absurd equal.symm hit
          · exact tail
        simp [List.cons_append, List.idxOf_cons, hitBeq, ih restMember]

/-- Last index is stable under appending a different letter. -/
private theorem lastIdxOf_append_ne {l : List Nat} {c x : Nat}
    (member : c ∈ l) (ne : c ≠ x) :
    lastIdxOf (l ++ [x]) c = lastIdxOf l c := by
  have xc : (x == c) = false := by
    have xcNe : x ≠ c := fun equal => ne equal.symm
    simp [xcNe]
  have reverseShape : (l ++ [x]).reverse = x :: l.reverse := by simp
  rw [lastIdxOf, lastIdxOf, reverseShape, List.idxOf_cons, xc]
  have lengthShape : (l ++ [x]).length = l.length + 1 := by simp
  rw [lengthShape]
  simp only [cond_false]
  have posBound : l.reverse.idxOf c < l.length := by
    have revMember : c ∈ l.reverse := by simpa using member
    have := List.idxOf_lt_length_of_mem revMember
    simpa using this
  omega

/-- Filter congruence over a membership-respecting predicate change. -/
private theorem filter_congr_mem {l : List Nat} {p q : Nat → Bool}
    (agree : ∀ a, a ∈ l → p a = q a) : l.filter p = l.filter q := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
      have restAgree : ∀ b, b ∈ rest → p b = q b :=
        fun b member => agree b (List.mem_cons_of_mem _ member)
      have headAgree : p a = q a := agree a (by simp)
      simp only [List.filter_cons, headAgree, ih restAgree]

/-- Index of a fresh letter appended at the end. -/
private theorem idxOf_append_self_of_not_mem {l : List Nat} {x : Nat}
    (fresh : x ∉ l) : (l ++ [x]).idxOf x = l.length := by
  induction l with
  | nil => simp
  | cons a rest ih =>
      have ax : a ≠ x := by
        intro equal
        exact fresh (equal ▸ (by simp : a ∈ a :: rest))
      have axBeq : (a == x) = false := by simp [ax]
      have restFresh : x ∉ rest :=
        fun member => fresh (List.mem_cons_of_mem _ member)
      simp [List.cons_append, List.idxOf_cons, axBeq, ih restFresh]

/-- Members have an index below the length. -/
private theorem idxOf_lt_length_of_mem_local {l : List Nat} {c : Nat}
    (member : c ∈ l) : l.idxOf c < l.length :=
  List.idxOf_lt_length_of_mem member

/-- takeWhile only depends on the predicate over the list members. -/
private theorem takeWhile_congr_mem {l : List Nat} {q q' : Nat → Bool}
    (agree : ∀ a, a ∈ l → q a = q' a) :
    l.takeWhile q = l.takeWhile q' := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
      have headAgree : q a = q' a := agree a (by simp)
      have restAgree : ∀ b, b ∈ rest → q b = q' b :=
        fun b member => agree b (List.mem_cons_of_mem _ member)
      simp only [List.takeWhile_cons, headAgree, ih restAgree]

/-- takeWhile runs across an append when the left part passes. -/
private theorem takeWhile_append_all {l r : List Nat} {q : Nat → Bool}
    (all : ∀ a, a ∈ l → q a = true) :
    (l ++ r).takeWhile q = l ++ r.takeWhile q := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
      have headTrue : q a = true := all a (by simp)
      have restAll : ∀ b, b ∈ rest → q b = true :=
        fun b member => all b (List.mem_cons_of_mem _ member)
      simp [List.takeWhile_cons, headTrue, ih restAll]

/-- takeWhile ignores the right part when the left part stops it. -/
private theorem takeWhile_append_stop {l r : List Nat} {q : Nat → Bool}
    (stop : (l.takeWhile q).length ≠ l.length) :
    (l ++ r).takeWhile q = l.takeWhile q := by
  induction l with
  | nil => simp at stop
  | cons a rest ih =>
      by_cases headPass : q a = true
      · have restStop : (rest.takeWhile q).length ≠ rest.length := by
          intro equal
          exact stop (by simp [List.takeWhile_cons, headPass, equal])
        simp [List.takeWhile_cons, headPass, ih restStop]
      · have headFalse : q a = false := by
          cases verdict : q a
          · rfl
          · exact absurd verdict headPass
        simp [List.takeWhile_cons, headFalse]

/-- flatMap only depends on the function over the list members. -/
private theorem flatMap_congr_mem {l : List Nat}
    {f g : Nat → List Nat} (agree : ∀ a, a ∈ l → f a = g a) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
      have headAgree : f a = g a := agree a (by simp)
      have restAgree : ∀ b, b ∈ rest → f b = g b :=
        fun b member => agree b (List.mem_cons_of_mem _ member)
      simp only [List.flatMap_cons, headAgree, ih restAgree]

/-- First index over an append, absent on the left. -/
private theorem idxOf_append_absent {P Q : List Nat} {e : Nat}
    (absent : e ∉ P) :
    (P ++ Q).idxOf e = P.length + Q.idxOf e := by
  induction P with
  | nil => simp
  | cons a rest ih =>
      have ae : a ≠ e := by
        intro equal
        exact absent (equal ▸ (by simp : a ∈ a :: rest))
      have aeBeq : (a == e) = false := by simp [ae]
      have restAbsent : e ∉ rest :=
        fun member => absent (List.mem_cons_of_mem _ member)
      simp [List.cons_append, List.idxOf_cons, aeBeq, ih restAbsent]
      omega

/-- First index over an append, member on the left. -/
private theorem idxOf_append_left {P : List Nat} {e : Nat}
    (member : e ∈ P) (Q : List Nat) :
    (P ++ Q).idxOf e = P.idxOf e := by
  induction P with
  | nil => simp at member
  | cons a rest ih =>
      by_cases hit : a = e
      · have hitBeq : (a == e) = true := by simp [hit]
        simp [List.cons_append, List.idxOf_cons, hitBeq]
      · have hitBeq : (a == e) = false := by simp [hit]
        have restMember : e ∈ rest := by
          rcases List.mem_cons.mp member with equal | tail
          · exact absurd equal.symm hit
          · exact tail
        simp [List.cons_append, List.idxOf_cons, hitBeq, ih restMember]

/-- Last index over an append, member on the right. -/
private theorem lastIdxOf_append_right {P Q : List Nat} {e : Nat}
    (member : e ∈ Q) :
    lastIdxOf (P ++ Q) e = P.length + lastIdxOf Q e := by
  have reverseShape : (P ++ Q).reverse = Q.reverse ++ P.reverse := by
    simp
  have revMember : e ∈ Q.reverse := List.mem_reverse.mpr member
  rw [lastIdxOf, lastIdxOf, reverseShape,
    idxOf_append_left revMember]
  have bound : Q.reverse.idxOf e < Q.reverse.length :=
    idxOf_lt_length_of_mem_local revMember
  simp only [List.length_append, List.length_reverse] at bound ⊢
  omega

/-- Last index over an append, member absent on the right. -/
private theorem lastIdxOf_append_left {P Q : List Nat} {e : Nat}
    (member : e ∈ P) (absent : e ∉ Q) :
    lastIdxOf (P ++ Q) e = lastIdxOf P e := by
  have reverseShape : (P ++ Q).reverse = Q.reverse ++ P.reverse := by
    simp
  have revAbsent : e ∉ Q.reverse :=
    fun inRev => absent (List.mem_reverse.mp inRev)
  have revMember : e ∈ P.reverse := List.mem_reverse.mpr member
  rw [lastIdxOf, lastIdxOf, reverseShape,
    idxOf_append_absent revAbsent]
  have bound : P.reverse.idxOf e < P.reverse.length :=
    idxOf_lt_length_of_mem_local revMember
  simp only [List.length_append, List.length_reverse] at bound ⊢
  omega

/-- Last index shifts across a cons when the letter recurs behind it. -/
private theorem lastIdxOf_cons_of_mem {B : List Nat} {a e : Nat}
    (member : e ∈ B) :
    lastIdxOf (a :: B) e = lastIdxOf B e + 1 := by
  have reverseShape : (a :: B).reverse = B.reverse ++ [a] := by simp
  have revMember : e ∈ B.reverse := List.mem_reverse.mpr member
  rw [lastIdxOf, lastIdxOf, reverseShape,
    idxOf_append_left revMember]
  have bound : B.reverse.idxOf e < B.reverse.length :=
    idxOf_lt_length_of_mem_local revMember
  simp only [List.length_append, List.length_cons, List.length_nil,
    List.length_reverse] at bound ⊢
  omega

/-- First-index formula over the spliced list. -/
private theorem idxOf_splice {P B : List Nat} {c e : Nat}
    (ne : e ≠ c) (memberEither : e ∈ P ∨ e ∈ B) :
    (P ++ c :: B).idxOf e =
      (if e ∈ P then P.idxOf e else P.length + 1 + B.idxOf e) ∧
    (P ++ B).idxOf e =
      (if e ∈ P then P.idxOf e else P.length + B.idxOf e) := by
  by_cases inP : e ∈ P
  · rw [if_pos inP, if_pos inP]
    exact ⟨idxOf_append_left inP _, idxOf_append_left inP _⟩
  · rw [if_neg inP, if_neg inP]
    have inB : e ∈ B := by
      rcases memberEither with hit | hit
      · exact absurd hit inP
      · exact hit
    constructor
    · rw [idxOf_append_absent inP]
      have consShift : (c :: B).idxOf e = B.idxOf e + 1 := by
        have ceBeq : (c == e) = false := by
          have ce : c ≠ e := fun h => ne h.symm
          simp [ce]
        simp [List.idxOf_cons, ceBeq]
      rw [consShift]
      omega
    · rw [idxOf_append_absent inP]

/-- Last-index formula over the spliced list, for letters other than
the dropped one. -/
private theorem lastIdxOf_splice {P B : List Nat} {c e : Nat}
    (ne : e ≠ c) (memberEither : e ∈ P ∨ e ∈ B) :
    lastIdxOf (P ++ c :: B) e =
      (if e ∈ B then P.length + 1 + lastIdxOf B e else lastIdxOf P e) ∧
    lastIdxOf (P ++ B) e =
      (if e ∈ B then P.length + lastIdxOf B e else lastIdxOf P e) := by
  by_cases inB : e ∈ B
  · rw [if_pos inB, if_pos inB]
    constructor
    · rw [lastIdxOf_append_right (List.mem_cons_of_mem _ inB),
        lastIdxOf_cons_of_mem inB]
      omega
    · rw [lastIdxOf_append_right inB]
  · rw [if_neg inB, if_neg inB]
    have inP : e ∈ P := by
      rcases memberEither with hit | hit
      · exact hit
      · exact absurd hit inB
    have notInCons : e ∉ c :: B := by
      intro member
      rcases List.mem_cons.mp member with equal | tail
      · exact ne equal
      · exact inB tail
    exact ⟨lastIdxOf_append_left inP notInCons,
      lastIdxOf_append_left inP inB⟩

/-- The dropped letter's endpoints over the spliced list. -/
private theorem idxOf_splice_self {P B : List Nat} {c : Nat}
    (memberP : c ∈ P) (memberB : c ∈ B) :
    (P ++ c :: B).idxOf c = P.idxOf c ∧
    (P ++ B).idxOf c = P.idxOf c ∧
    lastIdxOf (P ++ c :: B) c = P.length + 1 + lastIdxOf B c ∧
    lastIdxOf (P ++ B) c = P.length + lastIdxOf B c := by
  refine ⟨idxOf_append_left memberP _, idxOf_append_left memberP _,
    ?_, lastIdxOf_append_right memberB⟩
  rw [lastIdxOf_append_right (List.mem_cons_of_mem _ memberB),
    lastIdxOf_cons_of_mem memberB]
  omega

/-! ## Middle-occurrence dropping: descriptor stability -/

/-- Members survive eraseDups (hand-proved; absent from pinned core). -/
private theorem mem_of_mem_eraseDups {l : List Nat} {c : Nat}
    (member : c ∈ l.eraseDups) : c ∈ l := by
  have general : ∀ (l : List Nat) (seen : List Nat) (c : Nat),
      c ∈ List.eraseDupsBy.loop (fun a b => a == b) l seen →
        c ∈ l ∨ c ∈ seen.reverse := by
    intro l
    induction l with
    | nil =>
        intro seen c member
        rw [List.eraseDupsBy.loop] at member
        exact Or.inr member
    | cons a rest ih =>
        intro seen c member
        rw [List.eraseDupsBy.loop] at member
        split at member
        · rcases ih seen c member with inRest | inSeen
          · exact Or.inl (List.mem_cons_of_mem _ inRest)
          · exact Or.inr inSeen
        · rcases ih (a :: seen) c member with inRest | inSeen
          · exact Or.inl (List.mem_cons_of_mem _ inRest)
          · simp only [List.reverse_cons] at inSeen
            rcases List.mem_append.mp inSeen with old | hit
            · exact Or.inr old
            · simp only [List.mem_singleton] at hit
              exact Or.inl (hit ▸ (by simp : a ∈ a :: rest))
  have unfolded : c ∈ List.eraseDupsBy.loop (fun a b => a == b) l [] := by
    simpa [List.eraseDups, List.eraseDupsBy] using member
  rcases general l [] c unfolded with inL | inNil
  · exact inL
  · simp at inNil


/-- A middle duplicate is invisible to eraseDups. -/
private theorem eraseDups_splice_mem {P B : List Nat} {c : Nat}
    (member : c ∈ P) :
    (P ++ c :: B).eraseDups = (P ++ B).eraseDups := by
  have loop : ∀ (l seen : List Nat), c ∈ l ∨ c ∈ seen →
      List.eraseDupsBy.loop (fun a b => a == b) (l ++ c :: B) seen =
        List.eraseDupsBy.loop (fun a b => a == b) (l ++ B) seen := by
    intro l
    induction l with
    | nil =>
        intro seen side
        have seenHit : c ∈ seen := by
          rcases side with inNil | inSeen
          · simp at inNil
          · exact inSeen
        rw [List.nil_append, List.nil_append, List.eraseDupsBy.loop]
        have anyHit : seen.any (fun b => c == b) = true := by
          rw [List.any_eq_true]
          exact ⟨c, seenHit, by simp⟩
        rw [anyHit]
    | cons a rest ih =>
        intro seen side
        rw [List.cons_append, List.cons_append,
          List.eraseDupsBy.loop, List.eraseDupsBy.loop]
        by_cases anyHit : seen.any (fun b => a == b) = true
        · rw [anyHit]
          apply ih
          rcases side with inCons | inSeen
          · rcases List.mem_cons.mp inCons with equal | inRest
            · right
              rw [List.any_eq_true] at anyHit
              obtain ⟨b, bMem, abBeq⟩ := anyHit
              have ab : a = b := by simpa using abBeq
              exact equal ▸ (ab ▸ bMem)
            · exact Or.inl inRest
          · exact Or.inr inSeen
        · have anyMiss : seen.any (fun b => a == b) = false := by
            cases verdict : seen.any (fun b => a == b)
            · rfl
            · exact absurd verdict anyHit
          rw [anyMiss]
          apply ih
          rcases side with inCons | inSeen
          · rcases List.mem_cons.mp inCons with equal | inRest
            · exact Or.inr (by simp [equal])
            · exact Or.inl inRest
          · exact Or.inr (List.mem_cons_of_mem _ inSeen)
  rw [List.eraseDups, List.eraseDups, List.eraseDupsBy,
    List.eraseDupsBy]
  exact loop P [] (Or.inl member)

/-- Count over the spliced list. -/
private theorem count_splice {P B : List Nat} {c e : Nat} :
    (P ++ c :: B).count e =
      (P ++ B).count e + (if e = c then 1 else 0) := by
  by_cases hit : e = c
  · rw [if_pos hit, hit]
    simp [List.count_append, List.count_cons]
    omega
  · rw [if_neg hit]
    have ce : ¬ (c = e) := fun h => hit h.symm
    simp [List.count_append, List.count_cons, ce]

/-- The spliced word's letter lists. -/
private theorem toList_splice (h c : Nat) (A B : List Nat) :
    (⟨h, A ++ c :: B⟩ : Word Nat).toList = (h :: A) ++ c :: B ∧
    (⟨h, A ++ B⟩ : Word Nat).toList = (h :: A) ++ B := by
  constructor <;> simp [Word.toList]

/-- Dropping a middle occurrence keeps the singles sequence. -/
private theorem singlesSeq_splice {h c : Nat} {A B : List Nat}
    (beforeMem : c ∈ h :: A) (afterMem : c ∈ B) :
    singlesSeq (⟨h, A ++ c :: B⟩ : Word Nat) =
      singlesSeq (⟨h, A ++ B⟩ : Word Nat) := by
  obtain ⟨listL, listR⟩ := toList_splice h c A B
  have cBig : 2 ≤ ((h :: A) ++ B).count c := by
    have inL : 0 < (h :: A).count c := List.count_pos_iff.mpr beforeMem
    have inR : 0 < B.count c := List.count_pos_iff.mpr afterMem
    simp only [List.count_append]
    omega
  rw [singlesSeq, singlesSeq, listL, listR]
  have expand : (h :: A) ++ c :: B = ((h :: A) ++ [c]) ++ B := by
    simp
  rw [expand, List.filter_append, List.filter_append,
    List.filter_append]
  have leftCongr : (h :: A).filter
      (fun e => (((h :: A) ++ [c]) ++ B).count e == 1) =
      (h :: A).filter (fun e => ((h :: A) ++ B).count e == 1) := by
    apply filter_congr_mem
    intro a _
    have shape : ((h :: A) ++ [c]) ++ B = (h :: A) ++ c :: B := by
      simp
    rw [shape, count_splice]
    by_cases hit : a = c
    · have bigCount : 2 ≤ ((h :: A) ++ B).count a := by
        rw [hit]
        exact cBig
      have leftF : (((h :: A) ++ B).count a +
          (if a = c then 1 else 0) == 1) = false := by
        rw [if_pos hit]
        cases v : (((h :: A) ++ B).count a + 1 == 1)
        · rfl
        · exfalso
          have eq1 : ((h :: A) ++ B).count a + 1 = 1 := by
            simpa using v
          omega
      have rightF : (((h :: A) ++ B).count a == 1) = false := by
        cases v : (((h :: A) ++ B).count a == 1)
        · rfl
        · exfalso
          have eq1 : ((h :: A) ++ B).count a = 1 := by
            simpa using v
          omega
      rw [leftF, rightF]
    · rw [if_neg hit]
      simp
  have midEmpty : ([c] : List Nat).filter
      (fun e => (((h :: A) ++ [c]) ++ B).count e == 1) = [] := by
    have bigF : ((((h :: A) ++ [c]) ++ B).count c == 1) = false := by
      cases v : ((((h :: A) ++ [c]) ++ B).count c == 1)
      · rfl
      · exfalso
        have e1 : (((h :: A) ++ [c]) ++ B).count c = 1 := by
          simpa using v
        rw [show ((h :: A) ++ [c]) ++ B = (h :: A) ++ c :: B by simp,
          count_splice, if_pos rfl] at e1
        omega
    simp [List.filter_cons]
    have expand2 : List.count c (h :: (A ++ c :: B)) =
        ((h :: A) ++ B).count c + 1 := by
      rw [show h :: (A ++ c :: B) = (h :: A) ++ c :: B from by simp,
        count_splice, if_pos rfl]
    omega
  have rightCongr : B.filter
      (fun e => (((h :: A) ++ [c]) ++ B).count e == 1) =
      B.filter (fun e => ((h :: A) ++ B).count e == 1) := by
    apply filter_congr_mem
    intro a _
    have shape : ((h :: A) ++ [c]) ++ B = (h :: A) ++ c :: B := by
      simp
    rw [shape, count_splice]
    by_cases hit : a = c
    · have bigCount : 2 ≤ ((h :: A) ++ B).count a := by
        rw [hit]
        exact cBig
      have leftF : (((h :: A) ++ B).count a +
          (if a = c then 1 else 0) == 1) = false := by
        rw [if_pos hit]
        cases v : (((h :: A) ++ B).count a + 1 == 1)
        · rfl
        · exfalso
          have eq1 : ((h :: A) ++ B).count a + 1 = 1 := by
            simpa using v
          omega
      have rightF : (((h :: A) ++ B).count a == 1) = false := by
        cases v : (((h :: A) ++ B).count a == 1)
        · rfl
        · exfalso
          have eq1 : ((h :: A) ++ B).count a = 1 := by
            simpa using v
          omega
      rw [leftF, rightF]
    · rw [if_neg hit]
      simp
  rw [leftCongr, midEmpty, rightCongr, List.append_nil]

/-- Dropping a middle occurrence keeps the plasma sequence. -/
private theorem plasmaSeq_splice {h c : Nat} {A B : List Nat}
    (beforeMem : c ∈ h :: A) (afterMem : c ∈ B) :
    plasmaSeq (⟨h, A ++ c :: B⟩ : Word Nat) =
      plasmaSeq (⟨h, A ++ B⟩ : Word Nat) := by
  obtain ⟨listL, listR⟩ := toList_splice h c A B
  rw [plasmaSeq, plasmaSeq, listL, listR,
    eraseDups_splice_mem beforeMem]
  apply filter_congr_mem
  intro a member
  have aIn : a ∈ (h :: A) ++ B :=
    mem_of_mem_eraseDups member
  rw [count_splice]
  by_cases hit : a = c
  · have cBig : 2 ≤ ((h :: A) ++ B).count c := by
      have inL : 0 < (h :: A).count c := List.count_pos_iff.mpr beforeMem
      have inR : 0 < B.count c := List.count_pos_iff.mpr afterMem
      simp only [List.count_append]
      omega
    have bigR : 2 ≤ ((h :: A) ++ B).count a := by
      rw [hit]
      exact cBig
    rw [if_pos hit]
    simp only [decide_eq_true bigR,
      decide_eq_true (by omega : 2 ≤ ((h :: A) ++ B).count a + 1)]
  · rw [if_neg hit]
    simp

/-! ## Position-coordinate stability under middle-occurrence dropping -/

/-- The order-preserving reindexing induced by dropping the spliced
occurrence: positions inside the prefix are unchanged, later positions
move up by one. -/
private def spliceShift (n k : Nat) : Nat :=
  if n < k then n else n + 1

private theorem spliceShift_lt_iff {a b k : Nat} :
    spliceShift a k < spliceShift b k ↔ a < b := by
  simp only [spliceShift]
  by_cases ha : a < k <;> by_cases hb : b < k <;>
    simp only [if_pos, if_neg, ha, hb, if_true, if_false] <;> omega

/-- Both position coordinates of every surviving letter move by the
uniform splice shift when the middle occurrence is dropped. -/
private theorem pos_splice {P B : List Nat} {c : Nat}
    (memberP : c ∈ P) (memberB : c ∈ B) {e : Nat}
    (memberE : e ∈ P ++ B) :
    (P ++ c :: B).idxOf e = spliceShift ((P ++ B).idxOf e) P.length ∧
    lastIdxOf (P ++ c :: B) e =
      spliceShift (lastIdxOf (P ++ B) e) P.length := by
  by_cases ec : e = c
  · subst ec
    obtain ⟨iSpl, iUn, lSpl, lUn⟩ := idxOf_splice_self memberP memberB
    rw [iSpl, iUn, lSpl, lUn]
    have iLt : P.idxOf e < P.length :=
      idxOf_lt_length_of_mem_local memberP
    constructor
    · simp only [spliceShift]
      rw [if_pos iLt]
    · simp only [spliceShift]
      rw [if_neg (by omega : ¬ P.length + lastIdxOf B e < P.length)]
      omega
  · have memberEither : e ∈ P ∨ e ∈ B := List.mem_append.mp memberE
    obtain ⟨iSpl, iUn⟩ := idxOf_splice ec memberEither
    obtain ⟨lSpl, lUn⟩ := lastIdxOf_splice ec memberEither
    rw [iSpl, iUn, lSpl, lUn]
    constructor
    · by_cases inP : e ∈ P
      · rw [if_pos inP, if_pos inP]
        have iLt : P.idxOf e < P.length :=
          idxOf_lt_length_of_mem_local inP
        simp only [spliceShift]
        rw [if_pos iLt]
      · rw [if_neg inP, if_neg inP]
        simp only [spliceShift]
        rw [if_neg (by omega : ¬ P.length + B.idxOf e < P.length)]
        omega
    · by_cases inB : e ∈ B
      · rw [if_pos inB, if_pos inB]
        simp only [spliceShift]
        rw [if_neg (by omega : ¬ P.length + lastIdxOf B e < P.length)]
        omega
      · rw [if_neg inB, if_neg inB]
        have inP : e ∈ P := by
          rcases memberEither with hit | hit
          · exact hit
          · exact absurd hit inB
        have posLen : 0 < P.length := by
          cases P with
          | nil => cases inP
          | cons a t => simp
        have lLt : lastIdxOf P e < P.length := by
          simp only [lastIdxOf]
          omega
        simp only [spliceShift]
        rw [if_pos lLt]

/-- All three positional comparisons used by the signature are stable
under middle-occurrence dropping. -/
private theorem cond_stab {P B : List Nat} {c : Nat}
    (memberP : c ∈ P) (memberB : c ∈ B) {e f : Nat}
    (memberE : e ∈ P ++ B) (memberF : f ∈ P ++ B) :
    ((P ++ c :: B).idxOf e < (P ++ c :: B).idxOf f ↔
      (P ++ B).idxOf e < (P ++ B).idxOf f) ∧
    (lastIdxOf (P ++ c :: B) f < (P ++ c :: B).idxOf e ↔
      lastIdxOf (P ++ B) f < (P ++ B).idxOf e) ∧
    ((P ++ c :: B).idxOf e < lastIdxOf (P ++ c :: B) f ↔
      (P ++ B).idxOf e < lastIdxOf (P ++ B) f) := by
  obtain ⟨iE, lE⟩ := pos_splice memberP memberB memberE
  obtain ⟨iF, lF⟩ := pos_splice memberP memberB memberF
  rw [iE, iF, lF]
  exact ⟨spliceShift_lt_iff, spliceShift_lt_iff, spliceShift_lt_iff⟩

/-- all only depends on the predicate over the list members. -/
private theorem all_congr_mem {l : List Nat} {p q : Nat → Bool}
    (agree : ∀ a, a ∈ l → p a = q a) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
      have restAgree : ∀ b, b ∈ rest → p b = q b :=
        fun b member => agree b (List.mem_cons_of_mem _ member)
      have headAgree : p a = q a := agree a (by simp)
      simp only [List.all_cons, headAgree, ih restAgree]

/-- any only depends on the predicate over the list members. -/
private theorem any_congr_mem {l : List Nat} {p q : Nat → Bool}
    (agree : ∀ a, a ∈ l → p a = q a) : l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
      have restAgree : ∀ b, b ∈ rest → p b = q b :=
        fun b member => agree b (List.mem_cons_of_mem _ member)
      have headAgree : p a = q a := agree a (by simp)
      simp only [List.any_cons, headAgree, ih restAgree]

/-- Plasma members live in the unspliced letter list. -/
private theorem mem_of_mem_plasmaSeq {h c : Nat} {A B : List Nat}
    {p : Nat} (member : p ∈ plasmaSeq (⟨h, A ++ B⟩ : Word Nat)) :
    p ∈ (h :: A) ++ B := by
  simp only [plasmaSeq] at member
  have inDups := (List.mem_filter.mp member).1
  obtain ⟨listL, listR⟩ := toList_splice h c A B
  rw [listR] at inDups
  exact mem_of_mem_eraseDups inDups

private theorem beforeOpenList_splice {h c : Nat} {A B : List Nat}
    (beforeMem : c ∈ h :: A) (afterMem : c ∈ B) {s : Nat}
    (sMem : s ∈ (h :: A) ++ B) :
    beforeOpenList (⟨h, A ++ c :: B⟩ : Word Nat) s =
      beforeOpenList (⟨h, A ++ B⟩ : Word Nat) s := by
  obtain ⟨listL, listR⟩ := toList_splice h c A B
  simp only [beforeOpenList]
  rw [listL, listR, plasmaSeq_splice beforeMem afterMem]
  apply filter_congr_mem
  intro p pMem
  have pIn : p ∈ (h :: A) ++ B :=
    mem_of_mem_plasmaSeq (c := c) pMem
  exact decide_eq_decide.mpr
    (cond_stab beforeMem afterMem sMem pIn).1

private theorem rel4_splice {h c : Nat} {A B : List Nat}
    (beforeMem : c ∈ h :: A) (afterMem : c ∈ B) {s : Nat}
    (sMem : s ∈ (h :: A) ++ B) :
    rel4 (⟨h, A ++ c :: B⟩ : Word Nat) s =
      rel4 (⟨h, A ++ B⟩ : Word Nat) s := by
  obtain ⟨listL, listR⟩ := toList_splice h c A B
  simp only [rel4]
  rw [listL, listR, plasmaSeq_splice beforeMem afterMem]
  have c1 : (plasmaSeq (⟨h, A ++ B⟩ : Word Nat)).all
      (fun p => ((h :: A) ++ c :: B).idxOf s <
        ((h :: A) ++ c :: B).idxOf p) =
      (plasmaSeq (⟨h, A ++ B⟩ : Word Nat)).all
      (fun p => ((h :: A) ++ B).idxOf s < ((h :: A) ++ B).idxOf p) := by
    apply all_congr_mem
    intro p pMem
    have pIn : p ∈ (h :: A) ++ B := mem_of_mem_plasmaSeq (c := c) pMem
    exact decide_eq_decide.mpr
      (cond_stab beforeMem afterMem sMem pIn).1
  have c2 : (plasmaSeq (⟨h, A ++ B⟩ : Word Nat)).all
      (fun p => lastIdxOf ((h :: A) ++ c :: B) p <
        ((h :: A) ++ c :: B).idxOf s) =
      (plasmaSeq (⟨h, A ++ B⟩ : Word Nat)).all
      (fun p => lastIdxOf ((h :: A) ++ B) p <
        ((h :: A) ++ B).idxOf s) := by
    apply all_congr_mem
    intro p pMem
    have pIn : p ∈ (h :: A) ++ B := mem_of_mem_plasmaSeq (c := c) pMem
    exact decide_eq_decide.mpr
      (cond_stab beforeMem afterMem sMem pIn).2.1
  have c3 : (plasmaSeq (⟨h, A ++ B⟩ : Word Nat)).any
      (fun p => ((h :: A) ++ c :: B).idxOf p <
          ((h :: A) ++ c :: B).idxOf s &&
        (((h :: A) ++ c :: B).idxOf s <
          lastIdxOf ((h :: A) ++ c :: B) p)) =
      (plasmaSeq (⟨h, A ++ B⟩ : Word Nat)).any
      (fun p => ((h :: A) ++ B).idxOf p < ((h :: A) ++ B).idxOf s &&
        (((h :: A) ++ B).idxOf s < lastIdxOf ((h :: A) ++ B) p)) := by
    apply any_congr_mem
    intro p pMem
    have pIn : p ∈ (h :: A) ++ B := mem_of_mem_plasmaSeq (c := c) pMem
    rw [decide_eq_decide.mpr (cond_stab beforeMem afterMem pIn sMem).1,
      decide_eq_decide.mpr (cond_stab beforeMem afterMem sMem pIn).2.2]
  rw [c1, c2, c3]

private theorem slotOf_splice {h c : Nat} {A B : List Nat}
    (beforeMem : c ∈ h :: A) (afterMem : c ∈ B) {s : Nat}
    (sMem : s ∈ (h :: A) ++ B) :
    slotOf (⟨h, A ++ c :: B⟩ : Word Nat) s =
      slotOf (⟨h, A ++ B⟩ : Word Nat) s := by
  obtain ⟨listL, listR⟩ := toList_splice h c A B
  simp only [slotOf]
  rw [listL, listR, plasmaSeq_splice beforeMem afterMem]
  congr 1
  apply takeWhile_congr_mem
  intro p pMem
  have pIn : p ∈ (h :: A) ++ B := mem_of_mem_plasmaSeq (c := c) pMem
  exact decide_eq_decide.mpr
    (cond_stab beforeMem afterMem pIn sMem).1

/-! ## Middle-occurrence dropping: derivability and signature transport -/

/-- Word append unfolded to the record literal (for simp). -/
private theorem append_mk (u v : Word Nat) :
    u ++ v = (⟨u.head, u.tail ++ v.head :: v.tail⟩ : Word Nat) := rfl

/-- The bare drop move `cVcWc ~ cVWc` (four emptiness cases route to
four different laws, all read right-to-left). -/
private theorem derivesDropMidCore (c : Nat) (V W : List Nat) :
    Derives basis (⟨c, V ++ (c :: (W ++ [c]))⟩ : Word Nat)
      (⟨c, V ++ (W ++ [c])⟩ : Word Nat) := by
  cases V with
  | nil =>
    cases W with
    | nil =>
        have move := Derives.symm (derivesPower (Word.singleton c))
        simpa [Word.singleton, append_mk] using move
    | cons w0 W' =>
        have move := Derives.symm
          (derivesLeftDuplication (Word.singleton c) (⟨w0, W'⟩ : Word Nat))
        simpa [Word.singleton, append_mk] using move
  | cons v0 V' =>
    cases W with
    | nil =>
        have move := Derives.symm
          (derivesRightDuplication (Word.singleton c) (⟨v0, V'⟩ : Word Nat))
        simpa [Word.singleton, append_mk] using move
    | cons w0 W' =>
        have move := Derives.symm
          (derivesMiddleReduplication (Word.singleton c)
            (⟨v0, V'⟩ : Word Nat) (⟨w0, W'⟩ : Word Nat))
        simpa [Word.singleton, append_mk] using move

/-- Dropping a middle occurrence (one earlier and one later occurrence
exist) is derivable from the displayed basis. -/
private theorem derivesDropMid {h c : Nat} {A B : List Nat}
    (beforeMem : c ∈ h :: A) (afterMem : c ∈ B) :
    Derives basis (⟨h, A ++ c :: B⟩ : Word Nat)
      (⟨h, A ++ B⟩ : Word Nat) := by
  obtain ⟨U, V, splitUV⟩ := List.append_of_mem beforeMem
  obtain ⟨W, X, splitWX⟩ := List.append_of_mem afterMem
  cases U with
  | nil =>
      rw [List.nil_append] at splitUV
      injection splitUV with headEq tailEq
      subst headEq
      subst tailEq
      have wrapped := derivesFactor (derivesDropMidCore h A W) none X
      simpa [splitWX, List.append_assoc] using wrapped
  | cons u0 U' =>
      injection splitUV with headEq tailEq
      subst headEq
      subst tailEq
      have wrapped := derivesFactor (derivesDropMidCore c V W)
        (some (⟨h, U'⟩ : Word Nat)) X
      simpa [splitWX, append_mk, List.append_assoc] using wrapped

/-- Dropping a middle occurrence preserves the full D_378 signature. -/
private theorem sameSignature_dropMid {h c : Nat} {A B : List Nat}
    (beforeMem : c ∈ h :: A) (afterMem : c ∈ B) :
    SameD378Signature (⟨h, A ++ c :: B⟩ : Word Nat)
      (⟨h, A ++ B⟩ : Word Nat) := by
  refine ⟨rfl, singlesSeq_splice beforeMem afterMem,
    plasmaSeq_splice beforeMem afterMem, ?_⟩
  intro s single
  obtain ⟨listL, listR⟩ := toList_splice h c A B
  have countOne : ((h :: A) ++ c :: B).count s = 1 := by
    have := single
    simp only [IsSingle, letterCount] at this
    rw [listL] at this
    exact this
  have sne : s ≠ c := by
    intro equal
    subst equal
    have inP : 0 < (h :: A).count s := List.count_pos_iff.mpr beforeMem
    have inB : 0 < B.count s := List.count_pos_iff.mpr afterMem
    rw [List.count_append] at countOne
    have consCount : (s :: B).count s = B.count s + 1 := by simp
    omega
  have countUn : ((h :: A) ++ B).count s = 1 := by
    have splice := count_splice (P := h :: A) (B := B) (c := c) (e := s)
    rw [if_neg sne] at splice
    omega
  have sMem : s ∈ (h :: A) ++ B :=
    List.count_pos_iff.mp (by omega)
  exact ⟨beforeOpenList_splice beforeMem afterMem sMem,
    rel4_splice beforeMem afterMem sMem⟩

/-! ## Collapse to skeleton: every word reaches counts ≤ 2 -/

/-- Split a list at the first occurrence of a member. -/
private theorem firstSplit {T : List Nat} {c : Nat} (member : c ∈ T) :
    ∃ A B, T = A ++ c :: B ∧ c ∉ A := by
  induction T with
  | nil => cases member
  | cons a rest ih =>
      by_cases ac : a = c
      · exact ⟨[], rest, by simp [ac], by simp⟩
      · have restMem : c ∈ rest := by
          rcases List.mem_cons.mp member with equal | tailMem
          · exact absurd equal.symm ac
          · exact tailMem
        obtain ⟨A, B, shape, notInA⟩ := ih restMem
        refine ⟨a :: A, B, by rw [shape]; rfl, ?_⟩
        intro inCons
        rcases List.mem_cons.mp inCons with equal | tailMem
        · exact ac equal.symm
        · exact notInA tailMem

/-- A letter of count ≥ 3 has a middle occurrence: a tail decomposition
with one occurrence strictly before and one strictly after. -/
private theorem middleDecomp {h c : Nat} {T : List Nat}
    (big : 3 ≤ List.count c (h :: T)) :
    ∃ A B, T = A ++ c :: B ∧ c ∈ h :: A ∧ c ∈ B := by
  by_cases hc : h = c
  · have expand : List.count c (h :: T) = List.count c T + 1 := by
      rw [hc, List.count_cons_self]
    have memT : c ∈ T := List.count_pos_iff.mp (by omega)
    obtain ⟨A, B, shape, notInA⟩ := firstSplit memT
    have countA : List.count c A = 0 := List.count_eq_zero.mpr notInA
    have expandT : List.count c T =
        List.count c A + (List.count c B + 1) := by
      rw [shape]
      simp [List.count_append]
    refine ⟨A, B, shape, ?_, List.count_pos_iff.mp (by omega)⟩
    rw [hc]
    exact List.mem_cons_self
  · have expand : List.count c (h :: T) = List.count c T :=
      List.count_cons_of_ne hc
    have memT : c ∈ T := List.count_pos_iff.mp (by omega)
    obtain ⟨A0, B0, shape0, notInA0⟩ := firstSplit memT
    have countA0 : List.count c A0 = 0 := List.count_eq_zero.mpr notInA0
    have expandT : List.count c T =
        List.count c A0 + (List.count c B0 + 1) := by
      rw [shape0]
      simp [List.count_append]
    have memB0 : c ∈ B0 := List.count_pos_iff.mp (by omega)
    obtain ⟨A1, B1, shape1, notInA1⟩ := firstSplit memB0
    have countA1 : List.count c A1 = 0 := List.count_eq_zero.mpr notInA1
    have expandB0 : List.count c B0 =
        List.count c A1 + (List.count c B1 + 1) := by
      rw [shape1]
      simp [List.count_append]
    refine ⟨A0 ++ c :: A1, B1, ?_, ?_,
      List.count_pos_iff.mp (by omega)⟩
    · rw [shape0, shape1]
      simp
    · exact List.mem_cons_of_mem _ (by simp)

/-- Signature equality is reflexive. -/
private theorem sameSignature_refl (u : Word Nat) :
    SameD378Signature u u :=
  ⟨rfl, rfl, rfl, fun _ _ => ⟨rfl, rfl⟩⟩

/-- Singleness transports along signature equality. -/
private theorem isSingle_of_sameSignature {u v : Word Nat}
    (same : SameD378Signature u v) {s : Nat} (single : IsSingle u s) :
    IsSingle v s := by
  have cnt : List.count s u.toList = 1 := single
  have memSingles : s ∈ singlesSeq u := by
    simp only [singlesSeq, List.mem_filter]
    exact ⟨List.count_pos_iff.mp (by omega), by simp [cnt]⟩
  rw [same.2.1] at memSingles
  simp only [singlesSeq, List.mem_filter] at memSingles
  have verdict := memSingles.2
  simp only [beq_iff_eq] at verdict
  exact verdict

/-- Signature equality is transitive. -/
private theorem sameSignature_trans {u v x : Word Nat}
    (uv : SameD378Signature u v) (vx : SameD378Signature v x) :
    SameD378Signature u x := by
  obtain ⟨h1, s1, p1, r1⟩ := uv
  obtain ⟨h2, s2, p2, r2⟩ := vx
  refine ⟨h1.trans h2, s1.trans s2, p1.trans p2, ?_⟩
  intro s single
  obtain ⟨b1, rr1⟩ := r1 s single
  obtain ⟨b2, rr2⟩ := r2 s
    (isSingle_of_sameSignature ⟨h1, s1, p1, r1⟩ single)
  exact ⟨b1.trans b2, rr1.trans rr2⟩

/-- Every word derives to a signature-equal skeleton with all letter
counts at most two. -/
private theorem collapseToSkeleton :
    ∀ (n : Nat) (u : Word Nat), u.tail.length ≤ n →
      ∃ v : Word Nat, Derives basis u v ∧ SameD378Signature u v ∧
        ∀ x : Nat, letterCount v x ≤ 2 := by
  intro n
  induction n with
  | zero =>
      intro u bound
      obtain ⟨h, T⟩ := u
      cases T with
      | cons a t => simp at bound
      | nil =>
          refine ⟨⟨h, []⟩, Derives.refl _, sameSignature_refl _, ?_⟩
          intro x
          have small : List.count x [h] ≤ 1 := by
            by_cases xh : x = h
            · subst xh
              simp
            · rw [List.count_cons_of_ne (fun e => xh e.symm)]
              simp
          have same : letterCount (⟨h, []⟩ : Word Nat) x =
              List.count x [h] := rfl
          omega
  | succ n ih =>
      intro u bound
      by_cases allSmall : ∀ x : Nat, letterCount u x ≤ 2
      · exact ⟨u, Derives.refl u, sameSignature_refl u, allSmall⟩
      · obtain ⟨c, cBig⟩ := Classical.not_forall.mp allSmall
        obtain ⟨h, T⟩ := u
        have bigList : 3 ≤ List.count c (h :: T) := by
          have expand : letterCount (⟨h, T⟩ : Word Nat) c =
              List.count c (h :: T) := rfl
          omega
        obtain ⟨A, B, shape, beforeMem, afterMem⟩ := middleDecomp bigList
        subst shape
        have step := derivesDropMid beforeMem afterMem
        have sig := sameSignature_dropMid beforeMem afterMem
        have lenBound : (A ++ c :: B).length ≤ n + 1 := bound
        have goalLen : (A ++ B).length ≤ n := by
          simp only [List.length_append, List.length_cons] at lenBound
          simp only [List.length_append]
          omega
        obtain ⟨v, deriv, same, small⟩ :=
          ih (⟨h, A ++ B⟩ : Word Nat) goalLen
        exact ⟨v, Derives.trans step deriv,
          sameSignature_trans sig same, small⟩

/-! ## Snoc coordinate toolkit: appending one fresh letter -/

private theorem toList_mk (h : Nat) (T : List Nat) :
    (⟨h, T⟩ : Word Nat).toList = h :: T := rfl

/-- The appended letter's last index is the old length. -/
private theorem lastIdxOf_append_self (l : List Nat) (x : Nat) :
    lastIdxOf (l ++ [x]) x = l.length := by
  have reverseShape : (l ++ [x]).reverse = x :: l.reverse := by simp
  rw [lastIdxOf, reverseShape]
  simp [List.idxOf_cons]

/-- Members have a last index below the length. -/
private theorem lastIdxOf_lt_length {l : List Nat} {e : Nat}
    (member : e ∈ l) : lastIdxOf l e < l.length := by
  have posLen : 0 < l.length := by
    cases l with
    | nil => cases member
    | cons a t => simp
  rw [lastIdxOf]
  omega

/-- A fresh appended letter passes through eraseDups to the end. -/
private theorem eraseDups_snoc_fresh {l : List Nat} {x : Nat}
    (fresh : x ∉ l) :
    (l ++ [x]).eraseDups = l.eraseDups ++ [x] := by
  have loop : ∀ (rest seen : List Nat), x ∉ rest → x ∉ seen →
      List.eraseDupsBy.loop (fun a b => a == b) (rest ++ [x]) seen =
        List.eraseDupsBy.loop (fun a b => a == b) rest seen ++ [x] := by
    intro rest
    induction rest with
    | nil =>
        intro seen _ seenFresh
        rw [List.nil_append, List.eraseDupsBy.loop,
          List.eraseDupsBy.loop]
        have anyMiss : seen.any (fun b => x == b) = false := by
          cases verdict : seen.any (fun b => x == b)
          · rfl
          · exfalso
            rw [List.any_eq_true] at verdict
            obtain ⟨b, bMem, hit⟩ := verdict
            have xb : x = b := by simpa using hit
            exact seenFresh (xb ▸ bMem)
        rw [anyMiss]
        have unfoldInner : List.eraseDupsBy.loop (fun a b => a == b) []
            (x :: seen) = (x :: seen).reverse := by
          rw [List.eraseDupsBy.loop]
        simp [unfoldInner]
    | cons a restTail ih =>
        intro seen consFresh seenFresh
        have aNe : a ≠ x := by
          intro equal
          exact consFresh (equal ▸ List.mem_cons_self)
        have tailFresh : x ∉ restTail :=
          fun member => consFresh (List.mem_cons_of_mem _ member)
        rw [List.cons_append, List.eraseDupsBy.loop,
          List.eraseDupsBy.loop]
        by_cases anyHit : seen.any (fun b => a == b) = true
        · rw [anyHit]
          simp only [if_true]
          exact ih seen tailFresh seenFresh
        · have anyMiss : seen.any (fun b => a == b) = false := by
            cases verdict : seen.any (fun b => a == b)
            · rfl
            · exact absurd verdict anyHit
          rw [anyMiss]
          simp only [if_false]
          have seenFresh' : x ∉ a :: seen := by
            intro member
            rcases List.mem_cons.mp member with equal | tailMem
            · exact aNe equal.symm
            · exact seenFresh tailMem
          exact ih (a :: seen) tailFresh seenFresh'
  rw [List.eraseDups, List.eraseDups, List.eraseDupsBy,
    List.eraseDupsBy]
  exact loop l [] fresh (by simp)

/-- All-true predicates keep the whole list under takeWhile. -/
private theorem takeWhile_all {l : List Nat} {q : Nat → Bool}
    (allTrue : ∀ a, a ∈ l → q a = true) : l.takeWhile q = l := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
      simp [List.takeWhile_cons, allTrue a (by simp),
        ih (fun b member => allTrue b (List.mem_cons_of_mem _ member))]

/-- Plasma members live in the letter list (generic form). -/
private theorem mem_toList_of_mem_plasmaSeq {u : Word Nat} {p : Nat}
    (member : p ∈ plasmaSeq u) : p ∈ u.toList :=
  mem_of_mem_eraseDups (List.mem_filter.mp member).1

/-- List-level singles filter under a fresh snoc. -/
private theorem singlesList_snoc_fresh {L : List Nat} {x : Nat}
    (fresh : x ∉ L) :
    (L ++ [x]).filter (fun c => (L ++ [x]).count c == 1) =
      L.filter (fun c => L.count c == 1) ++ [x] := by
  rw [List.filter_append]
  congr 1
  · apply filter_congr_mem
    intro e eMem
    have ne : e ≠ x := fun equal => fresh (equal ▸ eMem)
    rw [count_append_ne ne]
  · have countX : (L ++ [x]).count x = 1 := by
      rw [count_append_self, List.count_eq_zero.mpr fresh]
    rw [List.filter_cons, countX]
    simp

/-- Appending a fresh letter appends it to the singles sequence. -/
private theorem singlesSeq_snoc_fresh {h x : Nat} {T : List Nat}
    (fresh : x ∉ h :: T) :
    singlesSeq (⟨h, T ++ [x]⟩ : Word Nat) =
      singlesSeq (⟨h, T⟩ : Word Nat) ++ [x] :=
  singlesList_snoc_fresh (L := h :: T) fresh

/-- List-level plasma filter under a fresh snoc. -/
private theorem plasmaList_snoc_fresh {L : List Nat} {x : Nat}
    (fresh : x ∉ L) :
    (L ++ [x]).eraseDups.filter (fun c => 2 ≤ (L ++ [x]).count c) =
      L.eraseDups.filter (fun c => 2 ≤ L.count c) := by
  rw [eraseDups_snoc_fresh fresh, List.filter_append]
  have rightNil : List.filter
      (fun c => decide (2 ≤ (L ++ [x]).count c)) [x] = [] := by
    have countX : (L ++ [x]).count x = 1 := by
      rw [count_append_self, List.count_eq_zero.mpr fresh]
    rw [List.filter_cons, countX]
    simp
  rw [rightNil, List.append_nil]
  apply filter_congr_mem
  intro e eMem
  have eIn : e ∈ L := mem_of_mem_eraseDups eMem
  have ne : e ≠ x := fun equal => fresh (equal ▸ eIn)
  rw [count_append_ne ne]

/-- Appending a fresh letter leaves the plasma sequence unchanged. -/
private theorem plasmaSeq_snoc_fresh {h x : Nat} {T : List Nat}
    (fresh : x ∉ h :: T) :
    plasmaSeq (⟨h, T ++ [x]⟩ : Word Nat) =
      plasmaSeq (⟨h, T⟩ : Word Nat) :=
  plasmaList_snoc_fresh (L := h :: T) fresh

/-- Members of the list-level plasma filter are members of the list. -/
private theorem mem_of_mem_plasmaList {L : List Nat} {p : Nat}
    (member : p ∈ L.eraseDups.filter (fun c => 2 ≤ L.count c)) :
    p ∈ L :=
  mem_of_mem_eraseDups (List.mem_filter.mp member).1

/-- Old letters keep their before-open lists under a fresh snoc. -/
private theorem beforeOpenList_snoc_fresh {h x : Nat} {T : List Nat}
    (fresh : x ∉ h :: T) {s : Nat} (sMem : s ∈ h :: T) :
    beforeOpenList (⟨h, T ++ [x]⟩ : Word Nat) s =
      beforeOpenList (⟨h, T⟩ : Word Nat) s := by
  have core : ∀ (L : List Nat), x ∉ L → s ∈ L →
      ((L ++ [x]).eraseDups.filter
        (fun c => 2 ≤ (L ++ [x]).count c)).filter
        (fun p => (L ++ [x]).idxOf s < (L ++ [x]).idxOf p) =
      (L.eraseDups.filter (fun c => 2 ≤ L.count c)).filter
        (fun p => L.idxOf s < L.idxOf p) := by
    intro L freshL sMemL
    rw [plasmaList_snoc_fresh freshL]
    apply filter_congr_mem
    intro p pMem
    have pIn : p ∈ L := mem_of_mem_plasmaList pMem
    rw [idxOf_append_of_mem sMemL x, idxOf_append_of_mem pIn x]
  exact core (h :: T) fresh sMem

/-- Old letters keep their four-way relation under a fresh snoc. -/
private theorem rel4_snoc_fresh {h x : Nat} {T : List Nat}
    (fresh : x ∉ h :: T) {s : Nat} (sMem : s ∈ h :: T) :
    rel4 (⟨h, T ++ [x]⟩ : Word Nat) s =
      rel4 (⟨h, T⟩ : Word Nat) s := by
  have core : ∀ (L : List Nat), x ∉ L → s ∈ L →
      (if ((L ++ [x]).eraseDups.filter
            (fun c => 2 ≤ (L ++ [x]).count c)).all
          (fun p => (L ++ [x]).idxOf s < (L ++ [x]).idxOf p) then
        Rel4.before
      else if ((L ++ [x]).eraseDups.filter
            (fun c => 2 ≤ (L ++ [x]).count c)).all
          (fun p => lastIdxOf (L ++ [x]) p < (L ++ [x]).idxOf s) then
        Rel4.after
      else if ((L ++ [x]).eraseDups.filter
            (fun c => 2 ≤ (L ++ [x]).count c)).any
          (fun p => (L ++ [x]).idxOf p < (L ++ [x]).idxOf s &&
            ((L ++ [x]).idxOf s < lastIdxOf (L ++ [x]) p)) then
        Rel4.inside
      else Rel4.gap) =
      (if (L.eraseDups.filter (fun c => 2 ≤ L.count c)).all
          (fun p => L.idxOf s < L.idxOf p) then Rel4.before
      else if (L.eraseDups.filter (fun c => 2 ≤ L.count c)).all
          (fun p => lastIdxOf L p < L.idxOf s) then Rel4.after
      else if (L.eraseDups.filter (fun c => 2 ≤ L.count c)).any
          (fun p => L.idxOf p < L.idxOf s &&
            (L.idxOf s < lastIdxOf L p)) then Rel4.inside
      else Rel4.gap) := by
    intro L freshL sMemL
    rw [plasmaList_snoc_fresh freshL]
    have memData : ∀ p,
        p ∈ L.eraseDups.filter (fun c => 2 ≤ L.count c) →
        p ∈ L ∧ p ≠ x := by
      intro p pMem
      have pIn : p ∈ L := mem_of_mem_plasmaList pMem
      exact ⟨pIn, fun equal => freshL (equal ▸ pIn)⟩
    have c1 : (L.eraseDups.filter (fun c => 2 ≤ L.count c)).all
        (fun p => (L ++ [x]).idxOf s < (L ++ [x]).idxOf p) =
        (L.eraseDups.filter (fun c => 2 ≤ L.count c)).all
        (fun p => L.idxOf s < L.idxOf p) := by
      apply all_congr_mem
      intro p pMem
      obtain ⟨pIn, _⟩ := memData p pMem
      rw [idxOf_append_of_mem sMemL x, idxOf_append_of_mem pIn x]
    have c2 : (L.eraseDups.filter (fun c => 2 ≤ L.count c)).all
        (fun p => lastIdxOf (L ++ [x]) p < (L ++ [x]).idxOf s) =
        (L.eraseDups.filter (fun c => 2 ≤ L.count c)).all
        (fun p => lastIdxOf L p < L.idxOf s) := by
      apply all_congr_mem
      intro p pMem
      obtain ⟨pIn, pNe⟩ := memData p pMem
      rw [lastIdxOf_append_ne pIn pNe, idxOf_append_of_mem sMemL x]
    have c3 : (L.eraseDups.filter (fun c => 2 ≤ L.count c)).any
        (fun p => (L ++ [x]).idxOf p < (L ++ [x]).idxOf s &&
          ((L ++ [x]).idxOf s < lastIdxOf (L ++ [x]) p)) =
        (L.eraseDups.filter (fun c => 2 ≤ L.count c)).any
        (fun p => L.idxOf p < L.idxOf s &&
          (L.idxOf s < lastIdxOf L p)) := by
      apply any_congr_mem
      intro p pMem
      obtain ⟨pIn, pNe⟩ := memData p pMem
      rw [idxOf_append_of_mem sMemL x, idxOf_append_of_mem pIn x,
        lastIdxOf_append_ne pIn pNe]
    rw [c1, c2, c3]
  exact core (h :: T) fresh sMem

/-- Old letters keep their slots under a fresh snoc. -/
private theorem slotOf_snoc_fresh {h x : Nat} {T : List Nat}
    (fresh : x ∉ h :: T) {s : Nat} (sMem : s ∈ h :: T) :
    slotOf (⟨h, T ++ [x]⟩ : Word Nat) s =
      slotOf (⟨h, T⟩ : Word Nat) s := by
  have core : ∀ (L : List Nat), x ∉ L → s ∈ L →
      (((L ++ [x]).eraseDups.filter
        (fun c => 2 ≤ (L ++ [x]).count c)).takeWhile
        (fun p => (L ++ [x]).idxOf p < (L ++ [x]).idxOf s)).length =
      ((L.eraseDups.filter (fun c => 2 ≤ L.count c)).takeWhile
        (fun p => L.idxOf p < L.idxOf s)).length := by
    intro L freshL sMemL
    rw [plasmaList_snoc_fresh freshL]
    congr 1
    apply takeWhile_congr_mem
    intro p pMem
    have pIn : p ∈ L := mem_of_mem_plasmaList pMem
    rw [idxOf_append_of_mem pIn x, idxOf_append_of_mem sMemL x]
  exact core (h :: T) fresh sMem

/-- The fresh letter's slot is the full plasma count. -/
private theorem slotOf_snoc_self_fresh {h x : Nat} {T : List Nat}
    (fresh : x ∉ h :: T) :
    slotOf (⟨h, T ++ [x]⟩ : Word Nat) x =
      (plasmaSeq (⟨h, T⟩ : Word Nat)).length := by
  have core : ∀ (L : List Nat), x ∉ L →
      (((L ++ [x]).eraseDups.filter
        (fun c => 2 ≤ (L ++ [x]).count c)).takeWhile
        (fun p => (L ++ [x]).idxOf p < (L ++ [x]).idxOf x)).length =
      (L.eraseDups.filter (fun c => 2 ≤ L.count c)).length := by
    intro L freshL
    rw [plasmaList_snoc_fresh freshL]
    congr 1
    apply takeWhile_all
    intro p pMem
    have pIn : p ∈ L := mem_of_mem_plasmaList pMem
    rw [idxOf_append_of_mem pIn x, idxOf_append_self_of_not_mem freshL]
    exact decide_eq_true (idxOf_lt_length_of_mem_local pIn)
  exact core (h :: T) fresh

/-- The fresh letter's relation is after (nonempty plasma). -/
private theorem rel4_snoc_self_fresh {h x : Nat} {T : List Nat}
    (fresh : x ∉ h :: T)
    (nonempty : plasmaSeq (⟨h, T⟩ : Word Nat) ≠ []) :
    rel4 (⟨h, T ++ [x]⟩ : Word Nat) x = Rel4.after := by
  have core : ∀ (L : List Nat), x ∉ L →
      L.eraseDups.filter (fun c => 2 ≤ L.count c) ≠ [] →
      (if ((L ++ [x]).eraseDups.filter
            (fun c => 2 ≤ (L ++ [x]).count c)).all
          (fun p => (L ++ [x]).idxOf x < (L ++ [x]).idxOf p) then
        Rel4.before
      else if ((L ++ [x]).eraseDups.filter
            (fun c => 2 ≤ (L ++ [x]).count c)).all
          (fun p => lastIdxOf (L ++ [x]) p < (L ++ [x]).idxOf x) then
        Rel4.after
      else if ((L ++ [x]).eraseDups.filter
            (fun c => 2 ≤ (L ++ [x]).count c)).any
          (fun p => (L ++ [x]).idxOf p < (L ++ [x]).idxOf x &&
            ((L ++ [x]).idxOf x < lastIdxOf (L ++ [x]) p)) then
        Rel4.inside
      else Rel4.gap) = Rel4.after := by
    intro L freshL nonemptyL
    rw [plasmaList_snoc_fresh freshL]
    have notBefore : (L.eraseDups.filter (fun c => 2 ≤ L.count c)).all
        (fun p => (L ++ [x]).idxOf x < (L ++ [x]).idxOf p) = false := by
      obtain ⟨p0, rest, shape⟩ := List.exists_cons_of_ne_nil nonemptyL
      have p0Mem : p0 ∈ L.eraseDups.filter (fun c => 2 ≤ L.count c) := by
        rw [shape]
        exact List.mem_cons_self
      have p0In : p0 ∈ L := mem_of_mem_plasmaList p0Mem
      rw [shape, List.all_cons]
      have headFalse : decide ((L ++ [x]).idxOf x <
          (L ++ [x]).idxOf p0) = false := by
        rw [idxOf_append_of_mem p0In x,
          idxOf_append_self_of_not_mem freshL]
        have bound := idxOf_lt_length_of_mem_local p0In
        simp
        omega
      rw [headFalse]
      simp
    have allAfter : (L.eraseDups.filter (fun c => 2 ≤ L.count c)).all
        (fun p => lastIdxOf (L ++ [x]) p < (L ++ [x]).idxOf x) =
        true := by
      rw [List.all_eq_true]
      intro p pMem
      have pIn : p ∈ L := mem_of_mem_plasmaList pMem
      have pNe : p ≠ x := fun equal => freshL (equal ▸ pIn)
      rw [lastIdxOf_append_ne pIn pNe,
        idxOf_append_self_of_not_mem freshL]
      exact decide_eq_true (lastIdxOf_lt_length pIn)
    rw [notBefore, allAfter]
    simp
  exact core (h :: T) fresh nonempty

/-! ## Fresh-letter insertion: the canonical word extends by the letter -/

/-- Stripped singles are singles. -/
private theorem mem_singles_of_mem_stripped {u : Word Nat} {s : Nat}
    (member : s ∈ strippedSingles u) : s ∈ singlesSeq u := by
  simp only [strippedSingles] at member
  split at member
  · exact List.mem_of_mem_drop member
  · exact member

/-- Singles are letters of the word. -/
private theorem mem_toList_of_mem_singlesSeq {u : Word Nat} {s : Nat}
    (member : s ∈ singlesSeq u) : s ∈ u.toList :=
  (List.mem_filter.mp member).1

/-- With no plasma letters every relation is before. -/
private theorem rel4_of_plasma_nil {u : Word Nat} {s : Nat}
    (empty : plasmaSeq u = []) : rel4 u s = Rel4.before := by
  simp only [rel4, empty, List.all_nil]
  rfl

/-- The stripped singles extend by a fresh appended letter. -/
private theorem strippedSingles_snoc_fresh {h x : Nat} {T : List Nat}
    (fresh : x ∉ h :: T) :
    strippedSingles (⟨h, T ++ [x]⟩ : Word Nat) =
      strippedSingles (⟨h, T⟩ : Word Nat) ++ [x] := by
  have headNe : h ≠ x := fun equal => fresh (equal ▸ List.mem_cons_self)
  have plasmaHead : decide (IsPlasma (⟨h, T ++ [x]⟩ : Word Nat) h) =
      decide (IsPlasma (⟨h, T⟩ : Word Nat) h) := by
    apply decide_eq_decide.mpr
    simp only [IsPlasma, letterCount]
    have countHead : (⟨h, T ++ [x]⟩ : Word Nat).toList.count h =
        (⟨h, T⟩ : Word Nat).toList.count h := by
      show ((h :: T) ++ [x]).count h = (h :: T).count h
      exact count_append_ne headNe
    rw [countHead]
  have takeHead : decide (List.take 1
      (singlesSeq (⟨h, T⟩ : Word Nat) ++ [x]) = [h]) =
      decide (List.take 1 (singlesSeq (⟨h, T⟩ : Word Nat)) = [h]) := by
    apply decide_eq_decide.mpr
    cases sShape : singlesSeq (⟨h, T⟩ : Word Nat) with
    | nil =>
        simp
        exact fun equal => headNe equal.symm
    | cons s0 rest => simp
  simp only [strippedSingles, plasmaHead, singlesSeq_snoc_fresh fresh]
  rw [takeHead]
  by_cases cond : (decide (List.take 1
      (singlesSeq (⟨h, T⟩ : Word Nat)) = [h]) &&
      !decide (IsPlasma (⟨h, T⟩ : Word Nat) h)) = true
  · rw [if_pos cond, if_pos cond]
    have nonNil : singlesSeq (⟨h, T⟩ : Word Nat) ≠ [] := by
      intro isNil
      rw [isNil] at cond
      simp at cond
    cases sShape : singlesSeq (⟨h, T⟩ : Word Nat) with
    | nil => exact absurd sShape nonNil
    | cons s0 rest => simp
  · rw [if_neg cond, if_neg cond]

/-- Blocks are unchanged by a fresh snoc (nonempty plasma). -/
private theorem blockOf_snoc_fresh {h x : Nat} {T : List Nat}
    (fresh : x ∉ h :: T)
    (nonempty : plasmaSeq (⟨h, T⟩ : Word Nat) ≠ []) (i p : Nat) :
    blockOf (⟨h, T ++ [x]⟩ : Word Nat) i p =
      blockOf (⟨h, T⟩ : Word Nat) i p := by
  have filterEq : ∀ (r : Rel4), (r == Rel4.after) = false →
      (strippedSingles (⟨h, T ++ [x]⟩ : Word Nat)).filter
        (fun s => slotOf (⟨h, T ++ [x]⟩ : Word Nat) s == i + 1 &&
          rel4 (⟨h, T ++ [x]⟩ : Word Nat) s == r) =
      (strippedSingles (⟨h, T⟩ : Word Nat)).filter
        (fun s => slotOf (⟨h, T⟩ : Word Nat) s == i + 1 &&
          rel4 (⟨h, T⟩ : Word Nat) s == r) := by
    intro r rNe
    rw [strippedSingles_snoc_fresh fresh, List.filter_append]
    have xGone : List.filter
        (fun s => slotOf (⟨h, T ++ [x]⟩ : Word Nat) s == i + 1 &&
          rel4 (⟨h, T ++ [x]⟩ : Word Nat) s == r) [x] = [] := by
      rw [List.filter_cons]
      have relNe : (rel4 (⟨h, T ++ [x]⟩ : Word Nat) x == r) = false := by
        rw [rel4_snoc_self_fresh fresh nonempty]
        cases r with
        | after => simp at rNe
        | before => rfl
        | inside => rfl
        | gap => rfl
      rw [relNe, Bool.and_false]
      simp
    rw [xGone, List.append_nil]
    apply filter_congr_mem
    intro s sMem
    have sIn : s ∈ h :: T := mem_toList_of_mem_singlesSeq
      (mem_singles_of_mem_stripped sMem)
    rw [slotOf_snoc_fresh fresh sIn, rel4_snoc_fresh fresh sIn]
  simp only [blockOf]
  rw [filterEq Rel4.inside (by decide), filterEq Rel4.gap (by decide)]

/-- Appending a fresh letter appends it to the canonical word. -/
private theorem canonicalize_snoc_fresh {h x : Nat} {T : List Nat}
    (fresh : x ∉ h :: T) :
    canonicalize (⟨h, T ++ [x]⟩ : Word Nat) =
      canonicalize (⟨h, T⟩ : Word Nat) ++ (⟨x, []⟩ : Word Nat) := by
  rw [append_mk]
  simp only [canonicalize]
  rw [plasmaSeq_snoc_fresh fresh, strippedSingles_snoc_fresh fresh]
  by_cases plasmaCase : plasmaSeq (⟨h, T⟩ : Word Nat) = []
  · rw [plasmaCase]
    have beforesExt : ((strippedSingles (⟨h, T⟩ : Word Nat)) ++
        [x]).filter (fun s =>
          slotOf (⟨h, T ++ [x]⟩ : Word Nat) s == 0) =
        (strippedSingles (⟨h, T⟩ : Word Nat)).filter (fun s =>
          slotOf (⟨h, T⟩ : Word Nat) s == 0) ++ [x] := by
      rw [List.filter_append]
      congr 1
      · apply filter_congr_mem
        intro s sMem
        have sIn : s ∈ h :: T := mem_toList_of_mem_singlesSeq
          (mem_singles_of_mem_stripped sMem)
        rw [slotOf_snoc_fresh fresh sIn]
      · rw [List.filter_cons]
        have slotX : (slotOf (⟨h, T ++ [x]⟩ : Word Nat) x == 0) =
            true := by
          rw [slotOf_snoc_self_fresh fresh, plasmaCase]
          rfl
        rw [slotX]
        simp
    have aftersNilSnoc : ((strippedSingles (⟨h, T⟩ : Word Nat)) ++
        [x]).filter (fun s =>
          slotOf (⟨h, T ++ [x]⟩ : Word Nat) s ==
            ([] : List Nat).length &&
          rel4 (⟨h, T ++ [x]⟩ : Word Nat) s == Rel4.after) = [] := by
      rw [List.filter_eq_nil_iff]
      intro s sMem
      have plasmaNil' : plasmaSeq (⟨h, T ++ [x]⟩ : Word Nat) = [] := by
        rw [plasmaSeq_snoc_fresh fresh, plasmaCase]
      rw [rel4_of_plasma_nil plasmaNil']
      simp
    have aftersNil : (strippedSingles (⟨h, T⟩ : Word Nat)).filter
        (fun s => slotOf (⟨h, T⟩ : Word Nat) s ==
            ([] : List Nat).length &&
          rel4 (⟨h, T⟩ : Word Nat) s == Rel4.after) = [] := by
      rw [List.filter_eq_nil_iff]
      intro s sMem
      rw [rel4_of_plasma_nil plasmaCase]
      simp
    rw [beforesExt, aftersNilSnoc, aftersNil]
    simp
  · have beforesEq : ((strippedSingles (⟨h, T⟩ : Word Nat)) ++
        [x]).filter (fun s =>
          slotOf (⟨h, T ++ [x]⟩ : Word Nat) s == 0) =
        (strippedSingles (⟨h, T⟩ : Word Nat)).filter (fun s =>
          slotOf (⟨h, T⟩ : Word Nat) s == 0) := by
      rw [List.filter_append]
      have xGone : List.filter (fun s =>
          slotOf (⟨h, T ++ [x]⟩ : Word Nat) s == 0) [x] = [] := by
        rw [List.filter_cons]
        have slotX : (slotOf (⟨h, T ++ [x]⟩ : Word Nat) x == 0) =
            false := by
          rw [slotOf_snoc_self_fresh fresh]
          obtain ⟨p0, rest, shape⟩ :=
            List.exists_cons_of_ne_nil plasmaCase
          rw [shape]
          rfl
        rw [slotX]
        simp
      rw [xGone, List.append_nil]
      apply filter_congr_mem
      intro s sMem
      have sIn : s ∈ h :: T := mem_toList_of_mem_singlesSeq
        (mem_singles_of_mem_stripped sMem)
      rw [slotOf_snoc_fresh fresh sIn]
    have blocksEq : (List.range
        (plasmaSeq (⟨h, T⟩ : Word Nat)).length).flatMap
        (fun i => blockOf (⟨h, T ++ [x]⟩ : Word Nat) i
          ((plasmaSeq (⟨h, T⟩ : Word Nat)).getD i 0)) =
        (List.range (plasmaSeq (⟨h, T⟩ : Word Nat)).length).flatMap
        (fun i => blockOf (⟨h, T⟩ : Word Nat) i
          ((plasmaSeq (⟨h, T⟩ : Word Nat)).getD i 0)) := by
      apply flatMap_congr_mem
      intro i _
      rw [blockOf_snoc_fresh fresh plasmaCase]
    have aftersExt : ((strippedSingles (⟨h, T⟩ : Word Nat)) ++
        [x]).filter (fun s =>
          slotOf (⟨h, T ++ [x]⟩ : Word Nat) s ==
            (plasmaSeq (⟨h, T⟩ : Word Nat)).length &&
          rel4 (⟨h, T ++ [x]⟩ : Word Nat) s == Rel4.after) =
        (strippedSingles (⟨h, T⟩ : Word Nat)).filter (fun s =>
          slotOf (⟨h, T⟩ : Word Nat) s ==
            (plasmaSeq (⟨h, T⟩ : Word Nat)).length &&
          rel4 (⟨h, T⟩ : Word Nat) s == Rel4.after) ++ [x] := by
      rw [List.filter_append]
      congr 1
      · apply filter_congr_mem
        intro s sMem
        have sIn : s ∈ h :: T := mem_toList_of_mem_singlesSeq
          (mem_singles_of_mem_stripped sMem)
        rw [slotOf_snoc_fresh fresh sIn, rel4_snoc_fresh fresh sIn]
      · rw [List.filter_cons]
        have slotX : (slotOf (⟨h, T ++ [x]⟩ : Word Nat) x ==
            (plasmaSeq (⟨h, T⟩ : Word Nat)).length) = true := by
          rw [slotOf_snoc_self_fresh fresh]
          simp
        have relX : (rel4 (⟨h, T ++ [x]⟩ : Word Nat) x ==
            Rel4.after) = true := by
          rw [rel4_snoc_self_fresh fresh plasmaCase]
          rfl
        rw [slotX, relX]
        simp
    rw [beforesEq, blocksEq, aftersExt]
    simp


/-! ## Case-2 macros: pull the trailing close left (generated from validated BFS paths) -/

private theorem macroCrossFull (H X E P Y Z : Word Nat) :
    Derives basis (H ++ (X ++ (E ++ (P ++ (Y ++ (P ++ (Z ++ X)))))))
      (H ++ (X ++ (E ++ (X ++ (P ++ (Y ++ (Z ++ P))))))) := by
  have step0 : Derives basis (H ++ (X ++ (E ++ (P ++ (Y ++ (P ++ (Z ++ X)))))))
      (H ++ (X ++ (E ++ (P ++ (P ++ (Y ++ (P ++ (Z ++ X)))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend (H ++ (X ++ E)) (derivesLeftDuplication P Y)) (Z ++ X))
  have step1 : Derives basis (H ++ (X ++ (E ++ (P ++ (P ++ (Y ++ (P ++ (Z ++ X))))))))
      (H ++ (X ++ (E ++ (X ++ (P ++ (P ++ (Y ++ (P ++ (Z ++ X))))))))) := by
    simpa [Word.append_assoc] using (Derives.prepend H (derivesMiddleReduplication X E (P ++ (P ++ (Y ++ (P ++ Z))))))
  have step2 : Derives basis (H ++ (X ++ (E ++ (X ++ (P ++ (P ++ (Y ++ (P ++ (Z ++ X)))))))))
      (H ++ (X ++ (E ++ (X ++ (X ++ (P ++ (Y ++ (P ++ (Z ++ P))))))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (H ++ (X ++ E)) (Derives.symm (derivesCrossShuffle X P (Y ++ (P ++ Z)))))
  have step3 : Derives basis (H ++ (X ++ (E ++ (X ++ (X ++ (P ++ (Y ++ (P ++ (Z ++ P)))))))))
      (H ++ (X ++ (E ++ (X ++ (P ++ (Y ++ (P ++ (Z ++ P)))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend H (Derives.symm (derivesRightDuplication X E))) (P ++ (Y ++ (P ++ (Z ++ P)))))
  have step4 : Derives basis (H ++ (X ++ (E ++ (X ++ (P ++ (Y ++ (P ++ (Z ++ P))))))))
      (H ++ (X ++ (E ++ (X ++ (P ++ (Y ++ (Z ++ P))))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (H ++ (X ++ (E ++ X))) (Derives.symm (derivesMiddleReduplication P Y Z)))
  exact Derives.trans (Derives.trans (Derives.trans (Derives.trans (step0) step1) step2) step3) step4

private theorem macroCrossE (H X P Y Z : Word Nat) :
    Derives basis (H ++ (X ++ (P ++ (Y ++ (P ++ (Z ++ X))))))
      (H ++ (X ++ (X ++ (P ++ (Y ++ (Z ++ P)))))) := by
  have step0 : Derives basis (H ++ (X ++ (P ++ (Y ++ (P ++ (Z ++ X))))))
      (H ++ (X ++ (P ++ (P ++ (Y ++ (P ++ (Z ++ X))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend (H ++ X) (derivesLeftDuplication P Y)) (Z ++ X))
  have step1 : Derives basis (H ++ (X ++ (P ++ (P ++ (Y ++ (P ++ (Z ++ X)))))))
      (H ++ (X ++ (X ++ (P ++ (Y ++ (P ++ (Z ++ P))))))) := by
    simpa [Word.append_assoc] using (Derives.prepend H (Derives.symm (derivesCrossShuffle X P (Y ++ (P ++ Z)))))
  have step2 : Derives basis (H ++ (X ++ (X ++ (P ++ (Y ++ (P ++ (Z ++ P)))))))
      (H ++ (X ++ (X ++ (P ++ (Y ++ (Z ++ P)))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (H ++ (X ++ X)) (Derives.symm (derivesMiddleReduplication P Y Z)))
  exact Derives.trans (Derives.trans (step0) step1) step2

private theorem macroCrossY (H X E P Z : Word Nat) :
    Derives basis (H ++ (X ++ (E ++ (P ++ (P ++ (Z ++ X))))))
      (H ++ (X ++ (E ++ (X ++ (P ++ (Z ++ P)))))) := by
  have step0 : Derives basis (H ++ (X ++ (E ++ (P ++ (P ++ (Z ++ X))))))
      (H ++ (X ++ (E ++ (X ++ (P ++ (P ++ (Z ++ X))))))) := by
    simpa [Word.append_assoc] using (Derives.prepend H (derivesMiddleReduplication X E (P ++ (P ++ Z))))
  have step1 : Derives basis (H ++ (X ++ (E ++ (X ++ (P ++ (P ++ (Z ++ X)))))))
      (H ++ (X ++ (E ++ (X ++ (X ++ (P ++ (Z ++ P))))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (H ++ (X ++ E)) (Derives.symm (derivesCrossShuffle X P Z)))
  have step2 : Derives basis (H ++ (X ++ (E ++ (X ++ (X ++ (P ++ (Z ++ P)))))))
      (H ++ (X ++ (E ++ (X ++ (P ++ (Z ++ P)))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend H (Derives.symm (derivesRightDuplication X E))) (P ++ (Z ++ P)))
  exact Derives.trans (Derives.trans (step0) step1) step2

private theorem macroCrossZ (H X E P Y : Word Nat) :
    Derives basis (H ++ (X ++ (E ++ (P ++ (Y ++ (P ++ X))))))
      (H ++ (X ++ (E ++ (X ++ (P ++ (Y ++ P)))))) := by
  have step0 : Derives basis (H ++ (X ++ (E ++ (P ++ (Y ++ (P ++ X))))))
      (H ++ (X ++ (E ++ (P ++ (P ++ (Y ++ (P ++ X))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend (H ++ (X ++ E)) (derivesLeftDuplication P Y)) X)
  have step1 : Derives basis (H ++ (X ++ (E ++ (P ++ (P ++ (Y ++ (P ++ X)))))))
      (H ++ (X ++ (E ++ (X ++ (P ++ (P ++ (Y ++ (P ++ X)))))))) := by
    simpa [Word.append_assoc] using (Derives.prepend H (derivesMiddleReduplication X E (P ++ (P ++ (Y ++ P)))))
  have step2 : Derives basis (H ++ (X ++ (E ++ (X ++ (P ++ (P ++ (Y ++ (P ++ X))))))))
      (H ++ (X ++ (E ++ (X ++ (X ++ (P ++ (Y ++ (P ++ P)))))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (H ++ (X ++ E)) (Derives.symm (derivesCrossShuffle X P (Y ++ P))))
  have step3 : Derives basis (H ++ (X ++ (E ++ (X ++ (X ++ (P ++ (Y ++ (P ++ P))))))))
      (H ++ (X ++ (E ++ (X ++ (P ++ (Y ++ (P ++ P))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend H (Derives.symm (derivesRightDuplication X E))) (P ++ (Y ++ (P ++ P))))
  have step4 : Derives basis (H ++ (X ++ (E ++ (X ++ (P ++ (Y ++ (P ++ P)))))))
      (H ++ (X ++ (E ++ (X ++ (P ++ (Y ++ P)))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (H ++ (X ++ (E ++ X))) (Derives.symm (derivesRightDuplication P Y)))
  exact Derives.trans (Derives.trans (Derives.trans (Derives.trans (step0) step1) step2) step3) step4

private theorem macroCrossEY (H X P Z : Word Nat) :
    Derives basis (H ++ (X ++ (P ++ (P ++ (Z ++ X)))))
      (H ++ (X ++ (X ++ (P ++ (Z ++ P))))) := by
  have step0 : Derives basis (H ++ (X ++ (P ++ (P ++ (Z ++ X)))))
      (H ++ (X ++ (X ++ (P ++ (Z ++ P))))) := by
    simpa [Word.append_assoc] using (Derives.prepend H (Derives.symm (derivesCrossShuffle X P Z)))
  exact step0

private theorem macroCrossEZ (H X P Y : Word Nat) :
    Derives basis (H ++ (X ++ (P ++ (Y ++ (P ++ X)))))
      (H ++ (X ++ (X ++ (P ++ (Y ++ P))))) := by
  have step0 : Derives basis (H ++ (X ++ (P ++ (Y ++ (P ++ X)))))
      (H ++ (X ++ (P ++ (P ++ (Y ++ (P ++ X)))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend (H ++ X) (derivesLeftDuplication P Y)) X)
  have step1 : Derives basis (H ++ (X ++ (P ++ (P ++ (Y ++ (P ++ X))))))
      (H ++ (X ++ (X ++ (P ++ (Y ++ (P ++ P)))))) := by
    simpa [Word.append_assoc] using (Derives.prepend H (Derives.symm (derivesCrossShuffle X P (Y ++ P))))
  have step2 : Derives basis (H ++ (X ++ (X ++ (P ++ (Y ++ (P ++ P))))))
      (H ++ (X ++ (X ++ (P ++ (Y ++ P))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (H ++ (X ++ X)) (Derives.symm (derivesRightDuplication P Y)))
  exact Derives.trans (Derives.trans (step0) step1) step2

private theorem macroCrossYZ (H X E P : Word Nat) :
    Derives basis (H ++ (X ++ (E ++ (P ++ (P ++ X)))))
      (H ++ (X ++ (E ++ (X ++ (P ++ P))))) := by
  have step0 : Derives basis (H ++ (X ++ (E ++ (P ++ (P ++ X)))))
      (H ++ (X ++ (E ++ (X ++ (P ++ (P ++ X)))))) := by
    simpa [Word.append_assoc] using (Derives.prepend H (derivesMiddleReduplication X E (P ++ P)))
  have step1 : Derives basis (H ++ (X ++ (E ++ (X ++ (P ++ (P ++ X))))))
      (H ++ (X ++ (E ++ (X ++ (X ++ (P ++ P)))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (H ++ (X ++ E)) (Derives.symm (derivesSquareFinalSwitch X P)))
  have step2 : Derives basis (H ++ (X ++ (E ++ (X ++ (X ++ (P ++ P))))))
      (H ++ (X ++ (E ++ (X ++ (P ++ P))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend H (Derives.symm (derivesRightDuplication X E))) (P ++ P))
  exact Derives.trans (Derives.trans (step0) step1) step2

private theorem macroCrossEYZ (H X P : Word Nat) :
    Derives basis (H ++ (X ++ (P ++ (P ++ X))))
      (H ++ (X ++ (X ++ (P ++ P)))) := by
  have step0 : Derives basis (H ++ (X ++ (P ++ (P ++ X))))
      (H ++ (X ++ (X ++ (P ++ P)))) := by
    simpa [Word.append_assoc] using (Derives.prepend H (Derives.symm (derivesSquareFinalSwitch X P)))
  exact step0

private theorem macroSplitFull (H E Q A X B G : Word Nat) :
    Derives basis (H ++ (E ++ (Q ++ (A ++ (X ++ (B ++ (Q ++ (G ++ X))))))))
      (H ++ (E ++ (Q ++ (A ++ (Q ++ (X ++ (B ++ (G ++ X)))))))) := by
  have step0 : Derives basis (H ++ (E ++ (Q ++ (A ++ (X ++ (B ++ (Q ++ (G ++ X))))))))
      (H ++ (E ++ (Q ++ (A ++ (X ++ (X ++ (B ++ (Q ++ (G ++ X))))))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (H ++ (E ++ (Q ++ A))) (derivesLeftDuplication X (B ++ (Q ++ G))))
  have step1 : Derives basis (H ++ (E ++ (Q ++ (A ++ (X ++ (X ++ (B ++ (Q ++ (G ++ X)))))))))
      (H ++ (E ++ (Q ++ (A ++ (Q ++ (X ++ (X ++ (B ++ (Q ++ (G ++ X)))))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend (H ++ E) (derivesMiddleReduplication Q A (X ++ (X ++ B)))) (G ++ X))
  have step2 : Derives basis (H ++ (E ++ (Q ++ (A ++ (Q ++ (X ++ (X ++ (B ++ (Q ++ (G ++ X))))))))))
      (H ++ (E ++ (Q ++ (A ++ (Q ++ (Q ++ (X ++ (B ++ (X ++ (G ++ X)))))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend (H ++ (E ++ (Q ++ A))) (Derives.symm (derivesCrossShuffle Q X B))) (G ++ X))
  have step3 : Derives basis (H ++ (E ++ (Q ++ (A ++ (Q ++ (Q ++ (X ++ (B ++ (X ++ (G ++ X))))))))))
      (H ++ (E ++ (Q ++ (A ++ (Q ++ (X ++ (B ++ (X ++ (G ++ X))))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend (H ++ E) (Derives.symm (derivesRightDuplication Q A))) (X ++ (B ++ (X ++ (G ++ X)))))
  have step4 : Derives basis (H ++ (E ++ (Q ++ (A ++ (Q ++ (X ++ (B ++ (X ++ (G ++ X)))))))))
      (H ++ (E ++ (Q ++ (A ++ (Q ++ (X ++ (B ++ (G ++ X)))))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (H ++ (E ++ (Q ++ (A ++ Q)))) (Derives.symm (derivesMiddleReduplication X B G)))
  exact Derives.trans (Derives.trans (Derives.trans (Derives.trans (step0) step1) step2) step3) step4

private theorem macroSplitE (H Q A X B G : Word Nat) :
    Derives basis (H ++ (Q ++ (A ++ (X ++ (B ++ (Q ++ (G ++ X)))))))
      (H ++ (Q ++ (A ++ (Q ++ (X ++ (B ++ (G ++ X))))))) := by
  have step0 : Derives basis (H ++ (Q ++ (A ++ (X ++ (B ++ (Q ++ (G ++ X)))))))
      (H ++ (Q ++ (A ++ (X ++ (X ++ (B ++ (Q ++ (G ++ X)))))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (H ++ (Q ++ A)) (derivesLeftDuplication X (B ++ (Q ++ G))))
  have step1 : Derives basis (H ++ (Q ++ (A ++ (X ++ (X ++ (B ++ (Q ++ (G ++ X))))))))
      (H ++ (Q ++ (A ++ (Q ++ (X ++ (X ++ (B ++ (Q ++ (G ++ X))))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend H (derivesMiddleReduplication Q A (X ++ (X ++ B)))) (G ++ X))
  have step2 : Derives basis (H ++ (Q ++ (A ++ (Q ++ (X ++ (X ++ (B ++ (Q ++ (G ++ X)))))))))
      (H ++ (Q ++ (A ++ (Q ++ (Q ++ (X ++ (B ++ (X ++ (G ++ X))))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend (H ++ (Q ++ A)) (Derives.symm (derivesCrossShuffle Q X B))) (G ++ X))
  have step3 : Derives basis (H ++ (Q ++ (A ++ (Q ++ (Q ++ (X ++ (B ++ (X ++ (G ++ X)))))))))
      (H ++ (Q ++ (A ++ (Q ++ (X ++ (B ++ (X ++ (G ++ X)))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend H (Derives.symm (derivesRightDuplication Q A))) (X ++ (B ++ (X ++ (G ++ X)))))
  have step4 : Derives basis (H ++ (Q ++ (A ++ (Q ++ (X ++ (B ++ (X ++ (G ++ X))))))))
      (H ++ (Q ++ (A ++ (Q ++ (X ++ (B ++ (G ++ X))))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (H ++ (Q ++ (A ++ Q))) (Derives.symm (derivesMiddleReduplication X B G)))
  exact Derives.trans (Derives.trans (Derives.trans (Derives.trans (step0) step1) step2) step3) step4

private theorem macroSplitA (H E Q X B G : Word Nat) :
    Derives basis (H ++ (E ++ (Q ++ (X ++ (B ++ (Q ++ (G ++ X)))))))
      (H ++ (E ++ (Q ++ (Q ++ (X ++ (B ++ (G ++ X))))))) := by
  have step0 : Derives basis (H ++ (E ++ (Q ++ (X ++ (B ++ (Q ++ (G ++ X)))))))
      (H ++ (E ++ (Q ++ (X ++ (X ++ (B ++ (Q ++ (G ++ X)))))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (H ++ (E ++ Q)) (derivesLeftDuplication X (B ++ (Q ++ G))))
  have step1 : Derives basis (H ++ (E ++ (Q ++ (X ++ (X ++ (B ++ (Q ++ (G ++ X))))))))
      (H ++ (E ++ (Q ++ (Q ++ (X ++ (B ++ (X ++ (G ++ X)))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend (H ++ E) (Derives.symm (derivesCrossShuffle Q X B))) (G ++ X))
  have step2 : Derives basis (H ++ (E ++ (Q ++ (Q ++ (X ++ (B ++ (X ++ (G ++ X))))))))
      (H ++ (E ++ (Q ++ (Q ++ (X ++ (B ++ (G ++ X))))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (H ++ (E ++ (Q ++ Q))) (Derives.symm (derivesMiddleReduplication X B G)))
  exact Derives.trans (Derives.trans (step0) step1) step2

private theorem macroSplitB (H E Q A X G : Word Nat) :
    Derives basis (H ++ (E ++ (Q ++ (A ++ (X ++ (Q ++ (G ++ X)))))))
      (H ++ (E ++ (Q ++ (A ++ (Q ++ (X ++ (G ++ X))))))) := by
  have step0 : Derives basis (H ++ (E ++ (Q ++ (A ++ (X ++ (Q ++ (G ++ X)))))))
      (H ++ (E ++ (Q ++ (A ++ (X ++ (X ++ (Q ++ (G ++ X)))))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (H ++ (E ++ (Q ++ A))) (derivesLeftDuplication X (Q ++ G)))
  have step1 : Derives basis (H ++ (E ++ (Q ++ (A ++ (X ++ (X ++ (Q ++ (G ++ X))))))))
      (H ++ (E ++ (Q ++ (A ++ (Q ++ (X ++ (X ++ (Q ++ (G ++ X))))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend (H ++ E) (derivesMiddleReduplication Q A (X ++ X))) (G ++ X))
  have step2 : Derives basis (H ++ (E ++ (Q ++ (A ++ (Q ++ (X ++ (X ++ (Q ++ (G ++ X)))))))))
      (H ++ (E ++ (Q ++ (A ++ (Q ++ (Q ++ (X ++ (X ++ (G ++ X))))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend (H ++ (E ++ (Q ++ A))) (Derives.symm (derivesSquareFinalSwitch Q X))) (G ++ X))
  have step3 : Derives basis (H ++ (E ++ (Q ++ (A ++ (Q ++ (Q ++ (X ++ (X ++ (G ++ X)))))))))
      (H ++ (E ++ (Q ++ (A ++ (Q ++ (Q ++ (X ++ (G ++ X)))))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (H ++ (E ++ (Q ++ (A ++ (Q ++ Q))))) (Derives.symm (derivesLeftDuplication X G)))
  have step4 : Derives basis (H ++ (E ++ (Q ++ (A ++ (Q ++ (Q ++ (X ++ (G ++ X))))))))
      (H ++ (E ++ (Q ++ (A ++ (Q ++ (X ++ (G ++ X))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend (H ++ E) (Derives.symm (derivesRightDuplication Q A))) (X ++ (G ++ X)))
  exact Derives.trans (Derives.trans (Derives.trans (Derives.trans (step0) step1) step2) step3) step4

private theorem macroSplitG (H E Q A X B : Word Nat) :
    Derives basis (H ++ (E ++ (Q ++ (A ++ (X ++ (B ++ (Q ++ X)))))))
      (H ++ (E ++ (Q ++ (A ++ (Q ++ (X ++ (B ++ X))))))) := by
  have step0 : Derives basis (H ++ (E ++ (Q ++ (A ++ (X ++ (B ++ (Q ++ X)))))))
      (H ++ (E ++ (Q ++ (A ++ (X ++ (X ++ (B ++ (Q ++ X)))))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (H ++ (E ++ (Q ++ A))) (derivesLeftDuplication X (B ++ Q)))
  have step1 : Derives basis (H ++ (E ++ (Q ++ (A ++ (X ++ (X ++ (B ++ (Q ++ X))))))))
      (H ++ (E ++ (Q ++ (A ++ (Q ++ (X ++ (X ++ (B ++ (Q ++ X))))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend (H ++ E) (derivesMiddleReduplication Q A (X ++ (X ++ B)))) X)
  have step2 : Derives basis (H ++ (E ++ (Q ++ (A ++ (Q ++ (X ++ (X ++ (B ++ (Q ++ X)))))))))
      (H ++ (E ++ (Q ++ (A ++ (Q ++ (Q ++ (X ++ (B ++ (X ++ X))))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend (H ++ (E ++ (Q ++ A))) (Derives.symm (derivesCrossShuffle Q X B))) X)
  have step3 : Derives basis (H ++ (E ++ (Q ++ (A ++ (Q ++ (Q ++ (X ++ (B ++ (X ++ X)))))))))
      (H ++ (E ++ (Q ++ (A ++ (Q ++ (X ++ (B ++ (X ++ X)))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend (H ++ E) (Derives.symm (derivesRightDuplication Q A))) (X ++ (B ++ (X ++ X))))
  have step4 : Derives basis (H ++ (E ++ (Q ++ (A ++ (Q ++ (X ++ (B ++ (X ++ X))))))))
      (H ++ (E ++ (Q ++ (A ++ (Q ++ (X ++ (B ++ X))))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (H ++ (E ++ (Q ++ (A ++ Q)))) (Derives.symm (derivesRightDuplication X B)))
  exact Derives.trans (Derives.trans (Derives.trans (Derives.trans (step0) step1) step2) step3) step4

private theorem macroSplitEA (H Q X B G : Word Nat) :
    Derives basis (H ++ (Q ++ (X ++ (B ++ (Q ++ (G ++ X))))))
      (H ++ (Q ++ (Q ++ (X ++ (B ++ (G ++ X)))))) := by
  have step0 : Derives basis (H ++ (Q ++ (X ++ (B ++ (Q ++ (G ++ X))))))
      (H ++ (Q ++ (X ++ (X ++ (B ++ (Q ++ (G ++ X))))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (H ++ Q) (derivesLeftDuplication X (B ++ (Q ++ G))))
  have step1 : Derives basis (H ++ (Q ++ (X ++ (X ++ (B ++ (Q ++ (G ++ X)))))))
      (H ++ (Q ++ (Q ++ (X ++ (B ++ (X ++ (G ++ X))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend H (Derives.symm (derivesCrossShuffle Q X B))) (G ++ X))
  have step2 : Derives basis (H ++ (Q ++ (Q ++ (X ++ (B ++ (X ++ (G ++ X)))))))
      (H ++ (Q ++ (Q ++ (X ++ (B ++ (G ++ X)))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (H ++ (Q ++ Q)) (Derives.symm (derivesMiddleReduplication X B G)))
  exact Derives.trans (Derives.trans (step0) step1) step2

private theorem macroSplitEB (H Q A X G : Word Nat) :
    Derives basis (H ++ (Q ++ (A ++ (X ++ (Q ++ (G ++ X))))))
      (H ++ (Q ++ (A ++ (Q ++ (X ++ (G ++ X)))))) := by
  have step0 : Derives basis (H ++ (Q ++ (A ++ (X ++ (Q ++ (G ++ X))))))
      (H ++ (Q ++ (A ++ (X ++ (X ++ (Q ++ (G ++ X))))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (H ++ (Q ++ A)) (derivesLeftDuplication X (Q ++ G)))
  have step1 : Derives basis (H ++ (Q ++ (A ++ (X ++ (X ++ (Q ++ (G ++ X)))))))
      (H ++ (Q ++ (A ++ (Q ++ (X ++ (X ++ (Q ++ (G ++ X)))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend H (derivesMiddleReduplication Q A (X ++ X))) (G ++ X))
  have step2 : Derives basis (H ++ (Q ++ (A ++ (Q ++ (X ++ (X ++ (Q ++ (G ++ X))))))))
      (H ++ (Q ++ (A ++ (Q ++ (Q ++ (X ++ (X ++ (G ++ X)))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend (H ++ (Q ++ A)) (Derives.symm (derivesSquareFinalSwitch Q X))) (G ++ X))
  have step3 : Derives basis (H ++ (Q ++ (A ++ (Q ++ (Q ++ (X ++ (X ++ (G ++ X))))))))
      (H ++ (Q ++ (A ++ (Q ++ (Q ++ (X ++ (G ++ X))))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (H ++ (Q ++ (A ++ (Q ++ Q)))) (Derives.symm (derivesLeftDuplication X G)))
  have step4 : Derives basis (H ++ (Q ++ (A ++ (Q ++ (Q ++ (X ++ (G ++ X)))))))
      (H ++ (Q ++ (A ++ (Q ++ (X ++ (G ++ X)))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend H (Derives.symm (derivesRightDuplication Q A))) (X ++ (G ++ X)))
  exact Derives.trans (Derives.trans (Derives.trans (Derives.trans (step0) step1) step2) step3) step4

private theorem macroSplitEG (H Q A X B : Word Nat) :
    Derives basis (H ++ (Q ++ (A ++ (X ++ (B ++ (Q ++ X))))))
      (H ++ (Q ++ (A ++ (Q ++ (X ++ (B ++ X)))))) := by
  have step0 : Derives basis (H ++ (Q ++ (A ++ (X ++ (B ++ (Q ++ X))))))
      (H ++ (Q ++ (A ++ (X ++ (X ++ (B ++ (Q ++ X))))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (H ++ (Q ++ A)) (derivesLeftDuplication X (B ++ Q)))
  have step1 : Derives basis (H ++ (Q ++ (A ++ (X ++ (X ++ (B ++ (Q ++ X)))))))
      (H ++ (Q ++ (A ++ (Q ++ (X ++ (X ++ (B ++ (Q ++ X)))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend H (derivesMiddleReduplication Q A (X ++ (X ++ B)))) X)
  have step2 : Derives basis (H ++ (Q ++ (A ++ (Q ++ (X ++ (X ++ (B ++ (Q ++ X))))))))
      (H ++ (Q ++ (A ++ (Q ++ (Q ++ (X ++ (B ++ (X ++ X)))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend (H ++ (Q ++ A)) (Derives.symm (derivesCrossShuffle Q X B))) X)
  have step3 : Derives basis (H ++ (Q ++ (A ++ (Q ++ (Q ++ (X ++ (B ++ (X ++ X))))))))
      (H ++ (Q ++ (A ++ (Q ++ (X ++ (B ++ (X ++ X))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend H (Derives.symm (derivesRightDuplication Q A))) (X ++ (B ++ (X ++ X))))
  have step4 : Derives basis (H ++ (Q ++ (A ++ (Q ++ (X ++ (B ++ (X ++ X)))))))
      (H ++ (Q ++ (A ++ (Q ++ (X ++ (B ++ X)))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (H ++ (Q ++ (A ++ Q))) (Derives.symm (derivesRightDuplication X B)))
  exact Derives.trans (Derives.trans (Derives.trans (Derives.trans (step0) step1) step2) step3) step4

private theorem macroSplitAB (H E Q X G : Word Nat) :
    Derives basis (H ++ (E ++ (Q ++ (X ++ (Q ++ (G ++ X))))))
      (H ++ (E ++ (Q ++ (Q ++ (X ++ (G ++ X)))))) := by
  have step0 : Derives basis (H ++ (E ++ (Q ++ (X ++ (Q ++ (G ++ X))))))
      (H ++ (E ++ (Q ++ (X ++ (X ++ (Q ++ (G ++ X))))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (H ++ (E ++ Q)) (derivesLeftDuplication X (Q ++ G)))
  have step1 : Derives basis (H ++ (E ++ (Q ++ (X ++ (X ++ (Q ++ (G ++ X)))))))
      (H ++ (E ++ (Q ++ (Q ++ (X ++ (X ++ (G ++ X))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend (H ++ E) (Derives.symm (derivesSquareFinalSwitch Q X))) (G ++ X))
  have step2 : Derives basis (H ++ (E ++ (Q ++ (Q ++ (X ++ (X ++ (G ++ X)))))))
      (H ++ (E ++ (Q ++ (Q ++ (X ++ (G ++ X)))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (H ++ (E ++ (Q ++ Q))) (Derives.symm (derivesLeftDuplication X G)))
  exact Derives.trans (Derives.trans (step0) step1) step2

private theorem macroSplitAG (H E Q X B : Word Nat) :
    Derives basis (H ++ (E ++ (Q ++ (X ++ (B ++ (Q ++ X))))))
      (H ++ (E ++ (Q ++ (Q ++ (X ++ (B ++ X)))))) := by
  have step0 : Derives basis (H ++ (E ++ (Q ++ (X ++ (B ++ (Q ++ X))))))
      (H ++ (E ++ (Q ++ (X ++ (X ++ (B ++ (Q ++ X))))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (H ++ (E ++ Q)) (derivesLeftDuplication X (B ++ Q)))
  have step1 : Derives basis (H ++ (E ++ (Q ++ (X ++ (X ++ (B ++ (Q ++ X)))))))
      (H ++ (E ++ (Q ++ (Q ++ (X ++ (B ++ (X ++ X))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend (H ++ E) (Derives.symm (derivesCrossShuffle Q X B))) X)
  have step2 : Derives basis (H ++ (E ++ (Q ++ (Q ++ (X ++ (B ++ (X ++ X)))))))
      (H ++ (E ++ (Q ++ (Q ++ (X ++ (B ++ X)))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (H ++ (E ++ (Q ++ Q))) (Derives.symm (derivesRightDuplication X B)))
  exact Derives.trans (Derives.trans (step0) step1) step2

private theorem macroSplitBG (H E Q A X : Word Nat) :
    Derives basis (H ++ (E ++ (Q ++ (A ++ (X ++ (Q ++ X))))))
      (H ++ (E ++ (Q ++ (A ++ (Q ++ (X ++ X)))))) := by
  have step0 : Derives basis (H ++ (E ++ (Q ++ (A ++ (X ++ (Q ++ X))))))
      (H ++ (E ++ (Q ++ (A ++ (Q ++ (X ++ (Q ++ X))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend (H ++ E) (derivesMiddleReduplication Q A X)) X)
  have step1 : Derives basis (H ++ (E ++ (Q ++ (A ++ (Q ++ (X ++ (Q ++ X)))))))
      (H ++ (E ++ (Q ++ (A ++ (Q ++ (Q ++ (X ++ X))))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (H ++ (E ++ (Q ++ A))) (Derives.symm (derivesSquareInterleave Q X)))
  have step2 : Derives basis (H ++ (E ++ (Q ++ (A ++ (Q ++ (Q ++ (X ++ X)))))))
      (H ++ (E ++ (Q ++ (A ++ (Q ++ (X ++ X)))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend (H ++ E) (Derives.symm (derivesRightDuplication Q A))) (X ++ X))
  exact Derives.trans (Derives.trans (step0) step1) step2

private theorem macroSplitEAB (H Q X G : Word Nat) :
    Derives basis (H ++ (Q ++ (X ++ (Q ++ (G ++ X)))))
      (H ++ (Q ++ (Q ++ (X ++ (G ++ X))))) := by
  have step0 : Derives basis (H ++ (Q ++ (X ++ (Q ++ (G ++ X)))))
      (H ++ (Q ++ (X ++ (X ++ (Q ++ (G ++ X)))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (H ++ Q) (derivesLeftDuplication X (Q ++ G)))
  have step1 : Derives basis (H ++ (Q ++ (X ++ (X ++ (Q ++ (G ++ X))))))
      (H ++ (Q ++ (Q ++ (X ++ (X ++ (G ++ X)))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend H (Derives.symm (derivesSquareFinalSwitch Q X))) (G ++ X))
  have step2 : Derives basis (H ++ (Q ++ (Q ++ (X ++ (X ++ (G ++ X))))))
      (H ++ (Q ++ (Q ++ (X ++ (G ++ X))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (H ++ (Q ++ Q)) (Derives.symm (derivesLeftDuplication X G)))
  exact Derives.trans (Derives.trans (step0) step1) step2

private theorem macroSplitEAG (H Q X B : Word Nat) :
    Derives basis (H ++ (Q ++ (X ++ (B ++ (Q ++ X)))))
      (H ++ (Q ++ (Q ++ (X ++ (B ++ X))))) := by
  have step0 : Derives basis (H ++ (Q ++ (X ++ (B ++ (Q ++ X)))))
      (H ++ (Q ++ (X ++ (X ++ (B ++ (Q ++ X)))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (H ++ Q) (derivesLeftDuplication X (B ++ Q)))
  have step1 : Derives basis (H ++ (Q ++ (X ++ (X ++ (B ++ (Q ++ X))))))
      (H ++ (Q ++ (Q ++ (X ++ (B ++ (X ++ X)))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend H (Derives.symm (derivesCrossShuffle Q X B))) X)
  have step2 : Derives basis (H ++ (Q ++ (Q ++ (X ++ (B ++ (X ++ X))))))
      (H ++ (Q ++ (Q ++ (X ++ (B ++ X))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (H ++ (Q ++ Q)) (Derives.symm (derivesRightDuplication X B)))
  exact Derives.trans (Derives.trans (step0) step1) step2

private theorem macroSplitEBG (H Q A X : Word Nat) :
    Derives basis (H ++ (Q ++ (A ++ (X ++ (Q ++ X)))))
      (H ++ (Q ++ (A ++ (Q ++ (X ++ X))))) := by
  have step0 : Derives basis (H ++ (Q ++ (A ++ (X ++ (Q ++ X)))))
      (H ++ (Q ++ (A ++ (Q ++ (X ++ (Q ++ X)))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend H (derivesMiddleReduplication Q A X)) X)
  have step1 : Derives basis (H ++ (Q ++ (A ++ (Q ++ (X ++ (Q ++ X))))))
      (H ++ (Q ++ (A ++ (Q ++ (Q ++ (X ++ X)))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (H ++ (Q ++ A)) (Derives.symm (derivesSquareInterleave Q X)))
  have step2 : Derives basis (H ++ (Q ++ (A ++ (Q ++ (Q ++ (X ++ X))))))
      (H ++ (Q ++ (A ++ (Q ++ (X ++ X))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend H (Derives.symm (derivesRightDuplication Q A))) (X ++ X))
  exact Derives.trans (Derives.trans (step0) step1) step2

private theorem macroSplitABG (H E Q X : Word Nat) :
    Derives basis (H ++ (E ++ (Q ++ (X ++ (Q ++ X)))))
      (H ++ (E ++ (Q ++ (Q ++ (X ++ X))))) := by
  have step0 : Derives basis (H ++ (E ++ (Q ++ (X ++ (Q ++ X)))))
      (H ++ (E ++ (Q ++ (Q ++ (X ++ X))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (H ++ E) (Derives.symm (derivesSquareInterleave Q X)))
  exact step0

private theorem macroSplitEABG (H Q X : Word Nat) :
    Derives basis (H ++ (Q ++ (X ++ (Q ++ X))))
      (H ++ (Q ++ (Q ++ (X ++ X)))) := by
  have step0 : Derives basis (H ++ (Q ++ (X ++ (Q ++ X))))
      (H ++ (Q ++ (Q ++ (X ++ X)))) := by
    simpa [Word.append_assoc] using (Derives.prepend H (Derives.symm (derivesSquareInterleave Q X)))
  exact step0

/-! ## Second-occurrence snoc: count coordinates -/

/-- Appending a letter already present is invisible to eraseDups. -/
private theorem eraseDups_snoc_mem {L : List Nat} {x : Nat}
    (member : x ∈ L) :
    (L ++ [x]).eraseDups = L.eraseDups := by
  have := eraseDups_splice_mem (P := L) (B := []) (c := x) member
  simpa using this

/-- Appending a second occurrence removes the letter from the singles
sequence and keeps every other single. -/
private theorem singlesSeq_snoc_second {h x : Nat} {T : List Nat}
    (single : List.count x ((h :: T)) = 1) :
    singlesSeq (⟨h, T ++ [x]⟩ : Word Nat) =
      (singlesSeq (⟨h, T⟩ : Word Nat)).filter (fun s => !(s == x)) := by
  have core : ∀ (L : List Nat), List.count x L = 1 →
      (L ++ [x]).filter (fun c => (L ++ [x]).count c == 1) =
      (L.filter (fun c => L.count c == 1)).filter
        (fun s => !(s == x)) := by
    intro L singleL
    rw [List.filter_filter]
    rw [List.filter_append]
    have rightNil : List.filter
        (fun c => (L ++ [x]).count c == 1) [x] = [] := by
      rw [List.filter_cons]
      have countX : (L ++ [x]).count x = 2 := by
        rw [count_append_self, singleL]
      rw [countX]
      simp
    rw [rightNil, List.append_nil]
    apply filter_congr_mem
    intro e eMem
    by_cases hit : e = x
    · have countE : (L ++ [x]).count e = 2 := by
        rw [hit, count_append_self, singleL]
      rw [countE, hit]
      simp
    · rw [count_append_ne hit]
      have neBeq : (!(e == x)) = true := by
        simp [hit]
      rw [neBeq, Bool.true_and]
  exact core (h :: T) single

/-! ## eraseDups structure: first-occurrence order and sortedness -/

/-- Reference implementation: head, then recursive result minus head. -/
private def firstOccs : List Nat → List Nat
  | [] => []
  | a :: rest => a :: (firstOccs rest).filter (fun b => !(b == a))

private theorem eraseDups_loop_eq (l : List Nat) : ∀ (seen : List Nat),
    List.eraseDupsBy.loop (fun a b => a == b) l seen =
      seen.reverse ++ (firstOccs l).filter
        (fun b => !(seen.any (fun c => b == c))) := by
  induction l with
  | nil =>
      intro seen
      rw [List.eraseDupsBy.loop]
      simp [firstOccs]
  | cons a rest ih =>
      intro seen
      rw [List.eraseDupsBy.loop]
      by_cases anyHit : seen.any (fun b => a == b) = true
      · rw [anyHit]
        simp only [if_true]
        rw [ih seen]
        have aInSeen : a ∈ seen := by
          rw [List.any_eq_true] at anyHit
          obtain ⟨c, cMem, beq⟩ := anyHit
          have : a = c := by simpa using beq
          exact this ▸ cMem
        have aPred : (!(seen.any (fun c => a == c))) = false := by
          rw [anyHit]
          rfl
        rw [firstOccs, List.filter_cons, aPred]
        simp only [Bool.false_eq_true, if_false]
        rw [List.filter_filter]
        congr 1
        apply filter_congr_mem
        intro b _
        by_cases bIn : b ∈ seen
        · have v : seen.any (fun c => b == c) = true := by
            rw [List.any_eq_true]
            exact ⟨b, bIn, by simp⟩
          rw [v]
          simp
        · have v : seen.any (fun c => b == c) = false := by
            cases verdict : seen.any (fun c => b == c)
            · rfl
            · exfalso
              rw [List.any_eq_true] at verdict
              obtain ⟨c, cMem, beq⟩ := verdict
              have equal : b = c := by simpa using beq
              exact bIn (equal ▸ cMem)
          have bNe : (b == a) = false := by
            have neq : b ≠ a := fun equal => bIn (equal ▸ aInSeen)
            simp [neq]
          rw [v, bNe]
          simp
      · have anyMiss : seen.any (fun b => a == b) = false := by
          cases verdict : seen.any (fun b => a == b)
          · rfl
          · exact absurd verdict anyHit
        rw [anyMiss]
        simp only [if_false]
        rw [ih (a :: seen)]
        have aPred : (!(seen.any (fun c => a == c))) = true := by
          rw [anyMiss]
          rfl
        rw [firstOccs, List.filter_cons, aPred]
        simp only [if_true, List.reverse_cons, List.filter_filter]
        rw [List.append_assoc]
        congr 1
        rw [List.singleton_append]
        congr 1
        apply filter_congr_mem
        intro b _
        cases v1 : (b == a) with
        | true =>
            have shape : (a :: seen).any (fun c => b == c) = true := by
              rw [List.any_eq_true]
              exact ⟨a, List.mem_cons_self, v1⟩
            simp [shape, v1]
        | false =>
            have shape : (a :: seen).any (fun c => b == c) =
                seen.any (fun c => b == c) := by
              rw [List.any_cons, v1]
              rfl
            rw [shape]
            cases v2 : seen.any (fun c => b == c) <;> simp [v1, v2]

private theorem eraseDups_eq_firstOccs (L : List Nat) :
    L.eraseDups = firstOccs L := by
  rw [List.eraseDups, List.eraseDupsBy, eraseDups_loop_eq]
  simp

/-- Shifting the ambient list by a fresh head preserves sortedness of
index-ordered lists avoiding the head. -/
private theorem pairwise_shift {a : Nat} {rest : List Nat}
    {l : List Nat} (noA : ∀ e, e ∈ l → e ≠ a)
    (pw : List.Pairwise (fun e f => rest.idxOf e < rest.idxOf f) l) :
    List.Pairwise (fun e f =>
      (a :: rest).idxOf e < (a :: rest).idxOf f) l := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons e t ih =>
      rw [List.pairwise_cons] at pw ⊢
      obtain ⟨head, tail⟩ := pw
      refine ⟨?_, ih (fun f m => noA f (List.mem_cons_of_mem _ m)) tail⟩
      intro f fMem
      have eNe : (a == e) = false := by
        have neq : e ≠ a := noA e List.mem_cons_self
        have neq2 : a ≠ e := fun equal => neq equal.symm
        simp [neq2]
      have fNe : (a == f) = false := by
        have neq : f ≠ a := noA f (List.mem_cons_of_mem _ fMem)
        have neq2 : a ≠ f := fun equal => neq equal.symm
        simp [neq2]
      have eShift : (a :: rest).idxOf e = rest.idxOf e + 1 := by
        simp [List.idxOf_cons, eNe]
      have fShift : (a :: rest).idxOf f = rest.idxOf f + 1 := by
        simp [List.idxOf_cons, fNe]
      rw [eShift, fShift]
      have := head f fMem
      omega

/-- eraseDups lists letters in strictly increasing first-index order. -/
private theorem eraseDups_pairwise_idxOf (L : List Nat) :
    List.Pairwise (fun a b => L.idxOf a < L.idxOf b) L.eraseDups := by
  rw [eraseDups_eq_firstOccs]
  induction L with
  | nil => exact List.Pairwise.nil
  | cons a rest ih =>
      rw [firstOccs, List.pairwise_cons]
      constructor
      · intro b bMem
        have bData := List.mem_filter.mp bMem
        have bNe : (a == b) = false := by
          have : ¬ (b == a) = true := by
            intro hit
            rw [hit] at bData
            simp at bData
          have neq : b ≠ a := fun equal => this (by simp [equal])
          have neq2 : a ≠ b := fun equal => neq equal.symm
          simp [neq2]
        have aIdx : (a :: rest).idxOf a = 0 := by
          simp [List.idxOf_cons]
        have bIdx : (a :: rest).idxOf b = rest.idxOf b + 1 := by
          simp [List.idxOf_cons, bNe]
        omega
      · apply pairwise_shift
        · intro e eMem
          have eData := List.mem_filter.mp eMem
          intro equal
          rw [equal] at eData
          simp at eData
        · exact List.Pairwise.filter _ ih

/-! ## Region geometry used by second-occurrence assembly -/

/-- The first occurrence of a member never follows its last occurrence. -/
private theorem idxOf_le_lastIdxOf {L : List Nat} {x : Nat}
    (member : x ∈ L) : L.idxOf x ≤ lastIdxOf L x := by
  obtain ⟨A, B, shape, absent⟩ := firstSplit member
  subst L
  rw [idxOf_append_absent absent,
    lastIdxOf_append_right (P := A) (Q := x :: B)
      (by simp : x ∈ x :: B)]
  simp [List.idxOf_cons]

/-- Plasma letters occur in strictly increasing first-position order. -/
private theorem plasmaSeq_pairwise_idxOf (u : Word Nat) :
    List.Pairwise (fun a b => u.toList.idxOf a < u.toList.idxOf b)
      (plasmaSeq u) := by
  simpa only [plasmaSeq] using
    (List.Pairwise.filter
      (fun c => 2 ≤ u.toList.count c)
      (eraseDups_pairwise_idxOf u.toList))

/-- A take-while is empty when every member fails its predicate. -/
private theorem takeWhile_eq_nil_of_all_false {L : List Nat}
    {q : Nat → Bool} (fails : ∀ a, a ∈ L → q a = false) :
    L.takeWhile q = [] := by
  cases L with
  | nil => rfl
  | cons a rest =>
      rw [List.takeWhile_cons, fails a List.mem_cons_self]
      rfl

/-- A take-while cannot be longer than its source list. -/
private theorem length_takeWhile_le (L : List Nat) (q : Nat → Bool) :
    (L.takeWhile q).length ≤ L.length := by
  induction L with
  | nil => simp
  | cons a rest ih =>
      cases verdict : q a <;>
        simp [List.takeWhile_cons, verdict, ih]

/-- Pointwise implication of take-while predicates gives monotonicity of
their accepted-prefix lengths. -/
private theorem length_takeWhile_mono {L : List Nat} {q r : Nat → Bool}
    (imp : ∀ a, a ∈ L → q a = true → r a = true) :
    (L.takeWhile q).length ≤ (L.takeWhile r).length := by
  induction L with
  | nil => simp
  | cons a rest ih =>
      cases qHead : q a with
      | false => simp [List.takeWhile_cons, qHead]
      | true =>
          have rHead : r a = true := imp a List.mem_cons_self qHead
          have restImp : ∀ b, b ∈ rest → q b = true → r b = true := by
            intro b bMem
            exact imp b (List.mem_cons_of_mem _ bMem)
          simpa [List.takeWhile_cons, qHead, rHead] using ih restImp

/-- Slots are monotone in literal source position. -/
private theorem slotOf_mono_of_idx_le {u : Word Nat} {a b : Nat}
    (order : u.toList.idxOf a ≤ u.toList.idxOf b) :
    slotOf u a ≤ slotOf u b := by
  unfold slotOf
  apply length_takeWhile_mono
  intro p pMem passes
  have pBeforeA : u.toList.idxOf p < u.toList.idxOf a :=
    of_decide_eq_true passes
  exact decide_eq_true (Nat.lt_of_lt_of_le pBeforeA order)

/-- Every single slot is bounded by the plasma-sequence length. -/
private theorem slotOf_le_length (u : Word Nat) (s : Nat) :
    slotOf u s ≤ (plasmaSeq u).length := by
  exact length_takeWhile_le _ _

/-- A `before` single has slot zero. -/
private theorem slotOf_eq_zero_of_rel_before {u : Word Nat} {s : Nat}
    (relation : rel4 u s = Rel4.before) : slotOf u s = 0 := by
  have allBefore : (plasmaSeq u).all (fun p =>
      u.toList.idxOf s < u.toList.idxOf p) = true := by
    by_cases first : (plasmaSeq u).all (fun p =>
        u.toList.idxOf s < u.toList.idxOf p) = true
    · exact first
    · have firstFalse := Bool.eq_false_iff.mpr first
      have impossible : rel4 u s ≠ Rel4.before := by
        simp only [rel4, firstFalse, Bool.false_eq_true, if_false]
        split
        · simp
        · split <;> simp
      exact False.elim (impossible relation)
  rw [List.all_eq_true] at allBefore
  have allFail : ∀ p, p ∈ plasmaSeq u →
      decide (u.toList.idxOf p < u.toList.idxOf s) = false := by
    intro p pMem
    have later : u.toList.idxOf s < u.toList.idxOf p := by
      simpa using allBefore p pMem
    exact decide_eq_false (by omega)
  unfold slotOf
  rw [takeWhile_eq_nil_of_all_false allFail]
  rfl

/-- An `after` single has the terminal slot. -/
private theorem slotOf_eq_length_of_rel_after {u : Word Nat} {s : Nat}
    (relation : rel4 u s = Rel4.after) :
    slotOf u s = (plasmaSeq u).length := by
  have allAfter : (plasmaSeq u).all (fun p =>
      lastIdxOf u.toList p < u.toList.idxOf s) = true := by
    by_cases first : (plasmaSeq u).all (fun p =>
        u.toList.idxOf s < u.toList.idxOf p) = true
    · have impossible : rel4 u s = Rel4.before := by
        simp [rel4, first]
      rw [impossible] at relation
      cases relation
    · have firstFalse := Bool.eq_false_iff.mpr first
      by_cases second : (plasmaSeq u).all (fun p =>
          lastIdxOf u.toList p < u.toList.idxOf s) = true
      · exact second
      · have secondFalse := Bool.eq_false_iff.mpr second
        have impossible : rel4 u s ≠ Rel4.after := by
          simp only [rel4, firstFalse, secondFalse,
            Bool.false_eq_true, if_false]
          split <;> simp
        exact False.elim (impossible relation)
  rw [List.all_eq_true] at allAfter
  have allPass : ∀ p, p ∈ plasmaSeq u →
      decide (u.toList.idxOf p < u.toList.idxOf s) = true := by
    intro p pMem
    have pIn : p ∈ u.toList := mem_toList_of_mem_plasmaSeq pMem
    have lastBefore : lastIdxOf u.toList p < u.toList.idxOf s := by
      simpa using allAfter p pMem
    exact decide_eq_true
      (Nat.lt_of_le_of_lt (idxOf_le_lastIdxOf pIn) lastBefore)
  unfold slotOf
  have whole := takeWhile_append_all
    (l := plasmaSeq u) (r := []) allPass
  exact congrArg List.length (by simpa using whole)

/-- Membership survives into eraseDups. -/
private theorem mem_eraseDups_of_mem {L : List Nat} {x : Nat}
    (member : x ∈ L) : x ∈ L.eraseDups := by
  rw [eraseDups_eq_firstOccs]
  induction L with
  | nil => cases member
  | cons a rest ih =>
      rw [firstOccs]
      by_cases hit : x = a
      · rw [hit]
        exact List.mem_cons_self
      · have restMem : x ∈ rest := by
          rcases List.mem_cons.mp member with equal | tailMem
          · exact absurd equal hit
          · exact tailMem
        apply List.mem_cons_of_mem
        rw [List.mem_filter]
        refine ⟨ih restMem, ?_⟩
        simp [hit]

/-- Appending the second occurrence of a single letter inserts it into
the plasma sequence exactly at its slot. -/
private theorem plasmaSeq_snoc_second {h x : Nat} {T : List Nat}
    (single : List.count x (h :: T) = 1) :
    plasmaSeq (⟨h, T ++ [x]⟩ : Word Nat) =
      (plasmaSeq (⟨h, T⟩ : Word Nat)).take
        (slotOf (⟨h, T⟩ : Word Nat) x) ++
      x :: (plasmaSeq (⟨h, T⟩ : Word Nat)).drop
        (slotOf (⟨h, T⟩ : Word Nat) x) := by
  have core : ∀ (L : List Nat), List.count x L = 1 →
      (L ++ [x]).eraseDups.filter (fun c => 2 ≤ (L ++ [x]).count c) =
      (L.eraseDups.filter (fun c => 2 ≤ L.count c)).take
        ((L.eraseDups.filter (fun c => 2 ≤ L.count c)).takeWhile
          (fun p => L.idxOf p < L.idxOf x)).length ++
      x :: (L.eraseDups.filter (fun c => 2 ≤ L.count c)).drop
        ((L.eraseDups.filter (fun c => 2 ≤ L.count c)).takeWhile
          (fun p => L.idxOf p < L.idxOf x)).length := by
    intro L singleL
    have xMem : x ∈ L := List.count_pos_iff.mp (by omega)
    rw [eraseDups_snoc_mem xMem]
    obtain ⟨A, B, shape, notInA⟩ :=
      firstSplit (mem_eraseDups_of_mem xMem)
    have pw := eraseDups_pairwise_idxOf L
    rw [shape] at pw
    rw [List.pairwise_append] at pw
    obtain ⟨pwA, pwXB, cross⟩ := pw
    rw [List.pairwise_cons] at pwXB
    obtain ⟨xBelow, pwB⟩ := pwXB
    have aSide : ∀ a, a ∈ A → L.idxOf a < L.idxOf x :=
      fun a aMem => cross a aMem x List.mem_cons_self
    have bSide : ∀ b, b ∈ B → L.idxOf x < L.idxOf b := xBelow
    have notInB : x ∉ B := by
      intro xInB
      have := bSide x xInB
      omega
    -- new-count filter splits around x
    have countXNew : (L ++ [x]).count x = 2 := by
      rw [count_append_self, singleL]
    have filterNew : (A ++ x :: B).filter
        (fun c => 2 ≤ (L ++ [x]).count c) =
        A.filter (fun c => 2 ≤ L.count c) ++
        x :: B.filter (fun c => 2 ≤ L.count c) := by
      rw [List.filter_append, List.filter_cons]
      have xPass : decide (2 ≤ (L ++ [x]).count x) = true := by
        rw [countXNew]
        rfl
      rw [xPass]
      simp only [if_true]
      congr 1
      · apply filter_congr_mem
        intro e eMem
        have ne : e ≠ x := fun equal => notInA (equal ▸ eMem)
        rw [count_append_ne ne]
      · congr 1
        apply filter_congr_mem
        intro e eMem
        have ne : e ≠ x := fun equal => notInB (equal ▸ eMem)
        rw [count_append_ne ne]
    -- old filter drops x
    have filterOld : (A ++ x :: B).filter
        (fun c => 2 ≤ L.count c) =
        A.filter (fun c => 2 ≤ L.count c) ++
        B.filter (fun c => 2 ≤ L.count c) := by
      rw [List.filter_append, List.filter_cons]
      have xDrop : decide (2 ≤ L.count x) = false := by
        rw [singleL]
        rfl
      rw [xDrop]
      simp only [Bool.false_eq_true, if_false]
    rw [shape, filterNew, filterOld]
    -- takeWhile over the old filtered sequence is exactly filter A
    have takeShape : (A.filter (fun c => 2 ≤ L.count c) ++
        B.filter (fun c => 2 ≤ L.count c)).takeWhile
        (fun p => L.idxOf p < L.idxOf x) =
        A.filter (fun c => 2 ≤ L.count c) := by
      rw [takeWhile_append_all]
      · have stops : (B.filter (fun c => 2 ≤ L.count c)).takeWhile
            (fun p => L.idxOf p < L.idxOf x) = [] := by
          cases bShape : B.filter (fun c => 2 ≤ L.count c) with
          | nil => rfl
          | cons b0 rest =>
              have b0Mem : b0 ∈ B := by
                have : b0 ∈ B.filter (fun c => 2 ≤ L.count c) := by
                  rw [bShape]
                  exact List.mem_cons_self
                exact (List.mem_filter.mp this).1
              have := bSide b0 b0Mem
              rw [List.takeWhile_cons]
              have fails : decide (L.idxOf b0 < L.idxOf x) = false := by
                have notLt : ¬ (L.idxOf b0 < L.idxOf x) := by omega
                simp [notLt]
              rw [fails]
              simp
        rw [stops, List.append_nil]
      · intro a aMem
        have aInA : a ∈ A := (List.mem_filter.mp aMem).1
        exact decide_eq_true (aSide a aInA)
    rw [takeShape, List.take_left, List.drop_left]
  exact core (h :: T) single

/-! ## takeWhile under a single insertion (slot shift arithmetic) -/

/-- A failing member keeps takeWhile strictly short of the length. -/
private theorem takeWhile_ne_length_of_fail {P : List Nat}
    {q : Nat → Bool} {e : Nat} (eMem : e ∈ P) (eFail : q e = false) :
    (P.takeWhile q).length ≠ P.length := by
  induction P with
  | nil => cases eMem
  | cons a t ih =>
      rw [List.takeWhile_cons]
      by_cases qa : q a = true
      · rw [qa]
        simp only [if_true, List.length_cons]
        have eInT : e ∈ t := by
          rcases List.mem_cons.mp eMem with equal | tailMem
          · exfalso
            rw [← equal] at qa
            rw [qa] at eFail
            cases eFail
          · exact tailMem
        have := ih eInT
        omega
      · have qaF : q a = false := by
          cases v : q a
          · rfl
          · exact absurd v qa
        rw [qaF]
        simp only [Bool.false_eq_true, if_false, List.length_nil,
          List.length_cons]
        omega

/-- Inserting a failing element after a fully-failing tail start keeps
the takeWhile length. -/
private theorem takeWhile_insert_false {P Q : List Nat} {x : Nat}
    {q : Nat → Bool} (px : q x = false)
    (qFail : ∀ e, e ∈ Q → q e = false) :
    ((P ++ x :: Q).takeWhile q).length =
      ((P ++ Q).takeWhile q).length := by
  by_cases allP : ∀ e, e ∈ P → q e = true
  · rw [takeWhile_append_all allP, takeWhile_append_all allP]
    have t1 : (x :: Q).takeWhile q = [] := by
      rw [List.takeWhile_cons, px]
      simp
    have t2 : Q.takeWhile q = [] := by
      cases qShape : Q with
      | nil => rfl
      | cons e t =>
          rw [List.takeWhile_cons,
            qFail e (qShape ▸ List.mem_cons_self)]
          simp
    rw [t1, t2]
  · obtain ⟨e, eBad⟩ := Classical.not_forall.mp allP
    obtain ⟨eMem, eFailT⟩ := Classical.not_imp.mp eBad
    have eFail : q e = false := by
      cases v : q e
      · rfl
      · exact absurd v eFailT
    have stop := takeWhile_ne_length_of_fail eMem eFail
    rw [takeWhile_append_stop stop, takeWhile_append_stop stop]

/-- Inserting a passing element after a fully-passing prefix bumps the
takeWhile length by one. -/
private theorem takeWhile_insert_true {P Q : List Nat} {x : Nat}
    {q : Nat → Bool} (px : q x = true)
    (allP : ∀ e, e ∈ P → q e = true) :
    ((P ++ x :: Q).takeWhile q).length =
      ((P ++ Q).takeWhile q).length + 1 := by
  rw [takeWhile_append_all allP, takeWhile_append_all allP,
    List.takeWhile_cons, px]
  simp only [if_true, List.length_append, List.length_cons]
  omega

/-- idxOf is injective on members. -/
private theorem idxOf_inj_local {L : List Nat} {a b : Nat}
    (aMem : a ∈ L) (equal : L.idxOf a = L.idxOf b) : a = b := by
  induction L with
  | nil => cases aMem
  | cons c t ih =>
      by_cases ca : c = a
      · by_cases cb : c = b
        · rw [← ca, cb]
        · exfalso
          have caB : (c == a) = true := by simp [ca]
          have cbB : (c == b) = false := by simp [cb]
          simp [List.idxOf_cons, caB, cbB] at equal
      · by_cases cb : c = b
        · exfalso
          have caB : (c == a) = false := by simp [ca]
          have cbB : (c == b) = true := by simp [cb]
          simp [List.idxOf_cons, caB, cbB] at equal
        · have caB : (c == a) = false := by simp [ca]
          have cbB : (c == b) = false := by simp [cb]
          simp only [List.idxOf_cons, caB, cbB, cond_false] at equal
          have aInT : a ∈ t := by
            rcases List.mem_cons.mp aMem with hit | tailMem
            · exact absurd hit.symm ca
            · exact tailMem
          exact ih aInT (by omega)

/-- A single in any non-before region has a positive slot. -/
private theorem slotOf_pos_of_single_rel_ne_before {u : Word Nat} {s : Nat}
    (single : IsSingle u s) (relation : rel4 u s ≠ Rel4.before) :
    0 < slotOf u s := by
  have countOne : u.toList.count s = 1 := single
  have sMem : s ∈ u.toList := List.count_pos_iff.mp (by omega)
  have sNotPlasma : s ∉ plasmaSeq u := by
    intro sPlasma
    have big := (List.mem_filter.mp sPlasma).2
    have : 2 ≤ u.toList.count s := by simpa [plasmaSeq] using big
    omega
  by_cases zero : slotOf u s = 0
  · cases shape : plasmaSeq u with
    | nil =>
        exact False.elim
          (relation (rel4_of_plasma_nil shape))
    | cons p rest =>
        have firstFail :
            decide (u.toList.idxOf p < u.toList.idxOf s) = false := by
          unfold slotOf at zero
          rw [shape, List.takeWhile_cons] at zero
          cases verdict : decide
              (u.toList.idxOf p < u.toList.idxOf s)
          · rfl
          · simp only [verdict, if_true, List.length_cons] at zero
            omega
        have pMem : p ∈ plasmaSeq u := by
          rw [shape]
          exact List.mem_cons_self
        have pIn : p ∈ u.toList := mem_toList_of_mem_plasmaSeq pMem
        have psNe : p ≠ s := by
          intro equal
          exact sNotPlasma (equal ▸ pMem)
        have idxNe : u.toList.idxOf p ≠ u.toList.idxOf s :=
          fun equal => psNe (idxOf_inj_local pIn equal)
        have sBeforeP : u.toList.idxOf s < u.toList.idxOf p := by
          have notBefore : ¬ u.toList.idxOf p < u.toList.idxOf s := by
            simpa using Bool.eq_false_iff.mp firstFail
          omega
        have ordered := plasmaSeq_pairwise_idxOf u
        rw [shape, List.pairwise_cons] at ordered
        obtain ⟨pBeforeRest, _⟩ := ordered
        have allBefore : (plasmaSeq u).all (fun q =>
            u.toList.idxOf s < u.toList.idxOf q) = true := by
          rw [shape, List.all_eq_true]
          intro q qMem
          rcases List.mem_cons.mp qMem with equal | qRest
          · simpa [equal] using decide_eq_true sBeforeP
          · exact decide_eq_true
              (Nat.lt_trans sBeforeP (pBeforeRest q qRest))
        have before : rel4 u s = Rel4.before := by
          simp [rel4, allBefore]
        exact False.elim (relation before)
  · omega

/-! ## Source order of the single sequence -/

/-- Filtering a suffix for letters that occur once in the whole
prefix-plus-suffix word preserves strict literal source order. -/
private theorem singleFilter_pairwise_idxOf (P L : List Nat) :
    List.Pairwise
      (fun a b => (P ++ L).idxOf a < (P ++ L).idxOf b)
      (L.filter (fun c => (P ++ L).count c == 1)) := by
  induction L generalizing P with
  | nil => simp
  | cons a rest ih =>
      cases pass : ((P ++ a :: rest).count a == 1) with
      | false =>
          rw [List.filter_cons, pass]
          simpa [List.append_assoc] using ih (P ++ [a])
      | true =>
          rw [List.filter_cons, pass]
          simp only [if_true, List.pairwise_cons]
          constructor
          · intro b bMem
            have bData := List.mem_filter.mp bMem
            have bInRest : b ∈ rest := bData.1
            have aCount : (P ++ a :: rest).count a = 1 :=
              eq_of_beq pass
            have bCount : (P ++ a :: rest).count b = 1 :=
              eq_of_beq bData.2
            have aNotP : a ∉ P := by
              intro aInP
              have pPos : 0 < P.count a := List.count_pos_iff.mpr aInP
              rw [List.count_append] at aCount
              simp at aCount
              omega
            have aNeB : a ≠ b := by
              intro equal
              subst b
              have restPos : 0 < rest.count a :=
                List.count_pos_iff.mpr bInRest
              rw [List.count_append] at aCount
              simp at aCount
              omega
            have bNotP : b ∉ P := by
              intro bInP
              have pPos : 0 < P.count b := List.count_pos_iff.mpr bInP
              have restPos : 0 < (a :: rest).count b :=
                List.count_pos_iff.mpr (List.mem_cons_of_mem _ bInRest)
              rw [List.count_append] at bCount
              omega
            have idxA : (P ++ a :: rest).idxOf a = P.length := by
              rw [idxOf_append_absent aNotP]
              simp [List.idxOf_cons]
            have idxB : (P ++ a :: rest).idxOf b =
                P.length + 1 + rest.idxOf b := by
              rw [idxOf_append_absent bNotP]
              have ab : (a == b) = false := by simp [aNeB]
              simp [List.idxOf_cons, ab]
              omega
            rw [idxA, idxB]
            omega
          · simpa [List.append_assoc] using ih (P ++ [a])

/-- The displayed single sequence is strictly ordered by source index. -/
private theorem singlesSeq_pairwise_idxOf (u : Word Nat) :
    List.Pairwise (fun a b => u.toList.idxOf a < u.toList.idxOf b)
      (singlesSeq u) := by
  simpa only [singlesSeq, List.nil_append] using
    singleFilter_pairwise_idxOf [] u.toList

/-- Removing a count-one word head preserves strict source order. -/
private theorem strippedSingles_pairwise_idxOf (u : Word Nat) :
    List.Pairwise (fun a b => u.toList.idxOf a < u.toList.idxOf b)
      (strippedSingles u) := by
  have ordered := singlesSeq_pairwise_idxOf u
  unfold strippedSingles
  by_cases cond :
      (decide ((singlesSeq u).take 1 = [u.head]) &&
        !decide (IsPlasma u u.head)) = true
  · rw [if_pos cond]
    cases shape : singlesSeq u with
    | nil => simp [shape]
    | cons a rest =>
        rw [shape, List.pairwise_cons] at ordered
        simpa [shape] using ordered.2
  · rw [if_neg cond]
    exact ordered

/-- A single splits the single sequence at its literal source position. -/
private theorem singlesSeq_split_single {h x : Nat} {T : List Nat}
    (single : List.count x (h :: T) = 1) :
    ∃ A B,
      singlesSeq (⟨h, T⟩ : Word Nat) = A ++ x :: B ∧
      (∀ a, a ∈ A → (h :: T).idxOf a < (h :: T).idxOf x) ∧
      (∀ b, b ∈ B → (h :: T).idxOf x < (h :: T).idxOf b) := by
  have xMem : x ∈ h :: T := List.count_pos_iff.mp (by omega)
  obtain ⟨P, Q, shape, notInP⟩ := firstSplit xMem
  have countShape : List.count x (P ++ x :: Q) = 1 := by
    rw [← shape]
    exact single
  have notInQ : x ∉ Q := by
    intro inQ
    have pZero : P.count x = 0 := List.count_eq_zero.mpr notInP
    have qPos : 0 < Q.count x := List.count_pos_iff.mpr inQ
    rw [List.count_append, pZero] at countShape
    simp at countShape
    omega
  let q : Nat → Bool := fun c => (P ++ x :: Q).count c == 1
  refine ⟨P.filter q, Q.filter q, ?_, ?_, ?_⟩
  · simp only [singlesSeq, toList_mk, shape, List.filter_append,
      List.filter_cons, q]
    have xPass : ((P ++ x :: Q).count x == 1) = true := by
      simp [countShape]
    rw [xPass]
    rfl
  · intro a aMem
    have aInP : a ∈ P := (List.mem_filter.mp aMem).1
    have aBound : P.idxOf a < P.length :=
      idxOf_lt_length_of_mem_local aInP
    have idxA : (P ++ x :: Q).idxOf a = P.idxOf a :=
      idxOf_append_left aInP _
    have idxX : (P ++ x :: Q).idxOf x = P.length := by
      rw [idxOf_append_absent notInP]
      simp [List.idxOf_cons]
    rw [shape, idxA, idxX]
    exact aBound
  · intro b bMem
    have bData := List.mem_filter.mp bMem
    have bInQ : b ∈ Q := bData.1
    have bCount : (P ++ x :: Q).count b = 1 := by
      simpa [q] using bData.2
    have bNeX : b ≠ x := by
      intro equal
      exact notInQ (equal ▸ bInQ)
    have bNotInP : b ∉ P := by
      intro bInP
      have pPos : 0 < P.count b := List.count_pos_iff.mpr bInP
      have qPos : 0 < (x :: Q).count b :=
        List.count_pos_iff.mpr (List.mem_cons_of_mem _ bInQ)
      rw [List.count_append] at bCount
      omega
    have idxX : (P ++ x :: Q).idxOf x = P.length := by
      rw [idxOf_append_absent notInP]
      simp [List.idxOf_cons]
    have idxB : (P ++ x :: Q).idxOf b = P.length + 1 + Q.idxOf b := by
      rw [idxOf_append_absent bNotInP]
      have xb : (x == b) = false := by
        have : x ≠ b := fun equal => bNeX equal.symm
        simp [this]
      simp [List.idxOf_cons, xb]
      omega
    rw [shape, idxX, idxB]
    omega

/-- Except for a count-one word head, a single also splits the stripped
single sequence at its literal source position. -/
private theorem strippedSingles_split_single {h x : Nat} {T : List Nat}
    (single : List.count x (h :: T) = 1) (headNe : h ≠ x) :
    ∃ A B,
      strippedSingles (⟨h, T⟩ : Word Nat) = A ++ x :: B ∧
      (∀ a, a ∈ A → (h :: T).idxOf a < (h :: T).idxOf x) ∧
      (∀ b, b ∈ B → (h :: T).idxOf x < (h :: T).idxOf b) := by
  obtain ⟨A, B, shape, left, right⟩ := singlesSeq_split_single single
  simp only [strippedSingles]
  by_cases cond : (decide (List.take 1
      (singlesSeq (⟨h, T⟩ : Word Nat)) = [h]) &&
      !decide (IsPlasma (⟨h, T⟩ : Word Nat) h)) = true
  · rw [if_pos cond]
    have takeHead : List.take 1
        (singlesSeq (⟨h, T⟩ : Word Nat)) = [h] := by
      have parts := cond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at parts
      exact parts.1
    cases aShape : A with
    | nil =>
        have equal : x = h := by
          rw [shape, aShape] at takeHead
          simpa using takeHead
        exact False.elim (headNe equal.symm)
    | cons a rest =>
        refine ⟨rest, B, ?_, ?_, right⟩
        · rw [shape, aShape]
          rfl
        · intro b bMem
          exact left b (by rw [aShape]; exact List.mem_cons_of_mem _ bMem)
  · rw [if_neg cond]
    exact ⟨A, B, shape, left, right⟩

/-- The inside witness is exposed by an `inside` relation. -/
private theorem insideAny_eq_true_of_rel_inside {u : Word Nat} {s : Nat}
    (relation : rel4 u s = Rel4.inside) :
    (plasmaSeq u).any (fun p =>
      u.toList.idxOf p < u.toList.idxOf s &&
        u.toList.idxOf s < lastIdxOf u.toList p) = true := by
  unfold rel4 at relation
  split at relation
  · cases relation
  · split at relation
    · cases relation
    · split at relation
      · assumption
      · cases relation

/-- A displayed plasma interval forces the inside relation. -/
private theorem rel4_eq_inside_of_plasma_between {u : Word Nat}
    {p s : Nat} (pMem : p ∈ plasmaSeq u)
    (openBefore : u.toList.idxOf p < u.toList.idxOf s)
    (closeAfter : u.toList.idxOf s < lastIdxOf u.toList p) :
    rel4 u s = Rel4.inside := by
  have c1 : (plasmaSeq u).all (fun q =>
      u.toList.idxOf s < u.toList.idxOf q) = false := by
    rw [List.all_eq_false]
    refine ⟨p, pMem, ?_⟩
    show ¬ decide (u.toList.idxOf s < u.toList.idxOf p) = true
    rw [decide_eq_false (by omega)]
    simp
  have c2 : (plasmaSeq u).all (fun q =>
      lastIdxOf u.toList q < u.toList.idxOf s) = false := by
    rw [List.all_eq_false]
    refine ⟨p, pMem, ?_⟩
    show ¬ decide (lastIdxOf u.toList p < u.toList.idxOf s) = true
    rw [decide_eq_false (by omega)]
    simp
  have c3 : (plasmaSeq u).any (fun q =>
      u.toList.idxOf q < u.toList.idxOf s &&
        u.toList.idxOf s < lastIdxOf u.toList q) = true := by
    rw [List.any_eq_true]
    refine ⟨p, pMem, ?_⟩
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using
      And.intro openBefore closeAfter
  simp [rel4, c1, c2, c3]

/-- If a plasma open precedes one single, it precedes every single with
the same slot. -/
private theorem plasma_before_of_same_slot {u : Word Nat}
    {p x y : Nat} (pMem : p ∈ plasmaSeq u)
    (pBeforeX : u.toList.idxOf p < u.toList.idxOf x)
    (sameSlot : slotOf u x = slotOf u y)
    (ySingle : IsSingle u y) :
    u.toList.idxOf p < u.toList.idxOf y := by
  by_cases pBeforeY : u.toList.idxOf p < u.toList.idxOf y
  · exact pBeforeY
  · exfalso
    have pCount : 2 ≤ u.toList.count p := by
      exact of_decide_eq_true (List.mem_filter.mp pMem).2
    have yCount : u.toList.count y = 1 := ySingle
    have pNe : p ≠ y := by
      intro equal
      rw [equal] at pCount
      omega
    have idxNe : u.toList.idxOf p ≠ u.toList.idxOf y := by
      intro equal
      exact pNe (idxOf_inj_local
        (mem_toList_of_mem_plasmaSeq pMem) equal)
    have yBeforeP : u.toList.idxOf y < u.toList.idxOf p := by omega
    obtain ⟨A, B, pseqShape, _⟩ := firstSplit pMem
    have sorted := plasmaSeq_pairwise_idxOf u
    rw [pseqShape, List.pairwise_append] at sorted
    obtain ⟨_, _, cross⟩ := sorted
    have aBeforeP : ∀ a, a ∈ A →
        u.toList.idxOf a < u.toList.idxOf p := by
      intro a aMem
      exact cross a aMem p List.mem_cons_self
    have allAX : ∀ a, a ∈ A →
        decide (u.toList.idxOf a < u.toList.idxOf x) = true := by
      intro a aMem
      exact decide_eq_true (Nat.lt_trans (aBeforeP a aMem) pBeforeX)
    have pPassX :
        decide (u.toList.idxOf p < u.toList.idxOf x) = true :=
      decide_eq_true pBeforeX
    have xLower : A.length < slotOf u x := by
      unfold slotOf
      rw [pseqShape, takeWhile_append_all allAX,
        List.takeWhile_cons, pPassX]
      simp
    have pFailY :
        decide (u.toList.idxOf p < u.toList.idxOf y) = false :=
      decide_eq_false (by omega)
    have stop := takeWhile_ne_length_of_fail
      (P := A ++ [p])
      (q := fun q => u.toList.idxOf q < u.toList.idxOf y)
      (e := p) (by simp) pFailY
    have yUpper : slotOf u y ≤ A.length := by
      unfold slotOf
      rw [pseqShape]
      have appendShape : A ++ p :: B = (A ++ [p]) ++ B := by simp
      rw [appendShape, takeWhile_append_stop stop]
      have bound := length_takeWhile_le (A ++ [p])
        (fun q => u.toList.idxOf q < u.toList.idxOf y)
      have prefixLength : (A ++ [p]).length = A.length + 1 := by simp
      rw [prefixLength] at bound stop
      omega
    rw [sameSlot] at xLower
    omega

/-- At a fixed slot, inside singles precede gap singles in source order. -/
private theorem inside_before_same_slot_gap {u : Word Nat} {x g : Nat}
    (xSingle : IsSingle u x) (gSingle : IsSingle u g)
    (inside : rel4 u x = Rel4.inside)
    (gap : rel4 u g = Rel4.gap)
    (sameSlot : slotOf u x = slotOf u g) :
    u.toList.idxOf x < u.toList.idxOf g := by
  obtain ⟨p, pMem, insideData⟩ :=
    List.any_eq_true.mp (insideAny_eq_true_of_rel_inside inside)
  have bounds :
      u.toList.idxOf p < u.toList.idxOf x ∧
        u.toList.idxOf x < lastIdxOf u.toList p := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using insideData
  have pBeforeG :=
    plasma_before_of_same_slot pMem bounds.1 sameSlot gSingle
  by_cases xBeforeG : u.toList.idxOf x < u.toList.idxOf g
  · exact xBeforeG
  · have xgNe : x ≠ g := by
      intro equal
      rw [← equal] at gap
      rw [inside] at gap
      cases gap
    have xIn : x ∈ u.toList := by
      have xCount : u.toList.count x = 1 := xSingle
      exact List.count_pos_iff.mp (by omega)
    have idxNe : u.toList.idxOf x ≠ u.toList.idxOf g := by
      intro equal
      exact xgNe (idxOf_inj_local xIn equal)
    have gBeforeX : u.toList.idxOf g < u.toList.idxOf x := by omega
    have gInside := rel4_eq_inside_of_plasma_between pMem pBeforeG
      (Nat.lt_trans gBeforeX bounds.2)
    rw [gap] at gInside
    cases gInside

private theorem isSingle_of_mem_stripped {u : Word Nat} {s : Nat}
    (member : s ∈ strippedSingles u) : IsSingle u s := by
  have inSingles := mem_singles_of_mem_stripped member
  exact eq_of_beq (List.mem_filter.mp inSingles).2

private theorem inside_before_same_slot_gap_of_mem {u : Word Nat}
    {x g : Nat} (xSingle : IsSingle u x)
    (gMem : g ∈ strippedSingles u)
    (inside : rel4 u x = Rel4.inside)
    (gap : rel4 u g = Rel4.gap)
    (sameSlot : slotOf u x = slotOf u g) :
    u.toList.idxOf x < u.toList.idxOf g :=
  inside_before_same_slot_gap xSingle
    (isSingle_of_mem_stripped gMem) inside gap sameSlot

/-- The second guard of `rel4` is exposed by an `after` relation. -/
private theorem allAfter_of_rel4_after {u : Word Nat} {s : Nat}
    (relation : rel4 u s = Rel4.after) :
    (plasmaSeq u).all (fun p =>
      lastIdxOf u.toList p < u.toList.idxOf s) = true := by
  by_cases first : (plasmaSeq u).all (fun p =>
      u.toList.idxOf s < u.toList.idxOf p) = true
  · have before : rel4 u s = Rel4.before := by simp [rel4, first]
    rw [before] at relation
    cases relation
  · have firstFalse := Bool.eq_false_iff.mpr first
    by_cases second : (plasmaSeq u).all (fun p =>
        lastIdxOf u.toList p < u.toList.idxOf s) = true
    · exact second
    · have secondFalse := Bool.eq_false_iff.mpr second
      have notAfter : rel4 u s ≠ Rel4.after := by
        simp only [rel4, firstFalse, secondFalse,
          Bool.false_eq_true, if_false]
        split <;> simp
      exact False.elim (notAfter relation)

/-- The first guard of `rel4` is exposed by a `before` relation. -/
private theorem allBefore_of_rel4_before {u : Word Nat} {s : Nat}
    (relation : rel4 u s = Rel4.before) :
    (plasmaSeq u).all (fun p =>
      u.toList.idxOf s < u.toList.idxOf p) = true := by
  by_cases first : (plasmaSeq u).all (fun p =>
      u.toList.idxOf s < u.toList.idxOf p) = true
  · exact first
  · have firstFalse := Bool.eq_false_iff.mpr first
    have notBefore : rel4 u s ≠ Rel4.before := by
      simp only [rel4, firstFalse, Bool.false_eq_true, if_false]
      split
      · simp
      · split <;> simp
    exact False.elim (notBefore relation)

/-- A before-single forces the word head to be absent from the plasma
sequence; otherwise it would have to precede index zero. -/
private theorem head_not_mem_plasma_of_rel_before {u : Word Nat} {s : Nat}
    (relation : rel4 u s = Rel4.before) : u.head ∉ plasmaSeq u := by
  intro headMem
  have allBefore := allBefore_of_rel4_before relation
  rw [List.all_eq_true] at allBefore
  have impossible : u.toList.idxOf s < u.toList.idxOf u.head := by
    simpa using allBefore u.head headMem
  have headIdx : u.toList.idxOf u.head = 0 := by
    change (u.head :: u.tail).idxOf u.head = 0
    simp
  omega

/-- Once an after-single has occurred, every later single is also after. -/
private theorem rel4_after_of_later {u : Word Nat} {x s : Nat}
    (afterX : rel4 u x = Rel4.after)
    (late : u.toList.idxOf x < u.toList.idxOf s) :
    rel4 u s = Rel4.after := by
  have nonempty : plasmaSeq u ≠ [] := by
    intro empty
    have relation := rel4_of_plasma_nil (u := u) (s := x) empty
    rw [relation] at afterX
    cases afterX
  have afterAllX := allAfter_of_rel4_after afterX
  rw [List.all_eq_true] at afterAllX
  have afterAllS : (plasmaSeq u).all (fun p =>
      lastIdxOf u.toList p < u.toList.idxOf s) = true := by
    rw [List.all_eq_true]
    intro p pMem
    have closed : lastIdxOf u.toList p < u.toList.idxOf x := by
      simpa using afterAllX p pMem
    exact decide_eq_true (Nat.lt_trans closed late)
  have beforeFalse : (plasmaSeq u).all (fun p =>
      u.toList.idxOf s < u.toList.idxOf p) = false := by
    rw [List.all_eq_false]
    obtain ⟨p, rest, shape⟩ := List.exists_cons_of_ne_nil nonempty
    have pMem : p ∈ plasmaSeq u := by rw [shape]; simp
    have pIn : p ∈ u.toList := mem_toList_of_mem_plasmaSeq pMem
    have closed : lastIdxOf u.toList p < u.toList.idxOf x := by
      simpa using afterAllX p pMem
    refine ⟨p, pMem, ?_⟩
    have notBefore : ¬ u.toList.idxOf s < u.toList.idxOf p := by
      have firstLeLast := idxOf_le_lastIdxOf pIn
      omega
    rw [decide_eq_false notBefore]
    simp
  simp [rel4, beforeFalse, afterAllS]

/-- If a single is not after while another single is after, the former
occurs first in literal source order. -/
private theorem idxOf_lt_of_rel_ne_after_rel_after {u : Word Nat}
    {x s : Nat} (xSingle : IsSingle u x)
    (xNotAfter : rel4 u x ≠ Rel4.after)
    (sAfter : rel4 u s = Rel4.after) :
    u.toList.idxOf x < u.toList.idxOf s := by
  have xMem : x ∈ u.toList := by
    have countOne : u.toList.count x = 1 := xSingle
    exact List.count_pos_iff.mp (by omega)
  have xNeS : x ≠ s := by
    intro equal
    exact xNotAfter (equal ▸ sAfter)
  have idxNe : u.toList.idxOf x ≠ u.toList.idxOf s := by
    intro equal
    exact xNeS (idxOf_inj_local xMem equal)
  by_cases order : u.toList.idxOf x < u.toList.idxOf s
  · exact order
  · have reverse : u.toList.idxOf s < u.toList.idxOf x := by omega
    exact False.elim
      (xNotAfter (rel4_after_of_later sAfter reverse))

/-- A single position cannot coincide with the last occurrence of a
different member letter. -/
private theorem lastIdxOf_ne_idxOf_of_single {u : Word Nat} {s p : Nat}
    (single : IsSingle u s) (pMem : p ∈ u.toList) (pNe : p ≠ s) :
    lastIdxOf u.toList p ≠ u.toList.idxOf s := by
  have countOne : u.toList.count s = 1 := single
  have sMem : s ∈ u.toList := List.count_pos_iff.mp (by omega)
  obtain ⟨A, B, shape, notInA⟩ := firstSplit sMem
  have notInB : s ∉ B := by
    intro inB
    have aZero : A.count s = 0 := List.count_eq_zero.mpr notInA
    have bPos : 0 < B.count s := List.count_pos_iff.mpr inB
    rw [shape, List.count_append, aZero] at countOne
    simp at countOne
    omega
  rw [shape] at pMem ⊢
  by_cases inB : p ∈ B
  · rw [idxOf_append_absent notInA,
      lastIdxOf_append_right (P := A) (Q := s :: B)
        (List.mem_cons_of_mem _ inB),
      lastIdxOf_cons_of_mem inB]
    simp [List.idxOf_cons]
  · have inA : p ∈ A := by
      rcases List.mem_append.mp pMem with inA | inRest
      · exact inA
      · rcases List.mem_cons.mp inRest with equal | inB'
        · exact False.elim (pNe equal)
        · exact False.elim (inB inB')
    have notInRest : p ∉ s :: B := by simp [pNe, inB]
    rw [idxOf_append_absent notInA,
      lastIdxOf_append_left inA notInRest]
    simp [List.idxOf_cons]
    exact Nat.ne_of_lt (lastIdxOf_lt_length inA)

/-- A single at the terminal plasma slot is before no open, and hence
cannot be a gap. -/
private theorem rel4_ne_gap_of_terminal_slot {u : Word Nat} {s : Nat}
    (single : IsSingle u s)
    (terminal : slotOf u s = (plasmaSeq u).length) :
    rel4 u s ≠ Rel4.gap := by
  intro gap
  have beforeFalse : (plasmaSeq u).all (fun p =>
      u.toList.idxOf s < u.toList.idxOf p) = false := by
    cases first : (plasmaSeq u).all (fun p =>
        u.toList.idxOf s < u.toList.idxOf p) with
    | false => rfl
    | true =>
        have before : rel4 u s = Rel4.before := by
          simp [rel4, first]
        rw [before] at gap
        cases gap
  have afterFalse : (plasmaSeq u).all (fun p =>
      lastIdxOf u.toList p < u.toList.idxOf s) = false := by
    cases second : (plasmaSeq u).all (fun p =>
        lastIdxOf u.toList p < u.toList.idxOf s) with
    | false => rfl
    | true =>
        have after : rel4 u s = Rel4.after := by
          simp [rel4, beforeFalse, second]
        rw [after] at gap
        cases gap
  have insideFalse : (plasmaSeq u).any (fun p =>
      u.toList.idxOf p < u.toList.idxOf s &&
        u.toList.idxOf s < lastIdxOf u.toList p) = false := by
    cases inside : (plasmaSeq u).any (fun p =>
        u.toList.idxOf p < u.toList.idxOf s &&
          u.toList.idxOf s < lastIdxOf u.toList p) with
    | false => rfl
    | true =>
        have insideRel : rel4 u s = Rel4.inside := by
          simp [rel4, beforeFalse, afterFalse, inside]
        rw [insideRel] at gap
        cases gap
  have lengthEq : ((plasmaSeq u).takeWhile (fun p =>
      u.toList.idxOf p < u.toList.idxOf s)).length =
      (plasmaSeq u).length := by
    simpa only [slotOf] using terminal
  have allOpen : (plasmaSeq u).all (fun p =>
      u.toList.idxOf p < u.toList.idxOf s) = true := by
    rw [List.all_eq_true]
    intro p pMem
    by_cases pass : u.toList.idxOf p < u.toList.idxOf s
    · exact decide_eq_true pass
    · have fail := decide_eq_false pass
      exact False.elim
        ((takeWhile_ne_length_of_fail pMem fail) lengthEq)
  rw [List.all_eq_false] at afterFalse
  obtain ⟨p, pMem, pFail⟩ := afterFalse
  have pIn : p ∈ u.toList := mem_toList_of_mem_plasmaSeq pMem
  have pNe : p ≠ s := by
    intro equal
    have big := (List.mem_filter.mp pMem).2
    rw [equal] at big
    have two : 2 ≤ u.toList.count s := by
      simpa [plasmaSeq] using big
    have one : u.toList.count s = 1 := single
    omega
  have openBefore : u.toList.idxOf p < u.toList.idxOf s := by
    rw [List.all_eq_true] at allOpen
    simpa using allOpen p pMem
  have notClosed : ¬ lastIdxOf u.toList p < u.toList.idxOf s := by
    intro closed
    exact pFail (decide_eq_true closed)
  have lastNe := lastIdxOf_ne_idxOf_of_single single pIn pNe
  have stillOpen : u.toList.idxOf s < lastIdxOf u.toList p := by omega
  have insideTrue :
      (decide (u.toList.idxOf p < u.toList.idxOf s) &&
        decide (u.toList.idxOf s < lastIdxOf u.toList p)) = true := by
    rw [decide_eq_true openBefore, decide_eq_true stillOpen]
    rfl
  rw [List.any_eq_false] at insideFalse
  exact (insideFalse p pMem) insideTrue

/-- Slot shift under a second-occurrence snoc: singles before the new
letter keep their slot, later ones shift by one. -/
private theorem slotOf_snoc_second {h x : Nat} {T : List Nat}
    (single : List.count x (h :: T) = 1) {s : Nat}
    (sMem : s ∈ h :: T) (sNe : s ≠ x) :
    slotOf (⟨h, T ++ [x]⟩ : Word Nat) s =
      if (h :: T).idxOf s < (h :: T).idxOf x then
        slotOf (⟨h, T⟩ : Word Nat) s
      else slotOf (⟨h, T⟩ : Word Nat) s + 1 := by
  have xMem : x ∈ h :: T := List.count_pos_iff.mp (by omega)
  have memInsert : ∀ p, p ∈ (plasmaSeq (⟨h, T⟩ : Word Nat)).take
      (slotOf (⟨h, T⟩ : Word Nat) x) ++
      x :: (plasmaSeq (⟨h, T⟩ : Word Nat)).drop
        (slotOf (⟨h, T⟩ : Word Nat) x) → p ∈ h :: T := by
    intro p pMem
    rcases List.mem_append.mp pMem with inTake | inCons
    · exact mem_toList_of_mem_plasmaSeq (List.mem_of_mem_take inTake)
    · rcases List.mem_cons.mp inCons with hit | inDrop
      · exact hit ▸ xMem
      · exact mem_toList_of_mem_plasmaSeq (List.mem_of_mem_drop inDrop)
  have pw' : List.Pairwise (fun a b =>
      ((h :: T) ++ [x]).idxOf a < ((h :: T) ++ [x]).idxOf b)
      (plasmaSeq (⟨h, T ++ [x]⟩ : Word Nat)) :=
    List.Pairwise.filter _ (eraseDups_pairwise_idxOf ((h :: T) ++ [x]))
  rw [plasmaSeq_snoc_second single] at pw'
  rw [List.pairwise_append] at pw'
  obtain ⟨_, pwXD, cross⟩ := pw'
  rw [List.pairwise_cons] at pwXD
  obtain ⟨xVsDrop, _⟩ := pwXD
  have takeVsX : ∀ a, a ∈ (plasmaSeq (⟨h, T⟩ : Word Nat)).take
      (slotOf (⟨h, T⟩ : Word Nat) x) →
      (h :: T).idxOf a < (h :: T).idxOf x := by
    intro a aMem
    have := cross a aMem x List.mem_cons_self
    have aIn : a ∈ h :: T :=
      mem_toList_of_mem_plasmaSeq (List.mem_of_mem_take aMem)
    rw [idxOf_append_of_mem aIn x, idxOf_append_of_mem xMem x] at this
    exact this
  have dropVsX : ∀ b, b ∈ (plasmaSeq (⟨h, T⟩ : Word Nat)).drop
      (slotOf (⟨h, T⟩ : Word Nat) x) →
      (h :: T).idxOf x < (h :: T).idxOf b := by
    intro b bMem
    have := xVsDrop b bMem
    have bIn : b ∈ h :: T :=
      mem_toList_of_mem_plasmaSeq (List.mem_of_mem_drop bMem)
    rw [idxOf_append_of_mem bIn x, idxOf_append_of_mem xMem x] at this
    exact this
  simp only [slotOf]
  rw [plasmaSeq_snoc_second single]
  have predEq : ∀ p, p ∈ (plasmaSeq (⟨h, T⟩ : Word Nat)).take
      (slotOf (⟨h, T⟩ : Word Nat) x) ++
      x :: (plasmaSeq (⟨h, T⟩ : Word Nat)).drop
        (slotOf (⟨h, T⟩ : Word Nat) x) →
      (decide ((⟨h, T ++ [x]⟩ : Word Nat).toList.idxOf p <
        (⟨h, T ++ [x]⟩ : Word Nat).toList.idxOf s)) =
      (decide ((h :: T).idxOf p < (h :: T).idxOf s)) := by
    intro p pMem
    apply decide_eq_decide.mpr
    have pIn : p ∈ h :: T := memInsert p pMem
    show ((h :: T) ++ [x]).idxOf p < ((h :: T) ++ [x]).idxOf s ↔
      (h :: T).idxOf p < (h :: T).idxOf s
    rw [idxOf_append_of_mem pIn x, idxOf_append_of_mem sMem x]
  rw [takeWhile_congr_mem predEq]
  by_cases sLt : (h :: T).idxOf s < (h :: T).idxOf x
  · rw [if_pos sLt]
    have px : (decide ((h :: T).idxOf x < (h :: T).idxOf s)) =
        false := by
      have : ¬ ((h :: T).idxOf x < (h :: T).idxOf s) := by omega
      simp [this]
    have qFail : ∀ e, e ∈ (plasmaSeq (⟨h, T⟩ : Word Nat)).drop
        (slotOf (⟨h, T⟩ : Word Nat) x) →
        (decide ((h :: T).idxOf e < (h :: T).idxOf s)) = false := by
      intro e eMem
      have := dropVsX e eMem
      have notLt : ¬ ((h :: T).idxOf e < (h :: T).idxOf s) := by omega
      simp [notLt]
    rw [takeWhile_insert_false px qFail, List.take_append_drop]
    rfl
  · rw [if_neg sLt]
    have idxNe : (h :: T).idxOf s ≠ (h :: T).idxOf x :=
      fun equal => sNe (idxOf_inj_local sMem equal)
    have px : (decide ((h :: T).idxOf x < (h :: T).idxOf s)) =
        true := by
      have : (h :: T).idxOf x < (h :: T).idxOf s := by omega
      simp [this]
    have allP : ∀ e, e ∈ (plasmaSeq (⟨h, T⟩ : Word Nat)).take
        (slotOf (⟨h, T⟩ : Word Nat) x) →
        (decide ((h :: T).idxOf e < (h :: T).idxOf s)) = true := by
      intro e eMem
      have := takeVsX e eMem
      have lt : (h :: T).idxOf e < (h :: T).idxOf s := by omega
      simp [lt]
    rw [takeWhile_insert_true px allP, List.take_append_drop]
    rfl

/-- Relation shift, late singles: everything after the new letter's
open becomes inside. -/
private theorem rel4_snoc_second_late {h x : Nat} {T : List Nat}
    (single : List.count x (h :: T) = 1) {s : Nat}
    (sMem : s ∈ h :: T)
    (late : (h :: T).idxOf x < (h :: T).idxOf s) :
    rel4 (⟨h, T ++ [x]⟩ : Word Nat) s = Rel4.inside := by
  have xMem : x ∈ h :: T := List.count_pos_iff.mp (by omega)
  have xInMid : x ∈ (plasmaSeq (⟨h, T⟩ : Word Nat)).take
      (slotOf (⟨h, T⟩ : Word Nat) x) ++
      x :: (plasmaSeq (⟨h, T⟩ : Word Nat)).drop
        (slotOf (⟨h, T⟩ : Word Nat) x) := by
    apply List.mem_append.mpr
    exact Or.inr List.mem_cons_self
  have idxS : ((h :: T) ++ [x]).idxOf s = (h :: T).idxOf s :=
    idxOf_append_of_mem sMem x
  have idxX : ((h :: T) ++ [x]).idxOf x = (h :: T).idxOf x :=
    idxOf_append_of_mem xMem x
  have lastX : lastIdxOf ((h :: T) ++ [x]) x = (h :: T).length :=
    lastIdxOf_append_self (h :: T) x
  have sBound : (h :: T).idxOf s < (h :: T).length :=
    idxOf_lt_length_of_mem_local sMem
  simp only [rel4]
  rw [plasmaSeq_snoc_second single]
  have c1 : ((plasmaSeq (⟨h, T⟩ : Word Nat)).take
      (slotOf (⟨h, T⟩ : Word Nat) x) ++
      x :: (plasmaSeq (⟨h, T⟩ : Word Nat)).drop
        (slotOf (⟨h, T⟩ : Word Nat) x)).all
      (fun p => (⟨h, T ++ [x]⟩ : Word Nat).toList.idxOf s <
        (⟨h, T ++ [x]⟩ : Word Nat).toList.idxOf p) = false := by
    rw [List.all_eq_false]
    refine ⟨x, xInMid, ?_⟩
    show ¬ (decide (((h :: T) ++ [x]).idxOf s <
      ((h :: T) ++ [x]).idxOf x)) = true
    rw [idxS, idxX]
    have notLt : ¬ ((h :: T).idxOf s < (h :: T).idxOf x) := by omega
    rw [decide_eq_false notLt]
    simp
  have c2 : ((plasmaSeq (⟨h, T⟩ : Word Nat)).take
      (slotOf (⟨h, T⟩ : Word Nat) x) ++
      x :: (plasmaSeq (⟨h, T⟩ : Word Nat)).drop
        (slotOf (⟨h, T⟩ : Word Nat) x)).all
      (fun p => lastIdxOf (⟨h, T ++ [x]⟩ : Word Nat).toList p <
        (⟨h, T ++ [x]⟩ : Word Nat).toList.idxOf s) = false := by
    rw [List.all_eq_false]
    refine ⟨x, xInMid, ?_⟩
    show ¬ (decide (lastIdxOf ((h :: T) ++ [x]) x <
      ((h :: T) ++ [x]).idxOf s)) = true
    rw [lastX, idxS]
    have notLt : ¬ ((h :: T).length < (h :: T).idxOf s) := by omega
    rw [decide_eq_false notLt]
    simp
  have c3 : ((plasmaSeq (⟨h, T⟩ : Word Nat)).take
      (slotOf (⟨h, T⟩ : Word Nat) x) ++
      x :: (plasmaSeq (⟨h, T⟩ : Word Nat)).drop
        (slotOf (⟨h, T⟩ : Word Nat) x)).any
      (fun p => (⟨h, T ++ [x]⟩ : Word Nat).toList.idxOf p <
          (⟨h, T ++ [x]⟩ : Word Nat).toList.idxOf s &&
        ((⟨h, T ++ [x]⟩ : Word Nat).toList.idxOf s <
          lastIdxOf (⟨h, T ++ [x]⟩ : Word Nat).toList p)) = true := by
    rw [List.any_eq_true]
    refine ⟨x, xInMid, ?_⟩
    show (decide (((h :: T) ++ [x]).idxOf x <
        ((h :: T) ++ [x]).idxOf s) &&
      decide (((h :: T) ++ [x]).idxOf s <
        lastIdxOf ((h :: T) ++ [x]) x)) = true
    rw [idxS, idxX, lastX]
    rw [decide_eq_true late, decide_eq_true sBound]
    rfl
  rw [c1, c2, c3]
  simp

/-- Relation shift, early singles: after collapses to gap, the other
three relations survive. -/
private theorem rel4_snoc_second_early {h x : Nat} {T : List Nat}
    (single : List.count x (h :: T) = 1) {s : Nat}
    (sMem : s ∈ h :: T)
    (early : (h :: T).idxOf s < (h :: T).idxOf x) :
    rel4 (⟨h, T ++ [x]⟩ : Word Nat) s =
      if rel4 (⟨h, T⟩ : Word Nat) s = Rel4.after then Rel4.gap
      else rel4 (⟨h, T⟩ : Word Nat) s := by
  have xMem : x ∈ h :: T := List.count_pos_iff.mp (by omega)
  have idxS : ((h :: T) ++ [x]).idxOf s = (h :: T).idxOf s :=
    idxOf_append_of_mem sMem x
  have idxX : ((h :: T) ++ [x]).idxOf x = (h :: T).idxOf x :=
    idxOf_append_of_mem xMem x
  have lastX : lastIdxOf ((h :: T) ++ [x]) x = (h :: T).length :=
    lastIdxOf_append_self (h :: T) x
  have sBound : (h :: T).idxOf s < (h :: T).length :=
    idxOf_lt_length_of_mem_local sMem
  have plasmaNe : ∀ p, p ∈ plasmaSeq (⟨h, T⟩ : Word Nat) → p ≠ x := by
    intro p pMem equal
    have big := (List.mem_filter.mp pMem).2
    rw [equal] at big
    have : 2 ≤ List.count x (h :: T) := by simpa using big
    omega
  have memPseq : ∀ p, p ∈ (plasmaSeq (⟨h, T⟩ : Word Nat)).take
      (slotOf (⟨h, T⟩ : Word Nat) x) ++
      x :: (plasmaSeq (⟨h, T⟩ : Word Nat)).drop
        (slotOf (⟨h, T⟩ : Word Nat) x) →
      p = x ∨ p ∈ plasmaSeq (⟨h, T⟩ : Word Nat) := by
    intro p pMem
    rcases List.mem_append.mp pMem with inTake | inCons
    · exact Or.inr (List.mem_of_mem_take inTake)
    · rcases List.mem_cons.mp inCons with hit | inDrop
      · exact Or.inl hit
      · exact Or.inr (List.mem_of_mem_drop inDrop)
  simp only [rel4]
  rw [plasmaSeq_snoc_second single]
  -- condition 1: before-condition transfers
  have e1 : ((plasmaSeq (⟨h, T⟩ : Word Nat)).take
      (slotOf (⟨h, T⟩ : Word Nat) x) ++
      x :: (plasmaSeq (⟨h, T⟩ : Word Nat)).drop
        (slotOf (⟨h, T⟩ : Word Nat) x)).all
      (fun p => (⟨h, T ++ [x]⟩ : Word Nat).toList.idxOf s <
        (⟨h, T ++ [x]⟩ : Word Nat).toList.idxOf p) =
      (plasmaSeq (⟨h, T⟩ : Word Nat)).all
      (fun p => (⟨h, T⟩ : Word Nat).toList.idxOf s <
        (⟨h, T⟩ : Word Nat).toList.idxOf p) := by
    have step : ((plasmaSeq (⟨h, T⟩ : Word Nat)).take
        (slotOf (⟨h, T⟩ : Word Nat) x) ++
        x :: (plasmaSeq (⟨h, T⟩ : Word Nat)).drop
          (slotOf (⟨h, T⟩ : Word Nat) x)).all
        (fun p => (⟨h, T ++ [x]⟩ : Word Nat).toList.idxOf s <
          (⟨h, T ++ [x]⟩ : Word Nat).toList.idxOf p) =
        ((plasmaSeq (⟨h, T⟩ : Word Nat)).take
        (slotOf (⟨h, T⟩ : Word Nat) x) ++
        x :: (plasmaSeq (⟨h, T⟩ : Word Nat)).drop
          (slotOf (⟨h, T⟩ : Word Nat) x)).all
        (fun p => (⟨h, T⟩ : Word Nat).toList.idxOf s <
          (⟨h, T⟩ : Word Nat).toList.idxOf p) := by
      apply all_congr_mem
      intro p pMem
      apply decide_eq_decide.mpr
      rcases memPseq p pMem with hit | inPseq
      · show ((h :: T) ++ [x]).idxOf s < ((h :: T) ++ [x]).idxOf p ↔
          (h :: T).idxOf s < (h :: T).idxOf p
        rw [hit, idxS, idxX]
      · have pIn : p ∈ h :: T := mem_toList_of_mem_plasmaSeq inPseq
        show ((h :: T) ++ [x]).idxOf s < ((h :: T) ++ [x]).idxOf p ↔
          (h :: T).idxOf s < (h :: T).idxOf p
        rw [idxS, idxOf_append_of_mem pIn x]
    rw [step, List.all_append, List.all_cons]
    have px : (decide ((⟨h, T⟩ : Word Nat).toList.idxOf s <
        (⟨h, T⟩ : Word Nat).toList.idxOf x)) = true :=
      decide_eq_true early
    rw [px, Bool.true_and, ← List.all_append, List.take_append_drop]
  -- condition 2: after-condition dies at the new letter
  have e2 : ((plasmaSeq (⟨h, T⟩ : Word Nat)).take
      (slotOf (⟨h, T⟩ : Word Nat) x) ++
      x :: (plasmaSeq (⟨h, T⟩ : Word Nat)).drop
        (slotOf (⟨h, T⟩ : Word Nat) x)).all
      (fun p => lastIdxOf (⟨h, T ++ [x]⟩ : Word Nat).toList p <
        (⟨h, T ++ [x]⟩ : Word Nat).toList.idxOf s) = false := by
    rw [List.all_eq_false]
    refine ⟨x, List.mem_append.mpr (Or.inr List.mem_cons_self), ?_⟩
    show ¬ (decide (lastIdxOf ((h :: T) ++ [x]) x <
      ((h :: T) ++ [x]).idxOf s)) = true
    rw [lastX, idxS]
    rw [decide_eq_false (by omega :
      ¬ ((h :: T).length < (h :: T).idxOf s))]
    simp
  -- condition 3: inside-condition transfers
  have e3 : ((plasmaSeq (⟨h, T⟩ : Word Nat)).take
      (slotOf (⟨h, T⟩ : Word Nat) x) ++
      x :: (plasmaSeq (⟨h, T⟩ : Word Nat)).drop
        (slotOf (⟨h, T⟩ : Word Nat) x)).any
      (fun p => (⟨h, T ++ [x]⟩ : Word Nat).toList.idxOf p <
          (⟨h, T ++ [x]⟩ : Word Nat).toList.idxOf s &&
        ((⟨h, T ++ [x]⟩ : Word Nat).toList.idxOf s <
          lastIdxOf (⟨h, T ++ [x]⟩ : Word Nat).toList p)) =
      (plasmaSeq (⟨h, T⟩ : Word Nat)).any
      (fun p => (⟨h, T⟩ : Word Nat).toList.idxOf p <
          (⟨h, T⟩ : Word Nat).toList.idxOf s &&
        ((⟨h, T⟩ : Word Nat).toList.idxOf s <
          lastIdxOf (⟨h, T⟩ : Word Nat).toList p)) := by
    rw [List.any_append, List.any_cons]
    have px : (decide (((h :: T) ++ [x]).idxOf x <
        ((h :: T) ++ [x]).idxOf s) &&
        decide (((h :: T) ++ [x]).idxOf s <
          lastIdxOf ((h :: T) ++ [x]) x)) = false := by
      rw [idxS, idxX,
        decide_eq_false (by omega :
          ¬ ((h :: T).idxOf x < (h :: T).idxOf s))]
      rfl
    have pxT : (((⟨h, T ++ [x]⟩ : Word Nat).toList.idxOf x <
        (⟨h, T ++ [x]⟩ : Word Nat).toList.idxOf s :
        Bool) &&
        ((⟨h, T ++ [x]⟩ : Word Nat).toList.idxOf s <
          lastIdxOf (⟨h, T ++ [x]⟩ : Word Nat).toList x)) = false := px
    rw [pxT, Bool.false_or, ← List.any_append, List.take_append_drop]
    apply any_congr_mem
    intro p pMem
    have inPseq := pMem
    have pIn : p ∈ h :: T := mem_toList_of_mem_plasmaSeq inPseq
    have pNe : p ≠ x := plasmaNe p inPseq
    show ((decide (((h :: T) ++ [x]).idxOf p <
        ((h :: T) ++ [x]).idxOf s)) &&
      (decide (((h :: T) ++ [x]).idxOf s <
        lastIdxOf ((h :: T) ++ [x]) p))) =
      ((decide ((h :: T).idxOf p < (h :: T).idxOf s)) &&
      (decide ((h :: T).idxOf s < lastIdxOf (h :: T) p)))
    rw [idxS, idxOf_append_of_mem pIn x, lastIdxOf_append_ne pIn pNe]
  rw [e1, e2, e3]
  -- old after forces old inside false
  by_cases vB : (plasmaSeq (⟨h, T⟩ : Word Nat)).all
      (fun p => (⟨h, T⟩ : Word Nat).toList.idxOf s <
        (⟨h, T⟩ : Word Nat).toList.idxOf p) = true
  · rw [vB]
    simp
  · have vBf := Bool.eq_false_iff.mpr vB
    rw [vBf]
    by_cases vA : (plasmaSeq (⟨h, T⟩ : Word Nat)).all
        (fun p => lastIdxOf (⟨h, T⟩ : Word Nat).toList p <
          (⟨h, T⟩ : Word Nat).toList.idxOf s) = true
    · have vI : (plasmaSeq (⟨h, T⟩ : Word Nat)).any
          (fun p => (⟨h, T⟩ : Word Nat).toList.idxOf p <
              (⟨h, T⟩ : Word Nat).toList.idxOf s &&
            ((⟨h, T⟩ : Word Nat).toList.idxOf s <
              lastIdxOf (⟨h, T⟩ : Word Nat).toList p)) = false := by
        rw [List.any_eq_false]
        intro p pMem
        rw [List.all_eq_true] at vA
        have below := vA p pMem
        have belowP : lastIdxOf (⟨h, T⟩ : Word Nat).toList p <
            (⟨h, T⟩ : Word Nat).toList.idxOf s := by
          simpa using below
        have notLt : ¬ ((⟨h, T⟩ : Word Nat).toList.idxOf s <
            lastIdxOf (⟨h, T⟩ : Word Nat).toList p) := by omega
        rw [decide_eq_false notLt, Bool.and_false]
        simp
      rw [vA, vI]
      simp
    · have vAf := Bool.eq_false_iff.mpr vA
      rw [vAf]
      by_cases vI : (plasmaSeq (⟨h, T⟩ : Word Nat)).any
          (fun p => (⟨h, T⟩ : Word Nat).toList.idxOf p <
              (⟨h, T⟩ : Word Nat).toList.idxOf s &&
            ((⟨h, T⟩ : Word Nat).toList.idxOf s <
              lastIdxOf (⟨h, T⟩ : Word Nat).toList p)) = true
      · rw [vI]
        simp
      · rw [Bool.eq_false_iff.mpr vI]
        simp

/-- Before-open lists of late singles are unchanged by the second
occurrence (the new plasma letter opens before them). -/
private theorem beforeOpenList_snoc_second_late {h x : Nat}
    {T : List Nat} (single : List.count x (h :: T) = 1) {s : Nat}
    (sMem : s ∈ h :: T)
    (late : (h :: T).idxOf x < (h :: T).idxOf s) :
    beforeOpenList (⟨h, T ++ [x]⟩ : Word Nat) s =
      beforeOpenList (⟨h, T⟩ : Word Nat) s := by
  have xMem : x ∈ h :: T := List.count_pos_iff.mp (by omega)
  have idxS : ((h :: T) ++ [x]).idxOf s = (h :: T).idxOf s :=
    idxOf_append_of_mem sMem x
  have idxX : ((h :: T) ++ [x]).idxOf x = (h :: T).idxOf x :=
    idxOf_append_of_mem xMem x
  simp only [beforeOpenList]
  rw [plasmaSeq_snoc_second single, List.filter_append,
    List.filter_cons]
  have xFail : (decide ((⟨h, T ++ [x]⟩ : Word Nat).toList.idxOf s <
      (⟨h, T ++ [x]⟩ : Word Nat).toList.idxOf x)) = false := by
    show (decide (((h :: T) ++ [x]).idxOf s <
      ((h :: T) ++ [x]).idxOf x)) = false
    rw [idxS, idxX]
    exact decide_eq_false (by omega)
  rw [xFail]
  simp only [Bool.false_eq_true, if_false]
  rw [← List.filter_append, List.take_append_drop]
  apply filter_congr_mem
  intro p pMem
  have pIn : p ∈ h :: T := mem_toList_of_mem_plasmaSeq pMem
  apply decide_eq_decide.mpr
  show ((h :: T) ++ [x]).idxOf s < ((h :: T) ++ [x]).idxOf p ↔
    (h :: T).idxOf s < (h :: T).idxOf p
  rw [idxS, idxOf_append_of_mem pIn x]

/-- Before-open decompositions for early singles: the new letter and
every later plasma open after the single. -/
private theorem beforeOpenList_snoc_second_early {h x : Nat}
    {T : List Nat} (single : List.count x (h :: T) = 1) {s : Nat}
    (sMem : s ∈ h :: T)
    (early : (h :: T).idxOf s < (h :: T).idxOf x) :
    beforeOpenList (⟨h, T ++ [x]⟩ : Word Nat) s =
      ((plasmaSeq (⟨h, T⟩ : Word Nat)).take
        (slotOf (⟨h, T⟩ : Word Nat) x)).filter
        (fun p => (h :: T).idxOf s < (h :: T).idxOf p) ++
      x :: (plasmaSeq (⟨h, T⟩ : Word Nat)).drop
        (slotOf (⟨h, T⟩ : Word Nat) x) ∧
    beforeOpenList (⟨h, T⟩ : Word Nat) s =
      ((plasmaSeq (⟨h, T⟩ : Word Nat)).take
        (slotOf (⟨h, T⟩ : Word Nat) x)).filter
        (fun p => (h :: T).idxOf s < (h :: T).idxOf p) ++
      (plasmaSeq (⟨h, T⟩ : Word Nat)).drop
        (slotOf (⟨h, T⟩ : Word Nat) x) := by
  have xMem : x ∈ h :: T := List.count_pos_iff.mp (by omega)
  have idxS : ((h :: T) ++ [x]).idxOf s = (h :: T).idxOf s :=
    idxOf_append_of_mem sMem x
  have idxX : ((h :: T) ++ [x]).idxOf x = (h :: T).idxOf x :=
    idxOf_append_of_mem xMem x
  have pw' : List.Pairwise (fun a b =>
      ((h :: T) ++ [x]).idxOf a < ((h :: T) ++ [x]).idxOf b)
      (plasmaSeq (⟨h, T ++ [x]⟩ : Word Nat)) :=
    List.Pairwise.filter _ (eraseDups_pairwise_idxOf ((h :: T) ++ [x]))
  rw [plasmaSeq_snoc_second single, List.pairwise_append] at pw'
  obtain ⟨_, pwXD, _⟩ := pw'
  rw [List.pairwise_cons] at pwXD
  obtain ⟨xVsDrop, _⟩ := pwXD
  have dropPass : ∀ e, e ∈ (plasmaSeq (⟨h, T⟩ : Word Nat)).drop
      (slotOf (⟨h, T⟩ : Word Nat) x) →
      (h :: T).idxOf s < (h :: T).idxOf e := by
    intro e eMem
    have := xVsDrop e eMem
    have eIn : e ∈ h :: T :=
      mem_toList_of_mem_plasmaSeq (List.mem_of_mem_drop eMem)
    rw [idxOf_append_of_mem eIn x, idxOf_append_of_mem xMem x] at this
    omega
  constructor
  · simp only [beforeOpenList]
    rw [plasmaSeq_snoc_second single, List.filter_append,
      List.filter_cons]
    have xPass : (decide ((⟨h, T ++ [x]⟩ : Word Nat).toList.idxOf s <
        (⟨h, T ++ [x]⟩ : Word Nat).toList.idxOf x)) = true := by
      show (decide (((h :: T) ++ [x]).idxOf s <
        ((h :: T) ++ [x]).idxOf x)) = true
      rw [idxS, idxX]
      exact decide_eq_true early
    rw [xPass]
    simp only [if_true]
    congr 1
    · apply filter_congr_mem
      intro p pMem
      have pIn : p ∈ h :: T :=
        mem_toList_of_mem_plasmaSeq (List.mem_of_mem_take pMem)
      apply decide_eq_decide.mpr
      show ((h :: T) ++ [x]).idxOf s < ((h :: T) ++ [x]).idxOf p ↔
        (h :: T).idxOf s < (h :: T).idxOf p
      rw [idxS, idxOf_append_of_mem pIn x]
    · congr 1
      rw [List.filter_eq_self]
      intro e eMem
      have eIn : e ∈ h :: T :=
        mem_toList_of_mem_plasmaSeq (List.mem_of_mem_drop eMem)
      show (decide (((h :: T) ++ [x]).idxOf s <
        ((h :: T) ++ [x]).idxOf e)) = true
      rw [idxS, idxOf_append_of_mem eIn x]
      exact decide_eq_true (dropPass e eMem)
  · simp only [beforeOpenList]
    have chain : ((plasmaSeq (⟨h, T⟩ : Word Nat)).take
          (slotOf (⟨h, T⟩ : Word Nat) x)).filter
          (fun p => (⟨h, T⟩ : Word Nat).toList.idxOf s <
            (⟨h, T⟩ : Word Nat).toList.idxOf p) ++
        ((plasmaSeq (⟨h, T⟩ : Word Nat)).drop
          (slotOf (⟨h, T⟩ : Word Nat) x)).filter
          (fun p => (⟨h, T⟩ : Word Nat).toList.idxOf s <
            (⟨h, T⟩ : Word Nat).toList.idxOf p) =
        (plasmaSeq (⟨h, T⟩ : Word Nat)).filter
          (fun p => (⟨h, T⟩ : Word Nat).toList.idxOf s <
            (⟨h, T⟩ : Word Nat).toList.idxOf p) := by
      rw [← List.filter_append, List.take_append_drop]
    rw [← chain]
    have dropSelf : ((plasmaSeq (⟨h, T⟩ : Word Nat)).drop
        (slotOf (⟨h, T⟩ : Word Nat) x)).filter
        (fun p => (⟨h, T⟩ : Word Nat).toList.idxOf s <
          (⟨h, T⟩ : Word Nat).toList.idxOf p) =
        (plasmaSeq (⟨h, T⟩ : Word Nat)).drop
          (slotOf (⟨h, T⟩ : Word Nat) x) := by
      rw [List.filter_eq_self]
      intro e eMem
      show (decide ((h :: T).idxOf s < (h :: T).idxOf e)) = true
      exact decide_eq_true (dropPass e eMem)
    rw [dropSelf]
    rfl

/-- A single head letter leads the singles sequence. -/
private theorem singlesSeq_head_single {h : Nat} {T : List Nat}
    (single : List.count h (h :: T) = 1) :
    singlesSeq (⟨h, T⟩ : Word Nat) =
      h :: T.filter (fun c => (h :: T).count c == 1) := by
  simp only [singlesSeq, toList_mk]
  rw [List.filter_cons]
  have pass : ((h :: T).count h == 1) = true := by
    rw [single]
    rfl
  rw [pass]
  simp

/-- A letter of count one never repeats inside the singles sequence
tail. -/
private theorem head_not_in_singles_tail {h : Nat} {T : List Nat}
    (single : List.count h (h :: T) = 1) :
    h ∉ T.filter (fun c => (h :: T).count c == 1) := by
  intro member
  have inT : h ∈ T := (List.mem_filter.mp member).1
  have posT : 0 < List.count h T := List.count_pos_iff.mpr inT
  have expand : List.count h (h :: T) = List.count h T + 1 :=
    List.count_cons_self
  omega

/-- If the head is not the first single, it is not single at all. -/
private theorem head_first_single {h : Nat} {T : List Nat} {s0 : Nat}
    {rest : List Nat}
    (shape : singlesSeq (⟨h, T⟩ : Word Nat) = s0 :: rest)
    (ne : s0 ≠ h) : h ∉ singlesSeq (⟨h, T⟩ : Word Nat) := by
  intro member
  have hSingle : List.count h (h :: T) = 1 := by
    have raw := (List.mem_filter.mp member).2
    have beq : ((h :: T).count h == 1) = true := raw
    exact eq_of_beq beq
  have expand := singlesSeq_head_single hSingle
  rw [shape] at expand
  injection expand with headEq _
  exact ne headEq

/-- Filtering never raises a count. -/
private theorem count_filter_le_local (a : Nat) (p : Nat → Bool)
    (l : List Nat) : (l.filter p).count a ≤ l.count a := by
  induction l with
  | nil => simp
  | cons b t ih =>
      rw [List.filter_cons]
      by_cases pb : p b = true
      · rw [pb]
        simp only [if_true]
        simp [List.count_cons]
        omega
      · have pbF : p b = false := by
          cases v : p b
          · rfl
          · exact absurd v pb
        rw [pbF]
        simp only [Bool.false_eq_true, if_false]
        simp [List.count_cons]
        omega

/-- Second occurrence: the stripped singles lose the letter. -/
private theorem strippedSingles_snoc_second {h x : Nat} {T : List Nat}
    (single : List.count x (h :: T) = 1) :
    strippedSingles (⟨h, T ++ [x]⟩ : Word Nat) =
      (strippedSingles (⟨h, T⟩ : Word Nat)).filter
        (fun e => !(e == x)) := by
  have singlesEq := singlesSeq_snoc_second (h := h) (T := T) single
  by_cases hx : h = x
  · -- the head itself gains its second occurrence
    subst hx
    have shape := singlesSeq_head_single single
    have notInRest := head_not_in_singles_tail single
    have restSelf : (T.filter
        (fun c => (h :: T).count c == 1)).filter
        (fun e => !(e == h)) =
        T.filter (fun c => (h :: T).count c == 1) := by
      rw [List.filter_eq_self]
      intro e eMem
      have ne : e ≠ h := fun equal => notInRest (equal ▸ eMem)
      simp [ne]
    have newSingles : singlesSeq (⟨h, T ++ [h]⟩ : Word Nat) =
        T.filter (fun c => (h :: T).count c == 1) := by
      rw [singlesEq, shape, List.filter_cons]
      simp only [BEq.rfl, Bool.not_true, Bool.false_eq_true, if_false]
      exact restSelf
    simp only [strippedSingles]
    rw [newSingles, shape]
    -- old condition: head-single strip fires
    have oldCond : (decide (List.take 1
        (h :: T.filter (fun c => (h :: T).count c == 1)) =
        [(⟨h, T⟩ : Word Nat).head]) &&
        !decide (IsPlasma (⟨h, T⟩ : Word Nat)
          (⟨h, T⟩ : Word Nat).head)) = true := by
      have takeOk : decide (List.take 1
          (h :: T.filter (fun c => (h :: T).count c == 1)) =
          [(⟨h, T⟩ : Word Nat).head]) = true := by
        apply decide_eq_true
        rfl
      have plasmaNo : decide (IsPlasma (⟨h, T⟩ : Word Nat)
          (⟨h, T⟩ : Word Nat).head) = false := by
        apply decide_eq_false
        intro plasma
        have big : 2 ≤ List.count h (h :: T) := plasma
        omega
      rw [takeOk, plasmaNo]
      rfl
    -- new condition: the head is no longer in the singles
    have newCond : (decide (List.take 1
        (T.filter (fun c => (h :: T).count c == 1)) =
        [(⟨h, T ++ [h]⟩ : Word Nat).head]) &&
        !decide (IsPlasma (⟨h, T ++ [h]⟩ : Word Nat)
          (⟨h, T ++ [h]⟩ : Word Nat).head)) = false := by
      have takeNo : decide (List.take 1
          (T.filter (fun c => (h :: T).count c == 1)) =
          [(⟨h, T ++ [h]⟩ : Word Nat).head]) = false := by
        apply decide_eq_false
        intro equal
        cases restShape : T.filter (fun c => (h :: T).count c == 1) with
        | nil =>
            rw [restShape] at equal
            cases equal
        | cons r0 rest =>
            rw [restShape] at equal
            simp at equal
            exact notInRest (restShape ▸ (equal ▸ List.mem_cons_self))
      rw [takeNo]
      rfl
    rw [oldCond, newCond]
    simp only [if_true, Bool.false_eq_true, if_false]
    exact restSelf.symm
  · -- an ordinary single gains its second occurrence
    have headNe : (⟨h, T ++ [x]⟩ : Word Nat).head =
        (⟨h, T⟩ : Word Nat).head := rfl
    have plasmaEq : decide (IsPlasma (⟨h, T ++ [x]⟩ : Word Nat)
        (⟨h, T ++ [x]⟩ : Word Nat).head) =
        decide (IsPlasma (⟨h, T⟩ : Word Nat)
          (⟨h, T⟩ : Word Nat).head) := by
      apply decide_eq_decide.mpr
      simp only [IsPlasma, letterCount]
      have countEq : (⟨h, T ++ [x]⟩ : Word Nat).toList.count h =
          (⟨h, T⟩ : Word Nat).toList.count h := by
        show ((h :: T) ++ [x]).count h = (h :: T).count h
        exact count_append_ne hx
      rw [countEq]
    simp only [strippedSingles, singlesEq, plasmaEq, headNe]
    cases sShape : singlesSeq (⟨h, T⟩ : Word Nat) with
    | nil => simp
    | cons s0 rest =>
        by_cases s0x : s0 = x
        · -- the dropped single led the sequence; the head was not
          -- single, so neither condition fires
          have hNotSingle : h ∉ singlesSeq (⟨h, T⟩ : Word Nat) :=
            head_first_single sShape (s0x ▸ fun equal => hx equal.symm)
          have xNotInRest : x ∉ rest := by
            intro member
            have nodupCount : List.count x
                (singlesSeq (⟨h, T⟩ : Word Nat)) ≤ 1 := by
              have subCount : List.count x
                  (singlesSeq (⟨h, T⟩ : Word Nat)) ≤
                  List.count x (h :: T) := by
                simp only [singlesSeq, toList_mk]
                exact count_filter_le_local x _ (h :: T)
              omega
            rw [sShape, s0x, List.count_cons_self] at nodupCount
            have : 0 < List.count x rest :=
              List.count_pos_iff.mpr member
            omega
          have restSelf : rest.filter (fun e => !(e == x)) = rest := by
            rw [List.filter_eq_self]
            intro e eMem
            have ne : e ≠ x := fun equal => xNotInRest (equal ▸ eMem)
            simp [ne]
          rw [List.filter_cons]
          have s0Gone : (!(s0 == x)) = false := by
            rw [s0x]
            simp
          rw [s0Gone]
          simp only [Bool.false_eq_true, if_false]
          rw [restSelf]
          -- old take is [s0] ≠ [h]; new take is rest's head ∉ {h}
          have oldTake : decide (List.take 1 (s0 :: rest) =
              [(⟨h, T⟩ : Word Nat).head]) = false := by
            apply decide_eq_false
            intro equal
            simp at equal
            exact hx (equal ▸ s0x)
          have newTake : decide (List.take 1 rest =
              [(⟨h, T⟩ : Word Nat).head]) = false := by
            apply decide_eq_false
            intro equal
            cases restShape : rest with
            | nil =>
                rw [restShape] at equal
                cases equal
            | cons r0 rest' =>
                rw [restShape] at equal
                simp at equal
                exact hNotSingle (sShape ▸ List.mem_cons_of_mem _
                  (restShape ▸ (equal ▸ List.mem_cons_self)))
          rw [oldTake, newTake]
          simp only [Bool.false_and, Bool.false_eq_true, if_false]
          rw [List.filter_cons, s0Gone]
          simp only [Bool.false_eq_true, if_false]
          exact restSelf.symm
        · -- the surviving first single keeps both conditions aligned
          have takeEq : decide (List.take 1
              ((s0 :: rest).filter (fun e => !(e == x))) =
              [(⟨h, T⟩ : Word Nat).head]) =
              decide (List.take 1 (s0 :: rest) =
                [(⟨h, T⟩ : Word Nat).head]) := by
            rw [List.filter_cons]
            have keep : (!(s0 == x)) = true := by
              simp [s0x]
            rw [keep]
            simp
          rw [takeEq]
          by_cases cond : (decide (List.take 1 (s0 :: rest) =
              [(⟨h, T⟩ : Word Nat).head]) &&
              !decide (IsPlasma (⟨h, T⟩ : Word Nat)
                (⟨h, T⟩ : Word Nat).head)) = true
          · rw [if_pos cond, if_pos cond]
            rw [List.filter_cons]
            have keep : (!(s0 == x)) = true := by
              simp [s0x]
            rw [keep]
            simp
          · rw [if_neg cond, if_neg cond]

/-! ## The shifted components (formula F, oracle-certified 3207/3207) -/

/-- Shifted slot: early singles keep, late singles move up one. -/
private def slotP (u : Word Nat) (x s : Nat) : Nat :=
  if u.toList.idxOf s < u.toList.idxOf x then slotOf u s
  else slotOf u s + 1

/-- Shifted relation: late singles become inside; early after becomes
gap. -/
private def rel4P (u : Word Nat) (x s : Nat) : Rel4 :=
  if u.toList.idxOf s < u.toList.idxOf x then
    (if rel4 u s = Rel4.after then Rel4.gap else rel4 u s)
  else Rel4.inside

/-- Formula F never leaves an after-single: early afters become gaps and
all late singles become inside. -/
private theorem rel4P_beq_after_false (u : Word Nat) (x s : Nat) :
    (rel4P u x s == Rel4.after) = false := by
  by_cases early : u.toList.idxOf s < u.toList.idxOf x
  · rw [rel4P, if_pos early]
    cases relation : rel4 u s <;> simp [relation]
  · rw [rel4P, if_neg early]
    simp

/-- Combined slot-shift law in slotP form. -/
private theorem slotOf_snoc_second' {h x : Nat} {T : List Nat}
    (single : List.count x (h :: T) = 1) {s : Nat}
    (sMem : s ∈ h :: T) (sNe : s ≠ x) :
    slotOf (⟨h, T ++ [x]⟩ : Word Nat) s =
      slotP (⟨h, T⟩ : Word Nat) x s :=
  slotOf_snoc_second single sMem sNe

/-- Combined relation-shift law in rel4P form. -/
private theorem rel4_snoc_second' {h x : Nat} {T : List Nat}
    (single : List.count x (h :: T) = 1) {s : Nat}
    (sMem : s ∈ h :: T) (sNe : s ≠ x) :
    rel4 (⟨h, T ++ [x]⟩ : Word Nat) s =
      rel4P (⟨h, T⟩ : Word Nat) x s := by
  have xMem : x ∈ h :: T := List.count_pos_iff.mp (by omega)
  by_cases early : (⟨h, T⟩ : Word Nat).toList.idxOf s <
      (⟨h, T⟩ : Word Nat).toList.idxOf x
  · rw [rel4P, if_pos early]
    exact rel4_snoc_second_early single sMem early
  · have earlyL : ¬ (h :: T).idxOf s < (h :: T).idxOf x := early
    have idxNe : (h :: T).idxOf s ≠ (h :: T).idxOf x :=
      fun equal => sNe (idxOf_inj_local sMem equal)
    have late : (h :: T).idxOf x < (h :: T).idxOf s := by omega
    rw [rel4P, if_neg early]
    exact rel4_snoc_second_late single sMem late

/-- Shifted stripped singles. -/
private def strippedP (u : Word Nat) (x : Nat) : List Nat :=
  (strippedSingles u).filter (fun e => !(e == x))

/-- Shifted plasma sequence: the letter enters at its slot. -/
private def pseqP (u : Word Nat) (x : Nat) : List Nat :=
  (plasmaSeq u).take (slotOf u x) ++
    x :: (plasmaSeq u).drop (slotOf u x)

/-- Shifted block. -/
private def blockP (u : Word Nat) (x : Nat) (i p : Nat) : List Nat :=
  (if i == 0 && p == u.head then
    ((strippedP u x).filter
      (fun s => slotP u x s == i + 1 &&
        rel4P u x s == Rel4.inside)) ++ [p]
   else
    p :: ((strippedP u x).filter
      (fun s => slotP u x s == i + 1 &&
        rel4P u x s == Rel4.inside)) ++ [p]) ++
  ((strippedP u x).filter
    (fun s => slotP u x s == i + 1 && rel4P u x s == Rel4.gap))

/-- The oracle-certified canonical word of the extended class,
assembled from the base word's shifted components. -/
private def canonicalizeP (u : Word Nat) (x : Nat) : Word Nat :=
  ⟨u.head,
    ((strippedP u x).filter (fun s => slotP u x s == 0)) ++
      (List.range (pseqP u x).length).flatMap
        (fun i => blockP u x i ((pseqP u x).getD i 0)) ++
      ((strippedP u x).filter
        (fun s => slotP u x s == (pseqP u x).length &&
          rel4P u x s == Rel4.after))⟩

/-- Formula F: the canonical word of the second-occurrence extension. -/
private theorem canonicalize_snoc_second {h x : Nat} {T : List Nat}
    (single : List.count x (h :: T) = 1) :
    canonicalize (⟨h, T ++ [x]⟩ : Word Nat) =
      canonicalizeP (⟨h, T⟩ : Word Nat) x := by
  have memData : ∀ s, s ∈ strippedP (⟨h, T⟩ : Word Nat) x →
      s ∈ h :: T ∧ s ≠ x := by
    intro s sMem
    have parts := List.mem_filter.mp sMem
    have sIn : s ∈ h :: T := mem_toList_of_mem_singlesSeq
      (mem_singles_of_mem_stripped parts.1)
    have sNe : s ≠ x := by
      intro equal
      have verdict := parts.2
      rw [equal] at verdict
      simp at verdict
    exact ⟨sIn, sNe⟩
  have predSlot : ∀ (n : Nat) (s : Nat),
      s ∈ strippedP (⟨h, T⟩ : Word Nat) x →
      (slotOf (⟨h, T ++ [x]⟩ : Word Nat) s == n) =
      (slotP (⟨h, T⟩ : Word Nat) x s == n) := by
    intro n s sMem
    obtain ⟨sIn, sNe⟩ := memData s sMem
    rw [slotOf_snoc_second' single sIn sNe]
  have predRel : ∀ (r : Rel4) (s : Nat),
      s ∈ strippedP (⟨h, T⟩ : Word Nat) x →
      (rel4 (⟨h, T ++ [x]⟩ : Word Nat) s == r) =
      (rel4P (⟨h, T⟩ : Word Nat) x s == r) := by
    intro r s sMem
    obtain ⟨sIn, sNe⟩ := memData s sMem
    rw [rel4_snoc_second' single sIn sNe]
  simp only [canonicalize, canonicalizeP, strippedP, pseqP, blockP,
    blockOf]
  rw [strippedSingles_snoc_second single, plasmaSeq_snoc_second single]
  congr 1
  congr 1
  · congr 1
    · apply filter_congr_mem
      intro s sMem
      exact predSlot 0 s sMem
    · apply flatMap_congr_mem
      intro i _
      have insEq : ((strippedSingles (⟨h, T⟩ : Word Nat)).filter
          (fun e => !(e == x))).filter
          (fun s => slotOf (⟨h, T ++ [x]⟩ : Word Nat) s == i + 1 &&
            rel4 (⟨h, T ++ [x]⟩ : Word Nat) s == Rel4.inside) =
          ((strippedSingles (⟨h, T⟩ : Word Nat)).filter
          (fun e => !(e == x))).filter
          (fun s => slotP (⟨h, T⟩ : Word Nat) x s == i + 1 &&
            rel4P (⟨h, T⟩ : Word Nat) x s == Rel4.inside) := by
        apply filter_congr_mem
        intro s sMem
        rw [predSlot (i + 1) s sMem, predRel Rel4.inside s sMem]
      have gapEq : ((strippedSingles (⟨h, T⟩ : Word Nat)).filter
          (fun e => !(e == x))).filter
          (fun s => slotOf (⟨h, T ++ [x]⟩ : Word Nat) s == i + 1 &&
            rel4 (⟨h, T ++ [x]⟩ : Word Nat) s == Rel4.gap) =
          ((strippedSingles (⟨h, T⟩ : Word Nat)).filter
          (fun e => !(e == x))).filter
          (fun s => slotP (⟨h, T⟩ : Word Nat) x s == i + 1 &&
            rel4P (⟨h, T⟩ : Word Nat) x s == Rel4.gap) := by
        apply filter_congr_mem
        intro s sMem
        rw [predSlot (i + 1) s sMem, predRel Rel4.gap s sMem]
      rw [insEq, gapEq]
  · apply filter_congr_mem
    intro s sMem
    rw [predSlot _ s sMem, predRel Rel4.after s sMem]

/-! ## Head-empty macro variants (generated) -/

private theorem macroCrossH (X E P Y Z : Word Nat) :
    Derives basis (X ++ (E ++ (P ++ (Y ++ (P ++ (Z ++ X))))))
      (X ++ (E ++ (X ++ (P ++ (Y ++ (Z ++ P)))))) := by
  have step0 : Derives basis (X ++ (E ++ (P ++ (Y ++ (P ++ (Z ++ X))))))
      (X ++ (E ++ (P ++ (P ++ (Y ++ (P ++ (Z ++ X))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend (X ++ E) (derivesLeftDuplication P Y)) (Z ++ X))
  have step1 : Derives basis (X ++ (E ++ (P ++ (P ++ (Y ++ (P ++ (Z ++ X)))))))
      (X ++ (E ++ (X ++ (P ++ (P ++ (Y ++ (P ++ (Z ++ X)))))))) := by
    simpa [Word.append_assoc] using (derivesMiddleReduplication X E (P ++ (P ++ (Y ++ (P ++ Z)))))
  have step2 : Derives basis (X ++ (E ++ (X ++ (P ++ (P ++ (Y ++ (P ++ (Z ++ X))))))))
      (X ++ (E ++ (X ++ (X ++ (P ++ (Y ++ (P ++ (Z ++ P)))))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (X ++ E) (Derives.symm (derivesCrossShuffle X P (Y ++ (P ++ Z)))))
  have step3 : Derives basis (X ++ (E ++ (X ++ (X ++ (P ++ (Y ++ (P ++ (Z ++ P))))))))
      (X ++ (E ++ (X ++ (P ++ (Y ++ (P ++ (Z ++ P))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.symm (derivesRightDuplication X E)) (P ++ (Y ++ (P ++ (Z ++ P)))))
  have step4 : Derives basis (X ++ (E ++ (X ++ (P ++ (Y ++ (P ++ (Z ++ P)))))))
      (X ++ (E ++ (X ++ (P ++ (Y ++ (Z ++ P)))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (X ++ (E ++ X)) (Derives.symm (derivesMiddleReduplication P Y Z)))
  exact Derives.trans (Derives.trans (Derives.trans (Derives.trans (step0) step1) step2) step3) step4

private theorem macroCrossHE (X P Y Z : Word Nat) :
    Derives basis (X ++ (P ++ (Y ++ (P ++ (Z ++ X)))))
      (X ++ (X ++ (P ++ (Y ++ (Z ++ P))))) := by
  have step0 : Derives basis (X ++ (P ++ (Y ++ (P ++ (Z ++ X)))))
      (X ++ (P ++ (P ++ (Y ++ (P ++ (Z ++ X)))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend X (derivesLeftDuplication P Y)) (Z ++ X))
  have step1 : Derives basis (X ++ (P ++ (P ++ (Y ++ (P ++ (Z ++ X))))))
      (X ++ (X ++ (P ++ (Y ++ (P ++ (Z ++ P)))))) := by
    simpa [Word.append_assoc] using (Derives.symm (derivesCrossShuffle X P (Y ++ (P ++ Z))))
  have step2 : Derives basis (X ++ (X ++ (P ++ (Y ++ (P ++ (Z ++ P))))))
      (X ++ (X ++ (P ++ (Y ++ (Z ++ P))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (X ++ X) (Derives.symm (derivesMiddleReduplication P Y Z)))
  exact Derives.trans (Derives.trans (step0) step1) step2

private theorem macroCrossHY (X E P Z : Word Nat) :
    Derives basis (X ++ (E ++ (P ++ (P ++ (Z ++ X)))))
      (X ++ (E ++ (X ++ (P ++ (Z ++ P))))) := by
  have step0 : Derives basis (X ++ (E ++ (P ++ (P ++ (Z ++ X)))))
      (X ++ (E ++ (X ++ (P ++ (P ++ (Z ++ X)))))) := by
    simpa [Word.append_assoc] using (derivesMiddleReduplication X E (P ++ (P ++ Z)))
  have step1 : Derives basis (X ++ (E ++ (X ++ (P ++ (P ++ (Z ++ X))))))
      (X ++ (E ++ (X ++ (X ++ (P ++ (Z ++ P)))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (X ++ E) (Derives.symm (derivesCrossShuffle X P Z)))
  have step2 : Derives basis (X ++ (E ++ (X ++ (X ++ (P ++ (Z ++ P))))))
      (X ++ (E ++ (X ++ (P ++ (Z ++ P))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.symm (derivesRightDuplication X E)) (P ++ (Z ++ P)))
  exact Derives.trans (Derives.trans (step0) step1) step2

private theorem macroCrossHZ (X E P Y : Word Nat) :
    Derives basis (X ++ (E ++ (P ++ (Y ++ (P ++ X)))))
      (X ++ (E ++ (X ++ (P ++ (Y ++ P))))) := by
  have step0 : Derives basis (X ++ (E ++ (P ++ (Y ++ (P ++ X)))))
      (X ++ (E ++ (P ++ (P ++ (Y ++ (P ++ X)))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend (X ++ E) (derivesLeftDuplication P Y)) X)
  have step1 : Derives basis (X ++ (E ++ (P ++ (P ++ (Y ++ (P ++ X))))))
      (X ++ (E ++ (X ++ (P ++ (P ++ (Y ++ (P ++ X))))))) := by
    simpa [Word.append_assoc] using (derivesMiddleReduplication X E (P ++ (P ++ (Y ++ P))))
  have step2 : Derives basis (X ++ (E ++ (X ++ (P ++ (P ++ (Y ++ (P ++ X)))))))
      (X ++ (E ++ (X ++ (X ++ (P ++ (Y ++ (P ++ P))))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (X ++ E) (Derives.symm (derivesCrossShuffle X P (Y ++ P))))
  have step3 : Derives basis (X ++ (E ++ (X ++ (X ++ (P ++ (Y ++ (P ++ P)))))))
      (X ++ (E ++ (X ++ (P ++ (Y ++ (P ++ P)))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.symm (derivesRightDuplication X E)) (P ++ (Y ++ (P ++ P))))
  have step4 : Derives basis (X ++ (E ++ (X ++ (P ++ (Y ++ (P ++ P))))))
      (X ++ (E ++ (X ++ (P ++ (Y ++ P))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (X ++ (E ++ X)) (Derives.symm (derivesRightDuplication P Y)))
  exact Derives.trans (Derives.trans (Derives.trans (Derives.trans (step0) step1) step2) step3) step4

private theorem macroCrossHEY (X P Z : Word Nat) :
    Derives basis (X ++ (P ++ (P ++ (Z ++ X))))
      (X ++ (X ++ (P ++ (Z ++ P)))) := by
  have step0 : Derives basis (X ++ (P ++ (P ++ (Z ++ X))))
      (X ++ (X ++ (P ++ (Z ++ P)))) := by
    simpa [Word.append_assoc] using (Derives.symm (derivesCrossShuffle X P Z))
  exact step0

private theorem macroCrossHEZ (X P Y : Word Nat) :
    Derives basis (X ++ (P ++ (Y ++ (P ++ X))))
      (X ++ (X ++ (P ++ (Y ++ P)))) := by
  have step0 : Derives basis (X ++ (P ++ (Y ++ (P ++ X))))
      (X ++ (P ++ (P ++ (Y ++ (P ++ X))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend X (derivesLeftDuplication P Y)) X)
  have step1 : Derives basis (X ++ (P ++ (P ++ (Y ++ (P ++ X)))))
      (X ++ (X ++ (P ++ (Y ++ (P ++ P))))) := by
    simpa [Word.append_assoc] using (Derives.symm (derivesCrossShuffle X P (Y ++ P)))
  have step2 : Derives basis (X ++ (X ++ (P ++ (Y ++ (P ++ P)))))
      (X ++ (X ++ (P ++ (Y ++ P)))) := by
    simpa [Word.append_assoc] using (Derives.prepend (X ++ X) (Derives.symm (derivesRightDuplication P Y)))
  exact Derives.trans (Derives.trans (step0) step1) step2

private theorem macroCrossHYZ (X E P : Word Nat) :
    Derives basis (X ++ (E ++ (P ++ (P ++ X))))
      (X ++ (E ++ (X ++ (P ++ P)))) := by
  have step0 : Derives basis (X ++ (E ++ (P ++ (P ++ X))))
      (X ++ (E ++ (X ++ (P ++ (P ++ X))))) := by
    simpa [Word.append_assoc] using (derivesMiddleReduplication X E (P ++ P))
  have step1 : Derives basis (X ++ (E ++ (X ++ (P ++ (P ++ X)))))
      (X ++ (E ++ (X ++ (X ++ (P ++ P))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (X ++ E) (Derives.symm (derivesSquareFinalSwitch X P)))
  have step2 : Derives basis (X ++ (E ++ (X ++ (X ++ (P ++ P)))))
      (X ++ (E ++ (X ++ (P ++ P)))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.symm (derivesRightDuplication X E)) (P ++ P))
  exact Derives.trans (Derives.trans (step0) step1) step2

private theorem macroCrossHEYZ (X P : Word Nat) :
    Derives basis (X ++ (P ++ (P ++ X)))
      (X ++ (X ++ (P ++ P))) := by
  have step0 : Derives basis (X ++ (P ++ (P ++ X)))
      (X ++ (X ++ (P ++ P))) := by
    simpa [Word.append_assoc] using (Derives.symm (derivesSquareFinalSwitch X P))
  exact step0

private theorem macroSplitH (E Q A X B G : Word Nat) :
    Derives basis (E ++ (Q ++ (A ++ (X ++ (B ++ (Q ++ (G ++ X)))))))
      (E ++ (Q ++ (A ++ (Q ++ (X ++ (B ++ (G ++ X))))))) := by
  have step0 : Derives basis (E ++ (Q ++ (A ++ (X ++ (B ++ (Q ++ (G ++ X)))))))
      (E ++ (Q ++ (A ++ (X ++ (X ++ (B ++ (Q ++ (G ++ X)))))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (E ++ (Q ++ A)) (derivesLeftDuplication X (B ++ (Q ++ G))))
  have step1 : Derives basis (E ++ (Q ++ (A ++ (X ++ (X ++ (B ++ (Q ++ (G ++ X))))))))
      (E ++ (Q ++ (A ++ (Q ++ (X ++ (X ++ (B ++ (Q ++ (G ++ X))))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend E (derivesMiddleReduplication Q A (X ++ (X ++ B)))) (G ++ X))
  have step2 : Derives basis (E ++ (Q ++ (A ++ (Q ++ (X ++ (X ++ (B ++ (Q ++ (G ++ X)))))))))
      (E ++ (Q ++ (A ++ (Q ++ (Q ++ (X ++ (B ++ (X ++ (G ++ X))))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend (E ++ (Q ++ A)) (Derives.symm (derivesCrossShuffle Q X B))) (G ++ X))
  have step3 : Derives basis (E ++ (Q ++ (A ++ (Q ++ (Q ++ (X ++ (B ++ (X ++ (G ++ X)))))))))
      (E ++ (Q ++ (A ++ (Q ++ (X ++ (B ++ (X ++ (G ++ X)))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend E (Derives.symm (derivesRightDuplication Q A))) (X ++ (B ++ (X ++ (G ++ X)))))
  have step4 : Derives basis (E ++ (Q ++ (A ++ (Q ++ (X ++ (B ++ (X ++ (G ++ X))))))))
      (E ++ (Q ++ (A ++ (Q ++ (X ++ (B ++ (G ++ X))))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (E ++ (Q ++ (A ++ Q))) (Derives.symm (derivesMiddleReduplication X B G)))
  exact Derives.trans (Derives.trans (Derives.trans (Derives.trans (step0) step1) step2) step3) step4

private theorem macroSplitHE (Q A X B G : Word Nat) :
    Derives basis (Q ++ (A ++ (X ++ (B ++ (Q ++ (G ++ X))))))
      (Q ++ (A ++ (Q ++ (X ++ (B ++ (G ++ X)))))) := by
  have step0 : Derives basis (Q ++ (A ++ (X ++ (B ++ (Q ++ (G ++ X))))))
      (Q ++ (A ++ (X ++ (X ++ (B ++ (Q ++ (G ++ X))))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (Q ++ A) (derivesLeftDuplication X (B ++ (Q ++ G))))
  have step1 : Derives basis (Q ++ (A ++ (X ++ (X ++ (B ++ (Q ++ (G ++ X)))))))
      (Q ++ (A ++ (Q ++ (X ++ (X ++ (B ++ (Q ++ (G ++ X)))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (derivesMiddleReduplication Q A (X ++ (X ++ B))) (G ++ X))
  have step2 : Derives basis (Q ++ (A ++ (Q ++ (X ++ (X ++ (B ++ (Q ++ (G ++ X))))))))
      (Q ++ (A ++ (Q ++ (Q ++ (X ++ (B ++ (X ++ (G ++ X)))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend (Q ++ A) (Derives.symm (derivesCrossShuffle Q X B))) (G ++ X))
  have step3 : Derives basis (Q ++ (A ++ (Q ++ (Q ++ (X ++ (B ++ (X ++ (G ++ X))))))))
      (Q ++ (A ++ (Q ++ (X ++ (B ++ (X ++ (G ++ X))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.symm (derivesRightDuplication Q A)) (X ++ (B ++ (X ++ (G ++ X)))))
  have step4 : Derives basis (Q ++ (A ++ (Q ++ (X ++ (B ++ (X ++ (G ++ X)))))))
      (Q ++ (A ++ (Q ++ (X ++ (B ++ (G ++ X)))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (Q ++ (A ++ Q)) (Derives.symm (derivesMiddleReduplication X B G)))
  exact Derives.trans (Derives.trans (Derives.trans (Derives.trans (step0) step1) step2) step3) step4

private theorem macroSplitHA (E Q X B G : Word Nat) :
    Derives basis (E ++ (Q ++ (X ++ (B ++ (Q ++ (G ++ X))))))
      (E ++ (Q ++ (Q ++ (X ++ (B ++ (G ++ X)))))) := by
  have step0 : Derives basis (E ++ (Q ++ (X ++ (B ++ (Q ++ (G ++ X))))))
      (E ++ (Q ++ (X ++ (X ++ (B ++ (Q ++ (G ++ X))))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (E ++ Q) (derivesLeftDuplication X (B ++ (Q ++ G))))
  have step1 : Derives basis (E ++ (Q ++ (X ++ (X ++ (B ++ (Q ++ (G ++ X)))))))
      (E ++ (Q ++ (Q ++ (X ++ (B ++ (X ++ (G ++ X))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend E (Derives.symm (derivesCrossShuffle Q X B))) (G ++ X))
  have step2 : Derives basis (E ++ (Q ++ (Q ++ (X ++ (B ++ (X ++ (G ++ X)))))))
      (E ++ (Q ++ (Q ++ (X ++ (B ++ (G ++ X)))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (E ++ (Q ++ Q)) (Derives.symm (derivesMiddleReduplication X B G)))
  exact Derives.trans (Derives.trans (step0) step1) step2

private theorem macroSplitHB (E Q A X G : Word Nat) :
    Derives basis (E ++ (Q ++ (A ++ (X ++ (Q ++ (G ++ X))))))
      (E ++ (Q ++ (A ++ (Q ++ (X ++ (G ++ X)))))) := by
  have step0 : Derives basis (E ++ (Q ++ (A ++ (X ++ (Q ++ (G ++ X))))))
      (E ++ (Q ++ (A ++ (X ++ (X ++ (Q ++ (G ++ X))))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (E ++ (Q ++ A)) (derivesLeftDuplication X (Q ++ G)))
  have step1 : Derives basis (E ++ (Q ++ (A ++ (X ++ (X ++ (Q ++ (G ++ X)))))))
      (E ++ (Q ++ (A ++ (Q ++ (X ++ (X ++ (Q ++ (G ++ X)))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend E (derivesMiddleReduplication Q A (X ++ X))) (G ++ X))
  have step2 : Derives basis (E ++ (Q ++ (A ++ (Q ++ (X ++ (X ++ (Q ++ (G ++ X))))))))
      (E ++ (Q ++ (A ++ (Q ++ (Q ++ (X ++ (X ++ (G ++ X)))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend (E ++ (Q ++ A)) (Derives.symm (derivesSquareFinalSwitch Q X))) (G ++ X))
  have step3 : Derives basis (E ++ (Q ++ (A ++ (Q ++ (Q ++ (X ++ (X ++ (G ++ X))))))))
      (E ++ (Q ++ (A ++ (Q ++ (Q ++ (X ++ (G ++ X))))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (E ++ (Q ++ (A ++ (Q ++ Q)))) (Derives.symm (derivesLeftDuplication X G)))
  have step4 : Derives basis (E ++ (Q ++ (A ++ (Q ++ (Q ++ (X ++ (G ++ X)))))))
      (E ++ (Q ++ (A ++ (Q ++ (X ++ (G ++ X)))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend E (Derives.symm (derivesRightDuplication Q A))) (X ++ (G ++ X)))
  exact Derives.trans (Derives.trans (Derives.trans (Derives.trans (step0) step1) step2) step3) step4

private theorem macroSplitHG (E Q A X B : Word Nat) :
    Derives basis (E ++ (Q ++ (A ++ (X ++ (B ++ (Q ++ X))))))
      (E ++ (Q ++ (A ++ (Q ++ (X ++ (B ++ X)))))) := by
  have step0 : Derives basis (E ++ (Q ++ (A ++ (X ++ (B ++ (Q ++ X))))))
      (E ++ (Q ++ (A ++ (X ++ (X ++ (B ++ (Q ++ X))))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (E ++ (Q ++ A)) (derivesLeftDuplication X (B ++ Q)))
  have step1 : Derives basis (E ++ (Q ++ (A ++ (X ++ (X ++ (B ++ (Q ++ X)))))))
      (E ++ (Q ++ (A ++ (Q ++ (X ++ (X ++ (B ++ (Q ++ X)))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend E (derivesMiddleReduplication Q A (X ++ (X ++ B)))) X)
  have step2 : Derives basis (E ++ (Q ++ (A ++ (Q ++ (X ++ (X ++ (B ++ (Q ++ X))))))))
      (E ++ (Q ++ (A ++ (Q ++ (Q ++ (X ++ (B ++ (X ++ X)))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend (E ++ (Q ++ A)) (Derives.symm (derivesCrossShuffle Q X B))) X)
  have step3 : Derives basis (E ++ (Q ++ (A ++ (Q ++ (Q ++ (X ++ (B ++ (X ++ X))))))))
      (E ++ (Q ++ (A ++ (Q ++ (X ++ (B ++ (X ++ X))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend E (Derives.symm (derivesRightDuplication Q A))) (X ++ (B ++ (X ++ X))))
  have step4 : Derives basis (E ++ (Q ++ (A ++ (Q ++ (X ++ (B ++ (X ++ X)))))))
      (E ++ (Q ++ (A ++ (Q ++ (X ++ (B ++ X)))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (E ++ (Q ++ (A ++ Q))) (Derives.symm (derivesRightDuplication X B)))
  exact Derives.trans (Derives.trans (Derives.trans (Derives.trans (step0) step1) step2) step3) step4

private theorem macroSplitHEA (Q X B G : Word Nat) :
    Derives basis (Q ++ (X ++ (B ++ (Q ++ (G ++ X)))))
      (Q ++ (Q ++ (X ++ (B ++ (G ++ X))))) := by
  have step0 : Derives basis (Q ++ (X ++ (B ++ (Q ++ (G ++ X)))))
      (Q ++ (X ++ (X ++ (B ++ (Q ++ (G ++ X)))))) := by
    simpa [Word.append_assoc] using (Derives.prepend Q (derivesLeftDuplication X (B ++ (Q ++ G))))
  have step1 : Derives basis (Q ++ (X ++ (X ++ (B ++ (Q ++ (G ++ X))))))
      (Q ++ (Q ++ (X ++ (B ++ (X ++ (G ++ X)))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.symm (derivesCrossShuffle Q X B)) (G ++ X))
  have step2 : Derives basis (Q ++ (Q ++ (X ++ (B ++ (X ++ (G ++ X))))))
      (Q ++ (Q ++ (X ++ (B ++ (G ++ X))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (Q ++ Q) (Derives.symm (derivesMiddleReduplication X B G)))
  exact Derives.trans (Derives.trans (step0) step1) step2

private theorem macroSplitHEB (Q A X G : Word Nat) :
    Derives basis (Q ++ (A ++ (X ++ (Q ++ (G ++ X)))))
      (Q ++ (A ++ (Q ++ (X ++ (G ++ X))))) := by
  have step0 : Derives basis (Q ++ (A ++ (X ++ (Q ++ (G ++ X)))))
      (Q ++ (A ++ (X ++ (X ++ (Q ++ (G ++ X)))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (Q ++ A) (derivesLeftDuplication X (Q ++ G)))
  have step1 : Derives basis (Q ++ (A ++ (X ++ (X ++ (Q ++ (G ++ X))))))
      (Q ++ (A ++ (Q ++ (X ++ (X ++ (Q ++ (G ++ X))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (derivesMiddleReduplication Q A (X ++ X)) (G ++ X))
  have step2 : Derives basis (Q ++ (A ++ (Q ++ (X ++ (X ++ (Q ++ (G ++ X)))))))
      (Q ++ (A ++ (Q ++ (Q ++ (X ++ (X ++ (G ++ X))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend (Q ++ A) (Derives.symm (derivesSquareFinalSwitch Q X))) (G ++ X))
  have step3 : Derives basis (Q ++ (A ++ (Q ++ (Q ++ (X ++ (X ++ (G ++ X)))))))
      (Q ++ (A ++ (Q ++ (Q ++ (X ++ (G ++ X)))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (Q ++ (A ++ (Q ++ Q))) (Derives.symm (derivesLeftDuplication X G)))
  have step4 : Derives basis (Q ++ (A ++ (Q ++ (Q ++ (X ++ (G ++ X))))))
      (Q ++ (A ++ (Q ++ (X ++ (G ++ X))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.symm (derivesRightDuplication Q A)) (X ++ (G ++ X)))
  exact Derives.trans (Derives.trans (Derives.trans (Derives.trans (step0) step1) step2) step3) step4

private theorem macroSplitHEG (Q A X B : Word Nat) :
    Derives basis (Q ++ (A ++ (X ++ (B ++ (Q ++ X)))))
      (Q ++ (A ++ (Q ++ (X ++ (B ++ X))))) := by
  have step0 : Derives basis (Q ++ (A ++ (X ++ (B ++ (Q ++ X)))))
      (Q ++ (A ++ (X ++ (X ++ (B ++ (Q ++ X)))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (Q ++ A) (derivesLeftDuplication X (B ++ Q)))
  have step1 : Derives basis (Q ++ (A ++ (X ++ (X ++ (B ++ (Q ++ X))))))
      (Q ++ (A ++ (Q ++ (X ++ (X ++ (B ++ (Q ++ X))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (derivesMiddleReduplication Q A (X ++ (X ++ B))) X)
  have step2 : Derives basis (Q ++ (A ++ (Q ++ (X ++ (X ++ (B ++ (Q ++ X)))))))
      (Q ++ (A ++ (Q ++ (Q ++ (X ++ (B ++ (X ++ X))))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend (Q ++ A) (Derives.symm (derivesCrossShuffle Q X B))) X)
  have step3 : Derives basis (Q ++ (A ++ (Q ++ (Q ++ (X ++ (B ++ (X ++ X)))))))
      (Q ++ (A ++ (Q ++ (X ++ (B ++ (X ++ X)))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.symm (derivesRightDuplication Q A)) (X ++ (B ++ (X ++ X))))
  have step4 : Derives basis (Q ++ (A ++ (Q ++ (X ++ (B ++ (X ++ X))))))
      (Q ++ (A ++ (Q ++ (X ++ (B ++ X))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (Q ++ (A ++ Q)) (Derives.symm (derivesRightDuplication X B)))
  exact Derives.trans (Derives.trans (Derives.trans (Derives.trans (step0) step1) step2) step3) step4

private theorem macroSplitHAB (E Q X G : Word Nat) :
    Derives basis (E ++ (Q ++ (X ++ (Q ++ (G ++ X)))))
      (E ++ (Q ++ (Q ++ (X ++ (G ++ X))))) := by
  have step0 : Derives basis (E ++ (Q ++ (X ++ (Q ++ (G ++ X)))))
      (E ++ (Q ++ (X ++ (X ++ (Q ++ (G ++ X)))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (E ++ Q) (derivesLeftDuplication X (Q ++ G)))
  have step1 : Derives basis (E ++ (Q ++ (X ++ (X ++ (Q ++ (G ++ X))))))
      (E ++ (Q ++ (Q ++ (X ++ (X ++ (G ++ X)))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend E (Derives.symm (derivesSquareFinalSwitch Q X))) (G ++ X))
  have step2 : Derives basis (E ++ (Q ++ (Q ++ (X ++ (X ++ (G ++ X))))))
      (E ++ (Q ++ (Q ++ (X ++ (G ++ X))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (E ++ (Q ++ Q)) (Derives.symm (derivesLeftDuplication X G)))
  exact Derives.trans (Derives.trans (step0) step1) step2

private theorem macroSplitHAG (E Q X B : Word Nat) :
    Derives basis (E ++ (Q ++ (X ++ (B ++ (Q ++ X)))))
      (E ++ (Q ++ (Q ++ (X ++ (B ++ X))))) := by
  have step0 : Derives basis (E ++ (Q ++ (X ++ (B ++ (Q ++ X)))))
      (E ++ (Q ++ (X ++ (X ++ (B ++ (Q ++ X)))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (E ++ Q) (derivesLeftDuplication X (B ++ Q)))
  have step1 : Derives basis (E ++ (Q ++ (X ++ (X ++ (B ++ (Q ++ X))))))
      (E ++ (Q ++ (Q ++ (X ++ (B ++ (X ++ X)))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend E (Derives.symm (derivesCrossShuffle Q X B))) X)
  have step2 : Derives basis (E ++ (Q ++ (Q ++ (X ++ (B ++ (X ++ X))))))
      (E ++ (Q ++ (Q ++ (X ++ (B ++ X))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (E ++ (Q ++ Q)) (Derives.symm (derivesRightDuplication X B)))
  exact Derives.trans (Derives.trans (step0) step1) step2

private theorem macroSplitHBG (E Q A X : Word Nat) :
    Derives basis (E ++ (Q ++ (A ++ (X ++ (Q ++ X)))))
      (E ++ (Q ++ (A ++ (Q ++ (X ++ X))))) := by
  have step0 : Derives basis (E ++ (Q ++ (A ++ (X ++ (Q ++ X)))))
      (E ++ (Q ++ (A ++ (Q ++ (X ++ (Q ++ X)))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend E (derivesMiddleReduplication Q A X)) X)
  have step1 : Derives basis (E ++ (Q ++ (A ++ (Q ++ (X ++ (Q ++ X))))))
      (E ++ (Q ++ (A ++ (Q ++ (Q ++ (X ++ X)))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (E ++ (Q ++ A)) (Derives.symm (derivesSquareInterleave Q X)))
  have step2 : Derives basis (E ++ (Q ++ (A ++ (Q ++ (Q ++ (X ++ X))))))
      (E ++ (Q ++ (A ++ (Q ++ (X ++ X))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.prepend E (Derives.symm (derivesRightDuplication Q A))) (X ++ X))
  exact Derives.trans (Derives.trans (step0) step1) step2

private theorem macroSplitHEAB (Q X G : Word Nat) :
    Derives basis (Q ++ (X ++ (Q ++ (G ++ X))))
      (Q ++ (Q ++ (X ++ (G ++ X)))) := by
  have step0 : Derives basis (Q ++ (X ++ (Q ++ (G ++ X))))
      (Q ++ (X ++ (X ++ (Q ++ (G ++ X))))) := by
    simpa [Word.append_assoc] using (Derives.prepend Q (derivesLeftDuplication X (Q ++ G)))
  have step1 : Derives basis (Q ++ (X ++ (X ++ (Q ++ (G ++ X)))))
      (Q ++ (Q ++ (X ++ (X ++ (G ++ X))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.symm (derivesSquareFinalSwitch Q X)) (G ++ X))
  have step2 : Derives basis (Q ++ (Q ++ (X ++ (X ++ (G ++ X)))))
      (Q ++ (Q ++ (X ++ (G ++ X)))) := by
    simpa [Word.append_assoc] using (Derives.prepend (Q ++ Q) (Derives.symm (derivesLeftDuplication X G)))
  exact Derives.trans (Derives.trans (step0) step1) step2

private theorem macroSplitHEAG (Q X B : Word Nat) :
    Derives basis (Q ++ (X ++ (B ++ (Q ++ X))))
      (Q ++ (Q ++ (X ++ (B ++ X)))) := by
  have step0 : Derives basis (Q ++ (X ++ (B ++ (Q ++ X))))
      (Q ++ (X ++ (X ++ (B ++ (Q ++ X))))) := by
    simpa [Word.append_assoc] using (Derives.prepend Q (derivesLeftDuplication X (B ++ Q)))
  have step1 : Derives basis (Q ++ (X ++ (X ++ (B ++ (Q ++ X)))))
      (Q ++ (Q ++ (X ++ (B ++ (X ++ X))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.symm (derivesCrossShuffle Q X B)) X)
  have step2 : Derives basis (Q ++ (Q ++ (X ++ (B ++ (X ++ X)))))
      (Q ++ (Q ++ (X ++ (B ++ X)))) := by
    simpa [Word.append_assoc] using (Derives.prepend (Q ++ Q) (Derives.symm (derivesRightDuplication X B)))
  exact Derives.trans (Derives.trans (step0) step1) step2

private theorem macroSplitHEBG (Q A X : Word Nat) :
    Derives basis (Q ++ (A ++ (X ++ (Q ++ X))))
      (Q ++ (A ++ (Q ++ (X ++ X)))) := by
  have step0 : Derives basis (Q ++ (A ++ (X ++ (Q ++ X))))
      (Q ++ (A ++ (Q ++ (X ++ (Q ++ X))))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (derivesMiddleReduplication Q A X) X)
  have step1 : Derives basis (Q ++ (A ++ (Q ++ (X ++ (Q ++ X)))))
      (Q ++ (A ++ (Q ++ (Q ++ (X ++ X))))) := by
    simpa [Word.append_assoc] using (Derives.prepend (Q ++ A) (Derives.symm (derivesSquareInterleave Q X)))
  have step2 : Derives basis (Q ++ (A ++ (Q ++ (Q ++ (X ++ X)))))
      (Q ++ (A ++ (Q ++ (X ++ X)))) := by
    simpa [Word.append_assoc] using (Derives.appendRight (Derives.symm (derivesRightDuplication Q A)) (X ++ X))
  exact Derives.trans (Derives.trans (step0) step1) step2

private theorem macroSplitHABG (E Q X : Word Nat) :
    Derives basis (E ++ (Q ++ (X ++ (Q ++ X))))
      (E ++ (Q ++ (Q ++ (X ++ X)))) := by
  have step0 : Derives basis (E ++ (Q ++ (X ++ (Q ++ X))))
      (E ++ (Q ++ (Q ++ (X ++ X)))) := by
    simpa [Word.append_assoc] using (Derives.prepend E (Derives.symm (derivesSquareInterleave Q X)))
  exact step0

private theorem macroSplitHEABG (Q X : Word Nat) :
    Derives basis (Q ++ (X ++ (Q ++ X)))
      (Q ++ (Q ++ (X ++ X))) := by
  have step0 : Derives basis (Q ++ (X ++ (Q ++ X)))
      (Q ++ (Q ++ (X ++ X))) := by
    simpa [Word.append_assoc] using (Derives.symm (derivesSquareInterleave Q X))
  exact step0

/-! ## List-level crossing macro (unifies the emptiness variants) -/

/-- Cross one rendered block with the trailing close, tail-open form:
the pulled letter's open sits in the tail after `pre`. -/
private theorem macroCrossList (hd : Nat) (pre : List Nat) (x : Nat)
    (E : List Nat) (p : Nat) (Y Z R : List Nat) :
    Derives basis
      (⟨hd, pre ++ x :: (E ++ (p :: (Y ++ p :: Z)) ++ x :: R)⟩ :
        Word Nat)
      (⟨hd, pre ++ x :: (E ++ x :: (p :: ((Y ++ Z) ++ [p])) ++ R)⟩ :
        Word Nat) := by
  cases E with
  | nil =>
      cases Y with
      | nil =>
          cases Z with
          | nil =>
              simpa [append_mk, List.append_assoc] using
                derivesFactor (macroCrossEYZ (⟨hd, pre⟩ : Word Nat)
                  (Word.singleton x) (Word.singleton p)) none R
          | cons z0 Z' =>
              simpa [append_mk, List.append_assoc] using
                derivesFactor (macroCrossEY (⟨hd, pre⟩ : Word Nat)
                  (Word.singleton x) (Word.singleton p)
                  (⟨z0, Z'⟩ : Word Nat)) none R
      | cons y0 Y' =>
          cases Z with
          | nil =>
              simpa [append_mk, List.append_assoc] using
                derivesFactor (macroCrossEZ (⟨hd, pre⟩ : Word Nat)
                  (Word.singleton x) (Word.singleton p)
                  (⟨y0, Y'⟩ : Word Nat)) none R
          | cons z0 Z' =>
              simpa [append_mk, List.append_assoc] using
                derivesFactor (macroCrossE (⟨hd, pre⟩ : Word Nat)
                  (Word.singleton x) (Word.singleton p)
                  (⟨y0, Y'⟩ : Word Nat) (⟨z0, Z'⟩ : Word Nat)) none R
  | cons e0 E' =>
      cases Y with
      | nil =>
          cases Z with
          | nil =>
              simpa [append_mk, List.append_assoc] using
                derivesFactor (macroCrossYZ (⟨hd, pre⟩ : Word Nat)
                  (Word.singleton x) (⟨e0, E'⟩ : Word Nat)
                  (Word.singleton p)) none R
          | cons z0 Z' =>
              simpa [append_mk, List.append_assoc] using
                derivesFactor (macroCrossY (⟨hd, pre⟩ : Word Nat)
                  (Word.singleton x) (⟨e0, E'⟩ : Word Nat)
                  (Word.singleton p) (⟨z0, Z'⟩ : Word Nat)) none R
      | cons y0 Y' =>
          cases Z with
          | nil =>
              simpa [append_mk, List.append_assoc] using
                derivesFactor (macroCrossZ (⟨hd, pre⟩ : Word Nat)
                  (Word.singleton x) (⟨e0, E'⟩ : Word Nat)
                  (Word.singleton p) (⟨y0, Y'⟩ : Word Nat)) none R
          | cons z0 Z' =>
              simpa [append_mk, List.append_assoc] using
                derivesFactor (macroCrossFull (⟨hd, pre⟩ : Word Nat)
                  (Word.singleton x) (⟨e0, E'⟩ : Word Nat)
                  (Word.singleton p) (⟨y0, Y'⟩ : Word Nat)
                  (⟨z0, Z'⟩ : Word Nat)) none R

/-- Cross one rendered block, head-open form: the pulled letter's open
is the word head itself. -/
private theorem macroCrossListHead (x : Nat) (E : List Nat) (p : Nat)
    (Y Z R : List Nat) :
    Derives basis
      (⟨x, E ++ (p :: (Y ++ p :: Z)) ++ x :: R⟩ : Word Nat)
      (⟨x, E ++ x :: (p :: ((Y ++ Z) ++ [p])) ++ R⟩ : Word Nat) := by
  cases E with
  | nil =>
      cases Y with
      | nil =>
          cases Z with
          | nil =>
              simpa [append_mk, List.append_assoc] using
                derivesFactor (macroCrossHEYZ (Word.singleton x)
                  (Word.singleton p)) none R
          | cons z0 Z' =>
              simpa [append_mk, List.append_assoc] using
                derivesFactor (macroCrossHEY (Word.singleton x)
                  (Word.singleton p) (⟨z0, Z'⟩ : Word Nat)) none R
      | cons y0 Y' =>
          cases Z with
          | nil =>
              simpa [append_mk, List.append_assoc] using
                derivesFactor (macroCrossHEZ (Word.singleton x)
                  (Word.singleton p) (⟨y0, Y'⟩ : Word Nat)) none R
          | cons z0 Z' =>
              simpa [append_mk, List.append_assoc] using
                derivesFactor (macroCrossHE (Word.singleton x)
                  (Word.singleton p) (⟨y0, Y'⟩ : Word Nat)
                  (⟨z0, Z'⟩ : Word Nat)) none R
  | cons e0 E' =>
      cases Y with
      | nil =>
          cases Z with
          | nil =>
              simpa [append_mk, List.append_assoc] using
                derivesFactor (macroCrossHYZ (Word.singleton x)
                  (⟨e0, E'⟩ : Word Nat) (Word.singleton p)) none R
          | cons z0 Z' =>
              simpa [append_mk, List.append_assoc] using
                derivesFactor (macroCrossHY (Word.singleton x)
                  (⟨e0, E'⟩ : Word Nat) (Word.singleton p)
                  (⟨z0, Z'⟩ : Word Nat)) none R
      | cons y0 Y' =>
          cases Z with
          | nil =>
              simpa [append_mk, List.append_assoc] using
                derivesFactor (macroCrossHZ (Word.singleton x)
                  (⟨e0, E'⟩ : Word Nat) (Word.singleton p)
                  (⟨y0, Y'⟩ : Word Nat)) none R
          | cons z0 Z' =>
              simpa [append_mk, List.append_assoc] using
                derivesFactor (macroCrossH (Word.singleton x)
                  (⟨e0, E'⟩ : Word Nat) (Word.singleton p)
                  (⟨y0, Y'⟩ : Word Nat) (⟨z0, Z'⟩ : Word Nat)) none R

/-! ## List-level split macro (unifies the emptiness variants) -/

/-- Split an enclosing pair around a nested pair, tail-open form. -/
private theorem macroSplitList (hd : Nat) (pre : List Nat) (q : Nat)
    (A : List Nat) (x : Nat) (Bq G R : List Nat) :
    Derives basis
      (⟨hd, pre ++ (q :: (A ++ x :: (Bq ++ q :: (G ++ x :: R))))⟩ :
        Word Nat)
      (⟨hd, pre ++ (q :: (A ++ q :: (x :: (Bq ++ G ++ [x]) ++ R)))⟩ :
        Word Nat) := by
  cases A with
  | nil =>
      cases Bq with
      | nil =>
          cases G with
          | nil =>
              simpa [append_mk, List.append_assoc] using
                derivesFactor (macroSplitEABG (⟨hd, pre⟩ : Word Nat)
                  (Word.singleton q) (Word.singleton x)) none R
          | cons g0 G' =>
              simpa [append_mk, List.append_assoc] using
                derivesFactor (macroSplitEAB (⟨hd, pre⟩ : Word Nat)
                  (Word.singleton q) (Word.singleton x)
                  (⟨g0, G'⟩ : Word Nat)) none R
      | cons b0 Bq' =>
          cases G with
          | nil =>
              simpa [append_mk, List.append_assoc] using
                derivesFactor (macroSplitEAG (⟨hd, pre⟩ : Word Nat)
                  (Word.singleton q) (Word.singleton x)
                  (⟨b0, Bq'⟩ : Word Nat)) none R
          | cons g0 G' =>
              simpa [append_mk, List.append_assoc] using
                derivesFactor (macroSplitEA (⟨hd, pre⟩ : Word Nat)
                  (Word.singleton q) (Word.singleton x)
                  (⟨b0, Bq'⟩ : Word Nat) (⟨g0, G'⟩ : Word Nat)) none R
  | cons a0 A' =>
      cases Bq with
      | nil =>
          cases G with
          | nil =>
              simpa [append_mk, List.append_assoc] using
                derivesFactor (macroSplitEBG (⟨hd, pre⟩ : Word Nat)
                  (Word.singleton q) (⟨a0, A'⟩ : Word Nat)
                  (Word.singleton x)) none R
          | cons g0 G' =>
              simpa [append_mk, List.append_assoc] using
                derivesFactor (macroSplitEB (⟨hd, pre⟩ : Word Nat)
                  (Word.singleton q) (⟨a0, A'⟩ : Word Nat)
                  (Word.singleton x) (⟨g0, G'⟩ : Word Nat)) none R
      | cons b0 Bq' =>
          cases G with
          | nil =>
              simpa [append_mk, List.append_assoc] using
                derivesFactor (macroSplitEG (⟨hd, pre⟩ : Word Nat)
                  (Word.singleton q) (⟨a0, A'⟩ : Word Nat)
                  (Word.singleton x) (⟨b0, Bq'⟩ : Word Nat)) none R
          | cons g0 G' =>
              simpa [append_mk, List.append_assoc] using
                derivesFactor (macroSplitE (⟨hd, pre⟩ : Word Nat)
                  (Word.singleton q) (⟨a0, A'⟩ : Word Nat)
                  (Word.singleton x) (⟨b0, Bq'⟩ : Word Nat)
                  (⟨g0, G'⟩ : Word Nat)) none R

/-- Split an enclosing pair around a nested pair, head-open form. -/
private theorem macroSplitListHead (q : Nat) (A : List Nat) (x : Nat)
    (Bq G R : List Nat) :
    Derives basis
      (⟨q, A ++ x :: (Bq ++ q :: (G ++ x :: R))⟩ : Word Nat)
      (⟨q, A ++ q :: (x :: (Bq ++ G ++ [x]) ++ R)⟩ : Word Nat) := by
  cases A with
  | nil =>
      cases Bq with
      | nil =>
          cases G with
          | nil =>
              simpa [append_mk, List.append_assoc] using
                derivesFactor (macroSplitHEABG (Word.singleton q)
                  (Word.singleton x)) none R
          | cons g0 G' =>
              simpa [append_mk, List.append_assoc] using
                derivesFactor (macroSplitHEAB (Word.singleton q)
                  (Word.singleton x) (⟨g0, G'⟩ : Word Nat)) none R
      | cons b0 Bq' =>
          cases G with
          | nil =>
              simpa [append_mk, List.append_assoc] using
                derivesFactor (macroSplitHEAG (Word.singleton q)
                  (Word.singleton x) (⟨b0, Bq'⟩ : Word Nat)) none R
          | cons g0 G' =>
              simpa [append_mk, List.append_assoc] using
                derivesFactor (macroSplitHEA (Word.singleton q)
                  (Word.singleton x) (⟨b0, Bq'⟩ : Word Nat)
                  (⟨g0, G'⟩ : Word Nat)) none R
  | cons a0 A' =>
      cases Bq with
      | nil =>
          cases G with
          | nil =>
              simpa [append_mk, List.append_assoc] using
                derivesFactor (macroSplitHEBG (Word.singleton q)
                  (⟨a0, A'⟩ : Word Nat) (Word.singleton x)) none R
          | cons g0 G' =>
              simpa [append_mk, List.append_assoc] using
                derivesFactor (macroSplitHEB (Word.singleton q)
                  (⟨a0, A'⟩ : Word Nat) (Word.singleton x)
                  (⟨g0, G'⟩ : Word Nat)) none R
      | cons b0 Bq' =>
          cases G with
          | nil =>
              simpa [append_mk, List.append_assoc] using
                derivesFactor (macroSplitHEG (Word.singleton q)
                  (⟨a0, A'⟩ : Word Nat) (Word.singleton x)
                  (⟨b0, Bq'⟩ : Word Nat)) none R
          | cons g0 G' =>
              simpa [append_mk, List.append_assoc] using
                derivesFactor (macroSplitHE (Word.singleton q)
                  (⟨a0, A'⟩ : Word Nat) (Word.singleton x)
                  (⟨b0, Bq'⟩ : Word Nat) (⟨g0, G'⟩ : Word Nat)) none R

/-! ## Pulling one close left across a suffix of plasma blocks -/

private structure PullBlock where
  letter : Nat
  ins : List Nat
  gaps : List Nat

private def insAt (u : Word Nat) (i : Nat) : List Nat :=
  (strippedSingles u).filter
    (fun s => slotOf u s == i + 1 && rel4 u s == Rel4.inside)

private def gapAt (u : Word Nat) (i : Nat) : List Nat :=
  (strippedSingles u).filter
    (fun s => slotOf u s == i + 1 && rel4 u s == Rel4.gap)

private def beforeAt (u : Word Nat) : List Nat :=
  (strippedSingles u).filter (fun s => slotOf u s == 0)

private def afterAt (u : Word Nat) : List Nat :=
  (strippedSingles u).filter
    (fun s => slotOf u s == (plasmaSeq u).length &&
      rel4 u s == Rel4.after)

/-! ## Ordered partitions of a single slot -/

/-- Strengthen a pairwise relation using membership information for both
endpoints. -/
private theorem pairwise_imp_of_mem_local {α : Type} {L : List α}
    {r q : α → α → Prop}
    (pw : List.Pairwise r L)
    (imp : ∀ a, a ∈ L → ∀ b, b ∈ L → r a b → q a b) :
    List.Pairwise q L := by
  induction L with
  | nil => exact List.Pairwise.nil
  | cons a rest ih =>
      rw [List.pairwise_cons] at pw ⊢
      obtain ⟨head, tail⟩ := pw
      constructor
      · intro b bMem
        exact imp a List.mem_cons_self b
          (List.mem_cons_of_mem _ bMem) (head b bMem)
      · apply ih tail
        intro b bMem c cMem
        exact imp b (List.mem_cons_of_mem _ bMem) c
          (List.mem_cons_of_mem _ cMem)

/-- If every `p`-item precedes every `q`-item, a Boolean union filter
splits into its two ordered component filters. -/
private theorem filter_or_eq_append_of_pairwise {α : Type}
    (L : List α) (p q : α → Bool)
    (disjoint : ∀ a, a ∈ L → p a = true → q a = false)
    (ordered : List.Pairwise
      (fun a b => q a = true → p b = false) L) :
    L.filter (fun a => p a || q a) = L.filter p ++ L.filter q := by
  induction L with
  | nil => rfl
  | cons a rest ih =>
      rw [List.pairwise_cons] at ordered
      obtain ⟨headOrder, tailOrder⟩ := ordered
      have disjointTail : ∀ b, b ∈ rest → p b = true → q b = false :=
        fun b bMem => disjoint b (List.mem_cons_of_mem _ bMem)
      have tailEq := ih disjointTail tailOrder
      cases pa : p a with
      | true =>
          have qa : q a = false := disjoint a List.mem_cons_self pa
          simp [List.filter_cons, pa, qa, tailEq]
      | false =>
          cases qa : q a with
          | false => simp [List.filter_cons, pa, qa, tailEq]
          | true =>
              have pTail : rest.filter p = [] := by
                rw [List.filter_eq_nil_iff]
                intro b bMem
                have falseEq := headOrder b bMem qa
                simp [falseEq]
              simp [List.filter_cons, pa, qa, tailEq, pTail]

/-- A count-one letter in a positive nonterminal slot is either inside or
in the following gap. -/
private theorem rel4_inside_or_gap_of_single_interior {u : Word Nat}
    {s j : Nat} (single : IsSingle u s) (positive : 0 < j)
    (slot : slotOf u s = j) (below : j < (plasmaSeq u).length) :
    rel4 u s = Rel4.inside ∨ rel4 u s = Rel4.gap := by
  cases relation : rel4 u s with
  | before =>
      have zero := slotOf_eq_zero_of_rel_before relation
      rw [slot] at zero
      omega
  | after =>
      have terminal := slotOf_eq_length_of_rel_after relation
      rw [slot] at terminal
      omega
  | inside => exact Or.inl rfl
  | gap => exact Or.inr rfl

/-- A count-one letter in the positive terminal slot is either inside or
after all plasma intervals. -/
private theorem rel4_inside_or_after_of_single_terminal {u : Word Nat}
    {s : Nat} (single : IsSingle u s)
    (positive : 0 < (plasmaSeq u).length)
    (slot : slotOf u s = (plasmaSeq u).length) :
    rel4 u s = Rel4.inside ∨ rel4 u s = Rel4.after := by
  cases relation : rel4 u s with
  | before =>
      have zero := slotOf_eq_zero_of_rel_before relation
      rw [slot] at zero
      omega
  | after => exact Or.inr rfl
  | inside => exact Or.inl rfl
  | gap =>
      have impossible := rel4_ne_gap_of_terminal_slot single slot relation
      exact False.elim impossible

/-- A positive nonterminal slot consists of its inside singles followed
by its gap singles. -/
private theorem slotFilter_eq_ins_gap (u : Word Nat) {j : Nat}
    (jPos : 0 < j) (jLt : j < (plasmaSeq u).length) :
    (strippedSingles u).filter (fun s => slotOf u s == j) =
      insAt u (j - 1) ++ gapAt u (j - 1) := by
  let p : Nat → Bool := fun s =>
    slotOf u s == j && rel4 u s == Rel4.inside
  let q : Nat → Bool := fun s =>
    slotOf u s == j && rel4 u s == Rel4.gap
  have classify : ∀ s, s ∈ strippedSingles u →
      (slotOf u s == j) = (p s || q s) := by
    intro s sMem
    by_cases slot : slotOf u s = j
    · rcases rel4_inside_or_gap_of_single_interior
          (isSingle_of_mem_stripped sMem) jPos slot jLt with inside | gap
      · simp [p, q, slot, inside]
      · simp [p, q, slot, gap]
    · have slotFalse : (slotOf u s == j) = false := by
        apply Bool.eq_false_iff.mpr
        intro pass
        exact slot (eq_of_beq pass)
      simp [p, q, slotFalse]
  have disjoint : ∀ s, s ∈ strippedSingles u →
      p s = true → q s = false := by
    intro s _ pass
    have parts : slotOf u s = j ∧ rel4 u s = Rel4.inside := by
      simpa only [p, Bool.and_eq_true, beq_iff_eq] using pass
    simp [q, parts.1, parts.2]
  have ordered : List.Pairwise
      (fun a b => q a = true → p b = false) (strippedSingles u) := by
    apply pairwise_imp_of_mem_local (strippedSingles_pairwise_idxOf u)
    intro a aMem b bMem sourceOrder
    intro qa
    cases pb : p b with
    | false => rfl
    | true =>
        have qaParts : slotOf u a = j ∧ rel4 u a = Rel4.gap := by
          simpa only [q, Bool.and_eq_true, beq_iff_eq] using qa
        have pbParts : slotOf u b = j ∧ rel4 u b = Rel4.inside := by
          simpa only [p, Bool.and_eq_true, beq_iff_eq] using pb
        have reverse := inside_before_same_slot_gap
          (isSingle_of_mem_stripped bMem)
          (isSingle_of_mem_stripped aMem)
          pbParts.2 qaParts.2 (by omega)
        omega
  have partition := filter_or_eq_append_of_pairwise
    (strippedSingles u) p q disjoint ordered
  have pred : j - 1 + 1 = j := by omega
  calc
    (strippedSingles u).filter (fun s => slotOf u s == j) =
        (strippedSingles u).filter (fun s => p s || q s) :=
      filter_congr_mem classify
    _ = (strippedSingles u).filter p ++
        (strippedSingles u).filter q := partition
    _ = insAt u (j - 1) ++ gapAt u (j - 1) := by
      simp [p, q, insAt, gapAt, pred]

/-- The positive terminal slot consists of its inside singles followed
by its after singles. -/
private theorem slotFilter_terminal_eq_ins_after (u : Word Nat)
    (nPos : 0 < (plasmaSeq u).length) :
    (strippedSingles u).filter
      (fun s => slotOf u s == (plasmaSeq u).length) =
      insAt u ((plasmaSeq u).length - 1) ++ afterAt u := by
  let n : Nat := (plasmaSeq u).length
  let p : Nat → Bool := fun s =>
    slotOf u s == n && rel4 u s == Rel4.inside
  let q : Nat → Bool := fun s =>
    slotOf u s == n && rel4 u s == Rel4.after
  have classify : ∀ s, s ∈ strippedSingles u →
      (slotOf u s == n) = (p s || q s) := by
    intro s sMem
    by_cases slot : slotOf u s = n
    · rcases rel4_inside_or_after_of_single_terminal
          (isSingle_of_mem_stripped sMem) (by simpa [n] using nPos)
          (by simpa [n] using slot) with inside | after
      · simp [p, q, slot, inside]
      · simp [p, q, slot, after]
    · have slotFalse : (slotOf u s == n) = false := by
        apply Bool.eq_false_iff.mpr
        intro pass
        exact slot (eq_of_beq pass)
      simp [p, q, slotFalse]
  have disjoint : ∀ s, s ∈ strippedSingles u →
      p s = true → q s = false := by
    intro s _ pass
    have parts : slotOf u s = n ∧ rel4 u s = Rel4.inside := by
      simpa only [p, Bool.and_eq_true, beq_iff_eq] using pass
    simp [q, parts.1, parts.2]
  have ordered : List.Pairwise
      (fun a b => q a = true → p b = false) (strippedSingles u) := by
    apply pairwise_imp_of_mem_local (strippedSingles_pairwise_idxOf u)
    intro a aMem b bMem sourceOrder
    intro qa
    cases pb : p b with
    | false => rfl
    | true =>
        have qaParts : slotOf u a = n ∧ rel4 u a = Rel4.after := by
          simpa only [q, Bool.and_eq_true, beq_iff_eq] using qa
        have pbParts : slotOf u b = n ∧ rel4 u b = Rel4.inside := by
          simpa only [p, Bool.and_eq_true, beq_iff_eq] using pb
        have afterB := rel4_after_of_later qaParts.2 sourceOrder
        rw [pbParts.2] at afterB
        cases afterB
  have partition := filter_or_eq_append_of_pairwise
    (strippedSingles u) p q disjoint ordered
  have pred : n - 1 + 1 = n := by omega
  calc
    (strippedSingles u).filter (fun s => slotOf u s == n) =
        (strippedSingles u).filter (fun s => p s || q s) :=
      filter_congr_mem classify
    _ = (strippedSingles u).filter p ++
        (strippedSingles u).filter q := partition
    _ = insAt u (n - 1) ++ afterAt u := by
      simp [p, q, insAt, afterAt, n, pred]

private def pullBlockAt (u : Word Nat) (i p : Nat) : PullBlock where
  letter := p
  ins := insAt u i
  gaps := gapAt u i

private def renderB (block : PullBlock) : List Nat :=
  block.letter :: (block.ins ++ block.letter :: block.gaps)

private def absorbB (block : PullBlock) : List Nat :=
  block.letter :: ((block.ins ++ block.gaps) ++ [block.letter])

/-- Every non-head-special canonical block is literally a rendered pull
block. -/
private theorem blockOf_eq_renderB (u : Word Nat) (i p : Nat)
    (regular : (i == 0 && p == u.head) = false) :
    blockOf u i p = renderB (pullBlockAt u i p) := by
  simp only [blockOf, renderB, pullBlockAt, insAt, gapAt, regular,
    Bool.false_eq_true, if_false]
  simp [List.append_assoc]

/-- The head-special block is its inside list, close, and gaps. -/
private theorem blockOf_eq_headBlock (u : Word Nat) (i p : Nat)
    (special : (i == 0 && p == u.head) = true) :
    blockOf u i p = insAt u i ++ p :: gapAt u i := by
  simp only [blockOf, insAt, gapAt, special, if_true]
  simp [List.append_assoc]

/-- Flat-mapping a list can be split at any take/drop boundary. -/
private theorem flatMap_take_append_drop {α β : Type}
    (L : List α) (k : Nat) (f : α → List β) :
    L.flatMap f = (L.take k).flatMap f ++ (L.drop k).flatMap f := by
  rw [← List.flatMap_append, List.take_append_drop]

private theorem filter_split_cons {L A B : List Nat} {x : Nat}
    (shape : L = A ++ x :: B) (q : Nat → Bool)
    (pass : q x = true) :
    L.filter q = A.filter q ++ x :: B.filter q := by
  rw [shape, List.filter_append, List.filter_cons, pass]
  rfl

/-! ## Contiguous block-index suffixes -/

/-- The `m` consecutive indices beginning at `k`. -/
private def indicesFrom : Nat → Nat → List Nat
  | _, 0 => []
  | k, m + 1 => k :: indicesFrom (k + 1) m

private theorem indicesFrom_snoc (k m : Nat) :
    indicesFrom k (m + 1) = indicesFrom k m ++ [k + m] := by
  induction m generalizing k with
  | zero => rfl
  | succ m ih =>
      change k :: indicesFrom (k + 1) (m + 1) =
        k :: (indicesFrom (k + 1) m ++ [k + (m + 1)])
      rw [ih (k := k + 1)]
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem mem_indicesFrom_bounds {k m i : Nat}
    (member : i ∈ indicesFrom k m) : k ≤ i ∧ i < k + m := by
  induction m generalizing k with
  | zero => simp [indicesFrom] at member
  | succ m ih =>
      simp only [indicesFrom, List.mem_cons] at member
      rcases member with equal | later
      · subst i
        omega
      · have bounds := ih (k := k + 1) later
        omega

private theorem range_add_indices (k m : Nat) :
    List.range (k + m) = List.range k ++ indicesFrom k m := by
  induction m with
  | zero => simp [indicesFrom]
  | succ m ih =>
      rw [Nat.add_succ, List.range_succ, ih, indicesFrom_snoc]
      simp [List.append_assoc]

private theorem range_split_indices {k n : Nat} (hk : k ≤ n) :
    List.range n = List.range k ++ indicesFrom k (n - k) := by
  have sum : k + (n - k) = n := by omega
  calc
    List.range n = List.range (k + (n - k)) :=
      congrArg List.range sum.symm
    _ = _ := range_add_indices k (n - k)

private theorem range_insert_indices {k n : Nat} (hk : k ≤ n) :
    List.range (n + 1) =
      List.range k ++ k :: indicesFrom (k + 1) (n - k) := by
  have sum : k + ((n - k) + 1) = n + 1 := by omega
  calc
    List.range (n + 1) = List.range (k + ((n - k) + 1)) :=
      congrArg List.range sum.symm
    _ = List.range k ++ indicesFrom k ((n - k) + 1) :=
      range_add_indices k ((n - k) + 1)
    _ = _ := rfl

private theorem flatMap_range_insert {α : Type} (f : Nat → List α)
    {k n : Nat} (hk : k ≤ n) :
    (List.range (n + 1)).flatMap f =
      (List.range k).flatMap f ++
        (f k ++ (indicesFrom (k + 1) (n - k)).flatMap f) := by
  rw [range_insert_indices hk, List.flatMap_append, List.flatMap_cons]

private theorem indicesFrom_map_succ (k m : Nat) :
    (indicesFrom k m).map (fun i => i + 1) =
      indicesFrom (k + 1) m := by
  induction m generalizing k with
  | zero => rfl
  | succ m ih =>
      change (k + 1) ::
          (indicesFrom (k + 1) m).map (fun i => i + 1) =
        (k + 1) :: indicesFrom ((k + 1) + 1) m
      rw [ih (k := k + 1)]

/-! ## The inserted plasma-coordinate splice -/

private theorem getD_splice_self (x d : Nat) :
    ∀ (P : List Nat) (k : Nat), k ≤ P.length →
      (P.take k ++ x :: P.drop k).getD k d = x
  | [], 0, _ => rfl
  | [], _ + 1, hk => by simp at hk
  | _ :: _, 0, _ => rfl
  | _ :: P, k + 1, hk => by
      have hk' : k ≤ P.length := by simpa using hk
      simpa using getD_splice_self x d P k hk'

private theorem getD_splice_before (x d : Nat) :
    ∀ (P : List Nat) (k i : Nat), k ≤ P.length → i < k →
      (P.take k ++ x :: P.drop k).getD i d = P.getD i d
  | [], k, i, hk, hi => by simp at hk; omega
  | _ :: _, 0, _, _, hi => by omega
  | _ :: _, _ + 1, 0, _, _ => rfl
  | _ :: P, k + 1, i + 1, hk, hi => by
      have hk' : k ≤ P.length := by simpa using hk
      have hi' : i < k := by omega
      simpa using getD_splice_before x d P k i hk' hi'

private theorem getD_splice_after (x d : Nat) :
    ∀ (P : List Nat) (k i : Nat), k ≤ P.length → k ≤ i →
      i < P.length →
      (P.take k ++ x :: P.drop k).getD (i + 1) d = P.getD i d
  | [], _, _, _, _, hi => by simp at hi
  | _ :: _, 0, _, _, _, _ => rfl
  | _ :: _, _ + 1, 0, _, hki, _ => by omega
  | _ :: P, k + 1, i + 1, hk, hki, hi => by
      have hk' : k ≤ P.length := by simpa using hk
      have hki' : k ≤ i := by omega
      have hi' : i < P.length := by simpa using hi
      simpa using getD_splice_after x d P k i hk' hki' hi'

private theorem getD_append_single_of_lt
    (L : List Nat) (x d : Nat) {i : Nat} (hi : i < L.length) :
    (L ++ [x]).getD i d = L.getD i d := by
  induction L generalizing i with
  | nil => simp at hi
  | cons a rest ih =>
      cases i with
      | zero => rfl
      | succ i =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hi
          simpa using ih hi

private theorem getD_append_single_length
    (L : List Nat) (x d : Nat) :
    (L ++ [x]).getD L.length d = x := by
  induction L with
  | nil => rfl
  | cons a rest ih => simpa using ih

private theorem getD_mem_of_lt (L : List Nat) (d : Nat) {i : Nat}
    (hi : i < L.length) : L.getD i d ∈ L := by
  induction L generalizing i with
  | nil => simp at hi
  | cons a rest ih =>
      cases i with
      | zero => simp
      | succ i =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hi
          exact List.mem_cons_of_mem _ (ih hi)

private theorem length_splice (x : Nat) :
    ∀ (P : List Nat) (k : Nat), k ≤ P.length →
      (P.take k ++ x :: P.drop k).length = P.length + 1
  | [], 0, _ => rfl
  | [], _ + 1, hk => by simp at hk
  | _ :: _, 0, _ => by simp
  | _ :: P, k + 1, hk => by
      have hk' : k ≤ P.length := by simpa using hk
      simpa using length_splice x P k hk'

private theorem pseqP_length (u : Word Nat) (x : Nat) :
    (pseqP u x).length = (plasmaSeq u).length + 1 := by
  unfold pseqP
  exact length_splice x (plasmaSeq u) (slotOf u x)
    (slotOf_le_length u x)

private theorem pseqP_getD_self (u : Word Nat) (x : Nat) :
    (pseqP u x).getD (slotOf u x) 0 = x := by
  unfold pseqP
  exact getD_splice_self x 0 (plasmaSeq u) (slotOf u x)
    (slotOf_le_length u x)

private theorem pseqP_getD_before (u : Word Nat) (x i : Nat)
    (hi : i < slotOf u x) :
    (pseqP u x).getD i 0 = (plasmaSeq u).getD i 0 := by
  unfold pseqP
  exact getD_splice_before x 0 (plasmaSeq u) (slotOf u x) i
    (slotOf_le_length u x) hi

private theorem pseqP_getD_succ (u : Word Nat) (x i : Nat)
    (lo : slotOf u x ≤ i) (hi : i < (plasmaSeq u).length) :
    (pseqP u x).getD (i + 1) 0 = (plasmaSeq u).getD i 0 := by
  unfold pseqP
  exact getD_splice_after x 0 (plasmaSeq u) (slotOf u x) i
    (slotOf_le_length u x) lo hi

private def pullSuffix (u : Word Nat) (k m : Nat) : List PullBlock :=
  (indicesFrom k m).map (fun i =>
    pullBlockAt u i ((plasmaSeq u).getD i 0))

private theorem pullSuffix_render (u : Word Nat) (k m : Nat)
    (regular : ∀ i, i ∈ indicesFrom k m →
      (i == 0 && (plasmaSeq u).getD i 0 == u.head) = false) :
    (pullSuffix u k m).flatMap renderB =
      (indicesFrom k m).flatMap (fun i =>
        blockOf u i ((plasmaSeq u).getD i 0)) := by
  simp only [pullSuffix, List.flatMap_map, Function.comp_def]
  apply flatMap_congr_mem
  intro i hi
  exact (blockOf_eq_renderB u i ((plasmaSeq u).getD i 0)
    (regular i hi)).symm

private theorem canonicalBlocks_split (u : Word Nat) (k : Nat)
    (hk : k ≤ (plasmaSeq u).length)
    (regular : ∀ i,
      i ∈ indicesFrom k ((plasmaSeq u).length - k) →
      (i == 0 && (plasmaSeq u).getD i 0 == u.head) = false) :
    (List.range (plasmaSeq u).length).flatMap (fun i =>
      blockOf u i ((plasmaSeq u).getD i 0)) =
    (List.range k).flatMap (fun i =>
      blockOf u i ((plasmaSeq u).getD i 0)) ++
    (pullSuffix u k ((plasmaSeq u).length - k)).flatMap renderB := by
  rw [range_split_indices hk, List.flatMap_append,
    ← pullSuffix_render u k ((plasmaSeq u).length - k) regular]

private def suffixShiftBlock (u : Word Nat) (x i : Nat) : List Nat :=
  blockP u x (i + 1) ((pseqP u x).getD (i + 1) 0)

private theorem suffixShift_actual (u : Word Nat) (x k m : Nat) :
    (indicesFrom k m).flatMap (suffixShiftBlock u x) =
    (indicesFrom (k + 1) m).flatMap (fun j =>
      blockP u x j ((pseqP u x).getD j 0)) := by
  rw [← indicesFrom_map_succ, List.flatMap_map]
  rfl

/-! ## Coordinate transport for a before-single -/

/-- After inserting a before-single at slot zero, the inside component
of shifted block `i+1` is the entire old slot `i+1`. -/
private theorem shiftedInsideSlice_of_before {u : Word Nat} {x i : Nat}
    (relation : rel4 u x = Rel4.before) :
    (strippedP u x).filter (fun s =>
      slotP u x s == (i + 1) + 1 && rel4P u x s == Rel4.inside) =
    (strippedSingles u).filter (fun s => slotOf u s == i + 1) := by
  have slotX := slotOf_eq_zero_of_rel_before relation
  have allX := allBefore_of_rel4_before relation
  rw [List.all_eq_true] at allX
  simp only [strippedP, List.filter_filter]
  apply filter_congr_mem
  intro s sMem
  by_cases sx : s = x
  · subst s
    simp [slotX]
  · have sIn : s ∈ u.toList := mem_toList_of_mem_singlesSeq
      (mem_singles_of_mem_stripped sMem)
    by_cases early : u.toList.idxOf s < u.toList.idxOf x
    · have allS : (plasmaSeq u).all (fun p =>
          u.toList.idxOf s < u.toList.idxOf p) = true := by
        rw [List.all_eq_true]
        intro p pMem
        have xp : u.toList.idxOf x < u.toList.idxOf p := by
          simpa using allX p pMem
        exact decide_eq_true (Nat.lt_trans early xp)
      have relS : rel4 u s = Rel4.before := by
        simp [rel4, allS]
      have slotS := slotOf_eq_zero_of_rel_before relS
      simp [sx, slotP, rel4P, early, relS, slotS]
    · have idxNe : u.toList.idxOf s ≠ u.toList.idxOf x :=
        fun equal => sx (idxOf_inj_local sIn equal)
      have late : u.toList.idxOf x < u.toList.idxOf s := by omega
      have shiftEq :
          (slotOf u s + 1 == (i + 1) + 1) =
            (slotOf u s == i + 1) := by
        apply decide_eq_decide.mpr
        omega
      simp [sx, slotP, rel4P, early, shiftEq]

/-- A shifted suffix block created by a before-single has no gap
component. -/
private theorem shiftedGapNil_of_before {u : Word Nat} {x i : Nat}
    (relation : rel4 u x = Rel4.before) :
    (strippedP u x).filter (fun s =>
      slotP u x s == (i + 1) + 1 && rel4P u x s == Rel4.gap) = [] := by
  have allX := allBefore_of_rel4_before relation
  rw [List.all_eq_true] at allX
  simp only [strippedP, List.filter_filter]
  rw [List.filter_eq_nil_iff]
  intro s sMem
  by_cases sx : s = x
  · subst s
    simp
  · by_cases early : u.toList.idxOf s < u.toList.idxOf x
    · have allS : (plasmaSeq u).all (fun p =>
          u.toList.idxOf s < u.toList.idxOf p) = true := by
        rw [List.all_eq_true]
        intro p pMem
        have xp : u.toList.idxOf x < u.toList.idxOf p := by
          simpa using allX p pMem
        exact decide_eq_true (Nat.lt_trans early xp)
      have relS : rel4 u s = Rel4.before := by
        simp [rel4, allS]
      simp [sx, slotP, rel4P, early, relS]
    · simp [sx, slotP, rel4P, early]

/-- No old gap lies at the terminal plasma slot. -/
private theorem gapAt_eq_nil_of_terminal (u : Word Nat) {i : Nat}
    (terminal : (plasmaSeq u).length = i + 1) : gapAt u i = [] := by
  unfold gapAt
  rw [List.filter_eq_nil_iff]
  intro s sMem
  by_cases atTerminal : slotOf u s = i + 1
  · have noGap := rel4_ne_gap_of_terminal_slot
      (isSingle_of_mem_stripped sMem) (by rw [terminal]; exact atTerminal)
    simp [atTerminal, noGap]
  · simp [atTerminal]

/-- A nonterminal shifted suffix block is the ordinary absorbed old
block. -/
private theorem suffixShiftBlock_eq_absorbB_before (u : Word Nat)
    (x : Nat) {i : Nat} (relation : rel4 u x = Rel4.before)
    (nonterminal : i + 1 < (plasmaSeq u).length) :
    suffixShiftBlock u x i =
      absorbB (pullBlockAt u i ((plasmaSeq u).getD i 0)) := by
  have slotX := slotOf_eq_zero_of_rel_before relation
  have get := pseqP_getD_succ u x i
    (by rw [slotX]; omega) (by omega)
  have insideRaw := shiftedInsideSlice_of_before
    (u := u) (x := x) (i := i) relation
  have insideEq : (strippedP u x).filter (fun s =>
      slotP u x s == (i + 1) + 1 && rel4P u x s == Rel4.inside) =
      insAt u i ++ gapAt u i := by
    rw [insideRaw]
    simpa using slotFilter_eq_ins_gap u (j := i + 1)
      (by omega) nonterminal
  have gapNil := shiftedGapNil_of_before
    (u := u) (x := x) (i := i) relation
  unfold suffixShiftBlock
  rw [get]
  simp only [blockP]
  rw [insideEq, gapNil]
  simp [absorbB, pullBlockAt, List.append_assoc]

/-- The terminal crossed block with its riding after-singles. -/
private def absorbLastB (block : PullBlock) (A : List Nat) : List Nat :=
  block.letter :: (((block.ins ++ block.gaps) ++ A) ++ [block.letter])

/-- The terminal shifted suffix block absorbs all old after-singles. -/
private theorem suffixShiftBlock_eq_absorbLastB_before (u : Word Nat)
    (x : Nat) {i : Nat} (relation : rel4 u x = Rel4.before)
    (terminal : (plasmaSeq u).length = i + 1) :
    suffixShiftBlock u x i =
      absorbLastB (pullBlockAt u i ((plasmaSeq u).getD i 0))
        (afterAt u) := by
  have slotX := slotOf_eq_zero_of_rel_before relation
  have nPos : 0 < (plasmaSeq u).length := by omega
  have iLt : i < (plasmaSeq u).length := by omega
  have get := pseqP_getD_succ u x i
    (by rw [slotX]; omega) iLt
  have insideRaw := shiftedInsideSlice_of_before
    (u := u) (x := x) (i := i) relation
  have insideEq : (strippedP u x).filter (fun s =>
      slotP u x s == (i + 1) + 1 && rel4P u x s == Rel4.inside) =
      insAt u i ++ afterAt u := by
    rw [insideRaw]
    simpa [terminal] using slotFilter_terminal_eq_ins_after u nPos
  have gapNil := shiftedGapNil_of_before
    (u := u) (x := x) (i := i) relation
  have oldGapNil := gapAt_eq_nil_of_terminal u terminal
  unfold suffixShiftBlock
  rw [get]
  simp only [blockP]
  rw [insideEq, gapNil]
  simp [absorbLastB, pullBlockAt, oldGapNil, terminal,
    List.append_assoc]

/-- Pull a tail-open letter close left across a list of rendered plasma
blocks.  The suffix is crossed rightmost first: the induction hypothesis
handles `rest`, then `macroCrossList` crosses the current block. -/
private theorem pullBlocks (hd : Nat) (pre : List Nat) (x : Nat) :
    ∀ (blocks : List PullBlock) (B R : List Nat),
      Derives basis
        (⟨hd,
          pre ++ x ::
            (B ++ (blocks.flatMap renderB ++ x :: R))⟩ : Word Nat)
        (⟨hd,
          pre ++ x ::
            (B ++ x :: (blocks.flatMap absorbB ++ R))⟩ : Word Nat) := by
  intro blocks
  induction blocks with
  | nil =>
      intro B R
      simpa using
        (Derives.refl
          (⟨hd, pre ++ x :: (B ++ x :: R)⟩ : Word Nat) :
            Derives basis _ _)
  | cons block rest ih =>
      intro B R
      have step1 :=
        ih (B ++ renderB block) R
      have step2 :=
        macroCrossList hd pre x B block.letter block.ins block.gaps
          (rest.flatMap absorbB ++ R)
      exact
        Derives.trans
          (by
            simpa [renderB, List.append_assoc] using step1)
          (by
            simpa [renderB, absorbB, List.append_assoc] using step2)

/-- Head-open twin of `pullBlocks`.  Here the pulled letter's open is the
word head, so each local crossing uses `macroCrossListHead`. -/
private theorem pullBlocksHead (x : Nat) :
    ∀ (blocks : List PullBlock) (B R : List Nat),
      Derives basis
        (⟨x, B ++ (blocks.flatMap renderB ++ x :: R)⟩ : Word Nat)
        (⟨x, B ++ x :: (blocks.flatMap absorbB ++ R)⟩ : Word Nat) := by
  intro blocks
  induction blocks with
  | nil =>
      intro B R
      simpa using
        (Derives.refl (⟨x, B ++ x :: R⟩ : Word Nat) :
          Derives basis _ _)
  | cons block rest ih =>
      intro B R
      have step1 :=
        ih (B ++ renderB block) R
      have step2 :=
        macroCrossListHead x B block.letter block.ins block.gaps
          (rest.flatMap absorbB ++ R)
      exact
        Derives.trans
          (by
            simpa [renderB, List.append_assoc] using step1)
          (by
            simpa [renderB, absorbB, List.append_assoc] using step2)

/-! ## Pulling across a suffix with terminal after-singles -/

/-- Render the crossed suffix after the terminal singles have ridden the
rightmost crossing.  With no crossed block, the terminal singles remain
inside the new `x`-pair. -/
private def absorbTail : List PullBlock → List Nat → List Nat
  | [], tail => tail
  | [block], tail =>
      block.letter ::
        (((block.ins ++ block.gaps) ++ tail) ++ [block.letter])
  | block :: next :: rest, tail =>
      absorbB block ++ absorbTail (next :: rest) tail

private theorem absorbTail_append_singleton :
    ∀ (blocks : List PullBlock) (block : PullBlock) (A : List Nat),
      absorbTail (blocks ++ [block]) A =
        blocks.flatMap absorbB ++ absorbLastB block A := by
  intro blocks
  induction blocks with
  | nil =>
      intro block A
      rfl
  | cons first rest ih =>
      intro block A
      cases rest with
      | nil => simp [absorbTail, absorbLastB]
      | cons next rest =>
          simpa only [List.cons_append, List.flatMap_cons, absorbTail,
            List.append_assoc] using
            congrArg (fun L => absorbB first ++ L) (ih block A)

/-- Coordinate-wise absorption of a nonempty contiguous suffix. -/
private theorem absorbTail_pullSuffix_succ
    (u : Word Nat) (x k r : Nat) (A : List Nat)
    (nonfinal : ∀ i, i ∈ indicesFrom k r →
      suffixShiftBlock u x i =
        absorbB (pullBlockAt u i ((plasmaSeq u).getD i 0)))
    (terminal : suffixShiftBlock u x (k + r) =
      absorbLastB
        (pullBlockAt u (k + r)
          ((plasmaSeq u).getD (k + r) 0)) A) :
    absorbTail (pullSuffix u k (r + 1)) A =
      (indicesFrom k (r + 1)).flatMap (suffixShiftBlock u x) := by
  simp only [pullSuffix]
  rw [indicesFrom_snoc]
  rw [List.map_append, List.map_singleton,
    absorbTail_append_singleton,
    List.flatMap_append, List.flatMap_singleton]
  simp only [List.flatMap_map, Function.comp_def]
  congr 1
  · apply flatMap_congr_mem
    intro i hi
    exact (nonfinal i hi).symm
  · exact terminal.symm

/-- Pull a tail-open close across a suffix of ordinary plasma blocks while
folding the terminal after-singles into the last crossed block.  If the
suffix is empty, those singles instead remain inside the new pair. -/
private theorem pullBlocksWithTail (hd : Nat) (pre : List Nat) (x : Nat) :
    ∀ (blocks : List PullBlock) (B tail R : List Nat),
      Derives basis
        (⟨hd,
          pre ++ x ::
            (B ++ (blocks.flatMap renderB ++ tail ++ x :: R))⟩ : Word Nat)
        (⟨hd,
          pre ++ x ::
            (B ++ match blocks with
              | [] => tail ++ x :: R
              | _ :: _ => x :: (absorbTail blocks tail ++ R))⟩ : Word Nat) := by
  intro blocks
  induction blocks with
  | nil =>
      intro B tail R
      simpa using
        (Derives.refl
          (⟨hd, pre ++ x :: (B ++ tail ++ x :: R)⟩ : Word Nat) :
            Derives basis _ _)
  | cons block rest ih =>
      intro B tail R
      cases rest with
      | nil =>
          simpa [renderB, absorbTail, List.append_assoc] using
            (macroCrossList hd pre x B block.letter block.ins
              (block.gaps ++ tail) R)
      | cons next rest =>
          have step1 := ih (B ++ renderB block) tail R
          have step2 :=
            macroCrossList hd pre x B block.letter block.ins block.gaps
              (absorbTail (next :: rest) tail ++ R)
          exact
            Derives.trans
              (by
                simpa [renderB, List.append_assoc] using step1)
              (by
                simpa [renderB, absorbB, absorbTail, List.append_assoc]
                  using step2)

/-- Head-open twin of `pullBlocksWithTail`. -/
private theorem pullBlocksWithTailHead (x : Nat) :
    ∀ (blocks : List PullBlock) (B tail R : List Nat),
      Derives basis
        (⟨x, B ++ (blocks.flatMap renderB ++ tail ++ x :: R)⟩ : Word Nat)
        (⟨x,
          B ++ match blocks with
            | [] => tail ++ x :: R
            | _ :: _ => x :: (absorbTail blocks tail ++ R)⟩ : Word Nat) := by
  intro blocks
  induction blocks with
  | nil =>
      intro B tail R
      simpa using
        (Derives.refl (⟨x, B ++ tail ++ x :: R⟩ : Word Nat) :
          Derives basis _ _)
  | cons block rest ih =>
      intro B tail R
      cases rest with
      | nil =>
          simpa [renderB, absorbTail, List.append_assoc] using
            (macroCrossListHead x B block.letter block.ins
              (block.gaps ++ tail) R)
      | cons next rest =>
          have step1 := ih (B ++ renderB block) tail R
          have step2 :=
            macroCrossListHead x B block.letter block.ins block.gaps
              (absorbTail (next :: rest) tail ++ R)
          exact
            Derives.trans
              (by
                simpa [renderB, List.append_assoc] using step1)
              (by
                simpa [renderB, absorbB, absorbTail, List.append_assoc]
                  using step2)

/-! ## Second-occurrence insertion: the terminal-after branch -/

/-- When the new plasma letter was an after-single, formula F is already
the old canonical word with the second occurrence appended. -/
private theorem canonicalize_append_second_after {h x : Nat} {T : List Nat}
    (single : List.count x (h :: T) = 1)
    (relation : rel4 (⟨h, T⟩ : Word Nat) x = Rel4.after) :
    canonicalize (⟨h, T⟩ : Word Nat) ++ Word.singleton x =
      canonicalizeP (⟨h, T⟩ : Word Nat) x := by
  let u : Word Nat := ⟨h, T⟩
  let P : List Nat := plasmaSeq u
  let S : List Nat := strippedSingles u
  let n : Nat := P.length
  have singleU : IsSingle u x := by
    change u.toList.count x = 1
    simpa [u] using single
  have relationU : rel4 u x = Rel4.after := by
    simpa [u] using relation
  have pNonempty : P ≠ [] := by
    intro empty
    have plasmaEmpty : plasmaSeq u = [] := by simpa [P] using empty
    have before := rel4_of_plasma_nil (u := u) (s := x) plasmaEmpty
    rw [before] at relationU
    cases relationU
  have nPos : 0 < n := by
    exact List.length_pos_iff.mpr pNonempty
  have headNe : h ≠ x := by
    intro equal
    subst x
    have afterAll := allAfter_of_rel4_after relationU
    rw [List.all_eq_true] at afterAll
    obtain ⟨p, rest, shape⟩ := List.exists_cons_of_ne_nil pNonempty
    have pMem : p ∈ P := by rw [shape]; simp
    have closed : lastIdxOf u.toList p < u.toList.idxOf h := by
      have pMem' : p ∈ plasmaSeq u := by simpa [P] using pMem
      simpa using afterAll p pMem'
    have headIdx : u.toList.idxOf h = 0 := by
      change (h :: T).idxOf h = 0
      simp
    omega
  obtain ⟨A, B, splitRaw, left, right⟩ :=
    strippedSingles_split_single single headNe
  have split : S = A ++ x :: B := by
    simpa [S, u] using splitRaw
  have splitU : strippedSingles u = A ++ x :: B := by
    simpa [S] using split
  have leftU : ∀ a, a ∈ A →
      u.toList.idxOf a < u.toList.idxOf x := by
    intro a aMem
    simpa [u] using left a aMem
  have rightU : ∀ b, b ∈ B →
      u.toList.idxOf x < u.toList.idxOf b := by
    intro b bMem
    simpa [u] using right b bMem
  have slotX : slotOf u x = n := by
    simpa [n, P] using slotOf_eq_length_of_rel_after relationU
  have xNotA : x ∉ A := by
    intro member
    have order := leftU x member
    omega
  have xNotB : x ∉ B := by
    intro member
    have order := rightU x member
    omega
  have keepA : A.filter (fun e => !(e == x)) = A := by
    rw [List.filter_eq_self]
    intro a aMem
    have ne : a ≠ x := by
      intro equal
      exact xNotA (equal ▸ aMem)
    simp [ne]
  have keepB : B.filter (fun e => !(e == x)) = B := by
    rw [List.filter_eq_self]
    intro b bMem
    have ne : b ≠ x := by
      intro equal
      exact xNotB (equal ▸ bMem)
    simp [ne]
  have stripPEq : strippedP u x = A ++ B := by
    simp only [strippedP, splitU, List.filter_append, List.filter_cons]
    rw [keepA, keepB]
    simp
  have singleS : ∀ s, s ∈ S → IsSingle u s := by
    intro s sMem
    have raw := (List.mem_filter.mp
      (mem_singles_of_mem_stripped (by simpa [S] using sMem))).2
    change u.toList.count s = 1
    exact eq_of_beq raw
  have singleA : ∀ a, a ∈ A → IsSingle u a := by
    intro a aMem
    apply singleS
    rw [split]
    simp [aMem]
  have relB : ∀ b, b ∈ B → rel4 u b = Rel4.after := by
    intro b bMem
    exact rel4_after_of_later relationU (rightU b bMem)
  have slotB : ∀ b, b ∈ B → slotOf u b = n := by
    intro b bMem
    simpa [n, P] using slotOf_eq_length_of_rel_after (relB b bMem)
  have slotPA : ∀ a, a ∈ A → slotP u x a = slotOf u a := by
    intro a aMem
    rw [slotP, if_pos (leftU a aMem)]
  have relPA : ∀ a, a ∈ A → rel4P u x a =
      (if rel4 u a = Rel4.after then Rel4.gap else rel4 u a) := by
    intro a aMem
    rw [rel4P, if_pos (leftU a aMem)]
  have slotPB : ∀ b, b ∈ B → slotP u x b = n + 1 := by
    intro b bMem
    rw [slotP, if_neg (by
      have later := rightU b bMem
      omega : ¬ u.toList.idxOf b < u.toList.idxOf x), slotB b bMem]
  have relPB : ∀ b, b ∈ B → rel4P u x b = Rel4.inside := by
    intro b bMem
    rw [rel4P, if_neg (by
      have later := rightU b bMem
      omega : ¬ u.toList.idxOf b < u.toList.idxOf x)]
  have pseqPEq : pseqP u x = P ++ [x] := by
    simp [pseqP, slotX, n, P]
  have oldAfters :
      S.filter (fun s => slotOf u s == n && rel4 u s == Rel4.after) =
        A.filter (fun s => rel4 u s == Rel4.after) ++ x :: B := by
    rw [split, List.filter_append, List.filter_cons]
    have leftEq : A.filter
        (fun s => slotOf u s == n && rel4 u s == Rel4.after) =
        A.filter (fun s => rel4 u s == Rel4.after) := by
      apply filter_congr_mem
      intro a aMem
      by_cases rel : rel4 u a = Rel4.after
      · rw [slotOf_eq_length_of_rel_after rel]
        simp [rel, n, P]
      · simp [rel]
    have xPass :
        (slotOf u x == n && rel4 u x == Rel4.after) = true := by
      rw [slotX, relationU]
      simp
    have rightSelf : B.filter
        (fun s => slotOf u s == n && rel4 u s == Rel4.after) = B := by
      rw [List.filter_eq_self]
      intro b bMem
      rw [slotB b bMem, relB b bMem]
      simp
    rw [leftEq, xPass, rightSelf]
    simp
  have newAfters : (A ++ B).filter (fun s =>
      slotP u x s == n + 1 && rel4P u x s == Rel4.after) = [] := by
    rw [List.filter_eq_nil_iff]
    intro s sMem
    rcases List.mem_append.mp sMem with inA | inB
    · have relFalse : (rel4P u x s == Rel4.after) = false := by
        rw [relPA s inA]
        cases rel : rel4 u s <;> simp [rel]
      rw [relFalse]
      simp
    · rw [relPB s inB]
      simp
  have beforeA : A.filter (fun s => slotP u x s == 0) =
      A.filter (fun s => slotOf u s == 0) := by
    apply filter_congr_mem
    intro a aMem
    rw [slotPA a aMem]
  have beforeBNew : B.filter (fun s => slotP u x s == 0) = [] := by
    rw [List.filter_eq_nil_iff]
    intro b bMem
    rw [slotPB b bMem]
    simp
  have beforeBOld : B.filter (fun s => slotOf u s == 0) = [] := by
    rw [List.filter_eq_nil_iff]
    intro b bMem
    rw [slotB b bMem]
    simp [Nat.ne_of_gt nPos]
  have beforeX : (slotOf u x == 0) = false := by
    rw [slotX]
    simp [Nat.ne_of_gt nPos]
  have beforesEq : (A ++ B).filter (fun s => slotP u x s == 0) =
      S.filter (fun s => slotOf u s == 0) := by
    rw [split, List.filter_append, List.filter_append, List.filter_cons,
      beforeA, beforeBNew, beforeBOld, beforeX]
    simp
  have blockBefore : ∀ i p, i + 1 < n →
      blockP u x i p = blockOf u i p := by
    intro i p hi
    have insA : A.filter (fun s =>
        slotP u x s == i + 1 && rel4P u x s == Rel4.inside) =
        A.filter (fun s =>
          slotOf u s == i + 1 && rel4 u s == Rel4.inside) := by
      apply filter_congr_mem
      intro a aMem
      rw [slotPA a aMem, relPA a aMem]
      cases rel : rel4 u a <;> simp [rel]
    have insBNew : B.filter (fun s =>
        slotP u x s == i + 1 && rel4P u x s == Rel4.inside) = [] := by
      rw [List.filter_eq_nil_iff]
      intro b bMem
      rw [slotPB b bMem, relPB b bMem]
      have ne : n ≠ i := by omega
      simp [ne]
    have insBOld : B.filter (fun s =>
        slotOf u s == i + 1 && rel4 u s == Rel4.inside) = [] := by
      rw [List.filter_eq_nil_iff]
      intro b bMem
      rw [relB b bMem]
      simp
    have insX :
        (slotOf u x == i + 1 && rel4 u x == Rel4.inside) = false := by
      rw [relationU]
      simp
    have insEq : (A ++ B).filter (fun s =>
        slotP u x s == i + 1 && rel4P u x s == Rel4.inside) =
        S.filter (fun s =>
          slotOf u s == i + 1 && rel4 u s == Rel4.inside) := by
      rw [split, List.filter_append, List.filter_append, List.filter_cons,
        insA, insBNew, insBOld, insX]
      simp
    have gapA : A.filter (fun s =>
        slotP u x s == i + 1 && rel4P u x s == Rel4.gap) =
        A.filter (fun s =>
          slotOf u s == i + 1 && rel4 u s == Rel4.gap) := by
      apply filter_congr_mem
      intro a aMem
      rw [slotPA a aMem, relPA a aMem]
      by_cases rel : rel4 u a = Rel4.after
      · have slot := slotOf_eq_length_of_rel_after rel
        have ne : n ≠ i + 1 := by omega
        simp [rel, slot, n, P, ne]
      · simp [rel]
    have gapBNew : B.filter (fun s =>
        slotP u x s == i + 1 && rel4P u x s == Rel4.gap) = [] := by
      rw [List.filter_eq_nil_iff]
      intro b bMem
      rw [slotPB b bMem, relPB b bMem]
      simp
    have gapBOld : B.filter (fun s =>
        slotOf u s == i + 1 && rel4 u s == Rel4.gap) = [] := by
      rw [List.filter_eq_nil_iff]
      intro b bMem
      rw [relB b bMem]
      simp
    have gapX :
        (slotOf u x == i + 1 && rel4 u x == Rel4.gap) = false := by
      rw [relationU]
      simp
    have gapEq : (A ++ B).filter (fun s =>
        slotP u x s == i + 1 && rel4P u x s == Rel4.gap) =
        S.filter (fun s =>
          slotOf u s == i + 1 && rel4 u s == Rel4.gap) := by
      rw [split, List.filter_append, List.filter_append, List.filter_cons,
        gapA, gapBNew, gapBOld, gapX]
      simp
    simp only [blockP, blockOf]
    rw [stripPEq, insEq, gapEq]
  have oldTerminalGaps : S.filter (fun s =>
      slotOf u s == n && rel4 u s == Rel4.gap) = [] := by
    rw [List.filter_eq_nil_iff]
    intro s sMem
    by_cases terminal : slotOf u s = n
    · have noGap : rel4 u s ≠ Rel4.gap :=
        rel4_ne_gap_of_terminal_slot (singleS s sMem)
          (by simpa [n, P] using terminal)
      simp [terminal, noGap]
    · simp [terminal]
  have blockLast : ∀ k, n = k + 1 →
      blockP u x k (P.getD k 0) =
        blockOf u k (P.getD k 0) ++
          A.filter (fun s => rel4 u s == Rel4.after) := by
    intro k nk
    have insA : A.filter (fun s =>
        slotP u x s == n && rel4P u x s == Rel4.inside) =
        A.filter (fun s =>
          slotOf u s == n && rel4 u s == Rel4.inside) := by
      apply filter_congr_mem
      intro a aMem
      rw [slotPA a aMem, relPA a aMem]
      cases rel : rel4 u a <;> simp [rel]
    have insBNew : B.filter (fun s =>
        slotP u x s == n && rel4P u x s == Rel4.inside) = [] := by
      rw [List.filter_eq_nil_iff]
      intro b bMem
      rw [slotPB b bMem]
      simp
    have insBOld : B.filter (fun s =>
        slotOf u s == n && rel4 u s == Rel4.inside) = [] := by
      rw [List.filter_eq_nil_iff]
      intro b bMem
      rw [relB b bMem]
      simp
    have insX :
        (slotOf u x == n && rel4 u x == Rel4.inside) = false := by
      rw [relationU]
      simp
    have insEq : (A ++ B).filter (fun s =>
        slotP u x s == n && rel4P u x s == Rel4.inside) =
        S.filter (fun s =>
          slotOf u s == n && rel4 u s == Rel4.inside) := by
      rw [split, List.filter_append, List.filter_append, List.filter_cons,
        insA, insBNew, insBOld, insX]
      simp
    have gapA : A.filter (fun s =>
        slotP u x s == n && rel4P u x s == Rel4.gap) =
        A.filter (fun s => rel4 u s == Rel4.after) := by
      apply filter_congr_mem
      intro a aMem
      rw [slotPA a aMem, relPA a aMem]
      cases relEq : rel4 u a with
      | before => simp [relEq]
      | after =>
          have slot := slotOf_eq_length_of_rel_after relEq
          simp [relEq, slot, n, P]
      | inside => simp [relEq]
      | gap =>
          have slotNe : slotOf u a ≠ n := by
            intro terminal
            exact rel4_ne_gap_of_terminal_slot (singleA a aMem)
              (by simpa [n, P] using terminal) relEq
          simp [relEq, slotNe]
    have gapB : B.filter (fun s =>
        slotP u x s == n && rel4P u x s == Rel4.gap) = [] := by
      rw [List.filter_eq_nil_iff]
      intro b bMem
      rw [relPB b bMem]
      simp
    have gapEq : (A ++ B).filter (fun s =>
        slotP u x s == n && rel4P u x s == Rel4.gap) =
        A.filter (fun s => rel4 u s == Rel4.after) := by
      rw [List.filter_append, gapA, gapB]
      simp
    simp only [blockP, blockOf]
    rw [← nk, stripPEq, insEq, gapEq, oldTerminalGaps]
    simp [S, List.append_assoc]
  have blockNew : blockP u x n x = x :: (B ++ [x]) := by
    have insANil : A.filter (fun s =>
        slotP u x s == n + 1 && rel4P u x s == Rel4.inside) = [] := by
      rw [List.filter_eq_nil_iff]
      intro a aMem
      rw [slotPA a aMem]
      have bound : slotOf u a ≤ n := by
        simpa [n, P] using slotOf_le_length u a
      have ne : slotOf u a ≠ n + 1 := by omega
      simp [ne]
    have insBSelf : B.filter (fun s =>
        slotP u x s == n + 1 && rel4P u x s == Rel4.inside) = B := by
      rw [List.filter_eq_self]
      intro b bMem
      rw [slotPB b bMem, relPB b bMem]
      simp
    have insEq : (A ++ B).filter (fun s =>
        slotP u x s == n + 1 && rel4P u x s == Rel4.inside) = B := by
      rw [List.filter_append, insANil, insBSelf]
      simp
    have gapNil : (A ++ B).filter (fun s =>
        slotP u x s == n + 1 && rel4P u x s == Rel4.gap) = [] := by
      rw [List.filter_eq_nil_iff]
      intro s sMem
      rcases List.mem_append.mp sMem with inA | inB
      · rw [slotPA s inA]
        have bound : slotOf u s ≤ n := by
          simpa [n, P] using slotOf_le_length u s
        have ne : slotOf u s ≠ n + 1 := by omega
        simp [ne]
      · rw [relPB s inB]
        simp
    simp only [blockP]
    rw [stripPEq, insEq, gapNil]
    have nNe : (n == 0) = false := by simp [Nat.ne_of_gt nPos]
    rw [nNe]
    simp [List.append_assoc]
  let k : Nat := n - 1
  have oneLe : 1 ≤ n := nPos
  have nk : n = k + 1 := by
    dsimp [k]
    exact (Nat.sub_add_cancel oneLe).symm
  have getOld : ∀ i, i < n →
      (P ++ [x]).getD i 0 = P.getD i 0 := by
    intro i hi
    exact getD_append_single_of_lt P x 0 (by simpa [n] using hi)
  have getNew : (P ++ [x]).getD n 0 = x := by
    simpa [n] using getD_append_single_length P x 0
  have prefixBlocks :
      (List.range k).flatMap
          (fun i => blockP u x i ((P ++ [x]).getD i 0)) =
      (List.range k).flatMap
          (fun i => blockOf u i (P.getD i 0)) := by
    apply flatMap_congr_mem
    intro i iMem
    have ik : i < k := List.mem_range.mp iMem
    rw [getOld i (by omega)]
    exact blockBefore i _ (by omega)
  have oldAftersP :
      S.filter (fun s =>
        slotOf u s == P.length && rel4 u s == Rel4.after) =
        A.filter (fun s => rel4 u s == Rel4.after) ++ x :: B := by
    simpa [n] using oldAfters
  have blocksEq :
      (List.range (pseqP u x).length).flatMap
          (fun i => blockP u x i ((pseqP u x).getD i 0)) =
      (List.range P.length).flatMap
          (fun i => blockOf u i (P.getD i 0)) ++
        S.filter (fun s =>
          slotOf u s == P.length && rel4 u s == Rel4.after) ++ [x] := by
    rw [pseqPEq]
    have rangeN : List.range n = List.range k ++ [k] := by
      rw [nk, List.range_succ]
    have rangeNp : List.range (n + 1) = List.range n ++ [n] := by
      rw [List.range_succ]
    have lenNew : (P ++ [x]).length = n + 1 := by simp [n]
    have lenOld : P.length = n := rfl
    rw [lenNew, lenOld, rangeNp, rangeN]
    simp only [List.flatMap_append, List.flatMap_singleton]
    rw [prefixBlocks, getOld k (by omega), getNew,
      blockLast k nk, blockNew, oldAftersP]
    simp [List.append_assoc]
  have beforesEq' :
      (strippedP u x).filter (fun s => slotP u x s == 0) =
        S.filter (fun s => slotOf u s == 0) := by
    rw [stripPEq]
    exact beforesEq
  have newAftersP :
      (strippedP u x).filter (fun s =>
        slotP u x s == (pseqP u x).length &&
          rel4P u x s == Rel4.after) = [] := by
    rw [stripPEq, pseqPEq]
    simpa [n] using newAfters
  change canonicalize u ++ Word.singleton x = canonicalizeP u x
  rw [append_mk]
  simp only [canonicalizeP, canonicalize]
  congr 1
  rw [beforesEq', blocksEq, newAftersP]
  simp [P, S, List.append_assoc]

private theorem derivesInsertSecondAfter {h x : Nat} {T : List Nat}
    (single : List.count x (h :: T) = 1)
    (relation : rel4 (⟨h, T⟩ : Word Nat) x = Rel4.after) :
    Derives basis
      (canonicalize (⟨h, T⟩ : Word Nat) ++ Word.singleton x)
      (canonicalizeP (⟨h, T⟩ : Word Nat) x) := by
  rw [canonicalize_append_second_after single relation]
  exact Derives.refl _

/-! ## Second-occurrence insertion: the gap branch -/

/-- Pull the new close across the suffix when its old occurrence was a
gap-single. -/
private theorem derivesInsertSecondGap {h x : Nat} {T : List Nat}
    (single : List.count x (h :: T) = 1)
    (relation : rel4 (⟨h, T⟩ : Word Nat) x = Rel4.gap) :
    Derives basis
      (canonicalize (⟨h, T⟩ : Word Nat) ++ Word.singleton x)
      (canonicalizeP (⟨h, T⟩ : Word Nat) x) := by
  let u : Word Nat := ⟨h, T⟩
  let P : List Nat := plasmaSeq u
  let S : List Nat := strippedSingles u
  let n : Nat := P.length
  let k : Nat := slotOf u x
  have singleU : IsSingle u x := by
    change u.toList.count x = 1
    simpa [u] using single
  have relationU : rel4 u x = Rel4.gap := by
    simpa [u] using relation
  have kPos : 0 < k := by
    apply slotOf_pos_of_single_rel_ne_before singleU
    intro before
    rw [before] at relationU
    cases relationU
  have kLe : k ≤ n := by
    simpa [k, n, P] using slotOf_le_length u x
  have kLt : k < n := by
    by_cases kn : k = n
    · have terminal : slotOf u x = (plasmaSeq u).length := by
        simpa [k, n, P] using kn
      exact False.elim
        (rel4_ne_gap_of_terminal_slot singleU terminal relationU)
    · omega
  have nPos : 0 < n := by omega
  have headNe : h ≠ x := by
    intro equal
    subst x
    have allFail : ∀ p, p ∈ plasmaSeq u →
        decide (u.toList.idxOf p < u.toList.idxOf h) = false := by
      intro p _
      have headIdx : u.toList.idxOf h = 0 := by
        change (h :: T).idxOf h = 0
        simp
      rw [headIdx]
      exact decide_eq_false (by omega)
    have zero : slotOf u h = 0 := by
      unfold slotOf
      rw [takeWhile_eq_nil_of_all_false allFail]
      rfl
    change 0 < slotOf u h at kPos
    omega
  obtain ⟨A, B, splitRaw, left, right⟩ :=
    strippedSingles_split_single single headNe
  have splitU : strippedSingles u = A ++ x :: B := by
    simpa [u] using splitRaw
  have split : S = A ++ x :: B := by
    simpa [S] using splitU
  have leftU : ∀ a, a ∈ A →
      u.toList.idxOf a < u.toList.idxOf x := by
    intro a aMem
    simpa [u] using left a aMem
  have rightU : ∀ b, b ∈ B →
      u.toList.idxOf x < u.toList.idxOf b := by
    intro b bMem
    simpa [u] using right b bMem
  have slotX : slotOf u x = k := rfl
  have slotA : ∀ a, a ∈ A → slotOf u a ≤ k := by
    intro a aMem
    exact slotOf_mono_of_idx_le (Nat.le_of_lt (leftU a aMem))
  have slotB : ∀ b, b ∈ B → k ≤ slotOf u b := by
    intro b bMem
    exact slotOf_mono_of_idx_le (Nat.le_of_lt (rightU b bMem))
  have xNotA : x ∉ A := by
    intro member
    have order := leftU x member
    omega
  have xNotB : x ∉ B := by
    intro member
    have order := rightU x member
    omega
  have stripPEq : strippedP u x = A ++ B := by
    simp only [strippedP, splitU, List.filter_append, List.filter_cons]
    have keepA : A.filter (fun e => !(e == x)) = A := by
      rw [List.filter_eq_self]
      intro a aMem
      have ne : a ≠ x := fun equal => xNotA (equal ▸ aMem)
      simp [ne]
    have keepB : B.filter (fun e => !(e == x)) = B := by
      rw [List.filter_eq_self]
      intro b bMem
      have ne : b ≠ x := fun equal => xNotB (equal ▸ bMem)
      simp [ne]
    rw [keepA, keepB]
    simp
  have singleS : ∀ s, s ∈ S → IsSingle u s := by
    intro s sMem
    apply isSingle_of_mem_stripped
    simpa [S] using sMem
  have singleA : ∀ a, a ∈ A → IsSingle u a := by
    intro a aMem
    apply singleS a
    rw [split]
    simp [aMem]
  have singleB : ∀ b, b ∈ B → IsSingle u b := by
    intro b bMem
    apply singleS b
    rw [split]
    simp [bMem]
  have slotPA : ∀ a, a ∈ A → slotP u x a = slotOf u a := by
    intro a aMem
    rw [slotP, if_pos (leftU a aMem)]
  have relPA : ∀ a, a ∈ A → rel4P u x a =
      (if rel4 u a = Rel4.after then Rel4.gap else rel4 u a) := by
    intro a aMem
    rw [rel4P, if_pos (leftU a aMem)]
  have slotPB : ∀ b, b ∈ B → slotP u x b = slotOf u b + 1 := by
    intro b bMem
    rw [slotP, if_neg (by have := rightU b bMem; omega)]
  have relPB : ∀ b, b ∈ B → rel4P u x b = Rel4.inside := by
    intro b bMem
    rw [rel4P, if_neg (by have := rightU b bMem; omega)]
  let j : Nat := k - 1
  have jk : j + 1 = k := by
    dsimp [j]
    omega
  let q : Nat := P.getD j 0
  let gx : Nat → Bool := fun s =>
    slotOf u s == k && rel4 u s == Rel4.gap
  let GL : List Nat := A.filter gx
  let GR : List Nat := B.filter gx
  let stem : List Nat :=
    if j == 0 && q == u.head then insAt u j ++ [q]
    else q :: insAt u j ++ [q]
  let pre : List Nat :=
    beforeAt u ++
      (List.range j).flatMap (fun i => blockOf u i (P.getD i 0)) ++
      stem ++ GL
  let bs : List PullBlock := pullSuffix u k (n - k)
  have gapPivot : gapAt u j = GL ++ x :: GR := by
    have pass : gx x = true := by
      simp [gx, slotX, relationU]
    have raw := filter_split_cons (L := strippedSingles u)
      (A := A) (B := B) (x := x) splitU gx pass
    unfold gapAt
    rw [jk]
    change (strippedSingles u).filter gx = GL ++ x :: GR
    simpa [GL, GR] using raw
  have blockPivotOld : blockOf u j q = stem ++ GL ++ x :: GR := by
    simp only [blockOf]
    change
      ((if j == 0 && q == u.head then insAt u j ++ [q]
        else q :: insAt u j ++ [q]) ++ gapAt u j) = _
    rw [gapPivot]
    simp [stem, List.append_assoc]
  have beforesEq :
      (strippedP u x).filter (fun s => slotP u x s == 0) =
        beforeAt u := by
    have aEq : A.filter (fun s => slotP u x s == 0) =
        A.filter (fun s => slotOf u s == 0) := by
      apply filter_congr_mem
      intro a aMem
      rw [slotPA a aMem]
    have bNew : B.filter (fun s => slotP u x s == 0) = [] := by
      rw [List.filter_eq_nil_iff]
      intro b bMem
      rw [slotPB b bMem]
      simp
    have bOld : B.filter (fun s => slotOf u s == 0) = [] := by
      rw [List.filter_eq_nil_iff]
      intro b bMem
      have bound := slotB b bMem
      have ne : slotOf u b ≠ 0 := by omega
      simp [ne]
    have xOld : (slotOf u x == 0) = false := by
      rw [slotX]
      simp [Nat.ne_of_gt kPos]
    simp only [beforeAt]
    rw [stripPEq, List.filter_append, aEq, bNew,
      splitU, List.filter_append, List.filter_cons, bOld, xOld]
    simp
  have blockEarly : ∀ i p, i + 1 < k →
      blockP u x i p = blockOf u i p := by
    intro i p hi
    have insA : A.filter (fun s =>
        slotP u x s == i + 1 && rel4P u x s == Rel4.inside) =
        A.filter (fun s =>
          slotOf u s == i + 1 && rel4 u s == Rel4.inside) := by
      apply filter_congr_mem
      intro a aMem
      rw [slotPA a aMem, relPA a aMem]
      cases rel : rel4 u a <;> simp [rel]
    have insBNew : B.filter (fun s =>
        slotP u x s == i + 1 && rel4P u x s == Rel4.inside) = [] := by
      rw [List.filter_eq_nil_iff]
      intro b bMem
      rw [slotPB b bMem, relPB b bMem]
      have bound := slotB b bMem
      have ne : slotOf u b ≠ i := by omega
      simp [ne]
    have insBOld : B.filter (fun s =>
        slotOf u s == i + 1 && rel4 u s == Rel4.inside) = [] := by
      rw [List.filter_eq_nil_iff]
      intro b bMem
      have bound := slotB b bMem
      have ne : slotOf u b ≠ i + 1 := by omega
      simp [ne]
    have insX :
        (slotOf u x == i + 1 && rel4 u x == Rel4.inside) = false := by
      rw [relationU]
      simp
    have insEq : (A ++ B).filter (fun s =>
        slotP u x s == i + 1 && rel4P u x s == Rel4.inside) =
        S.filter (fun s =>
          slotOf u s == i + 1 && rel4 u s == Rel4.inside) := by
      rw [split, List.filter_append, List.filter_append, List.filter_cons,
        insA, insBNew, insBOld, insX]
      simp
    have gapA : A.filter (fun s =>
        slotP u x s == i + 1 && rel4P u x s == Rel4.gap) =
        A.filter (fun s =>
          slotOf u s == i + 1 && rel4 u s == Rel4.gap) := by
      apply filter_congr_mem
      intro a aMem
      rw [slotPA a aMem, relPA a aMem]
      cases rel : rel4 u a with
      | before => simp [rel]
      | after =>
          have terminal := slotOf_eq_length_of_rel_after rel
          have ne : n ≠ i + 1 := by omega
          simp [rel, terminal, n, P, ne]
      | inside => simp [rel]
      | gap => simp [rel]
    have gapBNew : B.filter (fun s =>
        slotP u x s == i + 1 && rel4P u x s == Rel4.gap) = [] := by
      rw [List.filter_eq_nil_iff]
      intro b bMem
      rw [relPB b bMem]
      simp
    have gapBOld : B.filter (fun s =>
        slotOf u s == i + 1 && rel4 u s == Rel4.gap) = [] := by
      rw [List.filter_eq_nil_iff]
      intro b bMem
      have bound := slotB b bMem
      have ne : slotOf u b ≠ i + 1 := by omega
      simp [ne]
    have gapX :
        (slotOf u x == i + 1 && rel4 u x == Rel4.gap) = false := by
      rw [slotX]
      have ne : k ≠ i + 1 := by omega
      simp [ne]
    have gapEq : (A ++ B).filter (fun s =>
        slotP u x s == i + 1 && rel4P u x s == Rel4.gap) =
        S.filter (fun s =>
          slotOf u s == i + 1 && rel4 u s == Rel4.gap) := by
      rw [split, List.filter_append, List.filter_append, List.filter_cons,
        gapA, gapBNew, gapBOld, gapX]
      simp
    simp only [blockP, blockOf]
    rw [stripPEq, insEq, gapEq]
  have oldInsB : B.filter (fun s =>
      slotOf u s == k && rel4 u s == Rel4.inside) = [] := by
    rw [List.filter_eq_nil_iff]
    intro b bMem
    by_cases pass :
        (slotOf u b == k && rel4 u b == Rel4.inside) = true
    · have data : (slotOf u b == k) = true ∧
          (rel4 u b == Rel4.inside) = true := by
        simpa only [Bool.and_eq_true] using pass
      have bSlot : slotOf u b = k := eq_of_beq data.1
      have bInside : rel4 u b = Rel4.inside := eq_of_beq data.2
      have reverse := inside_before_same_slot_gap
        (singleB b bMem) singleU bInside relationU
        (by rw [bSlot, slotX])
      have forward := rightU b bMem
      omega
    · exact pass
  have pivotInside : (strippedP u x).filter (fun s =>
      slotP u x s == k && rel4P u x s == Rel4.inside) = insAt u j := by
    have newA : A.filter (fun s =>
        slotP u x s == k && rel4P u x s == Rel4.inside) =
        A.filter (fun s =>
          slotOf u s == k && rel4 u s == Rel4.inside) := by
      apply filter_congr_mem
      intro a aMem
      rw [slotPA a aMem, relPA a aMem]
      cases rel : rel4 u a <;> simp [rel]
    have newB : B.filter (fun s =>
        slotP u x s == k && rel4P u x s == Rel4.inside) = [] := by
      rw [List.filter_eq_nil_iff]
      intro b bMem
      rw [slotPB b bMem]
      have bound := slotB b bMem
      have ne : slotOf u b + 1 ≠ k := by omega
      simp [ne]
    unfold insAt
    rw [jk, stripPEq, List.filter_append, newA, newB,
      splitU, List.filter_append, List.filter_cons, oldInsB]
    rw [relationU]
    simp
  have pivotGap : (strippedP u x).filter (fun s =>
      slotP u x s == k && rel4P u x s == Rel4.gap) = GL := by
    have newA : A.filter (fun s =>
        slotP u x s == k && rel4P u x s == Rel4.gap) = GL := by
      change A.filter (fun s =>
        slotP u x s == k && rel4P u x s == Rel4.gap) = A.filter gx
      apply filter_congr_mem
      intro a aMem
      rw [slotPA a aMem, relPA a aMem]
      cases rel : rel4 u a with
      | before => simp [gx, rel]
      | after =>
          have terminal := slotOf_eq_length_of_rel_after rel
          have ne : n ≠ k := by omega
          simp [gx, rel, terminal, n, P, ne]
      | inside => simp [gx, rel]
      | gap => simp [gx, rel]
    have newB : B.filter (fun s =>
        slotP u x s == k && rel4P u x s == Rel4.gap) = [] := by
      rw [List.filter_eq_nil_iff]
      intro b bMem
      rw [relPB b bMem]
      simp
    rw [stripPEq, List.filter_append, newA, newB]
    simp
  have blockPivotNew : blockP u x j q = stem ++ GL := by
    simp only [blockP]
    rw [jk, pivotInside, pivotGap]
  have bSlotGap : B.filter (fun s => slotOf u s == k) = GR := by
    change B.filter (fun s => slotOf u s == k) = B.filter gx
    apply filter_congr_mem
    intro b bMem
    by_cases atK : slotOf u b = k
    · have bGap : rel4 u b = Rel4.gap := by
        cases rel : rel4 u b with
        | before =>
            have zero := slotOf_eq_zero_of_rel_before rel
            omega
        | after =>
            exfalso
            have terminal := slotOf_eq_length_of_rel_after rel
            have kn : k = n := by
              calc
                k = slotOf u b := atK.symm
                _ = (plasmaSeq u).length := terminal
                _ = n := by simp [n, P]
            omega
        | inside =>
            have reverse := inside_before_same_slot_gap
              (singleB b bMem) singleU rel relationU
              (by rw [atK, slotX])
            have forward := rightU b bMem
            omega
        | gap => exact rfl
      simp [gx, atK, bGap]
    · simp [gx, atK]
  have insertedInside : (strippedP u x).filter (fun s =>
      slotP u x s == k + 1 && rel4P u x s == Rel4.inside) = GR := by
    have newA : A.filter (fun s =>
        slotP u x s == k + 1 && rel4P u x s == Rel4.inside) = [] := by
      rw [List.filter_eq_nil_iff]
      intro a aMem
      rw [slotPA a aMem]
      have bound := slotA a aMem
      have ne : slotOf u a ≠ k + 1 := by omega
      simp [ne]
    have newB : B.filter (fun s =>
        slotP u x s == k + 1 && rel4P u x s == Rel4.inside) =
        B.filter (fun s => slotOf u s == k) := by
      apply filter_congr_mem
      intro b bMem
      rw [slotPB b bMem, relPB b bMem]
      have eqSlot : (slotOf u b + 1 == k + 1) =
          (slotOf u b == k) := by
        apply decide_eq_decide.mpr
        omega
      rw [eqSlot]
      simp
    rw [stripPEq, List.filter_append, newA, newB, bSlotGap]
    simp
  have insertedGap : (strippedP u x).filter (fun s =>
      slotP u x s == k + 1 && rel4P u x s == Rel4.gap) = [] := by
    rw [stripPEq, List.filter_eq_nil_iff]
    intro s sMem
    rcases List.mem_append.mp sMem with inA | inB
    · rw [slotPA s inA]
      have bound := slotA s inA
      have ne : slotOf u s ≠ k + 1 := by omega
      simp [ne]
    · rw [relPB s inB]
      simp
  have blockInserted : blockP u x k x = x :: (GR ++ [x]) := by
    simp only [blockP]
    rw [insertedInside, insertedGap]
    have regular : (k == 0 && x == u.head) = false := by
      simp [Nat.ne_of_gt kPos]
    rw [regular]
    simp [List.append_assoc]
  have shiftedInside : ∀ i, k ≤ i → i < n →
      (strippedP u x).filter (fun s =>
        slotP u x s == (i + 1) + 1 && rel4P u x s == Rel4.inside) =
      S.filter (fun s => slotOf u s == i + 1) := by
    intro i lo hi
    have newA : A.filter (fun s =>
        slotP u x s == (i + 1) + 1 &&
          rel4P u x s == Rel4.inside) = [] := by
      rw [List.filter_eq_nil_iff]
      intro a aMem
      rw [slotPA a aMem]
      have bound := slotA a aMem
      have ne : slotOf u a ≠ (i + 1) + 1 := by omega
      simp [ne]
    have newB : B.filter (fun s =>
        slotP u x s == (i + 1) + 1 &&
          rel4P u x s == Rel4.inside) =
        B.filter (fun s => slotOf u s == i + 1) := by
      apply filter_congr_mem
      intro b bMem
      rw [slotPB b bMem, relPB b bMem]
      have eqSlot : (slotOf u b + 1 == (i + 1) + 1) =
          (slotOf u b == i + 1) := by
        apply decide_eq_decide.mpr
        omega
      rw [eqSlot]
      simp
    have oldA : A.filter (fun s => slotOf u s == i + 1) = [] := by
      rw [List.filter_eq_nil_iff]
      intro a aMem
      have bound := slotA a aMem
      have ne : slotOf u a ≠ i + 1 := by omega
      simp [ne]
    have oldX : (slotOf u x == i + 1) = false := by
      rw [slotX]
      have ne : k ≠ i + 1 := by omega
      simp [ne]
    rw [stripPEq, List.filter_append, newA, newB,
      split, List.filter_append, List.filter_cons, oldA, oldX]
    simp
  have shiftedGapNil : ∀ i, k ≤ i →
      (strippedP u x).filter (fun s =>
        slotP u x s == (i + 1) + 1 && rel4P u x s == Rel4.gap) = [] := by
    intro i lo
    rw [stripPEq, List.filter_eq_nil_iff]
    intro s sMem
    rcases List.mem_append.mp sMem with inA | inB
    · rw [slotPA s inA]
      have bound := slotA s inA
      have ne : slotOf u s ≠ (i + 1) + 1 := by omega
      simp [ne]
    · rw [relPB s inB]
      simp
  have terminalGapNil : gapAt u (n - 1) = [] := by
    unfold gapAt
    have predN : n - 1 + 1 = n := by omega
    rw [predN, List.filter_eq_nil_iff]
    intro s sMem
    by_cases atN : slotOf u s = n
    · have noGap := rel4_ne_gap_of_terminal_slot
        (isSingle_of_mem_stripped sMem)
        (by simpa [n, P] using atN)
      simp [atN, noGap]
    · simp [atN]
  have suffixNonfinal : ∀ i, k ≤ i → i + 1 < n →
      suffixShiftBlock u x i =
        absorbB (pullBlockAt u i (P.getD i 0)) := by
    intro i lo hi
    have insideEq : (strippedP u x).filter (fun s =>
        slotP u x s == (i + 1) + 1 &&
          rel4P u x s == Rel4.inside) =
        insAt u i ++ gapAt u i := by
      rw [shiftedInside i lo (by omega)]
      simpa [S, n, P] using
        slotFilter_eq_ins_gap u (j := i + 1) (by omega)
          (by simpa [n, P] using hi)
    have gapNil := shiftedGapNil i lo
    unfold suffixShiftBlock
    rw [pseqP_getD_succ u x i lo
      (by simpa [n, P] using (show i < n by omega))]
    simp only [blockP]
    rw [insideEq, gapNil]
    have regular :
        ((i + 1 == 0) &&
          ((plasmaSeq u).getD i 0 == u.head)) = false := by simp
    rw [regular]
    simp [absorbB, pullBlockAt, P, List.append_assoc]
  have suffixTerminal :
      suffixShiftBlock u x (n - 1) =
        absorbLastB
          (pullBlockAt u (n - 1) (P.getD (n - 1) 0)) (afterAt u) := by
    have lo : k ≤ n - 1 := by omega
    have hi : n - 1 < n := by omega
    have nPred : n - 1 + 1 = n := by omega
    have insideEq : (strippedP u x).filter (fun s =>
        slotP u x s == n + 1 && rel4P u x s == Rel4.inside) =
        insAt u (n - 1) ++ afterAt u := by
      calc
        (strippedP u x).filter (fun s =>
            slotP u x s == n + 1 && rel4P u x s == Rel4.inside) =
            S.filter (fun s => slotOf u s == n) := by
              simpa [nPred] using shiftedInside (n - 1) lo hi
        _ = insAt u (n - 1) ++ afterAt u := by
              simpa [S, n, P] using
                slotFilter_terminal_eq_ins_after u
                  (by simpa [n, P] using nPos)
    have gapNil : (strippedP u x).filter (fun s =>
        slotP u x s == n + 1 && rel4P u x s == Rel4.gap) = [] := by
      simpa [nPred] using shiftedGapNil (n - 1) lo
    unfold suffixShiftBlock
    rw [pseqP_getD_succ u x (n - 1) lo hi, nPred]
    simp only [blockP]
    rw [insideEq, gapNil]
    have regular :
        ((n == 0) &&
          ((plasmaSeq u).getD (n - 1) 0 == u.head)) = false := by
      simp [Nat.ne_of_gt nPos]
    rw [regular]
    simp [absorbLastB, pullBlockAt, terminalGapNil, P,
      List.append_assoc]
  have suffixRegular : ∀ i, i ∈ indicesFrom k (n - k) →
      (i == 0 && P.getD i 0 == u.head) = false := by
    intro i iMem
    have bounds := mem_indicesFrom_bounds iMem
    have iPos : 0 < i := Nat.lt_of_lt_of_le kPos bounds.1
    simp [Nat.ne_of_gt iPos]
  have mPos : 0 < n - k := by omega
  let r : Nat := n - k - 1
  have mr : n - k = r + 1 := by
    dsimp [r]
    omega
  have kr : k + r = n - 1 := by omega
  have absorbEq :
      absorbTail bs (afterAt u) =
        (indicesFrom k (n - k)).flatMap (suffixShiftBlock u x) := by
    dsimp [bs]
    rw [mr]
    apply absorbTail_pullSuffix_succ
    · intro i iMem
      have bounds := mem_indicesFrom_bounds iMem
      exact suffixNonfinal i bounds.1 (by omega)
    · simpa [kr] using suffixTerminal
  have bsNonempty : bs ≠ [] := by
    dsimp [bs]
    rw [mr]
    simp [pullSuffix, indicesFrom]
  have rangeK : List.range k = List.range j ++ [j] := by
    rw [← jk, List.range_succ]
  have oldPrefixEq :
      beforeAt u ++ (List.range k).flatMap
        (fun i => blockOf u i (P.getD i 0)) = pre ++ x :: GR := by
    rw [rangeK, List.flatMap_append, List.flatMap_singleton,
      blockPivotOld]
    simp [pre, List.append_assoc]
  have earlyBlocksEq :
      (List.range j).flatMap (fun i =>
        blockP u x i ((pseqP u x).getD i 0)) =
      (List.range j).flatMap (fun i =>
        blockOf u i (P.getD i 0)) := by
    apply flatMap_congr_mem
    intro i iMem
    have ij : i < j := List.mem_range.mp iMem
    rw [pseqP_getD_before u x i (by omega)]
    exact blockEarly i _ (by omega)
  have newPrefixEq :
      (strippedP u x).filter (fun s => slotP u x s == 0) ++
        (List.range k).flatMap (fun i =>
          blockP u x i ((pseqP u x).getD i 0)) = pre := by
    rw [beforesEq, rangeK, List.flatMap_append,
      List.flatMap_singleton, earlyBlocksEq,
      pseqP_getD_before u x j (by omega), blockPivotNew]
    simp [pre, List.append_assoc]
  have oldBlocksSplit :
      (List.range n).flatMap (fun i => blockOf u i (P.getD i 0)) =
        (List.range k).flatMap (fun i => blockOf u i (P.getD i 0)) ++
          bs.flatMap renderB := by
    simpa [n, P, bs] using
      canonicalBlocks_split u k (by simpa [n, P] using kLe)
        (by
          intro i iMem
          have bounds := mem_indicesFrom_bounds iMem
          have iPos : 0 < i := Nat.lt_of_lt_of_le kPos bounds.1
          simp [Nat.ne_of_gt iPos])
  have shiftedSuffix :
      (indicesFrom (k + 1) (n - k)).flatMap (fun i =>
        blockP u x i ((pseqP u x).getD i 0)) =
        absorbTail bs (afterAt u) := by
    rw [← suffixShift_actual u x k (n - k)]
    exact absorbEq.symm
  have newRange :
      List.range (pseqP u x).length =
        List.range k ++ k :: indicesFrom (k + 1) (n - k) := by
    rw [pseqP_length]
    simpa [n, P] using
      range_insert_indices (k := k) (n := n)
        (by simpa [n, P] using kLe)
  have newBlocksSplit :
      (List.range (pseqP u x).length).flatMap (fun i =>
        blockP u x i ((pseqP u x).getD i 0)) =
        (List.range k).flatMap (fun i =>
          blockP u x i ((pseqP u x).getD i 0)) ++
          blockP u x k x ++ absorbTail bs (afterAt u) := by
    rw [newRange, List.flatMap_append, List.flatMap_cons,
      pseqP_getD_self, shiftedSuffix]
    simp [List.append_assoc]
  have newAfter : (strippedP u x).filter (fun s =>
      slotP u x s == (pseqP u x).length &&
        rel4P u x s == Rel4.after) = [] := by
    rw [List.filter_eq_nil_iff]
    intro s _
    rw [rel4P_beq_after_false]
    simp
  have sourceTail :
      (beforeAt u ++
          (List.range n).flatMap (fun i => blockOf u i (P.getD i 0)) ++
          afterAt u) ++ [x] =
        pre ++ x ::
          (GR ++ (bs.flatMap renderB ++ afterAt u ++ x :: [])) := by
    rw [oldBlocksSplit]
    calc
      (beforeAt u ++
          ((List.range k).flatMap
              (fun i => blockOf u i (P.getD i 0)) ++
            bs.flatMap renderB) ++ afterAt u) ++ [x] =
          (beforeAt u ++
            (List.range k).flatMap
              (fun i => blockOf u i (P.getD i 0))) ++
            bs.flatMap renderB ++ afterAt u ++ [x] := by
              simp [List.append_assoc]
      _ = (pre ++ x :: GR) ++
            bs.flatMap renderB ++ afterAt u ++ [x] := by
              rw [oldPrefixEq]
      _ = pre ++ x ::
            (GR ++ (bs.flatMap renderB ++ afterAt u ++ x :: [])) := by
              simp [List.append_assoc]
  have sourceEq :
      canonicalize u ++ Word.singleton x =
        (⟨u.head, pre ++ x ::
          (GR ++ (bs.flatMap renderB ++ afterAt u ++ x :: []))⟩ :
            Word Nat) := by
    rw [append_mk]
    simp only [canonicalize]
    congr 1
  have targetTail :
      (strippedP u x).filter (fun s => slotP u x s == 0) ++
          (List.range (pseqP u x).length).flatMap (fun i =>
            blockP u x i ((pseqP u x).getD i 0)) ++
          (strippedP u x).filter (fun s =>
            slotP u x s == (pseqP u x).length &&
              rel4P u x s == Rel4.after) =
        pre ++ x ::
          (GR ++ x :: absorbTail bs (afterAt u)) := by
    rw [newAfter, newBlocksSplit]
    simp only [List.append_nil]
    calc
      (strippedP u x).filter (fun s => slotP u x s == 0) ++
          ((List.range k).flatMap (fun i =>
              blockP u x i ((pseqP u x).getD i 0)) ++
            blockP u x k x ++ absorbTail bs (afterAt u)) =
        ((strippedP u x).filter (fun s => slotP u x s == 0) ++
          (List.range k).flatMap (fun i =>
            blockP u x i ((pseqP u x).getD i 0))) ++
          blockP u x k x ++ absorbTail bs (afterAt u) := by
            simp [List.append_assoc]
      _ = pre ++ blockP u x k x ++ absorbTail bs (afterAt u) := by
            rw [newPrefixEq]
      _ = pre ++ x ::
          (GR ++ x :: absorbTail bs (afterAt u)) := by
            rw [blockInserted]
            simp [List.append_assoc]
  have targetEq :
      canonicalizeP u x =
        (⟨u.head, pre ++ x ::
          (GR ++ x :: absorbTail bs (afterAt u))⟩ : Word Nat) := by
    simp only [canonicalizeP]
    congr 1
  change Derives basis
    (canonicalize u ++ Word.singleton x) (canonicalizeP u x)
  rw [sourceEq, targetEq]
  cases blocksShape : bs with
  | nil => exact False.elim (bsNonempty blocksShape)
  | cons first rest =>
      simpa [blocksShape, List.append_assoc] using
        (pullBlocksWithTail u.head pre x bs GR (afterAt u) [])

/-! ## Second-occurrence insertion: the before branch -/

/-- Pull the new close across every old plasma block when the old single
preceded all plasma opens.  The count-one head uses the head-open macro. -/
private theorem derivesInsertSecondBefore {h x : Nat} {T : List Nat}
    (single : List.count x (h :: T) = 1)
    (relation : rel4 (⟨h, T⟩ : Word Nat) x = Rel4.before) :
    Derives basis
      (canonicalize (⟨h, T⟩ : Word Nat) ++ Word.singleton x)
      (canonicalizeP (⟨h, T⟩ : Word Nat) x) := by
  let u : Word Nat := ⟨h, T⟩
  let P : List Nat := plasmaSeq u
  let S : List Nat := strippedSingles u
  let n : Nat := P.length
  have singleU : IsSingle u x := by
    change u.toList.count x = 1
    simpa [u] using single
  have relationU : rel4 u x = Rel4.before := by
    simpa [u] using relation
  have slotX : slotOf u x = 0 :=
    slotOf_eq_zero_of_rel_before relationU
  have headNotP : u.head ∉ P := by
    simpa [P] using head_not_mem_plasma_of_rel_before relationU
  have suffixRegular : ∀ i, i ∈ indicesFrom 0 n →
      (i == 0 && P.getD i 0 == u.head) = false := by
    intro i iMem
    by_cases iz : i = 0
    · subst i
      have bounds := mem_indicesFrom_bounds iMem
      have pMem : P.getD 0 0 ∈ P :=
        getD_mem_of_lt P 0 (by simpa [n] using bounds.2)
      have ne : P.getD 0 0 ≠ u.head := by
        intro equal
        apply headNotP
        rw [← equal]
        exact pMem
      have neBool : (P.getD 0 0 == u.head) = false := by
        exact decide_eq_false ne
      rw [neBool]
      rfl
    · simp [iz]
  have oldBlocks :
      (List.range n).flatMap (fun i => blockOf u i (P.getD i 0)) =
        (pullSuffix u 0 n).flatMap renderB := by
    have rangeZero : List.range n = indicesFrom 0 n := by
      simpa using range_add_indices 0 n
    rw [rangeZero]
    simpa [P] using (pullSuffix_render u 0 n suffixRegular).symm
  have getX : (pseqP u x).getD 0 0 = x := by
    simpa [slotX] using pseqP_getD_self u x
  have newRange :
      List.range (pseqP u x).length = 0 :: indicesFrom 1 n := by
    rw [pseqP_length]
    simpa [n, P] using
      range_insert_indices (k := 0) (n := n) (Nat.zero_le n)
  have newAfter : (strippedP u x).filter (fun s =>
      slotP u x s == (pseqP u x).length &&
        rel4P u x s == Rel4.after) = [] := by
    rw [List.filter_eq_nil_iff]
    intro s _
    rw [rel4P_beq_after_false]
    simp
  have afterNil : P = [] → afterAt u = [] := by
    intro pNil
    unfold afterAt
    rw [List.filter_eq_nil_iff]
    intro s _
    rw [rel4_of_plasma_nil (by simpa [P] using pNil)]
    simp
  by_cases xHead : x = h
  · subst x
    let R : List Nat := T.filter (fun c => (h :: T).count c == 1)
    have singlesHead : singlesSeq u = h :: R := by
      simpa [u, R] using singlesSeq_head_single single
    have notPlasma : ¬ IsPlasma u h := by
      intro plasma
      change 2 ≤ u.toList.count h at plasma
      change u.toList.count h = 1 at singleU
      omega
    have oldCond :
        (decide (List.take 1 (h :: R) = [u.head]) &&
          !decide (IsPlasma u u.head)) = true := by
      have takeOk : decide (List.take 1 (h :: R) = [u.head]) = true := by
        apply decide_eq_true
        simp [u]
      have plasmaNo : decide (IsPlasma u u.head) = false := by
        apply decide_eq_false
        simpa [u] using notPlasma
      rw [takeOk, plasmaNo]
      rfl
    have stripHead : strippedSingles u = R := by
      simp only [strippedSingles]
      rw [singlesHead, if_pos oldCond]
      rfl
    have hNotR : h ∉ R := by
      simpa [R] using head_not_in_singles_tail single
    have hNotS : h ∉ S := by
      intro member
      apply hNotR
      simpa [S, stripHead] using member
    have stripPEq : strippedP u h = S := by
      simp only [strippedP]
      rw [List.filter_eq_self]
      intro s sMem
      have sMemS : s ∈ S := by simpa [S] using sMem
      have ne : s ≠ h := by
        intro equal
        apply hNotS
        rw [← equal]
        exact sMemS
      simp [ne]
    have ordered := singlesSeq_pairwise_idxOf u
    rw [singlesHead, List.pairwise_cons] at ordered
    have lateS : ∀ s, s ∈ S →
        u.toList.idxOf h < u.toList.idxOf s := by
      intro s sMem
      apply ordered.1 s
      simpa [S, stripHead] using sMem
    have slotPS : ∀ s, s ∈ S →
        slotP u h s = slotOf u s + 1 := by
      intro s sMem
      rw [slotP, if_neg (by have := lateS s sMem; omega)]
    have relPS : ∀ s, s ∈ S →
        rel4P u h s = Rel4.inside := by
      intro s sMem
      rw [rel4P, if_neg (by have := lateS s sMem; omega)]
    let B0 : List Nat := beforeAt u
    have newBefore : (strippedP u h).filter
        (fun s => slotP u h s == 0) = [] := by
      rw [stripPEq, List.filter_eq_nil_iff]
      intro s sMem
      rw [slotPS s sMem]
      simp
    have insertedInside : (strippedP u h).filter (fun s =>
        slotP u h s == 1 && rel4P u h s == Rel4.inside) = B0 := by
      rw [stripPEq]
      change S.filter (fun s =>
        slotP u h s == 1 && rel4P u h s == Rel4.inside) =
        S.filter (fun s => slotOf u s == 0)
      apply filter_congr_mem
      intro s sMem
      rw [slotPS s sMem, relPS s sMem]
      have eqSlot : (slotOf u s + 1 == 1) =
          (slotOf u s == 0) := by
        apply decide_eq_decide.mpr
        omega
      rw [eqSlot]
      simp
    have insertedGap : (strippedP u h).filter (fun s =>
        slotP u h s == 1 && rel4P u h s == Rel4.gap) = [] := by
      rw [stripPEq, List.filter_eq_nil_iff]
      intro s sMem
      rw [relPS s sMem]
      simp
    have blockInserted : blockP u h 0 h = B0 ++ [h] := by
      simp only [blockP]
      rw [insertedInside, insertedGap]
      have special : (0 == 0 && h == u.head) = true := by
        simp [u]
      rw [special]
      simp [List.append_assoc]
    have shiftedInside : ∀ i, i < n →
        (strippedP u h).filter (fun s =>
          slotP u h s == (i + 1) + 1 &&
            rel4P u h s == Rel4.inside) =
        S.filter (fun s => slotOf u s == i + 1) := by
      intro i _
      rw [stripPEq]
      apply filter_congr_mem
      intro s sMem
      rw [slotPS s sMem, relPS s sMem]
      have eqSlot : (slotOf u s + 1 == (i + 1) + 1) =
          (slotOf u s == i + 1) := by
        apply decide_eq_decide.mpr
        omega
      rw [eqSlot]
      simp
    have shiftedGapNil : ∀ i,
        (strippedP u h).filter (fun s =>
          slotP u h s == (i + 1) + 1 &&
            rel4P u h s == Rel4.gap) = [] := by
      intro i
      rw [stripPEq, List.filter_eq_nil_iff]
      intro s sMem
      rw [relPS s sMem]
      simp
    by_cases nZero : n = 0
    · have pNil : P = [] :=
        List.eq_nil_of_length_eq_zero (by simpa [n] using nZero)
      have after0 : afterAt u = [] := afterNil pNil
      have sourceTail :
          (beforeAt u ++
              (List.range n).flatMap
                (fun i => blockOf u i (P.getD i 0)) ++
              afterAt u) ++ [h] = B0 ++ h :: [] := by
        rw [nZero, after0]
        simp [B0]
      have sourceEq :
          canonicalize u ++ Word.singleton h =
            (⟨u.head, B0 ++ h :: []⟩ : Word Nat) := by
        rw [append_mk]
        simp only [canonicalize]
        congr 1
      have targetTail :
          (strippedP u h).filter (fun s => slotP u h s == 0) ++
              (List.range (pseqP u h).length).flatMap (fun i =>
                blockP u h i ((pseqP u h).getD i 0)) ++
              (strippedP u h).filter (fun s =>
                slotP u h s == (pseqP u h).length &&
                  rel4P u h s == Rel4.after) =
            B0 ++ h :: [] := by
        rw [newBefore, newAfter, newRange, List.flatMap_cons, getX,
          blockInserted]
        simp [nZero, indicesFrom, List.append_assoc]
      have targetEq :
          canonicalizeP u h =
            (⟨u.head, B0 ++ h :: []⟩ : Word Nat) := by
        simp only [canonicalizeP]
        congr 1
      change Derives basis
        (canonicalize u ++ Word.singleton h) (canonicalizeP u h)
      rw [sourceEq, targetEq]
      exact Derives.refl _
    · have nPos : 0 < n := by omega
      have terminalGapNil : gapAt u (n - 1) = [] := by
        unfold gapAt
        have nPred : n - 1 + 1 = n := by omega
        rw [nPred, List.filter_eq_nil_iff]
        intro s sMem
        by_cases atN : slotOf u s = n
        · have noGap := rel4_ne_gap_of_terminal_slot
            (isSingle_of_mem_stripped sMem)
            (by simpa [n, P] using atN)
          simp [atN, noGap]
        · simp [atN]
      have suffixNonfinal : ∀ i, i + 1 < n →
          suffixShiftBlock u h i =
            absorbB (pullBlockAt u i (P.getD i 0)) := by
        intro i hi
        have insideEq : (strippedP u h).filter (fun s =>
            slotP u h s == (i + 1) + 1 &&
              rel4P u h s == Rel4.inside) =
            insAt u i ++ gapAt u i := by
          rw [shiftedInside i (by omega)]
          simpa [S, n, P] using
            slotFilter_eq_ins_gap u (j := i + 1) (by omega)
              (by simpa [n, P] using hi)
        have gapNil := shiftedGapNil i
        unfold suffixShiftBlock
        rw [pseqP_getD_succ u h i (by rw [slotX]; omega)
          (by simpa [n, P] using (show i < n by omega))]
        simp only [blockP]
        rw [insideEq, gapNil]
        have regular :
            ((i + 1 == 0) &&
              ((plasmaSeq u).getD i 0 == u.head)) = false := by simp
        rw [regular]
        simp [absorbB, pullBlockAt, P, List.append_assoc]
      have suffixTerminal :
          suffixShiftBlock u h (n - 1) =
            absorbLastB
              (pullBlockAt u (n - 1) (P.getD (n - 1) 0))
              (afterAt u) := by
        have hi : n - 1 < n := by omega
        have nPred : n - 1 + 1 = n := by omega
        have insideEq : (strippedP u h).filter (fun s =>
            slotP u h s == n + 1 && rel4P u h s == Rel4.inside) =
            insAt u (n - 1) ++ afterAt u := by
          calc
            (strippedP u h).filter (fun s =>
                slotP u h s == n + 1 &&
                  rel4P u h s == Rel4.inside) =
                S.filter (fun s => slotOf u s == n) := by
                  simpa [nPred] using shiftedInside (n - 1) hi
            _ = insAt u (n - 1) ++ afterAt u := by
                  simpa [S, n, P] using
                    slotFilter_terminal_eq_ins_after u
                      (by simpa [n, P] using nPos)
        have gapNil : (strippedP u h).filter (fun s =>
            slotP u h s == n + 1 && rel4P u h s == Rel4.gap) = [] := by
          simpa [nPred] using shiftedGapNil (n - 1)
        unfold suffixShiftBlock
        rw [pseqP_getD_succ u h (n - 1) (by rw [slotX]; omega) hi,
          nPred]
        simp only [blockP]
        rw [insideEq, gapNil]
        have regular :
            ((n == 0) &&
              ((plasmaSeq u).getD (n - 1) 0 == u.head)) = false := by
          simp [Nat.ne_of_gt nPos]
        rw [regular]
        simp [absorbLastB, pullBlockAt, terminalGapNil, P,
          List.append_assoc]
      let bs : List PullBlock := pullSuffix u 0 n
      let r : Nat := n - 1
      have nr : n = r + 1 := by
        dsimp [r]
        omega
      have lastIndex : 0 + r = n - 1 := by omega
      have absorbEq :
          absorbTail bs (afterAt u) =
            (indicesFrom 0 n).flatMap (suffixShiftBlock u h) := by
        dsimp [bs]
        rw [nr]
        apply absorbTail_pullSuffix_succ
        · intro i iMem
          have bounds := mem_indicesFrom_bounds iMem
          exact suffixNonfinal i (by omega)
        · simpa [lastIndex] using suffixTerminal
      have bsNonempty : bs ≠ [] := by
        dsimp [bs]
        rw [nr]
        simp [pullSuffix, indicesFrom]
      have shiftedSuffix :
          (indicesFrom 1 n).flatMap (fun i =>
            blockP u h i ((pseqP u h).getD i 0)) =
            absorbTail bs (afterAt u) := by
        rw [← suffixShift_actual u h 0 n]
        exact absorbEq.symm
      have newBlocks :
          (List.range (pseqP u h).length).flatMap (fun i =>
            blockP u h i ((pseqP u h).getD i 0)) =
            blockP u h 0 h ++ absorbTail bs (afterAt u) := by
        rw [newRange, List.flatMap_cons, getX, shiftedSuffix]
      have sourceTail :
          (beforeAt u ++
              (List.range n).flatMap
                (fun i => blockOf u i (P.getD i 0)) ++
              afterAt u) ++ [h] =
            B0 ++ (bs.flatMap renderB ++ afterAt u ++ h :: []) := by
        rw [oldBlocks]
        simp [B0, bs, List.append_assoc]
      have sourceEq :
          canonicalize u ++ Word.singleton h =
            (⟨u.head,
              B0 ++ (bs.flatMap renderB ++ afterAt u ++ h :: [])⟩ :
                Word Nat) := by
        rw [append_mk]
        simp only [canonicalize]
        congr 1
      have targetTail :
          (strippedP u h).filter (fun s => slotP u h s == 0) ++
              (List.range (pseqP u h).length).flatMap (fun i =>
                blockP u h i ((pseqP u h).getD i 0)) ++
              (strippedP u h).filter (fun s =>
                slotP u h s == (pseqP u h).length &&
                  rel4P u h s == Rel4.after) =
            B0 ++ h :: absorbTail bs (afterAt u) := by
        rw [newBefore, newAfter, newBlocks, blockInserted]
        simp [List.append_assoc]
      have targetEq :
          canonicalizeP u h =
            (⟨u.head, B0 ++ h :: absorbTail bs (afterAt u)⟩ :
              Word Nat) := by
        simp only [canonicalizeP]
        congr 1
      change Derives basis
        (canonicalize u ++ Word.singleton h) (canonicalizeP u h)
      rw [sourceEq, targetEq]
      cases blocksShape : bs with
      | nil => exact False.elim (bsNonempty blocksShape)
      | cons first rest =>
          simpa [blocksShape, List.append_assoc] using
            (pullBlocksWithTailHead u.head bs B0 (afterAt u) [])
  · have headNe : h ≠ x := fun equal => xHead equal.symm
    obtain ⟨A, B, splitRaw, left, right⟩ :=
      strippedSingles_split_single single headNe
    have splitU : strippedSingles u = A ++ x :: B := by
      simpa [u] using splitRaw
    have split : S = A ++ x :: B := by
      simpa [S] using splitU
    have leftU : ∀ a, a ∈ A →
        u.toList.idxOf a < u.toList.idxOf x := by
      intro a aMem
      simpa [u] using left a aMem
    have rightU : ∀ b, b ∈ B →
        u.toList.idxOf x < u.toList.idxOf b := by
      intro b bMem
      simpa [u] using right b bMem
    have beforeAllX := allBefore_of_rel4_before relationU
    rw [List.all_eq_true] at beforeAllX
    have relA : ∀ a, a ∈ A → rel4 u a = Rel4.before := by
      intro a aMem
      have allA : (plasmaSeq u).all (fun p =>
          u.toList.idxOf a < u.toList.idxOf p) = true := by
        rw [List.all_eq_true]
        intro p pMem
        have xp : u.toList.idxOf x < u.toList.idxOf p := by
          simpa using beforeAllX p pMem
        exact decide_eq_true (Nat.lt_trans (leftU a aMem) xp)
      simp [rel4, allA]
    have slotA : ∀ a, a ∈ A → slotOf u a = 0 := by
      intro a aMem
      exact slotOf_eq_zero_of_rel_before (relA a aMem)
    have xNotA : x ∉ A := by
      intro member
      have order := leftU x member
      omega
    have xNotB : x ∉ B := by
      intro member
      have order := rightU x member
      omega
    have stripPEq : strippedP u x = A ++ B := by
      simp only [strippedP, splitU, List.filter_append, List.filter_cons]
      have keepA : A.filter (fun e => !(e == x)) = A := by
        rw [List.filter_eq_self]
        intro a aMem
        have ne : a ≠ x := fun equal => xNotA (equal ▸ aMem)
        simp [ne]
      have keepB : B.filter (fun e => !(e == x)) = B := by
        rw [List.filter_eq_self]
        intro b bMem
        have ne : b ≠ x := fun equal => xNotB (equal ▸ bMem)
        simp [ne]
      rw [keepA, keepB]
      simp
    have slotPA : ∀ a, a ∈ A → slotP u x a = 0 := by
      intro a aMem
      rw [slotP, if_pos (leftU a aMem), slotA a aMem]
    have relPA : ∀ a, a ∈ A → rel4P u x a = Rel4.before := by
      intro a aMem
      rw [rel4P, if_pos (leftU a aMem), relA a aMem]
      rfl
    have slotPB : ∀ b, b ∈ B →
        slotP u x b = slotOf u b + 1 := by
      intro b bMem
      rw [slotP, if_neg (by have := rightU b bMem; omega)]
    have relPB : ∀ b, b ∈ B → rel4P u x b = Rel4.inside := by
      intro b bMem
      rw [rel4P, if_neg (by have := rightU b bMem; omega)]
    let B0 : List Nat := B.filter (fun s => slotOf u s == 0)
    have oldBefore : beforeAt u = A ++ x :: B0 := by
      have aSelf : A.filter (fun s => slotOf u s == 0) = A := by
        rw [List.filter_eq_self]
        intro a aMem
        rw [slotA a aMem]
        rfl
      unfold beforeAt
      rw [splitU, List.filter_append, List.filter_cons, aSelf, slotX]
      simp [B0]
    have newBefore : (strippedP u x).filter
        (fun s => slotP u x s == 0) = A := by
      have aSelf : A.filter (fun s => slotP u x s == 0) = A := by
        rw [List.filter_eq_self]
        intro a aMem
        rw [slotPA a aMem]
        rfl
      have bNil : B.filter (fun s => slotP u x s == 0) = [] := by
        rw [List.filter_eq_nil_iff]
        intro b bMem
        rw [slotPB b bMem]
        simp
      rw [stripPEq, List.filter_append, aSelf, bNil]
      simp
    have insertedInside : (strippedP u x).filter (fun s =>
        slotP u x s == 1 && rel4P u x s == Rel4.inside) = B0 := by
      have aNil : A.filter (fun s =>
          slotP u x s == 1 && rel4P u x s == Rel4.inside) = [] := by
        rw [List.filter_eq_nil_iff]
        intro a aMem
        rw [relPA a aMem]
        simp
      have bEq : B.filter (fun s =>
          slotP u x s == 1 && rel4P u x s == Rel4.inside) = B0 := by
        change B.filter (fun s =>
          slotP u x s == 1 && rel4P u x s == Rel4.inside) =
          B.filter (fun s => slotOf u s == 0)
        apply filter_congr_mem
        intro b bMem
        rw [slotPB b bMem, relPB b bMem]
        have eqSlot : (slotOf u b + 1 == 1) =
            (slotOf u b == 0) := by
          apply decide_eq_decide.mpr
          omega
        rw [eqSlot]
        simp
      rw [stripPEq, List.filter_append, aNil, bEq]
      simp
    have insertedGap : (strippedP u x).filter (fun s =>
        slotP u x s == 1 && rel4P u x s == Rel4.gap) = [] := by
      rw [stripPEq, List.filter_eq_nil_iff]
      intro s sMem
      rcases List.mem_append.mp sMem with inA | inB
      · rw [relPA s inA]
        simp
      · rw [relPB s inB]
        simp
    have blockInserted : blockP u x 0 x = x :: (B0 ++ [x]) := by
      simp only [blockP]
      rw [insertedInside, insertedGap]
      have regular : (0 == 0 && x == u.head) = false := by
        have ne : x ≠ u.head := by simpa [u] using xHead
        simp [ne]
      rw [regular]
      simp [List.append_assoc]
    have shiftedInside : ∀ i, i < n →
        (strippedP u x).filter (fun s =>
          slotP u x s == (i + 1) + 1 &&
            rel4P u x s == Rel4.inside) =
        S.filter (fun s => slotOf u s == i + 1) := by
      intro i hi
      have newA : A.filter (fun s =>
          slotP u x s == (i + 1) + 1 &&
            rel4P u x s == Rel4.inside) = [] := by
        rw [List.filter_eq_nil_iff]
        intro a aMem
        rw [slotPA a aMem]
        simp
      have newB : B.filter (fun s =>
          slotP u x s == (i + 1) + 1 &&
            rel4P u x s == Rel4.inside) =
          B.filter (fun s => slotOf u s == i + 1) := by
        apply filter_congr_mem
        intro b bMem
        rw [slotPB b bMem, relPB b bMem]
        have eqSlot : (slotOf u b + 1 == (i + 1) + 1) =
            (slotOf u b == i + 1) := by
          apply decide_eq_decide.mpr
          omega
        rw [eqSlot]
        simp
      have oldA : A.filter (fun s => slotOf u s == i + 1) = [] := by
        rw [List.filter_eq_nil_iff]
        intro a aMem
        rw [slotA a aMem]
        simp
      have oldX : (slotOf u x == i + 1) = false := by
        rw [slotX]
        simp
      rw [stripPEq, List.filter_append, newA, newB,
        split, List.filter_append, List.filter_cons, oldA, oldX]
      simp
    have shiftedGapNil : ∀ i,
        (strippedP u x).filter (fun s =>
          slotP u x s == (i + 1) + 1 &&
            rel4P u x s == Rel4.gap) = [] := by
      intro i
      rw [stripPEq, List.filter_eq_nil_iff]
      intro s sMem
      rcases List.mem_append.mp sMem with inA | inB
      · rw [relPA s inA]
        simp
      · rw [relPB s inB]
        simp
    by_cases nZero : n = 0
    · have pNil : P = [] :=
        List.eq_nil_of_length_eq_zero (by simpa [n] using nZero)
      have after0 : afterAt u = [] := afterNil pNil
      have sourceTail :
          (beforeAt u ++
              (List.range n).flatMap
                (fun i => blockOf u i (P.getD i 0)) ++
              afterAt u) ++ [x] =
            A ++ x :: (B0 ++ x :: []) := by
        rw [oldBefore, nZero, after0]
        simp [List.append_assoc]
      have sourceEq :
          canonicalize u ++ Word.singleton x =
            (⟨u.head, A ++ x :: (B0 ++ x :: [])⟩ : Word Nat) := by
        rw [append_mk]
        simp only [canonicalize]
        congr 1
      have targetTail :
          (strippedP u x).filter (fun s => slotP u x s == 0) ++
              (List.range (pseqP u x).length).flatMap (fun i =>
                blockP u x i ((pseqP u x).getD i 0)) ++
              (strippedP u x).filter (fun s =>
                slotP u x s == (pseqP u x).length &&
                  rel4P u x s == Rel4.after) =
            A ++ x :: (B0 ++ x :: []) := by
        rw [newBefore, newAfter, newRange, List.flatMap_cons, getX,
          blockInserted]
        simp [nZero, indicesFrom, List.append_assoc]
      have targetEq :
          canonicalizeP u x =
            (⟨u.head, A ++ x :: (B0 ++ x :: [])⟩ : Word Nat) := by
        simp only [canonicalizeP]
        congr 1
      change Derives basis
        (canonicalize u ++ Word.singleton x) (canonicalizeP u x)
      rw [sourceEq, targetEq]
      exact Derives.refl _
    · have nPos : 0 < n := by omega
      have terminalGapNil : gapAt u (n - 1) = [] := by
        unfold gapAt
        have nPred : n - 1 + 1 = n := by omega
        rw [nPred, List.filter_eq_nil_iff]
        intro s sMem
        by_cases atN : slotOf u s = n
        · have noGap := rel4_ne_gap_of_terminal_slot
            (isSingle_of_mem_stripped sMem)
            (by simpa [n, P] using atN)
          simp [atN, noGap]
        · simp [atN]
      have suffixNonfinal : ∀ i, i + 1 < n →
          suffixShiftBlock u x i =
            absorbB (pullBlockAt u i (P.getD i 0)) := by
        intro i hi
        have insideEq : (strippedP u x).filter (fun s =>
            slotP u x s == (i + 1) + 1 &&
              rel4P u x s == Rel4.inside) =
            insAt u i ++ gapAt u i := by
          rw [shiftedInside i (by omega)]
          simpa [S, n, P] using
            slotFilter_eq_ins_gap u (j := i + 1) (by omega)
              (by simpa [n, P] using hi)
        have gapNil := shiftedGapNil i
        unfold suffixShiftBlock
        rw [pseqP_getD_succ u x i (by rw [slotX]; omega)
          (by simpa [n, P] using (show i < n by omega))]
        simp only [blockP]
        rw [insideEq, gapNil]
        have regular :
            ((i + 1 == 0) &&
              ((plasmaSeq u).getD i 0 == u.head)) = false := by simp
        rw [regular]
        simp [absorbB, pullBlockAt, P, List.append_assoc]
      have suffixTerminal :
          suffixShiftBlock u x (n - 1) =
            absorbLastB
              (pullBlockAt u (n - 1) (P.getD (n - 1) 0))
              (afterAt u) := by
        have hi : n - 1 < n := by omega
        have nPred : n - 1 + 1 = n := by omega
        have insideEq : (strippedP u x).filter (fun s =>
            slotP u x s == n + 1 && rel4P u x s == Rel4.inside) =
            insAt u (n - 1) ++ afterAt u := by
          calc
            (strippedP u x).filter (fun s =>
                slotP u x s == n + 1 &&
                  rel4P u x s == Rel4.inside) =
                S.filter (fun s => slotOf u s == n) := by
                  simpa [nPred] using shiftedInside (n - 1) hi
            _ = insAt u (n - 1) ++ afterAt u := by
                  simpa [S, n, P] using
                    slotFilter_terminal_eq_ins_after u
                      (by simpa [n, P] using nPos)
        have gapNil : (strippedP u x).filter (fun s =>
            slotP u x s == n + 1 && rel4P u x s == Rel4.gap) = [] := by
          simpa [nPred] using shiftedGapNil (n - 1)
        unfold suffixShiftBlock
        rw [pseqP_getD_succ u x (n - 1) (by rw [slotX]; omega) hi,
          nPred]
        simp only [blockP]
        rw [insideEq, gapNil]
        have regular :
            ((n == 0) &&
              ((plasmaSeq u).getD (n - 1) 0 == u.head)) = false := by
          simp [Nat.ne_of_gt nPos]
        rw [regular]
        simp [absorbLastB, pullBlockAt, terminalGapNil, P,
          List.append_assoc]
      let bs : List PullBlock := pullSuffix u 0 n
      let r : Nat := n - 1
      have nr : n = r + 1 := by
        dsimp [r]
        omega
      have lastIndex : 0 + r = n - 1 := by omega
      have absorbEq :
          absorbTail bs (afterAt u) =
            (indicesFrom 0 n).flatMap (suffixShiftBlock u x) := by
        dsimp [bs]
        rw [nr]
        apply absorbTail_pullSuffix_succ
        · intro i iMem
          have bounds := mem_indicesFrom_bounds iMem
          exact suffixNonfinal i (by omega)
        · simpa [lastIndex] using suffixTerminal
      have bsNonempty : bs ≠ [] := by
        dsimp [bs]
        rw [nr]
        simp [pullSuffix, indicesFrom]
      have shiftedSuffix :
          (indicesFrom 1 n).flatMap (fun i =>
            blockP u x i ((pseqP u x).getD i 0)) =
            absorbTail bs (afterAt u) := by
        rw [← suffixShift_actual u x 0 n]
        exact absorbEq.symm
      have newBlocks :
          (List.range (pseqP u x).length).flatMap (fun i =>
            blockP u x i ((pseqP u x).getD i 0)) =
            blockP u x 0 x ++ absorbTail bs (afterAt u) := by
        rw [newRange, List.flatMap_cons, getX, shiftedSuffix]
      have sourceTail :
          (beforeAt u ++
              (List.range n).flatMap
                (fun i => blockOf u i (P.getD i 0)) ++
              afterAt u) ++ [x] =
            A ++ x ::
              (B0 ++ (bs.flatMap renderB ++ afterAt u ++ x :: [])) := by
        rw [oldBefore, oldBlocks]
        simp [bs, List.append_assoc]
      have sourceEq :
          canonicalize u ++ Word.singleton x =
            (⟨u.head, A ++ x ::
              (B0 ++ (bs.flatMap renderB ++ afterAt u ++ x :: []))⟩ :
                Word Nat) := by
        rw [append_mk]
        simp only [canonicalize]
        congr 1
      have targetTail :
          (strippedP u x).filter (fun s => slotP u x s == 0) ++
              (List.range (pseqP u x).length).flatMap (fun i =>
                blockP u x i ((pseqP u x).getD i 0)) ++
              (strippedP u x).filter (fun s =>
                slotP u x s == (pseqP u x).length &&
                  rel4P u x s == Rel4.after) =
            A ++ x :: (B0 ++ x :: absorbTail bs (afterAt u)) := by
        rw [newBefore, newAfter, newBlocks, blockInserted]
        simp [List.append_assoc]
      have targetEq :
          canonicalizeP u x =
            (⟨u.head,
              A ++ x :: (B0 ++ x :: absorbTail bs (afterAt u))⟩ :
                Word Nat) := by
        simp only [canonicalizeP]
        congr 1
      change Derives basis
        (canonicalize u ++ Word.singleton x) (canonicalizeP u x)
      rw [sourceEq, targetEq]
      cases blocksShape : bs with
      | nil => exact False.elim (bsNonempty blocksShape)
      | cons first rest =>
          simpa [blocksShape, List.append_assoc] using
            (pullBlocksWithTail u.head A x bs B0 (afterAt u) [])

/-! ## Second-occurrence insertion: the inside branch -/

/-- Split the enclosing plasma pair, then pull the new close across the
remaining plasma suffix. -/
private theorem derivesInsertSecondInside {h x : Nat} {T : List Nat}
    (single : List.count x (h :: T) = 1)
    (relation : rel4 (⟨h, T⟩ : Word Nat) x = Rel4.inside) :
    Derives basis
      (canonicalize (⟨h, T⟩ : Word Nat) ++ Word.singleton x)
      (canonicalizeP (⟨h, T⟩ : Word Nat) x) := by
  let u : Word Nat := ⟨h, T⟩
  let P : List Nat := plasmaSeq u
  let S : List Nat := strippedSingles u
  let n : Nat := P.length
  let k : Nat := slotOf u x
  have singleU : IsSingle u x := by
    change u.toList.count x = 1
    simpa [u] using single
  have relationU : rel4 u x = Rel4.inside := by
    simpa [u] using relation
  have xNotAfter : rel4 u x ≠ Rel4.after := by
    intro after
    rw [relationU] at after
    cases after
  have kPos : 0 < k := by
    apply slotOf_pos_of_single_rel_ne_before singleU
    intro before
    rw [before] at relationU
    cases relationU
  have kLe : k ≤ n := by
    simpa [k, n, P] using slotOf_le_length u x
  have nPos : 0 < n := by omega
  have headNe : h ≠ x := by
    intro equal
    subst x
    have allFail : ∀ p, p ∈ plasmaSeq u →
        decide (u.toList.idxOf p < u.toList.idxOf h) = false := by
      intro p _
      have headIdx : u.toList.idxOf h = 0 := by
        change (h :: T).idxOf h = 0
        simp
      rw [headIdx]
      exact decide_eq_false (by omega)
    have zero : slotOf u h = 0 := by
      unfold slotOf
      rw [takeWhile_eq_nil_of_all_false allFail]
      rfl
    change 0 < slotOf u h at kPos
    omega
  obtain ⟨A, B, splitRaw, left, right⟩ :=
    strippedSingles_split_single single headNe
  have splitU : strippedSingles u = A ++ x :: B := by
    simpa [u] using splitRaw
  have split : S = A ++ x :: B := by
    simpa [S] using splitU
  have leftU : ∀ a, a ∈ A →
      u.toList.idxOf a < u.toList.idxOf x := by
    intro a aMem
    simpa [u] using left a aMem
  have rightU : ∀ b, b ∈ B →
      u.toList.idxOf x < u.toList.idxOf b := by
    intro b bMem
    simpa [u] using right b bMem
  have slotX : slotOf u x = k := rfl
  have slotA : ∀ a, a ∈ A → slotOf u a ≤ k := by
    intro a aMem
    exact slotOf_mono_of_idx_le (Nat.le_of_lt (leftU a aMem))
  have slotB : ∀ b, b ∈ B → k ≤ slotOf u b := by
    intro b bMem
    exact slotOf_mono_of_idx_le (Nat.le_of_lt (rightU b bMem))
  have xNotA : x ∉ A := by
    intro member
    have order := leftU x member
    omega
  have xNotB : x ∉ B := by
    intro member
    have order := rightU x member
    omega
  have stripPEq : strippedP u x = A ++ B := by
    simp only [strippedP, splitU, List.filter_append, List.filter_cons]
    have keepA : A.filter (fun e => !(e == x)) = A := by
      rw [List.filter_eq_self]
      intro a aMem
      have ne : a ≠ x := fun equal => xNotA (equal ▸ aMem)
      simp [ne]
    have keepB : B.filter (fun e => !(e == x)) = B := by
      rw [List.filter_eq_self]
      intro b bMem
      have ne : b ≠ x := fun equal => xNotB (equal ▸ bMem)
      simp [ne]
    rw [keepA, keepB]
    simp
  have singleS : ∀ s, s ∈ S → IsSingle u s := by
    intro s sMem
    apply isSingle_of_mem_stripped
    simpa [S] using sMem
  have singleA : ∀ a, a ∈ A → IsSingle u a := by
    intro a aMem
    apply singleS a
    rw [split]
    simp [aMem]
  have singleB : ∀ b, b ∈ B → IsSingle u b := by
    intro b bMem
    apply singleS b
    rw [split]
    simp [bMem]
  have slotPA : ∀ a, a ∈ A → slotP u x a = slotOf u a := by
    intro a aMem
    rw [slotP, if_pos (leftU a aMem)]
  have relPA : ∀ a, a ∈ A → rel4P u x a = rel4 u a := by
    intro a aMem
    have aNotAfter : rel4 u a ≠ Rel4.after := by
      intro afterA
      have later := idxOf_lt_of_rel_ne_after_rel_after
        singleU xNotAfter afterA
      have earlier := leftU a aMem
      omega
    rw [rel4P, if_pos (leftU a aMem), if_neg aNotAfter]
  have slotPB : ∀ b, b ∈ B → slotP u x b = slotOf u b + 1 := by
    intro b bMem
    rw [slotP, if_neg (by have := rightU b bMem; omega)]
  have relPB : ∀ b, b ∈ B → rel4P u x b = Rel4.inside := by
    intro b bMem
    rw [rel4P, if_neg (by have := rightU b bMem; omega)]
  let j : Nat := k - 1
  have jk : j + 1 = k := by
    dsimp [j]
    omega
  have jLt : j < n := by omega
  let q : Nat := P.getD j 0
  have qMem : q ∈ P := by
    dsimp [q]
    exact getD_mem_of_lt P 0 (by simpa [n] using jLt)
  let insidePred : Nat → Bool := fun s =>
    slotOf u s == k && rel4 u s == Rel4.inside
  let IL : List Nat := A.filter insidePred
  let IR : List Nat := B.filter insidePred
  let G : List Nat := gapAt u j
  let headSpecial : Bool := j == 0 && q == u.head
  let preBase : List Nat :=
    beforeAt u ++
      (List.range j).flatMap (fun i => blockOf u i (P.getD i 0))
  let pre : List Nat :=
    if headSpecial then IL else preBase ++ q :: IL
  let bs : List PullBlock := pullSuffix u k (n - k)
  let KR : List Nat := B.filter (fun s => slotOf u s == k)
  have insPivot : insAt u j = IL ++ x :: IR := by
    have pass : insidePred x = true := by
      simp [insidePred, slotX, relationU]
    have raw := filter_split_cons (L := strippedSingles u)
      (A := A) (B := B) (x := x) splitU insidePred pass
    unfold insAt
    rw [jk]
    change (strippedSingles u).filter insidePred = IL ++ x :: IR
    simpa [IL, IR] using raw
  have preBase_eq_nil_of_special
      (special : headSpecial = true) : preBase = [] := by
    have parts : j = 0 ∧ q = u.head := by
      simpa only [headSpecial, Bool.and_eq_true, beq_iff_eq] using special
    have headMem : u.head ∈ plasmaSeq u := by
      have member := qMem
      rw [parts.2] at member
      simpa [P] using member
    have beforeNil : beforeAt u = [] := by
      unfold beforeAt
      rw [List.filter_eq_nil_iff]
      intro s sMem
      have sSingle := isSingle_of_mem_stripped sMem
      have sNotBefore : rel4 u s ≠ Rel4.before := by
        intro before
        exact (head_not_mem_plasma_of_rel_before before) headMem
      have sPos := slotOf_pos_of_single_rel_ne_before sSingle sNotBefore
      simp [Nat.ne_of_gt sPos]
    simp [preBase, beforeNil, parts.1]
  have blockPivotOld : blockOf u j q =
      if headSpecial then IL ++ x :: (IR ++ q :: G)
      else q :: (IL ++ x :: (IR ++ q :: G)) := by
    simp only [blockOf]
    change
      ((if headSpecial then insAt u j ++ [q]
        else q :: insAt u j ++ [q]) ++ gapAt u j) = _
    rw [insPivot]
    cases special : headSpecial <;>
      simp [special, G, List.append_assoc]
  have beforesEq :
      (strippedP u x).filter (fun s => slotP u x s == 0) =
        beforeAt u := by
    have aEq : A.filter (fun s => slotP u x s == 0) =
        A.filter (fun s => slotOf u s == 0) := by
      apply filter_congr_mem
      intro a aMem
      rw [slotPA a aMem]
    have bNew : B.filter (fun s => slotP u x s == 0) = [] := by
      rw [List.filter_eq_nil_iff]
      intro b bMem
      rw [slotPB b bMem]
      simp
    have bOld : B.filter (fun s => slotOf u s == 0) = [] := by
      rw [List.filter_eq_nil_iff]
      intro b bMem
      have bound := slotB b bMem
      have ne : slotOf u b ≠ 0 := by omega
      simp [ne]
    have xOld : (slotOf u x == 0) = false := by
      rw [slotX]
      simp [Nat.ne_of_gt kPos]
    simp only [beforeAt]
    rw [stripPEq, List.filter_append, aEq, bNew,
      splitU, List.filter_append, List.filter_cons, bOld, xOld]
    simp
  have blockEarly : ∀ i p, i + 1 < k →
      blockP u x i p = blockOf u i p := by
    intro i p hi
    have insA : A.filter (fun s =>
        slotP u x s == i + 1 && rel4P u x s == Rel4.inside) =
        A.filter (fun s =>
          slotOf u s == i + 1 && rel4 u s == Rel4.inside) := by
      apply filter_congr_mem
      intro a aMem
      rw [slotPA a aMem, relPA a aMem]
    have insBNew : B.filter (fun s =>
        slotP u x s == i + 1 && rel4P u x s == Rel4.inside) = [] := by
      rw [List.filter_eq_nil_iff]
      intro b bMem
      rw [slotPB b bMem, relPB b bMem]
      have bound := slotB b bMem
      have ne : slotOf u b ≠ i := by omega
      simp [ne]
    have insBOld : B.filter (fun s =>
        slotOf u s == i + 1 && rel4 u s == Rel4.inside) = [] := by
      rw [List.filter_eq_nil_iff]
      intro b bMem
      have bound := slotB b bMem
      have ne : slotOf u b ≠ i + 1 := by omega
      simp [ne]
    have insX :
        (slotOf u x == i + 1 && rel4 u x == Rel4.inside) = false := by
      rw [slotX]
      have ne : k ≠ i + 1 := by omega
      simp [ne]
    have insEq : (A ++ B).filter (fun s =>
        slotP u x s == i + 1 && rel4P u x s == Rel4.inside) =
        S.filter (fun s =>
          slotOf u s == i + 1 && rel4 u s == Rel4.inside) := by
      rw [split, List.filter_append, List.filter_append, List.filter_cons,
        insA, insBNew, insBOld, insX]
      simp
    have gapA : A.filter (fun s =>
        slotP u x s == i + 1 && rel4P u x s == Rel4.gap) =
        A.filter (fun s =>
          slotOf u s == i + 1 && rel4 u s == Rel4.gap) := by
      apply filter_congr_mem
      intro a aMem
      rw [slotPA a aMem, relPA a aMem]
    have gapBNew : B.filter (fun s =>
        slotP u x s == i + 1 && rel4P u x s == Rel4.gap) = [] := by
      rw [List.filter_eq_nil_iff]
      intro b bMem
      rw [relPB b bMem]
      simp
    have gapBOld : B.filter (fun s =>
        slotOf u s == i + 1 && rel4 u s == Rel4.gap) = [] := by
      rw [List.filter_eq_nil_iff]
      intro b bMem
      have bound := slotB b bMem
      have ne : slotOf u b ≠ i + 1 := by omega
      simp [ne]
    have gapX :
        (slotOf u x == i + 1 && rel4 u x == Rel4.gap) = false := by
      rw [slotX]
      have ne : k ≠ i + 1 := by omega
      simp [ne]
    have gapEq : (A ++ B).filter (fun s =>
        slotP u x s == i + 1 && rel4P u x s == Rel4.gap) =
        S.filter (fun s =>
          slotOf u s == i + 1 && rel4 u s == Rel4.gap) := by
      rw [split, List.filter_append, List.filter_append, List.filter_cons,
        gapA, gapBNew, gapBOld, gapX]
      simp
    simp only [blockP, blockOf]
    rw [stripPEq, insEq, gapEq]
  have pivotInside : (strippedP u x).filter (fun s =>
      slotP u x s == k && rel4P u x s == Rel4.inside) = IL := by
    have newA : A.filter (fun s =>
        slotP u x s == k && rel4P u x s == Rel4.inside) = IL := by
      change A.filter (fun s =>
        slotP u x s == k && rel4P u x s == Rel4.inside) =
        A.filter insidePred
      apply filter_congr_mem
      intro a aMem
      rw [slotPA a aMem, relPA a aMem]
    have newB : B.filter (fun s =>
        slotP u x s == k && rel4P u x s == Rel4.inside) = [] := by
      rw [List.filter_eq_nil_iff]
      intro b bMem
      rw [slotPB b bMem]
      have bound := slotB b bMem
      have ne : slotOf u b + 1 ≠ k := by omega
      simp [ne]
    rw [stripPEq, List.filter_append, newA, newB]
    simp
  have pivotGap : (strippedP u x).filter (fun s =>
      slotP u x s == k && rel4P u x s == Rel4.gap) = [] := by
    have newA : A.filter (fun s =>
        slotP u x s == k && rel4P u x s == Rel4.gap) = [] := by
      rw [List.filter_eq_nil_iff]
      intro a aMem
      rw [slotPA a aMem, relPA a aMem]
      by_cases pass :
          (slotOf u a == k && rel4 u a == Rel4.gap) = true
      · have data : slotOf u a = k ∧ rel4 u a = Rel4.gap := by
          simpa only [Bool.and_eq_true, beq_iff_eq] using pass
        have reverse := inside_before_same_slot_gap
          singleU (singleA a aMem) relationU data.2
          (by rw [slotX, data.1])
        have forward := leftU a aMem
        omega
      · exact pass
    have newB : B.filter (fun s =>
        slotP u x s == k && rel4P u x s == Rel4.gap) = [] := by
      rw [List.filter_eq_nil_iff]
      intro b bMem
      rw [relPB b bMem]
      simp
    rw [stripPEq, List.filter_append, newA, newB]
    simp
  have blockPivotNew : blockP u x j q =
      if headSpecial then IL ++ [q] else q :: (IL ++ [q]) := by
    simp only [blockP]
    rw [jk, pivotInside, pivotGap]
    simp [headSpecial, List.append_assoc]
  have insertedInside : (strippedP u x).filter (fun s =>
      slotP u x s == k + 1 && rel4P u x s == Rel4.inside) = KR := by
    have newA : A.filter (fun s =>
        slotP u x s == k + 1 && rel4P u x s == Rel4.inside) = [] := by
      rw [List.filter_eq_nil_iff]
      intro a aMem
      rw [slotPA a aMem]
      have bound := slotA a aMem
      have ne : slotOf u a ≠ k + 1 := by omega
      simp [ne]
    have newB : B.filter (fun s =>
        slotP u x s == k + 1 && rel4P u x s == Rel4.inside) = KR := by
      change B.filter (fun s =>
        slotP u x s == k + 1 && rel4P u x s == Rel4.inside) =
        B.filter (fun s => slotOf u s == k)
      apply filter_congr_mem
      intro b bMem
      rw [slotPB b bMem, relPB b bMem]
      have eqSlot : (slotOf u b + 1 == k + 1) =
          (slotOf u b == k) := by
        apply decide_eq_decide.mpr
        omega
      rw [eqSlot]
      simp
    rw [stripPEq, List.filter_append, newA, newB]
    simp
  have insertedGap : (strippedP u x).filter (fun s =>
      slotP u x s == k + 1 && rel4P u x s == Rel4.gap) = [] := by
    rw [stripPEq, List.filter_eq_nil_iff]
    intro s sMem
    rcases List.mem_append.mp sMem with inA | inB
    · rw [slotPA s inA]
      have bound := slotA s inA
      have ne : slotOf u s ≠ k + 1 := by omega
      simp [ne]
    · rw [relPB s inB]
      simp
  have blockInserted : blockP u x k x = x :: (KR ++ [x]) := by
    simp only [blockP]
    rw [insertedInside, insertedGap]
    have regular : (k == 0 && x == u.head) = false := by
      simp [Nat.ne_of_gt kPos]
    rw [regular]
    simp [List.append_assoc]
  have leftSlot : A.filter (fun s => slotOf u s == k) = IL := by
    change A.filter (fun s => slotOf u s == k) = A.filter insidePred
    apply filter_congr_mem
    intro a aMem
    by_cases atK : slotOf u a = k
    · have aInside : rel4 u a = Rel4.inside := by
        cases rel : rel4 u a with
        | before =>
            have zero := slotOf_eq_zero_of_rel_before rel
            omega
        | after =>
            have later := idxOf_lt_of_rel_ne_after_rel_after
              singleU xNotAfter rel
            have earlier := leftU a aMem
            omega
        | inside => rfl
        | gap =>
            have reverse := inside_before_same_slot_gap
              singleU (singleA a aMem) relationU rel
              (by rw [slotX, atK])
            have forward := leftU a aMem
            omega
      simp [insidePred, atK, aInside]
    · simp [insidePred, atK]
  have slotSplit :
      S.filter (fun s => slotOf u s == k) = IL ++ x :: KR := by
    have pass : (slotOf u x == k) = true := by simp [slotX]
    have raw := filter_split_cons (L := strippedSingles u)
      (A := A) (B := B) (x := x) splitU
      (fun s => slotOf u s == k) pass
    rw [leftSlot] at raw
    simpa [S, KR] using raw
  have slotTailNonterminal (nonterminal : k < n) :
      KR = IR ++ G := by
    have whole : S.filter (fun s => slotOf u s == k) =
        insAt u j ++ gapAt u j := by
      simpa [S, j, n, P] using
        slotFilter_eq_ins_gap u (j := k) kPos
          (by simpa [n, P] using nonterminal)
    have whole' : IL ++ x :: KR = (IL ++ x :: IR) ++ G := by
      calc
        IL ++ x :: KR = S.filter (fun s => slotOf u s == k) :=
          slotSplit.symm
        _ = insAt u j ++ gapAt u j := whole
        _ = (IL ++ x :: IR) ++ G := by rw [insPivot]
    have aligned : IL ++ (x :: KR) =
        IL ++ (x :: (IR ++ G)) := by
      simpa [List.append_assoc] using whole'
    simpa using List.append_cancel_left aligned
  have slotTailTerminal (terminal : k = n) :
      KR = IR ++ afterAt u := by
    have whole : S.filter (fun s => slotOf u s == k) =
        insAt u j ++ afterAt u := by
      simpa [S, j, terminal, n, P] using
        slotFilter_terminal_eq_ins_after u
          (by simpa [n, P] using nPos)
    have whole' : IL ++ x :: KR =
        (IL ++ x :: IR) ++ afterAt u := by
      calc
        IL ++ x :: KR = S.filter (fun s => slotOf u s == k) :=
          slotSplit.symm
        _ = insAt u j ++ afterAt u := whole
        _ = (IL ++ x :: IR) ++ afterAt u := by rw [insPivot]
    have aligned : IL ++ (x :: KR) =
        IL ++ (x :: (IR ++ afterAt u)) := by
      simpa [List.append_assoc] using whole'
    simpa using List.append_cancel_left aligned
  have terminalGapNil : gapAt u (n - 1) = [] := by
    unfold gapAt
    have predN : n - 1 + 1 = n := by omega
    rw [predN, List.filter_eq_nil_iff]
    intro s sMem
    by_cases atN : slotOf u s = n
    · have noGap := rel4_ne_gap_of_terminal_slot
        (isSingle_of_mem_stripped sMem)
        (by simpa [n, P] using atN)
      simp [atN, noGap]
    · simp [atN]
  have GNilOfTerminal (terminal : k = n) : G = [] := by
    have index : j = n - 1 := by omega
    dsimp [G]
    rw [index]
    exact terminalGapNil
  have splitStep : ∀ (G' R : List Nat),
      Derives basis
        (⟨u.head,
          pre ++ x :: (IR ++ q :: (G' ++ x :: R))⟩ : Word Nat)
        (⟨u.head,
          pre ++ q :: (x :: (IR ++ G' ++ [x]) ++ R)⟩ : Word Nat) := by
    intro G' R
    cases special : headSpecial with
    | false =>
        simpa [pre, special, List.append_assoc] using
          (macroSplitList u.head preBase q IL x IR G' R)
    | true =>
        have parts : j = 0 ∧ q = u.head := by
          simpa only [headSpecial, Bool.and_eq_true, beq_iff_eq] using special
        simpa [pre, special, parts.2, List.append_assoc] using
          (macroSplitListHead q IL x IR G' R)
  have rangeK : List.range k = List.range j ++ [j] := by
    rw [← jk, List.range_succ]
  have oldPrefixEq :
      beforeAt u ++ (List.range k).flatMap
        (fun i => blockOf u i (P.getD i 0)) =
      pre ++ x :: (IR ++ q :: G) := by
    calc
      beforeAt u ++ (List.range k).flatMap
          (fun i => blockOf u i (P.getD i 0)) =
        preBase ++ blockOf u j q := by
          rw [rangeK, List.flatMap_append, List.flatMap_singleton]
          simp [preBase, q, List.append_assoc]
      _ = preBase ++
          (if headSpecial then IL ++ x :: (IR ++ q :: G)
           else q :: (IL ++ x :: (IR ++ q :: G))) := by
          rw [blockPivotOld]
      _ = pre ++ x :: (IR ++ q :: G) := by
          cases special : headSpecial with
          | false => simp [pre, special, List.append_assoc]
          | true =>
              have baseNil := preBase_eq_nil_of_special special
              simp [pre, special, baseNil, List.append_assoc]
  have earlyBlocksEq :
      (List.range j).flatMap (fun i =>
        blockP u x i ((pseqP u x).getD i 0)) =
      (List.range j).flatMap (fun i =>
        blockOf u i (P.getD i 0)) := by
    apply flatMap_congr_mem
    intro i iMem
    have ij : i < j := List.mem_range.mp iMem
    rw [pseqP_getD_before u x i (by omega)]
    exact blockEarly i _ (by omega)
  have newPrefixEq :
      (strippedP u x).filter (fun s => slotP u x s == 0) ++
        (List.range k).flatMap (fun i =>
          blockP u x i ((pseqP u x).getD i 0)) =
      pre ++ [q] := by
    calc
      (strippedP u x).filter (fun s => slotP u x s == 0) ++
          (List.range k).flatMap (fun i =>
            blockP u x i ((pseqP u x).getD i 0)) =
        preBase ++ blockP u x j q := by
          rw [beforesEq, rangeK, List.flatMap_append,
            List.flatMap_singleton, earlyBlocksEq,
            pseqP_getD_before u x j (by omega)]
          simp [preBase, q, P, List.append_assoc]
      _ = preBase ++
          (if headSpecial then IL ++ [q] else q :: (IL ++ [q])) := by
          rw [blockPivotNew]
      _ = pre ++ [q] := by
          cases special : headSpecial with
          | false => simp [pre, special, List.append_assoc]
          | true =>
              have baseNil := preBase_eq_nil_of_special special
              simp [pre, special, baseNil, List.append_assoc]
  have newAfter : (strippedP u x).filter (fun s =>
      slotP u x s == (pseqP u x).length &&
        rel4P u x s == Rel4.after) = [] := by
    rw [List.filter_eq_nil_iff]
    intro s _
    rw [rel4P_beq_after_false]
    simp
  have shiftedInside : ∀ i, k ≤ i → i < n →
      (strippedP u x).filter (fun s =>
        slotP u x s == (i + 1) + 1 && rel4P u x s == Rel4.inside) =
      S.filter (fun s => slotOf u s == i + 1) := by
    intro i lo hi
    have newA : A.filter (fun s =>
        slotP u x s == (i + 1) + 1 &&
          rel4P u x s == Rel4.inside) = [] := by
      rw [List.filter_eq_nil_iff]
      intro a aMem
      rw [slotPA a aMem]
      have bound := slotA a aMem
      have ne : slotOf u a ≠ (i + 1) + 1 := by omega
      simp [ne]
    have newB : B.filter (fun s =>
        slotP u x s == (i + 1) + 1 &&
          rel4P u x s == Rel4.inside) =
        B.filter (fun s => slotOf u s == i + 1) := by
      apply filter_congr_mem
      intro b bMem
      rw [slotPB b bMem, relPB b bMem]
      have eqSlot : (slotOf u b + 1 == (i + 1) + 1) =
          (slotOf u b == i + 1) := by
        apply decide_eq_decide.mpr
        omega
      rw [eqSlot]
      simp
    have oldA : A.filter (fun s => slotOf u s == i + 1) = [] := by
      rw [List.filter_eq_nil_iff]
      intro a aMem
      have bound := slotA a aMem
      have ne : slotOf u a ≠ i + 1 := by omega
      simp [ne]
    have oldX : (slotOf u x == i + 1) = false := by
      rw [slotX]
      have ne : k ≠ i + 1 := by omega
      simp [ne]
    rw [stripPEq, List.filter_append, newA, newB,
      split, List.filter_append, List.filter_cons, oldA, oldX]
    simp
  have shiftedGapNil : ∀ i, k ≤ i →
      (strippedP u x).filter (fun s =>
        slotP u x s == (i + 1) + 1 && rel4P u x s == Rel4.gap) = [] := by
    intro i lo
    rw [stripPEq, List.filter_eq_nil_iff]
    intro s sMem
    rcases List.mem_append.mp sMem with inA | inB
    · rw [slotPA s inA]
      have bound := slotA s inA
      have ne : slotOf u s ≠ (i + 1) + 1 := by omega
      simp [ne]
    · rw [relPB s inB]
      simp
  have suffixNonfinal : ∀ i, k ≤ i → i + 1 < n →
      suffixShiftBlock u x i =
        absorbB (pullBlockAt u i (P.getD i 0)) := by
    intro i lo hi
    have insideEq : (strippedP u x).filter (fun s =>
        slotP u x s == (i + 1) + 1 &&
          rel4P u x s == Rel4.inside) =
        insAt u i ++ gapAt u i := by
      rw [shiftedInside i lo (by omega)]
      simpa [S, n, P] using
        slotFilter_eq_ins_gap u (j := i + 1) (by omega)
          (by simpa [n, P] using hi)
    have gapNil := shiftedGapNil i lo
    unfold suffixShiftBlock
    rw [pseqP_getD_succ u x i lo
      (by simpa [n, P] using (show i < n by omega))]
    simp only [blockP]
    rw [insideEq, gapNil]
    have regular :
        ((i + 1 == 0) &&
          ((plasmaSeq u).getD i 0 == u.head)) = false := by simp
    rw [regular]
    simp [absorbB, pullBlockAt, P, List.append_assoc]
  have suffixRegular : ∀ i, i ∈ indicesFrom k (n - k) →
      (i == 0 && P.getD i 0 == u.head) = false := by
    intro i iMem
    have bounds := mem_indicesFrom_bounds iMem
    have iPos : 0 < i := Nat.lt_of_lt_of_le kPos bounds.1
    simp [Nat.ne_of_gt iPos]
  have oldBlocksSplit :
      (List.range n).flatMap (fun i => blockOf u i (P.getD i 0)) =
        (List.range k).flatMap (fun i => blockOf u i (P.getD i 0)) ++
          bs.flatMap renderB := by
    simpa [n, P, bs] using
      canonicalBlocks_split u k (by simpa [n, P] using kLe)
        (by
          intro i iMem
          have bounds := mem_indicesFrom_bounds iMem
          have iPos : 0 < i := Nat.lt_of_lt_of_le kPos bounds.1
          simp [Nat.ne_of_gt iPos])
  have sourceTail :
      (beforeAt u ++
          (List.range n).flatMap (fun i => blockOf u i (P.getD i 0)) ++
          afterAt u) ++ [x] =
        pre ++ x ::
          (IR ++ q ::
            (G ++ bs.flatMap renderB ++ afterAt u ++ x :: [])) := by
    rw [oldBlocksSplit]
    calc
      (beforeAt u ++
          ((List.range k).flatMap
              (fun i => blockOf u i (P.getD i 0)) ++
            bs.flatMap renderB) ++ afterAt u) ++ [x] =
        (beforeAt u ++
          (List.range k).flatMap
            (fun i => blockOf u i (P.getD i 0))) ++
          bs.flatMap renderB ++ afterAt u ++ [x] := by
            simp [List.append_assoc]
      _ = (pre ++ x :: (IR ++ q :: G)) ++
          bs.flatMap renderB ++ afterAt u ++ [x] := by
            rw [oldPrefixEq]
      _ = pre ++ x ::
          (IR ++ q ::
            (G ++ bs.flatMap renderB ++ afterAt u ++ x :: [])) := by
            simp [List.append_assoc]
  have sourceEq :
      canonicalize u ++ Word.singleton x =
        (⟨u.head,
          pre ++ x ::
            (IR ++ q ::
              (G ++ bs.flatMap renderB ++ afterAt u ++ x :: []))⟩ :
          Word Nat) := by
    rw [append_mk]
    simp only [canonicalize]
    congr 1
  have newRange :
      List.range (pseqP u x).length =
        List.range k ++ k :: indicesFrom (k + 1) (n - k) := by
    rw [pseqP_length]
    simpa [n, P] using
      range_insert_indices (k := k) (n := n)
        (by simpa [n, P] using kLe)
  change Derives basis
    (canonicalize u ++ Word.singleton x) (canonicalizeP u x)
  by_cases terminal : k = n
  · have tailEq : KR = IR ++ afterAt u :=
      slotTailTerminal terminal
    have gNil : G = [] := GNilOfTerminal terminal
    have bsNil : bs = [] := by
      dsimp [bs, pullSuffix]
      have diff : n - k = 0 := by omega
      rw [diff]
      rfl
    have shiftedNil :
        (indicesFrom (k + 1) (n - k)).flatMap (fun i =>
          blockP u x i ((pseqP u x).getD i 0)) = [] := by
      have diff : n - k = 0 := by omega
      rw [diff]
      rfl
    have newBlocksTerminal :
        (List.range (pseqP u x).length).flatMap (fun i =>
          blockP u x i ((pseqP u x).getD i 0)) =
        (List.range k).flatMap (fun i =>
          blockP u x i ((pseqP u x).getD i 0)) ++
          blockP u x k x := by
      rw [newRange, List.flatMap_append, List.flatMap_cons,
        pseqP_getD_self u x, shiftedNil]
      simp [List.append_assoc]
    have targetTail :
        (strippedP u x).filter (fun s => slotP u x s == 0) ++
            (List.range (pseqP u x).length).flatMap (fun i =>
              blockP u x i ((pseqP u x).getD i 0)) ++
            (strippedP u x).filter (fun s =>
              slotP u x s == (pseqP u x).length &&
                rel4P u x s == Rel4.after) =
          pre ++ q :: (x :: (KR ++ x :: [])) := by
      rw [newAfter, newBlocksTerminal]
      simp only [List.append_nil]
      calc
        (strippedP u x).filter (fun s => slotP u x s == 0) ++
            ((List.range k).flatMap (fun i =>
                blockP u x i ((pseqP u x).getD i 0)) ++
              blockP u x k x) =
          ((strippedP u x).filter (fun s => slotP u x s == 0) ++
            (List.range k).flatMap (fun i =>
              blockP u x i ((pseqP u x).getD i 0))) ++
            blockP u x k x := by
              simp [List.append_assoc]
        _ = (pre ++ [q]) ++ blockP u x k x := by
              rw [newPrefixEq]
        _ = pre ++ q :: (x :: (KR ++ x :: [])) := by
              rw [blockInserted]
              simp [List.append_assoc]
    have targetEq :
        canonicalizeP u x =
          (⟨u.head, pre ++ q :: (x :: (KR ++ x :: []))⟩ : Word Nat) := by
      simp only [canonicalizeP]
      congr 1
    rw [sourceEq, targetEq]
    have pulled :=
      pullBlocksWithTail u.head pre x bs
        (IR ++ q :: G) (afterAt u) []
    have splitFinal := splitStep (G ++ afterAt u) []
    exact Derives.trans
      (by simpa [bsNil, List.append_assoc] using pulled)
      (by simpa [gNil, tailEq, List.append_assoc] using splitFinal)
  · have kLt : k < n := by omega
    have tailEq : KR = IR ++ G := slotTailNonterminal kLt
    have suffixTerminal :
        suffixShiftBlock u x (n - 1) =
          absorbLastB
            (pullBlockAt u (n - 1) (P.getD (n - 1) 0))
            (afterAt u) := by
      have lo : k ≤ n - 1 := by omega
      have hi : n - 1 < n := by omega
      have nPred : n - 1 + 1 = n := by omega
      have insideEq : (strippedP u x).filter (fun s =>
          slotP u x s == n + 1 && rel4P u x s == Rel4.inside) =
          insAt u (n - 1) ++ afterAt u := by
        calc
          (strippedP u x).filter (fun s =>
              slotP u x s == n + 1 && rel4P u x s == Rel4.inside) =
              S.filter (fun s => slotOf u s == n) := by
                simpa [nPred] using shiftedInside (n - 1) lo hi
          _ = insAt u (n - 1) ++ afterAt u := by
                simpa [S, n, P] using
                  slotFilter_terminal_eq_ins_after u
                    (by simpa [n, P] using nPos)
      have gapNil : (strippedP u x).filter (fun s =>
          slotP u x s == n + 1 && rel4P u x s == Rel4.gap) = [] := by
        simpa [nPred] using shiftedGapNil (n - 1) lo
      unfold suffixShiftBlock
      rw [pseqP_getD_succ u x (n - 1) lo hi, nPred]
      simp only [blockP]
      rw [insideEq, gapNil]
      have regular :
          ((n == 0) &&
            ((plasmaSeq u).getD (n - 1) 0 == u.head)) = false := by
        simp [Nat.ne_of_gt nPos]
      rw [regular]
      simp [absorbLastB, pullBlockAt, terminalGapNil, P,
        List.append_assoc]
    have mPos : 0 < n - k := by omega
    let r : Nat := n - k - 1
    have mr : n - k = r + 1 := by
      dsimp [r]
      omega
    have kr : k + r = n - 1 := by omega
    have absorbEq :
        absorbTail bs (afterAt u) =
          (indicesFrom k (n - k)).flatMap (suffixShiftBlock u x) := by
      dsimp [bs]
      rw [mr]
      apply absorbTail_pullSuffix_succ
      · intro i iMem
        have bounds := mem_indicesFrom_bounds iMem
        exact suffixNonfinal i bounds.1 (by omega)
      · simpa [kr] using suffixTerminal
    have bsNonempty : bs ≠ [] := by
      dsimp [bs]
      rw [mr]
      simp [pullSuffix, indicesFrom]
    have shiftedSuffix :
        (indicesFrom (k + 1) (n - k)).flatMap (fun i =>
          blockP u x i ((pseqP u x).getD i 0)) =
          absorbTail bs (afterAt u) := by
      rw [← suffixShift_actual u x k (n - k)]
      exact absorbEq.symm
    have newBlocksSplit :
        (List.range (pseqP u x).length).flatMap (fun i =>
          blockP u x i ((pseqP u x).getD i 0)) =
        (List.range k).flatMap (fun i =>
          blockP u x i ((pseqP u x).getD i 0)) ++
          blockP u x k x ++ absorbTail bs (afterAt u) := by
      rw [newRange, List.flatMap_append, List.flatMap_cons,
        pseqP_getD_self u x, shiftedSuffix]
      simp [List.append_assoc]
    have targetTail :
        (strippedP u x).filter (fun s => slotP u x s == 0) ++
            (List.range (pseqP u x).length).flatMap (fun i =>
              blockP u x i ((pseqP u x).getD i 0)) ++
            (strippedP u x).filter (fun s =>
              slotP u x s == (pseqP u x).length &&
                rel4P u x s == Rel4.after) =
          pre ++ q ::
            (x :: (KR ++ x :: absorbTail bs (afterAt u))) := by
      rw [newAfter, newBlocksSplit]
      simp only [List.append_nil]
      calc
        (strippedP u x).filter (fun s => slotP u x s == 0) ++
            ((List.range k).flatMap (fun i =>
                blockP u x i ((pseqP u x).getD i 0)) ++
              blockP u x k x ++ absorbTail bs (afterAt u)) =
          ((strippedP u x).filter (fun s => slotP u x s == 0) ++
            (List.range k).flatMap (fun i =>
              blockP u x i ((pseqP u x).getD i 0))) ++
            blockP u x k x ++ absorbTail bs (afterAt u) := by
              simp [List.append_assoc]
        _ = (pre ++ [q]) ++ blockP u x k x ++
            absorbTail bs (afterAt u) := by
              rw [newPrefixEq]
        _ = pre ++ q ::
            (x :: (KR ++ x :: absorbTail bs (afterAt u))) := by
              rw [blockInserted]
              simp [List.append_assoc]
    have targetEq :
        canonicalizeP u x =
          (⟨u.head,
            pre ++ q ::
              (x :: (KR ++ x :: absorbTail bs (afterAt u)))⟩ :
            Word Nat) := by
      simp only [canonicalizeP]
      congr 1
    rw [sourceEq, targetEq]
    cases blocksShape : bs with
    | nil => exact False.elim (bsNonempty blocksShape)
    | cons first rest =>
        have pulled :=
          pullBlocksWithTail u.head pre x bs
            (IR ++ q :: G) (afterAt u) []
        have splitFinal := splitStep G (absorbTail bs (afterAt u))
        exact Derives.trans
          (by simpa [blocksShape, List.append_assoc] using pulled)
          (by simpa [blocksShape, tailEq, List.append_assoc] using splitFinal)

private theorem derivesInsertSecond {h x : Nat} {T : List Nat}
    (single : List.count x (h :: T) = 1) :
    Derives basis
      (canonicalize (⟨h, T⟩ : Word Nat) ++ Word.singleton x)
      (canonicalizeP (⟨h, T⟩ : Word Nat) x) := by
  cases relation : rel4 (⟨h, T⟩ : Word Nat) x with
  | before => exact derivesInsertSecondBefore single relation
  | after => exact derivesInsertSecondAfter single relation
  | inside => exact derivesInsertSecondInside single relation
  | gap => exact derivesInsertSecondGap single relation

/-! ## Skeleton normalization -/

/-- A singleton is already in canonical form. -/
private theorem canonicalize_singleton (h : Nat) :
    canonicalize (⟨h, []⟩ : Word Nat) =
      (⟨h, []⟩ : Word Nat) := by
  simp [canonicalize, plasmaSeq, singlesSeq, strippedSingles,
    IsPlasma, letterCount, Word.toList, List.eraseDups_cons]

/-- Every word whose letter counts are at most two derives to its
canonical representative.  The reverse-tail induction exposes a snoc:
fresh letters use the frozen equality, while second occurrences use the
four-way Formula-F dispatcher. -/
private theorem derivesToCanonical :
    ∀ u : Word Nat, (∀ c : Nat, letterCount u c ≤ 2) →
      Derives basis u (canonicalize u) := by
  suffices aux : ∀ (h : Nat) (rt : List Nat),
      (∀ c : Nat,
        letterCount (⟨h, rt.reverse⟩ : Word Nat) c ≤ 2) →
      Derives basis (⟨h, rt.reverse⟩ : Word Nat)
        (canonicalize (⟨h, rt.reverse⟩ : Word Nat)) by
    intro u small
    have run := aux u.head u.tail.reverse (by
      intro c
      simpa using small c)
    rw [List.reverse_reverse] at run
    exact run
  intro h rt
  induction rt with
  | nil =>
      intro _
      simp only [List.reverse_nil]
      rw [canonicalize_singleton]
      exact Derives.refl _
  | cons x rt ih =>
      intro small
      rw [List.reverse_cons] at small ⊢

      have prefixSmall :
          ∀ c : Nat,
            letterCount (⟨h, rt.reverse⟩ : Word Nat) c ≤ 2 := by
        intro c
        have bound := small c
        change ((h :: rt.reverse) ++ [x]).count c ≤ 2 at bound
        change (h :: rt.reverse).count c ≤ 2
        by_cases cx : c = x
        · subst c
          rw [count_append_self] at bound
          omega
        · rw [count_append_ne cx] at bound
          exact bound

      have appendIH :
          Derives basis (⟨h, rt.reverse ++ [x]⟩ : Word Nat)
            (canonicalize (⟨h, rt.reverse⟩ : Word Nat) ++
              Word.singleton x) := by
        simpa [append_mk, Word.singleton] using
          (Derives.appendRight (ih prefixSmall) (Word.singleton x))

      by_cases fresh : x ∉ h :: rt.reverse
      · rw [canonicalize_snoc_fresh fresh]
        exact appendIH
      · have present : x ∈ h :: rt.reverse :=
          Decidable.not_not.mp fresh
        have totalBound := small x
        change ((h :: rt.reverse) ++ [x]).count x ≤ 2 at totalBound
        rw [count_append_self] at totalBound
        have positive : 0 < (h :: rt.reverse).count x :=
          List.count_pos_iff.mpr present
        have single : (h :: rt.reverse).count x = 1 := by
          omega
        rw [canonicalize_snoc_second single]
        exact Derives.trans appendIH
          (derivesInsertSecond
            (h := h) (T := rt.reverse) (x := x) single)

/-! ## Signature bridge and completeness -/

/-- For a strictly rank-sorted list avoiding the cut rank, filtering the
strictly-later elements is the suffix after the strictly-earlier prefix. -/
private theorem filter_after_eq_drop_takeWhile_before
    {L : List Nat} {f : Nat → Nat} {k : Nat}
    (ordered : List.Pairwise (fun a b => f a < f b) L)
    (avoids : ∀ a, a ∈ L → f a ≠ k) :
    L.filter (fun a => k < f a) =
      L.drop (L.takeWhile (fun a => f a < k)).length := by
  induction L with
  | nil => rfl
  | cons a rest ih =>
      rw [List.pairwise_cons] at ordered
      obtain ⟨headOrder, restOrder⟩ := ordered
      have restAvoids : ∀ b, b ∈ rest → f b ≠ k :=
        fun b bMem => avoids b (List.mem_cons_of_mem _ bMem)
      by_cases early : f a < k
      · have earlyTrue : decide (f a < k) = true :=
          decide_eq_true early
        have lateFalse : decide (k < f a) = false :=
          decide_eq_false (by omega)
        simpa [List.filter_cons, lateFalse, List.takeWhile_cons,
          earlyTrue] using ih restOrder restAvoids
      · have late : k < f a := by
          have unequal := avoids a List.mem_cons_self
          omega
        have earlyFalse : decide (f a < k) = false :=
          decide_eq_false early
        have lateTrue : decide (k < f a) = true :=
          decide_eq_true late
        have restSelf : rest.filter (fun b => k < f b) = rest := by
          rw [List.filter_eq_self]
          intro b bMem
          show decide (k < f b) = true
          exact decide_eq_true
            (Nat.lt_trans late (headOrder b bMem))
        simp [List.filter_cons, lateTrue, List.takeWhile_cons,
          earlyFalse, restSelf]

/-- A count-one letter cannot itself be a plasma letter. -/
private theorem not_mem_plasmaSeq_of_single {u : Word Nat} {s : Nat}
    (single : IsSingle u s) : s ∉ plasmaSeq u := by
  intro sPlasma
  have big := (List.mem_filter.mp sPlasma).2
  have countBig : 2 ≤ u.toList.count s := by
    simpa [plasmaSeq] using big
  have countOne : u.toList.count s = 1 := single
  omega

/-- Opens after a single are exactly the plasma suffix after its slot. -/
private theorem beforeOpenList_eq_drop_slotOf {u : Word Nat} {s : Nat}
    (single : IsSingle u s) :
    beforeOpenList u s = (plasmaSeq u).drop (slotOf u s) := by
  unfold beforeOpenList slotOf
  apply filter_after_eq_drop_takeWhile_before
  · exact plasmaSeq_pairwise_idxOf u
  · intro p pMem equal
    have pIn : p ∈ u.toList := mem_toList_of_mem_plasmaSeq pMem
    have ps : p = s := idxOf_inj_local pIn equal
    exact (not_mem_plasmaSeq_of_single single) (ps ▸ pMem)

/-- The slot is determined by the plasma sequence and opens-after list. -/
private theorem slotOf_eq_length_sub_beforeOpenList
    {u : Word Nat} {s : Nat} (single : IsSingle u s) :
    slotOf u s =
      (plasmaSeq u).length - (beforeOpenList u s).length := by
  have bound : slotOf u s ≤ (plasmaSeq u).length :=
    slotOf_le_length u s
  rw [beforeOpenList_eq_drop_slotOf single, List.length_drop]
  omega

/-- Signature equality transports the slot of every source single. -/
private theorem slotOf_eq_of_sameSignature
    {u v : Word Nat} {s : Nat}
    (same : SameD378Signature u v) (single : IsSingle u s) :
    slotOf u s = slotOf v s := by
  have coord := same.2.2.2 s single
  have singleV := isSingle_of_sameSignature same single
  calc
    slotOf u s =
        (plasmaSeq u).length - (beforeOpenList u s).length :=
      slotOf_eq_length_sub_beforeOpenList single
    _ = (plasmaSeq v).length - (beforeOpenList v s).length := by
      rw [same.2.2.1, coord.1]
    _ = slotOf v s :=
      (slotOf_eq_length_sub_beforeOpenList singleV).symm

/-- Plasma membership is exactly multiplicity at least two. -/
private theorem isPlasma_iff_mem_plasmaSeq (u : Word Nat) (x : Nat) :
    IsPlasma u x ↔ x ∈ plasmaSeq u := by
  constructor
  · intro multiple
    apply List.mem_filter.mpr
    constructor
    · apply mem_eraseDups_of_mem
      apply List.count_pos_iff.mp
      have data := multiple
      unfold IsPlasma letterCount at data
      omega
    · simpa [plasmaSeq, IsPlasma, letterCount] using multiple
  · intro member
    have kept := (List.mem_filter.mp member).2
    simpa [plasmaSeq, IsPlasma, letterCount] using kept

/-- Head stripping depends only on the signature's head, singles, and
plasma sequence. -/
private theorem strippedSingles_eq_of_sameSignature {u v : Word Nat}
    (same : SameD378Signature u v) :
    strippedSingles u = strippedSingles v := by
  have plasmaIff : IsPlasma u u.head ↔ IsPlasma v v.head := by
    rw [isPlasma_iff_mem_plasmaSeq u u.head,
      isPlasma_iff_mem_plasmaSeq v v.head,
      same.2.2.1, same.1]
  have plasmaBool : decide (IsPlasma u u.head) =
      decide (IsPlasma v v.head) := decide_eq_decide.mpr plasmaIff
  unfold strippedSingles
  rw [same.2.1, plasmaBool, same.1]

/-- Equal D_378 signatures have literally equal canonical words. -/
theorem canonicalizeEqOfSameSignature {u v : Word Nat}
    (same : SameD378Signature u v) :
    canonicalize u = canonicalize v := by
  have strippedEq := strippedSingles_eq_of_sameSignature same
  have predSlot : ∀ (n s : Nat), s ∈ strippedSingles u →
      (slotOf u s == n) = (slotOf v s == n) := by
    intro n s sMem
    rw [slotOf_eq_of_sameSignature same (isSingle_of_mem_stripped sMem)]
  have predRel : ∀ (r : Rel4) (s : Nat), s ∈ strippedSingles u →
      (rel4 u s == r) = (rel4 v s == r) := by
    intro r s sMem
    rw [(same.2.2.2 s (isSingle_of_mem_stripped sMem)).2]
  simp only [canonicalize, blockOf]
  rw [← same.1, ← same.2.2.1, ← strippedEq]
  congr 1
  congr 1
  · congr 1
    · apply filter_congr_mem
      intro s sMem
      exact predSlot 0 s sMem
    · apply flatMap_congr_mem
      intro i _
      have insEq : (strippedSingles u).filter
          (fun s => slotOf u s == i + 1 && rel4 u s == Rel4.inside) =
          (strippedSingles u).filter
          (fun s => slotOf v s == i + 1 && rel4 v s == Rel4.inside) := by
        apply filter_congr_mem
        intro s sMem
        rw [predSlot (i + 1) s sMem, predRel Rel4.inside s sMem]
      have gapEq : (strippedSingles u).filter
          (fun s => slotOf u s == i + 1 && rel4 u s == Rel4.gap) =
          (strippedSingles u).filter
          (fun s => slotOf v s == i + 1 && rel4 v s == Rel4.gap) := by
        apply filter_congr_mem
        intro s sMem
        rw [predSlot (i + 1) s sMem, predRel Rel4.gap s sMem]
      rw [insEq, gapEq]
  · apply filter_congr_mem
    intro s sMem
    rw [predSlot _ s sMem, predRel Rel4.after s sMem]

/-- Every word derives through a signature-equal skeleton to its canonical
representative. -/
private theorem derivesToCanonicalAll (u : Word Nat) :
    Derives basis u (canonicalize u) := by
  obtain ⟨skeleton, collapse, same, bounded⟩ :=
    collapseToSkeleton u.tail.length u (Nat.le_refl _)
  have normalize := derivesToCanonical skeleton bounded
  rw [← canonicalizeEqOfSameSignature same] at normalize
  exact Derives.trans collapse normalize

/-- The displayed seven-law basis derives every pair of words with the same
D_378 signature. -/
theorem derivesOfSameD378 {u v : Word Nat}
    (same : SameD378Signature u v) : Derives basis u v := by
  have left := derivesToCanonicalAll u
  rw [canonicalizeEqOfSameSignature same] at left
  exact Derives.trans left (Derives.symm (derivesToCanonicalAll v))

-- D378_FORMULA_F_REPLAY_BEGIN
/-! ## Formula-F deterministic oracle replay (generated) -/
-- Generator: research/formalization/order6/accelerator/generate_d378_formula_f_replay.py
-- Full sweep: 3207/3207 zero mismatch
-- Full manifest SHA-256: d60ec8be37efee697946096ad85a82c1fe068a0f74bfa5099c0ae4031bc8a581
-- Sample rule: first 200 by SHA-256 rank seeded with D378-canonicalizeP-v1
-- Sample manifest SHA-256: 494546a0310a38194f837155bfec7a03042bd67b997f5a47fddaa0a524d2d5df
-- Do not edit this block by hand.

-- sample 001; key=4|0,0,3,2,2|3; rel4=gap; rank_sha256=00137837e7d6dd3eda586bde590f5618e7375033612af112f68543796da0d99e
example :
    ((canonicalizeP (⟨0, [0, 3, 2, 2]⟩ : Word Nat) 3).toList = [0, 0, 3, 3, 2, 2]) ∧
      ((canonicalize (⟨0, [0, 3, 2, 2, 3]⟩ : Word Nat)).toList = [0, 0, 3, 3, 2, 2]) := by decide

-- sample 002; key=4|0,1,0,3,1|3; rel4=inside; rank_sha256=00149fa1c3233be320807682f4d68229322e8bf2e55a4fbf61ef679e6a6002b9
example :
    ((canonicalizeP (⟨0, [1, 0, 3, 1]⟩ : Word Nat) 3).toList = [0, 0, 1, 1, 3, 3]) ∧
      ((canonicalize (⟨0, [1, 0, 3, 1, 3]⟩ : Word Nat)).toList = [0, 0, 1, 1, 3, 3]) := by decide

-- sample 003; key=4|3,2,2,2,0|0; rel4=after; rank_sha256=0036c3a5e0c1076740ff819ae138c7c897ae97bcd32310ac2106e7aba7376287
example :
    ((canonicalizeP (⟨3, [2, 2, 2, 0]⟩ : Word Nat) 0).toList = [3, 2, 2, 0, 0]) ∧
      ((canonicalize (⟨3, [2, 2, 2, 0, 0]⟩ : Word Nat)).toList = [3, 2, 2, 0, 0]) := by decide

-- sample 004; key=4|2,2,0,1,2|1; rel4=inside; rank_sha256=003cf23e330d75673cf9377544846901d6030f81bd94dad553ee8dac105ed7f2
example :
    ((canonicalizeP (⟨2, [2, 0, 1, 2]⟩ : Word Nat) 1).toList = [2, 0, 2, 1, 1]) ∧
      ((canonicalize (⟨2, [2, 0, 1, 2, 1]⟩ : Word Nat)).toList = [2, 0, 2, 1, 1]) := by decide

-- sample 005; key=4|3,2,0,1,2|3; rel4=before; rank_sha256=004dbec4501103f1258fc57e888084f4b6aacb902654779d832ae60d07324b7a
example :
    ((canonicalizeP (⟨3, [2, 0, 1, 2]⟩ : Word Nat) 3).toList = [3, 3, 2, 0, 1, 2]) ∧
      ((canonicalize (⟨3, [2, 0, 1, 2, 3]⟩ : Word Nat)).toList = [3, 3, 2, 0, 1, 2]) := by decide

-- sample 006; key=3|0,2,2,2,1,2|1; rel4=inside; rank_sha256=008a625ff5dea388b58930a11ea2741320e6cee7fa37d8e81c61c5a1dc5d87f6
example :
    ((canonicalizeP (⟨0, [2, 2, 2, 1, 2]⟩ : Word Nat) 1).toList = [0, 2, 2, 1, 1]) ∧
      ((canonicalize (⟨0, [2, 2, 2, 1, 2, 1]⟩ : Word Nat)).toList = [0, 2, 2, 1, 1]) := by decide

-- sample 007; key=3|0,0,0,0,1,2|1; rel4=after; rank_sha256=008bb5536bfdabd4768db4ad27fdb4f4bf192ac6df9be0a4f7a67a7b40debcc1
example :
    ((canonicalizeP (⟨0, [0, 0, 0, 1, 2]⟩ : Word Nat) 1).toList = [0, 0, 1, 2, 1]) ∧
      ((canonicalize (⟨0, [0, 0, 0, 1, 2, 1]⟩ : Word Nat)).toList = [0, 0, 1, 2, 1]) := by decide

-- sample 008; key=3|1,0,1,2|2; rel4=after; rank_sha256=00a2aa811ddfa2a0e9f2ac7a35c8fd3ee3772c3f58b0ccbcfe8894248996db63
example :
    ((canonicalizeP (⟨1, [0, 1, 2]⟩ : Word Nat) 2).toList = [1, 0, 1, 2, 2]) ∧
      ((canonicalize (⟨1, [0, 1, 2, 2]⟩ : Word Nat)).toList = [1, 0, 1, 2, 2]) := by decide

-- sample 009; key=4|0,0,1,3|1; rel4=after; rank_sha256=00c3eb501ad6b2e27df80283db63e368080fee6aa4c5309ff2b167d550c2a5ad
example :
    ((canonicalizeP (⟨0, [0, 1, 3]⟩ : Word Nat) 1).toList = [0, 0, 1, 3, 1]) ∧
      ((canonicalize (⟨0, [0, 1, 3, 1]⟩ : Word Nat)).toList = [0, 0, 1, 3, 1]) := by decide

-- sample 010; key=4|2,2,3,0|3; rel4=after; rank_sha256=00f8c66bdc3c1cc4993ff3fcf368632029e99ad16bbe217798309f97037ba1f5
example :
    ((canonicalizeP (⟨2, [2, 3, 0]⟩ : Word Nat) 3).toList = [2, 2, 3, 0, 3]) ∧
      ((canonicalize (⟨2, [2, 3, 0, 3]⟩ : Word Nat)).toList = [2, 2, 3, 0, 3]) := by decide

-- sample 011; key=4|0,0,0,2,3|3; rel4=after; rank_sha256=012286a84b7ff6347d0be5a9c3984532decdd61088ce8d2fc0bf6370e1b3249e
example :
    ((canonicalizeP (⟨0, [0, 0, 2, 3]⟩ : Word Nat) 3).toList = [0, 0, 2, 3, 3]) ∧
      ((canonicalize (⟨0, [0, 0, 2, 3, 3]⟩ : Word Nat)).toList = [0, 0, 2, 3, 3]) := by decide

-- sample 012; key=4|2,1,0,2,3|0; rel4=inside; rank_sha256=0131817d7900bd5f830a60df2c49eb08afd9a81ee6671747ec5bc01b97b48883
example :
    ((canonicalizeP (⟨2, [1, 0, 2, 3]⟩ : Word Nat) 0).toList = [2, 1, 2, 0, 3, 0]) ∧
      ((canonicalize (⟨2, [1, 0, 2, 3, 0]⟩ : Word Nat)).toList = [2, 1, 2, 0, 3, 0]) := by decide

-- sample 013; key=3|1,2,2,0,2,2|0; rel4=inside; rank_sha256=0132ae07a9471ce78dcda0f8cffc95d50da53723bc2abaa4fc481bcb52ec3bec
example :
    ((canonicalizeP (⟨1, [2, 2, 0, 2, 2]⟩ : Word Nat) 0).toList = [1, 2, 2, 0, 0]) ∧
      ((canonicalize (⟨1, [2, 2, 0, 2, 2, 0]⟩ : Word Nat)).toList = [1, 2, 2, 0, 0]) := by decide

-- sample 014; key=4|0,0,2,1,0|1; rel4=inside; rank_sha256=013979b6df865a278ed815cdba378e574e41b49a1ff666c8bb39d577bf78b8eb
example :
    ((canonicalizeP (⟨0, [0, 2, 1, 0]⟩ : Word Nat) 1).toList = [0, 2, 0, 1, 1]) ∧
      ((canonicalize (⟨0, [0, 2, 1, 0, 1]⟩ : Word Nat)).toList = [0, 2, 0, 1, 1]) := by decide

-- sample 015; key=3|1,1,2|2; rel4=after; rank_sha256=013f242d56e82eb9343c5dc0c419280d081b5a1cc0d9350426a20f0e4c2fa606
example :
    ((canonicalizeP (⟨1, [1, 2]⟩ : Word Nat) 2).toList = [1, 1, 2, 2]) ∧
      ((canonicalize (⟨1, [1, 2, 2]⟩ : Word Nat)).toList = [1, 1, 2, 2]) := by decide

-- sample 016; key=4|3,0,1,2|2; rel4=before; rank_sha256=0143b05653471a00d9a382bf110e38702509fd5e167bb4e4dc98c9a18abdb758
example :
    ((canonicalizeP (⟨3, [0, 1, 2]⟩ : Word Nat) 2).toList = [3, 0, 1, 2, 2]) ∧
      ((canonicalize (⟨3, [0, 1, 2, 2]⟩ : Word Nat)).toList = [3, 0, 1, 2, 2]) := by decide

-- sample 017; key=4|3,2,1,1,3|2; rel4=inside; rank_sha256=01452f2a8e8c825ac1f1731ec14a25de5a82dbcddbb383687758021043a60691
example :
    ((canonicalizeP (⟨3, [2, 1, 1, 3]⟩ : Word Nat) 2).toList = [3, 3, 2, 2, 1, 1]) ∧
      ((canonicalize (⟨3, [2, 1, 1, 3, 2]⟩ : Word Nat)).toList = [3, 3, 2, 2, 1, 1]) := by decide

-- sample 018; key=3|1,1,0,2,0,1|2; rel4=inside; rank_sha256=014c388b557349c8c0775862054e53ef4b922049335617744e06d19698a781d8
example :
    ((canonicalizeP (⟨1, [1, 0, 2, 0, 1]⟩ : Word Nat) 2).toList = [1, 1, 0, 0, 2, 2]) ∧
      ((canonicalize (⟨1, [1, 0, 2, 0, 1, 2]⟩ : Word Nat)).toList = [1, 1, 0, 0, 2, 2]) := by decide

-- sample 019; key=4|3,0,2,2,2|0; rel4=before; rank_sha256=014ee255d1152dc3ce077ff82b899a0c8fe997f834839d0eb7196a938c89860e
example :
    ((canonicalizeP (⟨3, [0, 2, 2, 2]⟩ : Word Nat) 0).toList = [3, 0, 0, 2, 2]) ∧
      ((canonicalize (⟨3, [0, 2, 2, 2, 0]⟩ : Word Nat)).toList = [3, 0, 0, 2, 2]) := by decide

-- sample 020; key=4|1,3,0,0,0|1; rel4=before; rank_sha256=0155e0785670ebd1bd3da040adc5a7f8fa94ad02e00807c85cfc86e93a7a2b24
example :
    ((canonicalizeP (⟨1, [3, 0, 0, 0]⟩ : Word Nat) 1).toList = [1, 3, 1, 0, 0]) ∧
      ((canonicalize (⟨1, [3, 0, 0, 0, 1]⟩ : Word Nat)).toList = [1, 3, 1, 0, 0]) := by decide

-- sample 021; key=4|1,0,1,2,1|2; rel4=inside; rank_sha256=017d7e68b701dd6969047a5160c2839b4a180b065734105d5ea4196f51c7a441
example :
    ((canonicalizeP (⟨1, [0, 1, 2, 1]⟩ : Word Nat) 2).toList = [1, 0, 1, 2, 2]) ∧
      ((canonicalize (⟨1, [0, 1, 2, 1, 2]⟩ : Word Nat)).toList = [1, 0, 1, 2, 2]) := by decide

-- sample 022; key=4|0,1,2,2|1; rel4=before; rank_sha256=0188f21941bd08b2603bb004dcb63fe38d63f6bd6791189105538c9b17c08ddc
example :
    ((canonicalizeP (⟨0, [1, 2, 2]⟩ : Word Nat) 1).toList = [0, 1, 1, 2, 2]) ∧
      ((canonicalize (⟨0, [1, 2, 2, 1]⟩ : Word Nat)).toList = [0, 1, 1, 2, 2]) := by decide

-- sample 023; key=4|3,3,2,0|0; rel4=after; rank_sha256=01908d9f87ff69d3d25c32c5fbef363d460f9b7e0cf9806113b846c2c4c481e0
example :
    ((canonicalizeP (⟨3, [3, 2, 0]⟩ : Word Nat) 0).toList = [3, 3, 2, 0, 0]) ∧
      ((canonicalize (⟨3, [3, 2, 0, 0]⟩ : Word Nat)).toList = [3, 3, 2, 0, 0]) := by decide

-- sample 024; key=3|2,2,2,0,1|1; rel4=after; rank_sha256=0190efc1d1cbb2e2e43e3ce5df3136e4f383382a5322f87b8c74a858907a2931
example :
    ((canonicalizeP (⟨2, [2, 2, 0, 1]⟩ : Word Nat) 1).toList = [2, 2, 0, 1, 1]) ∧
      ((canonicalize (⟨2, [2, 2, 0, 1, 1]⟩ : Word Nat)).toList = [2, 2, 0, 1, 1]) := by decide

-- sample 025; key=3|2,1,1,0,0|2; rel4=before; rank_sha256=0197f791d99186dba78ed409f35a89d12c6205b805687fbba185d007d1442000
example :
    ((canonicalizeP (⟨2, [1, 1, 0, 0]⟩ : Word Nat) 2).toList = [2, 2, 1, 1, 0, 0]) ∧
      ((canonicalize (⟨2, [1, 1, 0, 0, 2]⟩ : Word Nat)).toList = [2, 2, 1, 1, 0, 0]) := by decide

-- sample 026; key=4|3,2,0,1,2|1; rel4=inside; rank_sha256=01a760b42046bd9597a9db3233a48d5f29e02f5df9897ce7332385c98c0ce879
example :
    ((canonicalizeP (⟨3, [2, 0, 1, 2]⟩ : Word Nat) 1).toList = [3, 2, 0, 2, 1, 1]) ∧
      ((canonicalize (⟨3, [2, 0, 1, 2, 1]⟩ : Word Nat)).toList = [3, 2, 0, 2, 1, 1]) := by decide

-- sample 027; key=4|2,1,0,3|1; rel4=before; rank_sha256=01bc5a650ce2317e8d8fb76fb1e25cdaeafb2d3b3b51be28952c5e583c5ef250
example :
    ((canonicalizeP (⟨2, [1, 0, 3]⟩ : Word Nat) 1).toList = [2, 1, 0, 3, 1]) ∧
      ((canonicalize (⟨2, [1, 0, 3, 1]⟩ : Word Nat)).toList = [2, 1, 0, 3, 1]) := by decide

-- sample 028; key=4|3,2|2; rel4=before; rank_sha256=01c3635911612004bae91695d1b5eefb4fcc63ace36254839132c937825af7ac
example :
    ((canonicalizeP (⟨3, [2]⟩ : Word Nat) 2).toList = [3, 2, 2]) ∧
      ((canonicalize (⟨3, [2, 2]⟩ : Word Nat)).toList = [3, 2, 2]) := by decide

-- sample 029; key=4|0,1,2,3|2; rel4=before; rank_sha256=01d9b49388a28333b0986bd1e1af604f1cebbe2b35294f974a8420dd64f4e491
example :
    ((canonicalizeP (⟨0, [1, 2, 3]⟩ : Word Nat) 2).toList = [0, 1, 2, 3, 2]) ∧
      ((canonicalize (⟨0, [1, 2, 3, 2]⟩ : Word Nat)).toList = [0, 1, 2, 3, 2]) := by decide

-- sample 030; key=3|1,2,2,2,2,0|1; rel4=before; rank_sha256=01db89a1a7f2195dee5382b3d8d3ab3ed19ab41378a805bf2ba2f81c5d148166
example :
    ((canonicalizeP (⟨1, [2, 2, 2, 2, 0]⟩ : Word Nat) 1).toList = [1, 1, 2, 0, 2]) ∧
      ((canonicalize (⟨1, [2, 2, 2, 2, 0, 1]⟩ : Word Nat)).toList = [1, 1, 2, 0, 2]) := by decide

-- sample 031; key=4|1,2,3|3; rel4=before; rank_sha256=022f6fb409461b18555eb1f18c6f339d93f0b71a2d1ad272949b9a3822a9d499
example :
    ((canonicalizeP (⟨1, [2, 3]⟩ : Word Nat) 3).toList = [1, 2, 3, 3]) ∧
      ((canonicalize (⟨1, [2, 3, 3]⟩ : Word Nat)).toList = [1, 2, 3, 3]) := by decide

-- sample 032; key=3|2,1,0,1,0,0|2; rel4=before; rank_sha256=02459aa99aacb69cb382b124669eff40933ecfd839373af5b81c6684a1190f71
example :
    ((canonicalizeP (⟨2, [1, 0, 1, 0, 0]⟩ : Word Nat) 2).toList = [2, 2, 1, 1, 0, 0]) ∧
      ((canonicalize (⟨2, [1, 0, 1, 0, 0, 2]⟩ : Word Nat)).toList = [2, 2, 1, 1, 0, 0]) := by decide

-- sample 033; key=4|3,0,2,0|2; rel4=inside; rank_sha256=0260ba3ecd516af3abbe8d2845063472b15b76ca6fa89f641610e21f68f1f6e5
example :
    ((canonicalizeP (⟨3, [0, 2, 0]⟩ : Word Nat) 2).toList = [3, 0, 0, 2, 2]) ∧
      ((canonicalize (⟨3, [0, 2, 0, 2]⟩ : Word Nat)).toList = [3, 0, 0, 2, 2]) := by decide

-- sample 034; key=3|0,1,0,0,2,0|1; rel4=inside; rank_sha256=026ad09173c9b7e3052166cc82f8940bc8fd25b3ac8a35bf78830fa8b9464251
example :
    ((canonicalizeP (⟨0, [1, 0, 0, 2, 0]⟩ : Word Nat) 1).toList = [0, 0, 1, 2, 1]) ∧
      ((canonicalize (⟨0, [1, 0, 0, 2, 0, 1]⟩ : Word Nat)).toList = [0, 0, 1, 2, 1]) := by decide

-- sample 035; key=3|2,1,0,1,2,2|0; rel4=inside; rank_sha256=026cc4e29767dbfb29e5f02e46975a1e13606bb6be94089fc7edfcd2dc529e1e
example :
    ((canonicalizeP (⟨2, [1, 0, 1, 2, 2]⟩ : Word Nat) 0).toList = [2, 2, 1, 1, 0, 0]) ∧
      ((canonicalize (⟨2, [1, 0, 1, 2, 2, 0]⟩ : Word Nat)).toList = [2, 2, 1, 1, 0, 0]) := by decide

-- sample 036; key=4|2,1,3,0|2; rel4=before; rank_sha256=0281a1309ce0582263a834a81da29cb001ce025cc95449bb0e72dcef3bdec664
example :
    ((canonicalizeP (⟨2, [1, 3, 0]⟩ : Word Nat) 2).toList = [2, 1, 3, 0, 2]) ∧
      ((canonicalize (⟨2, [1, 3, 0, 2]⟩ : Word Nat)).toList = [2, 1, 3, 0, 2]) := by decide

-- sample 037; key=3|1,1,1,2,1|2; rel4=inside; rank_sha256=028650e4e0ca3ebd48cbd256d775d7c8aba91439106df7d913420f1856a678cb
example :
    ((canonicalizeP (⟨1, [1, 1, 2, 1]⟩ : Word Nat) 2).toList = [1, 1, 2, 2]) ∧
      ((canonicalize (⟨1, [1, 1, 2, 1, 2]⟩ : Word Nat)).toList = [1, 1, 2, 2]) := by decide

-- sample 038; key=3|0,1,2,1,1|0; rel4=before; rank_sha256=029e22a83fa9b3c6fc8ecec53ca00ad9cf9a7268c3c19f6749c310f8f833dbd1
example :
    ((canonicalizeP (⟨0, [1, 2, 1, 1]⟩ : Word Nat) 0).toList = [0, 0, 1, 2, 1]) ∧
      ((canonicalize (⟨0, [1, 2, 1, 1, 0]⟩ : Word Nat)).toList = [0, 0, 1, 2, 1]) := by decide

-- sample 039; key=4|1,1,2,0,3|2; rel4=after; rank_sha256=02d9f6f56afd262f7388d087c44e9188b9abbc697e50bbb59ceb31cdc019eb40
example :
    ((canonicalizeP (⟨1, [1, 2, 0, 3]⟩ : Word Nat) 2).toList = [1, 1, 2, 0, 3, 2]) ∧
      ((canonicalize (⟨1, [1, 2, 0, 3, 2]⟩ : Word Nat)).toList = [1, 1, 2, 0, 3, 2]) := by decide

-- sample 040; key=4|0,3,3,2|2; rel4=after; rank_sha256=02dd203e80bc39fa7ac66d7361a0fca7432afc4985e7e3a9b0693b025fff9183
example :
    ((canonicalizeP (⟨0, [3, 3, 2]⟩ : Word Nat) 2).toList = [0, 3, 3, 2, 2]) ∧
      ((canonicalize (⟨0, [3, 3, 2, 2]⟩ : Word Nat)).toList = [0, 3, 3, 2, 2]) := by decide

-- sample 041; key=3|1,0,0,0,2|1; rel4=before; rank_sha256=0304a82179c3da53641d003cbb0987f0c6e59c0876f6a243e8f68d8d585eaf20
example :
    ((canonicalizeP (⟨1, [0, 0, 0, 2]⟩ : Word Nat) 1).toList = [1, 1, 0, 2, 0]) ∧
      ((canonicalize (⟨1, [0, 0, 0, 2, 1]⟩ : Word Nat)).toList = [1, 1, 0, 2, 0]) := by decide

-- sample 042; key=4|1,0,2,1,1|0; rel4=inside; rank_sha256=03093c3a7b7be4fdfdfebdb3e4d62a2ec141c4e2faae858df83f237d95bb409d
example :
    ((canonicalizeP (⟨1, [0, 2, 1, 1]⟩ : Word Nat) 0).toList = [1, 1, 0, 2, 0]) ∧
      ((canonicalize (⟨1, [0, 2, 1, 1, 0]⟩ : Word Nat)).toList = [1, 1, 0, 2, 0]) := by decide

-- sample 043; key=4|2,1,3,1,1|3; rel4=inside; rank_sha256=032358f951c3d5fd30f20ad8b377684c4562c1f1be1323f2eb20f80b727ff7a4
example :
    ((canonicalizeP (⟨2, [1, 3, 1, 1]⟩ : Word Nat) 3).toList = [2, 1, 1, 3, 3]) ∧
      ((canonicalize (⟨2, [1, 3, 1, 1, 3]⟩ : Word Nat)).toList = [2, 1, 1, 3, 3]) := by decide

-- sample 044; key=4|2,1,2,2,3|3; rel4=after; rank_sha256=032a5ea738c9ecab5d0edc094148460685adc5f47ad093cb389febf15f014094
example :
    ((canonicalizeP (⟨2, [1, 2, 2, 3]⟩ : Word Nat) 3).toList = [2, 1, 2, 3, 3]) ∧
      ((canonicalize (⟨2, [1, 2, 2, 3, 3]⟩ : Word Nat)).toList = [2, 1, 2, 3, 3]) := by decide

-- sample 045; key=4|1,3,3,3,0|1; rel4=before; rank_sha256=035c235f3ce774ea2571b1ab8953db211e5e412d73c9bec52e8394f0fb18d1a2
example :
    ((canonicalizeP (⟨1, [3, 3, 3, 0]⟩ : Word Nat) 1).toList = [1, 1, 3, 0, 3]) ∧
      ((canonicalize (⟨1, [3, 3, 3, 0, 1]⟩ : Word Nat)).toList = [1, 1, 3, 0, 3]) := by decide

-- sample 046; key=4|1,1,1,0,1|0; rel4=inside; rank_sha256=038519063ead3d8d740c747b1d136468f8576b7901407aee5a163fec67ec750e
example :
    ((canonicalizeP (⟨1, [1, 1, 0, 1]⟩ : Word Nat) 0).toList = [1, 1, 0, 0]) ∧
      ((canonicalize (⟨1, [1, 1, 0, 1, 0]⟩ : Word Nat)).toList = [1, 1, 0, 0]) := by decide

-- sample 047; key=4|2,1,1,0,1|0; rel4=inside; rank_sha256=0385c58612e1352520811451a2e9e9c910eab490a817faeb05c8ea88111cd3f7
example :
    ((canonicalizeP (⟨2, [1, 1, 0, 1]⟩ : Word Nat) 0).toList = [2, 1, 1, 0, 0]) ∧
      ((canonicalize (⟨2, [1, 1, 0, 1, 0]⟩ : Word Nat)).toList = [2, 1, 1, 0, 0]) := by decide

-- sample 048; key=3|2,2,1|1; rel4=after; rank_sha256=03960bf39d744e1a5f4a3c93a6b82f7080352d44825adab2e2179b57831a0b8c
example :
    ((canonicalizeP (⟨2, [2, 1]⟩ : Word Nat) 1).toList = [2, 2, 1, 1]) ∧
      ((canonicalize (⟨2, [2, 1, 1]⟩ : Word Nat)).toList = [2, 2, 1, 1]) := by decide

-- sample 049; key=3|1,1,0,2,1,1|2; rel4=inside; rank_sha256=039bb3d459c0aeced71f8b657bc577b68b90d7b6cde99a497fb6190d5eaa670b
example :
    ((canonicalizeP (⟨1, [1, 0, 2, 1, 1]⟩ : Word Nat) 2).toList = [1, 0, 1, 2, 2]) ∧
      ((canonicalize (⟨1, [1, 0, 2, 1, 1, 2]⟩ : Word Nat)).toList = [1, 0, 1, 2, 2]) := by decide

-- sample 050; key=3|2,2,2,0,1|0; rel4=after; rank_sha256=03b34f8947c3d37407cc2ae8e9eabdda3047b3bef986f0b31f03ad5dcec7020a
example :
    ((canonicalizeP (⟨2, [2, 2, 0, 1]⟩ : Word Nat) 0).toList = [2, 2, 0, 1, 0]) ∧
      ((canonicalize (⟨2, [2, 2, 0, 1, 0]⟩ : Word Nat)).toList = [2, 2, 0, 1, 0]) := by decide

-- sample 051; key=4|3,1,1,1,0|0; rel4=after; rank_sha256=03bccdb69faf5ed4b681108fe7392a821d853d9b5481d9f7313bb65aa2eb1e59
example :
    ((canonicalizeP (⟨3, [1, 1, 1, 0]⟩ : Word Nat) 0).toList = [3, 1, 1, 0, 0]) ∧
      ((canonicalize (⟨3, [1, 1, 1, 0, 0]⟩ : Word Nat)).toList = [3, 1, 1, 0, 0]) := by decide

-- sample 052; key=3|0,1,1,2,1|2; rel4=inside; rank_sha256=03c3c6d45f2c59f46099b2593c3c7e839c02222a494558f74db7ef5da0f51c32
example :
    ((canonicalizeP (⟨0, [1, 1, 2, 1]⟩ : Word Nat) 2).toList = [0, 1, 1, 2, 2]) ∧
      ((canonicalize (⟨0, [1, 1, 2, 1, 2]⟩ : Word Nat)).toList = [0, 1, 1, 2, 2]) := by decide

-- sample 053; key=4|2,2,2,2,0|0; rel4=after; rank_sha256=03d9539b9cc2965839517af9fc2cda1a900f6f1e855ac903301db0a4998822b4
example :
    ((canonicalizeP (⟨2, [2, 2, 2, 0]⟩ : Word Nat) 0).toList = [2, 2, 0, 0]) ∧
      ((canonicalize (⟨2, [2, 2, 2, 0, 0]⟩ : Word Nat)).toList = [2, 2, 0, 0]) := by decide

-- sample 054; key=4|0,2,2,1|0; rel4=before; rank_sha256=0429fe7165ac541cf01b8b14b9654a8ce4113b9b95d1489808ec150c75ff052b
example :
    ((canonicalizeP (⟨0, [2, 2, 1]⟩ : Word Nat) 0).toList = [0, 0, 2, 1, 2]) ∧
      ((canonicalize (⟨0, [2, 2, 1, 0]⟩ : Word Nat)).toList = [0, 0, 2, 1, 2]) := by decide

-- sample 055; key=3|1,1,0,2,1|2; rel4=inside; rank_sha256=045b51bfe10d44dcab57c90e7dd88dcdaee0d665164c8680a32d7641d5b69efa
example :
    ((canonicalizeP (⟨1, [1, 0, 2, 1]⟩ : Word Nat) 2).toList = [1, 0, 1, 2, 2]) ∧
      ((canonicalize (⟨1, [1, 0, 2, 1, 2]⟩ : Word Nat)).toList = [1, 0, 1, 2, 2]) := by decide

-- sample 056; key=4|0,2,1,3|1; rel4=before; rank_sha256=04860654ca89e00deae8bc68a2d3b0ce2e19503e3b5ff7191f4490d63027eac7
example :
    ((canonicalizeP (⟨0, [2, 1, 3]⟩ : Word Nat) 1).toList = [0, 2, 1, 3, 1]) ∧
      ((canonicalize (⟨0, [2, 1, 3, 1]⟩ : Word Nat)).toList = [0, 2, 1, 3, 1]) := by decide

-- sample 057; key=4|1,0,0,3,3|1; rel4=before; rank_sha256=048899094a583829c6caee1ba00ae92289e400cea9bff82682134618a95db2c8
example :
    ((canonicalizeP (⟨1, [0, 0, 3, 3]⟩ : Word Nat) 1).toList = [1, 1, 0, 0, 3, 3]) ∧
      ((canonicalize (⟨1, [0, 0, 3, 3, 1]⟩ : Word Nat)).toList = [1, 1, 0, 0, 3, 3]) := by decide

-- sample 058; key=4|0,1,0,0,0|1; rel4=inside; rank_sha256=04d37d914b7b34e7cf88628f998e06a5c254dd376a7b24c5e5c506dae102d4e7
example :
    ((canonicalizeP (⟨0, [1, 0, 0, 0]⟩ : Word Nat) 1).toList = [0, 0, 1, 1]) ∧
      ((canonicalize (⟨0, [1, 0, 0, 0, 1]⟩ : Word Nat)).toList = [0, 0, 1, 1]) := by decide

-- sample 059; key=4|1,1,3,1,2|2; rel4=after; rank_sha256=04e441540f25ff29662aad5a495be222e77538477d4d14077f71346485f8c641
example :
    ((canonicalizeP (⟨1, [1, 3, 1, 2]⟩ : Word Nat) 2).toList = [1, 3, 1, 2, 2]) ∧
      ((canonicalize (⟨1, [1, 3, 1, 2, 2]⟩ : Word Nat)).toList = [1, 3, 1, 2, 2]) := by decide

-- sample 060; key=4|2,1,2,2,2|1; rel4=inside; rank_sha256=04ea1d85f7efaef22f5c2b88f1c770de6c73091879e8f199f2c7c655d2d97960
example :
    ((canonicalizeP (⟨2, [1, 2, 2, 2]⟩ : Word Nat) 1).toList = [2, 2, 1, 1]) ∧
      ((canonicalize (⟨2, [1, 2, 2, 2, 1]⟩ : Word Nat)).toList = [2, 2, 1, 1]) := by decide

-- sample 061; key=4|0,1,2,3,3|0; rel4=before; rank_sha256=04f731825923b36711d056b88a81efc6b3ba3b0fff7aef559432bc9bee99d85a
example :
    ((canonicalizeP (⟨0, [1, 2, 3, 3]⟩ : Word Nat) 0).toList = [0, 1, 2, 0, 3, 3]) ∧
      ((canonicalize (⟨0, [1, 2, 3, 3, 0]⟩ : Word Nat)).toList = [0, 1, 2, 0, 3, 3]) := by decide

-- sample 062; key=3|2,1,0,2,2|0; rel4=inside; rank_sha256=0503d9b8a8d23ef74b98134b25fcb42eae1f05ed05ff1f07c3851f25f58264a7
example :
    ((canonicalizeP (⟨2, [1, 0, 2, 2]⟩ : Word Nat) 0).toList = [2, 1, 2, 0, 0]) ∧
      ((canonicalize (⟨2, [1, 0, 2, 2, 0]⟩ : Word Nat)).toList = [2, 1, 2, 0, 0]) := by decide

-- sample 063; key=4|3,0,1,2,2|3; rel4=before; rank_sha256=052fc127e7621c1b7c29617bfe31b4c9a4f3cccb2d5e1c821b93108b2ccf40fd
example :
    ((canonicalizeP (⟨3, [0, 1, 2, 2]⟩ : Word Nat) 3).toList = [3, 0, 1, 3, 2, 2]) ∧
      ((canonicalize (⟨3, [0, 1, 2, 2, 3]⟩ : Word Nat)).toList = [3, 0, 1, 3, 2, 2]) := by decide

-- sample 064; key=3|0,0,1,0,2,1|2; rel4=inside; rank_sha256=0560905a6ac7922aabc9450c85d6fddbe8bd11150ba6e6738f3adf2f888f522a
example :
    ((canonicalizeP (⟨0, [0, 1, 0, 2, 1]⟩ : Word Nat) 2).toList = [0, 0, 1, 1, 2, 2]) ∧
      ((canonicalize (⟨0, [0, 1, 0, 2, 1, 2]⟩ : Word Nat)).toList = [0, 0, 1, 1, 2, 2]) := by decide

-- sample 065; key=4|2,1,3,1,0|2; rel4=before; rank_sha256=056114eb90665160c00b4c3f7fb368398d76be23744761166b48edef607519d0
example :
    ((canonicalizeP (⟨2, [1, 3, 1, 0]⟩ : Word Nat) 2).toList = [2, 2, 1, 3, 0, 1]) ∧
      ((canonicalize (⟨2, [1, 3, 1, 0, 2]⟩ : Word Nat)).toList = [2, 2, 1, 3, 0, 1]) := by decide

-- sample 066; key=4|2,2,0,0,1|1; rel4=after; rank_sha256=0587270ebeb1bfaf303639f52016c7c162c17b1334817484ad9290b86a77d93b
example :
    ((canonicalizeP (⟨2, [2, 0, 0, 1]⟩ : Word Nat) 1).toList = [2, 2, 0, 0, 1, 1]) ∧
      ((canonicalize (⟨2, [2, 0, 0, 1, 1]⟩ : Word Nat)).toList = [2, 2, 0, 0, 1, 1]) := by decide

-- sample 067; key=4|0,1,3,0|1; rel4=inside; rank_sha256=05a60e3fa334d9f63b13494baa29674e92980bd9c3210bda560c54f358a3c7bd
example :
    ((canonicalizeP (⟨0, [1, 3, 0]⟩ : Word Nat) 1).toList = [0, 0, 1, 3, 1]) ∧
      ((canonicalize (⟨0, [1, 3, 0, 1]⟩ : Word Nat)).toList = [0, 0, 1, 3, 1]) := by decide

-- sample 068; key=3|0,0,2,0,0,1|1; rel4=after; rank_sha256=05bda49de8e4890d00705a7ba1dc6d77d8e5e34d9c38c4f85c84840dabd479bb
example :
    ((canonicalizeP (⟨0, [0, 2, 0, 0, 1]⟩ : Word Nat) 1).toList = [0, 2, 0, 1, 1]) ∧
      ((canonicalize (⟨0, [0, 2, 0, 0, 1, 1]⟩ : Word Nat)).toList = [0, 2, 0, 1, 1]) := by decide

-- sample 069; key=4|1,1,2,0|2; rel4=after; rank_sha256=05c41c809b53559517d96d880b9c712e951ea10ae7af99f90aab75fb84373632
example :
    ((canonicalizeP (⟨1, [1, 2, 0]⟩ : Word Nat) 2).toList = [1, 1, 2, 0, 2]) ∧
      ((canonicalize (⟨1, [1, 2, 0, 2]⟩ : Word Nat)).toList = [1, 1, 2, 0, 2]) := by decide

-- sample 070; key=3|0,1,2,1,1,1|0; rel4=before; rank_sha256=05dbe9a8d25b196fbdcf2990a9d1d343f91775418fd339b10a82564f0c0a6ced
example :
    ((canonicalizeP (⟨0, [1, 2, 1, 1, 1]⟩ : Word Nat) 0).toList = [0, 0, 1, 2, 1]) ∧
      ((canonicalize (⟨0, [1, 2, 1, 1, 1, 0]⟩ : Word Nat)).toList = [0, 0, 1, 2, 1]) := by decide

-- sample 071; key=4|2,1,0,2|0; rel4=inside; rank_sha256=05f17899196ee3a6ff22bc60957eb68965e4e256c4372522ddbbee34143d50a6
example :
    ((canonicalizeP (⟨2, [1, 0, 2]⟩ : Word Nat) 0).toList = [2, 1, 2, 0, 0]) ∧
      ((canonicalize (⟨2, [1, 0, 2, 0]⟩ : Word Nat)).toList = [2, 1, 2, 0, 0]) := by decide

-- sample 072; key=3|1,0,0,2,0,1|2; rel4=inside; rank_sha256=060c27a9ef90edca98a9a67ef006d76ab7a9f17a16c1a1bdee7a311506c38c98
example :
    ((canonicalizeP (⟨1, [0, 0, 2, 0, 1]⟩ : Word Nat) 2).toList = [1, 1, 0, 0, 2, 2]) ∧
      ((canonicalize (⟨1, [0, 0, 2, 0, 1, 2]⟩ : Word Nat)).toList = [1, 1, 0, 0, 2, 2]) := by decide

-- sample 073; key=4|1,3,1,3,2|2; rel4=after; rank_sha256=062040c81b5803b71164b7a0bfc57692022ec8d585f59437d81b8b8d1f50d221
example :
    ((canonicalizeP (⟨1, [3, 1, 3, 2]⟩ : Word Nat) 2).toList = [1, 1, 3, 3, 2, 2]) ∧
      ((canonicalize (⟨1, [3, 1, 3, 2, 2]⟩ : Word Nat)).toList = [1, 1, 3, 3, 2, 2]) := by decide

-- sample 074; key=3|0,2,2,2|0; rel4=before; rank_sha256=06333a22827cc3014ff0fb003589a3a6c36ab23d45725dac92a463a9c24324b2
example :
    ((canonicalizeP (⟨0, [2, 2, 2]⟩ : Word Nat) 0).toList = [0, 0, 2, 2]) ∧
      ((canonicalize (⟨0, [2, 2, 2, 0]⟩ : Word Nat)).toList = [0, 0, 2, 2]) := by decide

-- sample 075; key=4|3,3,0|0; rel4=after; rank_sha256=063d8393c4f9e1690b8c8f250ff70dad2eebbe949dc991e75c0313f0d934908d
example :
    ((canonicalizeP (⟨3, [3, 0]⟩ : Word Nat) 0).toList = [3, 3, 0, 0]) ∧
      ((canonicalize (⟨3, [3, 0, 0]⟩ : Word Nat)).toList = [3, 3, 0, 0]) := by decide

-- sample 076; key=3|1,2,2,2,0|0; rel4=after; rank_sha256=063fe423e75bc37c0643a619701df26a15016260c6b4250808d793042c3680f9
example :
    ((canonicalizeP (⟨1, [2, 2, 2, 0]⟩ : Word Nat) 0).toList = [1, 2, 2, 0, 0]) ∧
      ((canonicalize (⟨1, [2, 2, 2, 0, 0]⟩ : Word Nat)).toList = [1, 2, 2, 0, 0]) := by decide

-- sample 077; key=3|2,2,1,0,1,2|0; rel4=inside; rank_sha256=067302deb6d8b62fc69a46595222d0d0ec1130a1a224a91f81635d078df3c840
example :
    ((canonicalizeP (⟨2, [2, 1, 0, 1, 2]⟩ : Word Nat) 0).toList = [2, 2, 1, 1, 0, 0]) ∧
      ((canonicalize (⟨2, [2, 1, 0, 1, 2, 0]⟩ : Word Nat)).toList = [2, 2, 1, 1, 0, 0]) := by decide

-- sample 078; key=4|2,2,0,1,0|1; rel4=inside; rank_sha256=0697e35192bfc9b811b39ff65f27dd5a2024b6b4394405bba917d58a98639d99
example :
    ((canonicalizeP (⟨2, [2, 0, 1, 0]⟩ : Word Nat) 1).toList = [2, 2, 0, 0, 1, 1]) ∧
      ((canonicalize (⟨2, [2, 0, 1, 0, 1]⟩ : Word Nat)).toList = [2, 2, 0, 0, 1, 1]) := by decide

-- sample 079; key=4|0,3,0,1,1|3; rel4=inside; rank_sha256=0699eeb8aa5b8880efc37b58973b8619dbad549a00f300eabe65fc4549443b11
example :
    ((canonicalizeP (⟨0, [3, 0, 1, 1]⟩ : Word Nat) 3).toList = [0, 0, 3, 3, 1, 1]) ∧
      ((canonicalize (⟨0, [3, 0, 1, 1, 3]⟩ : Word Nat)).toList = [0, 0, 3, 3, 1, 1]) := by decide

-- sample 080; key=4|2,1,2,0,2|1; rel4=inside; rank_sha256=06a3af2ca000768fca10fd8709575ccdc0b83c55bcc32c92393917916471119a
example :
    ((canonicalizeP (⟨2, [1, 2, 0, 2]⟩ : Word Nat) 1).toList = [2, 2, 1, 0, 1]) ∧
      ((canonicalize (⟨2, [1, 2, 0, 2, 1]⟩ : Word Nat)).toList = [2, 2, 1, 0, 1]) := by decide

-- sample 081; key=4|1,1,3,0,3|0; rel4=inside; rank_sha256=06a7897257f9060bba43aa2a3a1726eae2b26f3e4ef40304e68a594f066a1949
example :
    ((canonicalizeP (⟨1, [1, 3, 0, 3]⟩ : Word Nat) 0).toList = [1, 1, 3, 3, 0, 0]) ∧
      ((canonicalize (⟨1, [1, 3, 0, 3, 0]⟩ : Word Nat)).toList = [1, 1, 3, 3, 0, 0]) := by decide

-- sample 082; key=3|2,0,0,1,1|2; rel4=before; rank_sha256=06bf99f956a2d97efb4db1f9a15f1830e136df5da02f0e8d30e7177f2945fb00
example :
    ((canonicalizeP (⟨2, [0, 0, 1, 1]⟩ : Word Nat) 2).toList = [2, 2, 0, 0, 1, 1]) ∧
      ((canonicalize (⟨2, [0, 0, 1, 1, 2]⟩ : Word Nat)).toList = [2, 2, 0, 0, 1, 1]) := by decide

-- sample 083; key=4|1,0,2,2,3|1; rel4=before; rank_sha256=06c1a7c01ca898d0a6323e5d6239b26c242b737f779186c587e56022a0cb6e48
example :
    ((canonicalizeP (⟨1, [0, 2, 2, 3]⟩ : Word Nat) 1).toList = [1, 0, 1, 2, 3, 2]) ∧
      ((canonicalize (⟨1, [0, 2, 2, 3, 1]⟩ : Word Nat)).toList = [1, 0, 1, 2, 3, 2]) := by decide

-- sample 084; key=4|3,3,1,2,1|2; rel4=inside; rank_sha256=06cdc28767fb4f768145e388eb7ea6cddc05b169882dc7dcfc633a1acb3bf19d
example :
    ((canonicalizeP (⟨3, [3, 1, 2, 1]⟩ : Word Nat) 2).toList = [3, 3, 1, 1, 2, 2]) ∧
      ((canonicalize (⟨3, [3, 1, 2, 1, 2]⟩ : Word Nat)).toList = [3, 3, 1, 1, 2, 2]) := by decide

-- sample 085; key=4|1,3,2,0|3; rel4=before; rank_sha256=06f94e58464bd117e7a04f973c39cf8fe1dd67d8655948ced8a7e63eccb6dbda
example :
    ((canonicalizeP (⟨1, [3, 2, 0]⟩ : Word Nat) 3).toList = [1, 3, 2, 0, 3]) ∧
      ((canonicalize (⟨1, [3, 2, 0, 3]⟩ : Word Nat)).toList = [1, 3, 2, 0, 3]) := by decide

-- sample 086; key=4|0,2,0,1,3|1; rel4=after; rank_sha256=0702b3f976c98305c1b6fec9d5b5c312ad6f9d4662b415c75cb238726781e52a
example :
    ((canonicalizeP (⟨0, [2, 0, 1, 3]⟩ : Word Nat) 1).toList = [0, 2, 0, 1, 3, 1]) ∧
      ((canonicalize (⟨0, [2, 0, 1, 3, 1]⟩ : Word Nat)).toList = [0, 2, 0, 1, 3, 1]) := by decide

-- sample 087; key=4|0,1,1,0,3|3; rel4=after; rank_sha256=0722fdefb5e635a3a6d7239bb0c1bd4855981f3845b2fed69ad0a8b0866db3ec
example :
    ((canonicalizeP (⟨0, [1, 1, 0, 3]⟩ : Word Nat) 3).toList = [0, 0, 1, 1, 3, 3]) ∧
      ((canonicalize (⟨0, [1, 1, 0, 3, 3]⟩ : Word Nat)).toList = [0, 0, 1, 1, 3, 3]) := by decide

-- sample 088; key=3|2,2,2,2,0,1|1; rel4=after; rank_sha256=074ef8b77eb23f6e525c1438b87d8d75c03aede686bb63e4a17c74fe21656d11
example :
    ((canonicalizeP (⟨2, [2, 2, 2, 0, 1]⟩ : Word Nat) 1).toList = [2, 2, 0, 1, 1]) ∧
      ((canonicalize (⟨2, [2, 2, 2, 0, 1, 1]⟩ : Word Nat)).toList = [2, 2, 0, 1, 1]) := by decide

-- sample 089; key=4|1,0,1,3,0|3; rel4=inside; rank_sha256=0765e873790d07b303645ed3dee16eae30db4e3ccf565ee94838acbcc6d5ba44
example :
    ((canonicalizeP (⟨1, [0, 1, 3, 0]⟩ : Word Nat) 3).toList = [1, 1, 0, 0, 3, 3]) ∧
      ((canonicalize (⟨1, [0, 1, 3, 0, 3]⟩ : Word Nat)).toList = [1, 1, 0, 0, 3, 3]) := by decide

-- sample 090; key=4|3,1,0,2,2|1; rel4=before; rank_sha256=0769c94a7b95d7d21059f9ecb28a438e854fcc1b200ef1c5c93288d3ab5ac8fe
example :
    ((canonicalizeP (⟨3, [1, 0, 2, 2]⟩ : Word Nat) 1).toList = [3, 1, 0, 1, 2, 2]) ∧
      ((canonicalize (⟨3, [1, 0, 2, 2, 1]⟩ : Word Nat)).toList = [3, 1, 0, 1, 2, 2]) := by decide

-- sample 091; key=4|2,2,1,3,2|1; rel4=inside; rank_sha256=07736b3f13bf5f3fb378cb081f9614ba8e6cb55e1456cab9bf0d49a2b9ffb4f4
example :
    ((canonicalizeP (⟨2, [2, 1, 3, 2]⟩ : Word Nat) 1).toList = [2, 2, 1, 3, 1]) ∧
      ((canonicalize (⟨2, [2, 1, 3, 2, 1]⟩ : Word Nat)).toList = [2, 2, 1, 3, 1]) := by decide

-- sample 092; key=4|0,0,3,1,3|1; rel4=inside; rank_sha256=07864f580f968343270d689a7699bfaac8d294384ae82bd38e9de01f93cb22b3
example :
    ((canonicalizeP (⟨0, [0, 3, 1, 3]⟩ : Word Nat) 1).toList = [0, 0, 3, 3, 1, 1]) ∧
      ((canonicalize (⟨0, [0, 3, 1, 3, 1]⟩ : Word Nat)).toList = [0, 0, 3, 3, 1, 1]) := by decide

-- sample 093; key=3|0,1,0,0|1; rel4=inside; rank_sha256=0791703a16d1afb0977ed54307b7bacfb6ae9af1f82a84a0a99e9b4582f45b13
example :
    ((canonicalizeP (⟨0, [1, 0, 0]⟩ : Word Nat) 1).toList = [0, 0, 1, 1]) ∧
      ((canonicalize (⟨0, [1, 0, 0, 1]⟩ : Word Nat)).toList = [0, 0, 1, 1]) := by decide

-- sample 094; key=4|1,2,1,3,2|3; rel4=inside; rank_sha256=07a145258931a78312381c81f47b3967756d98c1cf3d4f02fed108498c1f6cf3
example :
    ((canonicalizeP (⟨1, [2, 1, 3, 2]⟩ : Word Nat) 3).toList = [1, 1, 2, 2, 3, 3]) ∧
      ((canonicalize (⟨1, [2, 1, 3, 2, 3]⟩ : Word Nat)).toList = [1, 1, 2, 2, 3, 3]) := by decide

-- sample 095; key=4|2,0,3,1,0|3; rel4=inside; rank_sha256=07ad816a6c9880c52aec1df0ac660a618ef1cdaa7f5727a7cb7fb128ead8d420
example :
    ((canonicalizeP (⟨2, [0, 3, 1, 0]⟩ : Word Nat) 3).toList = [2, 0, 0, 3, 1, 3]) ∧
      ((canonicalize (⟨2, [0, 3, 1, 0, 3]⟩ : Word Nat)).toList = [2, 0, 0, 3, 1, 3]) := by decide

-- sample 096; key=4|0,1,3,2,0|3; rel4=inside; rank_sha256=07c18e03447abf19fb9a8da9e39782deca5ad058e554bab025e5293c535e29d2
example :
    ((canonicalizeP (⟨0, [1, 3, 2, 0]⟩ : Word Nat) 3).toList = [0, 1, 0, 3, 2, 3]) ∧
      ((canonicalize (⟨0, [1, 3, 2, 0, 3]⟩ : Word Nat)).toList = [0, 1, 0, 3, 2, 3]) := by decide

-- sample 097; key=4|2,0,3,1,0|1; rel4=inside; rank_sha256=07d1736002d9108398be5f4ced2e610c5e15eccc7a90ff7b9def7a7016a1f6d0
example :
    ((canonicalizeP (⟨2, [0, 3, 1, 0]⟩ : Word Nat) 1).toList = [2, 0, 3, 0, 1, 1]) ∧
      ((canonicalize (⟨2, [0, 3, 1, 0, 1]⟩ : Word Nat)).toList = [2, 0, 3, 0, 1, 1]) := by decide

-- sample 098; key=3|2,1,1,1,0,2|0; rel4=inside; rank_sha256=07d4f2ed1d5bb8838d047d86b07cf45c2244ab283e436278e127ea7aef3bb48f
example :
    ((canonicalizeP (⟨2, [1, 1, 1, 0, 2]⟩ : Word Nat) 0).toList = [2, 2, 1, 1, 0, 0]) ∧
      ((canonicalize (⟨2, [1, 1, 1, 0, 2, 0]⟩ : Word Nat)).toList = [2, 2, 1, 1, 0, 0]) := by decide

-- sample 099; key=4|1,0,3,3,0|1; rel4=before; rank_sha256=07d5127b6495749ce698827117a2ab64350d6456a2065862d6fcc0f6dff85abb
example :
    ((canonicalizeP (⟨1, [0, 3, 3, 0]⟩ : Word Nat) 1).toList = [1, 1, 0, 0, 3, 3]) ∧
      ((canonicalize (⟨1, [0, 3, 3, 0, 1]⟩ : Word Nat)).toList = [1, 1, 0, 0, 3, 3]) := by decide

-- sample 100; key=4|3,3,1,3,3|1; rel4=inside; rank_sha256=07f508f57caac6ee2912a1b2e101fd983655c06bfc9483e4f4214144682db736
example :
    ((canonicalizeP (⟨3, [3, 1, 3, 3]⟩ : Word Nat) 1).toList = [3, 3, 1, 1]) ∧
      ((canonicalize (⟨3, [3, 1, 3, 3, 1]⟩ : Word Nat)).toList = [3, 3, 1, 1]) := by decide

-- sample 101; key=4|1,1,3,1,1|3; rel4=inside; rank_sha256=0803627d4af41b7996158a2e7e1345ab2193ff63cd721cc3b43b0878e5a6db0d
example :
    ((canonicalizeP (⟨1, [1, 3, 1, 1]⟩ : Word Nat) 3).toList = [1, 1, 3, 3]) ∧
      ((canonicalize (⟨1, [1, 3, 1, 1, 3]⟩ : Word Nat)).toList = [1, 1, 3, 3]) := by decide

-- sample 102; key=4|0,1,3,1,2|0; rel4=before; rank_sha256=0827fd66a005a264106aaeaa329bbcf6fd43d3a474bccc36744b3ecf8502e2f8
example :
    ((canonicalizeP (⟨0, [1, 3, 1, 2]⟩ : Word Nat) 0).toList = [0, 0, 1, 3, 2, 1]) ∧
      ((canonicalize (⟨0, [1, 3, 1, 2, 0]⟩ : Word Nat)).toList = [0, 0, 1, 3, 2, 1]) := by decide

-- sample 103; key=3|2,0,1|1; rel4=before; rank_sha256=083e4d5209182f4f4f8f609bb2440df76d59c7d6796bab22e6dda6bb62033e72
example :
    ((canonicalizeP (⟨2, [0, 1]⟩ : Word Nat) 1).toList = [2, 0, 1, 1]) ∧
      ((canonicalize (⟨2, [0, 1, 1]⟩ : Word Nat)).toList = [2, 0, 1, 1]) := by decide

-- sample 104; key=4|1,2,1,2,0|0; rel4=after; rank_sha256=084cc41ee2679ef6b5b9f49d7a96d591239d8f0f5fa226d2e2b0dbaad44845c4
example :
    ((canonicalizeP (⟨1, [2, 1, 2, 0]⟩ : Word Nat) 0).toList = [1, 1, 2, 2, 0, 0]) ∧
      ((canonicalize (⟨1, [2, 1, 2, 0, 0]⟩ : Word Nat)).toList = [1, 1, 2, 2, 0, 0]) := by decide

-- sample 105; key=3|1,0,2,1,2,2|0; rel4=inside; rank_sha256=084ea9c6d8e2a7a83c0811459ec4d8fd4784884a34fa04682e9042f45ad9fac6
example :
    ((canonicalizeP (⟨1, [0, 2, 1, 2, 2]⟩ : Word Nat) 0).toList = [1, 1, 0, 0, 2, 2]) ∧
      ((canonicalize (⟨1, [0, 2, 1, 2, 2, 0]⟩ : Word Nat)).toList = [1, 1, 0, 0, 2, 2]) := by decide

-- sample 106; key=3|0,1,1,2,2,2|0; rel4=before; rank_sha256=0850b8fd2256c4d0450f0a45ea23359c53252db66cde1b1058d79c073297db66
example :
    ((canonicalizeP (⟨0, [1, 1, 2, 2, 2]⟩ : Word Nat) 0).toList = [0, 0, 1, 1, 2, 2]) ∧
      ((canonicalize (⟨0, [1, 1, 2, 2, 2, 0]⟩ : Word Nat)).toList = [0, 0, 1, 1, 2, 2]) := by decide

-- sample 107; key=3|0,2|2; rel4=before; rank_sha256=0874964085b9dfaf5a24b3a32be61a269851e3fb158672eb34d0ea05a8ea566b
example :
    ((canonicalizeP (⟨0, [2]⟩ : Word Nat) 2).toList = [0, 2, 2]) ∧
      ((canonicalize (⟨0, [2, 2]⟩ : Word Nat)).toList = [0, 2, 2]) := by decide

-- sample 108; key=4|2,0,1,3|3; rel4=before; rank_sha256=087beb132d9455f30fb1fdf7e385011c6e4d441070bc91cf93f5a5cb2c4013fb
example :
    ((canonicalizeP (⟨2, [0, 1, 3]⟩ : Word Nat) 3).toList = [2, 0, 1, 3, 3]) ∧
      ((canonicalize (⟨2, [0, 1, 3, 3]⟩ : Word Nat)).toList = [2, 0, 1, 3, 3]) := by decide

-- sample 109; key=3|0,2,1,0,0,0|1; rel4=inside; rank_sha256=088458fb509aa62c2b77d6b9a8d4bfab903e52cb0613c8f8ef17bd76a5e33238
example :
    ((canonicalizeP (⟨0, [2, 1, 0, 0, 0]⟩ : Word Nat) 1).toList = [0, 2, 0, 1, 1]) ∧
      ((canonicalize (⟨0, [2, 1, 0, 0, 0, 1]⟩ : Word Nat)).toList = [0, 2, 0, 1, 1]) := by decide

-- sample 110; key=3|2,1,1,0,1|2; rel4=before; rank_sha256=08859a69ba2f200109781c3ef3185c9350dec4779452a7656f227c552e675b46
example :
    ((canonicalizeP (⟨2, [1, 1, 0, 1]⟩ : Word Nat) 2).toList = [2, 2, 1, 0, 1]) ∧
      ((canonicalize (⟨2, [1, 1, 0, 1, 2]⟩ : Word Nat)).toList = [2, 2, 1, 0, 1]) := by decide

-- sample 111; key=4|2,2,3,1,0|1; rel4=after; rank_sha256=0899d6044d1c930126eba6c007e3417aa95045c0c23370527bf160804aa0cfc2
example :
    ((canonicalizeP (⟨2, [2, 3, 1, 0]⟩ : Word Nat) 1).toList = [2, 2, 3, 1, 0, 1]) ∧
      ((canonicalize (⟨2, [2, 3, 1, 0, 1]⟩ : Word Nat)).toList = [2, 2, 3, 1, 0, 1]) := by decide

-- sample 112; key=4|3,2,3,1,0|2; rel4=inside; rank_sha256=08ac706782bd5c4b47fdf3dcf67b7f7fb3096ad82c9fd9e0c2930141d90ce76c
example :
    ((canonicalizeP (⟨3, [2, 3, 1, 0]⟩ : Word Nat) 2).toList = [3, 3, 2, 1, 0, 2]) ∧
      ((canonicalize (⟨3, [2, 3, 1, 0, 2]⟩ : Word Nat)).toList = [3, 3, 2, 1, 0, 2]) := by decide

-- sample 113; key=3|1,2,1,0,2,2|0; rel4=inside; rank_sha256=08c801216972d172e82f45379d4fdfd79b60bf2aa1ac7470b38276d3ce99df40
example :
    ((canonicalizeP (⟨1, [2, 1, 0, 2, 2]⟩ : Word Nat) 0).toList = [1, 1, 2, 2, 0, 0]) ∧
      ((canonicalize (⟨1, [2, 1, 0, 2, 2, 0]⟩ : Word Nat)).toList = [1, 1, 2, 2, 0, 0]) := by decide

-- sample 114; key=4|0,2,1,3,2|0; rel4=before; rank_sha256=08e2e2d363cc60e470b3138dd526df403bae53708156d8b4b276d65402e1e920
example :
    ((canonicalizeP (⟨0, [2, 1, 3, 2]⟩ : Word Nat) 0).toList = [0, 0, 2, 1, 3, 2]) ∧
      ((canonicalize (⟨0, [2, 1, 3, 2, 0]⟩ : Word Nat)).toList = [0, 0, 2, 1, 3, 2]) := by decide

-- sample 115; key=4|0,1,1,1,2|0; rel4=before; rank_sha256=08efa589aa6057189a1139282b3ae39d995e1b4a7698ed13dec90e7e8d0b4c8d
example :
    ((canonicalizeP (⟨0, [1, 1, 1, 2]⟩ : Word Nat) 0).toList = [0, 0, 1, 2, 1]) ∧
      ((canonicalize (⟨0, [1, 1, 1, 2, 0]⟩ : Word Nat)).toList = [0, 0, 1, 2, 1]) := by decide

-- sample 116; key=4|0,1,0,3,0|1; rel4=inside; rank_sha256=096218a5ca050a78253706040842839576f99904209e952d5bae52755789072a
example :
    ((canonicalizeP (⟨0, [1, 0, 3, 0]⟩ : Word Nat) 1).toList = [0, 0, 1, 3, 1]) ∧
      ((canonicalize (⟨0, [1, 0, 3, 0, 1]⟩ : Word Nat)).toList = [0, 0, 1, 3, 1]) := by decide

-- sample 117; key=4|2,3,0,1,0|2; rel4=before; rank_sha256=09b22edcb556832c9be66c260d4c7ee77dbe681fb68c91899f18392351891e83
example :
    ((canonicalizeP (⟨2, [3, 0, 1, 0]⟩ : Word Nat) 2).toList = [2, 3, 2, 0, 1, 0]) ∧
      ((canonicalize (⟨2, [3, 0, 1, 0, 2]⟩ : Word Nat)).toList = [2, 3, 2, 0, 1, 0]) := by decide

-- sample 118; key=4|3,3,0,3,1|0; rel4=inside; rank_sha256=09e5c02d2cf78deda61d243fd54035d83b89768e301136047ce27efc90c7632f
example :
    ((canonicalizeP (⟨3, [3, 0, 3, 1]⟩ : Word Nat) 0).toList = [3, 3, 0, 1, 0]) ∧
      ((canonicalize (⟨3, [3, 0, 3, 1, 0]⟩ : Word Nat)).toList = [3, 3, 0, 1, 0]) := by decide

-- sample 119; key=4|3,0,2,3,2|0; rel4=inside; rank_sha256=09e9646325927ba364e8397785232814344b5f72ea9e719f3f1af512e04a346c
example :
    ((canonicalizeP (⟨3, [0, 2, 3, 2]⟩ : Word Nat) 0).toList = [3, 3, 0, 0, 2, 2]) ∧
      ((canonicalize (⟨3, [0, 2, 3, 2, 0]⟩ : Word Nat)).toList = [3, 3, 0, 0, 2, 2]) := by decide

-- sample 120; key=4|1,2,3,2,1|3; rel4=inside; rank_sha256=0a024ba3f9280b21d22394067cc32fc7169d9de55eaa7afeffd5e9156337b201
example :
    ((canonicalizeP (⟨1, [2, 3, 2, 1]⟩ : Word Nat) 3).toList = [1, 1, 2, 2, 3, 3]) ∧
      ((canonicalize (⟨1, [2, 3, 2, 1, 3]⟩ : Word Nat)).toList = [1, 1, 2, 2, 3, 3]) := by decide

-- sample 121; key=4|0,2,1,0,3|2; rel4=inside; rank_sha256=0a04d206c50a5f15c63f081cae66f0a58e0c1cc377a4d794228414ae40d3f7b6
example :
    ((canonicalizeP (⟨0, [2, 1, 0, 3]⟩ : Word Nat) 2).toList = [0, 0, 2, 1, 3, 2]) ∧
      ((canonicalize (⟨0, [2, 1, 0, 3, 2]⟩ : Word Nat)).toList = [0, 0, 2, 1, 3, 2]) := by decide

-- sample 122; key=4|1,3,2,1,2|3; rel4=inside; rank_sha256=0a063716cf06c11f83bfcbfdbc731e1c75b8948dc52bb5b7fdbd7645b8e2ed33
example :
    ((canonicalizeP (⟨1, [3, 2, 1, 2]⟩ : Word Nat) 3).toList = [1, 1, 3, 3, 2, 2]) ∧
      ((canonicalize (⟨1, [3, 2, 1, 2, 3]⟩ : Word Nat)).toList = [1, 1, 3, 3, 2, 2]) := by decide

-- sample 123; key=2|1,1,0,1,1,1|0; rel4=inside; rank_sha256=0a4e43f51a63e22c2e41aa38d48ff337f7bfaa95b26f6a109dda0023a7ab7a2e
example :
    ((canonicalizeP (⟨1, [1, 0, 1, 1, 1]⟩ : Word Nat) 0).toList = [1, 1, 0, 0]) ∧
      ((canonicalize (⟨1, [1, 0, 1, 1, 1, 0]⟩ : Word Nat)).toList = [1, 1, 0, 0]) := by decide

-- sample 124; key=4|1,3,2,0,2|1; rel4=before; rank_sha256=0a5bafb53936361bb9a3458803d603ab262fefc3bd760905a3cc77f8a776689a
example :
    ((canonicalizeP (⟨1, [3, 2, 0, 2]⟩ : Word Nat) 1).toList = [1, 3, 1, 2, 0, 2]) ∧
      ((canonicalize (⟨1, [3, 2, 0, 2, 1]⟩ : Word Nat)).toList = [1, 3, 1, 2, 0, 2]) := by decide

-- sample 125; key=4|0,2,0,0,0|2; rel4=inside; rank_sha256=0a6fba3c5d3cf30d5008db21e467ac593db1d49bf88d99402df21cc20d83ee3b
example :
    ((canonicalizeP (⟨0, [2, 0, 0, 0]⟩ : Word Nat) 2).toList = [0, 0, 2, 2]) ∧
      ((canonicalize (⟨0, [2, 0, 0, 0, 2]⟩ : Word Nat)).toList = [0, 0, 2, 2]) := by decide

-- sample 126; key=4|3,2,1,2,1|3; rel4=before; rank_sha256=0a7ab72cf52e686f2c821e101c0f48037c4d5b3ce70d9cabea66508c3774b163
example :
    ((canonicalizeP (⟨3, [2, 1, 2, 1]⟩ : Word Nat) 3).toList = [3, 3, 2, 2, 1, 1]) ∧
      ((canonicalize (⟨3, [2, 1, 2, 1, 3]⟩ : Word Nat)).toList = [3, 3, 2, 2, 1, 1]) := by decide

-- sample 127; key=4|2,0,1,3,1|0; rel4=before; rank_sha256=0a84873870558857962ad83d2e530738852ec040e16d3a53c6f3406708487bd1
example :
    ((canonicalizeP (⟨2, [0, 1, 3, 1]⟩ : Word Nat) 0).toList = [2, 0, 0, 1, 3, 1]) ∧
      ((canonicalize (⟨2, [0, 1, 3, 1, 0]⟩ : Word Nat)).toList = [2, 0, 0, 1, 3, 1]) := by decide

-- sample 128; key=4|1,2,2,2,3|1; rel4=before; rank_sha256=0a9e9f9031de5acc3e33fe60a8ff5386eee26bc64ff6fd29947af2c8e1976ec5
example :
    ((canonicalizeP (⟨1, [2, 2, 2, 3]⟩ : Word Nat) 1).toList = [1, 1, 2, 3, 2]) ∧
      ((canonicalize (⟨1, [2, 2, 2, 3, 1]⟩ : Word Nat)).toList = [1, 1, 2, 3, 2]) := by decide

-- sample 129; key=3|1,1,2,1,1,0|2; rel4=inside; rank_sha256=0ab9b0e73611b9200f5860a6db30196030177aeea4c5e29aa4f03af65f781fbe
example :
    ((canonicalizeP (⟨1, [1, 2, 1, 1, 0]⟩ : Word Nat) 2).toList = [1, 1, 2, 0, 2]) ∧
      ((canonicalize (⟨1, [1, 2, 1, 1, 0, 2]⟩ : Word Nat)).toList = [1, 1, 2, 0, 2]) := by decide

-- sample 130; key=4|2,0,1,2|0; rel4=inside; rank_sha256=0ac8bccd7756246b204b313dbadcfc02bdccce4e4ca3c5d609ae3d67bec5c935
example :
    ((canonicalizeP (⟨2, [0, 1, 2]⟩ : Word Nat) 0).toList = [2, 2, 0, 1, 0]) ∧
      ((canonicalize (⟨2, [0, 1, 2, 0]⟩ : Word Nat)).toList = [2, 2, 0, 1, 0]) := by decide

-- sample 131; key=3|2,1,0,2,1|0; rel4=inside; rank_sha256=0acb222d74089234655bb2add4c98b2de8fb85fc2a6b52707328c541f5eeabe4
example :
    ((canonicalizeP (⟨2, [1, 0, 2, 1]⟩ : Word Nat) 0).toList = [2, 2, 1, 1, 0, 0]) ∧
      ((canonicalize (⟨2, [1, 0, 2, 1, 0]⟩ : Word Nat)).toList = [2, 2, 1, 1, 0, 0]) := by decide

-- sample 132; key=3|1,1,1,1,0,2|2; rel4=after; rank_sha256=0ae1dda58ae3495bc0679826d473942611960a2706b160d77cd7e334009692db
example :
    ((canonicalizeP (⟨1, [1, 1, 1, 0, 2]⟩ : Word Nat) 2).toList = [1, 1, 0, 2, 2]) ∧
      ((canonicalize (⟨1, [1, 1, 1, 0, 2, 2]⟩ : Word Nat)).toList = [1, 1, 0, 2, 2]) := by decide

-- sample 133; key=4|0,2,3|3; rel4=before; rank_sha256=0ae9b8993fc6820a0ad0173499dcbb88722a84b756ca2a036c3690339c8b62de
example :
    ((canonicalizeP (⟨0, [2, 3]⟩ : Word Nat) 3).toList = [0, 2, 3, 3]) ∧
      ((canonicalize (⟨0, [2, 3, 3]⟩ : Word Nat)).toList = [0, 2, 3, 3]) := by decide

-- sample 134; key=4|0,2,3,1,1|3; rel4=before; rank_sha256=0b0f14857df48c5186f6350bcc795f059fb9602164cd95b136471ac54e8fdd2e
example :
    ((canonicalizeP (⟨0, [2, 3, 1, 1]⟩ : Word Nat) 3).toList = [0, 2, 3, 3, 1, 1]) ∧
      ((canonicalize (⟨0, [2, 3, 1, 1, 3]⟩ : Word Nat)).toList = [0, 2, 3, 3, 1, 1]) := by decide

-- sample 135; key=4|1,2,0,0,2|1; rel4=before; rank_sha256=0b2beb243291aab7dff06cb7a81c09c5d0a5f1c2a9a3c923cff7762165519e25
example :
    ((canonicalizeP (⟨1, [2, 0, 0, 2]⟩ : Word Nat) 1).toList = [1, 1, 2, 2, 0, 0]) ∧
      ((canonicalize (⟨1, [2, 0, 0, 2, 1]⟩ : Word Nat)).toList = [1, 1, 2, 2, 0, 0]) := by decide

-- sample 136; key=4|1,3,1,2,2|3; rel4=inside; rank_sha256=0b2e0fb501b97cc7f6cfcb2a809d28f97e1d1ea6e93757f03f337475163c16cb
example :
    ((canonicalizeP (⟨1, [3, 1, 2, 2]⟩ : Word Nat) 3).toList = [1, 1, 3, 3, 2, 2]) ∧
      ((canonicalize (⟨1, [3, 1, 2, 2, 3]⟩ : Word Nat)).toList = [1, 1, 3, 3, 2, 2]) := by decide

-- sample 137; key=4|2,2,2,3,1|3; rel4=after; rank_sha256=0b3963849439daf22aca4eef586432372bf0a71b0f553e9bc6476c277fec2b6e
example :
    ((canonicalizeP (⟨2, [2, 2, 3, 1]⟩ : Word Nat) 3).toList = [2, 2, 3, 1, 3]) ∧
      ((canonicalize (⟨2, [2, 2, 3, 1, 3]⟩ : Word Nat)).toList = [2, 2, 3, 1, 3]) := by decide

-- sample 138; key=4|0,1,3,3,3|0; rel4=before; rank_sha256=0b5bb18ba0962a72e4b7d2f9b1532fef4bc27dfcc809840f6dbee6c97edfb66e
example :
    ((canonicalizeP (⟨0, [1, 3, 3, 3]⟩ : Word Nat) 0).toList = [0, 1, 0, 3, 3]) ∧
      ((canonicalize (⟨0, [1, 3, 3, 3, 0]⟩ : Word Nat)).toList = [0, 1, 0, 3, 3]) := by decide

-- sample 139; key=3|0,0,1,0,2,2|1; rel4=inside; rank_sha256=0b91315246abe4a1274449764ee1e99afc348164d97bf5910521c7d33043e854
example :
    ((canonicalizeP (⟨0, [0, 1, 0, 2, 2]⟩ : Word Nat) 1).toList = [0, 0, 1, 1, 2, 2]) ∧
      ((canonicalize (⟨0, [0, 1, 0, 2, 2, 1]⟩ : Word Nat)).toList = [0, 0, 1, 1, 2, 2]) := by decide

-- sample 140; key=3|2,1,1,1,1,0|0; rel4=after; rank_sha256=0b95303ce33ff9d12ebc42b683bde3b3323717f016a23167d7b6d0fd92622969
example :
    ((canonicalizeP (⟨2, [1, 1, 1, 1, 0]⟩ : Word Nat) 0).toList = [2, 1, 1, 0, 0]) ∧
      ((canonicalize (⟨2, [1, 1, 1, 1, 0, 0]⟩ : Word Nat)).toList = [2, 1, 1, 0, 0]) := by decide

-- sample 141; key=4|2,2,0,1,3|3; rel4=after; rank_sha256=0bea1c684e537cc65120d053edc55ad5e9c2c9a920e5dd8e04b481cb8b4813b3
example :
    ((canonicalizeP (⟨2, [2, 0, 1, 3]⟩ : Word Nat) 3).toList = [2, 2, 0, 1, 3, 3]) ∧
      ((canonicalize (⟨2, [2, 0, 1, 3, 3]⟩ : Word Nat)).toList = [2, 2, 0, 1, 3, 3]) := by decide

-- sample 142; key=3|1,2,1,1,0|0; rel4=after; rank_sha256=0c1a7138ef334e502c8629914fbeb872a66e1d36e8ba1eb586a42aa3fea945cd
example :
    ((canonicalizeP (⟨1, [2, 1, 1, 0]⟩ : Word Nat) 0).toList = [1, 2, 1, 0, 0]) ∧
      ((canonicalize (⟨1, [2, 1, 1, 0, 0]⟩ : Word Nat)).toList = [1, 2, 1, 0, 0]) := by decide

-- sample 143; key=4|3,0,2,1,1|2; rel4=before; rank_sha256=0c2930ba3b8e33fa6532fb8b29b6041e0624e89f8b927b28724bd97a3295dadd
example :
    ((canonicalizeP (⟨3, [0, 2, 1, 1]⟩ : Word Nat) 2).toList = [3, 0, 2, 2, 1, 1]) ∧
      ((canonicalize (⟨3, [0, 2, 1, 1, 2]⟩ : Word Nat)).toList = [3, 0, 2, 2, 1, 1]) := by decide

-- sample 144; key=4|3,3,1,0,0|1; rel4=gap; rank_sha256=0c2f490e075a2be09350c5b511275269549c780b1f377af4fefc1f184715172b
example :
    ((canonicalizeP (⟨3, [3, 1, 0, 0]⟩ : Word Nat) 1).toList = [3, 3, 1, 1, 0, 0]) ∧
      ((canonicalize (⟨3, [3, 1, 0, 0, 1]⟩ : Word Nat)).toList = [3, 3, 1, 1, 0, 0]) := by decide

-- sample 145; key=4|3,3,1,3,0|1; rel4=inside; rank_sha256=0c47fcf6d6f583fccadd80fb8b23b52e8e0498e23346610453b9e638e2a67d98
example :
    ((canonicalizeP (⟨3, [3, 1, 3, 0]⟩ : Word Nat) 1).toList = [3, 3, 1, 0, 1]) ∧
      ((canonicalize (⟨3, [3, 1, 3, 0, 1]⟩ : Word Nat)).toList = [3, 3, 1, 0, 1]) := by decide

-- sample 146; key=3|0,0,1,0,2,0|2; rel4=inside; rank_sha256=0c4d0765a0f4042a8fda3f368f2c2662c9d3ae04d10fb6f43fd0c7ddb06d3ab7
example :
    ((canonicalizeP (⟨0, [0, 1, 0, 2, 0]⟩ : Word Nat) 2).toList = [0, 1, 0, 2, 2]) ∧
      ((canonicalize (⟨0, [0, 1, 0, 2, 0, 2]⟩ : Word Nat)).toList = [0, 1, 0, 2, 2]) := by decide

-- sample 147; key=4|3,0,0,2,0|3; rel4=before; rank_sha256=0c729544e000270b7a62f454d228530b82e3499ddd33809e7601030e8699c9a6
example :
    ((canonicalizeP (⟨3, [0, 0, 2, 0]⟩ : Word Nat) 3).toList = [3, 3, 0, 2, 0]) ∧
      ((canonicalize (⟨3, [0, 0, 2, 0, 3]⟩ : Word Nat)).toList = [3, 3, 0, 2, 0]) := by decide

-- sample 148; key=4|0,3,1,2,2|3; rel4=before; rank_sha256=0c7852f721b034afb45ad68059c23b51ede2fc70d4e434f5d65560c5414bbead
example :
    ((canonicalizeP (⟨0, [3, 1, 2, 2]⟩ : Word Nat) 3).toList = [0, 3, 1, 3, 2, 2]) ∧
      ((canonicalize (⟨0, [3, 1, 2, 2, 3]⟩ : Word Nat)).toList = [0, 3, 1, 3, 2, 2]) := by decide

-- sample 149; key=3|2,2,1,0,2|1; rel4=inside; rank_sha256=0c91f42797794fda13f09a52c60f77e8db3b55ad5bed46faf895a24aebbdfe80
example :
    ((canonicalizeP (⟨2, [2, 1, 0, 2]⟩ : Word Nat) 1).toList = [2, 2, 1, 0, 1]) ∧
      ((canonicalize (⟨2, [2, 1, 0, 2, 1]⟩ : Word Nat)).toList = [2, 2, 1, 0, 1]) := by decide

-- sample 150; key=4|3,0,1,1,2|2; rel4=after; rank_sha256=0c93fdb69ebd622e7abb810cc8d2fe038060f533f8961fc43b8a1ca79bac509d
example :
    ((canonicalizeP (⟨3, [0, 1, 1, 2]⟩ : Word Nat) 2).toList = [3, 0, 1, 1, 2, 2]) ∧
      ((canonicalize (⟨3, [0, 1, 1, 2, 2]⟩ : Word Nat)).toList = [3, 0, 1, 1, 2, 2]) := by decide

-- sample 151; key=4|1,0,0,3,1|3; rel4=inside; rank_sha256=0ca686a1405e02efaf2bcdaa351ae8ee72e26edb219fdf52b68dfb69a40d0e21
example :
    ((canonicalizeP (⟨1, [0, 0, 3, 1]⟩ : Word Nat) 3).toList = [1, 1, 0, 0, 3, 3]) ∧
      ((canonicalize (⟨1, [0, 0, 3, 1, 3]⟩ : Word Nat)).toList = [1, 1, 0, 0, 3, 3]) := by decide

-- sample 152; key=3|2,0,0,0,1,2|1; rel4=inside; rank_sha256=0caa81a217198d980411759530eb9758ffe62183d1039a80b0a886754626e4c8
example :
    ((canonicalizeP (⟨2, [0, 0, 0, 1, 2]⟩ : Word Nat) 1).toList = [2, 2, 0, 0, 1, 1]) ∧
      ((canonicalize (⟨2, [0, 0, 0, 1, 2, 1]⟩ : Word Nat)).toList = [2, 2, 0, 0, 1, 1]) := by decide

-- sample 153; key=3|2,2,1,2,0|1; rel4=inside; rank_sha256=0cb057ec313041e353c3010ca637ac9031587169ab98243e8ef45fc757575c2b
example :
    ((canonicalizeP (⟨2, [2, 1, 2, 0]⟩ : Word Nat) 1).toList = [2, 2, 1, 0, 1]) ∧
      ((canonicalize (⟨2, [2, 1, 2, 0, 1]⟩ : Word Nat)).toList = [2, 2, 1, 0, 1]) := by decide

-- sample 154; key=4|0,2,0,1|1; rel4=after; rank_sha256=0cbf3435545197c39f5831dfff6616d65b807d72970c7397304ce798cd1f7df2
example :
    ((canonicalizeP (⟨0, [2, 0, 1]⟩ : Word Nat) 1).toList = [0, 2, 0, 1, 1]) ∧
      ((canonicalize (⟨0, [2, 0, 1, 1]⟩ : Word Nat)).toList = [0, 2, 0, 1, 1]) := by decide

-- sample 155; key=4|3,3,1,2|1; rel4=after; rank_sha256=0cc00a5b3c08c6f80f9482b7b5c831b8700335091308d060fd8449e9088b3d29
example :
    ((canonicalizeP (⟨3, [3, 1, 2]⟩ : Word Nat) 1).toList = [3, 3, 1, 2, 1]) ∧
      ((canonicalize (⟨3, [3, 1, 2, 1]⟩ : Word Nat)).toList = [3, 3, 1, 2, 1]) := by decide

-- sample 156; key=4|1,2,3,2|1; rel4=before; rank_sha256=0cc03c69b281802b4eb4293489bdd9387de2f14203079154b63e2fdf900563da
example :
    ((canonicalizeP (⟨1, [2, 3, 2]⟩ : Word Nat) 1).toList = [1, 1, 2, 3, 2]) ∧
      ((canonicalize (⟨1, [2, 3, 2, 1]⟩ : Word Nat)).toList = [1, 1, 2, 3, 2]) := by decide

-- sample 157; key=4|1,1,1,3,2|3; rel4=after; rank_sha256=0ccfe9967c65d5c860afd86956b81db25c26d9ac609810edcd1e88a99fc2c583
example :
    ((canonicalizeP (⟨1, [1, 1, 3, 2]⟩ : Word Nat) 3).toList = [1, 1, 3, 2, 3]) ∧
      ((canonicalize (⟨1, [1, 1, 3, 2, 3]⟩ : Word Nat)).toList = [1, 1, 3, 2, 3]) := by decide

-- sample 158; key=4|3,3,3,2,1|1; rel4=after; rank_sha256=0cebc1d87daa698522bc7651b94bc9e17b24d1e41fbea9aa8d7f72a28ed20bcf
example :
    ((canonicalizeP (⟨3, [3, 3, 2, 1]⟩ : Word Nat) 1).toList = [3, 3, 2, 1, 1]) ∧
      ((canonicalize (⟨3, [3, 3, 2, 1, 1]⟩ : Word Nat)).toList = [3, 3, 2, 1, 1]) := by decide

-- sample 159; key=3|2,1,2,2,0,2|0; rel4=inside; rank_sha256=0cf1ae1584173af10b70d632550d5927cdd902a985352cbbed706d72f5649832
example :
    ((canonicalizeP (⟨2, [1, 2, 2, 0, 2]⟩ : Word Nat) 0).toList = [2, 1, 2, 0, 0]) ∧
      ((canonicalize (⟨2, [1, 2, 2, 0, 2, 0]⟩ : Word Nat)).toList = [2, 1, 2, 0, 0]) := by decide

-- sample 160; key=3|0,1,0,1,2,1|2; rel4=inside; rank_sha256=0cf4e35b49c00a034d078c96f0836986866fb88bf7b527715d4566873c9ba17c
example :
    ((canonicalizeP (⟨0, [1, 0, 1, 2, 1]⟩ : Word Nat) 2).toList = [0, 0, 1, 1, 2, 2]) ∧
      ((canonicalize (⟨0, [1, 0, 1, 2, 1, 2]⟩ : Word Nat)).toList = [0, 0, 1, 1, 2, 2]) := by decide

-- sample 161; key=4|3,2,1,1,2|3; rel4=before; rank_sha256=0d2a2dfaa1242b254bb147a802a96a9ceadbf910716648ce6f31bb46000a19fb
example :
    ((canonicalizeP (⟨3, [2, 1, 1, 2]⟩ : Word Nat) 3).toList = [3, 3, 2, 2, 1, 1]) ∧
      ((canonicalize (⟨3, [2, 1, 1, 2, 3]⟩ : Word Nat)).toList = [3, 3, 2, 2, 1, 1]) := by decide

-- sample 162; key=4|0,1,0,0,3|3; rel4=after; rank_sha256=0d2e7bab0fb8e9fe954e0fc13621bcf3167d0213c0efef402352f59a0bbfa989
example :
    ((canonicalizeP (⟨0, [1, 0, 0, 3]⟩ : Word Nat) 3).toList = [0, 1, 0, 3, 3]) ∧
      ((canonicalize (⟨0, [1, 0, 0, 3, 3]⟩ : Word Nat)).toList = [0, 1, 0, 3, 3]) := by decide

-- sample 163; key=3|2,2,0,0,1,2|1; rel4=inside; rank_sha256=0d31b17b2ea57ade5dc665c65a37a1882ae0b765e6f800f7e815c7f90be13ce2
example :
    ((canonicalizeP (⟨2, [2, 0, 0, 1, 2]⟩ : Word Nat) 1).toList = [2, 2, 0, 0, 1, 1]) ∧
      ((canonicalize (⟨2, [2, 0, 0, 1, 2, 1]⟩ : Word Nat)).toList = [2, 2, 0, 0, 1, 1]) := by decide

-- sample 164; key=4|2,2,1,3|1; rel4=after; rank_sha256=0d345aa0197d998acb20d24857b0f5c11a52f49108581a95d8f027382b06e5da
example :
    ((canonicalizeP (⟨2, [2, 1, 3]⟩ : Word Nat) 1).toList = [2, 2, 1, 3, 1]) ∧
      ((canonicalize (⟨2, [2, 1, 3, 1]⟩ : Word Nat)).toList = [2, 2, 1, 3, 1]) := by decide

-- sample 165; key=2|1,0|1; rel4=before; rank_sha256=0d549cf93a57107c42bb277d212ad2624949cea5f29e30844200baa769fdbfb8
example :
    ((canonicalizeP (⟨1, [0]⟩ : Word Nat) 1).toList = [1, 0, 1]) ∧
      ((canonicalize (⟨1, [0, 1]⟩ : Word Nat)).toList = [1, 0, 1]) := by decide

-- sample 166; key=4|2,0,3,1,3|0; rel4=before; rank_sha256=0dce46b27e883cbd719ee223030fb23f9cb4660ceb37d2e7b25fa66382c7670b
example :
    ((canonicalizeP (⟨2, [0, 3, 1, 3]⟩ : Word Nat) 0).toList = [2, 0, 0, 3, 1, 3]) ∧
      ((canonicalize (⟨2, [0, 3, 1, 3, 0]⟩ : Word Nat)).toList = [2, 0, 0, 3, 1, 3]) := by decide

-- sample 167; key=3|2,0,2,1,2|1; rel4=inside; rank_sha256=0dcec0f74fc8b0e47b10fd9918250ebb07ed640570b4eaedecb151f753e04ab8
example :
    ((canonicalizeP (⟨2, [0, 2, 1, 2]⟩ : Word Nat) 1).toList = [2, 0, 2, 1, 1]) ∧
      ((canonicalize (⟨2, [0, 2, 1, 2, 1]⟩ : Word Nat)).toList = [2, 0, 2, 1, 1]) := by decide

-- sample 168; key=4|2,2,1,3,0|3; rel4=after; rank_sha256=0dd2d7acd2afb7a0e7781a64c27633ec7a233c5911e96aa4c6cd7ce1f416873e
example :
    ((canonicalizeP (⟨2, [2, 1, 3, 0]⟩ : Word Nat) 3).toList = [2, 2, 1, 3, 0, 3]) ∧
      ((canonicalize (⟨2, [2, 1, 3, 0, 3]⟩ : Word Nat)).toList = [2, 2, 1, 3, 0, 3]) := by decide

-- sample 169; key=4|3,3,1|1; rel4=after; rank_sha256=0df864524a03cea34238c1269e6f0c19146ff7f8e7bb8df07fdc2d643aea47a7
example :
    ((canonicalizeP (⟨3, [3, 1]⟩ : Word Nat) 1).toList = [3, 3, 1, 1]) ∧
      ((canonicalize (⟨3, [3, 1, 1]⟩ : Word Nat)).toList = [3, 3, 1, 1]) := by decide

-- sample 170; key=4|3,1,0,2,0|1; rel4=before; rank_sha256=0e0101bdfb2ce03d985946ad7daf6892b76a7754649a8892d73edc7d0ba3f25c
example :
    ((canonicalizeP (⟨3, [1, 0, 2, 0]⟩ : Word Nat) 1).toList = [3, 1, 1, 0, 2, 0]) ∧
      ((canonicalize (⟨3, [1, 0, 2, 0, 1]⟩ : Word Nat)).toList = [3, 1, 1, 0, 2, 0]) := by decide

-- sample 171; key=3|1,0,0,1,2|2; rel4=after; rank_sha256=0e0d369bb55f36017a3c84884d261f4fd42a8d0cc1be22a10f457e3340443af1
example :
    ((canonicalizeP (⟨1, [0, 0, 1, 2]⟩ : Word Nat) 2).toList = [1, 1, 0, 0, 2, 2]) ∧
      ((canonicalize (⟨1, [0, 0, 1, 2, 2]⟩ : Word Nat)).toList = [1, 1, 0, 0, 2, 2]) := by decide

-- sample 172; key=3|1,0,0,2,1,0|2; rel4=inside; rank_sha256=0e1908ab1d98091cc26c01f3e813c60869822414ca661f34b3ac73c53fab1b85
example :
    ((canonicalizeP (⟨1, [0, 0, 2, 1, 0]⟩ : Word Nat) 2).toList = [1, 1, 0, 0, 2, 2]) ∧
      ((canonicalize (⟨1, [0, 0, 2, 1, 0, 2]⟩ : Word Nat)).toList = [1, 1, 0, 0, 2, 2]) := by decide

-- sample 173; key=3|0,2,0,1,1|2; rel4=inside; rank_sha256=0e2b106194ddbc242c5207ef342263db5730fcb04c7690f36643007fde36b834
example :
    ((canonicalizeP (⟨0, [2, 0, 1, 1]⟩ : Word Nat) 2).toList = [0, 0, 2, 2, 1, 1]) ∧
      ((canonicalize (⟨0, [2, 0, 1, 1, 2]⟩ : Word Nat)).toList = [0, 0, 2, 2, 1, 1]) := by decide

-- sample 174; key=3|1,1,2,0,2|0; rel4=inside; rank_sha256=0e32ddbcbad72ad257fe1e58af68a607d495c78b0904d77b313f277bc167059d
example :
    ((canonicalizeP (⟨1, [1, 2, 0, 2]⟩ : Word Nat) 0).toList = [1, 1, 2, 2, 0, 0]) ∧
      ((canonicalize (⟨1, [1, 2, 0, 2, 0]⟩ : Word Nat)).toList = [1, 1, 2, 2, 0, 0]) := by decide

-- sample 175; key=3|1,0,2,2|0; rel4=before; rank_sha256=0e404dbbecf06c09f1804602270e301b2ca63da9defadfc6a1119977f10d4d51
example :
    ((canonicalizeP (⟨1, [0, 2, 2]⟩ : Word Nat) 0).toList = [1, 0, 0, 2, 2]) ∧
      ((canonicalize (⟨1, [0, 2, 2, 0]⟩ : Word Nat)).toList = [1, 0, 0, 2, 2]) := by decide

-- sample 176; key=3|2,1,1,2,0,1|0; rel4=inside; rank_sha256=0e53f0c2d112c2e2921985f9a46a7f1c1a847eb67363b368fe06dfc7d6c08731
example :
    ((canonicalizeP (⟨2, [1, 1, 2, 0, 1]⟩ : Word Nat) 0).toList = [2, 2, 1, 1, 0, 0]) ∧
      ((canonicalize (⟨2, [1, 1, 2, 0, 1, 0]⟩ : Word Nat)).toList = [2, 2, 1, 1, 0, 0]) := by decide

-- sample 177; key=4|3,1,1,1,2|3; rel4=before; rank_sha256=0e556be4a8d20229a558031d6c06effcc3f27152686e94058a117a8d7368d71b
example :
    ((canonicalizeP (⟨3, [1, 1, 1, 2]⟩ : Word Nat) 3).toList = [3, 3, 1, 2, 1]) ∧
      ((canonicalize (⟨3, [1, 1, 1, 2, 3]⟩ : Word Nat)).toList = [3, 3, 1, 2, 1]) := by decide

-- sample 178; key=3|1,2,0,1,0,1|2; rel4=inside; rank_sha256=0e6a494fac8354bf03a4f4322382b9c996edd468f36e9a00504a4a7cd4995493
example :
    ((canonicalizeP (⟨1, [2, 0, 1, 0, 1]⟩ : Word Nat) 2).toList = [1, 1, 2, 2, 0, 0]) ∧
      ((canonicalize (⟨1, [2, 0, 1, 0, 1, 2]⟩ : Word Nat)).toList = [1, 1, 2, 2, 0, 0]) := by decide

-- sample 179; key=3|0,1,0,0,1,2|2; rel4=after; rank_sha256=0e6b2a4611d6967c336619fe11e71d0b5c9d68ebd3acf98f34c4114d504f8af3
example :
    ((canonicalizeP (⟨0, [1, 0, 0, 1, 2]⟩ : Word Nat) 2).toList = [0, 0, 1, 1, 2, 2]) ∧
      ((canonicalize (⟨0, [1, 0, 0, 1, 2, 2]⟩ : Word Nat)).toList = [0, 0, 1, 1, 2, 2]) := by decide

-- sample 180; key=4|0,1,2,3,3|2; rel4=before; rank_sha256=0e8d4756eb06e6d8519da0c439f4a82ba95c5af474179245ee6f068bdd183a9a
example :
    ((canonicalizeP (⟨0, [1, 2, 3, 3]⟩ : Word Nat) 2).toList = [0, 1, 2, 2, 3, 3]) ∧
      ((canonicalize (⟨0, [1, 2, 3, 3, 2]⟩ : Word Nat)).toList = [0, 1, 2, 2, 3, 3]) := by decide

-- sample 181; key=4|0,0,0,1,3|3; rel4=after; rank_sha256=0e9f8662c181a14662ddc33bf2c161560584cf29b9c5e80b33573b6be45f1e01
example :
    ((canonicalizeP (⟨0, [0, 0, 1, 3]⟩ : Word Nat) 3).toList = [0, 0, 1, 3, 3]) ∧
      ((canonicalize (⟨0, [0, 0, 1, 3, 3]⟩ : Word Nat)).toList = [0, 0, 1, 3, 3]) := by decide

-- sample 182; key=3|1,0,2,2,1|0; rel4=inside; rank_sha256=0ea1e4060ac21bb8b59a6a255386e8d0d316d008031bec9d0bf72fc363ceebff
example :
    ((canonicalizeP (⟨1, [0, 2, 2, 1]⟩ : Word Nat) 0).toList = [1, 1, 0, 0, 2, 2]) ∧
      ((canonicalize (⟨1, [0, 2, 2, 1, 0]⟩ : Word Nat)).toList = [1, 1, 0, 0, 2, 2]) := by decide

-- sample 183; key=4|1,3,1,2,1|2; rel4=inside; rank_sha256=0ec5c0adce1f00c46930c29305e9c09d91165098032249cd1b56b03bfca32fb8
example :
    ((canonicalizeP (⟨1, [3, 1, 2, 1]⟩ : Word Nat) 2).toList = [1, 3, 1, 2, 2]) ∧
      ((canonicalize (⟨1, [3, 1, 2, 1, 2]⟩ : Word Nat)).toList = [1, 3, 1, 2, 2]) := by decide

-- sample 184; key=4|1,0,2,1,2|0; rel4=inside; rank_sha256=0ec7b27ca14a753c8fc9e1f92714b07ae669415fc1549dd04857a2d8eb04c5b6
example :
    ((canonicalizeP (⟨1, [0, 2, 1, 2]⟩ : Word Nat) 0).toList = [1, 1, 0, 0, 2, 2]) ∧
      ((canonicalize (⟨1, [0, 2, 1, 2, 0]⟩ : Word Nat)).toList = [1, 1, 0, 0, 2, 2]) := by decide

-- sample 185; key=4|0,1,0,2,3|2; rel4=after; rank_sha256=0ecea44b94a16d4e193e3e672188192f739ee399c941d57cee1c0d288b703575
example :
    ((canonicalizeP (⟨0, [1, 0, 2, 3]⟩ : Word Nat) 2).toList = [0, 1, 0, 2, 3, 2]) ∧
      ((canonicalize (⟨0, [1, 0, 2, 3, 2]⟩ : Word Nat)).toList = [0, 1, 0, 2, 3, 2]) := by decide

-- sample 186; key=3|1,0,1,0,2|2; rel4=after; rank_sha256=0f4738fe21c3fd93c1418a6e3bd515769f6725fd71b88a0a62f97121e79a0759
example :
    ((canonicalizeP (⟨1, [0, 1, 0, 2]⟩ : Word Nat) 2).toList = [1, 1, 0, 0, 2, 2]) ∧
      ((canonicalize (⟨1, [0, 1, 0, 2, 2]⟩ : Word Nat)).toList = [1, 1, 0, 0, 2, 2]) := by decide

-- sample 187; key=3|0,2,2,2,1,0|1; rel4=inside; rank_sha256=0f480010a287ae74d0a3b0eef684d49e67ff38c544cb3d11f152ad123ffcb8f9
example :
    ((canonicalizeP (⟨0, [2, 2, 2, 1, 0]⟩ : Word Nat) 1).toList = [0, 0, 2, 2, 1, 1]) ∧
      ((canonicalize (⟨0, [2, 2, 2, 1, 0, 1]⟩ : Word Nat)).toList = [0, 0, 2, 2, 1, 1]) := by decide

-- sample 188; key=4|3,3,3,1,2|1; rel4=after; rank_sha256=0f480f06686cc7435e8c2a69b85a791db8b5cc36e6a1279868c8319747cd7055
example :
    ((canonicalizeP (⟨3, [3, 3, 1, 2]⟩ : Word Nat) 1).toList = [3, 3, 1, 2, 1]) ∧
      ((canonicalize (⟨3, [3, 3, 1, 2, 1]⟩ : Word Nat)).toList = [3, 3, 1, 2, 1]) := by decide

-- sample 189; key=3|0,0,0,2,1|1; rel4=after; rank_sha256=0f4ad07e6dc4dc4cb21915ef5225de5969c5ce2fe8dc5b4071f028c21fbe395f
example :
    ((canonicalizeP (⟨0, [0, 0, 2, 1]⟩ : Word Nat) 1).toList = [0, 0, 2, 1, 1]) ∧
      ((canonicalize (⟨0, [0, 0, 2, 1, 1]⟩ : Word Nat)).toList = [0, 0, 2, 1, 1]) := by decide

-- sample 190; key=3|2,2,0,0,1|1; rel4=after; rank_sha256=0f51b3883552296774d818ab502c6dcd862d0afbb6883af477ae1bcad440cac9
example :
    ((canonicalizeP (⟨2, [2, 0, 0, 1]⟩ : Word Nat) 1).toList = [2, 2, 0, 0, 1, 1]) ∧
      ((canonicalize (⟨2, [2, 0, 0, 1, 1]⟩ : Word Nat)).toList = [2, 2, 0, 0, 1, 1]) := by decide

-- sample 191; key=4|0,2,3,3,2|0; rel4=before; rank_sha256=0f6c38877af98f81df0170bfe210dbec4dda3ce306b1fff1cfcc3f0b44b9efb9
example :
    ((canonicalizeP (⟨0, [2, 3, 3, 2]⟩ : Word Nat) 0).toList = [0, 0, 2, 2, 3, 3]) ∧
      ((canonicalize (⟨0, [2, 3, 3, 2, 0]⟩ : Word Nat)).toList = [0, 0, 2, 2, 3, 3]) := by decide

-- sample 192; key=4|0,0,3,0,2|3; rel4=inside; rank_sha256=0f820c88a1935cedf5839ea1c3f1128a6e1fa2636ad0a967c19fc9d467a9cc58
example :
    ((canonicalizeP (⟨0, [0, 3, 0, 2]⟩ : Word Nat) 3).toList = [0, 0, 3, 2, 3]) ∧
      ((canonicalize (⟨0, [0, 3, 0, 2, 3]⟩ : Word Nat)).toList = [0, 0, 3, 2, 3]) := by decide

-- sample 193; key=4|3,1,0,3|1; rel4=inside; rank_sha256=0f8b29830cba687a3b9a0563dafbbc21bc192ca44f1d8962c486c64946d4f87c
example :
    ((canonicalizeP (⟨3, [1, 0, 3]⟩ : Word Nat) 1).toList = [3, 3, 1, 0, 1]) ∧
      ((canonicalize (⟨3, [1, 0, 3, 1]⟩ : Word Nat)).toList = [3, 3, 1, 0, 1]) := by decide

-- sample 194; key=3|2,1,0,0,2,2|1; rel4=inside; rank_sha256=0f9b11da9c20efcfd3495911e6228be1c1d47cdc425cbbe82ad2631512ffd6ef
example :
    ((canonicalizeP (⟨2, [1, 0, 0, 2, 2]⟩ : Word Nat) 1).toList = [2, 2, 1, 1, 0, 0]) ∧
      ((canonicalize (⟨2, [1, 0, 0, 2, 2, 1]⟩ : Word Nat)).toList = [2, 2, 1, 1, 0, 0]) := by decide

-- sample 195; key=4|0,1,2,1,3|3; rel4=after; rank_sha256=0fa079482873a34d91f07a38f51033ea15c4baeacf7568da32d492538467c440
example :
    ((canonicalizeP (⟨0, [1, 2, 1, 3]⟩ : Word Nat) 3).toList = [0, 1, 2, 1, 3, 3]) ∧
      ((canonicalize (⟨0, [1, 2, 1, 3, 3]⟩ : Word Nat)).toList = [0, 1, 2, 1, 3, 3]) := by decide

-- sample 196; key=4|0,1,1,3,0|3; rel4=inside; rank_sha256=0fa92ac461fa3e854b90042b47d01da7b91b7130cecb3d934f6704e4590e725a
example :
    ((canonicalizeP (⟨0, [1, 1, 3, 0]⟩ : Word Nat) 3).toList = [0, 0, 1, 1, 3, 3]) ∧
      ((canonicalize (⟨0, [1, 1, 3, 0, 3]⟩ : Word Nat)).toList = [0, 0, 1, 1, 3, 3]) := by decide

-- sample 197; key=4|3,0,0,2,3|2; rel4=inside; rank_sha256=0fc1738357e97805e2e4e98c2c86e0328b237b33753035ee5c8ba6e0af036139
example :
    ((canonicalizeP (⟨3, [0, 0, 2, 3]⟩ : Word Nat) 2).toList = [3, 3, 0, 0, 2, 2]) ∧
      ((canonicalize (⟨3, [0, 0, 2, 3, 2]⟩ : Word Nat)).toList = [3, 3, 0, 0, 2, 2]) := by decide

-- sample 198; key=3|2,1,1,0,1,0|2; rel4=before; rank_sha256=0fc987bd3dfe6be5486f57a5c6cbc1794ec811cb766ade25e37078b8bd0b9aa2
example :
    ((canonicalizeP (⟨2, [1, 1, 0, 1, 0]⟩ : Word Nat) 2).toList = [2, 2, 1, 1, 0, 0]) ∧
      ((canonicalize (⟨2, [1, 1, 0, 1, 0, 2]⟩ : Word Nat)).toList = [2, 2, 1, 1, 0, 0]) := by decide

-- sample 199; key=3|0,0,2,1,1|2; rel4=gap; rank_sha256=0fe19adce634c7c41386c613b04379461d62a6bd1492ae1427266bd8554b89fa
example :
    ((canonicalizeP (⟨0, [0, 2, 1, 1]⟩ : Word Nat) 2).toList = [0, 0, 2, 2, 1, 1]) ∧
      ((canonicalize (⟨0, [0, 2, 1, 1, 2]⟩ : Word Nat)).toList = [0, 0, 2, 2, 1, 1]) := by decide

-- sample 200; key=4|1,0,3,2|0; rel4=before; rank_sha256=0ff008839b60164ac2c85c5253db481f85026d1918dea3105fbc1f39010252ef
example :
    ((canonicalizeP (⟨1, [0, 3, 2]⟩ : Word Nat) 0).toList = [1, 0, 3, 2, 0]) ∧
      ((canonicalize (⟨1, [0, 3, 2, 0]⟩ : Word Nat)).toList = [1, 0, 3, 2, 0]) := by decide

-- D378_FORMULA_F_REPLAY_END


end SemigroupBasis.CoRoots.Order6FordLordD378
