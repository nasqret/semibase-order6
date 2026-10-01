import SemigroupBasis.Examples.CommutativeParityThree
import SemigroupBasis.Examples.CyclicTwo
import SemigroupBasis.Examples.SimpleEndpointsFour
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_120

open SemigroupBasis
open SemigroupBasis.Examples

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

private def supportSeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 0 else 3

private def initialSeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 2 else 3

private def finalSeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 1 else 3

def xx : Word Nat := w 0 [0]
def xxxx : Word Nat := w 0 [0, 0, 0]
def xyx : Word Nat := w 0 [1, 0]
def xxxyx : Word Nat := w 0 [0, 0, 1, 0]
def xxyxx : Word Nat := w 0 [0, 1, 0, 0]
def xxyyy : Word Nat := w 0 [0, 1, 1, 1]
def xyxxx : Word Nat := w 0 [1, 0, 0, 0]
def xyxyy : Word Nat := w 0 [1, 0, 1, 1]
def xyyxy : Word Nat := w 0 [1, 1, 0, 1]
def xyyyx : Word Nat := w 0 [1, 1, 1, 0]
def yxxyy : Word Nat := w 1 [0, 0, 1, 1]
def yxyxy : Word Nat := w 1 [0, 1, 0, 1]
def yxyyx : Word Nat := w 1 [0, 1, 1, 0]
def yyxxy : Word Nat := w 1 [1, 0, 0, 1]
def yyxyx : Word Nat := w 1 [1, 0, 1, 0]
def yyyxx : Word Nat := w 1 [1, 1, 0, 0]
def xyz : Word Nat := w 0 [1, 2]
def xyyyz : Word Nat := w 0 [1, 1, 1, 2]
def xxyx : Word Nat := w 0 [0, 1, 0]
def xyxx : Word Nat := w 0 [1, 0, 0]
def yxyy : Word Nat := w 1 [0, 1, 1]
def xxyy : Word Nat := w 0 [0, 1, 1]
def xyxy : Word Nat := w 0 [1, 0, 1]
def xyyx : Word Nat := w 0 [1, 1, 0]
def yxxy : Word Nat := w 1 [0, 0, 1]
def xxyz : Word Nat := w 0 [0, 1, 2]
def xyxz : Word Nat := w 0 [1, 0, 2]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xzyx : Word Nat := w 0 [2, 1, 0]
def xyzy : Word Nat := w 0 [1, 2, 1]
def xzyy : Word Nat := w 0 [2, 1, 1]
def xxyzx : Word Nat := w 0 [0, 1, 2, 0]
def yxyzy : Word Nat := w 1 [0, 1, 2, 1]
def xxyzy : Word Nat := w 0 [0, 1, 2, 1]
def xyyzx : Word Nat := w 0 [1, 1, 2, 0]
def yxxzy : Word Nat := w 1 [0, 0, 2, 1]

def powerLaw : Identity Nat := ⟨xx, xxxx⟩
def xyxXXXYXLaw : Identity Nat := ⟨xyx, xxxyx⟩
def xyxXXYXXLaw : Identity Nat := ⟨xyx, xxyxx⟩
def xyxXXYYYLaw : Identity Nat := ⟨xyx, xxyyy⟩
def xyxXYXXXLaw : Identity Nat := ⟨xyx, xyxxx⟩
def xyxXYXYYLaw : Identity Nat := ⟨xyx, xyxyy⟩
def xyxXYYXYLaw : Identity Nat := ⟨xyx, xyyxy⟩
def xyxXYYYXLaw : Identity Nat := ⟨xyx, xyyyx⟩
def xyxYXXYYLaw : Identity Nat := ⟨xyx, yxxyy⟩
def xyxYXYXYLaw : Identity Nat := ⟨xyx, yxyxy⟩
def xyxYXYYXLaw : Identity Nat := ⟨xyx, yxyyx⟩
def xyxYYXXYLaw : Identity Nat := ⟨xyx, yyxxy⟩
def xyxYYXYXLaw : Identity Nat := ⟨xyx, yyxyx⟩
def xyxYYYXXLaw : Identity Nat := ⟨xyx, yyyxx⟩
def interiorPowerLaw : Identity Nat := ⟨xyz, xyyyz⟩
def xxyxXYXXLaw : Identity Nat := ⟨xxyx, xyxx⟩
def xxyxYXYYLaw : Identity Nat := ⟨xxyx, yxyy⟩
def xxyyXYXYLaw : Identity Nat := ⟨xxyy, xyxy⟩
def xxyyXYYXLaw : Identity Nat := ⟨xxyy, xyyx⟩
def xxyyYXXYLaw : Identity Nat := ⟨xxyy, yxxy⟩
def xxyzXYXZLaw : Identity Nat := ⟨xxyz, xyxz⟩
def xyzxXZYXLaw : Identity Nat := ⟨xyzx, xzyx⟩
def xyzyXZYYLaw : Identity Nat := ⟨xyzy, xzyy⟩
def xxyzxYXYZYLaw : Identity Nat := ⟨xxyzx, yxyzy⟩
def xxyzyXYYZXLaw : Identity Nat := ⟨xxyzy, xyyzx⟩
def xxyzyYXXZYLaw : Identity Nat := ⟨xxyzy, yxxzy⟩

/-- The common ordered 26-identity basis of the `S5_120` family. -/
def basis : List (Identity Nat) :=
  [powerLaw,
    xyxXXXYXLaw, xyxXXYXXLaw, xyxXXYYYLaw, xyxXYXXXLaw,
    xyxXYXYYLaw, xyxXYYXYLaw, xyxXYYYXLaw, xyxYXXYYLaw,
    xyxYXYXYLaw, xyxYXYYXLaw, xyxYYXXYLaw, xyxYYXYXLaw,
    xyxYYYXXLaw, interiorPowerLaw, xxyxXYXXLaw, xxyxYXYYLaw,
    xxyyXYXYLaw, xxyyXYYXLaw, xxyyYXXYLaw, xxyzXYXZLaw,
    xyzxXZYXLaw, xyzyXZYYLaw, xxyzxYXYZYLaw,
    xxyzyXYYZXLaw, xxyzyYXXZYLaw]

def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

def finiteBasis : List (Identity (Fin 3)) :=
  basis.map fun e => e.map toFinThree

private theorem basis_roundTrip_checked :
    basis.all (fun e =>
      decide ((e.map toFinThree).map Fin.val = e)) = true := by
  decide

private theorem basis_roundTrip
    (e : Identity Nat) (member : e ∈ basis) :
    (e.map toFinThree).map Fin.val = e := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basis_roundTrip_checked) e member

theorem models_of_finite_checks
    (T : FiniteTable)
    (checked : finiteBasis.all T.checkIdentity = true) :
    Models T.semigroup basis := by
  intro e member
  have finiteMember : e.map toFinThree ∈ finiteBasis :=
    List.mem_map.mpr ⟨e, member, rfl⟩
  have finiteValid :=
    T.checkIdentityNat_sound (e.map toFinThree)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [basis_roundTrip e member] at finiteValid
  exact finiteValid

private theorem cyclicTwo_finiteBasis_checked :
    finiteBasis.all cyclicTwo.checkIdentity = true := by
  decide

theorem basis_models_cyclicTwo :
    Models cyclicTwo.semigroup basis :=
  models_of_finite_checks cyclicTwo cyclicTwo_finiteBasis_checked

private theorem simpleEndpointsFour_finiteBasis_checked :
    finiteBasis.all simpleEndpointsFour.checkIdentity = true := by
  decide

theorem basis_models_simpleEndpointsFour :
    Models simpleEndpointsFour.semigroup basis :=
  models_of_finite_checks
    simpleEndpointsFour simpleEndpointsFour_finiteBasis_checked

private def instantiateThreeWords
    (u v z : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private theorem bind_append (u v : Word Nat) (σ : Nat → Word Nat) :
    (u ++ v).bind σ = u.bind σ ++ v.bind σ := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind (word : Word Nat)
    (τ σ : Nat → Word Nat) :
    (word.bind τ).bind σ =
      word.bind (fun x => (τ x).bind σ) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- Add or remove two copies of an arbitrary nonempty block strictly
between fixed nonempty endpoint contexts. -/
theorem derivesInteriorPower
    (leftContext block rightContext : Word Nat) :
    Derives basis
      ((leftContext ++ block) ++ rightContext)
      ((leftContext ++ ((block ++ block) ++ block)) ++ rightContext) := by
  have base :
      Derives basis xyz xyyyz :=
    Derives.fromBasis (e := interiorPowerLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.head _
  have substituted :=
    Derives.subst base
      (instantiateThreeWords leftContext block rightContext)
  simpa [basis, interiorPowerLaw, xyz, xyyyz, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

private theorem derivesXYYXY (x y : Word Nat) :
    Derives basis
      ((x ++ y) ++ x)
      ((((x ++ y) ++ y) ++ x) ++ y) := by
  have base :
      Derives basis xyx xyyxy :=
    Derives.fromBasis (e := xyxXYYXYLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.head _
  have substituted :=
    Derives.subst base (instantiateThreeWords x y y)
  simpa [basis, xyxXYYXYLaw, xyx, xyyxy, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

private theorem derivesYXYXY (x y : Word Nat) :
    Derives basis
      ((x ++ y) ++ x)
      ((((y ++ x) ++ y) ++ x) ++ y) := by
  have base :
      Derives basis xyx yxyxy :=
    Derives.fromBasis (e := xyxYXYXYLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <|
        List.Mem.head _
  have substituted :=
    Derives.subst base (instantiateThreeWords x y y)
  simpa [basis, xyxYXYXYLaw, xyx, yxyxy, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Arbitrary adjacent nonempty blocks may be transposed strictly between
fixed nonempty prefix and suffix contexts. -/
theorem derivesInteriorSwap
    (leftContext left right rightContext : Word Nat) :
    Derives basis
      (((leftContext ++ left) ++ right) ++ rightContext)
      (((leftContext ++ right) ++ left) ++ rightContext) := by
  have step1 :=
    derivesInteriorPower leftContext (left ++ right) rightContext
  have step2 :=
    Derives.appendRight
      (Derives.prepend
        (((leftContext ++ left) ++ right) ++ left)
        (derivesXYYXY right left))
      rightContext
  have step3 :=
    Derives.appendRight
      (Derives.prepend leftContext
        (Derives.symm (derivesYXYXY right left)))
      ((((left ++ right) ++ left) ++ rightContext))
  have step4 :=
    Derives.symm
      (derivesInteriorPower leftContext (right ++ left) rightContext)
  exact Derives.trans
    (by simpa [Word.append_assoc] using step1) <|
    Derives.trans
      (by simpa [Word.append_assoc] using step2) <|
    Derives.trans
      (by simpa [Word.append_assoc] using step3)
      (by simpa [Word.append_assoc] using step4)

/-- Replay every derivation for `x = xxx`, `xy = yx` strictly between
fixed nonempty endpoint contexts. -/
theorem liftInteriorParity
    {u v : Word Nat}
    (derivation : Derives commutativeParityBasis u v)
    (leftContext rightContext : Word Nat) (σ : Nat → Word Nat) :
    Derives basis
      ((leftContext ++ u.bind σ) ++ rightContext)
      ((leftContext ++ v.bind σ) ++ rightContext) := by
  induction derivation generalizing leftContext rightContext σ with
  | fromBasis member =>
      simp only [commutativeParityBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simpa [parityPowerLaw, parityX, parityXXX, Word.bind,
          Word.append, Word.singleton, Word.append_assoc] using
          derivesInteriorPower leftContext (σ 0) rightContext
      · simpa [parityCommutativityLaw, parityXY, parityYX, Word.bind,
          Word.append, Word.singleton, Word.append_assoc] using
          derivesInteriorSwap leftContext (σ 0) (σ 1) rightContext
  | refl =>
      exact Derives.refl _
  | symm _ ih =>
      exact Derives.symm (ih leftContext rightContext σ)
  | trans _ _ ih₁ ih₂ =>
      exact Derives.trans
        (ih₁ leftContext rightContext σ)
        (ih₂ leftContext rightContext σ)
  | prepend p _ ih =>
      simpa [bind_append, Word.append_assoc] using
        ih (leftContext ++ p.bind σ) rightContext σ
  | appendRight _ q ih =>
      simpa [bind_append, Word.append_assoc] using
        ih leftContext (q.bind σ ++ rightContext) σ
  | subst _ τ ih =>
      simpa [bind_bind] using
        ih leftContext rightContext (fun x => (τ x).bind σ)

/-- Permute an arbitrary interior list while retaining both endpoint
letters. -/
theorem derivesMiddlePermutation
    (initial final : Nat) {left right : List Nat}
    (permutation : left.Perm right) :
    Derives basis
      (wordOfEndpoints initial left final)
      (wordOfEndpoints initial right final) := by
  induction permutation generalizing initial with
  | nil =>
      exact Derives.refl _
  | cons x _ ih =>
      simpa [wordOfEndpoints_cons] using
        Derives.prepend (Word.singleton initial) (ih x)
  | swap x y xs =>
      simpa [wordOfEndpoints_eq, Word.append_assoc] using
        derivesInteriorSwap
          (Word.singleton initial)
          (Word.singleton y) (Word.singleton x)
          (wordOfPrefixFinal xs final)
  | trans _ _ ih₁ ih₂ =>
      exact Derives.trans (ih₁ initial) (ih₂ initial)

private def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

private theorem wordOfCons_append_singleton
    (head : Nat) (tail : List Nat) (final : Nat) :
    wordOfCons head tail ++ Word.singleton final =
      wordOfPrefixFinal (head :: tail) final := by
  apply Word.toList_injective
  rw [Word.toList_append, Word.toList_singleton,
    toList_wordOfPrefixFinal]
  rfl

private theorem wordOfEndpoints_append_middle
    (initial : Nat) (pre suffix : List Nat) (final : Nat) :
    wordOfEndpoints initial (pre ++ suffix) final =
      wordOfCons initial pre ++ wordOfPrefixFinal suffix final := by
  apply Word.toList_injective
  rw [toList_wordOfEndpoints, Word.toList_append,
    toList_wordOfPrefixFinal]
  simp [wordOfCons, Word.toList, List.append_assoc]

/-- Normalize only the interior multiplicities: every supported interior
letter is retained once when odd and twice when even. -/
theorem derivesNormalizeMiddle
    (initial : Nat) (middle : List Nat) (final : Nat) :
    Derives basis
      (wordOfEndpoints initial middle final)
      (wordOfEndpoints initial
        (positiveParityReduce middle) final) := by
  cases middle with
  | nil =>
      exact Derives.refl _
  | cons x xs =>
      have normalized :=
        positiveParityDerivesNormal (wordOfCons x xs)
      change
        match positiveParityReduce (x :: xs) with
        | [] => False
        | y :: ys =>
            Derives commutativeParityBasis
              (wordOfCons x xs)
              (Word.mk y ys)
        at normalized
      cases reduced : positiveParityReduce (x :: xs) with
      | nil =>
          have present :
              x ∈ positiveParityReduce (x :: xs) :=
            (mem_positiveParityReduce_iff x (x :: xs)).mpr (by simp)
          exact False.elim (by simpa [reduced] using present)
      | cons y ys =>
          rw [reduced] at normalized
          have lifted :=
            liftInteriorParity normalized
              (Word.singleton initial) (Word.singleton final)
              Word.singleton
          rw [bind_singleton, bind_singleton] at lifted
          change
            Derives basis
              ((Word.singleton initial ++ wordOfCons x xs) ++
                Word.singleton final)
              ((Word.singleton initial ++ wordOfCons y ys) ++
                Word.singleton final)
          exact lifted

private theorem derivesPower (block : Word Nat) :
    Derives basis
      (block ++ block)
      (((block ++ block) ++ block) ++ block) := by
  have base :
      Derives basis xx xxxx :=
    Derives.fromBasis (e := powerLaw) (by simp [basis])
  have substituted :=
    Derives.subst base
      (instantiateThreeWords block block block)
  simpa [powerLaw, xx, xxxx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
    substituted

private theorem derivesClosedAddPair
    (endpoint : Nat) (middle : List Nat) :
    Derives basis
      (wordOfEndpoints endpoint middle endpoint)
      (wordOfEndpoints endpoint
        (endpoint :: endpoint :: middle) endpoint) := by
  cases middle with
  | nil =>
      simpa [wordOfEndpoints_nil, Word.append_assoc] using
        derivesPower (Word.singleton endpoint)
  | cons x xs =>
      have base :
          Derives basis xyx xxxyx :=
        Derives.fromBasis (e := xyxXXXYXLaw) (by simp [basis])
      have substituted :=
        Derives.subst base
          (instantiateThreeWords
            (Word.singleton endpoint) (wordOfCons x xs)
            (wordOfCons x xs))
      rw [wordOfEndpoints_eq, wordOfEndpoints_eq]
      have tailEq :=
        wordOfCons_append_singleton x xs endpoint
      change
        wordOfCons x xs ++ Word.singleton endpoint =
          Word.singleton x ++ wordOfPrefixFinal xs endpoint
        at tailEq
      have expanded :
          Derives basis
            (Word.singleton endpoint ++
              (wordOfCons x xs ++ Word.singleton endpoint))
            (Word.singleton endpoint ++
              (Word.singleton endpoint ++
                (Word.singleton endpoint ++
                  (wordOfCons x xs ++ Word.singleton endpoint)))) := by
        simpa [xyxXXXYXLaw, xyx, xxxyx, w,
          instantiateThreeWords, Word.bind, Word.append,
          Word.singleton, Word.append_assoc] using substituted
      rw [tailEq] at expanded
      simpa [wordOfPrefixFinal] using expanded

private theorem derivesExpandMiddle
    (initial final tested : Nat) (middle : List Nat)
    (member : tested ∈ middle) :
    Derives basis
      (wordOfEndpoints initial middle final)
      (wordOfEndpoints initial
        (tested :: tested :: tested :: middle.erase tested) final) := by
  have arrange :
      middle.Perm (tested :: middle.erase tested) :=
    List.perm_cons_erase member
  have arranged :=
    derivesMiddlePermutation initial final arrange
  have expanded :=
    derivesInteriorPower
      (Word.singleton initial) (Word.singleton tested)
      (wordOfPrefixFinal (middle.erase tested) final)
  exact Derives.trans arranged <| by
    simpa [wordOfEndpoints_eq, Word.append_assoc] using expanded

private theorem perm_extract_one_two
    {one two : Nat} {letters : List Nat}
    (different : one ≠ two)
    (oneMem : one ∈ letters)
    (twoCount : 2 ≤ letters.count two) :
    letters.Perm
      (one :: two :: two ::
        (((letters.erase one).erase two).erase two)) := by
  have first :
      letters.Perm (one :: letters.erase one) :=
    List.perm_cons_erase oneMem
  have countAfterOne :
      (letters.erase one).count two = letters.count two := by
    rw [List.count_erase_of_ne (Ne.symm different)]
  have twoMem₁ : two ∈ letters.erase one :=
    List.count_pos_iff.mp (by omega)
  have second :
      (letters.erase one).Perm
        (two :: (letters.erase one).erase two) :=
    List.perm_cons_erase twoMem₁
  have countAfterTwo :
      ((letters.erase one).erase two).count two =
        (letters.erase one).count two - 1 := by
    rw [List.count_erase_self]
  have twoMem₂ :
      two ∈ (letters.erase one).erase two :=
    List.count_pos_iff.mp (by omega)
  have third :
      ((letters.erase one).erase two).Perm
        (two :: ((letters.erase one).erase two).erase two) :=
    List.perm_cons_erase twoMem₂
  exact first.trans <|
    (List.Perm.cons one second).trans <|
      List.Perm.cons one (List.Perm.cons two third)

private theorem derivesInitialPattern
    (old new : Nat) (rest : List Nat) (final : Nat) :
    Derives basis
      (wordOfEndpoints old (old :: new :: new :: rest) final)
      (wordOfEndpoints new (old :: old :: new :: rest) final) := by
  have base :
      Derives basis xxyy yxxy :=
    Derives.fromBasis (e := xxyyYXXYLaw) (by simp [basis])
  have substituted :=
    Derives.subst base
      (instantiateThreeWords
        (Word.singleton old) (Word.singleton new)
        (Word.singleton new))
  have contextual :=
    Derives.appendRight substituted (wordOfPrefixFinal rest final)
  simpa [xxyyYXXYLaw, xxyy, yxxy, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    wordOfEndpoints_eq, Word.append_assoc] using contextual

private theorem derivesInitialSwitchOfMiddle
    (old new : Nat) (middle : List Nat) (final : Nat)
    (different : old ≠ new)
    (oldMem : old ∈ middle) (newMem : new ∈ middle) :
    ∃ switchedMiddle,
      Derives basis
        (wordOfEndpoints old middle final)
        (wordOfEndpoints new switchedMiddle final) := by
  let expanded :=
    new :: new :: new :: middle.erase new
  have expand :
      Derives basis
        (wordOfEndpoints old middle final)
        (wordOfEndpoints old expanded final) := by
    simpa [expanded] using
      derivesExpandMiddle old final new middle newMem
  have oldInErase : old ∈ middle.erase new := by
    rw [List.mem_erase_of_ne different]
    exact oldMem
  have oldInExpanded : old ∈ expanded := by
    simp [expanded, oldInErase, Ne.symm different]
  have newCount : 2 ≤ expanded.count new := by
    simp [expanded]
  let rest :=
    (((expanded.erase old).erase new).erase new)
  have arrange :
      expanded.Perm (old :: new :: new :: rest) := by
    simpa [rest] using
      perm_extract_one_two different oldInExpanded newCount
  have arranged :=
    derivesMiddlePermutation old final arrange
  refine ⟨old :: old :: new :: rest, ?_⟩
  exact Derives.trans expand <|
    Derives.trans arranged <|
      derivesInitialPattern old new rest final

/-- Replace a nonsimple initial endpoint by another supported variable.
The construction adds only pairs, so support, coordinate parity, and both
simple-endpoint markers are unchanged. -/
theorem derivesInitialSwitch
    (old new : Nat) (middle : List Nat) (final : Nat)
    (different : old ≠ new)
    (oldRepeated : old ∈ middle ∨ final = old)
    (newMem : new ∈ middle) :
    ∃ switchedMiddle,
      Derives basis
        (wordOfEndpoints old middle final)
        (wordOfEndpoints new switchedMiddle final) := by
  by_cases oldMem : old ∈ middle
  · exact derivesInitialSwitchOfMiddle
      old new middle final different oldMem newMem
  · have closed : final = old := oldRepeated.resolve_left oldMem
    subst final
    have addPair := derivesClosedAddPair old middle
    have switched :=
      derivesInitialSwitchOfMiddle
        old new (old :: old :: middle) old different
        (by simp) (by simp [different, newMem])
    obtain ⟨switchedMiddle, derivation⟩ := switched
    exact ⟨switchedMiddle, Derives.trans addPair derivation⟩

private theorem perm_cons_to_end (x : Nat) :
    ∀ letters : List Nat,
      (x :: letters).Perm (letters ++ [x])
  | [] => List.Perm.refl _
  | y :: ys =>
      (List.Perm.swap y x ys).trans <|
        List.Perm.cons y (perm_cons_to_end x ys)

private theorem perm_two_to_end (x y : Nat) :
    ∀ letters : List Nat,
      (x :: y :: letters).Perm (letters ++ [x, y])
  | [] => List.Perm.refl _
  | z :: zs =>
      (List.Perm.cons x (List.Perm.swap z y zs)).trans <|
        (List.Perm.swap z x (y :: zs)).trans <|
          List.Perm.cons z (perm_two_to_end x y zs)

private theorem derivesFinalPattern
    (initial : Nat) (rest : List Nat) (new old : Nat) :
    Derives basis
      (wordOfEndpoints initial (rest ++ [new, new, old]) old)
      (wordOfEndpoints initial (rest ++ [new, old, old]) new) := by
  have base :
      Derives basis xxyy xyyx :=
    Derives.fromBasis (e := xxyyXYYXLaw) (by simp [basis])
  have substituted :=
    Derives.subst base
      (instantiateThreeWords
        (Word.singleton new) (Word.singleton old)
        (Word.singleton old))
  have contextual :=
    Derives.prepend (wordOfCons initial rest) substituted
  rw [wordOfEndpoints_append_middle,
    wordOfEndpoints_append_middle]
  simpa [xxyyXYYXLaw, xxyy, xyyx, w,
    instantiateThreeWords, wordOfCons, Word.bind, Word.append,
    Word.singleton, wordOfPrefixFinal, Word.append_assoc] using
    contextual

private theorem derivesFinalSwitchOfMiddle
    (initial : Nat) (middle : List Nat) (old new : Nat)
    (different : old ≠ new)
    (oldMem : old ∈ middle) (newMem : new ∈ middle) :
    ∃ switchedMiddle,
      Derives basis
        (wordOfEndpoints initial middle old)
        (wordOfEndpoints initial switchedMiddle new) := by
  let expanded :=
    new :: new :: new :: middle.erase new
  have expand :
      Derives basis
        (wordOfEndpoints initial middle old)
        (wordOfEndpoints initial expanded old) := by
    simpa [expanded] using
      derivesExpandMiddle initial old new middle newMem
  have oldInErase : old ∈ middle.erase new := by
    rw [List.mem_erase_of_ne different]
    exact oldMem
  have oldInExpanded : old ∈ expanded := by
    simp [expanded, oldInErase, Ne.symm different]
  have newCount : 2 ≤ expanded.count new := by
    simp [expanded]
  let rest :=
    (((expanded.erase old).erase new).erase new)
  have arrangeFront :
      expanded.Perm (old :: new :: new :: rest) := by
    simpa [rest] using
      perm_extract_one_two different oldInExpanded newCount
  have moveOld :=
    perm_cons_to_end old (new :: new :: rest)
  have moveNew :=
    (perm_two_to_end new new rest).append_right [old]
  have arrangeEnd :
      expanded.Perm (rest ++ [new, new, old]) := by
    exact arrangeFront.trans <|
      moveOld.trans <| by
        simpa [List.append_assoc] using moveNew
  have arranged :=
    derivesMiddlePermutation initial old arrangeEnd
  refine ⟨rest ++ [new, old, old], ?_⟩
  exact Derives.trans expand <|
    Derives.trans arranged <|
      derivesFinalPattern initial rest new old

/-- Replace a nonsimple final endpoint by another supported variable. -/
theorem derivesFinalSwitch
    (initial : Nat) (middle : List Nat) (old new : Nat)
    (different : old ≠ new)
    (oldRepeated : old ∈ middle ∨ initial = old)
    (newMem : new ∈ middle) :
    ∃ switchedMiddle,
      Derives basis
        (wordOfEndpoints initial middle old)
        (wordOfEndpoints initial switchedMiddle new) := by
  by_cases oldMem : old ∈ middle
  · exact derivesFinalSwitchOfMiddle
      initial middle old new different oldMem newMem
  · have closed : initial = old := oldRepeated.resolve_left oldMem
    subst initial
    have addPair := derivesClosedAddPair old middle
    have switched :=
      derivesFinalSwitchOfMiddle
        old (old :: old :: middle) old new different
        (by simp) (by simp [different, newMem])
    obtain ⟨switchedMiddle, derivation⟩ := switched
    exact ⟨switchedMiddle, Derives.trans addPair derivation⟩

/-- Saturate a closed endpoint by adding two interior copies when it is
otherwise absent. The pair preserves every coordinate parity. -/
def saturatedMiddle
    (initial : Nat) (middle : List Nat) (final : Nat) : List Nat :=
  if initial = final ∧ initial ∉ middle then
    initial :: initial :: middle
  else middle

theorem saturatedMiddle_mem
    (z initial : Nat) (middle : List Nat) (final : Nat) :
    z ∈ saturatedMiddle initial middle final ↔
      z ∈ middle ∨ initial = final ∧ z = initial := by
  by_cases closed : initial = final
  · subst final
    by_cases present : initial ∈ middle
    · simp only [saturatedMiddle, true_and, present,
        not_true_eq_false, if_false]
      constructor
      · exact Or.inl
      · rintro (member | rfl)
        · exact member
        · exact present
    · simp [saturatedMiddle, present, or_comm]
  · simp [saturatedMiddle, closed]

theorem saturatedMiddle_closed
    (initial : Nat) (middle : List Nat) (final : Nat)
    (closed : initial = final) :
    initial ∈ saturatedMiddle initial middle final := by
  rw [saturatedMiddle_mem]
  exact Or.inr ⟨closed, rfl⟩

theorem saturatedMiddle_count_mod_two
    (z initial : Nat) (middle : List Nat) (final : Nat) :
    (saturatedMiddle initial middle final).count z % 2 =
      middle.count z % 2 := by
  by_cases added : initial = final ∧ initial ∉ middle
  · rcases added with ⟨closed, absent⟩
    subst final
    by_cases equal : initial = z
    · subst z
      simp [saturatedMiddle, absent]
      omega
    · simp [saturatedMiddle, absent, equal, Ne.symm equal]
  · simp [saturatedMiddle, added]

theorem derivesSaturate
    (initial : Nat) (middle : List Nat) (final : Nat) :
    Derives basis
      (wordOfEndpoints initial middle final)
      (wordOfEndpoints initial
        (saturatedMiddle initial middle final) final) := by
  by_cases added : initial = final ∧ initial ∉ middle
  · rcases added with ⟨closed, absent⟩
    subst final
    simpa [saturatedMiddle, absent] using
      derivesClosedAddPair initial middle
  · simp [saturatedMiddle, added]
    exact Derives.refl _

/-- Canonical interior: retain one odd or two even occurrences, then ensure
a closed endpoint occurs internally by inserting a parity-neutral pair. -/
def normalMiddle
    (initial : Nat) (middle : List Nat) (final : Nat) : List Nat :=
  saturatedMiddle initial (positiveParityReduce middle) final

theorem normalMiddle_count_le_two
    (z initial : Nat) (middle : List Nat) (final : Nat) :
    (normalMiddle initial middle final).count z ≤ 2 := by
  by_cases added :
      initial = final ∧ initial ∉ positiveParityReduce middle
  · rcases added with ⟨closed, absent⟩
    subst final
    by_cases equal : initial = z
    · subst z
      simp [normalMiddle, saturatedMiddle, absent,
        List.count_eq_zero.mpr absent]
    · simp [normalMiddle, saturatedMiddle, absent, equal]
      exact positiveParityReduce_count_le_two z middle
  · simp [normalMiddle, saturatedMiddle, added]
    exact positiveParityReduce_count_le_two z middle

theorem normalMiddle_closed
    (initial : Nat) (middle : List Nat) (final : Nat) :
    initial = final →
      initial ∈ normalMiddle initial middle final := by
  intro closed
  exact saturatedMiddle_closed initial
    (positiveParityReduce middle) final closed

theorem derivesNormalEndpoints
    (initial : Nat) (middle : List Nat) (final : Nat) :
    Derives basis
      (wordOfEndpoints initial middle final)
      (wordOfEndpoints initial
        (normalMiddle initial middle final) final) := by
  exact Derives.trans
    (derivesNormalizeMiddle initial middle final) <|
      derivesSaturate initial (positiveParityReduce middle) final

/-- The four invariants detected by the `C₂` and `S4_20` factors. -/
structure EndpointInvariants
    (initial₁ : Nat) (middle₁ : List Nat) (final₁ : Nat)
    (initial₂ : Nat) (middle₂ : List Nat) (final₂ : Nat) : Prop where
  support :
    ∀ z,
      (z ∈ initial₁ :: middle₁ ∨ final₁ = z) ↔
        (z ∈ initial₂ :: middle₂ ∨ final₂ = z)
  parity :
    ∀ z,
      (initial₁ :: middle₁ ++ [final₁]).count z % 2 =
        (initial₂ :: middle₂ ++ [final₂]).count z % 2
  simpleInitial :
    ∀ z,
      (initial₁ = z ∧ z ∉ middle₁ ∧ final₁ ≠ z) ↔
        (initial₂ = z ∧ z ∉ middle₂ ∧ final₂ ≠ z)
  simpleFinal :
    ∀ z,
      (final₁ = z ∧ z ∉ initial₁ :: middle₁) ↔
        (final₂ = z ∧ z ∉ initial₂ :: middle₂)

theorem endpointInvariants_of_factor_equal
    (initial₁ : Nat) (middle₁ : List Nat) (final₁ : Nat)
    (initial₂ : Nat) (middle₂ : List Nat) (final₂ : Nat)
    (simpleEqual :
      ∀ valuation : Nat → Fin 4,
        simpleEndpointsFour.semigroup.eval valuation
            (wordOfEndpoints initial₁ middle₁ final₁) =
          simpleEndpointsFour.semigroup.eval valuation
            (wordOfEndpoints initial₂ middle₂ final₂))
    (parityEqual :
      ∀ valuation : Nat → Fin 2,
        cyclicTwo.semigroup.eval valuation
            (wordOfEndpoints initial₁ middle₁ final₁) =
          cyclicTwo.semigroup.eval valuation
            (wordOfEndpoints initial₂ middle₂ final₂)) :
    EndpointInvariants
      initial₁ middle₁ final₁ initial₂ middle₂ final₂ := by
  constructor
  · intro z
    have absentIff :
        (z ∉ initial₁ :: middle₁ ∧ final₁ ≠ z) ↔
          (z ∉ initial₂ :: middle₂ ∧ final₂ ≠ z) := by
      constructor
      · intro absent
        apply
          (simpleEndpointsEval_supportSeparator_eq_three_iff
            z initial₂ middle₂ final₂).1
        exact
          (simpleEqual (supportSeparator z)).symm.trans <|
            (simpleEndpointsEval_supportSeparator_eq_three_iff
              z initial₁ middle₁ final₁).2 absent
      · intro absent
        apply
          (simpleEndpointsEval_supportSeparator_eq_three_iff
            z initial₁ middle₁ final₁).1
        exact
          (simpleEqual (supportSeparator z)).trans <|
            (simpleEndpointsEval_supportSeparator_eq_three_iff
              z initial₂ middle₂ final₂).2 absent
    constructor
    · intro present
      apply Decidable.byContradiction
      intro absent
      have absent₂ :
          z ∉ initial₂ :: middle₂ ∧ final₂ ≠ z := by
        simpa [not_or] using absent
      have absent₁ := absentIff.mpr absent₂
      exact
        (by simpa [not_or] using absent₁ :
          ¬(z ∈ initial₁ :: middle₁ ∨ final₁ = z)) present
    · intro present
      apply Decidable.byContradiction
      intro absent
      have absent₁ :
          z ∉ initial₁ :: middle₁ ∧ final₁ ≠ z := by
        simpa [not_or] using absent
      have absent₂ := absentIff.mp absent₁
      exact
        (by simpa [not_or] using absent₂ :
          ¬(z ∈ initial₂ :: middle₂ ∨ final₂ = z)) present
  · intro z
    have valid :
        (Identity.mk
          (wordOfEndpoints initial₁ middle₁ final₁)
          (wordOfEndpoints initial₂ middle₂ final₂)).SatisfiedBy
            cyclicTwo.semigroup :=
      parityEqual
    have parity :=
      cyclicValid_parity_eq
        (Identity.mk
          (wordOfEndpoints initial₁ middle₁ final₁)
          (wordOfEndpoints initial₂ middle₂ final₂))
        valid z
    simpa [toList_wordOfEndpoints] using parity
  · intro z
    constructor
    · intro simple
      apply
        (simpleEndpointsEval_initialSeparator_eq_two_iff
          z initial₂ middle₂ final₂).1
      exact
        (simpleEqual (initialSeparator z)).symm.trans <|
          (simpleEndpointsEval_initialSeparator_eq_two_iff
            z initial₁ middle₁ final₁).2 simple
    · intro simple
      apply
        (simpleEndpointsEval_initialSeparator_eq_two_iff
          z initial₁ middle₁ final₁).1
      exact
        (simpleEqual (initialSeparator z)).trans <|
          (simpleEndpointsEval_initialSeparator_eq_two_iff
            z initial₂ middle₂ final₂).2 simple
  · intro z
    constructor
    · intro simple
      apply
        (simpleEndpointsEval_finalSeparator_eq_one_iff
          z initial₂ middle₂ final₂).1
      exact
        (simpleEqual (finalSeparator z)).symm.trans <|
          (simpleEndpointsEval_finalSeparator_eq_one_iff
            z initial₁ middle₁ final₁).2 simple
    · intro simple
      apply
        (simpleEndpointsEval_finalSeparator_eq_one_iff
          z initial₁ middle₁ final₁).1
      exact
        (simpleEqual (finalSeparator z)).trans <|
          (simpleEndpointsEval_finalSeparator_eq_one_iff
            z initial₂ middle₂ final₂).2 simple

private theorem middle_mem_iff_invariants
    (z initial : Nat) (middle : List Nat) (final : Nat)
    (closed : initial = final → initial ∈ middle) :
    z ∈ middle ↔
      (z ∈ initial :: middle ∨ final = z) ∧
      ¬(initial = z ∧ z ∉ middle ∧ final ≠ z) ∧
      ¬(final = z ∧ z ∉ initial :: middle) := by
  constructor
  · intro member
    exact ⟨Or.inl (List.Mem.tail initial member),
      fun simple => simple.2.1 member,
      fun simple => simple.2 (List.Mem.tail initial member)⟩
  · rintro ⟨support, notInitial, notFinal⟩
    apply Decidable.byContradiction
    intro absent
    by_cases initialEq : initial = z
    · by_cases finalEq : final = z
      · apply absent
        simpa [initialEq] using closed (initialEq.trans finalEq.symm)
      · exact notInitial ⟨initialEq, absent, finalEq⟩
    · by_cases finalEq : final = z
      · apply notFinal
        refine ⟨finalEq, ?_⟩
        simpa [Ne.symm initialEq, absent]
      · exact False.elim <| by
          rcases support with support | support
          · exact initialEq <|
              (by simpa [absent] using support : z = initial).symm
          · exact finalEq support

theorem middle_mem_iff_of_invariants
    {initial₁ initial₂ : Nat}
    {middle₁ middle₂ : List Nat}
    {final₁ final₂ : Nat}
    (invariants :
      EndpointInvariants
        initial₁ middle₁ final₁ initial₂ middle₂ final₂)
    (closed₁ : initial₁ = final₁ → initial₁ ∈ middle₁)
    (closed₂ : initial₂ = final₂ → initial₂ ∈ middle₂) :
    ∀ z, z ∈ middle₁ ↔ z ∈ middle₂ := by
  intro z
  rw [middle_mem_iff_invariants
    z initial₁ middle₁ final₁ closed₁]
  rw [middle_mem_iff_invariants
    z initial₂ middle₂ final₂ closed₂]
  exact and_congr (invariants.support z) <|
    and_congr
      (not_congr (invariants.simpleInitial z))
      (not_congr (invariants.simpleFinal z))

theorem middle_parity_of_aligned_invariants
    {initial final : Nat}
    {middle₁ middle₂ : List Nat}
    (invariants :
      EndpointInvariants
        initial middle₁ final initial middle₂ final) :
    ∀ z, middle₁.count z % 2 = middle₂.count z % 2 := by
  intro z
  have parity := invariants.parity z
  by_cases initialEq : initial = z <;>
    by_cases finalEq : final = z <;>
      simp [List.count_cons, List.count_append, initialEq, finalEq,
        Nat.add_mod] at parity ⊢ <;>
      omega

theorem normalMiddle_perm_of_invariants
    {initial final : Nat}
    {middle₁ middle₂ : List Nat}
    (invariants :
      EndpointInvariants
        initial middle₁ final initial middle₂ final)
    (count₁ : ∀ z, middle₁.count z ≤ 2)
    (count₂ : ∀ z, middle₂.count z ≤ 2)
    (closed₁ : initial = final → initial ∈ middle₁)
    (closed₂ : initial = final → initial ∈ middle₂) :
    middle₁.Perm middle₂ := by
  rw [List.perm_iff_count]
  intro z
  have memberIff :=
    middle_mem_iff_of_invariants invariants closed₁ closed₂ z
  have parityEq :=
    middle_parity_of_aligned_invariants invariants z
  by_cases member₁ : z ∈ middle₁
  · have member₂ := memberIff.mp member₁
    have positive₁ := List.count_pos_iff.mpr member₁
    have positive₂ := List.count_pos_iff.mpr member₂
    have upper₁ := count₁ z
    have upper₂ := count₂ z
    omega
  · have absent₂ : z ∉ middle₂ := by
      intro member₂
      exact member₁ (memberIff.mpr member₂)
    rw [List.count_eq_zero.mpr member₁,
      List.count_eq_zero.mpr absent₂]

theorem derivesAlignInitial
    (initial₁ : Nat) (middle₁ : List Nat) (final₁ : Nat)
    (initial₂ : Nat) (middle₂ : List Nat) (final₂ : Nat)
    (invariants :
      EndpointInvariants
        initial₁ middle₁ final₁ initial₂ middle₂ final₂) :
    ∃ switchedMiddle,
      Derives basis
        (wordOfEndpoints initial₁ middle₁ final₁)
        (wordOfEndpoints initial₂ switchedMiddle final₁) := by
  by_cases initialsEq : initial₁ = initial₂
  · subst initial₂
    exact ⟨middle₁, Derives.refl _⟩
  · have oldRepeated :
        initial₁ ∈ middle₁ ∨ final₁ = initial₁ := by
      apply Decidable.byContradiction
      intro notRepeated
      have middleAbsent : initial₁ ∉ middle₁ :=
        fun member => notRepeated (Or.inl member)
      have finalNe : final₁ ≠ initial₁ :=
        fun equal => notRepeated (Or.inr equal)
      have matched :=
        (invariants.simpleInitial initial₁).mp
          ⟨rfl, middleAbsent, finalNe⟩
      exact initialsEq matched.1.symm
    have newMember : initial₂ ∈ middle₁ := by
      have targetSupport :
          initial₂ ∈ initial₂ :: middle₂ ∨ final₂ = initial₂ :=
        Or.inl (List.Mem.head middle₂)
      have sourceSupport :=
        (invariants.support initial₂).mpr targetSupport
      rcases sourceSupport with sourcePrefix | sourceFinal
      · simp only [List.mem_cons] at sourcePrefix
        rcases sourcePrefix with equal | member
        · exact False.elim (initialsEq equal.symm)
        · exact member
      · apply Decidable.byContradiction
        intro middleAbsent
        have prefixAbsent : initial₂ ∉ initial₁ :: middle₁ := by
          simpa [Ne.symm initialsEq, middleAbsent]
        have sourceSimpleFinal :
            final₁ = initial₂ ∧
              initial₂ ∉ initial₁ :: middle₁ :=
          ⟨sourceFinal, prefixAbsent⟩
        have targetSimpleFinal :=
          (invariants.simpleFinal initial₂).mp sourceSimpleFinal
        exact targetSimpleFinal.2 (List.Mem.head middle₂)
    exact derivesInitialSwitch
      initial₁ initial₂ middle₁ final₁
      initialsEq oldRepeated newMember

theorem derivesAlignFinal
    (initial₁ : Nat) (middle₁ : List Nat) (final₁ : Nat)
    (initial₂ : Nat) (middle₂ : List Nat) (final₂ : Nat)
    (initialsEq : initial₁ = initial₂)
    (invariants :
      EndpointInvariants
        initial₁ middle₁ final₁ initial₂ middle₂ final₂) :
    ∃ switchedMiddle,
      Derives basis
        (wordOfEndpoints initial₁ middle₁ final₁)
        (wordOfEndpoints initial₁ switchedMiddle final₂) := by
  subst initial₂
  by_cases finalsEq : final₁ = final₂
  · subst final₂
    exact ⟨middle₁, Derives.refl _⟩
  · have oldRepeated :
        final₁ ∈ middle₁ ∨ initial₁ = final₁ := by
      apply Decidable.byContradiction
      intro notRepeated
      have middleAbsent : final₁ ∉ middle₁ :=
        fun member => notRepeated (Or.inl member)
      have initialNe : initial₁ ≠ final₁ :=
        fun equal => notRepeated (Or.inr equal)
      have prefixAbsent : final₁ ∉ initial₁ :: middle₁ := by
        simpa [Ne.symm initialNe, middleAbsent]
      have matched :=
        (invariants.simpleFinal final₁).mp
          ⟨rfl, prefixAbsent⟩
      exact finalsEq matched.1.symm
    have newMember : final₂ ∈ middle₁ := by
      have targetSupport :
          final₂ ∈ initial₁ :: middle₂ ∨ final₂ = final₂ :=
        Or.inr rfl
      have sourceSupport :=
        (invariants.support final₂).mpr targetSupport
      rcases sourceSupport with sourcePrefix | sourceFinal
      · simp only [List.mem_cons] at sourcePrefix
        rcases sourcePrefix with equal | member
        · apply Decidable.byContradiction
          intro middleAbsent
          have sourceSimpleInitial :
              initial₁ = final₂ ∧
                final₂ ∉ middle₁ ∧ final₁ ≠ final₂ :=
            ⟨equal.symm, middleAbsent, finalsEq⟩
          have targetSimpleInitial :=
            (invariants.simpleInitial final₂).mp
              sourceSimpleInitial
          exact targetSimpleInitial.2.2 rfl
        · exact member
      · exact False.elim (finalsEq sourceFinal)
    exact derivesFinalSwitch
      initial₁ middle₁ final₁ final₂
      finalsEq oldRepeated newMember

/-- Complete derivation theorem for words with explicit initial and final
letters. Agreement in the parity and simple-endpoint factors is sufficient. -/
theorem derivesEndpointWords_of_factor_equal
    (initial₁ : Nat) (middle₁ : List Nat) (final₁ : Nat)
    (initial₂ : Nat) (middle₂ : List Nat) (final₂ : Nat)
    (simpleEqual :
      ∀ valuation : Nat → Fin 4,
        simpleEndpointsFour.semigroup.eval valuation
            (wordOfEndpoints initial₁ middle₁ final₁) =
          simpleEndpointsFour.semigroup.eval valuation
            (wordOfEndpoints initial₂ middle₂ final₂))
    (parityEqual :
      ∀ valuation : Nat → Fin 2,
        cyclicTwo.semigroup.eval valuation
            (wordOfEndpoints initial₁ middle₁ final₁) =
          cyclicTwo.semigroup.eval valuation
            (wordOfEndpoints initial₂ middle₂ final₂)) :
    Derives basis
      (wordOfEndpoints initial₁ middle₁ final₁)
      (wordOfEndpoints initial₂ middle₂ final₂) := by
  have initialInvariants :=
    endpointInvariants_of_factor_equal
      initial₁ middle₁ final₁ initial₂ middle₂ final₂
      simpleEqual parityEqual
  obtain ⟨initialMiddle, initialDerivation⟩ :=
    derivesAlignInitial
      initial₁ middle₁ final₁ initial₂ middle₂ final₂
      initialInvariants
  have initialSimpleEqual :
      ∀ valuation : Nat → Fin 4,
        simpleEndpointsFour.semigroup.eval valuation
            (wordOfEndpoints initial₂ initialMiddle final₁) =
          simpleEndpointsFour.semigroup.eval valuation
            (wordOfEndpoints initial₂ middle₂ final₂) := by
    intro valuation
    exact
      (initialDerivation.sound
        basis_models_simpleEndpointsFour valuation).symm.trans
          (simpleEqual valuation)
  have initialParityEqual :
      ∀ valuation : Nat → Fin 2,
        cyclicTwo.semigroup.eval valuation
            (wordOfEndpoints initial₂ initialMiddle final₁) =
          cyclicTwo.semigroup.eval valuation
            (wordOfEndpoints initial₂ middle₂ final₂) := by
    intro valuation
    exact
      (initialDerivation.sound
        basis_models_cyclicTwo valuation).symm.trans
          (parityEqual valuation)
  have finalInvariants :=
    endpointInvariants_of_factor_equal
      initial₂ initialMiddle final₁ initial₂ middle₂ final₂
      initialSimpleEqual initialParityEqual
  obtain ⟨alignedMiddle, finalDerivation⟩ :=
    derivesAlignFinal
      initial₂ initialMiddle final₁ initial₂ middle₂ final₂
      rfl finalInvariants
  have alignedSimpleEqual :
      ∀ valuation : Nat → Fin 4,
        simpleEndpointsFour.semigroup.eval valuation
            (wordOfEndpoints initial₂ alignedMiddle final₂) =
          simpleEndpointsFour.semigroup.eval valuation
            (wordOfEndpoints initial₂ middle₂ final₂) := by
    intro valuation
    exact
      (finalDerivation.sound
        basis_models_simpleEndpointsFour valuation).symm.trans
          (initialSimpleEqual valuation)
  have alignedParityEqual :
      ∀ valuation : Nat → Fin 2,
        cyclicTwo.semigroup.eval valuation
            (wordOfEndpoints initial₂ alignedMiddle final₂) =
          cyclicTwo.semigroup.eval valuation
            (wordOfEndpoints initial₂ middle₂ final₂) := by
    intro valuation
    exact
      (finalDerivation.sound
        basis_models_cyclicTwo valuation).symm.trans
          (initialParityEqual valuation)
  let leftMiddle :=
    normalMiddle initial₂ alignedMiddle final₂
  let rightMiddle :=
    normalMiddle initial₂ middle₂ final₂
  have leftNormal :
      Derives basis
        (wordOfEndpoints initial₂ alignedMiddle final₂)
        (wordOfEndpoints initial₂ leftMiddle final₂) := by
    simpa [leftMiddle] using
      derivesNormalEndpoints initial₂ alignedMiddle final₂
  have rightNormal :
      Derives basis
        (wordOfEndpoints initial₂ middle₂ final₂)
        (wordOfEndpoints initial₂ rightMiddle final₂) := by
    simpa [rightMiddle] using
      derivesNormalEndpoints initial₂ middle₂ final₂
  have normalSimpleEqual :
      ∀ valuation : Nat → Fin 4,
        simpleEndpointsFour.semigroup.eval valuation
            (wordOfEndpoints initial₂ leftMiddle final₂) =
          simpleEndpointsFour.semigroup.eval valuation
            (wordOfEndpoints initial₂ rightMiddle final₂) := by
    intro valuation
    exact
      (leftNormal.sound
        basis_models_simpleEndpointsFour valuation).symm.trans <|
          (alignedSimpleEqual valuation).trans <|
            rightNormal.sound
              basis_models_simpleEndpointsFour valuation
  have normalParityEqual :
      ∀ valuation : Nat → Fin 2,
        cyclicTwo.semigroup.eval valuation
            (wordOfEndpoints initial₂ leftMiddle final₂) =
          cyclicTwo.semigroup.eval valuation
            (wordOfEndpoints initial₂ rightMiddle final₂) := by
    intro valuation
    exact
      (leftNormal.sound
        basis_models_cyclicTwo valuation).symm.trans <|
          (alignedParityEqual valuation).trans <|
            rightNormal.sound basis_models_cyclicTwo valuation
  have normalInvariants :=
    endpointInvariants_of_factor_equal
      initial₂ leftMiddle final₂ initial₂ rightMiddle final₂
      normalSimpleEqual normalParityEqual
  have middlePerm : leftMiddle.Perm rightMiddle := by
    apply normalMiddle_perm_of_invariants normalInvariants
    · intro z
      simpa [leftMiddle] using
        normalMiddle_count_le_two
          z initial₂ alignedMiddle final₂
    · intro z
      simpa [rightMiddle] using
        normalMiddle_count_le_two
          z initial₂ middle₂ final₂
    · simpa [leftMiddle] using
        normalMiddle_closed initial₂ alignedMiddle final₂
    · simpa [rightMiddle] using
        normalMiddle_closed initial₂ middle₂ final₂
  exact Derives.trans initialDerivation <|
    Derives.trans finalDerivation <|
      Derives.trans leftNormal <|
        Derives.trans
          (derivesMiddlePermutation initial₂ final₂ middlePerm)
          (Derives.symm rightNormal)

/-- Generic unrestricted completeness theorem. A finite table has this basis
once it models the 26 laws and every one of its identities is inherited by the
`C₂` parity factor and the `S4_20` simple-endpoint factor. -/
theorem basis_complete_of_factors
    (T : FiniteTable)
    (models : Models T.semigroup basis)
    (toSimpleEndpoints :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        e.SatisfiedBy simpleEndpointsFour.semigroup)
    (toCyclicTwo :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        e.SatisfiedBy cyclicTwo.semigroup) :
    BasisFor T.semigroup basis := by
  refine ⟨models, ?_⟩
  intro e valid
  have simpleValid := toSimpleEndpoints e valid
  have parityValid := toCyclicTwo e valid
  cases e with
  | mk lhs rhs =>
      cases lhs with
      | mk lhsInitial lhsTail =>
          cases rhs with
          | mk rhsInitial rhsTail =>
              cases lhsTail with
              | nil =>
                  cases rhsTail with
                  | nil =>
                      have evaluated :=
                        simpleValid
                          (supportSeparator lhsInitial)
                      change
                        supportSeparator
                            lhsInitial lhsInitial =
                          supportSeparator
                            lhsInitial rhsInitial at evaluated
                      have initials : lhsInitial = rhsInitial := by
                        apply Decidable.byContradiction
                        intro different
                        simp [supportSeparator,
                          different, Ne.symm different] at evaluated
                      subst rhsInitial
                      exact Derives.refl _
                  | cons rhsNext rhsRest =>
                      have evaluated :=
                        simpleValid (fun _ => (1 : Fin 4))
                      have lhsOne :=
                        (simpleEndpointsSingletonSeparator
                          (Word.mk lhsInitial [])).2 rfl
                      have rhsOne := evaluated.symm.trans lhsOne
                      have tailNil :=
                        (simpleEndpointsSingletonSeparator
                          (Word.mk rhsInitial
                            (rhsNext :: rhsRest))).1 rhsOne
                      simp at tailNil
              | cons lhsNext lhsRest =>
                  cases rhsTail with
                  | nil =>
                      have evaluated :=
                        simpleValid (fun _ => (1 : Fin 4))
                      have rhsOne :=
                        (simpleEndpointsSingletonSeparator
                          (Word.mk rhsInitial [])).2 rfl
                      have lhsOne := evaluated.trans rhsOne
                      have tailNil :=
                        (simpleEndpointsSingletonSeparator
                          (Word.mk lhsInitial
                            (lhsNext :: lhsRest))).1 lhsOne
                      simp at tailNil
                  | cons rhsNext rhsRest =>
                      let lhsSuffix : Word Nat :=
                        Word.mk lhsNext lhsRest
                      let rhsSuffix : Word Nat :=
                        Word.mk rhsNext rhsRest
                      let lhsSplit := splitPrefixFinal lhsSuffix
                      let rhsSplit := splitPrefixFinal rhsSuffix
                      have lhsReconstruct :
                          wordOfEndpoints lhsInitial
                              lhsSplit.1 lhsSplit.2 =
                            Word.mk lhsInitial
                              (lhsNext :: lhsRest) := by
                        rw [wordOfEndpoints_eq]
                        simp only [lhsSplit]
                        rw [wordOfPrefixFinal_split lhsSuffix]
                        rfl
                      have rhsReconstruct :
                          wordOfEndpoints rhsInitial
                              rhsSplit.1 rhsSplit.2 =
                            Word.mk rhsInitial
                              (rhsNext :: rhsRest) := by
                        rw [wordOfEndpoints_eq]
                        simp only [rhsSplit]
                        rw [wordOfPrefixFinal_split rhsSuffix]
                        rfl
                      have simpleEqual :
                          ∀ valuation : Nat → Fin 4,
                            simpleEndpointsFour.semigroup.eval valuation
                                (wordOfEndpoints lhsInitial
                                  lhsSplit.1 lhsSplit.2) =
                              simpleEndpointsFour.semigroup.eval valuation
                                (wordOfEndpoints rhsInitial
                                  rhsSplit.1 rhsSplit.2) := by
                        intro valuation
                        rw [lhsReconstruct, rhsReconstruct]
                        exact simpleValid valuation
                      have parityEqual :
                          ∀ valuation : Nat → Fin 2,
                            cyclicTwo.semigroup.eval valuation
                                (wordOfEndpoints lhsInitial
                                  lhsSplit.1 lhsSplit.2) =
                              cyclicTwo.semigroup.eval valuation
                                (wordOfEndpoints rhsInitial
                                  rhsSplit.1 rhsSplit.2) := by
                        intro valuation
                        rw [lhsReconstruct, rhsReconstruct]
                        exact parityValid valuation
                      have derivation :=
                        derivesEndpointWords_of_factor_equal
                          lhsInitial lhsSplit.1 lhsSplit.2
                          rhsInitial rhsSplit.1 rhsSplit.2
                          simpleEqual parityEqual
                      rw [lhsReconstruct, rhsReconstruct] at derivation
                      exact derivation

end SemigroupBasis.CoRoots.S5_120
