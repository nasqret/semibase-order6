import SemigroupBasis.Examples.CommutativeParityThree
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- The zero-based form of the stored `S4_26` table
`[[1,1,3,1],[1,1,3,1],[3,3,1,3],[1,1,3,4]]`. -/
def paritySupportFourMul (a b : Fin 4) : Fin 4 :=
  if a = 0 then
    if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 2 else 0
  else if a = 1 then
    if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 2 else 0
  else if a = 2 then
    if b = 0 then 2 else if b = 1 then 2 else if b = 2 then 0 else 2
  else
    if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 2 else 3

/-- The Smallsemi representative `S4_26`. -/
def paritySupportFour : FiniteTable where
  order := 4
  mul := paritySupportFourMul
  assoc := by decide

def paritySupportXX : Word Nat := ⟨0, [0]⟩
def paritySupportXXXX : Word Nat := ⟨0, [0, 0, 0]⟩
def paritySupportXY : Word Nat := ⟨0, [1]⟩
def paritySupportYX : Word Nat := ⟨1, [0]⟩
def paritySupportXXXY : Word Nat := ⟨0, [0, 0, 1]⟩

def paritySupportPowerLaw : Identity Nat :=
  ⟨paritySupportXX, paritySupportXXXX⟩

def paritySupportCommutativityLaw : Identity Nat :=
  ⟨paritySupportXY, paritySupportYX⟩

def paritySupportInsertionLaw : Identity Nat :=
  ⟨paritySupportXY, paritySupportXXXY⟩

/-- The exact basis `xx = xxxx`, `xy = yx`, `xy = xxxy`. -/
def commutativeParitySupportBasis : List (Identity Nat) :=
  [paritySupportPowerLaw, paritySupportCommutativityLaw,
    paritySupportInsertionLaw]

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

theorem paritySupportDerivesCommutativity (u v : Word Nat) :
    Derives commutativeParitySupportBasis (u ++ v) (v ++ u) := by
  have hbase :
      Derives commutativeParitySupportBasis
        paritySupportXY paritySupportYX :=
    Derives.fromBasis (e := paritySupportCommutativityLaw) <| by
      exact List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [commutativeParitySupportBasis, paritySupportCommutativityLaw,
    paritySupportXY, paritySupportYX, instantiateTwoWords, Word.bind,
    Word.append, Word.singleton] using h

theorem paritySupportDerivesInsertion (u v : Word Nat) :
    Derives commutativeParitySupportBasis
      (u ++ v) (((u ++ u) ++ u) ++ v) := by
  have hbase :
      Derives commutativeParitySupportBasis
        paritySupportXY paritySupportXXXY :=
    Derives.fromBasis (e := paritySupportInsertionLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [commutativeParitySupportBasis, paritySupportInsertionLaw,
    paritySupportXY, paritySupportXXXY, instantiateTwoWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using h

theorem paritySupportDerivesPowerExpansion (u : Word Nat) :
    Derives commutativeParitySupportBasis
      (u ++ u) (((u ++ u) ++ u) ++ u) := by
  have hbase :
      Derives commutativeParitySupportBasis
        paritySupportXX paritySupportXXXX :=
    Derives.fromBasis (e := paritySupportPowerLaw) <| List.Mem.head _
  have h := Derives.subst hbase (instantiateTwoWords u u)
  simpa [commutativeParitySupportBasis, paritySupportPowerLaw,
    paritySupportXX, paritySupportXXXX, instantiateTwoWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using h

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private inductive ListDerives : List Nat → List Nat → Prop
  | empty : ListDerives [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives commutativeParitySupportBasis
        (wordOfCons x xs) (wordOfCons y ys) →
      ListDerives (x :: xs) (y :: ys)

private theorem listDerives_of_perm {xs ys : List Nat}
    (h : xs.Perm ys) : ListDerives xs ys := by
  induction h with
  | nil =>
      exact ListDerives.empty
  | cons x _ ih =>
      cases ih with
      | empty =>
          exact ListDerives.words (Derives.refl _)
      | words derivation =>
          exact ListDerives.words <| by
            simpa [wordOfCons, Word.singleton, Word.append] using
              Derives.prepend (Word.singleton x) derivation
  | swap x y xs =>
      exact ListDerives.words <| by
        cases xs with
        | nil =>
            simpa [wordOfCons, Word.append, Word.singleton] using
              paritySupportDerivesCommutativity
                (Word.singleton y) (Word.singleton x)
        | cons z zs =>
            have swapped :=
              Derives.appendRight
                (paritySupportDerivesCommutativity
                  (Word.singleton y) (Word.singleton x))
                (wordOfCons z zs)
            simpa [wordOfCons, Word.append, Word.singleton,
              Word.append_assoc] using swapped
  | trans _ _ ih₁ ih₂ =>
      cases ih₁ with
      | empty =>
          cases ih₂
          exact ListDerives.empty
      | words first =>
          cases ih₂ with
          | words second =>
              exact ListDerives.words (Derives.trans first second)

theorem paritySupportDerivesPermutation (u v : Word Nat)
    (h : u.toList.Perm v.toList) :
    Derives commutativeParitySupportBasis u v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          cases listDerives_of_perm h with
          | words derivation =>
              exact derivation

private theorem bind_append (u v : Word Nat) (σ : Nat → Word Nat) :
    (u ++ v).bind σ = u.bind σ ++ v.bind σ := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind (w : Word Nat)
    (τ σ : Nat → Word Nat) :
    (w.bind τ).bind σ = w.bind (fun x => (τ x).bind σ) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (w : Word Nat) :
    w.bind Word.singleton = w := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- The parity power law `u = uuu` is available after any fixed nonempty
prefix. The prefix supplies the context required by `xy = xxxy`. -/
theorem paritySupportDerivesContextPower
    (marker u : Word Nat) :
    Derives commutativeParitySupportBasis
      (marker ++ u) (marker ++ ((u ++ u) ++ u)) := by
  have enter := paritySupportDerivesCommutativity marker u
  have expand := paritySupportDerivesInsertion u marker
  have exit :=
    paritySupportDerivesCommutativity ((u ++ u) ++ u) marker
  exact Derives.trans enter <|
    Derives.trans
      (by simpa [Word.append_assoc] using expand)
      (by simpa [Word.append_assoc] using exit)

/-- Any derivation from `x = xxx`, `xy = yx` can be replayed inside a
fixed nonempty prefix using `xy = xxxy` for the power step. The explicit
substitution parameter makes the statement stable under nested substitution. -/
theorem paritySupportLiftParity
    {u v : Word Nat}
    (h : Derives commutativeParityBasis u v)
    (marker : Word Nat) (σ : Nat → Word Nat) :
    Derives commutativeParitySupportBasis
      (marker ++ u.bind σ) (marker ++ v.bind σ) := by
  induction h generalizing marker σ with
  | fromBasis hmem =>
      simp only [commutativeParityBasis, List.mem_cons,
        List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · simpa [parityPowerLaw, parityX, parityXXX, Word.bind,
          Word.append, Word.singleton, Word.append_assoc] using
          paritySupportDerivesContextPower marker (σ 0)
      · have commute :=
          paritySupportDerivesCommutativity (σ 0) (σ 1)
        simpa [parityCommutativityLaw, parityXY, parityYX, Word.bind,
          Word.append, Word.singleton, Word.append_assoc] using
          Derives.prepend marker commute
  | refl =>
      exact Derives.refl _
  | symm _ ih =>
      exact Derives.symm (ih marker σ)
  | trans _ _ ih₁ ih₂ =>
      exact Derives.trans (ih₁ marker σ) (ih₂ marker σ)
  | prepend p _ ih =>
      simpa [bind_append, Word.append_assoc] using
        ih (marker ++ p.bind σ) σ
  | appendRight _ q ih =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight (ih marker σ) (q.bind σ)
  | subst _ τ ih =>
      simpa [bind_bind] using
        ih marker (fun x => (τ x).bind σ)

private theorem two_copies_perm (x : Nat) (xs : List Nat)
    (hcount : xs.count x = 2) :
    xs.Perm (x :: x :: (xs.erase x).erase x) := by
  have hx : x ∈ xs := List.count_pos_iff.mp (by omega)
  have first := List.perm_cons_erase hx
  have herase : (xs.erase x).count x = 1 := by
    rw [List.count_erase_self]
    omega
  have hxErase : x ∈ xs.erase x :=
    List.count_pos_iff.mp (by omega)
  exact first.trans (List.Perm.cons x (List.perm_cons_erase hxErase))

/-- The normal form is the positive support-parity reduction, except that a
non-singleton unary word of odd length keeps three copies rather than one. -/
def paritySupportReduce (xs : List Nat) : List Nat :=
  match positiveParityReduce xs with
  | [x] => if xs.length = 1 then [x] else [x, x, x]
  | reduced => reduced

theorem paritySupportDerivesNormal (w : Word Nat) :
    match paritySupportReduce w.toList with
    | [] => False
    | x :: xs =>
        Derives commutativeParitySupportBasis w (wordOfCons x xs) := by
  cases w with
  | mk head tail =>
      cases tail with
      | nil =>
          exact Derives.refl _
      | cons next rest =>
          change
            match paritySupportReduce (head :: next :: rest) with
            | [] => False
            | x :: xs =>
                Derives commutativeParitySupportBasis
                  (wordOfCons head (next :: rest)) (wordOfCons x xs)
          let suffix := wordOfCons next rest
          have suffixNormal := positiveParityDerivesNormal suffix
          cases hs : positiveParityReduce (next :: rest) with
          | nil =>
              have present :
                  next ∈ positiveParityReduce (next :: rest) :=
                (mem_positiveParityReduce_iff _ _).mpr (by simp)
              exact False.elim (by simpa [hs] using present)
          | cons z zs =>
              change
                match positiveParityReduce (next :: rest) with
                | [] => False
                | x :: xs =>
                    Derives commutativeParityBasis
                      suffix (wordOfCons x xs) at suffixNormal
              rw [hs] at suffixNormal
              have lifted :=
                paritySupportLiftParity suffixNormal
                  (Word.singleton head) Word.singleton
              have prefixed :
                  Derives commutativeParitySupportBasis
                    (wordOfCons head (next :: rest))
                    (wordOfCons head (z :: zs)) := by
                rw [bind_singleton, bind_singleton] at lifted
                simpa [suffix, wordOfCons, Word.append,
                  Word.singleton] using lifted
              by_cases hcount : (z :: zs).count head < 2
              · have reduced :
                    positiveParityReduce (head :: next :: rest) =
                      head :: z :: zs := by
                  change
                    (if (positiveParityReduce (next :: rest)).count head < 2
                      then head :: positiveParityReduce (next :: rest)
                      else (positiveParityReduce (next :: rest)).erase head) =
                      head :: z :: zs
                  rw [hs, if_pos hcount]
                rw [show paritySupportReduce (head :: next :: rest) =
                    head :: z :: zs by
                  simp [paritySupportReduce, reduced]]
                exact prefixed
              · have countLe :
                    (z :: zs).count head ≤ 2 := by
                  rw [← hs]
                  exact positiveParityReduce_count_le_two head (next :: rest)
                have countEq : (z :: zs).count head = 2 := by omega
                let remainder := ((z :: zs).erase head).erase head
                have suffixPerm :
                    (z :: zs).Perm (head :: head :: remainder) := by
                  simpa [remainder] using
                    two_copies_perm head (z :: zs) countEq
                have expandedPerm :
                    (head :: z :: zs).Perm
                      (head :: head :: head :: remainder) :=
                  List.Perm.cons head suffixPerm
                have arrange :
                    Derives commutativeParitySupportBasis
                      (wordOfCons head (z :: zs))
                      (wordOfCons head (head :: head :: remainder)) :=
                  paritySupportDerivesPermutation _ _ expandedPerm
                have positiveReduced :
                    positiveParityReduce (head :: next :: rest) =
                      (z :: zs).erase head := by
                  change
                    (if (positiveParityReduce (next :: rest)).count head < 2
                      then head :: positiveParityReduce (next :: rest)
                      else (positiveParityReduce (next :: rest)).erase head) =
                      (z :: zs).erase head
                  rw [hs, if_neg hcount]
                cases hr : remainder with
                | nil =>
                    rw [hr] at arrange
                    have erasedOnce : (z :: zs).erase head = [head] := by
                      have eraseCount :
                          ((z :: zs).erase head).count head = 1 := by
                        rw [List.count_erase_self, countEq]
                      have eraseHas :
                          head ∈ (z :: zs).erase head :=
                        List.count_pos_iff.mp (by omega)
                      have secondErase :
                          ((z :: zs).erase head).erase head = [] := by
                        simpa [remainder, hr]
                      have perm :=
                        List.perm_cons_erase eraseHas
                      rw [secondErase] at perm
                      exact List.perm_singleton.mp perm
                    have finalReduce :
                        paritySupportReduce (head :: next :: rest) =
                          [head, head, head] := by
                      simp [paritySupportReduce, positiveReduced,
                        erasedOnce]
                    rw [finalReduce]
                    exact Derives.trans prefixed arrange
                | cons r rs =>
                    rw [hr] at arrange
                    have contract :
                        Derives commutativeParitySupportBasis
                          (wordOfCons head (head :: head :: r :: rs))
                          (wordOfCons head (r :: rs)) := by
                      have middle :=
                        Derives.symm <|
                          paritySupportDerivesContextPower
                            (wordOfCons r rs) (Word.singleton head)
                      have enter :=
                        paritySupportDerivesCommutativity
                          (((Word.singleton head ++ Word.singleton head) ++
                            Word.singleton head))
                          (wordOfCons r rs)
                      have exit :=
                        paritySupportDerivesCommutativity
                          (wordOfCons r rs) (Word.singleton head)
                      exact Derives.trans
                        (by
                          simpa [wordOfCons, Word.append, Word.singleton,
                            Word.append_assoc] using enter)
                        (Derives.trans
                          (by
                            simpa [wordOfCons, Word.append,
                              Word.singleton, Word.append_assoc] using middle)
                          (by
                            simpa [wordOfCons, Word.append,
                              Word.singleton, Word.append_assoc] using exit))
                    have eraseCount :
                        ((z :: zs).erase head).count head = 1 := by
                      rw [List.count_erase_self, countEq]
                    have eraseHas :
                        head ∈ (z :: zs).erase head :=
                      List.count_pos_iff.mp (by omega)
                    have restorePerm :
                        (head :: r :: rs).Perm ((z :: zs).erase head) := by
                      simpa [remainder, hr] using
                        (List.perm_cons_erase eraseHas).symm
                    have restore :=
                      paritySupportDerivesPermutation
                        (wordOfCons head (r :: rs))
                        (match (z :: zs).erase head with
                        | [] => wordOfCons head (r :: rs)
                        | q :: qs => wordOfCons q qs) <| by
                          cases he : (z :: zs).erase head with
                          | nil =>
                              exact False.elim <| by
                                simpa [he] using eraseCount
                          | cons q qs =>
                              simpa [he] using restorePerm
                    cases he : (z :: zs).erase head with
                    | nil =>
                        exact False.elim <| by
                          simpa [he] using eraseCount
                    | cons q qs =>
                        cases qs with
                        | nil =>
                            have lengths := restorePerm.length_eq
                            simp [he] at lengths
                        | cons s ss =>
                            have finalReduce :
                                paritySupportReduce
                                    (head :: next :: rest) =
                                  q :: s :: ss := by
                              simp [paritySupportReduce, positiveReduced, he]
                            rw [finalReduce]
                            exact Derives.trans prefixed <|
                              Derives.trans arrange <|
                              Derives.trans contract <| by
                                simpa [he] using restore

theorem paritySupportReduce_perm
    {xs ys : List Nat}
    (leftNonempty : xs ≠ [])
    (rightNonempty : ys ≠ [])
    (supportEq : ∀ z, z ∈ xs ↔ z ∈ ys)
    (parityEq : ∀ z, xs.count z % 2 = ys.count z % 2)
    (singletonEq : xs.length = 1 ↔ ys.length = 1) :
    (paritySupportReduce xs).Perm (paritySupportReduce ys) := by
  have reducedPerm :=
    positiveParityReduce_perm supportEq parityEq
  cases hl : positiveParityReduce xs with
  | nil =>
      have hx := leftNonempty
      cases xs with
      | nil => exact False.elim (hx rfl)
      | cons x rest =>
          have present :
              x ∈ positiveParityReduce (x :: rest) :=
            (mem_positiveParityReduce_iff _ _).mpr (by simp)
          exact False.elim (by simpa [hl] using present)
  | cons x xt =>
      cases xt with
      | nil =>
          have hr :
              positiveParityReduce ys = [x] :=
            List.perm_singleton.mp <| by
              simpa [hl] using reducedPerm.symm
          simp only [paritySupportReduce, hl, hr]
          by_cases hxl : xs.length = 1
          · have hyl : ys.length = 1 := singletonEq.mp hxl
            simp [hxl, hyl]
          · have hyl : ys.length ≠ 1 :=
              fun h => hxl (singletonEq.mpr h)
            simp [hxl, hyl]
      | cons y yt =>
          cases hr : positiveParityReduce ys with
          | nil =>
              rw [hl, hr] at reducedPerm
              exact False.elim (List.not_perm_cons_nil reducedPerm)
          | cons q qt =>
              cases qt with
              | nil =>
                  have lengthEq := reducedPerm.length_eq
                  simp [hl, hr] at lengthEq
              | cons r rt =>
                  simpa [paritySupportReduce, hl, hr] using reducedPerm

private theorem paritySupportFourMul_commutative (a b : Fin 4) :
    paritySupportFourMul a b = paritySupportFourMul b a := by
  decide +revert

private theorem paritySupportFourMul_power (a : Fin 4) :
    paritySupportFourMul a a =
      paritySupportFourMul
        (paritySupportFourMul
          (paritySupportFourMul a a) a) a := by
  decide +revert

private theorem paritySupportFourMul_insertion (a b : Fin 4) :
    paritySupportFourMul a b =
      paritySupportFourMul
        (paritySupportFourMul
          (paritySupportFourMul a a) a) b := by
  decide +revert

theorem paritySupportFourBasis_models :
    Models paritySupportFour.semigroup commutativeParitySupportBasis := by
  intro e he
  simp only [commutativeParitySupportBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · intro valuation
    exact paritySupportFourMul_power (valuation 0)
  · intro valuation
    exact paritySupportFourMul_commutative (valuation 0) (valuation 1)
  · intro valuation
    exact paritySupportFourMul_insertion (valuation 0) (valuation 1)

private def supportSeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 0 else 3

private def paritySeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 2 else 0

private def singletonSeparator : Nat → Fin 4 := fun _ => 1

private def supportState (n : Nat) : Fin 4 :=
  if n = 0 then 3 else 0

private theorem supportMul_target (n : Nat) :
    paritySupportFourMul (supportState n) 0 =
      supportState (n + 1) := by
  by_cases hn : n = 0
  · subst n
    rfl
  · simp [supportState, paritySupportFourMul, hn]

private theorem supportMul_other (n : Nat) :
    paritySupportFourMul (supportState n) 3 =
      supportState n := by
  by_cases hn : n = 0
  · subst n
    rfl
  · simp [supportState, paritySupportFourMul, hn]

private theorem supportFold
    (z : Nat) (xs : List Nat) (acc : Nat) :
    xs.foldl
        (fun current x =>
          paritySupportFourMul current (supportSeparator z x))
        (supportState acc) =
      supportState (acc + xs.count z) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [List.count_cons_self]
        rw [show supportSeparator z z = (0 : Fin 4) by
          simp [supportSeparator]]
        rw [supportMul_target, ih]
        congr 1
        omega
      · rw [List.count_cons_of_ne hx]
        rw [show supportSeparator z x = (3 : Fin 4) by
          simp [supportSeparator, hx]]
        rw [supportMul_other, ih]

private theorem paritySupportEval_supportSeparator
    (z : Nat) (w : Word Nat) :
    paritySupportFour.semigroup.eval (supportSeparator z) w =
      supportState (w.toList.count z) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              paritySupportFourMul current (supportSeparator z x))
            (supportSeparator z head) =
          supportState ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [List.count_cons_self]
        rw [show supportSeparator z z = supportState 1 by
          apply Fin.ext
          simp [supportSeparator, supportState]]
        rw [supportFold]
        congr 1
        omega
      · rw [List.count_cons_of_ne hhead]
        rw [show supportSeparator z head = supportState 0 by
          apply Fin.ext
          simp [supportSeparator, supportState, hhead]]
        rw [supportFold]
        congr 1
        omega

theorem paritySupportValid_support
    (e : Identity Nat)
    (valid : e.SatisfiedBy paritySupportFour.semigroup) :
    ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList := by
  intro z
  have evaluated := valid (supportSeparator z)
  rw [paritySupportEval_supportSeparator,
    paritySupportEval_supportSeparator] at evaluated
  constructor
  · intro hl
    apply Decidable.byContradiction
    intro hr
    have hlne : e.lhs.toList.count z ≠ 0 :=
      Nat.ne_of_gt (List.count_pos_iff.mpr hl)
    have hrzero : e.rhs.toList.count z = 0 :=
      List.count_eq_zero.mpr hr
    simp [supportState, hlne, hrzero] at evaluated
  · intro hr
    apply Decidable.byContradiction
    intro hl
    have hrne : e.rhs.toList.count z ≠ 0 :=
      Nat.ne_of_gt (List.count_pos_iff.mpr hr)
    have hlzero : e.lhs.toList.count z = 0 :=
      List.count_eq_zero.mpr hl
    simp [supportState, hlzero, hrne] at evaluated

private def parityState (n : Nat) : Fin 4 :=
  ⟨2 * (n % 2), by omega⟩

private theorem parityMul_target (n : Nat) :
    paritySupportFourMul (parityState n) 2 =
      parityState (n + 1) := by
  by_cases hp : n % 2 = 0
  · have hnext : (n + 1) % 2 = 1 := by omega
    simp [parityState, paritySupportFourMul, hp, hnext]
  · have hmod : n % 2 = 1 := by omega
    have hnext : (n + 1) % 2 = 0 := by omega
    simp [parityState, paritySupportFourMul, hmod, hnext]

private theorem parityMul_other (n : Nat) :
    paritySupportFourMul (parityState n) 0 =
      parityState n := by
  by_cases hp : n % 2 = 0
  · simp [parityState, paritySupportFourMul, hp]
  · have hmod : n % 2 = 1 := by omega
    simp [parityState, paritySupportFourMul, hmod]

private theorem parityFold
    (z : Nat) (xs : List Nat) (acc : Nat) :
    xs.foldl
        (fun current x =>
          paritySupportFourMul current (paritySeparator z x))
        (parityState acc) =
      parityState (acc + xs.count z) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [List.count_cons_self]
        rw [show paritySeparator z z = (2 : Fin 4) by
          simp [paritySeparator]]
        rw [parityMul_target, ih]
        congr 1
        omega
      · rw [List.count_cons_of_ne hx]
        rw [show paritySeparator z x = (0 : Fin 4) by
          simp [paritySeparator, hx]]
        rw [parityMul_other, ih]

private theorem paritySupportEval_paritySeparator
    (z : Nat) (w : Word Nat) :
    paritySupportFour.semigroup.eval (paritySeparator z) w =
      parityState (w.toList.count z) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              paritySupportFourMul current (paritySeparator z x))
            (paritySeparator z head) =
          parityState ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [List.count_cons_self]
        rw [show paritySeparator z z = parityState 1 by
          apply Fin.ext
          simp [paritySeparator, parityState]]
        rw [parityFold]
        congr 1
        omega
      · rw [List.count_cons_of_ne hhead]
        rw [show paritySeparator z head = parityState 0 by
          apply Fin.ext
          simp [paritySeparator, parityState, hhead]]
        rw [parityFold]
        congr 1
        omega

theorem paritySupportValid_parity
    (e : Identity Nat)
    (valid : e.SatisfiedBy paritySupportFour.semigroup) :
    ∀ z, e.lhs.toList.count z % 2 =
      e.rhs.toList.count z % 2 := by
  intro z
  have evaluated := valid (paritySeparator z)
  rw [paritySupportEval_paritySeparator,
    paritySupportEval_paritySeparator] at evaluated
  have values := congrArg Fin.val evaluated
  change
    2 * (e.lhs.toList.count z % 2) =
      2 * (e.rhs.toList.count z % 2) at values
  omega

private theorem singletonFold_zero (xs : List Nat) :
    xs.foldl
        (fun current x =>
          paritySupportFourMul current (singletonSeparator x)) 0 = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons, singletonSeparator]
      change
        xs.foldl (fun current _ => paritySupportFourMul current 1) 0 = 0
      exact ih

private theorem singletonFold (xs : List Nat) :
    xs.foldl
        (fun current x =>
          paritySupportFourMul current (singletonSeparator x)) 1 =
      if xs = [] then 1 else 0 := by
  cases xs with
  | nil => rfl
  | cons x xs =>
      simp only [List.foldl_cons, singletonSeparator]
      change
        xs.foldl (fun current _ => paritySupportFourMul current 1) 0 = 0
      exact singletonFold_zero xs

private theorem paritySupportEval_singletonSeparator
    (w : Word Nat) :
    paritySupportFour.semigroup.eval singletonSeparator w =
      if w.tail = [] then (1 : Fin 4) else 0 := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              paritySupportFourMul current (singletonSeparator x))
            (singletonSeparator head) =
          if tail = [] then 1 else 0
      simpa [singletonSeparator] using singletonFold tail

theorem paritySupportValid_singleton
    (e : Identity Nat)
    (valid : e.SatisfiedBy paritySupportFour.semigroup) :
    e.lhs.toList.length = 1 ↔ e.rhs.toList.length = 1 := by
  have evaluated := valid singletonSeparator
  rw [paritySupportEval_singletonSeparator,
    paritySupportEval_singletonSeparator] at evaluated
  have lhsIff : e.lhs.toList.length = 1 ↔ e.lhs.tail = [] := by
    simp [Word.toList]
  have rhsIff : e.rhs.toList.length = 1 ↔ e.rhs.tail = [] := by
    simp [Word.toList]
  rw [lhsIff, rhsIff]
  constructor
  · intro hl
    apply Decidable.byContradiction
    intro hr
    simp [hl, hr] at evaluated
  · intro hr
    apply Decidable.byContradiction
    intro hl
    simp [hl, hr] at evaluated

theorem commutativeParitySupportBasis_complete :
    BasisFor paritySupportFour.semigroup commutativeParitySupportBasis := by
  refine ⟨paritySupportFourBasis_models, ?_⟩
  intro e valid
  have reducedPerm :=
    paritySupportReduce_perm
      (by simp [Word.toList]) (by simp [Word.toList])
      (paritySupportValid_support e valid)
      (paritySupportValid_parity e valid)
      (paritySupportValid_singleton e valid)
  have lhsNormal := paritySupportDerivesNormal e.lhs
  have rhsNormal := paritySupportDerivesNormal e.rhs
  cases hl : paritySupportReduce e.lhs.toList with
  | nil =>
      have notEmpty : paritySupportReduce e.lhs.toList ≠ [] := by
        intro hempty
        unfold paritySupportReduce at hempty
        cases hp : positiveParityReduce e.lhs.toList with
        | nil =>
            have present :
                e.lhs.head ∈ positiveParityReduce e.lhs.toList :=
              (mem_positiveParityReduce_iff _ _).mpr
                (by simp [Word.toList])
            simpa [hp] using present
        | cons x xs =>
            cases xs with
            | nil =>
                split at hempty <;> simp_all
            | cons y ys =>
                simp [hp] at hempty
      exact False.elim (notEmpty hl)
  | cons x xs =>
      cases hr : paritySupportReduce e.rhs.toList with
      | nil =>
          rw [hl, hr] at reducedPerm
          exact False.elim (List.not_perm_cons_nil reducedPerm)
      | cons y ys =>
          rw [hl] at lhsNormal
          rw [hr] at rhsNormal
          rw [hl, hr] at reducedPerm
          exact Derives.trans lhsNormal <|
            Derives.trans
              (paritySupportDerivesPermutation
                (wordOfCons x xs) (wordOfCons y ys) reducedPerm)
              (Derives.symm rhsNormal)

theorem commutativeParitySupportOppositeBasis_complete :
    BasisFor paritySupportFour.semigroup.opposite
      (reversedBasis commutativeParitySupportBasis) :=
  commutativeParitySupportBasis_complete.oppositeReversed

end SemigroupBasis.Examples
