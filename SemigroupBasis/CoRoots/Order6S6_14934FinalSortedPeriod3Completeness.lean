import SemigroupBasis.CoRoots.Order6S6_14934FinalSortedPeriod3Prelude
import Std.Tactic

namespace SemigroupBasis

namespace CoRoots

namespace Order6S6_14934FinalSortedPeriod3

private def lastLetter (word : Word Nat) : Nat :=
  word.tail.foldl (fun _ next => next) word.head

private def positiveResidue (n : Nat) : Nat :=
  if n = 0 then 0 else (n - 1) % 3 + 1

private def cycleValue (n : Nat) : Fin 6 :=
  if n = 0 then 2 else if n % 3 = 1 then 4 else if n % 3 = 2 then 5 else 0

private theorem mul_2_2 : mul 2 2 = 2 := by decide
private theorem mul_4_2 : mul 4 2 = 4 := by decide
private theorem mul_5_2 : mul 5 2 = 5 := by decide
private theorem mul_0_2 : mul 0 2 = 0 := by decide
private theorem mul_2_4 : mul 2 4 = 4 := by decide
private theorem mul_4_4 : mul 4 4 = 5 := by decide
private theorem mul_5_4 : mul 5 4 = 0 := by decide
private theorem mul_0_4 : mul 0 4 = 4 := by decide

private theorem cycleValue_stay (n : Nat) :
    mul (cycleValue n) 2 = cycleValue n := by
  unfold cycleValue
  by_cases h0 : n = 0 <;> by_cases h1 : n % 3 = 1 <;>
    by_cases h2 : n % 3 = 2 <;>
      simp [h0, h1, h2, mul_2_2, mul_4_2, mul_5_2, mul_0_2]

private theorem cycleValue_step (n : Nat) :
    mul (cycleValue n) 4 = cycleValue (n + 1) := by
  unfold cycleValue
  by_cases h0 : n = 0
  · subst n
    decide
  · have hlt : n % 3 < 3 := Nat.mod_lt n (by decide)
    by_cases h1 : n % 3 = 1 <;> by_cases h2 : n % 3 = 2
    all_goals simp [h0, h1, h2, mul_4_4, mul_5_4, mul_0_4, Nat.add_mod]
    all_goals omega

private theorem fold_cycle (letters : List Nat) (x : Nat) (n : Nat) :
    letters.foldl
        (fun current y => mul current (if y = x then 4 else 2))
        (cycleValue n) =
      cycleValue (n + letters.count x) := by
  induction letters generalizing n with
  | nil => simp
  | cons y ys ih =>
      simp only [List.foldl_cons, List.count_cons]
      by_cases hy : y = x
      · simp [hy, cycleValue_step]
        rw [ih]
        congr 1
        omega
      · simp [hy, cycleValue_stay]
        exact ih n

private theorem eval_cycle (word : Word Nat) (x : Nat) :
    table.semigroup.eval (fun y => if y = x then (4 : Fin 6) else (2 : Fin 6)) word =
      cycleValue (word.toList.count x) := by
  rw [Semigroup.eval]
  rw [show word.toList = word.head :: word.tail by rfl]
  rw [show (if word.head = x then (4 : Fin 6) else (2 : Fin 6)) =
      cycleValue (if word.head = x then 1 else 0) by
    by_cases h : word.head = x <;> simp [h, cycleValue]]
  change List.foldl
      (fun current y => mul current (if y = x then 4 else 2))
      (cycleValue (if word.head = x then 1 else 0)) word.tail = _
  rw [fold_cycle]
  congr 1
  simp [List.count_cons]
  by_cases h : word.head = x <;> simp [h]
  omega

private theorem cycleValue_injective :
    ∀ {m n : Nat}, cycleValue m = cycleValue n →
      positiveResidue m = positiveResidue n := by
  unfold cycleValue positiveResidue at *;
  grind

private theorem mul_2_3 : mul 2 3 = 3 := by decide
private theorem mul_3_2 : mul 3 2 = 2 := by decide
private theorem mul_3_3 : mul 3 3 = 3 := by decide

private theorem fold_last_detector (letters : List Nat) (x start : Nat) :
    letters.foldl (fun state y => mul state (if y = x then 3 else 2))
        (if start = x then 3 else 2) =
      if lastLetter ⟨start, letters⟩ = x then 3 else 2 := by
  induction letters generalizing start with
  | nil => simp [lastLetter]
  | cons y ys ih =>
      simp only [List.foldl_cons]
      have hmul :
          mul (if start = x then (3 : Fin 6) else 2)
              (if y = x then 3 else 2) =
            (if y = x then 3 else 2) := by
        by_cases hs : start = x <;> by_cases hy : y = x <;>
          simp [hs, hy, mul_2_2, mul_2_3, mul_3_2, mul_3_3]
      rw [hmul, ih (start := y)]
      rfl

private theorem eval_last_detector (word : Word Nat) (x : Nat) :
    table.semigroup.eval (fun y => if y = x then (3 : Fin 6) else (2 : Fin 6)) word = (3 : Fin 6) ↔
      lastLetter word = x := by
  rw [show table.semigroup.eval
      (fun y => if y = x then (3 : Fin 6) else (2 : Fin 6)) word =
      (if lastLetter word = x then (3 : Fin 6) else (2 : Fin 6)) from
    fold_last_detector word.tail x word.head]
  by_cases h : lastLetter word = x <;> simp [h]

private theorem mul_0_1 : mul 0 1 = 0 := by decide
private theorem mul_0_2' : mul 0 2 = 0 := by decide
private theorem mul_1_1 : mul 1 1 = 0 := by decide
private theorem mul_1_2 : mul 1 2 = 0 := by decide
private theorem mul_2_1 : mul 2 1 = 1 := by decide
private theorem mul_2_2' : mul 2 2 = 2 := by decide

private def binaryFold (z : Nat) (letters : List Nat) : Fin 6 :=
  letters.foldl (fun state y => mul state (if y = z then 1 else 2)) 2

private theorem binaryFold_range (z : Nat) (letters : List Nat) :
    binaryFold z letters = 0 ∨ binaryFold z letters = 1 ∨
      binaryFold z letters = 2 := by
  have aux : ∀ (xs : List Nat) (current : Fin 6),
      (current = 0 ∨ current = 1 ∨ current = 2) →
      xs.foldl (fun state y => mul state (if y = z then 1 else 2)) current = 0 ∨
      xs.foldl (fun state y => mul state (if y = z then 1 else 2)) current = 1 ∨
      xs.foldl (fun state y => mul state (if y = z then 1 else 2)) current = 2 := by
    intro xs
    induction xs with
    | nil => intro current hc; simpa using hc
    | cons y ys ih =>
        intro current hc
        simp only [List.foldl_cons]
        apply ih
        rcases hc with rfl | rfl | rfl <;> by_cases h : y = z <;>
          simp [h, mul_0_1, mul_0_2', mul_1_1, mul_1_2, mul_2_1, mul_2_2']
  unfold binaryFold
  exact aux letters 2 (Or.inr (Or.inr rfl))

private theorem binaryFold_eq_two (z : Nat) (letters : List Nat) :
    binaryFold z letters = 2 ↔ letters.count z = 0 := by
  have aux : ∀ (xs : List Nat) (current : Fin 6),
      (current = 0 ∨ current = 1 ∨ current = 2) →
      (xs.foldl (fun state y => mul state (if y = z then 1 else 2)) current = 2 ↔
        current = 2 ∧ xs.count z = 0) := by
    intro xs
    induction xs with
    | nil => intro current hc; simp
    | cons y ys ih =>
        intro current hc
        simp only [List.foldl_cons, List.count_cons]
        have next_range :
            mul current (if y = z then 1 else 2) = 0 ∨
            mul current (if y = z then 1 else 2) = 1 ∨
            mul current (if y = z then 1 else 2) = 2 := by
          rcases hc with rfl | rfl | rfl <;> by_cases h : y = z <;>
            simp [h, mul_0_1, mul_0_2', mul_1_1, mul_1_2, mul_2_1, mul_2_2']
        rw [ih _ next_range]
        rcases hc with rfl | rfl | rfl <;> by_cases h : y = z <;>
          simp [h, mul_0_1, mul_0_2', mul_1_1, mul_1_2, mul_2_1, mul_2_2']
  unfold binaryFold
  simpa using aux letters 2 (Or.inr (Or.inr rfl))

private theorem toList_split_last (word : Word Nat) :
    ∃ p, word.toList = p ++ [lastLetter word] := by
  rcases word with ⟨head, tail⟩
  induction tail generalizing head with
  | nil => exact ⟨[], rfl⟩
  | cons y ys ih =>
      obtain ⟨p, hp⟩ := ih y
      exact ⟨head :: p, by
        change head :: y :: ys = head :: (p ++ [lastLetter ⟨head, y :: ys⟩])
        rw [show lastLetter ⟨head, y :: ys⟩ = lastLetter ⟨y, ys⟩ by rfl]
        exact congrArg (List.cons head) hp⟩

private theorem eval_as_binaryFold (word : Word Nat) (z : Nat) :
    table.semigroup.eval (fun y => if y = z then (1 : Fin 6) else (2 : Fin 6)) word =
      binaryFold z word.toList := by
  unfold Semigroup.eval binaryFold Word.toList
  change List.foldl (fun acc x => mul acc (if x = z then 1 else 2))
      (if word.head = z then 1 else 2) word.tail = _
  simp only [List.foldl_cons]
  by_cases h : word.head = z
  · simp [h, mul_2_1]
  · simp [h, mul_2_2']

private theorem eval_unique_final_detector (word : Word Nat) :
    table.semigroup.eval
      (fun y => if y = lastLetter word then (1 : Fin 6) else (2 : Fin 6)) word = (1 : Fin 6) ↔
      word.toList.count (lastLetter word) = 1 := by
  obtain ⟨p, hp⟩ := toList_split_last word
  rw [eval_as_binaryFold]
  have hfold : binaryFold (lastLetter word) word.toList =
      mul (binaryFold (lastLetter word) p) 1 := by
    rw [hp]
    simp [binaryFold, List.foldl_append]
  rw [hfold]
  have hrange := binaryFold_range (lastLetter word) p
  have htwo := binaryFold_eq_two (lastLetter word) p
  rw [hp]
  simp [List.count_append]
  rcases hrange with hzero | hone | htwoValue
  · have hcount : p.count (lastLetter word) ≠ 0 := by
      intro hc
      have : binaryFold (lastLetter word) p = 2 := htwo.mpr hc
      rw [hzero] at this
      cases this
    rw [hzero]
    simp [mul_0_1, hcount]
  · have hcount : p.count (lastLetter word) ≠ 0 := by
      intro hc
      have : binaryFold (lastLetter word) p = 2 := htwo.mpr hc
      rw [hone] at this
      cases this
    rw [hone]
    simp [mul_1_1, hcount]
  · have hcount : p.count (lastLetter word) = 0 := htwo.mp htwoValue
    rw [htwoValue]
    simp [mul_2_1, hcount]

private def finalState (word : Word Nat) :=
  let n := word.toList.count (lastLetter word)
  if n = 1 then 1 else (n - 2) % 3 + 2

private def prefixState (word : Word Nat) (x : Nat) : Nat :=
  if x = lastLetter word then 0
  else positiveResidue (word.toList.count x)

private theorem semantic_invariant {left right : Word Nat}
    (valid : ∀ valuation : Nat → Fin 6,
      table.semigroup.eval valuation left = table.semigroup.eval valuation right) :
    lastLetter left = lastLetter right ∧
      finalState left = finalState right ∧
      ∀ x, prefixState left x = prefixState right x := by
  have h_last_eq : lastLetter left = lastLetter right := by
    have hr : table.semigroup.eval
        (fun y => if y = lastLetter right then (3 : Fin 6) else (2 : Fin 6))
        right = (3 : Fin 6) :=
      (eval_last_detector right (lastLetter right)).mpr rfl
    have he := valid
      (fun y => if y = lastLetter right then (3 : Fin 6) else (2 : Fin 6))
    have hl : table.semigroup.eval
        (fun y => if y = lastLetter right then (3 : Fin 6) else (2 : Fin 6))
        left = (3 : Fin 6) := he.trans hr
    exact (eval_last_detector left (lastLetter right)).mp hl
  -- For residues: for each x, valid at x↦4 else2, rewrite both using eval_cycle, apply cycleValue_injective.
  have h_residues : ∀ x, positiveResidue (left.toList.count x) = positiveResidue (right.toList.count x) := by
    intro x
    have := valid (fun y => if y = x then (4 : Fin 6) else (2 : Fin 6))
    rw [eval_cycle, eval_cycle] at this
    exact cycleValue_injective this;
  -- By valid for unique final detector, eval lastLetter left = 1 ↔ lastLetter right = 1.
  have h_final_count : left.toList.count (lastLetter left) = 1 ↔ right.toList.count (lastLetter right) = 1 := by
    have h_unique_final_detector : table.semigroup.eval (fun y => if y = lastLetter left then (1 : Fin 6) else (2 : Fin 6)) left = (1 : Fin 6) ↔ table.semigroup.eval (fun y => if y = lastLetter right then (1 : Fin 6) else (2 : Fin 6)) right = (1 : Fin 6) := by
      rw [ h_last_eq, valid ];
    exact (eval_unique_final_detector left).symm.trans
      (h_unique_final_detector.trans (eval_unique_final_detector right))
  refine ⟨h_last_eq, ?_, ?_⟩
  · unfold finalState
    rw [h_last_eq]
    have hr := h_residues (lastLetter right)
    unfold positiveResidue at hr
    by_cases hl : left.toList.count (lastLetter right) = 1
    · have hh : right.toList.count (lastLetter right) = 1 :=
        h_final_count.mp (by simpa [h_last_eq] using hl)
      simp [hl, hh]
    · have hh : right.toList.count (lastLetter right) ≠ 1 := by
        intro h
        apply hl
        have := h_final_count.mpr h
        simpa [h_last_eq] using this
      have hl0 : left.toList.count (lastLetter right) ≠ 0 := by
        obtain ⟨p, hp⟩ := toList_split_last left
        rw [h_last_eq] at hp
        rw [hp]
        simp [List.count_append]
      have hr0 : right.toList.count (lastLetter right) ≠ 0 := by
        obtain ⟨p, hp⟩ := toList_split_last right
        rw [hp]
        simp [List.count_append]
      simp [hl, hh, hl0, hr0] at hr ⊢
      omega
  · intro x
    unfold prefixState
    rw [h_last_eq]
    by_cases hx : x = lastLetter right
    · simp [hx]
    · simp [hx, h_residues x]

private def variableBound (word : Word Nat) : Nat :=
  word.toList.foldl Nat.max 0 + 1

private def canonicalPrefix (word : Word Nat) : List Nat :=
  (List.range (variableBound word)).flatMap fun x =>
    List.replicate (prefixState word x) x

private def canonicalList (word : Word Nat) : List Nat :=
  canonicalPrefix word ++ List.replicate (finalState word) (lastLetter word)

private def canonicalWord (word : Word Nat) : Word Nat :=
  ⟨(canonicalList word).headD (lastLetter word), (canonicalList word).tail⟩

private theorem variable_lt_bound (word : Word Nat) (x : Nat)
    (hx : x ∈ word.toList) : x < variableBound word := by
  have aux : ∀ (xs : List Nat) (acc x : Nat),
      x ≤ acc ∨ x ∈ xs → x ≤ xs.foldl Nat.max acc := by
    intro xs
    induction xs with
    | nil => intro acc x h; simpa using h
    | cons y ys ih =>
        intro acc x h
        simp only [List.foldl_cons]
        apply ih
        rcases h with h | h
        · exact Or.inl (Nat.le_trans h (Nat.le_max_left _ _))
        · simp only [List.mem_cons] at h
          rcases h with rfl | h
          · exact Or.inl (Nat.le_max_right _ _)
          · exact Or.inr h
  unfold variableBound
  exact Nat.lt_succ_of_le (aux word.toList 0 x (Or.inr hx))

private theorem finalState_positive (word : Word Nat) : 0 < finalState word := by
  unfold finalState;
  grind

private theorem canonicalList_nonempty (word : Word Nat) :
    canonicalList word ≠ [] := by
  intro h
  have hlen := congrArg List.length h
  unfold canonicalList at hlen
  simp only [List.length_append, List.length_replicate, List.length_nil] at hlen
  have hz : finalState word = 0 := by omega
  exact (Nat.ne_of_gt (finalState_positive word)) hz

private theorem canonicalWord_toList (word : Word Nat) :
    (canonicalWord word).toList = canonicalList word := by
  unfold canonicalWord;
  cases h : canonicalList word <;> simp_all +decide [ Word.toList ];
  exact absurd h ( canonicalList_nonempty word )

private theorem fold_max_le_of_all_le (xs : List Nat) (bound : Nat)
    (h : ∀ x ∈ xs, x ≤ bound) : xs.foldl Nat.max 0 ≤ bound := by
  have aux : ∀ (ys : List Nat) (acc : Nat), acc ≤ bound →
      (∀ x ∈ ys, x ≤ bound) → ys.foldl Nat.max acc ≤ bound := by
    intro ys
    induction ys with
    | nil => intro acc ha hy; exact ha
    | cons y rest ih =>
        intro acc ha hy
        simp only [List.foldl_cons]
        apply ih
        · exact Nat.max_le.mpr ⟨ha, hy y (by simp)⟩
        · intro x hx
          exact hy x (by simp [hx])
  exact aux xs 0 (Nat.zero_le _) h

private theorem positiveResidue_eq_zero (n : Nat) :
    positiveResidue n = 0 ↔ n = 0 := by
  unfold positiveResidue
  by_cases h : n = 0
  · simp [h]
  · simp [h]

private theorem support_iff {left right : Word Nat}
    (last_eq : lastLetter left = lastLetter right)
    (prefix_eq : ∀ x, prefixState left x = prefixState right x) (x : Nat) :
    x ∈ left.toList ↔ x ∈ right.toList := by
  by_cases hx : x = lastLetter left
  · subst x
    constructor
    · intro _
      obtain ⟨p, hp⟩ := toList_split_last right
      rw [last_eq]
      rw [hp]
      simp
    · intro _
      obtain ⟨p, hp⟩ := toList_split_last left
      rw [hp]
      simp
  · have hxr : x ≠ lastLetter right := by simpa [← last_eq] using hx
    have he := prefix_eq x
    unfold prefixState at he
    simp [hx, hxr] at he
    rw [← List.count_pos_iff, ← List.count_pos_iff]
    have hz : left.toList.count x = 0 ↔ right.toList.count x = 0 := by
      rw [← positiveResidue_eq_zero, he, positiveResidue_eq_zero]
    omega

private theorem variableBound_eq {left right : Word Nat}
    (last_eq : lastLetter left = lastLetter right)
    (prefix_eq : ∀ x, prefixState left x = prefixState right x) :
    variableBound left = variableBound right := by
  unfold variableBound
  congr 1
  apply Nat.le_antisymm
  · apply fold_max_le_of_all_le
    intro x hx
    have hx' := (support_iff last_eq prefix_eq x).mp hx
    exact Nat.le_of_lt_succ (variable_lt_bound right x hx')
  · apply fold_max_le_of_all_le
    intro x hx
    have hx' := (support_iff last_eq prefix_eq x).mpr hx
    exact Nat.le_of_lt_succ (variable_lt_bound left x hx')

private theorem canonicalWord_eq {left right : Word Nat}
    (last_eq : lastLetter left = lastLetter right)
    (final_eq : finalState left = finalState right)
    (prefix_eq : ∀ x, prefixState left x = prefixState right x) :
    canonicalWord left = canonicalWord right := by
  apply Word.toList_injective
  rw [canonicalWord_toList, canonicalWord_toList]
  unfold canonicalList canonicalPrefix
  rw [variableBound_eq last_eq prefix_eq]
  simp [last_eq, final_eq, prefix_eq]

private def prefixWords (letters : List Nat) (suffix : Word Nat) : Word Nat :=
  letters.foldr (fun x rest => Word.singleton x ++ rest) suffix

private theorem prefixWords_toList (letters : List Nat) (suffix : Word Nat) :
    (prefixWords letters suffix).toList = letters ++ suffix.toList := by
  unfold prefixWords;
  induction letters <;> simp_all +decide [ Word.toList ]

private theorem derives_prefixSwap (a b : Nat) (suffix : Word Nat) :
    Derives basis (prefixWords [a, b] suffix) (prefixWords [b, a] suffix) := by
  let σ : Nat → Word Nat := fun i =>
    if i = 0 then Word.singleton a else if i = 1 then Word.singleton b else suffix
  have h : Derives basis (prefixSwapLaw.lhs.bind σ) (prefixSwapLaw.rhs.bind σ) :=
    Derives.subst (Derives.fromBasis (by simp [basis])) σ
  change Derives basis (prefixWords [a, b] suffix)
    (prefixWords [b, a] suffix) at h
  exact h

private theorem derives_gather (x : Nat) (middle : Word Nat) :
    Derives basis
      (Word.singleton x ++ middle ++ Word.singleton x)
      (middle ++ Word.singleton x ++ Word.singleton x) := by
  let σ : Nat → Word Nat := fun i => if i = 0 then Word.singleton x else middle
  have h : Derives basis (gatherLaw.lhs.bind σ) (gatherLaw.rhs.bind σ) :=
    Derives.subst (Derives.fromBasis (by simp [basis])) σ
  change Derives basis
    (Word.singleton x ++ middle ++ Word.singleton x)
    (middle ++ Word.singleton x ++ Word.singleton x) at h
  exact h

private theorem derives_tailPeriod (x : Nat) (suffix : Word Nat) :
    Derives basis (prefixWords [x, x, x, x] suffix)
      (Word.singleton x ++ suffix) := by
  let σ : Nat → Word Nat := fun i => if i = 0 then Word.singleton x else suffix
  have h : Derives basis (tailPeriodLaw.lhs.bind σ) (tailPeriodLaw.rhs.bind σ) :=
    Derives.subst (Derives.fromBasis (by simp [basis])) σ
  change Derives basis (prefixWords [x, x, x, x] suffix)
    (Word.singleton x ++ suffix) at h
  exact h

private theorem derives_power (x : Nat) :
    Derives basis (prefixWords [x, x] (Word.singleton x))
      (prefixWords [x, x, x, x, x] (Word.singleton x)) := by
  exact Derives.symm (derives_tailPeriod x
    (prefixWords [x] (Word.singleton x)))

private theorem derives_perm_prefix {as bs : List Nat} (suffix : Word Nat)
    (hperm : as.Perm bs) :
    Derives basis (prefixWords as suffix) (prefixWords bs suffix) := by
  induction hperm with
  | nil => exact Derives.refl _
  | cons x hperm ih =>
      exact Derives.prepend (Word.singleton x) ih
  | swap x y l =>
      exact derives_prefixSwap y x (prefixWords l suffix)
  | trans h₁ h₂ ih₁ ih₂ =>
      exact Derives.trans ih₁ ih₂

private def repeatPrefix (n x : Nat) (suffix : Word Nat) : Word Nat :=
  prefixWords (List.replicate n x) suffix

private theorem derives_tail_reduce (n x : Nat) (suffix : Word Nat) :
    Derives basis (repeatPrefix n x suffix)
      (repeatPrefix (positiveResidue n) x suffix) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      rcases n with _ | _ | _ | _ | k
      · exact Derives.refl _
      · exact Derives.refl _
      · exact Derives.refl _
      · exact Derives.refl _
      · have hstep : Derives basis
            (repeatPrefix (k + 4) x suffix)
            (repeatPrefix (k + 1) x suffix) := by
          exact derives_tailPeriod x (repeatPrefix k x suffix)
        have hrest := ih (k + 1) (by omega)
        have hres : positiveResidue (k + 1) = positiveResidue (k + 4) := by
          unfold positiveResidue
          simp only [Nat.add_eq_zero_iff, Nat.reduceEqDiff, and_false, ↓reduceIte]
          omega
        exact Derives.trans hstep (hres ▸ hrest)

private theorem derives_final_reduce (n x : Nat) (hn : 0 < n) :
    Derives basis (repeatPrefix (n - 1) x (Word.singleton x))
      (repeatPrefix (if n = 1 then 0 else (n - 2) % 3 + 1)
        x (Word.singleton x)) := by
  have heq : positiveResidue (n - 1) =
      (if n = 1 then 0 else (n - 2) % 3 + 1) := by
    unfold positiveResidue
    rcases n with _ | n
    · omega
    · rcases n with _ | n
      · simp
      · simp
  rw [← heq]
  exact derives_tail_reduce (n - 1) x (Word.singleton x)

private def sortedPrefixCounts (word : Word Nat) : List Nat :=
  (List.range (variableBound word)).flatMap fun x =>
    List.replicate (word.toList.count x - if x = lastLetter word then 1 else 0) x

private theorem count_sortedPrefixCounts (word : Word Nat) (y : Nat) :
    (sortedPrefixCounts word).count y =
      if y < variableBound word then
        word.toList.count y - if y = lastLetter word then 1 else 0
      else 0 := by
  unfold sortedPrefixCounts
  have aux : ∀ b : Nat,
      ((List.range b).flatMap fun x =>
        List.replicate (word.toList.count x - if x = lastLetter word then 1 else 0) x).count y =
      if y < b then word.toList.count y - if y = lastLetter word then 1 else 0 else 0 := by
    intro b
    induction b with
    | zero => simp
    | succ b ih =>
        rw [List.range_succ, List.flatMap_append, List.count_append, ih]
        simp
        by_cases hy : y = b
        · subst y
          simp
        · have hby : b ≠ y := fun h => hy h.symm
          have hcount : List.count y
              (List.replicate (word.toList.count b -
                if b = lastLetter word then 1 else 0) b) = 0 := by
            rw [List.count_replicate]
            have hbeq : (b == y) = false := by simp [hby]
            simp [hbeq]
          by_cases hlt : y < b
          · have hlt' : y < b + 1 := Nat.lt_trans hlt (Nat.lt_succ_self b)
            simp [hlt, hlt', hcount]
          · have hge : b ≤ y := Nat.le_of_not_gt hlt
            have hnot : ¬ y < b + 1 := by omega
            simp [hlt, hnot, hcount]
  exact aux (variableBound word)

private theorem sortedPrefixCounts_perm (word : Word Nat) (p : List Nat)
    (hp : word.toList = p ++ [lastLetter word]) :
    p.Perm (sortedPrefixCounts word) := by
  rw [List.perm_iff_count]
  intro x
  rw [count_sortedPrefixCounts]
  have hc : word.toList.count x = p.count x +
      (if x = lastLetter word then 1 else 0) := by
    rw [hp, List.count_append]
    by_cases h : x = lastLetter word
    · simp [h]
    · have h' : lastLetter word ≠ x := fun e => h e.symm
      simp [h, h']
  by_cases hx : x < variableBound word
  · simp [hx, hc]
  · have hz : word.toList.count x = 0 := by
      apply List.count_eq_zero_of_not_mem
      intro hm
      exact (Nat.not_lt_of_ge (Nat.le_of_not_gt hx)) (variable_lt_bound word x hm)
    simp [hx]
    omega

private def rawBlock (word : Word Nat) (x : Nat) : List Nat :=
  List.replicate (word.toList.count x - if x = lastLetter word then 1 else 0) x

private def reducedBlock (word : Word Nat) (x : Nat) : List Nat :=
  if x = lastLetter word then []
  else List.replicate (positiveResidue (word.toList.count x)) x

private theorem sortedPrefixCounts_eq (word : Word Nat) :
    sortedPrefixCounts word =
      (List.range (variableBound word)).flatMap (rawBlock word) := by
  rfl

private theorem canonicalPrefix_eq (word : Word Nat) :
    canonicalPrefix word =
      (List.range (variableBound word)).flatMap (reducedBlock word) := by
  unfold canonicalPrefix reducedBlock prefixState;
  grind

private def nonFinalVariables (word : Word Nat) : List Nat :=
  (List.range (variableBound word)).filter fun x => x != lastLetter word

private def rawNonFinal (word : Word Nat) : List Nat :=
  (nonFinalVariables word).flatMap (rawBlock word)

private def reducedNonFinal (word : Word Nat) : List Nat :=
  (nonFinalVariables word).flatMap (reducedBlock word)

private theorem sorted_to_nonFinal_perm (word : Word Nat) :
    (sortedPrefixCounts word).Perm
      (rawNonFinal word ++
        List.replicate (word.toList.count (lastLetter word) - 1)
          (lastLetter word)) := by
  have hzmem : lastLetter word ∈ List.range (variableBound word) := by
    rw [List.mem_range]
    apply variable_lt_bound
    obtain ⟨p, hp⟩ := toList_split_last word
    rw [hp]
    simp
  have hperm : (List.range (variableBound word)).Perm
      ((List.range (variableBound word)).filter
        (fun x => x != lastLetter word) ++ [lastLetter word]) := by
    rw [List.perm_iff_count]
    intro a
    by_cases ha : a = lastLetter word
    · subst a
      have hzfilter : List.count (lastLetter word)
          ((List.range (variableBound word)).filter
            (fun x => x != lastLetter word)) = 0 := by
        apply List.count_eq_zero_of_not_mem
        simp
      rw [List.count_append, hzfilter]
      have hzlt : lastLetter word < variableBound word := List.mem_range.mp hzmem
      simp [hzlt]
    · have hza : lastLetter word ≠ a := fun h => ha h.symm
      simp [ha, hza]
  have hflat := hperm.flatMap_right (rawBlock word)
  rw [sortedPrefixCounts_eq]
  unfold rawNonFinal nonFinalVariables
  simpa [rawBlock] using hflat

private theorem canonicalPrefix_nonFinal (word : Word Nat) :
    canonicalPrefix word = reducedNonFinal word := by
  rw [canonicalPrefix_eq]
  unfold reducedNonFinal nonFinalVariables
  generalize List.range (variableBound word) = xs
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      simp only [List.flatMap_cons, List.filter_cons]
      by_cases h : x = lastLetter word
      · subst x
        simp [reducedBlock, ih]
      · have hb : (x != lastLetter word) = true := by simp [h]
        simp [hb, ih]

private theorem prefixWords_append (as bs : List Nat) (suffix : Word Nat) :
    prefixWords (as ++ bs) suffix = prefixWords as (prefixWords bs suffix) := by
  apply Word.toList_injective
  rw [prefixWords_toList, prefixWords_toList, prefixWords_toList]
  simp [List.append_assoc]

private theorem derives_prependWords (xs : List Nat) {u v : Word Nat}
    (h : Derives basis u v) :
    Derives basis (prefixWords xs u) (prefixWords xs v) := by
  induction xs with
  | nil => exact h
  | cons x rest ih => exact Derives.prepend (Word.singleton x) ih

private theorem derives_reduce_nonFinal (word : Word Nat) (xs : List Nat)
    (hxs : ∀ x ∈ xs, x ≠ lastLetter word) (suffix : Word Nat) :
    Derives basis
      (prefixWords (xs.flatMap (rawBlock word)) suffix)
      (prefixWords (xs.flatMap (reducedBlock word)) suffix) := by
  induction xs generalizing suffix;
  · constructor;
  · rename_i k l ih;
    unfold rawBlock reducedBlock at *; simp_all +decide [ List.flatMap ] ;
    rw [ prefixWords_append, prefixWords_append ];
    exact Derives.trans ( derives_tail_reduce _ _ _ ) ( derives_prependWords _ ( ih _ ) )

private theorem final_count_positive (word : Word Nat) :
    0 < word.toList.count (lastLetter word) := by
  rw [List.count_pos_iff]
  obtain ⟨p, hp⟩ := toList_split_last word
  rw [hp]
  simp

private theorem final_target_eq_canonical (word : Word Nat) :
    prefixWords (reducedNonFinal word)
      (repeatPrefix
        (if word.toList.count (lastLetter word) = 1 then 0
          else (word.toList.count (lastLetter word) - 2) % 3 + 1)
        (lastLetter word) (Word.singleton (lastLetter word))) =
      canonicalWord word := by
  apply Word.toList_injective
  rw [canonicalWord_toList, prefixWords_toList]
  unfold repeatPrefix
  rw [prefixWords_toList]
  unfold canonicalList finalState
  rw [canonicalPrefix_nonFinal]
  by_cases h : word.toList.count (lastLetter word) = 1
  · simp [h]
  · rw [if_neg h, if_neg h]
    rw [show (word.toList.count (lastLetter word) - 2) % 3 + 2 =
        ((word.toList.count (lastLetter word) - 2) % 3 + 1) + 1 by omega]
    rw [List.replicate_succ]
    rw [List.replicate_succ]
    have happ : ∀ k : Nat,
        List.replicate k (lastLetter word) ++ [lastLetter word] =
          List.replicate (k + 1) (lastLetter word) := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
          simp only [List.replicate_succ]
          exact congrArg (List.cons (lastLetter word)) ih
    change reducedNonFinal word ++
      (lastLetter word :: (List.replicate
        ((word.toList.count (lastLetter word) - 2) % 3) (lastLetter word) ++
        [lastLetter word])) = _
    rw [happ]

private theorem derives_reduce_sorted (word : Word Nat) :
    Derives basis
      (prefixWords (sortedPrefixCounts word) (Word.singleton (lastLetter word)))
      (canonicalWord word) := by
  let z := lastLetter word
  let n := word.toList.count z
  let finalSuffix := repeatPrefix (n - 1) z (Word.singleton z)
  have hperm : (sortedPrefixCounts word).Perm
      (rawNonFinal word ++ List.replicate (n - 1) z) := by
    exact sorted_to_nonFinal_perm word
  have hstart : Derives basis
      (prefixWords (sortedPrefixCounts word) (Word.singleton z))
      (prefixWords (rawNonFinal word) finalSuffix) := by
    have h := derives_perm_prefix (Word.singleton z) hperm
    rw [prefixWords_append] at h
    exact h
  have hnonfinal : ∀ x ∈ nonFinalVariables word, x ≠ z := by
    intro x hx
    unfold nonFinalVariables at hx
    simp only [List.mem_filter] at hx
    intro h
    have hb : (x != lastLetter word) = false := by simp [z, h]
    rw [hb] at hx
    cases hx.2
  have hreduce : Derives basis
      (prefixWords (rawNonFinal word) finalSuffix)
      (prefixWords (reducedNonFinal word) finalSuffix) :=
    derives_reduce_nonFinal word (nonFinalVariables word) hnonfinal finalSuffix
  have hfinal0 := derives_final_reduce n z (by
    unfold n z
    exact final_count_positive word)
  have hfinal : Derives basis
      (prefixWords (reducedNonFinal word) finalSuffix)
      (prefixWords (reducedNonFinal word)
        (repeatPrefix (if n = 1 then 0 else (n - 2) % 3 + 1)
          z (Word.singleton z))) :=
    derives_prependWords (reducedNonFinal word) hfinal0
  have hend : prefixWords (reducedNonFinal word)
        (repeatPrefix (if n = 1 then 0 else (n - 2) % 3 + 1)
          z (Word.singleton z)) = canonicalWord word := by
    exact final_target_eq_canonical word
  exact Derives.trans hstart (Derives.trans hreduce (hend ▸ hfinal))

private theorem derives_canonical (word : Word Nat) :
    Derives basis word (canonicalWord word) := by
  obtain ⟨p, hp⟩ := toList_split_last word
  have hword : word = prefixWords p (Word.singleton (lastLetter word)) := by
    apply Word.toList_injective
    rw [prefixWords_toList]
    simpa using hp
  have hpder : Derives basis
      (prefixWords p (Word.singleton (lastLetter word)))
      (prefixWords (sortedPrefixCounts word) (Word.singleton (lastLetter word))) :=
    derives_perm_prefix _ (sortedPrefixCounts_perm word p hp)
  have h₁ : Derives basis word
      (prefixWords (sortedPrefixCounts word) (Word.singleton (lastLetter word))) := by
    exact Derives.trans (hword ▸ Derives.refl word) hpder
  exact Derives.trans h₁ (derives_reduce_sorted word)

private theorem invariant_derives {left right : Word Nat}
    (last_eq : lastLetter left = lastLetter right)
    (final_eq : finalState left = finalState right)
    (prefix_eq : ∀ x,
      prefixState left x = prefixState right x) :
    Derives basis left right := by
  exact Derives.trans (derives_canonical left)
    (Derives.trans (Derives.refl _ |> fun h => canonicalWord_eq last_eq final_eq prefix_eq ▸ h)
      (Derives.symm (derives_canonical right)))

theorem basis_complete_aristotle : BasisFor table.semigroup basis := by
  refine ⟨basis_models, ?_⟩
  intro identity valid
  obtain ⟨last_eq, final_eq, prefix_eq⟩ := semantic_invariant valid
  exact invariant_derives last_eq final_eq prefix_eq

end Order6S6_14934FinalSortedPeriod3

end CoRoots

end SemigroupBasis
