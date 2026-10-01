import SemigroupBasis.CoRoots.S6_8496Published

/-!
# S6_8496 separator-indexed probe kernel (msg-0077 contract, msg-0252 lane)

EVIDENCE LABEL: source-staged, NOT compiled here (no pinned toolchain on
the authoring side).  Every finite multiplication fact is a `decide` on
`S6_8496.mul`; the architecture is the msg-0077
`prefixCollapse` / `gapDetect` / `suffixFreeze` split in the compiling
`evalSecondProbeGeneric` style.

DESIGN NOTE (the eval bridge): all five endpoints are stated as
`probeFold v fullList 4`.  Since 4 is the two-sided identity
(`identityElement_certificate`), `mul 4 (v head) = v head`, so
`probeFold v (head :: tail) 4 = probeFold v tail (v head)` — i.e. the
fold-from-4 over the FULL word list IS `table.semigroup.eval v word`
after one rewrite.  This removes all head/tail plumbing from the kernel;
the alignment layer bridges with a single lemma.

Zero-based table roles: 0 zero, 1 armed, 2 hit, 3 and 5 idempotent
detectors, 4 identity.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6PublishedMonoid14.S6_8496

open SemigroupBasis

/-- Left fold of the probe valuation across a letter list. -/
def probeFold (valuation : Nat → Fin 6) (letters : List Nat)
    (state : Fin 6) : Fin 6 :=
  letters.foldl (fun current letter => mul current (valuation letter)) state

@[simp] theorem probeFold_nil (valuation : Nat → Fin 6) (state : Fin 6) :
    probeFold valuation [] state = state := rfl

@[simp] theorem probeFold_cons
    (valuation : Nat → Fin 6) (letter : Nat) (rest : List Nat)
    (state : Fin 6) :
    probeFold valuation (letter :: rest) state =
      probeFold valuation rest (mul state (valuation letter)) := rfl

theorem probeFold_append
    (valuation : Nat → Fin 6) (left right : List Nat) (state : Fin 6) :
    probeFold valuation (left ++ right) state =
      probeFold valuation right (probeFold valuation left state) := by
  simp [probeFold, List.foldl_append]

/-! ## Probe valuations (msg-0077 closed forms) -/

def interiorSupportProbe (previous current tested : Nat) : Nat → Fin 6 :=
  fun letter =>
    if letter = previous then 1 else
      if letter = current then 3 else
        if letter = tested then 5 else 4

def initialSupportProbe (current tested : Nat) : Nat → Fin 6 :=
  fun letter =>
    if letter = current then 3 else
      if letter = tested then 5 else 4

def finalSupportProbe (previous tested : Nat) : Nat → Fin 6 :=
  fun letter =>
    if letter = previous then 1 else
      if letter = tested then 5 else 4

def orderProbe (previous c d : Nat) : Nat → Fin 6 :=
  fun letter =>
    if letter = previous then 1 else
      if letter = c then 5 else
        if letter = d then 3 else 4

def initialOrderProbe (c d : Nat) : Nat → Fin 6 :=
  fun letter =>
    if letter = c then 5 else
      if letter = d then 3 else 4

/-! ## Stage 1: prefixCollapse -/

/-- States that survive an un-armed prefix. -/
def HighState (state : Fin 6) : Prop :=
  state = 3 ∨ state = 4 ∨ state = 5

private theorem mul_high_high {state value : Fin 6}
    (hs : HighState state) (hv : HighState value) :
    HighState (mul state value) := by
  rcases hs with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
    first
      | exact Or.inl (by decide)
      | exact Or.inr (Or.inl (by decide))
      | exact Or.inr (Or.inr (by decide))

theorem foldStaysHigh (valuation : Nat → Fin 6) :
    ∀ (letters : List Nat) (state : Fin 6),
      (∀ letter ∈ letters, HighState (valuation letter)) →
      HighState state →
      HighState (probeFold valuation letters state)
  | [], _, _, hs => hs
  | letter :: rest, state, hall, hs => by
      rw [probeFold_cons]
      exact foldStaysHigh valuation rest _
        (fun x hx => hall x (List.mem_cons_of_mem _ hx))
        (mul_high_high hs (hall letter (List.mem_cons_self ..)))

/-- Arming: every surviving prefix state collapses to 1. -/
theorem armAfterHigh {state : Fin 6} (hs : HighState state) :
    mul state 1 = 1 := by
  rcases hs with rfl | rfl | rfl <;> decide

/-! ## Stage 2: gapDetect (armed) -/

theorem freezeTwo (valuation : Nat → Fin 6) :
    ∀ letters : List Nat,
      (∀ letter ∈ letters, HighState (valuation letter)) →
      probeFold valuation letters 2 = 2
  | [], _ => rfl
  | letter :: rest, hall => by
      have step : mul 2 (valuation letter) = 2 := by
        rcases hall letter (List.mem_cons_self ..) with h | h | h <;>
          rw [h] <;> decide
      rw [probeFold_cons, step]
      exact freezeTwo valuation rest
        (fun x hx => hall x (List.mem_cons_of_mem _ hx))

private theorem zero_mul (value : Fin 6) : mul 0 value = 0 := by
  revert value
  decide

theorem freezeZero (valuation : Nat → Fin 6) :
    ∀ letters : List Nat, probeFold valuation letters 0 = 0
  | [] => rfl
  | letter :: rest => by
      rw [probeFold_cons, zero_mul]
      exact freezeZero valuation rest

/-- Armed support detection over `{4,5}`-valued letters. -/
theorem gapDetectSupport (valuation : Nat → Fin 6) :
    ∀ letters : List Nat,
      (∀ letter ∈ letters, valuation letter = 4 ∨ valuation letter = 5) →
      probeFold valuation letters 1 =
        (if ∃ letter ∈ letters, valuation letter = 5 then 2 else 1)
  | [], _ => by simp
  | letter :: rest, hall => by
      have hrest := fun x hx => hall x (List.mem_cons_of_mem _ hx)
      rcases hall letter (List.mem_cons_self ..) with h4 | h5
      · rw [probeFold_cons, h4, show mul 1 4 = 1 by decide,
          gapDetectSupport valuation rest hrest]
        have head_not5 : ¬ valuation letter = 5 := by simp [h4]
        by_cases hex : ∃ x ∈ rest, valuation x = 5 <;>
          simp [hex, head_not5]
      · have high : ∀ x ∈ rest, HighState (valuation x) := fun x hx =>
          (hrest x hx).elim (fun h => Or.inr (Or.inl h))
            (fun h => Or.inr (Or.inr h))
        rw [probeFold_cons, h5, show mul 1 5 = 2 by decide,
          freezeTwo valuation rest high]
        simp [h5]

/-- Armed order detection over `{3,4,5}`-valued letters: the first
non-4 value decides (5 lands on 2, 3 lands on 0); no event keeps 1. -/
theorem gapDetectOrder (valuation : Nat → Fin 6) :
    ∀ letters : List Nat,
      (∀ letter ∈ letters, HighState (valuation letter)) →
      probeFold valuation letters 1 =
        (match letters.find? (fun x => valuation x ≠ 4) with
          | none => 1
          | some x => if valuation x = 5 then 2 else 0)
  | [], _ => by simp
  | letter :: rest, hall => by
      have hrest := fun x hx => hall x (List.mem_cons_of_mem _ hx)
      rcases hall letter (List.mem_cons_self ..) with h3 | h4 | h5
      · rw [probeFold_cons, h3, show mul 1 3 = 0 by decide,
          freezeZero]
        rw [List.find?_cons_of_pos (by simp [h3])]
        simp [h3]
      · rw [probeFold_cons, h4, show mul 1 4 = 1 by decide,
          gapDetectOrder valuation rest hrest,
          List.find?_cons_of_neg (by simp [h4])]
      · rw [probeFold_cons, h5, show mul 1 5 = 2 by decide,
          freezeTwo valuation rest hrest,
          List.find?_cons_of_pos (by simp [h5])]
        simp [h5]

/-! ## Stage 2': un-armed (initial-gap) detection -/

theorem initialDetectSupport (valuation : Nat → Fin 6) :
    ∀ (letters : List Nat) (state : Fin 6),
      (state = 4 ∨ state = 5) →
      (∀ letter ∈ letters, valuation letter = 4 ∨ valuation letter = 5) →
      probeFold valuation letters state =
        (if state = 5 ∨ ∃ letter ∈ letters, valuation letter = 5
          then 5 else 4)
  | [], state, hs, _ => by rcases hs with rfl | rfl <;> simp
  | letter :: rest, state, hs, hall => by
      have hrest := fun x hx => hall x (List.mem_cons_of_mem _ hx)
      rcases hall letter (List.mem_cons_self ..) with h4 | h5 <;>
        rcases hs with rfl | rfl
      · rw [probeFold_cons, h4, show mul 4 4 = 4 by decide,
          initialDetectSupport valuation rest 4 (Or.inl rfl) hrest]
        have head_not5 : ¬ valuation letter = 5 := by simp [h4]
        by_cases hex : ∃ x ∈ rest, valuation x = 5 <;>
          simp [hex, head_not5]
      · rw [probeFold_cons, h4, show mul 5 4 = 5 by decide,
          initialDetectSupport valuation rest 5 (Or.inr rfl) hrest]
        simp
      · rw [probeFold_cons, h5, show mul 4 5 = 5 by decide,
          initialDetectSupport valuation rest 5 (Or.inr rfl) hrest]
        simp [h5]
      · rw [probeFold_cons, h5, show mul 5 5 = 5 by decide,
          initialDetectSupport valuation rest 5 (Or.inr rfl) hrest]
        simp

/-! ## Stage 3: suffixFreeze -/

/-- Detector outcomes 0, 2, 3, 5 are frozen by high-valued letters. -/
theorem suffixFreeze_aux (valuation : Nat → Fin 6) :
    ∀ letters : List Nat,
      (∀ letter ∈ letters, HighState (valuation letter)) →
      ∀ state : Fin 6,
        state = 0 ∨ state = 2 ∨ state = 3 ∨ state = 5 →
        probeFold valuation letters state = state
  | [], _, _, _ => rfl
  | letter :: rest, hall, state, hstate => by
      have hv := hall letter (List.mem_cons_self ..)
      have step : mul state (valuation letter) = state := by
        rcases hstate with rfl | rfl | rfl | rfl <;>
          rcases hv with h | h | h <;> rw [h] <;> decide
      rw [probeFold_cons, step]
      exact suffixFreeze_aux valuation rest
        (fun x hx => hall x (List.mem_cons_of_mem _ hx)) state hstate

/-- Un-armed order detection from the identity state. -/
theorem initialDetectOrder (valuation : Nat → Fin 6) :
    ∀ letters : List Nat,
      (∀ letter ∈ letters, HighState (valuation letter)) →
      probeFold valuation letters 4 =
        (match letters.find? (fun x => valuation x ≠ 4) with
          | none => 4
          | some x => if valuation x = 5 then 5 else 3)
  | [], _ => by simp
  | letter :: rest, hall => by
      have hrest := fun x hx => hall x (List.mem_cons_of_mem _ hx)
      rcases hall letter (List.mem_cons_self ..) with h3 | h4 | h5
      · rw [probeFold_cons, h3, show mul 4 3 = 3 by decide,
          suffixFreeze_aux valuation rest hrest 3
            (Or.inr (Or.inr (Or.inl rfl))),
          List.find?_cons_of_pos (by simp [h3])]
        simp [h3]
      · rw [probeFold_cons, h4, show mul 4 4 = 4 by decide,
          initialDetectOrder valuation rest hrest,
          List.find?_cons_of_neg (by simp [h4])]
      · rw [probeFold_cons, h5, show mul 4 5 = 5 by decide,
          suffixFreeze_aux valuation rest hrest 5
            (Or.inr (Or.inr (Or.inr rfl))),
          List.find?_cons_of_pos (by simp [h5])]
        simp [h5]

/-! ## Valuation-class facts -/

private theorem interiorSupport_high (previous current tested : Nat)
    {x : Nat} (hx : x ≠ previous) :
    HighState (interiorSupportProbe previous current tested x) := by
  unfold interiorSupportProbe HighState
  rw [if_neg hx]
  by_cases hc : x = current
  · simp [hc]
  · rw [if_neg hc]
    by_cases ht : x = tested <;> simp [ht]

private theorem interiorSupport_gapValue
    (previous current tested : Nat) {x : Nat}
    (hxp : x ≠ previous) (hxc : x ≠ current) :
    interiorSupportProbe previous current tested x = 4 ∨
      interiorSupportProbe previous current tested x = 5 := by
  unfold interiorSupportProbe
  rw [if_neg hxp, if_neg hxc]
  by_cases ht : x = tested <;> simp [ht]

private theorem interiorSupport_five_iff
    (previous current tested : Nat) {x : Nat}
    (hxp : x ≠ previous) (hxc : x ≠ current) :
    interiorSupportProbe previous current tested x = 5 ↔ x = tested := by
  unfold interiorSupportProbe
  rw [if_neg hxp, if_neg hxc]
  by_cases ht : x = tested <;> simp [ht]

/-! ## The five endpoint lemmas (msg-0252 items 1-5)

Each is a statement about `probeFold v L 4` on the FULL split list; the
identity element makes this equal to `table.semigroup.eval v word` when
`word.toList = L` (bridge lemma for the alignment layer:
`eval_eq_probeFold_four`). -/

theorem eval_eq_probeFold_four
    (valuation : Nat → Fin 6) (head : Nat) (tail : List Nat) :
    probeFold valuation (head :: tail) 4 =
      probeFold valuation tail (valuation (head)) := by
  rw [probeFold_cons, (identityElement_certificate).1]

/-- Item 1: interior support. -/
theorem interiorSupport_eval
    (before gap after : List Nat) (previous current tested : Nat)
    (hpc : current ≠ previous) (hpt : tested ≠ previous)
    (hct : tested ≠ current)
    (hbefore : ∀ x ∈ before, x ≠ previous)
    (hgapP : ∀ x ∈ gap, x ≠ previous) (hgapC : ∀ x ∈ gap, x ≠ current)
    (hafterP : ∀ x ∈ after, x ≠ previous) :
    probeFold (interiorSupportProbe previous current tested)
        (before ++ previous :: gap ++ current :: after) 4 =
      (if tested ∈ gap then 2 else 0) := by
  have hprefix : HighState (probeFold (interiorSupportProbe previous current tested) before 4) :=
    foldStaysHigh (interiorSupportProbe previous current tested) before 4
      (fun x hx => interiorSupport_high previous current tested
        (hbefore x hx))
      (Or.inr (Or.inl rfl))
  have hvp : (interiorSupportProbe previous current tested) previous = 1 := by simp [interiorSupportProbe]
  have hvc : (interiorSupportProbe previous current tested) current = 3 := by
    simp [interiorSupportProbe, hpc]
  have hgapVal := fun x hx =>
    interiorSupport_gapValue previous current tested
      (hgapP x hx) (hgapC x hx)
  have hdetect := gapDetectSupport (interiorSupportProbe previous current tested) gap hgapVal
  have hcond :
      (∃ x ∈ gap, (interiorSupportProbe previous current tested) x = 5) ↔ tested ∈ gap := by
    constructor
    · rintro ⟨x, hx, h5⟩
      have := (interiorSupport_five_iff previous current tested
        (hgapP x hx) (hgapC x hx)).mp h5
      exact this ▸ hx
    · intro ht
      exact ⟨tested, ht,
        (interiorSupport_five_iff previous current tested hpt hct).mpr rfl⟩
  rw [probeFold_append, probeFold_append, probeFold_cons,
    probeFold_cons, hvp, armAfterHigh hprefix, hdetect, hvc]
  by_cases hmem : tested ∈ gap
  · rw [if_pos (hcond.mpr hmem), show mul 2 3 = 2 by decide,
      suffixFreeze_aux (interiorSupportProbe previous current tested) after
        (fun x hx => interiorSupport_high previous current tested
          (hafterP x hx)) 2 (Or.inr (Or.inl rfl)),
      if_pos hmem]
  · rw [if_neg (fun h => hmem (hcond.mp h)),
      show mul 1 3 = 0 by decide,
      freezeZero, if_neg hmem]

/-- Item 2: initial support. -/
theorem initialSupport_eval
    (gap after : List Nat) (current tested : Nat)
    (hct : tested ≠ current)
    (hgapC : ∀ x ∈ gap, x ≠ current) :
    probeFold (initialSupportProbe current tested)
        (gap ++ current :: after) 4 =
      (if tested ∈ gap then 5 else 3) := by
  have hgapVal : ∀ x ∈ gap, (initialSupportProbe current tested) x = 4 ∨ (initialSupportProbe current tested) x = 5 := by
    intro x hx
    unfold initialSupportProbe
    rw [if_neg (hgapC x hx)]
    by_cases ht : x = tested <;> simp [ht]
  have hfive : ∀ x ∈ gap, ((initialSupportProbe current tested) x = 5 ↔ x = tested) := by
    intro x hx
    unfold initialSupportProbe
    rw [if_neg (hgapC x hx)]
    by_cases ht : x = tested <;> simp [ht]
  have hvc : (initialSupportProbe current tested) current = 3 := by simp [initialSupportProbe]
  have hcond : (∃ x ∈ gap, (initialSupportProbe current tested) x = 5) ↔ tested ∈ gap := by
    constructor
    · rintro ⟨x, hx, h5⟩
      exact ((hfive x hx).mp h5) ▸ hx
    · intro ht
      exact ⟨tested, ht, (hfive tested ht).mpr rfl⟩
  have hhigh : ∀ x ∈ after, HighState ((initialSupportProbe current tested) x) := by
    intro x hx
    unfold initialSupportProbe HighState
    by_cases hc : x = current
    · simp [hc]
    · rw [if_neg hc]
      by_cases ht : x = tested <;> simp [ht]
  rw [probeFold_append,
    initialDetectSupport (initialSupportProbe current tested) gap 4 (Or.inl rfl) hgapVal,
    probeFold_cons, hvc]
  by_cases hmem : tested ∈ gap
  · rw [if_pos (Or.inr (hcond.mpr hmem)),
      show mul 5 3 = 5 by decide,
      suffixFreeze_aux (initialSupportProbe current tested) after hhigh 5 (Or.inr (Or.inr (Or.inr rfl))),
      if_pos hmem]
  · rw [if_neg (by
        rintro (h | h)
        · exact absurd h (by decide)
        · exact hmem (hcond.mp h)),
      show mul 4 3 = 3 by decide,
      suffixFreeze_aux (initialSupportProbe current tested) after hhigh 3
        (Or.inr (Or.inr (Or.inl rfl))),
      if_neg hmem]

/-- Item 3: final support. -/
theorem finalSupport_eval
    (before gap : List Nat) (previous tested : Nat)
    (hpt : tested ≠ previous)
    (hbefore : ∀ x ∈ before, x ≠ previous)
    (hgapP : ∀ x ∈ gap, x ≠ previous) :
    probeFold (finalSupportProbe previous tested)
        (before ++ previous :: gap) 4 =
      (if tested ∈ gap then 2 else 1) := by
  have hhighBefore : ∀ x ∈ before, HighState ((finalSupportProbe previous tested) x) := by
    intro x hx
    unfold finalSupportProbe HighState
    rw [if_neg (hbefore x hx)]
    by_cases ht : x = tested <;> simp [ht]
  have hprefix : HighState (probeFold (finalSupportProbe previous tested) before 4) :=
    foldStaysHigh (finalSupportProbe previous tested) before 4 hhighBefore (Or.inr (Or.inl rfl))
  have hvp : (finalSupportProbe previous tested) previous = 1 := by simp [finalSupportProbe]
  have hgapVal : ∀ x ∈ gap, (finalSupportProbe previous tested) x = 4 ∨ (finalSupportProbe previous tested) x = 5 := by
    intro x hx
    unfold finalSupportProbe
    rw [if_neg (hgapP x hx)]
    by_cases ht : x = tested <;> simp [ht]
  have hfive : ∀ x ∈ gap, ((finalSupportProbe previous tested) x = 5 ↔ x = tested) := by
    intro x hx
    unfold finalSupportProbe
    rw [if_neg (hgapP x hx)]
    by_cases ht : x = tested <;> simp [ht]
  have hcond : (∃ x ∈ gap, (finalSupportProbe previous tested) x = 5) ↔ tested ∈ gap := by
    constructor
    · rintro ⟨x, hx, h5⟩
      exact ((hfive x hx).mp h5) ▸ hx
    · intro ht
      exact ⟨tested, ht, (hfive tested ht).mpr rfl⟩
  rw [probeFold_append, probeFold_cons, hvp, armAfterHigh hprefix,
    gapDetectSupport (finalSupportProbe previous tested) gap hgapVal]
  by_cases hmem : tested ∈ gap
  · rw [if_pos (hcond.mpr hmem), if_pos hmem]
  · rw [if_neg (fun h => hmem (hcond.mp h)), if_neg hmem]

/-- Local `find?` congruence on members (self-contained, so no stock
lemma spelling is load-bearing). -/
private theorem find?_congr_on_mem (p q : Nat → Bool) :
    ∀ letters : List Nat,
      (∀ x ∈ letters, p x = q x) →
      letters.find? p = letters.find? q
  | [], _ => rfl
  | letter :: rest, hall => by
      have hhead := hall letter (List.mem_cons_self ..)
      have hrest := find?_congr_on_mem p q rest
        (fun x hx => hall x (List.mem_cons_of_mem _ hx))
      by_cases hp : p letter = true
      · rw [List.find?_cons_of_pos hp,
          List.find?_cons_of_pos (hhead ▸ hp)]
      · rw [List.find?_cons_of_neg hp,
          List.find?_cons_of_neg (fun hq => hp (hhead ▸ hq)), hrest]

/-- Item 4: noninitial order.  Both `c` and `d` occur in `gap` (the
item-4 hypothesis of msg-0252), so the first occurrence among them
decides: 2 when it is `c`, 0 when it is `d`. -/
theorem interiorOrder_eval
    (before gap after : List Nat) (previous c d : Nat)
    (hcd : c ≠ d) (hcp : c ≠ previous) (hdp : d ≠ previous)
    (hbefore : ∀ x ∈ before, x ≠ previous)
    (hgapP : ∀ x ∈ gap, x ≠ previous)
    (hafterP : ∀ x ∈ after, x ≠ previous)
    (hcgap : c ∈ gap) :
    probeFold (orderProbe previous c d)
        (before ++ previous :: gap ++ after) 4 =
      (match gap.find? (fun x => decide (x = c ∨ x = d)) with
        | none => 1
        | some x => if x = c then 2 else 0) := by
  have hhigh : ∀ x, x ≠ previous → HighState ((orderProbe previous c d) x) := by
    intro x hx
    unfold orderProbe HighState
    rw [if_neg hx]
    by_cases hc : x = c
    · simp [hc]
    · rw [if_neg hc]
      have hdc : ¬ d = c := fun h => hcd h.symm
      by_cases hd : x = d <;> simp [hd, hc, hdc]
  have hprefix : HighState (probeFold (orderProbe previous c d) before 4) :=
    foldStaysHigh (orderProbe previous c d) before 4 (fun x hx => hhigh x (hbefore x hx))
      (Or.inr (Or.inl rfl))
  have hvp : (orderProbe previous c d) previous = 1 := by simp [orderProbe]
  have hval : ∀ x ∈ gap,
      (decide ((orderProbe previous c d) x ≠ 4) = decide (x = c ∨ x = d)) ∧
        ((orderProbe previous c d) x = 5 ↔ x = c) := by
    intro x hx
    unfold orderProbe
    rw [if_neg (hgapP x hx)]
    by_cases hc : x = c
    · simp [hc]
    · rw [if_neg hc]
      have hdc : ¬ d = c := fun h => hcd h.symm
      by_cases hd : x = d <;> simp [hd, hc, hdc]
  have hfind :
      gap.find? (fun x => decide ((orderProbe previous c d) x ≠ 4)) =
        gap.find? (fun x => decide (x = c ∨ x = d)) :=
    find?_congr_on_mem _ _ gap (fun x hx => (hval x hx).1)
  have hsome :
      ∃ x₀, gap.find? (fun x => decide (x = c ∨ x = d)) = some x₀ := by
    rcases hfound : gap.find? (fun x => decide (x = c ∨ x = d)) with
      _ | x₀
    · exact absurd (List.find?_eq_none.mp hfound c hcgap) (by simp)
    · exact ⟨x₀, rfl⟩
  rcases hsome with ⟨x₀, hx₀⟩
  have hx₀mem : x₀ ∈ gap := List.mem_of_find?_eq_some hx₀
  have hafterHigh : ∀ x ∈ after, HighState ((orderProbe previous c d) x) :=
    fun x hx => hhigh x (hafterP x hx)
  rw [probeFold_append, probeFold_append, probeFold_cons, hvp,
    armAfterHigh hprefix,
    gapDetectOrder (orderProbe previous c d) gap (fun x hx => hhigh x (hgapP x hx)),
    hfind, hx₀]
  simp only []
  by_cases hc : x₀ = c
  · rw [if_pos ((hval x₀ hx₀mem).2.mpr hc), if_pos hc,
      suffixFreeze_aux (orderProbe previous c d) after hafterHigh 2 (Or.inr (Or.inl rfl))]
  · have h5 : ¬ (orderProbe previous c d) x₀ = 5 := fun h => hc ((hval x₀ hx₀mem).2.mp h)
    rw [if_neg h5, if_neg hc, freezeZero]

/-- Item 5: initial order.  `c` occurs in the initial gap. -/
theorem initialOrder_eval
    (gap after : List Nat) (c d : Nat)
    (hcd : c ≠ d) (hcgap : c ∈ gap) :
    probeFold (initialOrderProbe c d) (gap ++ after) 4 =
      (match gap.find? (fun x => decide (x = c ∨ x = d)) with
        | none => 4
        | some x => if x = c then 5 else 3) := by
  have hhigh : ∀ x : Nat, HighState ((initialOrderProbe c d) x) := by
    intro x
    unfold initialOrderProbe HighState
    by_cases hc : x = c
    · simp [hc]
    · rw [if_neg hc]
      by_cases hd : x = d <;> simp [hd]
  have hval : ∀ x ∈ gap,
      (decide ((initialOrderProbe c d) x ≠ 4) = decide (x = c ∨ x = d)) ∧
        ((initialOrderProbe c d) x = 5 ↔ x = c) := by
    intro x _
    unfold initialOrderProbe
    by_cases hc : x = c
    · simp [hc]
    · rw [if_neg hc]
      have hdc : ¬ d = c := fun h => hcd h.symm
      by_cases hd : x = d <;> simp [hd, hc, hdc]
  have hfind :
      gap.find? (fun x => decide ((initialOrderProbe c d) x ≠ 4)) =
        gap.find? (fun x => decide (x = c ∨ x = d)) :=
    find?_congr_on_mem _ _ gap (fun x hx => (hval x hx).1)
  have hsome :
      ∃ x₀, gap.find? (fun x => decide (x = c ∨ x = d)) = some x₀ := by
    rcases hfound : gap.find? (fun x => decide (x = c ∨ x = d)) with
      _ | x₀
    · exact absurd (List.find?_eq_none.mp hfound c hcgap) (by simp)
    · exact ⟨x₀, rfl⟩
  rcases hsome with ⟨x₀, hx₀⟩
  have hx₀mem : x₀ ∈ gap := List.mem_of_find?_eq_some hx₀
  rw [probeFold_append,
    initialDetectOrder (initialOrderProbe c d) gap (fun x _ => hhigh x),
    hfind, hx₀]
  simp only []
  by_cases hc : x₀ = c
  · rw [if_pos ((hval x₀ hx₀mem).2.mpr hc), if_pos hc,
      suffixFreeze_aux (initialOrderProbe c d) after (fun x _ => hhigh x) 5
        (Or.inr (Or.inr (Or.inr rfl)))]
  · have h5 : ¬ (initialOrderProbe c d) x₀ = 5 := fun h => hc ((hval x₀ hx₀mem).2.mp h)
    rw [if_neg h5, if_neg hc,
      suffixFreeze_aux (initialOrderProbe c d) after (fun x _ => hhigh x) 3
        (Or.inr (Or.inr (Or.inl rfl)))]

end SemigroupBasis.CoRoots.Order6PublishedMonoid14.S6_8496
