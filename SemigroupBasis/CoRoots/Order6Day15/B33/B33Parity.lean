import SemigroupBasis.CoRoots.Order6Day15.B33.B33Probes

namespace SemigroupBasis.CoRoots.Order6Day15.B33

variable {S : Type u} {G : Semigroup S}

def parityEval (v : Nat → Bool) : List Block → Bool
  | [] => false
  | b :: bs => Bool.xor (b.power.odd && v b.letter) (parityEval v bs)

def parityAt (a : Nat) (bs : List Block) : Bool := parityEval (fun x => x == a) bs

def parityTotal (P : Probes G) : Option S → S
  | none => P.parity false
  | some a => a

theorem parity_power (P : Probes G) (p : Power) (a : Bool) :
    p.value G (P.parity a) = P.parity (p.odd && a) := by
  cases p <;> cases a <;> simp only [Power.value,Power.odd,P.parity_mul,Bool.and,Bool.xor] <;> rfl

theorem parity_eval (P : Probes G) (v : Nat → Bool) (bs : List Block) :
    parityTotal P (evalBlocks G (fun x => P.parity (v x)) bs) =
      P.parity (parityEval v bs) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [evalBlocks_cons,parity_power]
    simp only [parityEval]
    cases tailValue : evalBlocks G (fun x => P.parity (v x)) bs with
    | none =>
      have tailParity : P.parity false = P.parity (parityEval v bs) := by
        simpa only [tailValue,parityTotal] using ih
      have tailFalse := P.parity_injective tailParity
      rw [← tailFalse]
      simp only [optMul,parityTotal,Bool.xor_false]
    | some value =>
      have tailParity : value = P.parity (parityEval v bs) := by
        simpa only [tailValue,parityTotal] using ih
      simp only [optMul,parityTotal,tailParity,P.parity_mul]

theorem parityAt_absent (a : Nat) (bs : List Block) (ha : a ∉ letters bs) :
    parityAt a bs = false := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have different : b.letter ≠ a := by intro h; exact ha (by simp [h])
    have absent : a ∉ letters bs := by intro h; exact ha (by simp [h])
    change Bool.xor (b.power.odd && (b.letter == a)) (parityAt a bs) = false
    rw [beq_eq_false_iff_ne.mpr different,Bool.and_false,Bool.false_xor,ih absent]

theorem parityAt_cons (a : Nat) (b : Block) (bs : List Block) :
    parityAt a (b :: bs) = Bool.xor (b.power.odd && (b.letter == a)) (parityAt a bs) := rfl

theorem oddPowers_eq_of_parityAt (bs cs : List Block)
    (hb : (letters bs).Nodup) (hc : (letters cs).Nodup)
    (hl : letters bs = letters cs) (same : ∀ a, parityAt a bs = parityAt a cs) :
    oddPowers bs = oddPowers cs := by
  induction bs generalizing cs with
  | nil =>
    cases cs with
    | nil => rfl
    | cons c cs => simp at hl
  | cons b bs ih =>
    cases cs with
    | nil => simp at hl
    | cons c cs =>
      have letterEq : b.letter = c.letter := (List.cons.inj hl).1
      have restLetters : letters bs = letters cs := (List.cons.inj hl).2
      have bAbsent : b.letter ∉ letters bs := (List.nodup_cons.mp hb).1
      have cAbsent : c.letter ∉ letters cs := (List.nodup_cons.mp hc).1
      have oddEq : b.power.odd = c.power.odd := by
        have observed := same b.letter
        rw [parityAt_cons,parityAt_cons,parityAt_absent _ _ bAbsent] at observed
        rw [letterEq,parityAt_absent _ _ cAbsent] at observed
        simpa using observed
      have restEq : oddPowers bs = oddPowers cs := by
        apply ih _ (List.nodup_cons.mp hb).2 (List.nodup_cons.mp hc).2 restLetters
        intro a
        by_cases equal : a = b.letter
        · subst a
          rw [parityAt_absent _ _ bAbsent,letterEq,parityAt_absent _ _ cAbsent]
        · have bNe : b.letter ≠ a := Ne.symm equal
          have cNe : c.letter ≠ a := by simpa only [letterEq] using bNe
          simpa only [parityAt_cons,beq_eq_false_iff_ne.mpr bNe,
            beq_eq_false_iff_ne.mpr cNe,Bool.and_false,Bool.false_xor] using same a
      simp only [oddPowers,List.map_cons,oddEq]
      exact congrArg (List.cons c.power.odd) restEq

theorem oddPowers_eq_of_eval (P : Probes G) (bs cs : List Block)
    (hb : (letters bs).Nodup) (hc : (letters cs).Nodup)
    (hl : letters bs = letters cs) (same : ∀ v, evalBlocks G v bs = evalBlocks G v cs) :
    oddPowers bs = oddPowers cs := by
  apply oddPowers_eq_of_parityAt bs cs hb hc hl
  intro a
  apply P.parity_injective
  change P.parity (parityEval (fun x => x == a) bs) = P.parity (parityEval (fun x => x == a) cs)
  rw [← parity_eval P,← parity_eval P,same]

end SemigroupBasis.CoRoots.Order6Day15.B33
