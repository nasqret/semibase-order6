import SemigroupBasis.CoRoots.Order6Day15.B33.B33Shape

namespace SemigroupBasis.CoRoots.Order6Day15.B33

def Power.odd : Power → Bool
  | .one => true
  | .two => false
  | .three => true

def Power.simple : Power → Bool
  | .one => true
  | _ => false

def oddPowers (bs : List Block) : List Bool := bs.map (fun b => b.power.odd)

def headSimple : List Block → Bool
  | [] => false
  | b :: _ => b.power.simple

def tailSimple : List Block → Bool
  | [] => false
  | [b] => b.power.simple
  | _ :: c :: cs => tailSimple (c :: cs)

theorem power_eq_of_odd_simple (p q : Power) (ho : p.odd = q.odd)
    (hs : p.simple = q.simple) : p = q := by
  cases p <;> cases q <;> simp_all [Power.odd,Power.simple]

theorem power_eq_of_odd_small (p q : Power) (hp : p ≠ .three) (hq : q ≠ .three)
    (ho : p.odd = q.odd) : p = q := by
  cases p <;> cases q <;> simp_all [Power.odd]

/-- The four advertised observations uniquely determine every allowed block form. -/
theorem small_eq_of_key (isHead : Bool) (bs cs : List Block)
    (hb : Small isHead bs) (hc : Small isHead cs)
    (hl : letters bs = letters cs) (ho : oddPowers bs = oddPowers cs)
    (hh : isHead = true → headSimple bs = headSimple cs)
    (ht : tailSimple bs = tailSimple cs) : bs = cs := by
  induction bs generalizing isHead cs with
  | nil => cases cs <;> simpa using hl
  | cons b bs ih =>
    cases cs with
    | nil => simp at hl
    | cons c cs =>
      have letterEq : b.letter = c.letter := (List.cons.inj hl).1
      have restLetters : letters bs = letters cs := (List.cons.inj hl).2
      have oddEq : b.power.odd = c.power.odd := (List.cons.inj ho).1
      have restOdd : oddPowers bs = oddPowers cs := (List.cons.inj ho).2
      cases bs with
      | nil =>
        cases cs with
        | nil =>
          have powerEq := power_eq_of_odd_simple b.power c.power oddEq ht
          cases b; cases c; simp_all
        | cons d ds => simp at restLetters
      | cons d ds =>
        cases cs with
        | nil => simp at restLetters
        | cons e es =>
          have powerEq : b.power = c.power := by
            cases isHead with
            | true => exact power_eq_of_odd_simple _ _ oddEq (hh rfl)
            | false =>
              have bSmall : b.power ≠ .three := hb.1.resolve_left (by decide)
              have cSmall : c.power ≠ .three := hc.1.resolve_left (by decide)
              exact power_eq_of_odd_small _ _ bSmall cSmall oddEq
          have restEq := ih false (e :: es) hb.2 hc.2 restLetters restOdd
            (by intro impossible; cases impossible) ht
          have blockEq : b = c := by cases b; cases c; simp_all
          rw [blockEq,restEq]

theorem normal_eq_of_key (bs cs : List Block) (hb : Normal bs) (hc : Normal cs)
    (hl : letters bs = letters cs) (ho : oddPowers bs = oddPowers cs)
    (hh : headSimple bs = headSimple cs) (ht : tailSimple bs = tailSimple cs) :
    bs = cs := small_eq_of_key true bs cs hb.2 hc.2 hl ho (fun _ => hh) ht

end SemigroupBasis.CoRoots.Order6Day15.B33
