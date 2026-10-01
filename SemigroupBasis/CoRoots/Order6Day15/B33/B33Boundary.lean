import SemigroupBasis.CoRoots.Order6Day15.B33.B33Probes

namespace SemigroupBasis.CoRoots.Order6Day15.B33

variable {S : Type u} {G : Semigroup S}

theorem value_idempotent (G : Semigroup S) (x : S) (idem : G.mul x x = x) (p : Power) :
    p.value G x = x := by cases p <;> simp only [Power.value,idem]

theorem evalBlocks_const (G : Semigroup S) (x : S) (idem : G.mul x x = x) (bs : List Block) :
    evalBlocks G (fun _ => x) bs = if bs = [] then none else some x := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [evalBlocks_cons,value_idempotent G x idem,ih]
    cases bs <;> simp [optMul,idem]

theorem unit_idempotent (P : Probes G) : G.mul (P.order none) (P.order none) = P.order none :=
  P.order_mul none none

theorem evalBlocks_absent (P : Probes G) (a : Nat) (x : S) (bs : List Block)
    (absent : a ∉ letters bs) :
    evalBlocks G (fun b => if b = a then x else P.order none) bs =
      if bs = [] then none else some (P.order none) := by
  rw [evalBlocks_congr G bs _ (fun _ => P.order none)]
  · exact evalBlocks_const G _ (unit_idempotent P) bs
  · intro b member
    have different : b ≠ a := by intro h; subst b; exact absent member
    simp only [if_neg different]

theorem head_value (P : Probes G) (p : Power) :
    p.value G P.head = if p.simple then P.head else P.dead := by
  cases p <;> simp [Power.value,Power.simple,P.head_square,P.dead_head]

theorem head_probe (P : Probes G) (b : Block) (bs : List Block)
    (absent : b.letter ∉ letters bs) :
    evalBlocks G (fun x => if x = b.letter then P.head else P.order none) (b :: bs) =
      some (if b.power.simple then P.head else P.dead) := by
  rw [evalBlocks_cons,if_pos rfl,head_value,evalBlocks_absent P _ _ _ absent]
  cases bs with
  | nil => simp [optMul]
  | cons c cs =>
    simp only [List.cons_ne_nil,if_false,optMul]
    cases b.power <;> simp [Power.simple,P.head_unit,P.dead_unit]

theorem headSimple_eq_of_eval (P : Probes G) (bs cs : List Block)
    (hb : (letters bs).Nodup) (hc : (letters cs).Nodup)
    (hl : letters bs = letters cs) (same : ∀ v, evalBlocks G v bs = evalBlocks G v cs) :
    headSimple bs = headSimple cs := by
  cases bs with
  | nil => cases cs with
    | nil => rfl
    | cons c cs => simp at hl
  | cons b bs =>
    cases cs with
    | nil => simp at hl
    | cons c cs =>
      have letterEq : b.letter = c.letter := (List.cons.inj hl).1
      have observed := same (fun x => if x = b.letter then P.head else P.order none)
      rw [head_probe P b bs (List.nodup_cons.mp hb).1] at observed
      have right := head_probe P c cs (List.nodup_cons.mp hc).1
      rw [← letterEq] at right
      rw [right] at observed
      have values := Option.some.inj observed
      change b.power.simple = c.power.simple
      cases bh : b.power.simple <;> cases ch : c.power.simple <;>
        simp_all [P.head_ne_dead,Ne.symm P.head_ne_dead]

theorem evalBlocks_append (G : Semigroup S) (v : Nat → S) (bs cs : List Block) :
    evalBlocks G v (bs ++ cs) = optMul G (evalBlocks G v bs) (evalBlocks G v cs) := by
  have rendered : render (bs ++ cs) = render bs ++ render cs := by
    induction bs with
    | nil => rfl
    | cons b bs ih => simp only [List.cons_append,render,ih,List.append_assoc]
  unfold evalBlocks
  rw [rendered,evalList_append]

theorem tail_value (P : Probes G) (p : Power) :
    p.value G P.tail = if p.simple then P.tail else P.order (some false) := by
  cases p <;> simp [Power.value,Power.simple,P.tail_square,P.zero_tail]

theorem tail_probe (P : Probes G) (bs : List Block) (b : Block)
    (absent : b.letter ∉ letters bs) :
    evalBlocks G (fun x => if x = b.letter then P.tail else P.order none) (bs ++ [b]) =
      some (if b.power.simple then P.tail else P.order (some false)) := by
  rw [evalBlocks_append,evalBlocks_absent P _ _ _ absent,evalBlocks_cons,
    if_pos rfl,tail_value,evalBlocks_nil]
  cases bs with
  | nil => simp [optMul]
  | cons c cs =>
    simp only [List.cons_ne_nil,if_false,optMul]
    cases b.power.simple <;> simp [P.unit_tail,P.order_mul,firstJoin]

theorem tailSimple_append (bs : List Block) (b : Block) : tailSimple (bs ++ [b]) = b.power.simple := by
  induction bs with
  | nil => rfl
  | cons c cs ih =>
    cases cs with
    | nil => rfl
    | cons d ds => exact ih

theorem letters_append (bs cs : List Block) : letters (bs ++ cs) = letters bs ++ letters cs :=
  List.map_append

theorem nil_or_snoc (bs : List Block) : bs = [] ∨ ∃ cs c, bs = cs ++ [c] := by
  induction bs with
  | nil => exact Or.inl rfl
  | cons b bs ih =>
    rcases ih with empty | ⟨cs,c,equal⟩
    · subst bs; exact Or.inr ⟨[],b,rfl⟩
    · exact Or.inr ⟨b :: cs,c,by rw [equal]; rfl⟩

theorem tailSimple_eq_of_eval (P : Probes G) (bs cs : List Block)
    (hb : (letters bs).Nodup) (hc : (letters cs).Nodup)
    (hl : letters bs = letters cs) (same : ∀ v, evalBlocks G v bs = evalBlocks G v cs) :
    tailSimple bs = tailSimple cs := by
  rcases nil_or_snoc bs with empty | ⟨bs,b,rfl⟩
  · subst bs
    cases cs with
    | nil => rfl
    | cons c cs => simp at hl
  · rcases nil_or_snoc cs with empty | ⟨cs,c,rfl⟩
    · subst cs; simp [letters_append] at hl
    · have reversed : b.letter :: (letters bs).reverse = c.letter :: (letters cs).reverse := by
        simpa only [letters_append,letters_cons,letters_nil,List.reverse_append,
          List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,List.append_nil]
          using congrArg List.reverse hl
      have letterEq : b.letter = c.letter := (List.cons.inj reversed).1
      have bAbsent : b.letter ∉ letters bs := by
        intro member
        have nodup := List.nodup_append.mp (by simpa only [letters_append,letters_cons,letters_nil] using hb)
        exact nodup.2.2 b.letter member b.letter (by simp) rfl
      have cAbsent : c.letter ∉ letters cs := by
        intro member
        have nodup := List.nodup_append.mp (by simpa only [letters_append,letters_cons,letters_nil] using hc)
        exact nodup.2.2 c.letter member c.letter (by simp) rfl
      have observed := same (fun x => if x = b.letter then P.tail else P.order none)
      rw [tail_probe P bs b bAbsent] at observed
      have right := tail_probe P cs c cAbsent
      rw [← letterEq] at right
      rw [right] at observed
      have values := Option.some.inj observed
      rw [tailSimple_append,tailSimple_append]
      cases bh : b.power.simple <;> cases ch : c.power.simple <;>
        simp_all [P.tail_ne_zero,Ne.symm P.tail_ne_zero]

end SemigroupBasis.CoRoots.Order6Day15.B33
