import SemigroupBasis.CoRoots.Order6SporadicSection22Basis
import SemigroupBasis.CoRoots.S5_107ListDerives

/-! Unrestricted deletion steps in Lee-Zhang2015 Lemma22.10.
Every non-first-occurrence block contracts to its final letter. All optional
context cases of22.5 are instantiated explicitly, including empty contexts. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection22.E7
open SemigroupBasis

abbrev ListDerives : List Nat → List Nat → Prop := S5_107.ListDerives basis

private def replacement (x y h k : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | 2 => h
  | _ => k

private theorem instantiate (law : Identity Nat) (member : law ∈ basis)
    (x y h k : Word Nat) :
    ListDerives (law.lhs.bind (replacement x y h k)).toList
      (law.rhs.bind (replacement x y h k)).toList :=
  S5_107.ListDerives.ofWord
    (Derives.subst (Derives.fromBasis (e := law) member) (replacement x y h k))

theorem listPower (x : Nat) : ListDerives [x,x,x] [x,x] :=
  instantiate lawPower (by decide) (Word.singleton x) (Word.singleton x)
    (Word.singleton x) (Word.singleton x)

theorem contractLast (x : Nat) (gap : List Nat) :
    ListDerives ([x] ++ gap ++ [x,x]) ([x] ++ gap ++ [x]) := by
  cases gap with
  | nil => exact listPower x
  | cons h t =>
      have raw := instantiate lawPowerH (by decide) (Word.singleton x)
        (Word.singleton x) (S5_107.listWordOfCons h t) (Word.singleton x)
      simpa [lawPowerH, replacement, Word.bind, Word.toList, Word.append,
        Word.singleton, S5_107.listWordOfCons, List.append_assoc] using raw

theorem contractLastOfSeen (stem : List Nat) (x : Nat) (seen : x ∈ stem) :
    ListDerives (stem ++ [x,x]) (stem ++ [x]) := by
  obtain ⟨before,gap,shape⟩ := List.mem_iff_append.mp seen
  simpa [shape,List.append_assoc] using (contractLast x gap).prepend before

theorem deleteOrdered (x y : Nat) (firstGap secondGap : List Nat) :
    ListDerives ([x] ++ firstGap ++ [y] ++ secondGap ++ [x,y])
      ([x] ++ firstGap ++ [y] ++ secondGap ++ [y]) := by
  cases firstGap with
  | nil =>
      cases secondGap with
      | nil =>
          exact instantiate lawDelete (by decide) (Word.singleton x) (Word.singleton y)
            (Word.singleton x) (Word.singleton x)
      | cons h t =>
          have raw := instantiate lawDeleteK (by decide) (Word.singleton x) (Word.singleton y)
            (Word.singleton x) (S5_107.listWordOfCons h t)
          simpa [lawDeleteK,replacement,Word.bind,Word.toList,Word.append,
            Word.singleton,S5_107.listWordOfCons,List.append_assoc] using raw
  | cons h t =>
      cases secondGap with
      | nil =>
          have raw := instantiate lawDeleteH (by decide) (Word.singleton x) (Word.singleton y)
            (S5_107.listWordOfCons h t) (Word.singleton x)
          simpa [lawDeleteH,replacement,Word.bind,Word.toList,Word.append,
            Word.singleton,S5_107.listWordOfCons,List.append_assoc] using raw
      | cons k s =>
          have raw := instantiate lawDeleteHK (by decide) (Word.singleton x) (Word.singleton y)
            (S5_107.listWordOfCons h t) (S5_107.listWordOfCons k s)
          simpa [lawDeleteHK,replacement,Word.bind,Word.toList,Word.append,
            Word.singleton,S5_107.listWordOfCons,List.append_assoc] using raw

theorem deleteReverse (x y : Nat) (firstGap secondGap : List Nat) :
    ListDerives ([x] ++ firstGap ++ [y] ++ secondGap ++ [y,x])
      ([x] ++ firstGap ++ [y] ++ secondGap ++ [x]) := by
  cases firstGap with
  | nil =>
      cases secondGap with
      | nil =>
          exact instantiate lawReverse (by decide) (Word.singleton x) (Word.singleton y)
            (Word.singleton x) (Word.singleton x)
      | cons h t =>
          have raw := instantiate lawReverseK (by decide) (Word.singleton x) (Word.singleton y)
            (Word.singleton x) (S5_107.listWordOfCons h t)
          simpa [lawReverseK,replacement,Word.bind,Word.toList,Word.append,
            Word.singleton,S5_107.listWordOfCons,List.append_assoc] using raw
  | cons h t =>
      cases secondGap with
      | nil =>
          have raw := instantiate lawReverseH (by decide) (Word.singleton x) (Word.singleton y)
            (S5_107.listWordOfCons h t) (Word.singleton x)
          simpa [lawReverseH,replacement,Word.bind,Word.toList,Word.append,
            Word.singleton,S5_107.listWordOfCons,List.append_assoc] using raw
      | cons k s =>
          have raw := instantiate lawReverseHK (by decide) (Word.singleton x) (Word.singleton y)
            (S5_107.listWordOfCons h t) (S5_107.listWordOfCons k s)
          simpa [lawReverseHK,replacement,Word.bind,Word.toList,Word.append,
            Word.singleton,S5_107.listWordOfCons,List.append_assoc] using raw

theorem deleteAfterSeen (stem : List Nat) (x y : Nat)
    (seenX : x ∈ stem) (seenY : y ∈ stem) :
    ListDerives (stem ++ [x,y]) (stem ++ [y]) := by
  by_cases same : x = y
  · subst y
    exact contractLastOfSeen stem x seenX
  induction stem with
  | nil => simp at seenX
  | cons head tail ih =>
      by_cases headX : head = x
      · subst head
        have inTail : y ∈ tail := (List.mem_cons.mp seenY).resolve_left (Ne.symm same)
        obtain ⟨firstGap,secondGap,shape⟩ := List.mem_iff_append.mp inTail
        simpa [shape,List.append_assoc] using deleteOrdered x y firstGap secondGap
      · by_cases headY : head = y
        · subst head
          have inTail : x ∈ tail := (List.mem_cons.mp seenX).resolve_left same
          obtain ⟨firstGap,secondGap,shape⟩ := List.mem_iff_append.mp inTail
          simpa [shape,List.append_assoc] using deleteReverse y x firstGap secondGap
        · have xTail : x ∈ tail := (List.mem_cons.mp seenX).resolve_left (Ne.symm headX)
          have yTail : y ∈ tail := (List.mem_cons.mp seenY).resolve_left (Ne.symm headY)
          simpa using (ih xTail yTail).prepend [head]

def lastSingleton : List Nat → List Nat
  | [] => []
  | [x] => [x]
  | _ :: y :: rest => lastSingleton (y :: rest)

theorem lastSingleton_length : ∀ letters : List Nat, (lastSingleton letters).length ≤ 1
  | [] => by decide
  | [_] => Nat.le_refl 1
  | _ :: y :: rest => lastSingleton_length (y :: rest)

theorem lastSingleton_mem : ∀ (letters : List Nat) (x : Nat),
    x ∈ lastSingleton letters → x ∈ letters
  | [], _, member => by simp [lastSingleton] at member
  | [_], _, member => member
  | head :: y :: rest, x, member =>
      List.mem_cons_of_mem head (lastSingleton_mem (y :: rest) x member)

theorem pruneSeenBlock (stem : List Nat) : ∀ block : List Nat,
    (∀ x ∈ block, x ∈ stem) → ListDerives (stem ++ block) (stem ++ lastSingleton block)
  | [], _ => S5_107.ListDerives.refl _
  | [_], _ => S5_107.ListDerives.refl _
  | x :: y :: rest, seen => by
      have hx : x ∈ stem := seen x (by simp)
      have hy : y ∈ stem := seen y (by simp)
      have first : ListDerives (stem ++ x :: y :: rest) (stem ++ y :: rest) := by
        simpa [List.append_assoc] using (deleteAfterSeen stem x y hx hy).append rest
      exact first.trans (pruneSeenBlock stem (y :: rest)
        (fun a member => seen a (List.mem_cons_of_mem x member)))

#print axioms contractLast
#print axioms contractLastOfSeen
#print axioms deleteOrdered
#print axioms deleteReverse
#print axioms deleteAfterSeen
#print axioms lastSingleton_length
#print axioms lastSingleton_mem
#print axioms pruneSeenBlock

end SemigroupBasis.CoRoots.Order6SporadicSection22.E7
