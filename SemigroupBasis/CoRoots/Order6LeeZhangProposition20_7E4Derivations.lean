import SemigroupBasis.CoRoots.Order6LeeZhangProposition20_7E4Syntax
import SemigroupBasis.CoRoots.S5_107ListDerives

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeZhangProposition20_7E4

open SemigroupBasis

/-!
# Lee--Zhang Proposition 20.7 / E4: primitive derivations

This file exposes only substitution and contextual consequences of the exact
direct laws (20.6a)--(20.6f).  Optional paper contexts are represented by
`Option (Word Nat)` at word level and by possibly empty lists at list level.
Every absent context selects the corresponding literal member of the frozen
64-law basis; no empty semigroup word is introduced by substitution.

The guarded shapes in the theorem statements are intentional.  In
particular, this file does not assert unrestricted commutativity, import the
reversed route, transfer a neighbouring theory, or claim normalization or
completeness.
-/

/-- List-level derivability for the direct Proposition 20.7 basis. -/
abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives basis

/-- Place a word-level E4 derivation under arbitrary list context. -/
theorem listDerivesContextOfWord
    (before after : List Nat) {left right : Word Nat}
    (derivation : Derives basis left right) :
    ListDerives
      (before ++ left.toList ++ after)
      (before ++ right.toList ++ after) :=
  S5_107.ListDerives.context before after
    (S5_107.ListDerives.ofWord derivation)

/-! ## Optional-context selection -/

/-- Append a paper context exactly when its ordinary expansion retains it. -/
def appendOptional (stem : Word Nat) : Option (Word Nat) → Word Nat
  | none => stem
  | some context => stem ++ context

/-- Supply an arbitrary nonempty value for an omitted substitution slot.
The selected literal law does not contain that variable. -/
private def optionalReplacement
    (fallback : Word Nat) : Option (Word Nat) → Word Nat
  | none => fallback
  | some context => context

private def instantiateEightWords
    (x y h ka tb c z d : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | 2 => h
  | 3 => ka
  | 4 => tb
  | 5 => c
  | 6 => z
  | 7 => d
  | n + 8 => Word.singleton (n + 8)

private theorem substituteBasisLaw
    (identity : Identity Nat) (member : identity ∈ basis)
    (replacement : Nat → Word Nat) :
    Derives basis
      (identity.lhs.bind replacement)
      (identity.rhs.bind replacement) :=
  Derives.subst (derives_of_basis_member identity member) replacement

private def identity20_6a
    (optionalH optionalK : Option (Word Nat)) : Identity Nat :=
  match optionalH, optionalK with
  | some _, some _ => law20_6a_HK
  | some _, none => law20_6a_H
  | none, some _ => law20_6a_K
  | none, none => law20_6a_empty

private theorem identity20_6a_mem
    (optionalH optionalK : Option (Word Nat)) :
    identity20_6a optionalH optionalK ∈ basis := by
  cases optionalH <;> cases optionalK <;>
    simp [identity20_6a, basis]

private def identity20_6b
    (optionalH optionalK : Option (Word Nat)) : Identity Nat :=
  match optionalH, optionalK with
  | some _, some _ => law20_6b_HK
  | some _, none => law20_6b_H
  | none, some _ => law20_6b_K
  | none, none => law20_6b_empty

private theorem identity20_6b_mem
    (optionalH optionalK : Option (Word Nat)) :
    identity20_6b optionalH optionalK ∈ basis := by
  cases optionalH <;> cases optionalK <;>
    simp [identity20_6b, basis]

private def identity20_6c
    (optionalH optionalK optionalT : Option (Word Nat)) : Identity Nat :=
  match optionalH, optionalK, optionalT with
  | some _, some _, some _ => law20_6c_HKT
  | some _, some _, none => law20_6c_HK
  | some _, none, some _ => law20_6c_HT
  | some _, none, none => law20_6c_H
  | none, some _, some _ => law20_6c_KT
  | none, some _, none => law20_6c_K
  | none, none, some _ => law20_6c_T
  | none, none, none => law20_6c_empty

private theorem identity20_6c_mem
    (optionalH optionalK optionalT : Option (Word Nat)) :
    identity20_6c optionalH optionalK optionalT ∈ basis := by
  cases optionalH <;> cases optionalK <;> cases optionalT <;>
    simp [identity20_6c, basis]

private def identity20_6d
    (optionalH optionalK optionalT : Option (Word Nat)) : Identity Nat :=
  match optionalH, optionalK, optionalT with
  | some _, some _, some _ => law20_6d_HKT
  | some _, some _, none => law20_6d_HK
  | some _, none, some _ => law20_6d_HT
  | some _, none, none => law20_6d_H
  | none, some _, some _ => law20_6d_KT
  | none, some _, none => law20_6d_K
  | none, none, some _ => law20_6d_T
  | none, none, none => law20_6d_empty

private theorem identity20_6d_mem
    (optionalH optionalK optionalT : Option (Word Nat)) :
    identity20_6d optionalH optionalK optionalT ∈ basis := by
  cases optionalH <;> cases optionalK <;> cases optionalT <;>
    simp [identity20_6d, basis]

private def identity20_6e
    (optionalH optionalK optionalT : Option (Word Nat)) : Identity Nat :=
  match optionalH, optionalK, optionalT with
  | some _, some _, some _ => law20_6e_HKT
  | some _, some _, none => law20_6e_HK
  | some _, none, some _ => law20_6e_HT
  | some _, none, none => law20_6e_H
  | none, some _, some _ => law20_6e_KT
  | none, some _, none => law20_6e_K
  | none, none, some _ => law20_6e_T
  | none, none, none => law20_6e_empty

private theorem identity20_6e_mem
    (optionalH optionalK optionalT : Option (Word Nat)) :
    identity20_6e optionalH optionalK optionalT ∈ basis := by
  cases optionalH <;> cases optionalK <;> cases optionalT <;>
    simp [identity20_6e, basis]

private def identity20_6f
    (optionalH optionalA optionalB optionalC optionalD :
      Option (Word Nat)) : Identity Nat :=
  match optionalH, optionalA, optionalB, optionalC, optionalD with
  | some _, some _, some _, some _, some _ => law20_6f_HABCD
  | some _, some _, some _, some _, none => law20_6f_HABC
  | some _, some _, some _, none, some _ => law20_6f_HABD
  | some _, some _, some _, none, none => law20_6f_HAB
  | some _, some _, none, some _, some _ => law20_6f_HACD
  | some _, some _, none, some _, none => law20_6f_HAC
  | some _, some _, none, none, some _ => law20_6f_HAD
  | some _, some _, none, none, none => law20_6f_HA
  | some _, none, some _, some _, some _ => law20_6f_HBCD
  | some _, none, some _, some _, none => law20_6f_HBC
  | some _, none, some _, none, some _ => law20_6f_HBD
  | some _, none, some _, none, none => law20_6f_HB
  | some _, none, none, some _, some _ => law20_6f_HCD
  | some _, none, none, some _, none => law20_6f_HC
  | some _, none, none, none, some _ => law20_6f_HD
  | some _, none, none, none, none => law20_6f_H
  | none, some _, some _, some _, some _ => law20_6f_ABCD
  | none, some _, some _, some _, none => law20_6f_ABC
  | none, some _, some _, none, some _ => law20_6f_ABD
  | none, some _, some _, none, none => law20_6f_AB
  | none, some _, none, some _, some _ => law20_6f_ACD
  | none, some _, none, some _, none => law20_6f_AC
  | none, some _, none, none, some _ => law20_6f_AD
  | none, some _, none, none, none => law20_6f_A
  | none, none, some _, some _, some _ => law20_6f_BCD
  | none, none, some _, some _, none => law20_6f_BC
  | none, none, some _, none, some _ => law20_6f_BD
  | none, none, some _, none, none => law20_6f_B
  | none, none, none, some _, some _ => law20_6f_CD
  | none, none, none, some _, none => law20_6f_C
  | none, none, none, none, some _ => law20_6f_D
  | none, none, none, none, none => law20_6f_empty

private theorem identity20_6f_mem
    (optionalH optionalA optionalB optionalC optionalD :
      Option (Word Nat)) :
    identity20_6f optionalH optionalA optionalB optionalC optionalD ∈
      basis := by
  cases optionalH <;> cases optionalA <;> cases optionalB <;>
    cases optionalC <;> cases optionalD <;>
    simp [identity20_6f, basis]

/-! ## Word-level paper patterns -/

def pattern20_6aTarget
    (x : Word Nat) (optionalH optionalK : Option (Word Nat)) : Word Nat :=
  appendOptional (appendOptional x optionalH ++ x) optionalK ++ x

def pattern20_6aSource
    (x : Word Nat) (optionalH optionalK : Option (Word Nat)) : Word Nat :=
  pattern20_6aTarget x optionalH optionalK ++ x

def pattern20_6bSource
    (x : Word Nat) (optionalH optionalK : Option (Word Nat)) : Word Nat :=
  appendOptional (appendOptional x optionalH ++ x) optionalK ++ x

def pattern20_6bTarget
    (x : Word Nat) (optionalH optionalK : Option (Word Nat)) : Word Nat :=
  appendOptional (appendOptional x optionalK ++ x) optionalH ++ x

def pattern20_6cSource
    (x y : Word Nat)
    (optionalH optionalK optionalT : Option (Word Nat)) : Word Nat :=
  appendOptional
      (appendOptional (appendOptional x optionalH ++ x) optionalK ++ y)
      optionalT ++ y

def pattern20_6cTarget
    (x y : Word Nat)
    (optionalH optionalK optionalT : Option (Word Nat)) : Word Nat :=
  appendOptional
      (appendOptional (appendOptional x optionalH ++ x) optionalT ++ y)
      optionalK ++ y

def pattern20_6dSource
    (x y : Word Nat)
    (optionalH optionalK optionalT : Option (Word Nat)) : Word Nat :=
  appendOptional
      (appendOptional (appendOptional x optionalH ++ y) optionalK ++ x)
      optionalT ++ y

def pattern20_6dTarget
    (x y : Word Nat)
    (optionalH optionalK optionalT : Option (Word Nat)) : Word Nat :=
  appendOptional
      (appendOptional (appendOptional x optionalK ++ x) optionalH ++ y)
      optionalT ++ y

def pattern20_6eSource
    (x y : Word Nat)
    (optionalH optionalK optionalT : Option (Word Nat)) : Word Nat :=
  appendOptional
      (appendOptional (appendOptional x optionalH ++ y) optionalK ++ y)
      optionalT ++ x

def pattern20_6eTarget
    (x y : Word Nat)
    (optionalH optionalK optionalT : Option (Word Nat)) : Word Nat :=
  appendOptional
      (appendOptional (appendOptional x optionalT ++ x) optionalH ++ y)
      optionalK ++ y

def pattern20_6fSource
    (x y z : Word Nat)
    (optionalH optionalA optionalB optionalC optionalD :
      Option (Word Nat)) : Word Nat :=
  appendOptional
      (appendOptional
        (appendOptional
          (appendOptional (appendOptional x optionalH ++ x) optionalA ++ y)
          optionalB ++ y)
        optionalC ++ z)
      optionalD ++ z

def pattern20_6fTarget
    (x y z : Word Nat)
    (optionalH optionalA optionalB optionalC optionalD :
      Option (Word Nat)) : Word Nat :=
  appendOptional
      (appendOptional
        (appendOptional
          (appendOptional (appendOptional x optionalH ++ x) optionalC ++ z)
          optionalD ++ z)
        optionalA ++ y)
      optionalB ++ y

/-! ## Exact substituted identities -/

/-- Direct substitution form of the power cap (20.6a). -/
theorem derives20_6a
    (x : Word Nat) (optionalH optionalK : Option (Word Nat)) :
    Derives basis
      (pattern20_6aSource x optionalH optionalK)
      (pattern20_6aTarget x optionalH optionalK) := by
  have selected :=
    substituteBasisLaw
      (identity20_6a optionalH optionalK)
      (identity20_6a_mem optionalH optionalK)
      (instantiateEightWords x x
        (optionalReplacement x optionalH)
        (optionalReplacement x optionalK) x x x x)
  cases optionalH <;> cases optionalK <;>
    simpa [pattern20_6aSource, pattern20_6aTarget, appendOptional,
      identity20_6a, optionalReplacement, instantiateEightWords,
      law20_6a_HK, law20_6a_H, law20_6a_K, law20_6a_empty,
      w, Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      selected

/-- Direct substitution form of the `s_i x` block swap (20.6b). -/
theorem derives20_6b
    (x : Word Nat) (optionalH optionalK : Option (Word Nat)) :
    Derives basis
      (pattern20_6bSource x optionalH optionalK)
      (pattern20_6bTarget x optionalH optionalK) := by
  have selected :=
    substituteBasisLaw
      (identity20_6b optionalH optionalK)
      (identity20_6b_mem optionalH optionalK)
      (instantiateEightWords x x
        (optionalReplacement x optionalH)
        (optionalReplacement x optionalK) x x x x)
  cases optionalH <;> cases optionalK <;>
    simpa [pattern20_6bSource, pattern20_6bTarget, appendOptional,
      identity20_6b, optionalReplacement, instantiateEightWords,
      law20_6b_HK, law20_6b_H, law20_6b_K, law20_6b_empty,
      w, Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      selected

/-- Direct substitution form of the repeated-head block ordering (20.6c). -/
theorem derives20_6c
    (x y : Word Nat)
    (optionalH optionalK optionalT : Option (Word Nat)) :
    Derives basis
      (pattern20_6cSource x y optionalH optionalK optionalT)
      (pattern20_6cTarget x y optionalH optionalK optionalT) := by
  have selected :=
    substituteBasisLaw
      (identity20_6c optionalH optionalK optionalT)
      (identity20_6c_mem optionalH optionalK optionalT)
      (instantiateEightWords x y
        (optionalReplacement x optionalH)
        (optionalReplacement x optionalK)
        (optionalReplacement x optionalT) x x x)
  cases optionalH <;> cases optionalK <;> cases optionalT <;>
    simpa [pattern20_6cSource, pattern20_6cTarget, appendOptional,
      identity20_6c, optionalReplacement, instantiateEightWords,
      law20_6c_HKT, law20_6c_HK, law20_6c_HT, law20_6c_H,
      law20_6c_KT, law20_6c_K, law20_6c_T, law20_6c_empty,
      w, Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      selected

/-- Direct guarded move (20.6d), with both trailing `y` anchors retained. -/
theorem derives20_6d
    (x y : Word Nat)
    (optionalH optionalK optionalT : Option (Word Nat)) :
    Derives basis
      (pattern20_6dSource x y optionalH optionalK optionalT)
      (pattern20_6dTarget x y optionalH optionalK optionalT) := by
  have selected :=
    substituteBasisLaw
      (identity20_6d optionalH optionalK optionalT)
      (identity20_6d_mem optionalH optionalK optionalT)
      (instantiateEightWords x y
        (optionalReplacement x optionalH)
        (optionalReplacement x optionalK)
        (optionalReplacement x optionalT) x x x)
  cases optionalH <;> cases optionalK <;> cases optionalT <;>
    simpa [pattern20_6dSource, pattern20_6dTarget, appendOptional,
      identity20_6d, optionalReplacement, instantiateEightWords,
      law20_6d_HKT, law20_6d_HK, law20_6d_HT, law20_6d_H,
      law20_6d_KT, law20_6d_K, law20_6d_T, law20_6d_empty,
      w, Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      selected

/-- Direct guarded move (20.6e), with the doubled `y` block retained. -/
theorem derives20_6e
    (x y : Word Nat)
    (optionalH optionalK optionalT : Option (Word Nat)) :
    Derives basis
      (pattern20_6eSource x y optionalH optionalK optionalT)
      (pattern20_6eTarget x y optionalH optionalK optionalT) := by
  have selected :=
    substituteBasisLaw
      (identity20_6e optionalH optionalK optionalT)
      (identity20_6e_mem optionalH optionalK optionalT)
      (instantiateEightWords x y
        (optionalReplacement x optionalH)
        (optionalReplacement x optionalK)
        (optionalReplacement x optionalT) x x x)
  cases optionalH <;> cases optionalK <;> cases optionalT <;>
    simpa [pattern20_6eSource, pattern20_6eTarget, appendOptional,
      identity20_6e, optionalReplacement, instantiateEightWords,
      law20_6e_HKT, law20_6e_HK, law20_6e_HT, law20_6e_H,
      law20_6e_KT, law20_6e_K, law20_6e_T, law20_6e_empty,
      w, Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      selected

/-- Direct substitution form of the three repeated-block swap (20.6f). -/
theorem derives20_6f
    (x y z : Word Nat)
    (optionalH optionalA optionalB optionalC optionalD :
      Option (Word Nat)) :
    Derives basis
      (pattern20_6fSource x y z
        optionalH optionalA optionalB optionalC optionalD)
      (pattern20_6fTarget x y z
        optionalH optionalA optionalB optionalC optionalD) := by
  have selected :=
    substituteBasisLaw
      (identity20_6f optionalH optionalA optionalB optionalC optionalD)
      (identity20_6f_mem optionalH optionalA optionalB optionalC optionalD)
      (instantiateEightWords x y
        (optionalReplacement x optionalH)
        (optionalReplacement x optionalA)
        (optionalReplacement x optionalB)
        (optionalReplacement x optionalC) z
        (optionalReplacement x optionalD))
  cases optionalH <;> cases optionalA <;> cases optionalB <;>
    cases optionalC <;> cases optionalD <;>
    simpa [pattern20_6fSource, pattern20_6fTarget, appendOptional,
      identity20_6f, optionalReplacement, instantiateEightWords,
      law20_6f_HABCD, law20_6f_HABC, law20_6f_HABD, law20_6f_HAB,
      law20_6f_HACD, law20_6f_HAC, law20_6f_HAD, law20_6f_HA,
      law20_6f_HBCD, law20_6f_HBC, law20_6f_HBD, law20_6f_HB,
      law20_6f_HCD, law20_6f_HC, law20_6f_HD, law20_6f_H,
      law20_6f_ABCD, law20_6f_ABC, law20_6f_ABD, law20_6f_AB,
      law20_6f_ACD, law20_6f_AC, law20_6f_AD, law20_6f_A,
      law20_6f_BCD, law20_6f_BC, law20_6f_BD, law20_6f_B,
      law20_6f_CD, law20_6f_C, law20_6f_D, law20_6f_empty,
      w, Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      selected

/-! ## Contextual list instances -/

/-- Convert a possibly empty list into the matching optional paper word. -/
private def optionalWordOfList : List Nat → Option (Word Nat)
  | [] => none
  | head :: tail => some (S5_107.listWordOfCons head tail)

@[simp]
private theorem appendOptional_optionalWordOfList_toList
    (stem : Word Nat) (letters : List Nat) :
    (appendOptional stem (optionalWordOfList letters)).toList =
      stem.toList ++ letters := by
  cases letters with
  | nil =>
      simp [optionalWordOfList, appendOptional]
  | cons head tail =>
      simp [optionalWordOfList, appendOptional,
        S5_107.listWordOfCons, Word.toList]

/-- Contextual list form of the direct power cap (20.6a). -/
theorem listDerives20_6a
    (before after : List Nat) (x : Nat) (h k : List Nat) :
    ListDerives
      (before ++ [x] ++ h ++ [x] ++ k ++ [x, x] ++ after)
      (before ++ [x] ++ h ++ [x] ++ k ++ [x] ++ after) := by
  simpa only [pattern20_6aSource, pattern20_6aTarget,
    Word.toList_append, appendOptional_optionalWordOfList_toList,
    Word.toList_singleton, List.append_assoc, List.cons_append,
    List.nil_append, List.append_nil] using
      (listDerivesContextOfWord before after
        (derives20_6a (Word.singleton x)
          (optionalWordOfList h) (optionalWordOfList k)))

/-- Contextual list form of the direct `s_i x` block swap (20.6b). -/
theorem listDerives20_6b
    (before after : List Nat) (x : Nat) (h k : List Nat) :
    ListDerives
      (before ++ [x] ++ h ++ [x] ++ k ++ [x] ++ after)
      (before ++ [x] ++ k ++ [x] ++ h ++ [x] ++ after) := by
  simpa only [pattern20_6bSource, pattern20_6bTarget,
    Word.toList_append, appendOptional_optionalWordOfList_toList,
    Word.toList_singleton, List.append_assoc, List.cons_append,
    List.nil_append, List.append_nil] using
      (listDerivesContextOfWord before after
        (derives20_6b (Word.singleton x)
          (optionalWordOfList h) (optionalWordOfList k)))

/-- Contextual list form of the repeated-head ordering law (20.6c). -/
theorem listDerives20_6c
    (before after : List Nat) (x y : Nat)
    (h k t : List Nat) :
    ListDerives
      (before ++ [x] ++ h ++ [x] ++ k ++ [y] ++ t ++ [y] ++ after)
      (before ++ [x] ++ h ++ [x] ++ t ++ [y] ++ k ++ [y] ++ after) := by
  simpa only [pattern20_6cSource, pattern20_6cTarget,
    Word.toList_append, appendOptional_optionalWordOfList_toList,
    Word.toList_singleton, List.append_assoc, List.cons_append,
    List.nil_append, List.append_nil] using
      (listDerivesContextOfWord before after
        (derives20_6c (Word.singleton x) (Word.singleton y)
          (optionalWordOfList h) (optionalWordOfList k)
          (optionalWordOfList t)))

/-- Contextual list form of the first guarded Lemma 20.12 move (20.6d). -/
theorem listDerives20_6d
    (before after : List Nat) (x y : Nat)
    (h k t : List Nat) :
    ListDerives
      (before ++ [x] ++ h ++ [y] ++ k ++ [x] ++ t ++ [y] ++ after)
      (before ++ [x] ++ k ++ [x] ++ h ++ [y] ++ t ++ [y] ++ after) := by
  simpa only [pattern20_6dSource, pattern20_6dTarget,
    Word.toList_append, appendOptional_optionalWordOfList_toList,
    Word.toList_singleton, List.append_assoc, List.cons_append,
    List.nil_append, List.append_nil] using
      (listDerivesContextOfWord before after
        (derives20_6d (Word.singleton x) (Word.singleton y)
          (optionalWordOfList h) (optionalWordOfList k)
          (optionalWordOfList t)))

/-- Contextual list form of the second guarded Lemma 20.12 move (20.6e). -/
theorem listDerives20_6e
    (before after : List Nat) (x y : Nat)
    (h k t : List Nat) :
    ListDerives
      (before ++ [x] ++ h ++ [y] ++ k ++ [y] ++ t ++ [x] ++ after)
      (before ++ [x] ++ t ++ [x] ++ h ++ [y] ++ k ++ [y] ++ after) := by
  simpa only [pattern20_6eSource, pattern20_6eTarget,
    Word.toList_append, appendOptional_optionalWordOfList_toList,
    Word.toList_singleton, List.append_assoc, List.cons_append,
    List.nil_append, List.append_nil] using
      (listDerivesContextOfWord before after
        (derives20_6e (Word.singleton x) (Word.singleton y)
          (optionalWordOfList h) (optionalWordOfList k)
          (optionalWordOfList t)))

/-- Contextual list form of the exact three repeated-block swap (20.6f). -/
theorem listDerives20_6f
    (before after : List Nat) (x y z : Nat)
    (h a b c d : List Nat) :
    ListDerives
      (before ++ [x] ++ h ++ [x] ++ a ++ [y] ++ b ++ [y] ++
        c ++ [z] ++ d ++ [z] ++ after)
      (before ++ [x] ++ h ++ [x] ++ c ++ [z] ++ d ++ [z] ++
        a ++ [y] ++ b ++ [y] ++ after) := by
  simpa only [pattern20_6fSource, pattern20_6fTarget,
    Word.toList_append, appendOptional_optionalWordOfList_toList,
    Word.toList_singleton, List.append_assoc, List.cons_append,
    List.nil_append, List.append_nil] using
      (listDerivesContextOfWord before after
        (derives20_6f
          (Word.singleton x) (Word.singleton y) (Word.singleton z)
          (optionalWordOfList h) (optionalWordOfList a)
          (optionalWordOfList b) (optionalWordOfList c)
          (optionalWordOfList d)))

/-! ## Power capping -/

/-- One contextual contraction `x^4 → x^3`. -/
theorem listDerivesPowerContract
    (before after : List Nat) (x : Nat) :
    ListDerives
      (before ++ [x, x, x, x] ++ after)
      (before ++ [x, x, x] ++ after) := by
  simpa [List.append_assoc] using
    (listDerives20_6a before after x [] [])

/-- Cap an adjacent multiplicity at three. -/
def capThree (count : Nat) : Nat :=
  if count < 3 then count else 3

/-- Contract only an adjacent run to its exponent-three cap. -/
theorem listDerivesCapRunThree
    (before after : List Nat) (x : Nat) :
    ∀ count,
      ListDerives
        (before ++ List.replicate count x ++ after)
        (before ++ List.replicate (capThree count) x ++ after)
  | 0 => by
      simpa [capThree] using
        (S5_107.ListDerives.refl (basis := basis) (before ++ after))
  | 1 => by
      simpa [capThree] using
        (S5_107.ListDerives.refl (basis := basis)
          (before ++ [x] ++ after))
  | 2 => by
      simpa [capThree] using
        (S5_107.ListDerives.refl (basis := basis)
          (before ++ [x, x] ++ after))
  | 3 => by
      simpa [capThree] using
        (S5_107.ListDerives.refl (basis := basis)
          (before ++ [x, x, x] ++ after))
  | count + 4 => by
      have first :
          ListDerives
            (before ++ List.replicate (count + 4) x ++ after)
            (before ++ List.replicate (count + 3) x ++ after) := by
        simpa [List.replicate_succ, List.append_assoc] using
          listDerivesPowerContract before
            (List.replicate count x ++ after) x
      exact first.trans
        (listDerivesCapRunThree before after x (count + 3))

/-- Symmetric expansion from the exponent-three representative. -/
theorem listDerivesExpandRunFromCapThree
    (before after : List Nat) (x count : Nat) :
    ListDerives
      (before ++ List.replicate (capThree count) x ++ after)
      (before ++ List.replicate count x ++ after) :=
  (listDerivesCapRunThree before after x count).symm

/-! ## Permuting `s_i x` blocks -/

/-- Render contexts `s_i` with a displayed terminal `x` after each one. -/
def renderTerminatedBlocks (x : Nat) : List (List Nat) → List Nat
  | [] => []
  | block :: blocks =>
      block ++ [x] ++ renderTerminatedBlocks x blocks

private theorem listDerivesPermuteXBlocksCore
    (x : Nat) {source target : List (List Nat)}
    (permutation : source.Perm target) :
    ListDerives
      ([x] ++ renderTerminatedBlocks x source)
      ([x] ++ renderTerminatedBlocks x target) := by
  induction permutation with
  | nil =>
      exact S5_107.ListDerives.refl _
  | cons head _ ih =>
      have lifted :=
        S5_107.ListDerives.context ([x] ++ head) [] ih
      simpa [renderTerminatedBlocks, List.append_assoc] using lifted
  | swap left right suffix =>
      have swapped :=
        (listDerives20_6b [] (renderTerminatedBlocks x suffix)
          x left right).symm
      simpa [renderTerminatedBlocks, List.append_assoc] using swapped
  | trans _ _ first second =>
      exact first.trans second

/-- Permute complete `s_i x` blocks under arbitrary outer context.
This does not permute letters inside any `s_i`. -/
theorem listDerivesPermuteXBlocks
    (before after : List Nat) (x : Nat)
    {source target : List (List Nat)}
    (permutation : source.Perm target) :
    ListDerives
      (before ++ [x] ++ renderTerminatedBlocks x source ++ after)
      (before ++ [x] ++ renderTerminatedBlocks x target ++ after) := by
  have core := listDerivesPermuteXBlocksCore x permutation
  simpa [List.append_assoc] using
    S5_107.ListDerives.context before after core

/-! ## Descriptive guarded endpoints for normalization -/

/-- Move the `t y` block to the head of the displayed two-block tail.
The repeated `x H x` head remains an explicit guard. -/
theorem listDerivesMoveTerminatedBlockToHead20_6c
    (before after : List Nat) (x y : Nat)
    (h k t : List Nat) :
    ListDerives
      (before ++ [x] ++ h ++ [x] ++ k ++ [y] ++ t ++ [y] ++ after)
      (before ++ [x] ++ h ++ [x] ++ t ++ [y] ++ k ++ [y] ++ after) :=
  listDerives20_6c before after x y h k t

/-- First exact guarded move used in the Lemma 20.12 repair. -/
theorem listDerivesGuardedMove20_6d
    (before after : List Nat) (x y : Nat)
    (h k t : List Nat) :
    ListDerives
      (before ++ [x] ++ h ++ [y] ++ k ++ [x] ++ t ++ [y] ++ after)
      (before ++ [x] ++ k ++ [x] ++ h ++ [y] ++ t ++ [y] ++ after) :=
  listDerives20_6d before after x y h k t

/-- Second exact guarded move used in the Lemma 20.12 repair. -/
theorem listDerivesGuardedMove20_6e
    (before after : List Nat) (x y : Nat)
    (h k t : List Nat) :
    ListDerives
      (before ++ [x] ++ h ++ [y] ++ k ++ [y] ++ t ++ [x] ++ after)
      (before ++ [x] ++ t ++ [x] ++ h ++ [y] ++ k ++ [y] ++ after) :=
  listDerives20_6e before after x y h k t

/-- Swap the second and third displayed repeated blocks after `x H x`.
No swap is exposed without all three repeated-block anchors. -/
theorem listDerivesSwapRepeatedBlocks20_6f
    (before after : List Nat) (x y z : Nat)
    (h a b c d : List Nat) :
    ListDerives
      (before ++ [x] ++ h ++ [x] ++ a ++ [y] ++ b ++ [y] ++
        c ++ [z] ++ d ++ [z] ++ after)
      (before ++ [x] ++ h ++ [x] ++ c ++ [z] ++ d ++ [z] ++
        a ++ [y] ++ b ++ [y] ++ after) :=
  listDerives20_6f before after x y z h a b c d

end SemigroupBasis.CoRoots.Order6LeeZhangProposition20_7E4
