import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Opposite

/-! Fixed law translations for the exact msg-0436 and msg-0442 lists.
Only finite lists and fixed positive-word endpoints are supplied.
No all-word completeness or separation field is authored. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.ApprovedB3BridgesFinite

open SemigroupBasis

namespace Cap303

def approvedBasisLaw0 : Identity Nat := ⟨⟨3, [3]⟩, ⟨3, [3, 3]⟩⟩
def approvedBasisLaw1 : Identity Nat := ⟨⟨2, [3, 3]⟩, ⟨3, [2, 3]⟩⟩
def approvedBasisLaw2 : Identity Nat := ⟨⟨2, [3, 1, 0]⟩, ⟨3, [2, 1, 0]⟩⟩

def approvedBasis : List (Identity Nat) :=
  [approvedBasisLaw0, approvedBasisLaw1, approvedBasisLaw2]

def priorBasisLaw0 : Identity Nat := ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def priorBasisLaw1 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩
def priorBasisLaw2 : Identity Nat := ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩
def priorBasisLaw3 : Identity Nat := ⟨⟨0, [1, 2, 3]⟩, ⟨1, [0, 2, 3]⟩⟩

def priorBasis : List (Identity Nat) :=
  [priorBasisLaw0, priorBasisLaw1, priorBasisLaw2, priorBasisLaw3]

theorem approvedDerivesLaw0 :
    Derives approvedBasis priorBasisLaw0.lhs priorBasisLaw0.rhs := by
  have step0 : Derives approvedBasis ⟨0, [0]⟩ ⟨0, [0, 0]⟩ := by
    have base : Derives approvedBasis approvedBasisLaw0.lhs approvedBasisLaw0.rhs :=
      Derives.fromBasis (by simp [approvedBasis])
    let substitution : Nat → Word Nat := fun
      | 3 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [approvedBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem approvedOppositeDerivesLaw0 :
    Derives (reversedBasis approvedBasis)
      priorBasisLaw0.reversed.lhs priorBasisLaw0.reversed.rhs :=
  approvedDerivesLaw0.reverse

theorem approvedDerivesLaw1 :
    Derives approvedBasis priorBasisLaw1.lhs priorBasisLaw1.rhs := by
  have step0 : Derives approvedBasis ⟨0, [1, 0]⟩ ⟨1, [0, 0]⟩ := by
    have base : Derives approvedBasis approvedBasisLaw1.lhs approvedBasisLaw1.rhs :=
      Derives.fromBasis (by simp [approvedBasis])
    let substitution : Nat → Word Nat := fun
      | 2 => ⟨1, []⟩
      | 3 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [approvedBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem approvedOppositeDerivesLaw1 :
    Derives (reversedBasis approvedBasis)
      priorBasisLaw1.reversed.lhs priorBasisLaw1.reversed.rhs :=
  approvedDerivesLaw1.reverse

theorem approvedDerivesLaw2 :
    Derives approvedBasis priorBasisLaw2.lhs priorBasisLaw2.rhs := by
  have step0 : Derives approvedBasis ⟨0, [1, 2, 0]⟩ ⟨1, [0, 2, 0]⟩ := by
    have base : Derives approvedBasis approvedBasisLaw2.lhs approvedBasisLaw2.rhs :=
      Derives.fromBasis (by simp [approvedBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨2, []⟩
      | 2 => ⟨0, []⟩
      | 3 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [approvedBasisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives approvedBasis ⟨1, [0, 2, 0]⟩ ⟨1, [2, 0, 0]⟩ := by
    have base : Derives approvedBasis approvedBasisLaw1.lhs approvedBasisLaw1.rhs :=
      Derives.fromBasis (by simp [approvedBasis])
    let substitution : Nat → Word Nat := fun
      | 2 => ⟨2, []⟩
      | 3 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [approvedBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨1, []⟩ instantiated)
  have step2 : Derives approvedBasis ⟨1, [2, 0, 0]⟩ ⟨2, [1, 0, 0]⟩ := by
    have base : Derives approvedBasis approvedBasisLaw2.lhs approvedBasisLaw2.rhs :=
      Derives.fromBasis (by simp [approvedBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, []⟩
      | 2 => ⟨1, []⟩
      | 3 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [approvedBasisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step3 : Derives approvedBasis ⟨2, [1, 0, 0]⟩ ⟨2, [0, 1, 0]⟩ := by
    have base : Derives approvedBasis approvedBasisLaw1.lhs approvedBasisLaw1.rhs :=
      Derives.fromBasis (by simp [approvedBasis])
    let substitution : Nat → Word Nat := fun
      | 2 => ⟨1, []⟩
      | 3 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [approvedBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨2, []⟩ instantiated)
  have step4 : Derives approvedBasis ⟨2, [0, 1, 0]⟩ ⟨0, [2, 1, 0]⟩ := by
    have base : Derives approvedBasis approvedBasisLaw2.lhs approvedBasisLaw2.rhs :=
      Derives.fromBasis (by simp [approvedBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨2, []⟩
      | 3 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [approvedBasisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (Derives.trans step3 (step4))))

theorem approvedOppositeDerivesLaw2 :
    Derives (reversedBasis approvedBasis)
      priorBasisLaw2.reversed.lhs priorBasisLaw2.reversed.rhs :=
  approvedDerivesLaw2.reverse

theorem approvedDerivesLaw3 :
    Derives approvedBasis priorBasisLaw3.lhs priorBasisLaw3.rhs := by
  have step0 : Derives approvedBasis ⟨0, [1, 2, 3]⟩ ⟨1, [0, 2, 3]⟩ := by
    have base : Derives approvedBasis approvedBasisLaw2.lhs approvedBasisLaw2.rhs :=
      Derives.fromBasis (by simp [approvedBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨3, []⟩
      | 1 => ⟨2, []⟩
      | 2 => ⟨0, []⟩
      | 3 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [approvedBasisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem approvedOppositeDerivesLaw3 :
    Derives (reversedBasis approvedBasis)
      priorBasisLaw3.reversed.lhs priorBasisLaw3.reversed.rhs :=
  approvedDerivesLaw3.reverse

/-- Membership in this explicit finite target list only. -/
theorem priorLawsInApproved : FiniteCertificate.DerivesAll approvedBasis priorBasis := by
  intro identity member
  simp only [priorBasis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact approvedDerivesLaw0
  · exact approvedDerivesLaw1
  · exact approvedDerivesLaw2
  · exact approvedDerivesLaw3

theorem priorDerivesLaw0 :
    Derives priorBasis approvedBasisLaw0.lhs approvedBasisLaw0.rhs := by
  have step0 : Derives priorBasis ⟨3, [3]⟩ ⟨3, [3, 3]⟩ := by
    have base : Derives priorBasis priorBasisLaw0.lhs priorBasisLaw0.rhs :=
      Derives.fromBasis (by simp [priorBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨3, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [priorBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem priorOppositeDerivesLaw0 :
    Derives (reversedBasis priorBasis)
      approvedBasisLaw0.reversed.lhs approvedBasisLaw0.reversed.rhs :=
  priorDerivesLaw0.reverse

theorem priorDerivesLaw1 :
    Derives priorBasis approvedBasisLaw1.lhs approvedBasisLaw1.rhs := by
  have step0 : Derives priorBasis ⟨2, [3, 3]⟩ ⟨3, [2, 3]⟩ := by
    have base : Derives priorBasis priorBasisLaw1.lhs priorBasisLaw1.rhs :=
      Derives.fromBasis (by simp [priorBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨3, []⟩
      | 1 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [priorBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem priorOppositeDerivesLaw1 :
    Derives (reversedBasis priorBasis)
      approvedBasisLaw1.reversed.lhs approvedBasisLaw1.reversed.rhs :=
  priorDerivesLaw1.reverse

theorem priorDerivesLaw2 :
    Derives priorBasis approvedBasisLaw2.lhs approvedBasisLaw2.rhs := by
  have step0 : Derives priorBasis ⟨2, [3, 1, 0]⟩ ⟨3, [2, 1, 0]⟩ := by
    have base : Derives priorBasis priorBasisLaw3.lhs priorBasisLaw3.rhs :=
      Derives.fromBasis (by simp [priorBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | 1 => ⟨3, []⟩
      | 2 => ⟨1, []⟩
      | 3 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [priorBasisLaw3, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem priorOppositeDerivesLaw2 :
    Derives (reversedBasis priorBasis)
      approvedBasisLaw2.reversed.lhs approvedBasisLaw2.reversed.rhs :=
  priorDerivesLaw2.reverse

/-- Membership in this explicit finite target list only. -/
theorem approvedLawsInPrior : FiniteCertificate.DerivesAll priorBasis approvedBasis := by
  intro identity member
  simp only [approvedBasis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact priorDerivesLaw0
  · exact priorDerivesLaw1
  · exact priorDerivesLaw2

end Cap303

namespace Rank078

def approvedBasisLaw0 : Identity Nat := ⟨⟨3, [1, 2]⟩, ⟨3, [2, 1]⟩⟩
def approvedBasisLaw1 : Identity Nat := ⟨⟨2, [2, 3]⟩, ⟨3, [3, 2]⟩⟩
def approvedBasisLaw2 : Identity Nat := ⟨⟨0, [1, 2, 3]⟩, ⟨0, [1, 1, 2, 3]⟩⟩

def approvedBasis : List (Identity Nat) :=
  [approvedBasisLaw0, approvedBasisLaw1, approvedBasisLaw2]

def priorBasisLaw0 : Identity Nat := ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩
def priorBasisLaw1 : Identity Nat := ⟨⟨0, [0, 1]⟩, ⟨1, [0, 1]⟩⟩
def priorBasisLaw2 : Identity Nat := ⟨⟨0, [1, 1, 1]⟩, ⟨0, [1, 1, 1, 1]⟩⟩
def priorBasisLaw3 : Identity Nat := ⟨⟨0, [1, 1, 1, 2]⟩, ⟨0, [1, 1, 2]⟩⟩
def priorBasisLaw4 : Identity Nat := ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩
def priorBasisLaw5 : Identity Nat := ⟨⟨0, [1, 2, 3]⟩, ⟨0, [1, 1, 2, 3]⟩⟩

def priorBasis : List (Identity Nat) :=
  [priorBasisLaw0, priorBasisLaw1, priorBasisLaw2, priorBasisLaw3, priorBasisLaw4, priorBasisLaw5]

theorem approvedDerivesLaw0 :
    Derives approvedBasis priorBasisLaw0.lhs priorBasisLaw0.rhs := by
  have step0 : Derives approvedBasis ⟨0, [0, 1]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives approvedBasis approvedBasisLaw0.lhs approvedBasisLaw0.rhs :=
      Derives.fromBasis (by simp [approvedBasis])
    let substitution : Nat → Word Nat := fun
      | 1 => ⟨0, []⟩
      | 2 => ⟨1, []⟩
      | 3 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [approvedBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem approvedOppositeDerivesLaw0 :
    Derives (reversedBasis approvedBasis)
      priorBasisLaw0.reversed.lhs priorBasisLaw0.reversed.rhs :=
  approvedDerivesLaw0.reverse

theorem approvedDerivesLaw1 :
    Derives approvedBasis priorBasisLaw1.lhs priorBasisLaw1.rhs := by
  have step0 : Derives approvedBasis ⟨0, [0, 1]⟩ ⟨1, [1, 0]⟩ := by
    have base : Derives approvedBasis approvedBasisLaw1.lhs approvedBasisLaw1.rhs :=
      Derives.fromBasis (by simp [approvedBasis])
    let substitution : Nat → Word Nat := fun
      | 2 => ⟨0, []⟩
      | 3 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [approvedBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives approvedBasis ⟨1, [1, 0]⟩ ⟨1, [0, 1]⟩ := by
    have base : Derives approvedBasis approvedBasisLaw0.lhs approvedBasisLaw0.rhs :=
      Derives.fromBasis (by simp [approvedBasis])
    let substitution : Nat → Word Nat := fun
      | 1 => ⟨1, []⟩
      | 2 => ⟨0, []⟩
      | 3 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [approvedBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

theorem approvedOppositeDerivesLaw1 :
    Derives (reversedBasis approvedBasis)
      priorBasisLaw1.reversed.lhs priorBasisLaw1.reversed.rhs :=
  approvedDerivesLaw1.reverse

theorem approvedDerivesLaw2 :
    Derives approvedBasis priorBasisLaw2.lhs priorBasisLaw2.rhs := by
  have step0 : Derives approvedBasis ⟨0, [1, 1, 1]⟩ ⟨0, [1, 1, 1, 1]⟩ := by
    have base : Derives approvedBasis approvedBasisLaw2.lhs approvedBasisLaw2.rhs :=
      Derives.fromBasis (by simp [approvedBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨1, []⟩
      | 3 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [approvedBasisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem approvedOppositeDerivesLaw2 :
    Derives (reversedBasis approvedBasis)
      priorBasisLaw2.reversed.lhs priorBasisLaw2.reversed.rhs :=
  approvedDerivesLaw2.reverse

theorem approvedDerivesLaw3 :
    Derives approvedBasis priorBasisLaw3.lhs priorBasisLaw3.rhs := by
  have step0 : Derives approvedBasis ⟨0, [1, 1, 1, 2]⟩ ⟨0, [1, 1, 2]⟩ := by
    have base : Derives approvedBasis approvedBasisLaw2.lhs approvedBasisLaw2.rhs :=
      Derives.fromBasis (by simp [approvedBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨1, []⟩
      | 3 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [approvedBasisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem approvedOppositeDerivesLaw3 :
    Derives (reversedBasis approvedBasis)
      priorBasisLaw3.reversed.lhs priorBasisLaw3.reversed.rhs :=
  approvedDerivesLaw3.reverse

theorem approvedDerivesLaw4 :
    Derives approvedBasis priorBasisLaw4.lhs priorBasisLaw4.rhs := by
  have step0 : Derives approvedBasis ⟨0, [1, 2]⟩ ⟨0, [2, 1]⟩ := by
    have base : Derives approvedBasis approvedBasisLaw0.lhs approvedBasisLaw0.rhs :=
      Derives.fromBasis (by simp [approvedBasis])
    let substitution : Nat → Word Nat := fun
      | 1 => ⟨1, []⟩
      | 2 => ⟨2, []⟩
      | 3 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [approvedBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem approvedOppositeDerivesLaw4 :
    Derives (reversedBasis approvedBasis)
      priorBasisLaw4.reversed.lhs priorBasisLaw4.reversed.rhs :=
  approvedDerivesLaw4.reverse

theorem approvedDerivesLaw5 :
    Derives approvedBasis priorBasisLaw5.lhs priorBasisLaw5.rhs := by
  have step0 : Derives approvedBasis ⟨0, [1, 2, 3]⟩ ⟨0, [1, 1, 2, 3]⟩ := by
    have base : Derives approvedBasis approvedBasisLaw2.lhs approvedBasisLaw2.rhs :=
      Derives.fromBasis (by simp [approvedBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨2, []⟩
      | 3 => ⟨3, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [approvedBasisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem approvedOppositeDerivesLaw5 :
    Derives (reversedBasis approvedBasis)
      priorBasisLaw5.reversed.lhs priorBasisLaw5.reversed.rhs :=
  approvedDerivesLaw5.reverse

/-- Membership in this explicit finite target list only. -/
theorem priorLawsInApproved : FiniteCertificate.DerivesAll approvedBasis priorBasis := by
  intro identity member
  simp only [priorBasis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact approvedDerivesLaw0
  · exact approvedDerivesLaw1
  · exact approvedDerivesLaw2
  · exact approvedDerivesLaw3
  · exact approvedDerivesLaw4
  · exact approvedDerivesLaw5

theorem priorDerivesLaw0 :
    Derives priorBasis approvedBasisLaw0.lhs approvedBasisLaw0.rhs := by
  have step0 : Derives priorBasis ⟨3, [1, 2]⟩ ⟨3, [2, 1]⟩ := by
    have base : Derives priorBasis priorBasisLaw4.lhs priorBasisLaw4.rhs :=
      Derives.fromBasis (by simp [priorBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨3, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [priorBasisLaw4, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem priorOppositeDerivesLaw0 :
    Derives (reversedBasis priorBasis)
      approvedBasisLaw0.reversed.lhs approvedBasisLaw0.reversed.rhs :=
  priorDerivesLaw0.reverse

theorem priorDerivesLaw1 :
    Derives priorBasis approvedBasisLaw1.lhs approvedBasisLaw1.rhs := by
  have step0 : Derives priorBasis ⟨2, [2, 3]⟩ ⟨3, [2, 3]⟩ := by
    have base : Derives priorBasis priorBasisLaw1.lhs priorBasisLaw1.rhs :=
      Derives.fromBasis (by simp [priorBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | 1 => ⟨3, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [priorBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives priorBasis ⟨3, [2, 3]⟩ ⟨3, [3, 2]⟩ := by
    have base : Derives priorBasis priorBasisLaw4.lhs priorBasisLaw4.rhs :=
      Derives.fromBasis (by simp [priorBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨3, []⟩
      | 1 => ⟨2, []⟩
      | 2 => ⟨3, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [priorBasisLaw4, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

theorem priorOppositeDerivesLaw1 :
    Derives (reversedBasis priorBasis)
      approvedBasisLaw1.reversed.lhs approvedBasisLaw1.reversed.rhs :=
  priorDerivesLaw1.reverse

theorem priorDerivesLaw2 :
    Derives priorBasis approvedBasisLaw2.lhs approvedBasisLaw2.rhs := by
  have step0 : Derives priorBasis ⟨0, [1, 2, 3]⟩ ⟨0, [1, 1, 2, 3]⟩ := by
    have base : Derives priorBasis priorBasisLaw5.lhs priorBasisLaw5.rhs :=
      Derives.fromBasis (by simp [priorBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨2, []⟩
      | 3 => ⟨3, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [priorBasisLaw5, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem priorOppositeDerivesLaw2 :
    Derives (reversedBasis priorBasis)
      approvedBasisLaw2.reversed.lhs approvedBasisLaw2.reversed.rhs :=
  priorDerivesLaw2.reverse

/-- Membership in this explicit finite target list only. -/
theorem approvedLawsInPrior : FiniteCertificate.DerivesAll priorBasis approvedBasis := by
  intro identity member
  simp only [approvedBasis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact priorDerivesLaw0
  · exact priorDerivesLaw1
  · exact priorDerivesLaw2

end Rank078

end SemigroupBasis.CoRoots.Order6Sunday.ApprovedB3BridgesFinite
