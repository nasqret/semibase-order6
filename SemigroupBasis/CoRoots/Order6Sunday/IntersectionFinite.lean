import SemigroupBasis.Subdirect
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.CatalogueOrder3
import SemigroupBasis.Generated.CatalogueOrder5Part01
import SemigroupBasis.Generated.CatalogueOrder5Part03
import SemigroupBasis.Generated.CatalogueOrder5Part07

/-! Residual intersection tail: fixed laws, matched-condition derivations, and finite witnesses. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.IntersectionFinite

open SemigroupBasis

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

namespace SigmaFirst

def basisLaw0 : Identity Nat := ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def basisLaw1 : Identity Nat := ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩
def basisLaw2 : Identity Nat := ⟨⟨0, [1, 1, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

def basis : List (Identity Nat) :=
  [basisLaw0, basisLaw1, basisLaw2]

def leftBasisLaw0 : Identity Nat := ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def leftBasisLaw1 : Identity Nat := ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def leftBasis : List (Identity Nat) :=
  [leftBasisLaw0, leftBasisLaw1]

theorem leftDerivesLaw0 :
    Derives leftBasis basisLaw0.lhs basisLaw0.rhs := by
  have step0 : Derives leftBasis ⟨0, [0]⟩ ⟨0, [0, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  exact step0

theorem leftDerivesLaw1 :
    Derives leftBasis basisLaw1.lhs basisLaw1.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, []⟩
      | 2 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem leftDerivesLaw2 :
    Derives leftBasis basisLaw2.lhs basisLaw2.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 1, 2]⟩ ⟨0, [2, 1, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, [1]⟩
      | 2 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

/-- 3 fixed displayed-law instances. -/
theorem displayedInLeftBasis : FiniteCertificate.DerivesAll leftBasis basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact leftDerivesLaw0
  · exact leftDerivesLaw1
  · exact leftDerivesLaw2

def rightBasisLaw0 : Identity Nat := ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def rightBasisLaw1 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1]⟩⟩
def rightBasisLaw2 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def rightBasis : List (Identity Nat) :=
  [rightBasisLaw0, rightBasisLaw1, rightBasisLaw2]

theorem rightDerivesLaw0 :
    Derives rightBasis basisLaw0.lhs basisLaw0.rhs := by
  have step0 : Derives rightBasis ⟨0, [0]⟩ ⟨0, [0, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem rightDerivesLaw1 :
    Derives rightBasis basisLaw1.lhs basisLaw1.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem rightDerivesLaw2 :
    Derives rightBasis basisLaw2.lhs basisLaw2.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 1, 2]⟩ ⟨0, [1, 2, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  have step1 : Derives rightBasis ⟨0, [1, 2, 1]⟩ ⟨0, [2, 1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw2.lhs rightBasisLaw2.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw2, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  exact Derives.trans step0 (step1)

/-- 3 fixed displayed-law instances. -/
theorem displayedInRightBasis : FiniteCertificate.DerivesAll rightBasis basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact rightDerivesLaw0
  · exact rightDerivesLaw1
  · exact rightDerivesLaw2

def conditionBasisLaw0 : Identity Nat := ⟨⟨0, [1, 2, 1]⟩, ⟨0, [1, 1, 2]⟩⟩
def conditionBasisLaw1 : Identity Nat := ⟨⟨0, [0, 0]⟩, ⟨0, [0]⟩⟩
def conditionBasisLaw2 : Identity Nat := ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0]⟩⟩
def conditionBasisLaw3 : Identity Nat := ⟨⟨0, [1, 0, 0]⟩, ⟨0, [1, 0]⟩⟩
def conditionBasisLaw4 : Identity Nat := ⟨⟨0, [1, 0, 2, 0]⟩, ⟨0, [1, 2, 0]⟩⟩
def conditionBasisLaw5 : Identity Nat := ⟨⟨0, [0, 0, 0]⟩, ⟨0, [0]⟩⟩
def conditionBasisLaw6 : Identity Nat := ⟨⟨0, [0, 0, 1, 0]⟩, ⟨0, [1, 0]⟩⟩
def conditionBasisLaw7 : Identity Nat := ⟨⟨0, [1, 0, 1]⟩, ⟨0, [0, 1, 1]⟩⟩
def conditionBasisLaw8 : Identity Nat := ⟨⟨0, [1, 1, 2]⟩, ⟨0, [2, 1, 1]⟩⟩
def conditionBasisLaw9 : Identity Nat := ⟨⟨0, [0, 0, 0, 0, 0, 0, 0, 1]⟩, ⟨0, [0, 1]⟩⟩
def conditionBasisLaw10 : Identity Nat := ⟨⟨0, [1, 1, 1, 1, 1, 1, 1, 1]⟩, ⟨0, [1, 1]⟩⟩
def conditionBasisLaw11 : Identity Nat := ⟨⟨0, [0, 0, 0, 0, 0, 0, 1, 0]⟩, ⟨0, [1, 0]⟩⟩
def conditionBasisLaw12 : Identity Nat := ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩
def conditionBasisLaw13 : Identity Nat := ⟨⟨0, [1, 0, 2, 0]⟩, ⟨0, [0, 1, 2, 0]⟩⟩
def conditionBasisLaw14 : Identity Nat := ⟨⟨0, [2, 0, 1, 0]⟩, ⟨0, [2, 1, 0]⟩⟩
def conditionBasisLaw15 : Identity Nat := ⟨⟨1, [0, 0, 0, 0, 0, 0, 0, 0]⟩, ⟨1, [0, 0]⟩⟩
def conditionBasisLaw16 : Identity Nat := ⟨⟨1, [1, 1, 1, 1, 1, 1, 1, 0]⟩, ⟨1, [1, 0]⟩⟩
def conditionBasisLaw17 : Identity Nat := ⟨⟨0, [1, 0, 0, 0, 0, 0, 0, 0]⟩, ⟨0, [1, 0]⟩⟩
def conditionBasisLaw18 : Identity Nat := ⟨⟨0, [1, 0, 0]⟩, ⟨0, [0, 1, 0]⟩⟩
def conditionBasisLaw19 : Identity Nat := ⟨⟨0, [2, 0, 1, 0]⟩, ⟨0, [2, 1, 0, 0]⟩⟩
def conditionBasisLaw20 : Identity Nat := ⟨⟨1, [0, 1, 0]⟩, ⟨1, [1, 0, 0]⟩⟩

def conditionBasis : List (Identity Nat) :=
  [conditionBasisLaw0, conditionBasisLaw1, conditionBasisLaw2, conditionBasisLaw3, conditionBasisLaw4, conditionBasisLaw5, conditionBasisLaw6, conditionBasisLaw7, conditionBasisLaw8, conditionBasisLaw9, conditionBasisLaw10, conditionBasisLaw11, conditionBasisLaw12, conditionBasisLaw13, conditionBasisLaw14, conditionBasisLaw15, conditionBasisLaw16, conditionBasisLaw17, conditionBasisLaw18, conditionBasisLaw19, conditionBasisLaw20]

theorem conditionDerivesLaw0 :
    Derives basis conditionBasisLaw0.lhs conditionBasisLaw0.rhs := by
  have step0 : Derives basis ⟨0, [1, 2, 1]⟩ ⟨0, [1, 1, 2]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  exact step0

theorem conditionDerivesLaw1 :
    Derives basis conditionBasisLaw1.lhs conditionBasisLaw1.rhs := by
  have step0 : Derives basis ⟨0, [0, 0]⟩ ⟨0, [0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem conditionDerivesLaw2 :
    Derives basis conditionBasisLaw2.lhs conditionBasisLaw2.rhs := by
  have step0 : Derives basis ⟨0, [0, 1, 0]⟩ ⟨0, [0, 0, 1]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives basis ⟨0, [0, 0, 1]⟩ ⟨0, [0, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  have step2 : Derives basis ⟨0, [0, 1]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (step2))

theorem conditionDerivesLaw3 :
    Derives basis conditionBasisLaw3.lhs conditionBasisLaw3.rhs := by
  have step0 : Derives basis ⟨0, [1, 0, 0]⟩ ⟨0, [0, 0, 1]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, []⟩
      | 2 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives basis ⟨0, [0, 0, 1]⟩ ⟨0, [0, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  have step2 : Derives basis ⟨0, [0, 1]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (step2))

theorem conditionDerivesLaw4 :
    Derives basis conditionBasisLaw4.lhs conditionBasisLaw4.rhs := by
  have step0 : Derives basis ⟨0, [1, 0, 2, 0]⟩ ⟨0, [0, 1, 0, 2]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, [0, 2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives basis ⟨0, [0, 1, 0, 2]⟩ ⟨0, [0, 0, 1, 2]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, []⟩)
  have step2 : Derives basis ⟨0, [0, 0, 1, 2]⟩ ⟨0, [0, 1, 2]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [2]⟩)
  have step3 : Derives basis ⟨0, [0, 1, 2]⟩ ⟨0, [1, 2, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, [2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (step3)))

theorem conditionDerivesLaw5 :
    Derives basis conditionBasisLaw5.lhs conditionBasisLaw5.rhs := by
  have step0 : Derives basis ⟨0, [0, 0, 0]⟩ ⟨0, [0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  have step1 : Derives basis ⟨0, [0, 0]⟩ ⟨0, [0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

theorem conditionDerivesLaw6 :
    Derives basis conditionBasisLaw6.lhs conditionBasisLaw6.rhs := by
  have step0 : Derives basis ⟨0, [0, 0, 1, 0]⟩ ⟨0, [0, 1, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [0]⟩)
  have step1 : Derives basis ⟨0, [0, 1, 0]⟩ ⟨0, [0, 0, 1]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step2 : Derives basis ⟨0, [0, 0, 1]⟩ ⟨0, [0, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  have step3 : Derives basis ⟨0, [0, 1]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (step3)))

theorem conditionDerivesLaw7 :
    Derives basis conditionBasisLaw7.lhs conditionBasisLaw7.rhs := by
  have step0 : Derives basis ⟨0, [1, 0, 1]⟩ ⟨0, [0, 1, 1]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  exact step0

theorem conditionDerivesLaw8 :
    Derives basis conditionBasisLaw8.lhs conditionBasisLaw8.rhs := by
  have step0 : Derives basis ⟨0, [1, 1, 2]⟩ ⟨0, [2, 1, 1]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem conditionDerivesLaw9 :
    Derives basis conditionBasisLaw9.lhs conditionBasisLaw9.rhs := by
  have step0 : Derives basis ⟨0, [0, 0, 0, 0, 0, 0, 0, 1]⟩ ⟨0, [0, 0, 0, 0, 0, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, [0, 1]⟩)
  have step1 : Derives basis ⟨0, [0, 0, 0, 0, 0, 1]⟩ ⟨0, [0, 0, 0, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  have step2 : Derives basis ⟨0, [0, 0, 0, 1]⟩ ⟨0, [0, 0, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, [1]⟩)
  have step3 : Derives basis ⟨0, [0, 0, 1]⟩ ⟨0, [0, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (step3)))

theorem conditionDerivesLaw10 :
    Derives basis conditionBasisLaw10.lhs conditionBasisLaw10.rhs := by
  have step0 : Derives basis ⟨0, [1, 1, 1, 1, 1, 1, 1, 1]⟩ ⟨0, [1, 1, 1, 1, 1, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, []⟩ instantiated) ⟨1, [1]⟩)
  have step1 : Derives basis ⟨0, [1, 1, 1, 1, 1, 1]⟩ ⟨0, [1, 1, 1, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  have step2 : Derives basis ⟨0, [1, 1, 1, 1]⟩ ⟨0, [1, 1, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, []⟩ instantiated) ⟨1, []⟩)
  have step3 : Derives basis ⟨0, [1, 1, 1]⟩ ⟨0, [1, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (step3)))

theorem conditionDerivesLaw11 :
    Derives basis conditionBasisLaw11.lhs conditionBasisLaw11.rhs := by
  have step0 : Derives basis ⟨0, [0, 0, 0, 0, 0, 0, 1, 0]⟩ ⟨0, [0, 0, 0, 0, 1, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, [1, 0]⟩)
  have step1 : Derives basis ⟨0, [0, 0, 0, 0, 1, 0]⟩ ⟨0, [0, 0, 0, 1, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, [0, 1, 0]⟩)
  have step2 : Derives basis ⟨0, [0, 0, 0, 1, 0]⟩ ⟨0, [0, 0, 1, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, [1, 0]⟩)
  have step3 : Derives basis ⟨0, [0, 0, 1, 0]⟩ ⟨0, [0, 1, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [0]⟩)
  have step4 : Derives basis ⟨0, [0, 1, 0]⟩ ⟨0, [0, 0, 1]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step5 : Derives basis ⟨0, [0, 0, 1]⟩ ⟨0, [0, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  have step6 : Derives basis ⟨0, [0, 1]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (Derives.trans step3 (Derives.trans step4 (Derives.trans step5 (step6))))))

theorem conditionDerivesLaw12 :
    Derives basis conditionBasisLaw12.lhs conditionBasisLaw12.rhs := by
  have step0 : Derives basis ⟨0, [0, 1, 0]⟩ ⟨0, [0, 0, 1]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives basis ⟨0, [0, 0, 1]⟩ ⟨0, [0, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  have step2 : Derives basis ⟨0, [0, 1]⟩ ⟨0, [0, 0, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  have step3 : Derives basis ⟨0, [0, 0, 1]⟩ ⟨0, [1, 0, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, []⟩
      | 2 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (step3)))

theorem conditionDerivesLaw13 :
    Derives basis conditionBasisLaw13.lhs conditionBasisLaw13.rhs := by
  have step0 : Derives basis ⟨0, [1, 0, 2, 0]⟩ ⟨0, [0, 1, 0, 2]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, [0, 2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives basis ⟨0, [0, 1, 0, 2]⟩ ⟨0, [0, 0, 1, 2]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, []⟩)
  have step2 : Derives basis ⟨0, [0, 0, 1, 2]⟩ ⟨0, [0, 1, 2]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [2]⟩)
  have step3 : Derives basis ⟨0, [0, 1, 2]⟩ ⟨0, [0, 0, 1, 2]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [2]⟩)
  have step4 : Derives basis ⟨0, [0, 0, 1, 2]⟩ ⟨0, [0, 1, 2, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1, 2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (Derives.trans step3 (step4))))

theorem conditionDerivesLaw14 :
    Derives basis conditionBasisLaw14.lhs conditionBasisLaw14.rhs := by
  have step0 : Derives basis ⟨0, [2, 0, 1, 0]⟩ ⟨0, [0, 2, 0, 1]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨2, [0, 1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives basis ⟨0, [0, 2, 0, 1]⟩ ⟨0, [0, 0, 2, 1]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  have step2 : Derives basis ⟨0, [0, 0, 2, 1]⟩ ⟨0, [0, 2, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, [1]⟩)
  have step3 : Derives basis ⟨0, [0, 2, 1]⟩ ⟨0, [2, 1, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨2, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (step3)))

theorem conditionDerivesLaw15 :
    Derives basis conditionBasisLaw15.lhs conditionBasisLaw15.rhs := by
  have step0 : Derives basis ⟨1, [0, 0, 0, 0, 0, 0, 0, 0]⟩ ⟨1, [0, 0, 0, 0, 0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨1, []⟩ instantiated) ⟨0, [0]⟩)
  have step1 : Derives basis ⟨1, [0, 0, 0, 0, 0, 0]⟩ ⟨1, [0, 0, 0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨1, []⟩ instantiated)
  have step2 : Derives basis ⟨1, [0, 0, 0, 0]⟩ ⟨1, [0, 0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨1, []⟩ instantiated) ⟨0, []⟩)
  have step3 : Derives basis ⟨1, [0, 0, 0]⟩ ⟨1, [0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨1, []⟩ instantiated)
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (step3)))

theorem conditionDerivesLaw16 :
    Derives basis conditionBasisLaw16.lhs conditionBasisLaw16.rhs := by
  have step0 : Derives basis ⟨1, [1, 1, 1, 1, 1, 1, 1, 0]⟩ ⟨1, [1, 1, 1, 1, 1, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [1, 0]⟩)
  have step1 : Derives basis ⟨1, [1, 1, 1, 1, 1, 0]⟩ ⟨1, [1, 1, 1, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  have step2 : Derives basis ⟨1, [1, 1, 1, 0]⟩ ⟨1, [1, 1, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [0]⟩)
  have step3 : Derives basis ⟨1, [1, 1, 0]⟩ ⟨1, [1, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  have step4 : Derives basis ⟨1, [1, 0]⟩ ⟨1, [0, 1]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step5 : Derives basis ⟨1, [0, 1]⟩ ⟨1, [1, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (Derives.trans step3 (Derives.trans step4 (step5)))))

theorem conditionDerivesLaw17 :
    Derives basis conditionBasisLaw17.lhs conditionBasisLaw17.rhs := by
  have step0 : Derives basis ⟨0, [1, 0, 0, 0, 0, 0, 0, 0]⟩ ⟨0, [1, 0, 0, 0, 0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, [1]⟩ instantiated) ⟨0, []⟩)
  have step1 : Derives basis ⟨0, [1, 0, 0, 0, 0, 0]⟩ ⟨0, [1, 0, 0, 0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, [1]⟩ instantiated) ⟨0, [0]⟩)
  have step2 : Derives basis ⟨0, [1, 0, 0, 0, 0]⟩ ⟨0, [1, 0, 0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, [1]⟩ instantiated) ⟨0, []⟩)
  have step3 : Derives basis ⟨0, [1, 0, 0, 0]⟩ ⟨0, [1, 0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [1]⟩ instantiated)
  have step4 : Derives basis ⟨0, [1, 0, 0]⟩ ⟨0, [0, 0, 1]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, []⟩
      | 2 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step5 : Derives basis ⟨0, [0, 0, 1]⟩ ⟨0, [0, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  have step6 : Derives basis ⟨0, [0, 1]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (Derives.trans step3 (Derives.trans step4 (Derives.trans step5 (step6))))))

theorem conditionDerivesLaw18 :
    Derives basis conditionBasisLaw18.lhs conditionBasisLaw18.rhs := by
  have step0 : Derives basis ⟨0, [1, 0, 0]⟩ ⟨0, [0, 0, 1]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, []⟩
      | 2 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives basis ⟨0, [0, 0, 1]⟩ ⟨0, [0, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  have step2 : Derives basis ⟨0, [0, 1]⟩ ⟨0, [0, 0, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  have step3 : Derives basis ⟨0, [0, 0, 1]⟩ ⟨0, [0, 1, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (step3)))

theorem conditionDerivesLaw19 :
    Derives basis conditionBasisLaw19.lhs conditionBasisLaw19.rhs := by
  have step0 : Derives basis ⟨0, [2, 0, 1, 0]⟩ ⟨0, [0, 2, 0, 1]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨2, [0, 1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives basis ⟨0, [0, 2, 0, 1]⟩ ⟨0, [0, 0, 2, 1]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  have step2 : Derives basis ⟨0, [0, 0, 2, 1]⟩ ⟨0, [0, 2, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, [1]⟩)
  have step3 : Derives basis ⟨0, [0, 2, 1]⟩ ⟨0, [0, 0, 2, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, [1]⟩)
  have step4 : Derives basis ⟨0, [0, 0, 2, 1]⟩ ⟨0, [2, 1, 0, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, []⟩
      | 2 => ⟨2, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (Derives.trans step3 (step4))))

theorem conditionDerivesLaw20 :
    Derives basis conditionBasisLaw20.lhs conditionBasisLaw20.rhs := by
  have step0 : Derives basis ⟨1, [0, 1, 0]⟩ ⟨1, [0, 0, 1]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨1, []⟩ instantiated)
  have step1 : Derives basis ⟨1, [0, 0, 1]⟩ ⟨1, [1, 0, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

/-- Fixed positive identities from the actual signed condition matches. -/
theorem conditionsInDisplayed : FiniteCertificate.DerivesAll basis conditionBasis := by
  intro identity member
  simp only [conditionBasis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact conditionDerivesLaw0
  · exact conditionDerivesLaw1
  · exact conditionDerivesLaw2
  · exact conditionDerivesLaw3
  · exact conditionDerivesLaw4
  · exact conditionDerivesLaw5
  · exact conditionDerivesLaw6
  · exact conditionDerivesLaw7
  · exact conditionDerivesLaw8
  · exact conditionDerivesLaw9
  · exact conditionDerivesLaw10
  · exact conditionDerivesLaw11
  · exact conditionDerivesLaw12
  · exact conditionDerivesLaw13
  · exact conditionDerivesLaw14
  · exact conditionDerivesLaw15
  · exact conditionDerivesLaw16
  · exact conditionDerivesLaw17
  · exact conditionDerivesLaw18
  · exact conditionDerivesLaw19
  · exact conditionDerivesLaw20

private theorem leftModelsLaw0 : basisLaw0.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_15.table.semigroup := by
  have roundTrip : (basisLaw0.map toFinThree).map Fin.val = basisLaw0 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S3_15.table (basisLaw0.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw1 : basisLaw1.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_15.table.semigroup := by
  have roundTrip : (basisLaw1.map toFinThree).map Fin.val = basisLaw1 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S3_15.table (basisLaw1.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw2 : basisLaw2.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_15.table.semigroup := by
  have roundTrip : (basisLaw2.map toFinThree).map Fin.val = basisLaw2 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S3_15.table (basisLaw2.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem leftModels : Models SemigroupBasis.Generated.Catalogue.S3_15.table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact leftModelsLaw0
  · exact leftModelsLaw1
  · exact leftModelsLaw2

private theorem rightModelsLaw0 : basisLaw0.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_110.table.semigroup := by
  have roundTrip : (basisLaw0.map toFinThree).map Fin.val = basisLaw0 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_110.table (basisLaw0.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw1 : basisLaw1.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_110.table.semigroup := by
  have roundTrip : (basisLaw1.map toFinThree).map Fin.val = basisLaw1 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_110.table (basisLaw1.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw2 : basisLaw2.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_110.table.semigroup := by
  have roundTrip : (basisLaw2.map toFinThree).map Fin.val = basisLaw2 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_110.table (basisLaw2.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem rightModels : Models SemigroupBasis.Generated.Catalogue.S5_110.table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact rightModelsLaw0
  · exact rightModelsLaw1
  · exact rightModelsLaw2

namespace S6_3950

/-- Exact catalogue table SHA256 `c9b7db7943eefaafabe5cbcd34f5554adcd22f6520c2115fd3c3ffef35cdf024`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6)) else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)) else if a = 3 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6)) else if a = 4 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6)) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def ontoLeftMap (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (1 : Fin 3) else (2 : Fin 3)

def ontoLeftSection (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (4 : Fin 6) else (5 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S3_15.table.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (3 : Fin 5) else if a = 4 then (4 : Fin 5) else (4 : Fin 5)

def ontoRightSection (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (4 : Fin 6)

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_110.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.Catalogue.S3_15.table.semigroup SemigroupBasis.Generated.Catalogue.S5_110.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro a b
    exact by decide +revert

theorem models : Models table.semigroup basis := by
  intro identity member
  exact (pair.satisfiedBy_iff identity).mpr ⟨leftModels identity member, rightModels identity member⟩

def ontoLeftOpposite : SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S3_15.table.semigroup.opposite where
  toFun := ontoLeftMap
  map_mul := fun a b => ontoLeft.map_mul b a
  preimage := ontoLeftSection
  right_inverse := ontoLeft.right_inverse

def ontoRightOpposite : SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_110.table.semigroup.opposite where
  toFun := ontoRightMap
  map_mul := fun a b => ontoRight.map_mul b a
  preimage := ontoRightSection
  right_inverse := ontoRight.right_inverse

def pairOpposite : SubdirectPair table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_110.table.semigroup.opposite where
  left := ontoLeftOpposite
  right := ontoRightOpposite
  jointlyInjective := pair.jointlyInjective

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) :=
  models.oppositeReversed

theorem conditionModels : Models table.semigroup conditionBasis := by
  intro identity member
  exact Derives.sound models (conditionsInDisplayed _ member)

end S6_3950

end SigmaFirst

namespace SigmaMarker

def basisLaw0 : Identity Nat := ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def basisLaw1 : Identity Nat := ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩
def basisLaw2 : Identity Nat := ⟨⟨0, [0, 1, 1]⟩, ⟨1, [0, 0, 1]⟩⟩
def basisLaw3 : Identity Nat := ⟨⟨0, [1, 1, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

def basis : List (Identity Nat) :=
  [basisLaw0, basisLaw1, basisLaw2, basisLaw3]

def leftBasisLaw0 : Identity Nat := ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def leftBasisLaw1 : Identity Nat := ⟨⟨1, [0]⟩, ⟨1, [0, 0]⟩⟩
def leftBasisLaw2 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨1, [1, 0]⟩⟩
def leftBasisLaw3 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1]⟩⟩

def leftBasis : List (Identity Nat) :=
  [leftBasisLaw0, leftBasisLaw1, leftBasisLaw2, leftBasisLaw3]

theorem leftDerivesLaw0 :
    Derives leftBasis basisLaw0.lhs basisLaw0.rhs := by
  have step0 : Derives leftBasis ⟨0, [0]⟩ ⟨0, [0, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem leftDerivesLaw1 :
    Derives leftBasis basisLaw1.lhs basisLaw1.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw3.lhs leftBasisLaw3.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw3, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem leftDerivesLaw2 :
    Derives leftBasis basisLaw2.lhs basisLaw2.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 1]⟩ ⟨0, [0, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives leftBasis ⟨0, [0, 1]⟩ ⟨1, [0, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw2.lhs leftBasisLaw2.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step2 : Derives leftBasis ⟨1, [0, 1]⟩ ⟨1, [0, 0, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  exact Derives.trans step0 (Derives.trans step1 (step2))

theorem leftDerivesLaw3 :
    Derives leftBasis basisLaw3.lhs basisLaw3.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 1, 2]⟩ ⟨0, [1, 1, 1, 1, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, [1]⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, []⟩)
  have step1 : Derives leftBasis ⟨0, [1, 1, 1, 1, 2]⟩ ⟨0, [2, 1, 1, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw2.lhs leftBasisLaw2.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | 1 => ⟨1, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw2, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  have step2 : Derives leftBasis ⟨0, [2, 1, 1, 2]⟩ ⟨0, [2, 2, 1, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw3.lhs leftBasisLaw3.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | 1 => ⟨1, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw3, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  have step3 : Derives leftBasis ⟨0, [2, 2, 1, 1]⟩ ⟨0, [2, 1, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [1]⟩)
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (step3)))

/-- 4 fixed displayed-law instances. -/
theorem displayedInLeftBasis : FiniteCertificate.DerivesAll leftBasis basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact leftDerivesLaw0
  · exact leftDerivesLaw1
  · exact leftDerivesLaw2
  · exact leftDerivesLaw3

def rightBasisLaw0 : Identity Nat := ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def rightBasisLaw1 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1]⟩⟩
def rightBasisLaw2 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def rightBasis : List (Identity Nat) :=
  [rightBasisLaw0, rightBasisLaw1, rightBasisLaw2]

theorem rightDerivesLaw0 :
    Derives rightBasis basisLaw0.lhs basisLaw0.rhs := by
  have step0 : Derives rightBasis ⟨0, [0]⟩ ⟨0, [0, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem rightDerivesLaw1 :
    Derives rightBasis basisLaw1.lhs basisLaw1.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem rightDerivesLaw2 :
    Derives rightBasis basisLaw2.lhs basisLaw2.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 1]⟩ ⟨1, [0, 0, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw2.lhs rightBasisLaw2.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem rightDerivesLaw3 :
    Derives rightBasis basisLaw3.lhs basisLaw3.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 1, 2]⟩ ⟨0, [1, 2, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  have step1 : Derives rightBasis ⟨0, [1, 2, 1]⟩ ⟨0, [2, 1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw2.lhs rightBasisLaw2.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw2, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  exact Derives.trans step0 (step1)

/-- 4 fixed displayed-law instances. -/
theorem displayedInRightBasis : FiniteCertificate.DerivesAll rightBasis basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact rightDerivesLaw0
  · exact rightDerivesLaw1
  · exact rightDerivesLaw2
  · exact rightDerivesLaw3

def conditionBasisLaw0 : Identity Nat := ⟨⟨0, [1, 2, 1]⟩, ⟨0, [1, 1, 2]⟩⟩
def conditionBasisLaw1 : Identity Nat := ⟨⟨0, [0, 0]⟩, ⟨0, [0]⟩⟩
def conditionBasisLaw2 : Identity Nat := ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0]⟩⟩
def conditionBasisLaw3 : Identity Nat := ⟨⟨0, [1, 0, 0]⟩, ⟨0, [1, 0]⟩⟩
def conditionBasisLaw4 : Identity Nat := ⟨⟨0, [1, 0, 2, 0]⟩, ⟨0, [1, 2, 0]⟩⟩
def conditionBasisLaw5 : Identity Nat := ⟨⟨0, [0, 0, 0]⟩, ⟨0, [0]⟩⟩
def conditionBasisLaw6 : Identity Nat := ⟨⟨0, [0, 0, 1, 0]⟩, ⟨0, [1, 0]⟩⟩
def conditionBasisLaw7 : Identity Nat := ⟨⟨0, [1, 0, 1]⟩, ⟨0, [0, 1, 1]⟩⟩
def conditionBasisLaw8 : Identity Nat := ⟨⟨0, [1, 1, 2]⟩, ⟨0, [2, 1, 1]⟩⟩
def conditionBasisLaw9 : Identity Nat := ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩
def conditionBasisLaw10 : Identity Nat := ⟨⟨0, [0, 1, 2, 2]⟩, ⟨0, [1, 2, 2, 0]⟩⟩
def conditionBasisLaw11 : Identity Nat := ⟨⟨0, [0, 0, 0, 0, 0, 0, 0, 1]⟩, ⟨0, [0, 1]⟩⟩
def conditionBasisLaw12 : Identity Nat := ⟨⟨0, [1, 1, 1, 1, 1, 1, 1, 1]⟩, ⟨0, [1, 1]⟩⟩
def conditionBasisLaw13 : Identity Nat := ⟨⟨0, [0, 0, 0, 0, 0, 0, 1, 0]⟩, ⟨0, [1, 0]⟩⟩
def conditionBasisLaw14 : Identity Nat := ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩
def conditionBasisLaw15 : Identity Nat := ⟨⟨0, [1, 0, 2, 0]⟩, ⟨0, [0, 1, 2, 0]⟩⟩
def conditionBasisLaw16 : Identity Nat := ⟨⟨0, [2, 0, 1, 0]⟩, ⟨0, [2, 1, 0]⟩⟩
def conditionBasisLaw17 : Identity Nat := ⟨⟨1, [1, 0, 0]⟩, ⟨0, [0, 1, 1]⟩⟩
def conditionBasisLaw18 : Identity Nat := ⟨⟨2, [2, 1, 0, 0]⟩, ⟨0, [2, 2, 1, 0]⟩⟩
def conditionBasisLaw19 : Identity Nat := ⟨⟨1, [0, 0, 0, 0, 0, 0, 0, 0]⟩, ⟨1, [0, 0]⟩⟩
def conditionBasisLaw20 : Identity Nat := ⟨⟨1, [1, 1, 1, 1, 1, 1, 1, 0]⟩, ⟨1, [1, 0]⟩⟩
def conditionBasisLaw21 : Identity Nat := ⟨⟨0, [1, 0, 0, 0, 0, 0, 0, 0]⟩, ⟨0, [1, 0]⟩⟩
def conditionBasisLaw22 : Identity Nat := ⟨⟨0, [1, 0, 0]⟩, ⟨0, [0, 1, 0]⟩⟩
def conditionBasisLaw23 : Identity Nat := ⟨⟨0, [2, 0, 1, 0]⟩, ⟨0, [2, 1, 0, 0]⟩⟩
def conditionBasisLaw24 : Identity Nat := ⟨⟨1, [0, 1, 0]⟩, ⟨1, [1, 0, 0]⟩⟩

def conditionBasis : List (Identity Nat) :=
  [conditionBasisLaw0, conditionBasisLaw1, conditionBasisLaw2, conditionBasisLaw3, conditionBasisLaw4, conditionBasisLaw5, conditionBasisLaw6, conditionBasisLaw7, conditionBasisLaw8, conditionBasisLaw9, conditionBasisLaw10, conditionBasisLaw11, conditionBasisLaw12, conditionBasisLaw13, conditionBasisLaw14, conditionBasisLaw15, conditionBasisLaw16, conditionBasisLaw17, conditionBasisLaw18, conditionBasisLaw19, conditionBasisLaw20, conditionBasisLaw21, conditionBasisLaw22, conditionBasisLaw23, conditionBasisLaw24]

theorem conditionDerivesLaw0 :
    Derives basis conditionBasisLaw0.lhs conditionBasisLaw0.rhs := by
  have step0 : Derives basis ⟨0, [1, 2, 1]⟩ ⟨0, [1, 1, 2]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  exact step0

theorem conditionDerivesLaw1 :
    Derives basis conditionBasisLaw1.lhs conditionBasisLaw1.rhs := by
  have step0 : Derives basis ⟨0, [0, 0]⟩ ⟨0, [0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem conditionDerivesLaw2 :
    Derives basis conditionBasisLaw2.lhs conditionBasisLaw2.rhs := by
  have step0 : Derives basis ⟨0, [0, 1, 0]⟩ ⟨0, [0, 0, 1]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives basis ⟨0, [0, 0, 1]⟩ ⟨0, [0, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  have step2 : Derives basis ⟨0, [0, 1]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (step2))

theorem conditionDerivesLaw3 :
    Derives basis conditionBasisLaw3.lhs conditionBasisLaw3.rhs := by
  have step0 : Derives basis ⟨0, [1, 0, 0]⟩ ⟨0, [0, 0, 1]⟩ := by
    have base : Derives basis basisLaw3.lhs basisLaw3.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, []⟩
      | 2 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw3, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives basis ⟨0, [0, 0, 1]⟩ ⟨0, [0, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  have step2 : Derives basis ⟨0, [0, 1]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (step2))

theorem conditionDerivesLaw4 :
    Derives basis conditionBasisLaw4.lhs conditionBasisLaw4.rhs := by
  have step0 : Derives basis ⟨0, [1, 0, 2, 0]⟩ ⟨0, [0, 1, 0, 2]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, [0, 2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives basis ⟨0, [0, 1, 0, 2]⟩ ⟨0, [0, 0, 1, 2]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, []⟩)
  have step2 : Derives basis ⟨0, [0, 0, 1, 2]⟩ ⟨0, [0, 1, 2]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [2]⟩)
  have step3 : Derives basis ⟨0, [0, 1, 2]⟩ ⟨0, [1, 2, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, [2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (step3)))

theorem conditionDerivesLaw5 :
    Derives basis conditionBasisLaw5.lhs conditionBasisLaw5.rhs := by
  have step0 : Derives basis ⟨0, [0, 0, 0]⟩ ⟨0, [0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  have step1 : Derives basis ⟨0, [0, 0]⟩ ⟨0, [0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

theorem conditionDerivesLaw6 :
    Derives basis conditionBasisLaw6.lhs conditionBasisLaw6.rhs := by
  have step0 : Derives basis ⟨0, [0, 0, 1, 0]⟩ ⟨0, [0, 1, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [0]⟩)
  have step1 : Derives basis ⟨0, [0, 1, 0]⟩ ⟨0, [0, 0, 1]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step2 : Derives basis ⟨0, [0, 0, 1]⟩ ⟨0, [0, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  have step3 : Derives basis ⟨0, [0, 1]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (step3)))

theorem conditionDerivesLaw7 :
    Derives basis conditionBasisLaw7.lhs conditionBasisLaw7.rhs := by
  have step0 : Derives basis ⟨0, [1, 0, 1]⟩ ⟨0, [0, 1, 1]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  exact step0

theorem conditionDerivesLaw8 :
    Derives basis conditionBasisLaw8.lhs conditionBasisLaw8.rhs := by
  have step0 : Derives basis ⟨0, [1, 1, 2]⟩ ⟨0, [2, 1, 1]⟩ := by
    have base : Derives basis basisLaw3.lhs basisLaw3.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw3, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem conditionDerivesLaw9 :
    Derives basis conditionBasisLaw9.lhs conditionBasisLaw9.rhs := by
  have step0 : Derives basis ⟨0, [0, 1, 1]⟩ ⟨0, [1, 1, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives basis ⟨0, [1, 1, 0]⟩ ⟨1, [1, 0, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

theorem conditionDerivesLaw10 :
    Derives basis conditionBasisLaw10.lhs conditionBasisLaw10.rhs := by
  have step0 : Derives basis ⟨0, [0, 1, 2, 2]⟩ ⟨0, [1, 2, 2, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, [2, 2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem conditionDerivesLaw11 :
    Derives basis conditionBasisLaw11.lhs conditionBasisLaw11.rhs := by
  have step0 : Derives basis ⟨0, [0, 0, 0, 0, 0, 0, 0, 1]⟩ ⟨0, [0, 0, 0, 0, 0, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, [0, 1]⟩)
  have step1 : Derives basis ⟨0, [0, 0, 0, 0, 0, 1]⟩ ⟨0, [0, 0, 0, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  have step2 : Derives basis ⟨0, [0, 0, 0, 1]⟩ ⟨0, [0, 0, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, [1]⟩)
  have step3 : Derives basis ⟨0, [0, 0, 1]⟩ ⟨0, [0, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (step3)))

theorem conditionDerivesLaw12 :
    Derives basis conditionBasisLaw12.lhs conditionBasisLaw12.rhs := by
  have step0 : Derives basis ⟨0, [1, 1, 1, 1, 1, 1, 1, 1]⟩ ⟨0, [1, 1, 1, 1, 1, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, []⟩ instantiated) ⟨1, [1]⟩)
  have step1 : Derives basis ⟨0, [1, 1, 1, 1, 1, 1]⟩ ⟨0, [1, 1, 1, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  have step2 : Derives basis ⟨0, [1, 1, 1, 1]⟩ ⟨0, [1, 1, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, []⟩ instantiated) ⟨1, []⟩)
  have step3 : Derives basis ⟨0, [1, 1, 1]⟩ ⟨0, [1, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (step3)))

theorem conditionDerivesLaw13 :
    Derives basis conditionBasisLaw13.lhs conditionBasisLaw13.rhs := by
  have step0 : Derives basis ⟨0, [0, 0, 0, 0, 0, 0, 1, 0]⟩ ⟨0, [0, 0, 0, 0, 1, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, [1, 0]⟩)
  have step1 : Derives basis ⟨0, [0, 0, 0, 0, 1, 0]⟩ ⟨0, [0, 0, 0, 1, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, [0, 1, 0]⟩)
  have step2 : Derives basis ⟨0, [0, 0, 0, 1, 0]⟩ ⟨0, [0, 0, 1, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, [1, 0]⟩)
  have step3 : Derives basis ⟨0, [0, 0, 1, 0]⟩ ⟨0, [0, 1, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [0]⟩)
  have step4 : Derives basis ⟨0, [0, 1, 0]⟩ ⟨0, [0, 0, 1]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step5 : Derives basis ⟨0, [0, 0, 1]⟩ ⟨0, [0, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  have step6 : Derives basis ⟨0, [0, 1]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (Derives.trans step3 (Derives.trans step4 (Derives.trans step5 (step6))))))

theorem conditionDerivesLaw14 :
    Derives basis conditionBasisLaw14.lhs conditionBasisLaw14.rhs := by
  have step0 : Derives basis ⟨0, [0, 1, 0]⟩ ⟨0, [0, 0, 1]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives basis ⟨0, [0, 0, 1]⟩ ⟨0, [0, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  have step2 : Derives basis ⟨0, [0, 1]⟩ ⟨0, [0, 0, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  have step3 : Derives basis ⟨0, [0, 0, 1]⟩ ⟨0, [1, 0, 0]⟩ := by
    have base : Derives basis basisLaw3.lhs basisLaw3.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, []⟩
      | 2 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw3, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (step3)))

theorem conditionDerivesLaw15 :
    Derives basis conditionBasisLaw15.lhs conditionBasisLaw15.rhs := by
  have step0 : Derives basis ⟨0, [1, 0, 2, 0]⟩ ⟨0, [0, 1, 0, 2]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, [0, 2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives basis ⟨0, [0, 1, 0, 2]⟩ ⟨0, [0, 0, 1, 2]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, []⟩)
  have step2 : Derives basis ⟨0, [0, 0, 1, 2]⟩ ⟨0, [0, 1, 2]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [2]⟩)
  have step3 : Derives basis ⟨0, [0, 1, 2]⟩ ⟨0, [0, 0, 1, 2]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [2]⟩)
  have step4 : Derives basis ⟨0, [0, 0, 1, 2]⟩ ⟨0, [0, 1, 2, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1, 2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (Derives.trans step3 (step4))))

theorem conditionDerivesLaw16 :
    Derives basis conditionBasisLaw16.lhs conditionBasisLaw16.rhs := by
  have step0 : Derives basis ⟨0, [2, 0, 1, 0]⟩ ⟨0, [0, 2, 0, 1]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨2, [0, 1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives basis ⟨0, [0, 2, 0, 1]⟩ ⟨0, [0, 0, 2, 1]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  have step2 : Derives basis ⟨0, [0, 0, 2, 1]⟩ ⟨0, [0, 2, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, [1]⟩)
  have step3 : Derives basis ⟨0, [0, 2, 1]⟩ ⟨0, [2, 1, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨2, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (step3)))

theorem conditionDerivesLaw17 :
    Derives basis conditionBasisLaw17.lhs conditionBasisLaw17.rhs := by
  have step0 : Derives basis ⟨1, [1, 0, 0]⟩ ⟨0, [1, 1, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives basis ⟨0, [1, 1, 0]⟩ ⟨0, [0, 1, 1]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

theorem conditionDerivesLaw18 :
    Derives basis conditionBasisLaw18.lhs conditionBasisLaw18.rhs := by
  have step0 : Derives basis ⟨2, [2, 1, 0, 0]⟩ ⟨2, [0, 0, 2, 1]⟩ := by
    have base : Derives basis basisLaw3.lhs basisLaw3.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | 1 => ⟨0, []⟩
      | 2 => ⟨2, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw3, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives basis ⟨2, [0, 0, 2, 1]⟩ ⟨0, [0, 2, 2, 1]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  have step2 : Derives basis ⟨0, [0, 2, 2, 1]⟩ ⟨0, [0, 1, 2, 2]⟩ := by
    have base : Derives basis basisLaw3.lhs basisLaw3.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [0]⟩
      | 1 => ⟨2, []⟩
      | 2 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw3, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step3 : Derives basis ⟨0, [0, 1, 2, 2]⟩ ⟨0, [0, 2, 2, 1]⟩ := by
    have base : Derives basis basisLaw3.lhs basisLaw3.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [0]⟩
      | 1 => ⟨2, []⟩
      | 2 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw3, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step4 : Derives basis ⟨0, [0, 2, 2, 1]⟩ ⟨0, [2, 2, 1, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨2, [2, 1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (Derives.trans step3 (step4))))

theorem conditionDerivesLaw19 :
    Derives basis conditionBasisLaw19.lhs conditionBasisLaw19.rhs := by
  have step0 : Derives basis ⟨1, [0, 0, 0, 0, 0, 0, 0, 0]⟩ ⟨1, [0, 0, 0, 0, 0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨1, []⟩ instantiated) ⟨0, [0]⟩)
  have step1 : Derives basis ⟨1, [0, 0, 0, 0, 0, 0]⟩ ⟨1, [0, 0, 0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨1, []⟩ instantiated)
  have step2 : Derives basis ⟨1, [0, 0, 0, 0]⟩ ⟨1, [0, 0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨1, []⟩ instantiated) ⟨0, []⟩)
  have step3 : Derives basis ⟨1, [0, 0, 0]⟩ ⟨1, [0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨1, []⟩ instantiated)
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (step3)))

theorem conditionDerivesLaw20 :
    Derives basis conditionBasisLaw20.lhs conditionBasisLaw20.rhs := by
  have step0 : Derives basis ⟨1, [1, 1, 1, 1, 1, 1, 1, 0]⟩ ⟨1, [1, 1, 1, 1, 1, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [1, 0]⟩)
  have step1 : Derives basis ⟨1, [1, 1, 1, 1, 1, 0]⟩ ⟨1, [1, 1, 1, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  have step2 : Derives basis ⟨1, [1, 1, 1, 0]⟩ ⟨1, [1, 1, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [0]⟩)
  have step3 : Derives basis ⟨1, [1, 1, 0]⟩ ⟨1, [1, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  have step4 : Derives basis ⟨1, [1, 0]⟩ ⟨1, [0, 1]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step5 : Derives basis ⟨1, [0, 1]⟩ ⟨1, [1, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (Derives.trans step3 (Derives.trans step4 (step5)))))

theorem conditionDerivesLaw21 :
    Derives basis conditionBasisLaw21.lhs conditionBasisLaw21.rhs := by
  have step0 : Derives basis ⟨0, [1, 0, 0, 0, 0, 0, 0, 0]⟩ ⟨0, [1, 0, 0, 0, 0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, [1]⟩ instantiated) ⟨0, []⟩)
  have step1 : Derives basis ⟨0, [1, 0, 0, 0, 0, 0]⟩ ⟨0, [1, 0, 0, 0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, [1]⟩ instantiated) ⟨0, [0]⟩)
  have step2 : Derives basis ⟨0, [1, 0, 0, 0, 0]⟩ ⟨0, [1, 0, 0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, [1]⟩ instantiated) ⟨0, []⟩)
  have step3 : Derives basis ⟨0, [1, 0, 0, 0]⟩ ⟨0, [1, 0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [1]⟩ instantiated)
  have step4 : Derives basis ⟨0, [1, 0, 0]⟩ ⟨0, [0, 0, 1]⟩ := by
    have base : Derives basis basisLaw3.lhs basisLaw3.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, []⟩
      | 2 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw3, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step5 : Derives basis ⟨0, [0, 0, 1]⟩ ⟨0, [0, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  have step6 : Derives basis ⟨0, [0, 1]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (Derives.trans step3 (Derives.trans step4 (Derives.trans step5 (step6))))))

theorem conditionDerivesLaw22 :
    Derives basis conditionBasisLaw22.lhs conditionBasisLaw22.rhs := by
  have step0 : Derives basis ⟨0, [1, 0, 0]⟩ ⟨0, [0, 0, 1]⟩ := by
    have base : Derives basis basisLaw3.lhs basisLaw3.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, []⟩
      | 2 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw3, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives basis ⟨0, [0, 0, 1]⟩ ⟨0, [0, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  have step2 : Derives basis ⟨0, [0, 1]⟩ ⟨0, [0, 0, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  have step3 : Derives basis ⟨0, [0, 0, 1]⟩ ⟨0, [0, 1, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (step3)))

theorem conditionDerivesLaw23 :
    Derives basis conditionBasisLaw23.lhs conditionBasisLaw23.rhs := by
  have step0 : Derives basis ⟨0, [2, 0, 1, 0]⟩ ⟨0, [0, 2, 0, 1]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨2, [0, 1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives basis ⟨0, [0, 2, 0, 1]⟩ ⟨0, [0, 0, 2, 1]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  have step2 : Derives basis ⟨0, [0, 0, 2, 1]⟩ ⟨0, [0, 2, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, [1]⟩)
  have step3 : Derives basis ⟨0, [0, 2, 1]⟩ ⟨0, [0, 0, 2, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, [1]⟩)
  have step4 : Derives basis ⟨0, [0, 0, 2, 1]⟩ ⟨0, [2, 1, 0, 0]⟩ := by
    have base : Derives basis basisLaw3.lhs basisLaw3.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, []⟩
      | 2 => ⟨2, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw3, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (Derives.trans step3 (step4))))

theorem conditionDerivesLaw24 :
    Derives basis conditionBasisLaw24.lhs conditionBasisLaw24.rhs := by
  have step0 : Derives basis ⟨1, [0, 1, 0]⟩ ⟨1, [0, 0, 1]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨1, []⟩ instantiated)
  have step1 : Derives basis ⟨1, [0, 0, 1]⟩ ⟨0, [0, 1, 1]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step2 : Derives basis ⟨0, [0, 1, 1]⟩ ⟨0, [1, 1, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step3 : Derives basis ⟨0, [1, 1, 0]⟩ ⟨1, [1, 0, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (step3)))

/-- Fixed positive identities from the actual signed condition matches. -/
theorem conditionsInDisplayed : FiniteCertificate.DerivesAll basis conditionBasis := by
  intro identity member
  simp only [conditionBasis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact conditionDerivesLaw0
  · exact conditionDerivesLaw1
  · exact conditionDerivesLaw2
  · exact conditionDerivesLaw3
  · exact conditionDerivesLaw4
  · exact conditionDerivesLaw5
  · exact conditionDerivesLaw6
  · exact conditionDerivesLaw7
  · exact conditionDerivesLaw8
  · exact conditionDerivesLaw9
  · exact conditionDerivesLaw10
  · exact conditionDerivesLaw11
  · exact conditionDerivesLaw12
  · exact conditionDerivesLaw13
  · exact conditionDerivesLaw14
  · exact conditionDerivesLaw15
  · exact conditionDerivesLaw16
  · exact conditionDerivesLaw17
  · exact conditionDerivesLaw18
  · exact conditionDerivesLaw19
  · exact conditionDerivesLaw20
  · exact conditionDerivesLaw21
  · exact conditionDerivesLaw22
  · exact conditionDerivesLaw23
  · exact conditionDerivesLaw24

private def leftTable : FiniteTable where
  order := 3
  mul := fun a b => SemigroupBasis.Generated.Catalogue.S3_6.table.mul b a
  assoc := fun a b c => (SemigroupBasis.Generated.Catalogue.S3_6.table.assoc c b a).symm

private theorem leftModelsLaw0 : basisLaw0.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_6.table.semigroup.opposite := by
  have roundTrip : (basisLaw0.map toFinThree).map Fin.val = basisLaw0 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound leftTable (basisLaw0.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw1 : basisLaw1.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_6.table.semigroup.opposite := by
  have roundTrip : (basisLaw1.map toFinThree).map Fin.val = basisLaw1 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound leftTable (basisLaw1.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw2 : basisLaw2.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_6.table.semigroup.opposite := by
  have roundTrip : (basisLaw2.map toFinThree).map Fin.val = basisLaw2 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound leftTable (basisLaw2.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw3 : basisLaw3.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_6.table.semigroup.opposite := by
  have roundTrip : (basisLaw3.map toFinThree).map Fin.val = basisLaw3 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound leftTable (basisLaw3.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem leftModels : Models SemigroupBasis.Generated.Catalogue.S3_6.table.semigroup.opposite basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact leftModelsLaw0
  · exact leftModelsLaw1
  · exact leftModelsLaw2
  · exact leftModelsLaw3

private theorem rightModelsLaw0 : basisLaw0.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_110.table.semigroup := by
  have roundTrip : (basisLaw0.map toFinThree).map Fin.val = basisLaw0 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_110.table (basisLaw0.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw1 : basisLaw1.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_110.table.semigroup := by
  have roundTrip : (basisLaw1.map toFinThree).map Fin.val = basisLaw1 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_110.table (basisLaw1.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw2 : basisLaw2.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_110.table.semigroup := by
  have roundTrip : (basisLaw2.map toFinThree).map Fin.val = basisLaw2 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_110.table (basisLaw2.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw3 : basisLaw3.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_110.table.semigroup := by
  have roundTrip : (basisLaw3.map toFinThree).map Fin.val = basisLaw3 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_110.table (basisLaw3.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem rightModels : Models SemigroupBasis.Generated.Catalogue.S5_110.table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact rightModelsLaw0
  · exact rightModelsLaw1
  · exact rightModelsLaw2
  · exact rightModelsLaw3

namespace S6_1193

/-- Exact catalogue table SHA256 `0e6622cf2816429be4eb053ed7aabd40e1b864f913fa8d5581b33952eac5f24b`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6)) else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6)) else if a = 3 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6)) else if a = 4 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (4 : Fin 6)) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def ontoLeftMap (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (1 : Fin 3) else if a = 4 then (0 : Fin 3) else (2 : Fin 3)

def ontoLeftSection (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (3 : Fin 6) else (5 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S3_6.table.semigroup.opposite where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (2 : Fin 5) else if a = 4 then (3 : Fin 5) else (4 : Fin 5)

def ontoRightSection (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_110.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.Catalogue.S3_6.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_110.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro a b
    exact by decide +revert

theorem models : Models table.semigroup basis := by
  intro identity member
  exact (pair.satisfiedBy_iff identity).mpr ⟨leftModels identity member, rightModels identity member⟩

def ontoLeftOpposite : SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S3_6.table.semigroup.opposite.opposite where
  toFun := ontoLeftMap
  map_mul := fun a b => ontoLeft.map_mul b a
  preimage := ontoLeftSection
  right_inverse := ontoLeft.right_inverse

def ontoRightOpposite : SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_110.table.semigroup.opposite where
  toFun := ontoRightMap
  map_mul := fun a b => ontoRight.map_mul b a
  preimage := ontoRightSection
  right_inverse := ontoRight.right_inverse

def pairOpposite : SubdirectPair table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S3_6.table.semigroup.opposite.opposite SemigroupBasis.Generated.Catalogue.S5_110.table.semigroup.opposite where
  left := ontoLeftOpposite
  right := ontoRightOpposite
  jointlyInjective := pair.jointlyInjective

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) :=
  models.oppositeReversed

theorem conditionModels : Models table.semigroup conditionBasis := by
  intro identity member
  exact Derives.sound models (conditionsInDisplayed _ member)

end S6_1193

end SigmaMarker

namespace SigmaParity808

def basisLaw0 : Identity Nat := ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩
def basisLaw1 : Identity Nat := ⟨⟨0, [0, 1, 1, 2]⟩, ⟨0, [1, 1, 0, 2]⟩⟩
def basisLaw2 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def basis : List (Identity Nat) :=
  [basisLaw0, basisLaw1, basisLaw2]

def leftBasisLaw0 : Identity Nat := ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩
def leftBasisLaw1 : Identity Nat := ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def leftBasis : List (Identity Nat) :=
  [leftBasisLaw0, leftBasisLaw1]

theorem leftDerivesLaw0 :
    Derives leftBasis basisLaw0.lhs basisLaw0.rhs := by
  have step0 : Derives leftBasis ⟨0, [0]⟩ ⟨0, [0, 0, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  exact step0

theorem leftDerivesLaw1 :
    Derives leftBasis basisLaw1.lhs basisLaw1.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 1, 2]⟩ ⟨0, [1, 1, 0, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1, 1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, []⟩)
  exact step0

theorem leftDerivesLaw2 :
    Derives leftBasis basisLaw2.lhs basisLaw2.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 0]⟩ ⟨1, [0, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  exact step0

/-- 3 fixed displayed-law instances. -/
theorem displayedInLeftBasis : FiniteCertificate.DerivesAll leftBasis basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact leftDerivesLaw0
  · exact leftDerivesLaw1
  · exact leftDerivesLaw2

def rightBasisLaw0 : Identity Nat := ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def rightBasisLaw1 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩
def rightBasisLaw2 : Identity Nat := ⟨⟨0, [0, 1, 1, 2]⟩, ⟨0, [1, 1, 0, 2]⟩⟩

def rightBasis : List (Identity Nat) :=
  [rightBasisLaw0, rightBasisLaw1, rightBasisLaw2]

theorem rightDerivesLaw0 :
    Derives rightBasis basisLaw0.lhs basisLaw0.rhs := by
  have step0 : Derives rightBasis ⟨0, [0]⟩ ⟨0, [0, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives rightBasis ⟨0, [0, 0]⟩ ⟨0, [0, 0, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw1 :
    Derives rightBasis basisLaw1.lhs basisLaw1.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 1, 2]⟩ ⟨0, [1, 1, 0, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw2.lhs rightBasisLaw2.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem rightDerivesLaw2 :
    Derives rightBasis basisLaw2.lhs basisLaw2.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 0]⟩ ⟨1, [0, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

/-- 3 fixed displayed-law instances. -/
theorem displayedInRightBasis : FiniteCertificate.DerivesAll rightBasis basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact rightDerivesLaw0
  · exact rightDerivesLaw1
  · exact rightDerivesLaw2

def conditionBasisLaw0 : Identity Nat := ⟨⟨0, [0, 0, 0, 0, 0, 0, 0, 1]⟩, ⟨0, [0, 1]⟩⟩
def conditionBasisLaw1 : Identity Nat := ⟨⟨0, [1, 1, 1, 1, 1, 1, 1, 1]⟩, ⟨0, [1, 1]⟩⟩
def conditionBasisLaw2 : Identity Nat := ⟨⟨0, [0, 0, 0, 0, 0, 0, 1, 0]⟩, ⟨0, [1, 0]⟩⟩
def conditionBasisLaw3 : Identity Nat := ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩
def conditionBasisLaw4 : Identity Nat := ⟨⟨0, [1, 0, 2, 0]⟩, ⟨0, [0, 1, 2, 0]⟩⟩
def conditionBasisLaw5 : Identity Nat := ⟨⟨0, [1, 0, 1]⟩, ⟨0, [0, 1, 1]⟩⟩
def conditionBasisLaw6 : Identity Nat := ⟨⟨1, [2, 1, 0]⟩, ⟨2, [1, 1, 0]⟩⟩
def conditionBasisLaw7 : Identity Nat := ⟨⟨1, [0, 0, 0, 0, 0, 0, 0, 0]⟩, ⟨1, [0, 0]⟩⟩
def conditionBasisLaw8 : Identity Nat := ⟨⟨1, [1, 1, 1, 1, 1, 1, 1, 0]⟩, ⟨1, [1, 0]⟩⟩
def conditionBasisLaw9 : Identity Nat := ⟨⟨0, [1, 0, 0, 0, 0, 0, 0, 0]⟩, ⟨0, [1, 0]⟩⟩
def conditionBasisLaw10 : Identity Nat := ⟨⟨0, [1, 0, 0]⟩, ⟨0, [0, 1, 0]⟩⟩
def conditionBasisLaw11 : Identity Nat := ⟨⟨0, [2, 0, 1, 0]⟩, ⟨0, [2, 1, 0, 0]⟩⟩
def conditionBasisLaw12 : Identity Nat := ⟨⟨1, [0, 1, 0]⟩, ⟨1, [1, 0, 0]⟩⟩

def conditionBasis : List (Identity Nat) :=
  [conditionBasisLaw0, conditionBasisLaw1, conditionBasisLaw2, conditionBasisLaw3, conditionBasisLaw4, conditionBasisLaw5, conditionBasisLaw6, conditionBasisLaw7, conditionBasisLaw8, conditionBasisLaw9, conditionBasisLaw10, conditionBasisLaw11, conditionBasisLaw12]

theorem conditionDerivesLaw0 :
    Derives basis conditionBasisLaw0.lhs conditionBasisLaw0.rhs := by
  have step0 : Derives basis ⟨0, [0, 0, 0, 0, 0, 0, 0, 1]⟩ ⟨0, [0, 0, 0, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  have step1 : Derives basis ⟨0, [0, 0, 0, 1]⟩ ⟨0, [0, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  exact Derives.trans step0 (step1)

theorem conditionDerivesLaw1 :
    Derives basis conditionBasisLaw1.lhs conditionBasisLaw1.rhs := by
  have step0 : Derives basis ⟨0, [1, 1, 1, 1, 1, 1, 1, 1]⟩ ⟨0, [1, 1, 1, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  have step1 : Derives basis ⟨0, [1, 1, 1, 1]⟩ ⟨0, [1, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  exact Derives.trans step0 (step1)

theorem conditionDerivesLaw2 :
    Derives basis conditionBasisLaw2.lhs conditionBasisLaw2.rhs := by
  have step0 : Derives basis ⟨0, [0, 0, 0, 0, 0, 0, 1, 0]⟩ ⟨0, [0, 0, 0, 0, 1, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, [0, 0, 1, 0]⟩)
  have step1 : Derives basis ⟨0, [0, 0, 0, 0, 1, 0]⟩ ⟨0, [0, 0, 1, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, [1, 0]⟩)
  have step2 : Derives basis ⟨0, [0, 0, 1, 0]⟩ ⟨0, [0, 1, 0, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [0, 1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step3 : Derives basis ⟨0, [0, 1, 0, 0]⟩ ⟨1, [0, 0, 0, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [0]⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step4 : Derives basis ⟨1, [0, 0, 0, 0]⟩ ⟨1, [0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨1, []⟩ instantiated)
  have step5 : Derives basis ⟨1, [0, 0]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (Derives.trans step3 (Derives.trans step4 (step5)))))

theorem conditionDerivesLaw3 :
    Derives basis conditionBasisLaw3.lhs conditionBasisLaw3.rhs := by
  have step0 : Derives basis ⟨0, [0, 1, 0]⟩ ⟨0, [1, 0, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem conditionDerivesLaw4 :
    Derives basis conditionBasisLaw4.lhs conditionBasisLaw4.rhs := by
  have step0 : Derives basis ⟨0, [1, 0, 2, 0]⟩ ⟨0, [1, 2, 0, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [1]⟩ instantiated)
  have step1 : Derives basis ⟨0, [1, 2, 0, 0]⟩ ⟨0, [0, 1, 2, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1, 2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

theorem conditionDerivesLaw5 :
    Derives basis conditionBasisLaw5.lhs conditionBasisLaw5.rhs := by
  have step0 : Derives basis ⟨0, [1, 0, 1]⟩ ⟨0, [0, 1, 1]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  exact step0

theorem conditionDerivesLaw6 :
    Derives basis conditionBasisLaw6.lhs conditionBasisLaw6.rhs := by
  have step0 : Derives basis ⟨1, [2, 1, 0]⟩ ⟨2, [1, 1, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  exact step0

theorem conditionDerivesLaw7 :
    Derives basis conditionBasisLaw7.lhs conditionBasisLaw7.rhs := by
  have step0 : Derives basis ⟨1, [0, 0, 0, 0, 0, 0, 0, 0]⟩ ⟨1, [0, 0, 0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨1, []⟩ instantiated)
  have step1 : Derives basis ⟨1, [0, 0, 0, 0]⟩ ⟨1, [0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨1, []⟩ instantiated)
  have step2 : Derives basis ⟨1, [0, 0]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step3 : Derives basis ⟨0, [1, 0]⟩ ⟨1, [0, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (step3)))

theorem conditionDerivesLaw8 :
    Derives basis conditionBasisLaw8.lhs conditionBasisLaw8.rhs := by
  have step0 : Derives basis ⟨1, [1, 1, 1, 1, 1, 1, 1, 0]⟩ ⟨1, [1, 1, 1, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  have step1 : Derives basis ⟨1, [1, 1, 1, 0]⟩ ⟨1, [1, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  exact Derives.trans step0 (step1)

theorem conditionDerivesLaw9 :
    Derives basis conditionBasisLaw9.lhs conditionBasisLaw9.rhs := by
  have step0 : Derives basis ⟨0, [1, 0, 0, 0, 0, 0, 0, 0]⟩ ⟨0, [1, 0, 0, 0, 0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, [1]⟩ instantiated) ⟨0, [0, 0]⟩)
  have step1 : Derives basis ⟨0, [1, 0, 0, 0, 0, 0]⟩ ⟨0, [1, 0, 0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, [1]⟩ instantiated) ⟨0, []⟩)
  have step2 : Derives basis ⟨0, [1, 0, 0, 0]⟩ ⟨0, [0, 1, 0, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  have step3 : Derives basis ⟨0, [0, 1, 0, 0]⟩ ⟨0, [0, 0, 1, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [0, 1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step4 : Derives basis ⟨0, [0, 0, 1, 0]⟩ ⟨0, [0, 1, 0, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [0, 1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step5 : Derives basis ⟨0, [0, 1, 0, 0]⟩ ⟨1, [0, 0, 0, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [0]⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step6 : Derives basis ⟨1, [0, 0, 0, 0]⟩ ⟨1, [0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨1, []⟩ instantiated)
  have step7 : Derives basis ⟨1, [0, 0]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (Derives.trans step3 (Derives.trans step4 (Derives.trans step5 (Derives.trans step6 (step7)))))))

theorem conditionDerivesLaw10 :
    Derives basis conditionBasisLaw10.lhs conditionBasisLaw10.rhs := by
  have step0 : Derives basis ⟨0, [1, 0, 0]⟩ ⟨0, [0, 1, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem conditionDerivesLaw11 :
    Derives basis conditionBasisLaw11.lhs conditionBasisLaw11.rhs := by
  have step0 : Derives basis ⟨0, [2, 0, 1, 0]⟩ ⟨0, [2, 1, 0, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [2]⟩ instantiated)
  have step1 : Derives basis ⟨0, [2, 1, 0, 0]⟩ ⟨0, [0, 2, 1, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [2, 1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step2 : Derives basis ⟨0, [0, 2, 1, 0]⟩ ⟨0, [2, 1, 0, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [2, 1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (step2))

theorem conditionDerivesLaw12 :
    Derives basis conditionBasisLaw12.lhs conditionBasisLaw12.rhs := by
  have step0 : Derives basis ⟨1, [0, 1, 0]⟩ ⟨0, [1, 1, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  have step1 : Derives basis ⟨0, [1, 1, 0]⟩ ⟨1, [1, 0, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

/-- Fixed positive identities from the actual signed condition matches. -/
theorem conditionsInDisplayed : FiniteCertificate.DerivesAll basis conditionBasis := by
  intro identity member
  simp only [conditionBasis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact conditionDerivesLaw0
  · exact conditionDerivesLaw1
  · exact conditionDerivesLaw2
  · exact conditionDerivesLaw3
  · exact conditionDerivesLaw4
  · exact conditionDerivesLaw5
  · exact conditionDerivesLaw6
  · exact conditionDerivesLaw7
  · exact conditionDerivesLaw8
  · exact conditionDerivesLaw9
  · exact conditionDerivesLaw10
  · exact conditionDerivesLaw11
  · exact conditionDerivesLaw12

private theorem leftModelsLaw0 : basisLaw0.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_10.table.semigroup := by
  have roundTrip : (basisLaw0.map toFinThree).map Fin.val = basisLaw0 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S3_10.table (basisLaw0.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw1 : basisLaw1.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_10.table.semigroup := by
  have roundTrip : (basisLaw1.map toFinThree).map Fin.val = basisLaw1 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S3_10.table (basisLaw1.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw2 : basisLaw2.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_10.table.semigroup := by
  have roundTrip : (basisLaw2.map toFinThree).map Fin.val = basisLaw2 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S3_10.table (basisLaw2.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem leftModels : Models SemigroupBasis.Generated.Catalogue.S3_10.table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact leftModelsLaw0
  · exact leftModelsLaw1
  · exact leftModelsLaw2

private theorem rightModelsLaw0 : basisLaw0.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_808.table.semigroup := by
  have roundTrip : (basisLaw0.map toFinThree).map Fin.val = basisLaw0 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_808.table (basisLaw0.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw1 : basisLaw1.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_808.table.semigroup := by
  have roundTrip : (basisLaw1.map toFinThree).map Fin.val = basisLaw1 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_808.table (basisLaw1.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw2 : basisLaw2.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_808.table.semigroup := by
  have roundTrip : (basisLaw2.map toFinThree).map Fin.val = basisLaw2 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_808.table (basisLaw2.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem rightModels : Models SemigroupBasis.Generated.Catalogue.S5_808.table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact rightModelsLaw0
  · exact rightModelsLaw1
  · exact rightModelsLaw2

namespace S6_8866

/-- Exact catalogue table SHA256 `c48cf475319b140c6927c8084c059b7099cbaf9f10b9c5e4ea92e27ac33ecf07`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6)) else if a = 2 then (if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)) else if a = 3 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (3 : Fin 6)) else if a = 4 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (3 : Fin 6)) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def ontoLeftMap (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (1 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (0 : Fin 3) else (2 : Fin 3)

def ontoLeftSection (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else (5 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S3_10.table.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (0 : Fin 5) else if a = 3 then (2 : Fin 5) else if a = 4 then (3 : Fin 5) else (4 : Fin 5)

def ontoRightSection (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_808.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.Catalogue.S3_10.table.semigroup SemigroupBasis.Generated.Catalogue.S5_808.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro a b
    exact by decide +revert

theorem models : Models table.semigroup basis := by
  intro identity member
  exact (pair.satisfiedBy_iff identity).mpr ⟨leftModels identity member, rightModels identity member⟩

def ontoLeftOpposite : SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S3_10.table.semigroup.opposite where
  toFun := ontoLeftMap
  map_mul := fun a b => ontoLeft.map_mul b a
  preimage := ontoLeftSection
  right_inverse := ontoLeft.right_inverse

def ontoRightOpposite : SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_808.table.semigroup.opposite where
  toFun := ontoRightMap
  map_mul := fun a b => ontoRight.map_mul b a
  preimage := ontoRightSection
  right_inverse := ontoRight.right_inverse

def pairOpposite : SubdirectPair table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S3_10.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_808.table.semigroup.opposite where
  left := ontoLeftOpposite
  right := ontoRightOpposite
  jointlyInjective := pair.jointlyInjective

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) :=
  models.oppositeReversed

theorem conditionModels : Models table.semigroup conditionBasis := by
  intro identity member
  exact Derives.sound models (conditionsInDisplayed _ member)

end S6_8866

namespace S6_8877

/-- Exact catalogue table SHA256 `857890d21078e3e5b0c95a679c31f8411b8d2896bca86b89dedf8d9f25028cb4`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6)) else if a = 2 then (if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)) else if a = 3 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6)) else if a = 4 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

private theorem modelsLaw0 : basisLaw0.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw0.map toFinThree).map Fin.val = basisLaw0 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw0.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem modelsLaw1 : basisLaw1.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw1.map toFinThree).map Fin.val = basisLaw1 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw1.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem modelsLaw2 : basisLaw2.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw2.map toFinThree).map Fin.val = basisLaw2 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw2.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact modelsLaw0
  · exact modelsLaw1
  · exact modelsLaw2

def rootHom0Map (a : Fin 6) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (3 : Fin 6) else (4 : Fin 6)

def rootHom0 : Hom S6_8866.table.semigroup table.semigroup where
  toFun := rootHom0Map
  map_mul := by decide

def rootHom0Opposite : Hom S6_8866.table.semigroup.opposite table.semigroup.opposite where
  toFun := rootHom0.toFun
  map_mul := fun a b => rootHom0.map_mul b a

def rootHom1Map (a : Fin 6) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (4 : Fin 6) else if a = 4 then (5 : Fin 6) else (4 : Fin 6)

def rootHom1 : Hom S6_8866.table.semigroup table.semigroup where
  toFun := rootHom1Map
  map_mul := by decide

def rootHom1Opposite : Hom S6_8866.table.semigroup.opposite table.semigroup.opposite where
  toFun := rootHom1.toFun
  map_mul := fun a b => rootHom1.map_mul b a

def rootHomFamily (i : Fin 2) : Hom S6_8866.table.semigroup table.semigroup :=
  if i = 0 then rootHom0 else rootHom1

/-- Finite 2-coordinate root-to-leaf embedding. -/
def rootIntoPower : Embedding S6_8866.table.semigroup (table.semigroup.pi (Fin 2)) :=
  Embedding.ofSeparatingHoms rootHomFamily (by decide)

def rootHomFamilyOpposite (i : Fin 2) : Hom S6_8866.table.semigroup.opposite table.semigroup.opposite :=
  if i = 0 then rootHom0Opposite else rootHom1Opposite

/-- Finite 2-coordinate root-to-leaf embedding. -/
def rootOppositeIntoPower : Embedding S6_8866.table.semigroup.opposite (table.semigroup.opposite.pi (Fin 2)) :=
  Embedding.ofSeparatingHoms rootHomFamilyOpposite (by decide)

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) :=
  models.oppositeReversed

theorem conditionModels : Models table.semigroup conditionBasis := by
  intro identity member
  exact Derives.sound models (conditionsInDisplayed _ member)

end S6_8877

namespace S6_9010

/-- Exact catalogue table SHA256 `e4d60eb6d60e1c04f347c8ac6c79daf14466bd409522c6cebdc0220732398132`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6)) else if a = 2 then (if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6)) else if a = 3 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (3 : Fin 6)) else if a = 4 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (3 : Fin 6)) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def ontoLeftMap (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (1 : Fin 3) else if a = 2 then (1 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (0 : Fin 3) else (2 : Fin 3)

def ontoLeftSection (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S3_10.table.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (1 : Fin 5) else if a = 3 then (2 : Fin 5) else if a = 4 then (3 : Fin 5) else (4 : Fin 5)

def ontoRightSection (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_808.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.Catalogue.S3_10.table.semigroup SemigroupBasis.Generated.Catalogue.S5_808.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro a b
    exact by decide +revert

theorem models : Models table.semigroup basis := by
  intro identity member
  exact (pair.satisfiedBy_iff identity).mpr ⟨leftModels identity member, rightModels identity member⟩

def ontoLeftOpposite : SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S3_10.table.semigroup.opposite where
  toFun := ontoLeftMap
  map_mul := fun a b => ontoLeft.map_mul b a
  preimage := ontoLeftSection
  right_inverse := ontoLeft.right_inverse

def ontoRightOpposite : SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_808.table.semigroup.opposite where
  toFun := ontoRightMap
  map_mul := fun a b => ontoRight.map_mul b a
  preimage := ontoRightSection
  right_inverse := ontoRight.right_inverse

def pairOpposite : SubdirectPair table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S3_10.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_808.table.semigroup.opposite where
  left := ontoLeftOpposite
  right := ontoRightOpposite
  jointlyInjective := pair.jointlyInjective

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) :=
  models.oppositeReversed

theorem conditionModels : Models table.semigroup conditionBasis := by
  intro identity member
  exact Derives.sound models (conditionsInDisplayed _ member)

end S6_9010

namespace S6_9020

/-- Exact catalogue table SHA256 `66d3dacdbd044a89465b393faf2c58d4f67fbf7eef77cc9e85328b9648e7c6a1`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6)) else if a = 2 then (if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)) else if a = 3 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6)) else if a = 4 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

private theorem modelsLaw0 : basisLaw0.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw0.map toFinThree).map Fin.val = basisLaw0 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw0.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem modelsLaw1 : basisLaw1.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw1.map toFinThree).map Fin.val = basisLaw1 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw1.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem modelsLaw2 : basisLaw2.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw2.map toFinThree).map Fin.val = basisLaw2 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw2.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact modelsLaw0
  · exact modelsLaw1
  · exact modelsLaw2

def rootHom0Map (a : Fin 6) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (3 : Fin 6) else (4 : Fin 6)

def rootHom0 : Hom S6_9010.table.semigroup table.semigroup where
  toFun := rootHom0Map
  map_mul := by decide

def rootHom0Opposite : Hom S6_9010.table.semigroup.opposite table.semigroup.opposite where
  toFun := rootHom0.toFun
  map_mul := fun a b => rootHom0.map_mul b a

def rootHom1Map (a : Fin 6) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (4 : Fin 6) else if a = 4 then (5 : Fin 6) else (4 : Fin 6)

def rootHom1 : Hom S6_9010.table.semigroup table.semigroup where
  toFun := rootHom1Map
  map_mul := by decide

def rootHom1Opposite : Hom S6_9010.table.semigroup.opposite table.semigroup.opposite where
  toFun := rootHom1.toFun
  map_mul := fun a b => rootHom1.map_mul b a

def rootHomFamily (i : Fin 2) : Hom S6_9010.table.semigroup table.semigroup :=
  if i = 0 then rootHom0 else rootHom1

/-- Finite 2-coordinate root-to-leaf embedding. -/
def rootIntoPower : Embedding S6_9010.table.semigroup (table.semigroup.pi (Fin 2)) :=
  Embedding.ofSeparatingHoms rootHomFamily (by decide)

def rootHomFamilyOpposite (i : Fin 2) : Hom S6_9010.table.semigroup.opposite table.semigroup.opposite :=
  if i = 0 then rootHom0Opposite else rootHom1Opposite

/-- Finite 2-coordinate root-to-leaf embedding. -/
def rootOppositeIntoPower : Embedding S6_9010.table.semigroup.opposite (table.semigroup.opposite.pi (Fin 2)) :=
  Embedding.ofSeparatingHoms rootHomFamilyOpposite (by decide)

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) :=
  models.oppositeReversed

theorem conditionModels : Models table.semigroup conditionBasis := by
  intro identity member
  exact Derives.sound models (conditionsInDisplayed _ member)

end S6_9020

end SigmaParity808

namespace SigmaParity844

def basisLaw0 : Identity Nat := ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩
def basisLaw1 : Identity Nat := ⟨⟨0, [0, 1, 1, 2]⟩, ⟨0, [1, 1, 0, 2]⟩⟩
def basisLaw2 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def basis : List (Identity Nat) :=
  [basisLaw0, basisLaw1, basisLaw2]

def leftBasisLaw0 : Identity Nat := ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩
def leftBasisLaw1 : Identity Nat := ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def leftBasis : List (Identity Nat) :=
  [leftBasisLaw0, leftBasisLaw1]

theorem leftDerivesLaw0 :
    Derives leftBasis basisLaw0.lhs basisLaw0.rhs := by
  have step0 : Derives leftBasis ⟨0, [0]⟩ ⟨0, [0, 0, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  exact step0

theorem leftDerivesLaw1 :
    Derives leftBasis basisLaw1.lhs basisLaw1.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 1, 2]⟩ ⟨0, [1, 1, 0, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1, 1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, []⟩)
  exact step0

theorem leftDerivesLaw2 :
    Derives leftBasis basisLaw2.lhs basisLaw2.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 0]⟩ ⟨1, [0, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  exact step0

/-- 3 fixed displayed-law instances. -/
theorem displayedInLeftBasis : FiniteCertificate.DerivesAll leftBasis basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact leftDerivesLaw0
  · exact leftDerivesLaw1
  · exact leftDerivesLaw2

def rightBasisLaw0 : Identity Nat := ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def rightBasisLaw1 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩
def rightBasisLaw2 : Identity Nat := ⟨⟨0, [0, 1, 1, 2]⟩, ⟨0, [1, 1, 0, 2]⟩⟩

def rightBasis : List (Identity Nat) :=
  [rightBasisLaw0, rightBasisLaw1, rightBasisLaw2]

theorem rightDerivesLaw0 :
    Derives rightBasis basisLaw0.lhs basisLaw0.rhs := by
  have step0 : Derives rightBasis ⟨0, [0]⟩ ⟨0, [0, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives rightBasis ⟨0, [0, 0]⟩ ⟨0, [0, 0, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw1 :
    Derives rightBasis basisLaw1.lhs basisLaw1.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 1, 2]⟩ ⟨0, [1, 1, 0, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw2.lhs rightBasisLaw2.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem rightDerivesLaw2 :
    Derives rightBasis basisLaw2.lhs basisLaw2.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 0]⟩ ⟨1, [0, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

/-- 3 fixed displayed-law instances. -/
theorem displayedInRightBasis : FiniteCertificate.DerivesAll rightBasis basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact rightDerivesLaw0
  · exact rightDerivesLaw1
  · exact rightDerivesLaw2

def conditionBasisLaw0 : Identity Nat := ⟨⟨0, [0, 0, 0, 0, 0, 0, 0, 1]⟩, ⟨0, [0, 1]⟩⟩
def conditionBasisLaw1 : Identity Nat := ⟨⟨0, [1, 1, 1, 1, 1, 1, 1, 1]⟩, ⟨0, [1, 1]⟩⟩
def conditionBasisLaw2 : Identity Nat := ⟨⟨0, [0, 0, 0, 0, 0, 0, 1, 0]⟩, ⟨0, [1, 0]⟩⟩
def conditionBasisLaw3 : Identity Nat := ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩
def conditionBasisLaw4 : Identity Nat := ⟨⟨0, [1, 0, 2, 0]⟩, ⟨0, [0, 1, 2, 0]⟩⟩
def conditionBasisLaw5 : Identity Nat := ⟨⟨0, [1, 0, 1]⟩, ⟨0, [0, 1, 1]⟩⟩
def conditionBasisLaw6 : Identity Nat := ⟨⟨1, [2, 1, 0]⟩, ⟨2, [1, 1, 0]⟩⟩
def conditionBasisLaw7 : Identity Nat := ⟨⟨1, [0, 0, 0, 0, 0, 0, 0, 0]⟩, ⟨1, [0, 0]⟩⟩
def conditionBasisLaw8 : Identity Nat := ⟨⟨1, [1, 1, 1, 1, 1, 1, 1, 0]⟩, ⟨1, [1, 0]⟩⟩
def conditionBasisLaw9 : Identity Nat := ⟨⟨0, [1, 0, 0, 0, 0, 0, 0, 0]⟩, ⟨0, [1, 0]⟩⟩
def conditionBasisLaw10 : Identity Nat := ⟨⟨0, [1, 0, 0]⟩, ⟨0, [0, 1, 0]⟩⟩
def conditionBasisLaw11 : Identity Nat := ⟨⟨0, [2, 0, 1, 0]⟩, ⟨0, [2, 1, 0, 0]⟩⟩
def conditionBasisLaw12 : Identity Nat := ⟨⟨1, [0, 1, 0]⟩, ⟨1, [1, 0, 0]⟩⟩

def conditionBasis : List (Identity Nat) :=
  [conditionBasisLaw0, conditionBasisLaw1, conditionBasisLaw2, conditionBasisLaw3, conditionBasisLaw4, conditionBasisLaw5, conditionBasisLaw6, conditionBasisLaw7, conditionBasisLaw8, conditionBasisLaw9, conditionBasisLaw10, conditionBasisLaw11, conditionBasisLaw12]

theorem conditionDerivesLaw0 :
    Derives basis conditionBasisLaw0.lhs conditionBasisLaw0.rhs := by
  have step0 : Derives basis ⟨0, [0, 0, 0, 0, 0, 0, 0, 1]⟩ ⟨0, [0, 0, 0, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  have step1 : Derives basis ⟨0, [0, 0, 0, 1]⟩ ⟨0, [0, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  exact Derives.trans step0 (step1)

theorem conditionDerivesLaw1 :
    Derives basis conditionBasisLaw1.lhs conditionBasisLaw1.rhs := by
  have step0 : Derives basis ⟨0, [1, 1, 1, 1, 1, 1, 1, 1]⟩ ⟨0, [1, 1, 1, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  have step1 : Derives basis ⟨0, [1, 1, 1, 1]⟩ ⟨0, [1, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  exact Derives.trans step0 (step1)

theorem conditionDerivesLaw2 :
    Derives basis conditionBasisLaw2.lhs conditionBasisLaw2.rhs := by
  have step0 : Derives basis ⟨0, [0, 0, 0, 0, 0, 0, 1, 0]⟩ ⟨0, [0, 0, 0, 0, 1, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, [0, 0, 1, 0]⟩)
  have step1 : Derives basis ⟨0, [0, 0, 0, 0, 1, 0]⟩ ⟨0, [0, 0, 1, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, [1, 0]⟩)
  have step2 : Derives basis ⟨0, [0, 0, 1, 0]⟩ ⟨0, [0, 1, 0, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [0, 1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step3 : Derives basis ⟨0, [0, 1, 0, 0]⟩ ⟨1, [0, 0, 0, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [0]⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step4 : Derives basis ⟨1, [0, 0, 0, 0]⟩ ⟨1, [0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨1, []⟩ instantiated)
  have step5 : Derives basis ⟨1, [0, 0]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (Derives.trans step3 (Derives.trans step4 (step5)))))

theorem conditionDerivesLaw3 :
    Derives basis conditionBasisLaw3.lhs conditionBasisLaw3.rhs := by
  have step0 : Derives basis ⟨0, [0, 1, 0]⟩ ⟨0, [1, 0, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem conditionDerivesLaw4 :
    Derives basis conditionBasisLaw4.lhs conditionBasisLaw4.rhs := by
  have step0 : Derives basis ⟨0, [1, 0, 2, 0]⟩ ⟨0, [1, 2, 0, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [1]⟩ instantiated)
  have step1 : Derives basis ⟨0, [1, 2, 0, 0]⟩ ⟨0, [0, 1, 2, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1, 2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

theorem conditionDerivesLaw5 :
    Derives basis conditionBasisLaw5.lhs conditionBasisLaw5.rhs := by
  have step0 : Derives basis ⟨0, [1, 0, 1]⟩ ⟨0, [0, 1, 1]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  exact step0

theorem conditionDerivesLaw6 :
    Derives basis conditionBasisLaw6.lhs conditionBasisLaw6.rhs := by
  have step0 : Derives basis ⟨1, [2, 1, 0]⟩ ⟨2, [1, 1, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  exact step0

theorem conditionDerivesLaw7 :
    Derives basis conditionBasisLaw7.lhs conditionBasisLaw7.rhs := by
  have step0 : Derives basis ⟨1, [0, 0, 0, 0, 0, 0, 0, 0]⟩ ⟨1, [0, 0, 0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨1, []⟩ instantiated)
  have step1 : Derives basis ⟨1, [0, 0, 0, 0]⟩ ⟨1, [0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨1, []⟩ instantiated)
  have step2 : Derives basis ⟨1, [0, 0]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step3 : Derives basis ⟨0, [1, 0]⟩ ⟨1, [0, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (step3)))

theorem conditionDerivesLaw8 :
    Derives basis conditionBasisLaw8.lhs conditionBasisLaw8.rhs := by
  have step0 : Derives basis ⟨1, [1, 1, 1, 1, 1, 1, 1, 0]⟩ ⟨1, [1, 1, 1, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  have step1 : Derives basis ⟨1, [1, 1, 1, 0]⟩ ⟨1, [1, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  exact Derives.trans step0 (step1)

theorem conditionDerivesLaw9 :
    Derives basis conditionBasisLaw9.lhs conditionBasisLaw9.rhs := by
  have step0 : Derives basis ⟨0, [1, 0, 0, 0, 0, 0, 0, 0]⟩ ⟨0, [1, 0, 0, 0, 0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, [1]⟩ instantiated) ⟨0, [0, 0]⟩)
  have step1 : Derives basis ⟨0, [1, 0, 0, 0, 0, 0]⟩ ⟨0, [1, 0, 0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, [1]⟩ instantiated) ⟨0, []⟩)
  have step2 : Derives basis ⟨0, [1, 0, 0, 0]⟩ ⟨0, [0, 1, 0, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  have step3 : Derives basis ⟨0, [0, 1, 0, 0]⟩ ⟨0, [0, 0, 1, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [0, 1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step4 : Derives basis ⟨0, [0, 0, 1, 0]⟩ ⟨0, [0, 1, 0, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [0, 1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step5 : Derives basis ⟨0, [0, 1, 0, 0]⟩ ⟨1, [0, 0, 0, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [0]⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step6 : Derives basis ⟨1, [0, 0, 0, 0]⟩ ⟨1, [0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨1, []⟩ instantiated)
  have step7 : Derives basis ⟨1, [0, 0]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (Derives.trans step3 (Derives.trans step4 (Derives.trans step5 (Derives.trans step6 (step7)))))))

theorem conditionDerivesLaw10 :
    Derives basis conditionBasisLaw10.lhs conditionBasisLaw10.rhs := by
  have step0 : Derives basis ⟨0, [1, 0, 0]⟩ ⟨0, [0, 1, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem conditionDerivesLaw11 :
    Derives basis conditionBasisLaw11.lhs conditionBasisLaw11.rhs := by
  have step0 : Derives basis ⟨0, [2, 0, 1, 0]⟩ ⟨0, [2, 1, 0, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [2]⟩ instantiated)
  have step1 : Derives basis ⟨0, [2, 1, 0, 0]⟩ ⟨0, [0, 2, 1, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [2, 1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step2 : Derives basis ⟨0, [0, 2, 1, 0]⟩ ⟨0, [2, 1, 0, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [2, 1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (step2))

theorem conditionDerivesLaw12 :
    Derives basis conditionBasisLaw12.lhs conditionBasisLaw12.rhs := by
  have step0 : Derives basis ⟨1, [0, 1, 0]⟩ ⟨0, [1, 1, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  have step1 : Derives basis ⟨0, [1, 1, 0]⟩ ⟨1, [1, 0, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

/-- Fixed positive identities from the actual signed condition matches. -/
theorem conditionsInDisplayed : FiniteCertificate.DerivesAll basis conditionBasis := by
  intro identity member
  simp only [conditionBasis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact conditionDerivesLaw0
  · exact conditionDerivesLaw1
  · exact conditionDerivesLaw2
  · exact conditionDerivesLaw3
  · exact conditionDerivesLaw4
  · exact conditionDerivesLaw5
  · exact conditionDerivesLaw6
  · exact conditionDerivesLaw7
  · exact conditionDerivesLaw8
  · exact conditionDerivesLaw9
  · exact conditionDerivesLaw10
  · exact conditionDerivesLaw11
  · exact conditionDerivesLaw12

private theorem leftModelsLaw0 : basisLaw0.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup := by
  have roundTrip : (basisLaw0.map toFinThree).map Fin.val = basisLaw0 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S3_11.table (basisLaw0.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw1 : basisLaw1.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup := by
  have roundTrip : (basisLaw1.map toFinThree).map Fin.val = basisLaw1 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S3_11.table (basisLaw1.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw2 : basisLaw2.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup := by
  have roundTrip : (basisLaw2.map toFinThree).map Fin.val = basisLaw2 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S3_11.table (basisLaw2.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem leftModels : Models SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact leftModelsLaw0
  · exact leftModelsLaw1
  · exact leftModelsLaw2

private theorem rightModelsLaw0 : basisLaw0.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_844.table.semigroup := by
  have roundTrip : (basisLaw0.map toFinThree).map Fin.val = basisLaw0 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_844.table (basisLaw0.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw1 : basisLaw1.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_844.table.semigroup := by
  have roundTrip : (basisLaw1.map toFinThree).map Fin.val = basisLaw1 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_844.table (basisLaw1.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw2 : basisLaw2.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_844.table.semigroup := by
  have roundTrip : (basisLaw2.map toFinThree).map Fin.val = basisLaw2 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_844.table (basisLaw2.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem rightModels : Models SemigroupBasis.Generated.Catalogue.S5_844.table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact rightModelsLaw0
  · exact rightModelsLaw1
  · exact rightModelsLaw2

namespace S6_11237

/-- Exact catalogue table SHA256 `e574ec19de6e8f67a4ced779e3e3d62ee697d11b36bd15a50b0292e42da8acb2`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6)) else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)) else if a = 3 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6)) else if a = 4 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def ontoLeftMap (a : Fin 6) : Fin 3 :=
  if a = 0 then (2 : Fin 3) else if a = 1 then (2 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (1 : Fin 3) else if a = 4 then (0 : Fin 3) else (0 : Fin 3)

def ontoLeftSection (a : Fin 3) : Fin 6 :=
  if a = 0 then (2 : Fin 6) else if a = 1 then (3 : Fin 6) else (0 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (2 : Fin 5) else if a = 4 then (3 : Fin 5) else (4 : Fin 5)

def ontoRightSection (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_844.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup SemigroupBasis.Generated.Catalogue.S5_844.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro a b
    exact by decide +revert

theorem models : Models table.semigroup basis := by
  intro identity member
  exact (pair.satisfiedBy_iff identity).mpr ⟨leftModels identity member, rightModels identity member⟩

def ontoLeftOpposite : SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup.opposite where
  toFun := ontoLeftMap
  map_mul := fun a b => ontoLeft.map_mul b a
  preimage := ontoLeftSection
  right_inverse := ontoLeft.right_inverse

def ontoRightOpposite : SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_844.table.semigroup.opposite where
  toFun := ontoRightMap
  map_mul := fun a b => ontoRight.map_mul b a
  preimage := ontoRightSection
  right_inverse := ontoRight.right_inverse

def pairOpposite : SubdirectPair table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_844.table.semigroup.opposite where
  left := ontoLeftOpposite
  right := ontoRightOpposite
  jointlyInjective := pair.jointlyInjective

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) :=
  models.oppositeReversed

theorem conditionModels : Models table.semigroup conditionBasis := by
  intro identity member
  exact Derives.sound models (conditionsInDisplayed _ member)

end S6_11237

namespace S6_11389

/-- Exact catalogue table SHA256 `88ecc6159a56efd82c4e445b0d72a95106a58583a218ff1d5a589d2ccab2d785`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if a = 3 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if a = 4 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

private theorem modelsLaw0 : basisLaw0.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw0.map toFinThree).map Fin.val = basisLaw0 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw0.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem modelsLaw1 : basisLaw1.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw1.map toFinThree).map Fin.val = basisLaw1 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw1.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem modelsLaw2 : basisLaw2.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw2.map toFinThree).map Fin.val = basisLaw2 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw2.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact modelsLaw0
  · exact modelsLaw1
  · exact modelsLaw2

def rootHom0Map (a : Fin 6) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (4 : Fin 6) else if a = 4 then (2 : Fin 6) else (2 : Fin 6)

def rootHom0 : Hom S6_11237.table.semigroup table.semigroup where
  toFun := rootHom0Map
  map_mul := by decide

def rootHom0Opposite : Hom S6_11237.table.semigroup.opposite table.semigroup.opposite where
  toFun := rootHom0.toFun
  map_mul := fun a b => rootHom0.map_mul b a

def rootHom1Map (a : Fin 6) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (4 : Fin 6) else (5 : Fin 6)

def rootHom1 : Hom S6_11237.table.semigroup table.semigroup where
  toFun := rootHom1Map
  map_mul := by decide

def rootHom1Opposite : Hom S6_11237.table.semigroup.opposite table.semigroup.opposite where
  toFun := rootHom1.toFun
  map_mul := fun a b => rootHom1.map_mul b a

def rootHom2Map (a : Fin 6) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (2 : Fin 6) else (2 : Fin 6)

def rootHom2 : Hom S6_11237.table.semigroup table.semigroup where
  toFun := rootHom2Map
  map_mul := by decide

def rootHom2Opposite : Hom S6_11237.table.semigroup.opposite table.semigroup.opposite where
  toFun := rootHom2.toFun
  map_mul := fun a b => rootHom2.map_mul b a

def rootHomFamily (i : Fin 3) : Hom S6_11237.table.semigroup table.semigroup :=
  if i = 0 then rootHom0 else if i = 1 then rootHom1 else rootHom2

/-- Finite 3-coordinate root-to-leaf embedding. -/
def rootIntoPower : Embedding S6_11237.table.semigroup (table.semigroup.pi (Fin 3)) :=
  Embedding.ofSeparatingHoms rootHomFamily (by decide)

def rootHomFamilyOpposite (i : Fin 3) : Hom S6_11237.table.semigroup.opposite table.semigroup.opposite :=
  if i = 0 then rootHom0Opposite else if i = 1 then rootHom1Opposite else rootHom2Opposite

/-- Finite 3-coordinate root-to-leaf embedding. -/
def rootOppositeIntoPower : Embedding S6_11237.table.semigroup.opposite (table.semigroup.opposite.pi (Fin 3)) :=
  Embedding.ofSeparatingHoms rootHomFamilyOpposite (by decide)

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) :=
  models.oppositeReversed

theorem conditionModels : Models table.semigroup conditionBasis := by
  intro identity member
  exact Derives.sound models (conditionsInDisplayed _ member)

end S6_11389

end SigmaParity844

namespace SigmaCap303

def basisLaw0 : Identity Nat := ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def basisLaw1 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩
def basisLaw2 : Identity Nat := ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

def basis : List (Identity Nat) :=
  [basisLaw0, basisLaw1, basisLaw2]

def leftBasisLaw0 : Identity Nat := ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def leftBasisLaw1 : Identity Nat := ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def leftBasis : List (Identity Nat) :=
  [leftBasisLaw0, leftBasisLaw1]

theorem leftDerivesLaw0 :
    Derives leftBasis basisLaw0.lhs basisLaw0.rhs := by
  have step0 : Derives leftBasis ⟨0, [0]⟩ ⟨0, [0, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem leftDerivesLaw1 :
    Derives leftBasis basisLaw1.lhs basisLaw1.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 0]⟩ ⟨1, [0, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  exact step0

theorem leftDerivesLaw2 :
    Derives leftBasis basisLaw2.lhs basisLaw2.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 2, 0]⟩ ⟨0, [2, 1, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, []⟩ instantiated) ⟨0, []⟩)
  exact step0

/-- 3 fixed displayed-law instances. -/
theorem displayedInLeftBasis : FiniteCertificate.DerivesAll leftBasis basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact leftDerivesLaw0
  · exact leftDerivesLaw1
  · exact leftDerivesLaw2

def rightBasisLaw0 : Identity Nat := ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩
def rightBasisLaw1 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩
def rightBasisLaw2 : Identity Nat := ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

def rightBasis : List (Identity Nat) :=
  [rightBasisLaw0, rightBasisLaw1, rightBasisLaw2]

theorem rightDerivesLaw0 :
    Derives rightBasis basisLaw0.lhs basisLaw0.rhs := by
  have step0 : Derives rightBasis ⟨0, [0]⟩ ⟨0, [0, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem rightDerivesLaw1 :
    Derives rightBasis basisLaw1.lhs basisLaw1.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 0]⟩ ⟨1, [0, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem rightDerivesLaw2 :
    Derives rightBasis basisLaw2.lhs basisLaw2.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 2, 0]⟩ ⟨0, [2, 1, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw2.lhs rightBasisLaw2.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

/-- 3 fixed displayed-law instances. -/
theorem displayedInRightBasis : FiniteCertificate.DerivesAll rightBasis basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact rightDerivesLaw0
  · exact rightDerivesLaw1
  · exact rightDerivesLaw2

def conditionBasisLaw0 : Identity Nat := ⟨⟨0, [0, 0]⟩, ⟨0, [0]⟩⟩
def conditionBasisLaw1 : Identity Nat := ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0]⟩⟩
def conditionBasisLaw2 : Identity Nat := ⟨⟨0, [1, 0, 0]⟩, ⟨0, [1, 0]⟩⟩
def conditionBasisLaw3 : Identity Nat := ⟨⟨0, [1, 0, 2, 0]⟩, ⟨0, [1, 2, 0]⟩⟩
def conditionBasisLaw4 : Identity Nat := ⟨⟨0, [0, 0, 0, 0, 0, 0, 0, 1]⟩, ⟨0, [0, 1]⟩⟩
def conditionBasisLaw5 : Identity Nat := ⟨⟨0, [1, 1, 1, 1, 1, 1, 1, 1]⟩, ⟨0, [1, 1]⟩⟩
def conditionBasisLaw6 : Identity Nat := ⟨⟨0, [0, 0, 0, 0, 0, 0, 1, 0]⟩, ⟨0, [1, 0]⟩⟩
def conditionBasisLaw7 : Identity Nat := ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩
def conditionBasisLaw8 : Identity Nat := ⟨⟨0, [1, 0, 2, 0]⟩, ⟨0, [0, 1, 2, 0]⟩⟩
def conditionBasisLaw9 : Identity Nat := ⟨⟨0, [1, 0, 1]⟩, ⟨0, [0, 1, 1]⟩⟩
def conditionBasisLaw10 : Identity Nat := ⟨⟨1, [2, 1, 0]⟩, ⟨2, [1, 1, 0]⟩⟩
def conditionBasisLaw11 : Identity Nat := ⟨⟨0, [2, 0, 1, 0]⟩, ⟨0, [2, 1, 0]⟩⟩
def conditionBasisLaw12 : Identity Nat := ⟨⟨0, [0, 0, 0]⟩, ⟨0, [0]⟩⟩
def conditionBasisLaw13 : Identity Nat := ⟨⟨0, [1, 0, 0, 0]⟩, ⟨0, [1, 0]⟩⟩
def conditionBasisLaw14 : Identity Nat := ⟨⟨0, [1, 0, 0]⟩, ⟨0, [0, 1, 0]⟩⟩
def conditionBasisLaw15 : Identity Nat := ⟨⟨2, [2, 1, 0, 0]⟩, ⟨0, [2, 2, 1, 0]⟩⟩
def conditionBasisLaw16 : Identity Nat := ⟨⟨0, [2, 0, 1, 0]⟩, ⟨0, [1, 0, 2, 0]⟩⟩
def conditionBasisLaw17 : Identity Nat := ⟨⟨1, [0, 0, 0, 0, 0, 0, 0, 0]⟩, ⟨1, [0, 0]⟩⟩
def conditionBasisLaw18 : Identity Nat := ⟨⟨1, [1, 1, 1, 1, 1, 1, 1, 0]⟩, ⟨1, [1, 0]⟩⟩
def conditionBasisLaw19 : Identity Nat := ⟨⟨0, [1, 0, 0, 0, 0, 0, 0, 0]⟩, ⟨0, [1, 0]⟩⟩
def conditionBasisLaw20 : Identity Nat := ⟨⟨0, [2, 0, 1, 0]⟩, ⟨0, [2, 1, 0, 0]⟩⟩
def conditionBasisLaw21 : Identity Nat := ⟨⟨1, [0, 1, 0]⟩, ⟨1, [1, 0, 0]⟩⟩

def conditionBasis : List (Identity Nat) :=
  [conditionBasisLaw0, conditionBasisLaw1, conditionBasisLaw2, conditionBasisLaw3, conditionBasisLaw4, conditionBasisLaw5, conditionBasisLaw6, conditionBasisLaw7, conditionBasisLaw8, conditionBasisLaw9, conditionBasisLaw10, conditionBasisLaw11, conditionBasisLaw12, conditionBasisLaw13, conditionBasisLaw14, conditionBasisLaw15, conditionBasisLaw16, conditionBasisLaw17, conditionBasisLaw18, conditionBasisLaw19, conditionBasisLaw20, conditionBasisLaw21]

theorem conditionDerivesLaw0 :
    Derives basis conditionBasisLaw0.lhs conditionBasisLaw0.rhs := by
  have step0 : Derives basis ⟨0, [0, 0]⟩ ⟨0, [0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem conditionDerivesLaw1 :
    Derives basis conditionBasisLaw1.lhs conditionBasisLaw1.rhs := by
  have step0 : Derives basis ⟨0, [0, 1, 0]⟩ ⟨0, [1, 0, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives basis ⟨0, [1, 0, 0]⟩ ⟨1, [0, 0, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  have step2 : Derives basis ⟨1, [0, 0, 0]⟩ ⟨1, [0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨1, []⟩ instantiated)
  have step3 : Derives basis ⟨1, [0, 0]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (step3)))

theorem conditionDerivesLaw2 :
    Derives basis conditionBasisLaw2.lhs conditionBasisLaw2.rhs := by
  have step0 : Derives basis ⟨0, [1, 0, 0]⟩ ⟨0, [0, 1, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives basis ⟨0, [0, 1, 0]⟩ ⟨0, [1, 0, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step2 : Derives basis ⟨0, [1, 0, 0]⟩ ⟨1, [0, 0, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  have step3 : Derives basis ⟨1, [0, 0, 0]⟩ ⟨1, [0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨1, []⟩ instantiated)
  have step4 : Derives basis ⟨1, [0, 0]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (Derives.trans step3 (step4))))

theorem conditionDerivesLaw3 :
    Derives basis conditionBasisLaw3.lhs conditionBasisLaw3.rhs := by
  have step0 : Derives basis ⟨0, [1, 0, 2, 0]⟩ ⟨0, [0, 2, 1, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨0, [2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives basis ⟨0, [0, 2, 1, 0]⟩ ⟨0, [0, 1, 2, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨2, []⟩
      | 2 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  have step2 : Derives basis ⟨0, [0, 1, 2, 0]⟩ ⟨0, [1, 2, 0, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1, 2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step3 : Derives basis ⟨0, [1, 2, 0, 0]⟩ ⟨1, [2, 0, 0, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, [2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  have step4 : Derives basis ⟨1, [2, 0, 0, 0]⟩ ⟨1, [2, 0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨1, [2]⟩ instantiated)
  have step5 : Derives basis ⟨1, [2, 0, 0]⟩ ⟨0, [1, 2, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, [2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (Derives.trans step3 (Derives.trans step4 (step5)))))

theorem conditionDerivesLaw4 :
    Derives basis conditionBasisLaw4.lhs conditionBasisLaw4.rhs := by
  have step0 : Derives basis ⟨0, [0, 0, 0, 0, 0, 0, 0, 1]⟩ ⟨0, [0, 0, 0, 0, 0, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, [0, 1]⟩)
  have step1 : Derives basis ⟨0, [0, 0, 0, 0, 0, 1]⟩ ⟨0, [0, 0, 0, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  have step2 : Derives basis ⟨0, [0, 0, 0, 1]⟩ ⟨0, [0, 0, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, [1]⟩)
  have step3 : Derives basis ⟨0, [0, 0, 1]⟩ ⟨0, [0, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (step3)))

theorem conditionDerivesLaw5 :
    Derives basis conditionBasisLaw5.lhs conditionBasisLaw5.rhs := by
  have step0 : Derives basis ⟨0, [1, 1, 1, 1, 1, 1, 1, 1]⟩ ⟨0, [1, 1, 1, 1, 1, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, []⟩ instantiated) ⟨1, [1]⟩)
  have step1 : Derives basis ⟨0, [1, 1, 1, 1, 1, 1]⟩ ⟨0, [1, 1, 1, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  have step2 : Derives basis ⟨0, [1, 1, 1, 1]⟩ ⟨0, [1, 1, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, []⟩ instantiated) ⟨1, []⟩)
  have step3 : Derives basis ⟨0, [1, 1, 1]⟩ ⟨0, [1, 1]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (step3)))

theorem conditionDerivesLaw6 :
    Derives basis conditionBasisLaw6.lhs conditionBasisLaw6.rhs := by
  have step0 : Derives basis ⟨0, [0, 0, 0, 0, 0, 0, 1, 0]⟩ ⟨0, [0, 0, 0, 0, 1, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, [1, 0]⟩)
  have step1 : Derives basis ⟨0, [0, 0, 0, 0, 1, 0]⟩ ⟨0, [0, 0, 0, 1, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, [0, 1, 0]⟩)
  have step2 : Derives basis ⟨0, [0, 0, 0, 1, 0]⟩ ⟨0, [0, 0, 1, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, [1, 0]⟩)
  have step3 : Derives basis ⟨0, [0, 0, 1, 0]⟩ ⟨0, [0, 1, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [0]⟩)
  have step4 : Derives basis ⟨0, [0, 1, 0]⟩ ⟨0, [1, 0, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step5 : Derives basis ⟨0, [1, 0, 0]⟩ ⟨1, [0, 0, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  have step6 : Derives basis ⟨1, [0, 0, 0]⟩ ⟨1, [0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨1, []⟩ instantiated)
  have step7 : Derives basis ⟨1, [0, 0]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (Derives.trans step3 (Derives.trans step4 (Derives.trans step5 (Derives.trans step6 (step7)))))))

theorem conditionDerivesLaw7 :
    Derives basis conditionBasisLaw7.lhs conditionBasisLaw7.rhs := by
  have step0 : Derives basis ⟨0, [0, 1, 0]⟩ ⟨0, [1, 0, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem conditionDerivesLaw8 :
    Derives basis conditionBasisLaw8.lhs conditionBasisLaw8.rhs := by
  have step0 : Derives basis ⟨0, [1, 0, 2, 0]⟩ ⟨0, [0, 2, 1, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨0, [2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives basis ⟨0, [0, 2, 1, 0]⟩ ⟨0, [0, 1, 2, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨2, []⟩
      | 2 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  exact Derives.trans step0 (step1)

theorem conditionDerivesLaw9 :
    Derives basis conditionBasisLaw9.lhs conditionBasisLaw9.rhs := by
  have step0 : Derives basis ⟨0, [1, 0, 1]⟩ ⟨0, [0, 1, 1]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  exact step0

theorem conditionDerivesLaw10 :
    Derives basis conditionBasisLaw10.lhs conditionBasisLaw10.rhs := by
  have step0 : Derives basis ⟨1, [2, 1, 0]⟩ ⟨2, [1, 1, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  exact step0

theorem conditionDerivesLaw11 :
    Derives basis conditionBasisLaw11.lhs conditionBasisLaw11.rhs := by
  have step0 : Derives basis ⟨0, [2, 0, 1, 0]⟩ ⟨0, [0, 1, 2, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨2, []⟩
      | 2 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives basis ⟨0, [0, 1, 2, 0]⟩ ⟨0, [1, 2, 0, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1, 2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step2 : Derives basis ⟨0, [1, 2, 0, 0]⟩ ⟨1, [2, 0, 0, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, [2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  have step3 : Derives basis ⟨1, [2, 0, 0, 0]⟩ ⟨1, [2, 0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨1, [2]⟩ instantiated)
  have step4 : Derives basis ⟨1, [2, 0, 0]⟩ ⟨0, [1, 2, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, [2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step5 : Derives basis ⟨0, [1, 2, 0]⟩ ⟨0, [2, 1, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨2, []⟩
      | 2 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (Derives.trans step3 (Derives.trans step4 (step5)))))

theorem conditionDerivesLaw12 :
    Derives basis conditionBasisLaw12.lhs conditionBasisLaw12.rhs := by
  have step0 : Derives basis ⟨0, [0, 0, 0]⟩ ⟨0, [0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  have step1 : Derives basis ⟨0, [0, 0]⟩ ⟨0, [0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

theorem conditionDerivesLaw13 :
    Derives basis conditionBasisLaw13.lhs conditionBasisLaw13.rhs := by
  have step0 : Derives basis ⟨0, [1, 0, 0, 0]⟩ ⟨0, [1, 0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [1]⟩ instantiated)
  have step1 : Derives basis ⟨0, [1, 0, 0]⟩ ⟨0, [0, 1, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step2 : Derives basis ⟨0, [0, 1, 0]⟩ ⟨0, [1, 0, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step3 : Derives basis ⟨0, [1, 0, 0]⟩ ⟨1, [0, 0, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  have step4 : Derives basis ⟨1, [0, 0, 0]⟩ ⟨1, [0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨1, []⟩ instantiated)
  have step5 : Derives basis ⟨1, [0, 0]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (Derives.trans step3 (Derives.trans step4 (step5)))))

theorem conditionDerivesLaw14 :
    Derives basis conditionBasisLaw14.lhs conditionBasisLaw14.rhs := by
  have step0 : Derives basis ⟨0, [1, 0, 0]⟩ ⟨0, [0, 1, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem conditionDerivesLaw15 :
    Derives basis conditionBasisLaw15.lhs conditionBasisLaw15.rhs := by
  have step0 : Derives basis ⟨2, [2, 1, 0, 0]⟩ ⟨0, [2, 2, 1, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨2, [2, 1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives basis ⟨0, [2, 2, 1, 0]⟩ ⟨0, [1, 2, 2, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨2, [2]⟩
      | 2 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step2 : Derives basis ⟨0, [1, 2, 2, 0]⟩ ⟨0, [2, 2, 1, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨2, [2]⟩
      | 2 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (step2))

theorem conditionDerivesLaw16 :
    Derives basis conditionBasisLaw16.lhs conditionBasisLaw16.rhs := by
  have step0 : Derives basis ⟨0, [2, 0, 1, 0]⟩ ⟨0, [0, 1, 2, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨2, []⟩
      | 2 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives basis ⟨0, [0, 1, 2, 0]⟩ ⟨0, [0, 2, 1, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨2, []⟩
      | 2 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  have step2 : Derives basis ⟨0, [0, 2, 1, 0]⟩ ⟨0, [1, 0, 2, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨0, [2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (step2))

theorem conditionDerivesLaw17 :
    Derives basis conditionBasisLaw17.lhs conditionBasisLaw17.rhs := by
  have step0 : Derives basis ⟨1, [0, 0, 0, 0, 0, 0, 0, 0]⟩ ⟨1, [0, 0, 0, 0, 0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨1, []⟩ instantiated) ⟨0, [0]⟩)
  have step1 : Derives basis ⟨1, [0, 0, 0, 0, 0, 0]⟩ ⟨1, [0, 0, 0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨1, []⟩ instantiated)
  have step2 : Derives basis ⟨1, [0, 0, 0, 0]⟩ ⟨1, [0, 0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨1, []⟩ instantiated) ⟨0, []⟩)
  have step3 : Derives basis ⟨1, [0, 0, 0]⟩ ⟨1, [0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨1, []⟩ instantiated)
  have step4 : Derives basis ⟨1, [0, 0]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step5 : Derives basis ⟨0, [1, 0]⟩ ⟨1, [0, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (Derives.trans step3 (Derives.trans step4 (step5)))))

theorem conditionDerivesLaw18 :
    Derives basis conditionBasisLaw18.lhs conditionBasisLaw18.rhs := by
  have step0 : Derives basis ⟨1, [1, 1, 1, 1, 1, 1, 1, 0]⟩ ⟨1, [1, 1, 1, 1, 1, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [1, 0]⟩)
  have step1 : Derives basis ⟨1, [1, 1, 1, 1, 1, 0]⟩ ⟨1, [1, 1, 1, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  have step2 : Derives basis ⟨1, [1, 1, 1, 0]⟩ ⟨1, [1, 1, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [0]⟩)
  have step3 : Derives basis ⟨1, [1, 1, 0]⟩ ⟨1, [1, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (step3)))

theorem conditionDerivesLaw19 :
    Derives basis conditionBasisLaw19.lhs conditionBasisLaw19.rhs := by
  have step0 : Derives basis ⟨0, [1, 0, 0, 0, 0, 0, 0, 0]⟩ ⟨0, [1, 0, 0, 0, 0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, [1]⟩ instantiated) ⟨0, []⟩)
  have step1 : Derives basis ⟨0, [1, 0, 0, 0, 0, 0]⟩ ⟨0, [1, 0, 0, 0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, [1]⟩ instantiated) ⟨0, [0]⟩)
  have step2 : Derives basis ⟨0, [1, 0, 0, 0, 0]⟩ ⟨0, [1, 0, 0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, [1]⟩ instantiated) ⟨0, []⟩)
  have step3 : Derives basis ⟨0, [1, 0, 0, 0]⟩ ⟨0, [1, 0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [1]⟩ instantiated)
  have step4 : Derives basis ⟨0, [1, 0, 0]⟩ ⟨0, [0, 1, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step5 : Derives basis ⟨0, [0, 1, 0]⟩ ⟨0, [1, 0, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step6 : Derives basis ⟨0, [1, 0, 0]⟩ ⟨1, [0, 0, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  have step7 : Derives basis ⟨1, [0, 0, 0]⟩ ⟨1, [0, 0]⟩ := by
    have base : Derives basis basisLaw0.lhs basisLaw0.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨1, []⟩ instantiated)
  have step8 : Derives basis ⟨1, [0, 0]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (Derives.trans step3 (Derives.trans step4 (Derives.trans step5 (Derives.trans step6 (Derives.trans step7 (step8))))))))

theorem conditionDerivesLaw20 :
    Derives basis conditionBasisLaw20.lhs conditionBasisLaw20.rhs := by
  have step0 : Derives basis ⟨0, [2, 0, 1, 0]⟩ ⟨0, [0, 1, 2, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨2, []⟩
      | 2 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives basis ⟨0, [0, 1, 2, 0]⟩ ⟨0, [0, 2, 1, 0]⟩ := by
    have base : Derives basis basisLaw2.lhs basisLaw2.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨2, []⟩
      | 2 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [basisLaw2, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  have step2 : Derives basis ⟨0, [0, 2, 1, 0]⟩ ⟨0, [2, 1, 0, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [2, 1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (step2))

theorem conditionDerivesLaw21 :
    Derives basis conditionBasisLaw21.lhs conditionBasisLaw21.rhs := by
  have step0 : Derives basis ⟨1, [0, 1, 0]⟩ ⟨0, [1, 1, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  have step1 : Derives basis ⟨0, [1, 1, 0]⟩ ⟨1, [1, 0, 0]⟩ := by
    have base : Derives basis basisLaw1.lhs basisLaw1.rhs :=
      Derives.fromBasis (by simp [basis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [basisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

/-- Fixed positive identities from the actual signed condition matches. -/
theorem conditionsInDisplayed : FiniteCertificate.DerivesAll basis conditionBasis := by
  intro identity member
  simp only [conditionBasis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact conditionDerivesLaw0
  · exact conditionDerivesLaw1
  · exact conditionDerivesLaw2
  · exact conditionDerivesLaw3
  · exact conditionDerivesLaw4
  · exact conditionDerivesLaw5
  · exact conditionDerivesLaw6
  · exact conditionDerivesLaw7
  · exact conditionDerivesLaw8
  · exact conditionDerivesLaw9
  · exact conditionDerivesLaw10
  · exact conditionDerivesLaw11
  · exact conditionDerivesLaw12
  · exact conditionDerivesLaw13
  · exact conditionDerivesLaw14
  · exact conditionDerivesLaw15
  · exact conditionDerivesLaw16
  · exact conditionDerivesLaw17
  · exact conditionDerivesLaw18
  · exact conditionDerivesLaw19
  · exact conditionDerivesLaw20
  · exact conditionDerivesLaw21

private theorem leftModelsLaw0 : basisLaw0.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_8.table.semigroup := by
  have roundTrip : (basisLaw0.map toFinThree).map Fin.val = basisLaw0 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S3_8.table (basisLaw0.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw1 : basisLaw1.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_8.table.semigroup := by
  have roundTrip : (basisLaw1.map toFinThree).map Fin.val = basisLaw1 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S3_8.table (basisLaw1.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw2 : basisLaw2.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_8.table.semigroup := by
  have roundTrip : (basisLaw2.map toFinThree).map Fin.val = basisLaw2 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S3_8.table (basisLaw2.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem leftModels : Models SemigroupBasis.Generated.Catalogue.S3_8.table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact leftModelsLaw0
  · exact leftModelsLaw1
  · exact leftModelsLaw2

private theorem rightModelsLaw0 : basisLaw0.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_303.table.semigroup := by
  have roundTrip : (basisLaw0.map toFinThree).map Fin.val = basisLaw0 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_303.table (basisLaw0.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw1 : basisLaw1.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_303.table.semigroup := by
  have roundTrip : (basisLaw1.map toFinThree).map Fin.val = basisLaw1 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_303.table (basisLaw1.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw2 : basisLaw2.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_303.table.semigroup := by
  have roundTrip : (basisLaw2.map toFinThree).map Fin.val = basisLaw2 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_303.table (basisLaw2.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem rightModels : Models SemigroupBasis.Generated.Catalogue.S5_303.table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact rightModelsLaw0
  · exact rightModelsLaw1
  · exact rightModelsLaw2

namespace S6_3339

/-- Exact catalogue table SHA256 `612a61bc2c82552428fd4885b8891c7d57bdaeb12e6e9d0d228952d76cbfd14b`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 3 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6)) else if a = 4 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if b = 0 then (0 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def ontoLeftMap (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (1 : Fin 3) else if a = 4 then (2 : Fin 3) else (2 : Fin 3)

def ontoLeftSection (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (3 : Fin 6) else (4 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S3_8.table.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (0 : Fin 5) else if a = 4 then (3 : Fin 5) else (4 : Fin 5)

def ontoRightSection (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_303.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.Catalogue.S3_8.table.semigroup SemigroupBasis.Generated.Catalogue.S5_303.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro a b
    exact by decide +revert

theorem models : Models table.semigroup basis := by
  intro identity member
  exact (pair.satisfiedBy_iff identity).mpr ⟨leftModels identity member, rightModels identity member⟩

def ontoLeftOpposite : SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S3_8.table.semigroup.opposite where
  toFun := ontoLeftMap
  map_mul := fun a b => ontoLeft.map_mul b a
  preimage := ontoLeftSection
  right_inverse := ontoLeft.right_inverse

def ontoRightOpposite : SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_303.table.semigroup.opposite where
  toFun := ontoRightMap
  map_mul := fun a b => ontoRight.map_mul b a
  preimage := ontoRightSection
  right_inverse := ontoRight.right_inverse

def pairOpposite : SubdirectPair table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S3_8.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_303.table.semigroup.opposite where
  left := ontoLeftOpposite
  right := ontoRightOpposite
  jointlyInjective := pair.jointlyInjective

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) :=
  models.oppositeReversed

theorem conditionModels : Models table.semigroup conditionBasis := by
  intro identity member
  exact Derives.sound models (conditionsInDisplayed _ member)

end S6_3339

namespace S6_3889

/-- Exact catalogue table SHA256 `69b9b0a97834f1a161538703e80b8743099ef4c4ab6a4e085adc619d0c0da91f`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6)) else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6)) else if a = 3 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6)) else if a = 4 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def ontoLeftMap (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (1 : Fin 3) else if a = 2 then (1 : Fin 3) else if a = 3 then (1 : Fin 3) else if a = 4 then (2 : Fin 3) else (2 : Fin 3)

def ontoLeftSection (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (4 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S3_8.table.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (1 : Fin 5) else if a = 3 then (2 : Fin 5) else if a = 4 then (3 : Fin 5) else (4 : Fin 5)

def ontoRightSection (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_303.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.Catalogue.S3_8.table.semigroup SemigroupBasis.Generated.Catalogue.S5_303.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro a b
    exact by decide +revert

theorem models : Models table.semigroup basis := by
  intro identity member
  exact (pair.satisfiedBy_iff identity).mpr ⟨leftModels identity member, rightModels identity member⟩

def ontoLeftOpposite : SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S3_8.table.semigroup.opposite where
  toFun := ontoLeftMap
  map_mul := fun a b => ontoLeft.map_mul b a
  preimage := ontoLeftSection
  right_inverse := ontoLeft.right_inverse

def ontoRightOpposite : SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_303.table.semigroup.opposite where
  toFun := ontoRightMap
  map_mul := fun a b => ontoRight.map_mul b a
  preimage := ontoRightSection
  right_inverse := ontoRight.right_inverse

def pairOpposite : SubdirectPair table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S3_8.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_303.table.semigroup.opposite where
  left := ontoLeftOpposite
  right := ontoRightOpposite
  jointlyInjective := pair.jointlyInjective

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) :=
  models.oppositeReversed

theorem conditionModels : Models table.semigroup conditionBasis := by
  intro identity member
  exact Derives.sound models (conditionsInDisplayed _ member)

end S6_3889

end SigmaCap303

end SemigroupBasis.CoRoots.Order6Sunday.IntersectionFinite
