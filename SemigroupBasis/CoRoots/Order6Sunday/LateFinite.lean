import SemigroupBasis.Subdirect
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.CatalogueOrder2
import SemigroupBasis.Generated.CatalogueOrder3
import SemigroupBasis.Generated.CatalogueOrder4
import SemigroupBasis.Generated.CatalogueOrder5Part01
import SemigroupBasis.Generated.CatalogueOrder5Part05
import SemigroupBasis.Generated.CatalogueOrder5Part08
import SemigroupBasis.Generated.CatalogueOrder5Part09

/-! Four screened ten/eleven-law systems: only fixed derivations and exact finite witnesses. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.LateFinite

open SemigroupBasis

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

namespace Sigma17bb

def basisLaw0 : Identity Nat := ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def basisLaw1 : Identity Nat := ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0]⟩⟩
def basisLaw2 : Identity Nat := ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 0, 1]⟩⟩
def basisLaw3 : Identity Nat := ⟨⟨0, [0, 1, 1]⟩, ⟨1, [0, 0, 1]⟩⟩
def basisLaw4 : Identity Nat := ⟨⟨0, [0, 1, 1, 2]⟩, ⟨0, [1, 1, 0, 2]⟩⟩
def basisLaw5 : Identity Nat := ⟨⟨0, [0, 1, 2, 1]⟩, ⟨1, [0, 0, 2, 1]⟩⟩
def basisLaw6 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩
def basisLaw7 : Identity Nat := ⟨⟨0, [1, 0, 2, 0]⟩, ⟨0, [1, 2, 0]⟩⟩
def basisLaw8 : Identity Nat := ⟨⟨0, [1, 0, 2, 2]⟩, ⟨2, [0, 1, 0, 2]⟩⟩
def basisLaw9 : Identity Nat := ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def basis : List (Identity Nat) :=
  [basisLaw0, basisLaw1, basisLaw2, basisLaw3, basisLaw4, basisLaw5, basisLaw6, basisLaw7, basisLaw8, basisLaw9]

def leftBasisLaw0 : Identity Nat := ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def leftBasisLaw1 : Identity Nat := ⟨⟨2, [1, 0]⟩, ⟨1, [2, 0]⟩⟩

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
  have step0 : Derives leftBasis ⟨0, [0, 1, 0]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [0]⟩)
  exact step0

theorem leftDerivesLaw2 :
    Derives leftBasis basisLaw2.lhs basisLaw2.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 1]⟩ ⟨0, [1, 0, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, [1]⟩
      | 2 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem leftDerivesLaw3 :
    Derives leftBasis basisLaw3.lhs basisLaw3.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 1]⟩ ⟨1, [0, 0, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem leftDerivesLaw4 :
    Derives leftBasis basisLaw4.lhs basisLaw4.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 1, 2]⟩ ⟨0, [1, 1, 0, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | 1 => ⟨0, [1, 1]⟩
      | 2 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem leftDerivesLaw5 :
    Derives leftBasis basisLaw5.lhs basisLaw5.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 2, 1]⟩ ⟨1, [0, 0, 2, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  exact step0

theorem leftDerivesLaw6 :
    Derives leftBasis basisLaw6.lhs basisLaw6.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 0]⟩ ⟨0, [1, 0, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [1]⟩ instantiated)
  exact step0

theorem leftDerivesLaw7 :
    Derives leftBasis basisLaw7.lhs basisLaw7.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 0, 2, 0]⟩ ⟨0, [0, 1, 2, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | 1 => ⟨0, []⟩
      | 2 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  have step1 : Derives leftBasis ⟨0, [0, 1, 2, 0]⟩ ⟨0, [1, 2, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [2, 0]⟩)
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw8 :
    Derives leftBasis basisLaw8.lhs basisLaw8.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 0, 2, 2]⟩ ⟨2, [0, 1, 0, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | 1 => ⟨2, []⟩
      | 2 => ⟨0, [1, 0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem leftDerivesLaw9 :
    Derives leftBasis basisLaw9.lhs basisLaw9.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 2, 1]⟩ ⟨0, [2, 1, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨2, []⟩
      | 2 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  exact step0

/-- 10 fixed displayed-law instances. -/
theorem displayedInLeftBasis : FiniteCertificate.DerivesAll leftBasis basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact leftDerivesLaw0
  · exact leftDerivesLaw1
  · exact leftDerivesLaw2
  · exact leftDerivesLaw3
  · exact leftDerivesLaw4
  · exact leftDerivesLaw5
  · exact leftDerivesLaw6
  · exact leftDerivesLaw7
  · exact leftDerivesLaw8
  · exact leftDerivesLaw9

def rightBasisLaw0 : Identity Nat := ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def rightBasisLaw1 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0]⟩⟩
def rightBasisLaw2 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩
def rightBasisLaw3 : Identity Nat := ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 0, 1]⟩⟩
def rightBasisLaw4 : Identity Nat := ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 1, 0]⟩⟩
def rightBasisLaw5 : Identity Nat := ⟨⟨0, [0, 1, 1]⟩, ⟨1, [0, 0, 1]⟩⟩
def rightBasisLaw6 : Identity Nat := ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 2, 0]⟩⟩
def rightBasisLaw7 : Identity Nat := ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def rightBasis : List (Identity Nat) :=
  [rightBasisLaw0, rightBasisLaw1, rightBasisLaw2, rightBasisLaw3, rightBasisLaw4, rightBasisLaw5, rightBasisLaw6, rightBasisLaw7]

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
  have step0 : Derives rightBasis ⟨0, [0, 1, 0]⟩ ⟨0, [1, 0]⟩ := by
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
  have step0 : Derives rightBasis ⟨0, [0, 1, 1]⟩ ⟨0, [1, 0, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw3.lhs rightBasisLaw3.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw3, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem rightDerivesLaw3 :
    Derives rightBasis basisLaw3.lhs basisLaw3.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 1]⟩ ⟨1, [0, 0, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw5.lhs rightBasisLaw5.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw5, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem rightDerivesLaw4 :
    Derives rightBasis basisLaw4.lhs basisLaw4.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 1, 2]⟩ ⟨0, [1, 1, 0, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw4.lhs rightBasisLaw4.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw4, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, []⟩)
  exact step0

theorem rightDerivesLaw5 :
    Derives rightBasis basisLaw5.lhs basisLaw5.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 2, 1]⟩ ⟨0, [0, 1, 1, 2, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [0]⟩ instantiated)
  have step1 : Derives rightBasis ⟨0, [0, 1, 1, 2, 1]⟩ ⟨1, [0, 0, 1, 2, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw5.lhs rightBasisLaw5.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw5, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, [1]⟩)
  have step2 : Derives rightBasis ⟨1, [0, 0, 1, 2, 1]⟩ ⟨1, [0, 0, 2, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw6.lhs rightBasisLaw6.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, [0]⟩
      | 2 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw6, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (step2))

theorem rightDerivesLaw6 :
    Derives rightBasis basisLaw6.lhs basisLaw6.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 0]⟩ ⟨0, [1, 0, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw2.lhs rightBasisLaw2.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem rightDerivesLaw7 :
    Derives rightBasis basisLaw7.lhs basisLaw7.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 0, 2, 0]⟩ ⟨0, [1, 2, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw6.lhs rightBasisLaw6.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw6, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem rightDerivesLaw8 :
    Derives rightBasis basisLaw8.lhs basisLaw8.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 0, 2, 2]⟩ ⟨0, [0, 1, 0, 2, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, [2]⟩)
  have step1 : Derives rightBasis ⟨0, [0, 1, 0, 2, 2]⟩ ⟨0, [2, 0, 1, 0, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw7.lhs rightBasisLaw7.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨2, []⟩
      | 2 => ⟨0, [1, 0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw7, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step2 : Derives rightBasis ⟨0, [2, 0, 1, 0, 2]⟩ ⟨0, [2, 2, 0, 1, 0, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | 1 => ⟨0, [1, 0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  have step3 : Derives rightBasis ⟨0, [2, 2, 0, 1, 0, 2]⟩ ⟨2, [2, 0, 0, 1, 0, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw5.lhs rightBasisLaw5.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw5, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [0, 2]⟩)
  have step4 : Derives rightBasis ⟨2, [2, 0, 0, 1, 0, 2]⟩ ⟨2, [0, 0, 1, 0, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | 1 => ⟨0, [0, 1, 0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step5 : Derives rightBasis ⟨2, [0, 0, 1, 0, 2]⟩ ⟨2, [0, 1, 0, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨2, []⟩ instantiated) ⟨2, []⟩)
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (Derives.trans step3 (Derives.trans step4 (step5)))))

theorem rightDerivesLaw9 :
    Derives rightBasis basisLaw9.lhs basisLaw9.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 2, 1]⟩ ⟨0, [2, 1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw7.lhs rightBasisLaw7.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw7, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

/-- 10 fixed displayed-law instances. -/
theorem displayedInRightBasis : FiniteCertificate.DerivesAll rightBasis basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rightDerivesLaw0
  · exact rightDerivesLaw1
  · exact rightDerivesLaw2
  · exact rightDerivesLaw3
  · exact rightDerivesLaw4
  · exact rightDerivesLaw5
  · exact rightDerivesLaw6
  · exact rightDerivesLaw7
  · exact rightDerivesLaw8
  · exact rightDerivesLaw9

private def leftTable : FiniteTable where
  order := 3
  mul := fun a b => SemigroupBasis.Generated.Catalogue.S3_15.table.mul b a
  assoc := fun a b c => (SemigroupBasis.Generated.Catalogue.S3_15.table.assoc c b a).symm

private theorem leftModelsLaw0 : basisLaw0.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_15.table.semigroup.opposite := by
  have roundTrip : (basisLaw0.map toFinThree).map Fin.val = basisLaw0 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound leftTable (basisLaw0.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw1 : basisLaw1.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_15.table.semigroup.opposite := by
  have roundTrip : (basisLaw1.map toFinThree).map Fin.val = basisLaw1 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound leftTable (basisLaw1.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw2 : basisLaw2.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_15.table.semigroup.opposite := by
  have roundTrip : (basisLaw2.map toFinThree).map Fin.val = basisLaw2 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound leftTable (basisLaw2.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw3 : basisLaw3.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_15.table.semigroup.opposite := by
  have roundTrip : (basisLaw3.map toFinThree).map Fin.val = basisLaw3 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound leftTable (basisLaw3.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw4 : basisLaw4.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_15.table.semigroup.opposite := by
  have roundTrip : (basisLaw4.map toFinThree).map Fin.val = basisLaw4 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound leftTable (basisLaw4.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw5 : basisLaw5.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_15.table.semigroup.opposite := by
  have roundTrip : (basisLaw5.map toFinThree).map Fin.val = basisLaw5 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound leftTable (basisLaw5.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw6 : basisLaw6.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_15.table.semigroup.opposite := by
  have roundTrip : (basisLaw6.map toFinThree).map Fin.val = basisLaw6 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound leftTable (basisLaw6.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw7 : basisLaw7.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_15.table.semigroup.opposite := by
  have roundTrip : (basisLaw7.map toFinThree).map Fin.val = basisLaw7 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound leftTable (basisLaw7.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw8 : basisLaw8.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_15.table.semigroup.opposite := by
  have roundTrip : (basisLaw8.map toFinThree).map Fin.val = basisLaw8 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound leftTable (basisLaw8.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw9 : basisLaw9.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_15.table.semigroup.opposite := by
  have roundTrip : (basisLaw9.map toFinThree).map Fin.val = basisLaw9 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound leftTable (basisLaw9.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem leftModels : Models SemigroupBasis.Generated.Catalogue.S3_15.table.semigroup.opposite basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact leftModelsLaw0
  · exact leftModelsLaw1
  · exact leftModelsLaw2
  · exact leftModelsLaw3
  · exact leftModelsLaw4
  · exact leftModelsLaw5
  · exact leftModelsLaw6
  · exact leftModelsLaw7
  · exact leftModelsLaw8
  · exact leftModelsLaw9

private theorem rightModelsLaw0 : basisLaw0.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_610.table.semigroup := by
  have roundTrip : (basisLaw0.map toFinThree).map Fin.val = basisLaw0 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_610.table (basisLaw0.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw1 : basisLaw1.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_610.table.semigroup := by
  have roundTrip : (basisLaw1.map toFinThree).map Fin.val = basisLaw1 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_610.table (basisLaw1.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw2 : basisLaw2.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_610.table.semigroup := by
  have roundTrip : (basisLaw2.map toFinThree).map Fin.val = basisLaw2 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_610.table (basisLaw2.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw3 : basisLaw3.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_610.table.semigroup := by
  have roundTrip : (basisLaw3.map toFinThree).map Fin.val = basisLaw3 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_610.table (basisLaw3.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw4 : basisLaw4.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_610.table.semigroup := by
  have roundTrip : (basisLaw4.map toFinThree).map Fin.val = basisLaw4 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_610.table (basisLaw4.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw5 : basisLaw5.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_610.table.semigroup := by
  have roundTrip : (basisLaw5.map toFinThree).map Fin.val = basisLaw5 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_610.table (basisLaw5.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw6 : basisLaw6.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_610.table.semigroup := by
  have roundTrip : (basisLaw6.map toFinThree).map Fin.val = basisLaw6 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_610.table (basisLaw6.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw7 : basisLaw7.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_610.table.semigroup := by
  have roundTrip : (basisLaw7.map toFinThree).map Fin.val = basisLaw7 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_610.table (basisLaw7.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw8 : basisLaw8.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_610.table.semigroup := by
  have roundTrip : (basisLaw8.map toFinThree).map Fin.val = basisLaw8 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_610.table (basisLaw8.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw9 : basisLaw9.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_610.table.semigroup := by
  have roundTrip : (basisLaw9.map toFinThree).map Fin.val = basisLaw9 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_610.table (basisLaw9.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem rightModels : Models SemigroupBasis.Generated.Catalogue.S5_610.table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rightModelsLaw0
  · exact rightModelsLaw1
  · exact rightModelsLaw2
  · exact rightModelsLaw3
  · exact rightModelsLaw4
  · exact rightModelsLaw5
  · exact rightModelsLaw6
  · exact rightModelsLaw7
  · exact rightModelsLaw8
  · exact rightModelsLaw9

namespace S6_10934

/-- Exact catalogue table SHA256 `92e2ce85fec634a4eb85082bd0e6752716b7d0f30e3c1d94b12be3475e15c627`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6)) else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (2 : Fin 6)) else if a = 3 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (3 : Fin 6)) else if a = 4 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (2 : Fin 6)) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def ontoLeftMap (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (1 : Fin 3) else if a = 3 then (1 : Fin 3) else if a = 4 then (2 : Fin 3) else (1 : Fin 3)

def ontoLeftSection (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else (4 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S3_15.table.semigroup.opposite where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (3 : Fin 5) else if a = 4 then (2 : Fin 5) else (4 : Fin 5)

def ontoRightSection (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_610.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.Catalogue.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_610.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro a b
    exact by decide +revert

theorem models : Models table.semigroup basis := by
  intro identity member
  exact (pair.satisfiedBy_iff identity).mpr ⟨leftModels identity member, rightModels identity member⟩

def ontoLeftOpposite : SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S3_15.table.semigroup.opposite.opposite where
  toFun := ontoLeftMap
  map_mul := fun a b => ontoLeft.map_mul b a
  preimage := ontoLeftSection
  right_inverse := ontoLeft.right_inverse

def ontoRightOpposite : SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_610.table.semigroup.opposite where
  toFun := ontoRightMap
  map_mul := fun a b => ontoRight.map_mul b a
  preimage := ontoRightSection
  right_inverse := ontoRight.right_inverse

def pairOpposite : SubdirectPair table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S3_15.table.semigroup.opposite.opposite SemigroupBasis.Generated.Catalogue.S5_610.table.semigroup.opposite where
  left := ontoLeftOpposite
  right := ontoRightOpposite
  jointlyInjective := pair.jointlyInjective

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) :=
  models.oppositeReversed

end S6_10934

namespace S6_11222

/-- Exact catalogue table SHA256 `00a82ffa1363aa686a0d3c4634f9e8e93d9eea6d9bec9c3c4caf3917e29f5bee`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6)) else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)) else if a = 3 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6)) else if a = 4 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def ontoLeftMap (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (1 : Fin 3) else (2 : Fin 3)

def ontoLeftSection (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (4 : Fin 6) else (5 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S3_15.table.semigroup.opposite where
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

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_610.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.Catalogue.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_610.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro a b
    exact by decide +revert

theorem models : Models table.semigroup basis := by
  intro identity member
  exact (pair.satisfiedBy_iff identity).mpr ⟨leftModels identity member, rightModels identity member⟩

def ontoLeftOpposite : SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S3_15.table.semigroup.opposite.opposite where
  toFun := ontoLeftMap
  map_mul := fun a b => ontoLeft.map_mul b a
  preimage := ontoLeftSection
  right_inverse := ontoLeft.right_inverse

def ontoRightOpposite : SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_610.table.semigroup.opposite where
  toFun := ontoRightMap
  map_mul := fun a b => ontoRight.map_mul b a
  preimage := ontoRightSection
  right_inverse := ontoRight.right_inverse

def pairOpposite : SubdirectPair table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S3_15.table.semigroup.opposite.opposite SemigroupBasis.Generated.Catalogue.S5_610.table.semigroup.opposite where
  left := ontoLeftOpposite
  right := ontoRightOpposite
  jointlyInjective := pair.jointlyInjective

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) :=
  models.oppositeReversed

end S6_11222

end Sigma17bb

namespace Sigma086fa

def basisLaw0 : Identity Nat := ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩
def basisLaw1 : Identity Nat := ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0, 1, 1]⟩⟩
def basisLaw2 : Identity Nat := ⟨⟨0, [0, 1]⟩, ⟨0, [1, 1, 0, 1]⟩⟩
def basisLaw3 : Identity Nat := ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩
def basisLaw4 : Identity Nat := ⟨⟨0, [0, 1, 0, 0]⟩, ⟨0, [1, 0]⟩⟩
def basisLaw5 : Identity Nat := ⟨⟨0, [0, 1, 0, 1]⟩, ⟨0, [1, 1]⟩⟩
def basisLaw6 : Identity Nat := ⟨⟨0, [0, 1, 0, 2]⟩, ⟨0, [1, 2]⟩⟩
def basisLaw7 : Identity Nat := ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 0, 1]⟩⟩
def basisLaw8 : Identity Nat := ⟨⟨0, [0, 1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩
def basisLaw9 : Identity Nat := ⟨⟨0, [1, 0, 0, 1]⟩, ⟨0, [1, 1]⟩⟩
def basisLaw10 : Identity Nat := ⟨⟨0, [1, 0, 0, 2]⟩, ⟨0, [1, 2]⟩⟩

def basis : List (Identity Nat) :=
  [basisLaw0, basisLaw1, basisLaw2, basisLaw3, basisLaw4, basisLaw5, basisLaw6, basisLaw7, basisLaw8, basisLaw9, basisLaw10]

def leftBasisLaw0 : Identity Nat := ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩
def leftBasisLaw1 : Identity Nat := ⟨⟨0, [0, 1]⟩, ⟨1, []⟩⟩

def leftBasis : List (Identity Nat) :=
  [leftBasisLaw0, leftBasisLaw1]

theorem leftDerivesLaw0 :
    Derives leftBasis basisLaw0.lhs basisLaw0.rhs := by
  have step0 : Derives leftBasis ⟨0, []⟩ ⟨0, [0, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem leftDerivesLaw1 :
    Derives leftBasis basisLaw1.lhs basisLaw1.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1]⟩ ⟨1, []⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives leftBasis ⟨1, []⟩ ⟨0, [1, 0, 1, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [1]⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw2 :
    Derives leftBasis basisLaw2.lhs basisLaw2.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1]⟩ ⟨0, [1, 1, 0, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, []⟩ instantiated) ⟨1, []⟩)
  exact step0

theorem leftDerivesLaw3 :
    Derives leftBasis basisLaw3.lhs basisLaw3.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 0]⟩ ⟨0, [1, 0, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  exact step0

theorem leftDerivesLaw4 :
    Derives leftBasis basisLaw4.lhs basisLaw4.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 0, 0]⟩ ⟨0, [1, 0, 0, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, [0]⟩)
  have step1 : Derives leftBasis ⟨0, [1, 0, 0, 0]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [1]⟩ instantiated)
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw5 :
    Derives leftBasis basisLaw5.lhs basisLaw5.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 0, 1]⟩ ⟨0, [1, 0, 0, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, [1]⟩)
  have step1 : Derives leftBasis ⟨0, [1, 0, 0, 1]⟩ ⟨0, [1, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [1]⟩ instantiated)
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw6 :
    Derives leftBasis basisLaw6.lhs basisLaw6.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 0, 2]⟩ ⟨0, [1, 0, 0, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, [2]⟩)
  have step1 : Derives leftBasis ⟨0, [1, 0, 0, 2]⟩ ⟨0, [1, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [1]⟩ instantiated)
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw7 :
    Derives leftBasis basisLaw7.lhs basisLaw7.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 1]⟩ ⟨0, [1, 0, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  exact step0

theorem leftDerivesLaw8 :
    Derives leftBasis basisLaw8.lhs basisLaw8.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 2]⟩ ⟨0, [1, 0, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, []⟩)
  exact step0

theorem leftDerivesLaw9 :
    Derives leftBasis basisLaw9.lhs basisLaw9.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 0, 0, 1]⟩ ⟨0, [1, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [1]⟩ instantiated)
  exact step0

theorem leftDerivesLaw10 :
    Derives leftBasis basisLaw10.lhs basisLaw10.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 0, 0, 2]⟩ ⟨0, [1, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [1]⟩ instantiated)
  exact step0

/-- 11 fixed displayed-law instances. -/
theorem displayedInLeftBasis : FiniteCertificate.DerivesAll leftBasis basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact leftDerivesLaw0
  · exact leftDerivesLaw1
  · exact leftDerivesLaw2
  · exact leftDerivesLaw3
  · exact leftDerivesLaw4
  · exact leftDerivesLaw5
  · exact leftDerivesLaw6
  · exact leftDerivesLaw7
  · exact leftDerivesLaw8
  · exact leftDerivesLaw9
  · exact leftDerivesLaw10

def rightBasisLaw0 : Identity Nat := ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def rightBasisLaw1 : Identity Nat := ⟨⟨0, [1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

def rightBasis : List (Identity Nat) :=
  [rightBasisLaw0, rightBasisLaw1]

theorem rightDerivesLaw0 :
    Derives rightBasis basisLaw0.lhs basisLaw0.rhs := by
  have step0 : Derives rightBasis ⟨0, []⟩ ⟨0, [0]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives rightBasis ⟨0, [0]⟩ ⟨0, [0, 0]⟩ := by
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
  have step0 : Derives rightBasis ⟨0, [0, 1]⟩ ⟨0, [0, 1, 0, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  have step1 : Derives rightBasis ⟨0, [0, 1, 0, 1]⟩ ⟨0, [0, 1, 0, 1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [0, 1, 0]⟩ instantiated)
  have step2 : Derives rightBasis ⟨0, [0, 1, 0, 1, 1]⟩ ⟨0, [1, 0, 1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [0, 1, 1]⟩)
  exact Derives.trans step0 (Derives.trans step1 (step2))

theorem rightDerivesLaw2 :
    Derives rightBasis basisLaw2.lhs basisLaw2.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1]⟩ ⟨0, [0, 1, 0, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  have step1 : Derives rightBasis ⟨0, [0, 1, 0, 1]⟩ ⟨0, [0, 1, 1, 0, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, [0]⟩ instantiated) ⟨0, [1]⟩)
  have step2 : Derives rightBasis ⟨0, [0, 1, 1, 0, 1]⟩ ⟨0, [1, 1, 0, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [1, 0, 1]⟩)
  exact Derives.trans step0 (Derives.trans step1 (step2))

theorem rightDerivesLaw3 :
    Derives rightBasis basisLaw3.lhs basisLaw3.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 0]⟩ ⟨0, [0, 1, 0, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [0, 1]⟩ instantiated)
  have step1 : Derives rightBasis ⟨0, [0, 1, 0, 0]⟩ ⟨0, [1, 0, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [0, 0]⟩)
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw4 :
    Derives rightBasis basisLaw4.lhs basisLaw4.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 0, 0]⟩ ⟨0, [1, 0, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [0, 0]⟩)
  have step1 : Derives rightBasis ⟨0, [1, 0, 0]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [1]⟩ instantiated)
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw5 :
    Derives rightBasis basisLaw5.lhs basisLaw5.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 0, 1]⟩ ⟨0, [1, 0, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [0, 1]⟩)
  have step1 : Derives rightBasis ⟨0, [1, 0, 1]⟩ ⟨0, [1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw6 :
    Derives rightBasis basisLaw6.lhs basisLaw6.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 0, 2]⟩ ⟨0, [1, 0, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [0, 2]⟩)
  have step1 : Derives rightBasis ⟨0, [1, 0, 2]⟩ ⟨0, [1, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw7 :
    Derives rightBasis basisLaw7.lhs basisLaw7.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 1]⟩ ⟨0, [1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [1]⟩)
  have step1 : Derives rightBasis ⟨0, [1, 1]⟩ ⟨0, [1, 0, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw8 :
    Derives rightBasis basisLaw8.lhs basisLaw8.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 2]⟩ ⟨0, [1, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [2]⟩)
  have step1 : Derives rightBasis ⟨0, [1, 2]⟩ ⟨0, [1, 0, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw9 :
    Derives rightBasis basisLaw9.lhs basisLaw9.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 0, 0, 1]⟩ ⟨0, [1, 0, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, [1]⟩ instantiated) ⟨1, []⟩)
  have step1 : Derives rightBasis ⟨0, [1, 0, 1]⟩ ⟨0, [1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw10 :
    Derives rightBasis basisLaw10.lhs basisLaw10.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 0, 0, 2]⟩ ⟨0, [1, 0, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, [1]⟩ instantiated) ⟨2, []⟩)
  have step1 : Derives rightBasis ⟨0, [1, 0, 2]⟩ ⟨0, [1, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

/-- 11 fixed displayed-law instances. -/
theorem displayedInRightBasis : FiniteCertificate.DerivesAll rightBasis basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rightDerivesLaw0
  · exact rightDerivesLaw1
  · exact rightDerivesLaw2
  · exact rightDerivesLaw3
  · exact rightDerivesLaw4
  · exact rightDerivesLaw5
  · exact rightDerivesLaw6
  · exact rightDerivesLaw7
  · exact rightDerivesLaw8
  · exact rightDerivesLaw9
  · exact rightDerivesLaw10

private theorem leftModelsLaw0 : basisLaw0.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup := by
  have roundTrip : (basisLaw0.map toFinThree).map Fin.val = basisLaw0 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_2.table (basisLaw0.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw1 : basisLaw1.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup := by
  have roundTrip : (basisLaw1.map toFinThree).map Fin.val = basisLaw1 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_2.table (basisLaw1.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw2 : basisLaw2.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup := by
  have roundTrip : (basisLaw2.map toFinThree).map Fin.val = basisLaw2 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_2.table (basisLaw2.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw3 : basisLaw3.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup := by
  have roundTrip : (basisLaw3.map toFinThree).map Fin.val = basisLaw3 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_2.table (basisLaw3.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw4 : basisLaw4.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup := by
  have roundTrip : (basisLaw4.map toFinThree).map Fin.val = basisLaw4 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_2.table (basisLaw4.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw5 : basisLaw5.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup := by
  have roundTrip : (basisLaw5.map toFinThree).map Fin.val = basisLaw5 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_2.table (basisLaw5.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw6 : basisLaw6.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup := by
  have roundTrip : (basisLaw6.map toFinThree).map Fin.val = basisLaw6 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_2.table (basisLaw6.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw7 : basisLaw7.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup := by
  have roundTrip : (basisLaw7.map toFinThree).map Fin.val = basisLaw7 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_2.table (basisLaw7.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw8 : basisLaw8.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup := by
  have roundTrip : (basisLaw8.map toFinThree).map Fin.val = basisLaw8 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_2.table (basisLaw8.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw9 : basisLaw9.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup := by
  have roundTrip : (basisLaw9.map toFinThree).map Fin.val = basisLaw9 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_2.table (basisLaw9.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw10 : basisLaw10.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup := by
  have roundTrip : (basisLaw10.map toFinThree).map Fin.val = basisLaw10 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_2.table (basisLaw10.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem leftModels : Models SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact leftModelsLaw0
  · exact leftModelsLaw1
  · exact leftModelsLaw2
  · exact leftModelsLaw3
  · exact leftModelsLaw4
  · exact leftModelsLaw5
  · exact leftModelsLaw6
  · exact leftModelsLaw7
  · exact leftModelsLaw8
  · exact leftModelsLaw9
  · exact leftModelsLaw10

private theorem rightModelsLaw0 : basisLaw0.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup := by
  have roundTrip : (basisLaw0.map toFinThree).map Fin.val = basisLaw0 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S4_120.table (basisLaw0.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw1 : basisLaw1.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup := by
  have roundTrip : (basisLaw1.map toFinThree).map Fin.val = basisLaw1 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S4_120.table (basisLaw1.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw2 : basisLaw2.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup := by
  have roundTrip : (basisLaw2.map toFinThree).map Fin.val = basisLaw2 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S4_120.table (basisLaw2.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw3 : basisLaw3.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup := by
  have roundTrip : (basisLaw3.map toFinThree).map Fin.val = basisLaw3 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S4_120.table (basisLaw3.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw4 : basisLaw4.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup := by
  have roundTrip : (basisLaw4.map toFinThree).map Fin.val = basisLaw4 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S4_120.table (basisLaw4.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw5 : basisLaw5.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup := by
  have roundTrip : (basisLaw5.map toFinThree).map Fin.val = basisLaw5 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S4_120.table (basisLaw5.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw6 : basisLaw6.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup := by
  have roundTrip : (basisLaw6.map toFinThree).map Fin.val = basisLaw6 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S4_120.table (basisLaw6.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw7 : basisLaw7.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup := by
  have roundTrip : (basisLaw7.map toFinThree).map Fin.val = basisLaw7 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S4_120.table (basisLaw7.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw8 : basisLaw8.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup := by
  have roundTrip : (basisLaw8.map toFinThree).map Fin.val = basisLaw8 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S4_120.table (basisLaw8.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw9 : basisLaw9.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup := by
  have roundTrip : (basisLaw9.map toFinThree).map Fin.val = basisLaw9 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S4_120.table (basisLaw9.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw10 : basisLaw10.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup := by
  have roundTrip : (basisLaw10.map toFinThree).map Fin.val = basisLaw10 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S4_120.table (basisLaw10.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem rightModels : Models SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rightModelsLaw0
  · exact rightModelsLaw1
  · exact rightModelsLaw2
  · exact rightModelsLaw3
  · exact rightModelsLaw4
  · exact rightModelsLaw5
  · exact rightModelsLaw6
  · exact rightModelsLaw7
  · exact rightModelsLaw8
  · exact rightModelsLaw9
  · exact rightModelsLaw10

namespace S6_11897

/-- Exact catalogue table SHA256 `470cc19354bd54c6b69687e6871288ddad8a8c30e31d427ba1a0f060fa85f9eb`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6)) else if a = 2 then (if b = 0 then (2 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)) else if a = 3 then (if b = 0 then (3 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6)) else if a = 4 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def ontoLeftMap (a : Fin 6) : Fin 2 :=
  if a = 0 then (0 : Fin 2) else if a = 1 then (1 : Fin 2) else if a = 2 then (0 : Fin 2) else if a = 3 then (1 : Fin 2) else if a = 4 then (0 : Fin 2) else (0 : Fin 2)

def ontoLeftSection (a : Fin 2) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else (1 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (3 : Fin 4) else if a = 3 then (3 : Fin 4) else if a = 4 then (1 : Fin 4) else (2 : Fin 4)

def ontoRightSection (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (4 : Fin 6) else if a = 2 then (5 : Fin 6) else (2 : Fin 6)

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro a b
    exact by decide +revert

theorem models : Models table.semigroup basis := by
  intro identity member
  exact (pair.satisfiedBy_iff identity).mpr ⟨leftModels identity member, rightModels identity member⟩

def ontoLeftOpposite : SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup.opposite where
  toFun := ontoLeftMap
  map_mul := fun a b => ontoLeft.map_mul b a
  preimage := ontoLeftSection
  right_inverse := ontoLeft.right_inverse

def ontoRightOpposite : SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup.opposite where
  toFun := ontoRightMap
  map_mul := fun a b => ontoRight.map_mul b a
  preimage := ontoRightSection
  right_inverse := ontoRight.right_inverse

def pairOpposite : SubdirectPair table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup.opposite where
  left := ontoLeftOpposite
  right := ontoRightOpposite
  jointlyInjective := pair.jointlyInjective

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) :=
  models.oppositeReversed

end S6_11897

end Sigma086fa

namespace Sigma086fb

def basisLaw0 : Identity Nat := ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩
def basisLaw1 : Identity Nat := ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0, 1, 1]⟩⟩
def basisLaw2 : Identity Nat := ⟨⟨0, [0, 1]⟩, ⟨0, [1, 1, 0, 1]⟩⟩
def basisLaw3 : Identity Nat := ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩
def basisLaw4 : Identity Nat := ⟨⟨0, [0, 1, 0, 0]⟩, ⟨0, [1, 0]⟩⟩
def basisLaw5 : Identity Nat := ⟨⟨0, [0, 1, 0, 1]⟩, ⟨0, [1, 1]⟩⟩
def basisLaw6 : Identity Nat := ⟨⟨0, [0, 1, 0, 2]⟩, ⟨0, [1, 2]⟩⟩
def basisLaw7 : Identity Nat := ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 0, 1]⟩⟩
def basisLaw8 : Identity Nat := ⟨⟨0, [0, 1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩
def basisLaw9 : Identity Nat := ⟨⟨0, [1, 0, 0, 1]⟩, ⟨0, [1, 1]⟩⟩
def basisLaw10 : Identity Nat := ⟨⟨0, [1, 0, 0, 2]⟩, ⟨0, [1, 2]⟩⟩

def basis : List (Identity Nat) :=
  [basisLaw0, basisLaw1, basisLaw2, basisLaw3, basisLaw4, basisLaw5, basisLaw6, basisLaw7, basisLaw8, basisLaw9, basisLaw10]

def leftBasisLaw0 : Identity Nat := ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩
def leftBasisLaw1 : Identity Nat := ⟨⟨0, [0, 1]⟩, ⟨1, []⟩⟩

def leftBasis : List (Identity Nat) :=
  [leftBasisLaw0, leftBasisLaw1]

theorem leftDerivesLaw0 :
    Derives leftBasis basisLaw0.lhs basisLaw0.rhs := by
  have step0 : Derives leftBasis ⟨0, []⟩ ⟨0, [0, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem leftDerivesLaw1 :
    Derives leftBasis basisLaw1.lhs basisLaw1.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1]⟩ ⟨1, []⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives leftBasis ⟨1, []⟩ ⟨0, [1, 0, 1, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [1]⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw2 :
    Derives leftBasis basisLaw2.lhs basisLaw2.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1]⟩ ⟨0, [1, 1, 0, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, []⟩ instantiated) ⟨1, []⟩)
  exact step0

theorem leftDerivesLaw3 :
    Derives leftBasis basisLaw3.lhs basisLaw3.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 0]⟩ ⟨0, [1, 0, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  exact step0

theorem leftDerivesLaw4 :
    Derives leftBasis basisLaw4.lhs basisLaw4.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 0, 0]⟩ ⟨0, [1, 0, 0, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, [0]⟩)
  have step1 : Derives leftBasis ⟨0, [1, 0, 0, 0]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [1]⟩ instantiated)
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw5 :
    Derives leftBasis basisLaw5.lhs basisLaw5.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 0, 1]⟩ ⟨0, [1, 0, 0, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, [1]⟩)
  have step1 : Derives leftBasis ⟨0, [1, 0, 0, 1]⟩ ⟨0, [1, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [1]⟩ instantiated)
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw6 :
    Derives leftBasis basisLaw6.lhs basisLaw6.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 0, 2]⟩ ⟨0, [1, 0, 0, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, [2]⟩)
  have step1 : Derives leftBasis ⟨0, [1, 0, 0, 2]⟩ ⟨0, [1, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [1]⟩ instantiated)
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw7 :
    Derives leftBasis basisLaw7.lhs basisLaw7.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 1]⟩ ⟨0, [1, 0, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  exact step0

theorem leftDerivesLaw8 :
    Derives leftBasis basisLaw8.lhs basisLaw8.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 2]⟩ ⟨0, [1, 0, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, []⟩)
  exact step0

theorem leftDerivesLaw9 :
    Derives leftBasis basisLaw9.lhs basisLaw9.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 0, 0, 1]⟩ ⟨0, [1, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [1]⟩ instantiated)
  exact step0

theorem leftDerivesLaw10 :
    Derives leftBasis basisLaw10.lhs basisLaw10.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 0, 0, 2]⟩ ⟨0, [1, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [1]⟩ instantiated)
  exact step0

/-- 11 fixed displayed-law instances. -/
theorem displayedInLeftBasis : FiniteCertificate.DerivesAll leftBasis basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact leftDerivesLaw0
  · exact leftDerivesLaw1
  · exact leftDerivesLaw2
  · exact leftDerivesLaw3
  · exact leftDerivesLaw4
  · exact leftDerivesLaw5
  · exact leftDerivesLaw6
  · exact leftDerivesLaw7
  · exact leftDerivesLaw8
  · exact leftDerivesLaw9
  · exact leftDerivesLaw10

def rightBasisLaw0 : Identity Nat := ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def rightBasisLaw1 : Identity Nat := ⟨⟨0, [1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

def rightBasis : List (Identity Nat) :=
  [rightBasisLaw0, rightBasisLaw1]

theorem rightDerivesLaw0 :
    Derives rightBasis basisLaw0.lhs basisLaw0.rhs := by
  have step0 : Derives rightBasis ⟨0, []⟩ ⟨0, [0]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives rightBasis ⟨0, [0]⟩ ⟨0, [0, 0]⟩ := by
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
  have step0 : Derives rightBasis ⟨0, [0, 1]⟩ ⟨0, [0, 1, 0, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  have step1 : Derives rightBasis ⟨0, [0, 1, 0, 1]⟩ ⟨0, [0, 1, 0, 1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [0, 1, 0]⟩ instantiated)
  have step2 : Derives rightBasis ⟨0, [0, 1, 0, 1, 1]⟩ ⟨0, [1, 0, 1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [0, 1, 1]⟩)
  exact Derives.trans step0 (Derives.trans step1 (step2))

theorem rightDerivesLaw2 :
    Derives rightBasis basisLaw2.lhs basisLaw2.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1]⟩ ⟨0, [0, 1, 0, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  have step1 : Derives rightBasis ⟨0, [0, 1, 0, 1]⟩ ⟨0, [0, 1, 1, 0, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, [0]⟩ instantiated) ⟨0, [1]⟩)
  have step2 : Derives rightBasis ⟨0, [0, 1, 1, 0, 1]⟩ ⟨0, [1, 1, 0, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [1, 0, 1]⟩)
  exact Derives.trans step0 (Derives.trans step1 (step2))

theorem rightDerivesLaw3 :
    Derives rightBasis basisLaw3.lhs basisLaw3.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 0]⟩ ⟨0, [0, 1, 0, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [0, 1]⟩ instantiated)
  have step1 : Derives rightBasis ⟨0, [0, 1, 0, 0]⟩ ⟨0, [1, 0, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [0, 0]⟩)
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw4 :
    Derives rightBasis basisLaw4.lhs basisLaw4.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 0, 0]⟩ ⟨0, [1, 0, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [0, 0]⟩)
  have step1 : Derives rightBasis ⟨0, [1, 0, 0]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [1]⟩ instantiated)
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw5 :
    Derives rightBasis basisLaw5.lhs basisLaw5.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 0, 1]⟩ ⟨0, [1, 0, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [0, 1]⟩)
  have step1 : Derives rightBasis ⟨0, [1, 0, 1]⟩ ⟨0, [1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw6 :
    Derives rightBasis basisLaw6.lhs basisLaw6.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 0, 2]⟩ ⟨0, [1, 0, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [0, 2]⟩)
  have step1 : Derives rightBasis ⟨0, [1, 0, 2]⟩ ⟨0, [1, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw7 :
    Derives rightBasis basisLaw7.lhs basisLaw7.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 1]⟩ ⟨0, [1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [1]⟩)
  have step1 : Derives rightBasis ⟨0, [1, 1]⟩ ⟨0, [1, 0, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw8 :
    Derives rightBasis basisLaw8.lhs basisLaw8.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 2]⟩ ⟨0, [1, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [2]⟩)
  have step1 : Derives rightBasis ⟨0, [1, 2]⟩ ⟨0, [1, 0, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw9 :
    Derives rightBasis basisLaw9.lhs basisLaw9.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 0, 0, 1]⟩ ⟨0, [1, 0, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, [1]⟩ instantiated) ⟨1, []⟩)
  have step1 : Derives rightBasis ⟨0, [1, 0, 1]⟩ ⟨0, [1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw10 :
    Derives rightBasis basisLaw10.lhs basisLaw10.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 0, 0, 2]⟩ ⟨0, [1, 0, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, [1]⟩ instantiated) ⟨2, []⟩)
  have step1 : Derives rightBasis ⟨0, [1, 0, 2]⟩ ⟨0, [1, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

/-- 11 fixed displayed-law instances. -/
theorem displayedInRightBasis : FiniteCertificate.DerivesAll rightBasis basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rightDerivesLaw0
  · exact rightDerivesLaw1
  · exact rightDerivesLaw2
  · exact rightDerivesLaw3
  · exact rightDerivesLaw4
  · exact rightDerivesLaw5
  · exact rightDerivesLaw6
  · exact rightDerivesLaw7
  · exact rightDerivesLaw8
  · exact rightDerivesLaw9
  · exact rightDerivesLaw10

private theorem leftModelsLaw0 : basisLaw0.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup := by
  have roundTrip : (basisLaw0.map toFinThree).map Fin.val = basisLaw0 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_2.table (basisLaw0.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw1 : basisLaw1.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup := by
  have roundTrip : (basisLaw1.map toFinThree).map Fin.val = basisLaw1 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_2.table (basisLaw1.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw2 : basisLaw2.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup := by
  have roundTrip : (basisLaw2.map toFinThree).map Fin.val = basisLaw2 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_2.table (basisLaw2.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw3 : basisLaw3.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup := by
  have roundTrip : (basisLaw3.map toFinThree).map Fin.val = basisLaw3 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_2.table (basisLaw3.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw4 : basisLaw4.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup := by
  have roundTrip : (basisLaw4.map toFinThree).map Fin.val = basisLaw4 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_2.table (basisLaw4.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw5 : basisLaw5.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup := by
  have roundTrip : (basisLaw5.map toFinThree).map Fin.val = basisLaw5 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_2.table (basisLaw5.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw6 : basisLaw6.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup := by
  have roundTrip : (basisLaw6.map toFinThree).map Fin.val = basisLaw6 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_2.table (basisLaw6.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw7 : basisLaw7.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup := by
  have roundTrip : (basisLaw7.map toFinThree).map Fin.val = basisLaw7 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_2.table (basisLaw7.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw8 : basisLaw8.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup := by
  have roundTrip : (basisLaw8.map toFinThree).map Fin.val = basisLaw8 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_2.table (basisLaw8.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw9 : basisLaw9.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup := by
  have roundTrip : (basisLaw9.map toFinThree).map Fin.val = basisLaw9 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_2.table (basisLaw9.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw10 : basisLaw10.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup := by
  have roundTrip : (basisLaw10.map toFinThree).map Fin.val = basisLaw10 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_2.table (basisLaw10.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem leftModels : Models SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact leftModelsLaw0
  · exact leftModelsLaw1
  · exact leftModelsLaw2
  · exact leftModelsLaw3
  · exact leftModelsLaw4
  · exact leftModelsLaw5
  · exact leftModelsLaw6
  · exact leftModelsLaw7
  · exact leftModelsLaw8
  · exact leftModelsLaw9
  · exact leftModelsLaw10

private theorem rightModelsLaw0 : basisLaw0.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_1123.table.semigroup := by
  have roundTrip : (basisLaw0.map toFinThree).map Fin.val = basisLaw0 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_1123.table (basisLaw0.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw1 : basisLaw1.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_1123.table.semigroup := by
  have roundTrip : (basisLaw1.map toFinThree).map Fin.val = basisLaw1 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_1123.table (basisLaw1.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw2 : basisLaw2.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_1123.table.semigroup := by
  have roundTrip : (basisLaw2.map toFinThree).map Fin.val = basisLaw2 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_1123.table (basisLaw2.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw3 : basisLaw3.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_1123.table.semigroup := by
  have roundTrip : (basisLaw3.map toFinThree).map Fin.val = basisLaw3 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_1123.table (basisLaw3.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw4 : basisLaw4.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_1123.table.semigroup := by
  have roundTrip : (basisLaw4.map toFinThree).map Fin.val = basisLaw4 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_1123.table (basisLaw4.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw5 : basisLaw5.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_1123.table.semigroup := by
  have roundTrip : (basisLaw5.map toFinThree).map Fin.val = basisLaw5 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_1123.table (basisLaw5.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw6 : basisLaw6.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_1123.table.semigroup := by
  have roundTrip : (basisLaw6.map toFinThree).map Fin.val = basisLaw6 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_1123.table (basisLaw6.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw7 : basisLaw7.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_1123.table.semigroup := by
  have roundTrip : (basisLaw7.map toFinThree).map Fin.val = basisLaw7 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_1123.table (basisLaw7.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw8 : basisLaw8.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_1123.table.semigroup := by
  have roundTrip : (basisLaw8.map toFinThree).map Fin.val = basisLaw8 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_1123.table (basisLaw8.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw9 : basisLaw9.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_1123.table.semigroup := by
  have roundTrip : (basisLaw9.map toFinThree).map Fin.val = basisLaw9 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_1123.table (basisLaw9.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw10 : basisLaw10.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_1123.table.semigroup := by
  have roundTrip : (basisLaw10.map toFinThree).map Fin.val = basisLaw10 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_1123.table (basisLaw10.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem rightModels : Models SemigroupBasis.Generated.Catalogue.S5_1123.table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rightModelsLaw0
  · exact rightModelsLaw1
  · exact rightModelsLaw2
  · exact rightModelsLaw3
  · exact rightModelsLaw4
  · exact rightModelsLaw5
  · exact rightModelsLaw6
  · exact rightModelsLaw7
  · exact rightModelsLaw8
  · exact rightModelsLaw9
  · exact rightModelsLaw10

namespace S6_14651

/-- Exact catalogue table SHA256 `db108d61c6c1bf1f27af258e87a45da5b85b492530b6072873a8169053aa92c6`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6)) else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)) else if a = 3 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if a = 4 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def ontoLeftMap (a : Fin 6) : Fin 2 :=
  if a = 0 then (0 : Fin 2) else if a = 1 then (1 : Fin 2) else if a = 2 then (0 : Fin 2) else if a = 3 then (0 : Fin 2) else if a = 4 then (0 : Fin 2) else (0 : Fin 2)

def ontoLeftSection (a : Fin 2) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else (1 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup where
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

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_1123.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup SemigroupBasis.Generated.Catalogue.S5_1123.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro a b
    exact by decide +revert

theorem models : Models table.semigroup basis := by
  intro identity member
  exact (pair.satisfiedBy_iff identity).mpr ⟨leftModels identity member, rightModels identity member⟩

def ontoLeftOpposite : SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup.opposite where
  toFun := ontoLeftMap
  map_mul := fun a b => ontoLeft.map_mul b a
  preimage := ontoLeftSection
  right_inverse := ontoLeft.right_inverse

def ontoRightOpposite : SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_1123.table.semigroup.opposite where
  toFun := ontoRightMap
  map_mul := fun a b => ontoRight.map_mul b a
  preimage := ontoRightSection
  right_inverse := ontoRight.right_inverse

def pairOpposite : SubdirectPair table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_1123.table.semigroup.opposite where
  left := ontoLeftOpposite
  right := ontoRightOpposite
  jointlyInjective := pair.jointlyInjective

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) :=
  models.oppositeReversed

end S6_14651

end Sigma086fb

namespace Sigma086fc

def basisLaw0 : Identity Nat := ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩
def basisLaw1 : Identity Nat := ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0, 1, 1]⟩⟩
def basisLaw2 : Identity Nat := ⟨⟨0, [0, 1]⟩, ⟨0, [1, 1, 0, 1]⟩⟩
def basisLaw3 : Identity Nat := ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩
def basisLaw4 : Identity Nat := ⟨⟨0, [0, 1, 0, 0]⟩, ⟨0, [1, 0]⟩⟩
def basisLaw5 : Identity Nat := ⟨⟨0, [0, 1, 0, 1]⟩, ⟨0, [1, 1]⟩⟩
def basisLaw6 : Identity Nat := ⟨⟨0, [0, 1, 0, 2]⟩, ⟨0, [1, 2]⟩⟩
def basisLaw7 : Identity Nat := ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 0, 1]⟩⟩
def basisLaw8 : Identity Nat := ⟨⟨0, [0, 1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩
def basisLaw9 : Identity Nat := ⟨⟨0, [1, 0, 0, 1]⟩, ⟨0, [1, 1]⟩⟩
def basisLaw10 : Identity Nat := ⟨⟨0, [1, 0, 0, 2]⟩, ⟨0, [1, 2]⟩⟩

def basis : List (Identity Nat) :=
  [basisLaw0, basisLaw1, basisLaw2, basisLaw3, basisLaw4, basisLaw5, basisLaw6, basisLaw7, basisLaw8, basisLaw9, basisLaw10]

def leftBasisLaw0 : Identity Nat := ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def leftBasisLaw1 : Identity Nat := ⟨⟨0, [1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

def leftBasis : List (Identity Nat) :=
  [leftBasisLaw0, leftBasisLaw1]

theorem leftDerivesLaw0 :
    Derives leftBasis basisLaw0.lhs basisLaw0.rhs := by
  have step0 : Derives leftBasis ⟨0, []⟩ ⟨0, [0]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives leftBasis ⟨0, [0]⟩ ⟨0, [0, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw1 :
    Derives leftBasis basisLaw1.lhs basisLaw1.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1]⟩ ⟨0, [0, 1, 0, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  have step1 : Derives leftBasis ⟨0, [0, 1, 0, 1]⟩ ⟨0, [0, 1, 0, 1, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [0, 1, 0]⟩ instantiated)
  have step2 : Derives leftBasis ⟨0, [0, 1, 0, 1, 1]⟩ ⟨0, [1, 0, 1, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [0, 1, 1]⟩)
  exact Derives.trans step0 (Derives.trans step1 (step2))

theorem leftDerivesLaw2 :
    Derives leftBasis basisLaw2.lhs basisLaw2.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1]⟩ ⟨0, [0, 1, 0, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  have step1 : Derives leftBasis ⟨0, [0, 1, 0, 1]⟩ ⟨0, [0, 1, 1, 0, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, [0]⟩ instantiated) ⟨0, [1]⟩)
  have step2 : Derives leftBasis ⟨0, [0, 1, 1, 0, 1]⟩ ⟨0, [1, 1, 0, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [1, 0, 1]⟩)
  exact Derives.trans step0 (Derives.trans step1 (step2))

theorem leftDerivesLaw3 :
    Derives leftBasis basisLaw3.lhs basisLaw3.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 0]⟩ ⟨0, [0, 1, 0, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [0, 1]⟩ instantiated)
  have step1 : Derives leftBasis ⟨0, [0, 1, 0, 0]⟩ ⟨0, [1, 0, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [0, 0]⟩)
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw4 :
    Derives leftBasis basisLaw4.lhs basisLaw4.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 0, 0]⟩ ⟨0, [1, 0, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [0, 0]⟩)
  have step1 : Derives leftBasis ⟨0, [1, 0, 0]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [1]⟩ instantiated)
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw5 :
    Derives leftBasis basisLaw5.lhs basisLaw5.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 0, 1]⟩ ⟨0, [1, 0, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [0, 1]⟩)
  have step1 : Derives leftBasis ⟨0, [1, 0, 1]⟩ ⟨0, [1, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw6 :
    Derives leftBasis basisLaw6.lhs basisLaw6.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 0, 2]⟩ ⟨0, [1, 0, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [0, 2]⟩)
  have step1 : Derives leftBasis ⟨0, [1, 0, 2]⟩ ⟨0, [1, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw7 :
    Derives leftBasis basisLaw7.lhs basisLaw7.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 1]⟩ ⟨0, [1, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [1]⟩)
  have step1 : Derives leftBasis ⟨0, [1, 1]⟩ ⟨0, [1, 0, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw8 :
    Derives leftBasis basisLaw8.lhs basisLaw8.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 2]⟩ ⟨0, [1, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [2]⟩)
  have step1 : Derives leftBasis ⟨0, [1, 2]⟩ ⟨0, [1, 0, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw9 :
    Derives leftBasis basisLaw9.lhs basisLaw9.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 0, 0, 1]⟩ ⟨0, [1, 0, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, [1]⟩ instantiated) ⟨1, []⟩)
  have step1 : Derives leftBasis ⟨0, [1, 0, 1]⟩ ⟨0, [1, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw10 :
    Derives leftBasis basisLaw10.lhs basisLaw10.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 0, 0, 2]⟩ ⟨0, [1, 0, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, [1]⟩ instantiated) ⟨2, []⟩)
  have step1 : Derives leftBasis ⟨0, [1, 0, 2]⟩ ⟨0, [1, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

/-- 11 fixed displayed-law instances. -/
theorem displayedInLeftBasis : FiniteCertificate.DerivesAll leftBasis basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact leftDerivesLaw0
  · exact leftDerivesLaw1
  · exact leftDerivesLaw2
  · exact leftDerivesLaw3
  · exact leftDerivesLaw4
  · exact leftDerivesLaw5
  · exact leftDerivesLaw6
  · exact leftDerivesLaw7
  · exact leftDerivesLaw8
  · exact leftDerivesLaw9
  · exact leftDerivesLaw10

def rightBasisLaw0 : Identity Nat := ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩
def rightBasisLaw1 : Identity Nat := ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def rightBasis : List (Identity Nat) :=
  [rightBasisLaw0, rightBasisLaw1]

theorem rightDerivesLaw0 :
    Derives rightBasis basisLaw0.lhs basisLaw0.rhs := by
  have step0 : Derives rightBasis ⟨0, []⟩ ⟨0, [0, 0]⟩ := by
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
  have step0 : Derives rightBasis ⟨0, [0, 1]⟩ ⟨0, [0, 1, 1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [0]⟩ instantiated)
  have step1 : Derives rightBasis ⟨0, [0, 1, 1, 1]⟩ ⟨0, [1, 0, 1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [1]⟩)
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw2 :
    Derives rightBasis basisLaw2.lhs basisLaw2.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1]⟩ ⟨0, [0, 1, 1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [0]⟩ instantiated)
  have step1 : Derives rightBasis ⟨0, [0, 1, 1, 1]⟩ ⟨0, [1, 1, 0, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1, 1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw3 :
    Derives rightBasis basisLaw3.lhs basisLaw3.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 0]⟩ ⟨0, [1, 0, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  exact step0

theorem rightDerivesLaw4 :
    Derives rightBasis basisLaw4.lhs basisLaw4.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 0, 0]⟩ ⟨0, [1, 0, 0, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, [0]⟩)
  have step1 : Derives rightBasis ⟨0, [1, 0, 0, 0]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [1]⟩ instantiated)
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw5 :
    Derives rightBasis basisLaw5.lhs basisLaw5.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 0, 1]⟩ ⟨0, [0, 0, 1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [0, 1]⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  have step1 : Derives rightBasis ⟨0, [0, 0, 1, 1]⟩ ⟨0, [1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [1]⟩)
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw6 :
    Derives rightBasis basisLaw6.lhs basisLaw6.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 0, 2]⟩ ⟨0, [0, 0, 1, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [0, 1]⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, []⟩)
  have step1 : Derives rightBasis ⟨0, [0, 0, 1, 2]⟩ ⟨0, [1, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [2]⟩)
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw7 :
    Derives rightBasis basisLaw7.lhs basisLaw7.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 1]⟩ ⟨0, [1, 0, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  exact step0

theorem rightDerivesLaw8 :
    Derives rightBasis basisLaw8.lhs basisLaw8.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 2]⟩ ⟨0, [1, 0, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, []⟩)
  exact step0

theorem rightDerivesLaw9 :
    Derives rightBasis basisLaw9.lhs basisLaw9.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 0, 0, 1]⟩ ⟨0, [0, 0, 1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [1]⟩
      | 1 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  have step1 : Derives rightBasis ⟨0, [0, 0, 1, 1]⟩ ⟨0, [1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [1]⟩)
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw10 :
    Derives rightBasis basisLaw10.lhs basisLaw10.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 0, 0, 2]⟩ ⟨0, [0, 0, 1, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [1]⟩
      | 1 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, []⟩)
  have step1 : Derives rightBasis ⟨0, [0, 0, 1, 2]⟩ ⟨0, [1, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [2]⟩)
  exact Derives.trans step0 (step1)

/-- 11 fixed displayed-law instances. -/
theorem displayedInRightBasis : FiniteCertificate.DerivesAll rightBasis basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rightDerivesLaw0
  · exact rightDerivesLaw1
  · exact rightDerivesLaw2
  · exact rightDerivesLaw3
  · exact rightDerivesLaw4
  · exact rightDerivesLaw5
  · exact rightDerivesLaw6
  · exact rightDerivesLaw7
  · exact rightDerivesLaw8
  · exact rightDerivesLaw9
  · exact rightDerivesLaw10

private theorem leftModelsLaw0 : basisLaw0.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup := by
  have roundTrip : (basisLaw0.map toFinThree).map Fin.val = basisLaw0 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S4_120.table (basisLaw0.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw1 : basisLaw1.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup := by
  have roundTrip : (basisLaw1.map toFinThree).map Fin.val = basisLaw1 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S4_120.table (basisLaw1.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw2 : basisLaw2.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup := by
  have roundTrip : (basisLaw2.map toFinThree).map Fin.val = basisLaw2 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S4_120.table (basisLaw2.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw3 : basisLaw3.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup := by
  have roundTrip : (basisLaw3.map toFinThree).map Fin.val = basisLaw3 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S4_120.table (basisLaw3.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw4 : basisLaw4.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup := by
  have roundTrip : (basisLaw4.map toFinThree).map Fin.val = basisLaw4 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S4_120.table (basisLaw4.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw5 : basisLaw5.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup := by
  have roundTrip : (basisLaw5.map toFinThree).map Fin.val = basisLaw5 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S4_120.table (basisLaw5.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw6 : basisLaw6.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup := by
  have roundTrip : (basisLaw6.map toFinThree).map Fin.val = basisLaw6 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S4_120.table (basisLaw6.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw7 : basisLaw7.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup := by
  have roundTrip : (basisLaw7.map toFinThree).map Fin.val = basisLaw7 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S4_120.table (basisLaw7.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw8 : basisLaw8.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup := by
  have roundTrip : (basisLaw8.map toFinThree).map Fin.val = basisLaw8 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S4_120.table (basisLaw8.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw9 : basisLaw9.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup := by
  have roundTrip : (basisLaw9.map toFinThree).map Fin.val = basisLaw9 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S4_120.table (basisLaw9.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw10 : basisLaw10.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup := by
  have roundTrip : (basisLaw10.map toFinThree).map Fin.val = basisLaw10 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S4_120.table (basisLaw10.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem leftModels : Models SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact leftModelsLaw0
  · exact leftModelsLaw1
  · exact leftModelsLaw2
  · exact leftModelsLaw3
  · exact leftModelsLaw4
  · exact leftModelsLaw5
  · exact leftModelsLaw6
  · exact leftModelsLaw7
  · exact leftModelsLaw8
  · exact leftModelsLaw9
  · exact leftModelsLaw10

private theorem rightModelsLaw0 : basisLaw0.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_91.table.semigroup := by
  have roundTrip : (basisLaw0.map toFinThree).map Fin.val = basisLaw0 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S4_91.table (basisLaw0.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw1 : basisLaw1.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_91.table.semigroup := by
  have roundTrip : (basisLaw1.map toFinThree).map Fin.val = basisLaw1 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S4_91.table (basisLaw1.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw2 : basisLaw2.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_91.table.semigroup := by
  have roundTrip : (basisLaw2.map toFinThree).map Fin.val = basisLaw2 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S4_91.table (basisLaw2.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw3 : basisLaw3.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_91.table.semigroup := by
  have roundTrip : (basisLaw3.map toFinThree).map Fin.val = basisLaw3 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S4_91.table (basisLaw3.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw4 : basisLaw4.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_91.table.semigroup := by
  have roundTrip : (basisLaw4.map toFinThree).map Fin.val = basisLaw4 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S4_91.table (basisLaw4.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw5 : basisLaw5.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_91.table.semigroup := by
  have roundTrip : (basisLaw5.map toFinThree).map Fin.val = basisLaw5 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S4_91.table (basisLaw5.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw6 : basisLaw6.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_91.table.semigroup := by
  have roundTrip : (basisLaw6.map toFinThree).map Fin.val = basisLaw6 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S4_91.table (basisLaw6.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw7 : basisLaw7.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_91.table.semigroup := by
  have roundTrip : (basisLaw7.map toFinThree).map Fin.val = basisLaw7 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S4_91.table (basisLaw7.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw8 : basisLaw8.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_91.table.semigroup := by
  have roundTrip : (basisLaw8.map toFinThree).map Fin.val = basisLaw8 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S4_91.table (basisLaw8.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw9 : basisLaw9.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_91.table.semigroup := by
  have roundTrip : (basisLaw9.map toFinThree).map Fin.val = basisLaw9 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S4_91.table (basisLaw9.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw10 : basisLaw10.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_91.table.semigroup := by
  have roundTrip : (basisLaw10.map toFinThree).map Fin.val = basisLaw10 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S4_91.table (basisLaw10.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem rightModels : Models SemigroupBasis.Generated.Catalogue.S4_91.table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rightModelsLaw0
  · exact rightModelsLaw1
  · exact rightModelsLaw2
  · exact rightModelsLaw3
  · exact rightModelsLaw4
  · exact rightModelsLaw5
  · exact rightModelsLaw6
  · exact rightModelsLaw7
  · exact rightModelsLaw8
  · exact rightModelsLaw9
  · exact rightModelsLaw10

namespace S6_14680

/-- Exact catalogue table SHA256 `63ac2132270a6e68a6c25a2db63522dc253aeddd9cc9a94bda72f0b384be32ca`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6)) else if a = 1 then (if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6)) else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if a = 3 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if a = 4 then (if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6)) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def ontoLeftMap (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else if a = 4 then (0 : Fin 4) else (3 : Fin 4)

def ontoLeftSection (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (3 : Fin 6) else (5 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (2 : Fin 4) else if a = 3 then (2 : Fin 4) else if a = 4 then (3 : Fin 4) else (3 : Fin 4)

def ontoRightSection (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (4 : Fin 6)

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S4_91.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup SemigroupBasis.Generated.Catalogue.S4_91.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro a b
    exact by decide +revert

theorem models : Models table.semigroup basis := by
  intro identity member
  exact (pair.satisfiedBy_iff identity).mpr ⟨leftModels identity member, rightModels identity member⟩

def ontoLeftOpposite : SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup.opposite where
  toFun := ontoLeftMap
  map_mul := fun a b => ontoLeft.map_mul b a
  preimage := ontoLeftSection
  right_inverse := ontoLeft.right_inverse

def ontoRightOpposite : SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S4_91.table.semigroup.opposite where
  toFun := ontoRightMap
  map_mul := fun a b => ontoRight.map_mul b a
  preimage := ontoRightSection
  right_inverse := ontoRight.right_inverse

def pairOpposite : SubdirectPair table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S4_91.table.semigroup.opposite where
  left := ontoLeftOpposite
  right := ontoRightOpposite
  jointlyInjective := pair.jointlyInjective

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) :=
  models.oppositeReversed

end S6_14680

namespace S6_14762

/-- Exact catalogue table SHA256 `dc13c1b513d891f8a3afed4308fdcfbf5a850136a207d11bcc316482b1fbdcba`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)) else if a = 1 then (if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)) else if a = 2 then (if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)) else if a = 3 then (if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if a = 4 then (if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

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

private theorem modelsLaw3 : basisLaw3.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw3.map toFinThree).map Fin.val = basisLaw3 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw3.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem modelsLaw4 : basisLaw4.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw4.map toFinThree).map Fin.val = basisLaw4 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw4.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem modelsLaw5 : basisLaw5.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw5.map toFinThree).map Fin.val = basisLaw5 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw5.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem modelsLaw6 : basisLaw6.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw6.map toFinThree).map Fin.val = basisLaw6 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw6.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem modelsLaw7 : basisLaw7.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw7.map toFinThree).map Fin.val = basisLaw7 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw7.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem modelsLaw8 : basisLaw8.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw8.map toFinThree).map Fin.val = basisLaw8 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw8.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem modelsLaw9 : basisLaw9.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw9.map toFinThree).map Fin.val = basisLaw9 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw9.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem modelsLaw10 : basisLaw10.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw10.map toFinThree).map Fin.val = basisLaw10 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw10.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact modelsLaw0
  · exact modelsLaw1
  · exact modelsLaw2
  · exact modelsLaw3
  · exact modelsLaw4
  · exact modelsLaw5
  · exact modelsLaw6
  · exact modelsLaw7
  · exact modelsLaw8
  · exact modelsLaw9
  · exact modelsLaw10

def rootHom0Map (a : Fin 6) : Fin 6 :=
  if a = 0 then (2 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (4 : Fin 6) else if a = 4 then (2 : Fin 6) else (5 : Fin 6)

def rootHom0 : Hom S6_14680.table.semigroup table.semigroup where
  toFun := rootHom0Map
  map_mul := by decide

def rootHom0Opposite : Hom S6_14680.table.semigroup.opposite table.semigroup.opposite where
  toFun := rootHom0.toFun
  map_mul := fun a b => rootHom0.map_mul b a

def rootHom1Map (a : Fin 6) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (2 : Fin 6) else (2 : Fin 6)

def rootHom1 : Hom S6_14680.table.semigroup table.semigroup where
  toFun := rootHom1Map
  map_mul := by decide

def rootHom1Opposite : Hom S6_14680.table.semigroup.opposite table.semigroup.opposite where
  toFun := rootHom1.toFun
  map_mul := fun a b => rootHom1.map_mul b a

def rootHomFamily (i : Fin 2) : Hom S6_14680.table.semigroup table.semigroup :=
  if i = 0 then rootHom0 else rootHom1

/-- Finite 2-coordinate root-to-leaf embedding. -/
def rootIntoPower : Embedding S6_14680.table.semigroup (table.semigroup.pi (Fin 2)) :=
  Embedding.ofSeparatingHoms rootHomFamily (by decide)

def rootHomFamilyOpposite (i : Fin 2) : Hom S6_14680.table.semigroup.opposite table.semigroup.opposite :=
  if i = 0 then rootHom0Opposite else rootHom1Opposite

/-- Finite 2-coordinate root-to-leaf embedding. -/
def rootOppositeIntoPower : Embedding S6_14680.table.semigroup.opposite (table.semigroup.opposite.pi (Fin 2)) :=
  Embedding.ofSeparatingHoms rootHomFamilyOpposite (by decide)

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) :=
  models.oppositeReversed

end S6_14762

namespace S6_14780

/-- Exact catalogue table SHA256 `6fb6a23ec382beb5db116e6663c2037be489fd43f1bfe1dceb499f0c51f0669c`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6)) else if a = 1 then (if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6)) else if a = 2 then (if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)) else if a = 3 then (if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (2 : Fin 6)) else if a = 4 then (if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (2 : Fin 6)) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

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

private theorem modelsLaw3 : basisLaw3.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw3.map toFinThree).map Fin.val = basisLaw3 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw3.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem modelsLaw4 : basisLaw4.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw4.map toFinThree).map Fin.val = basisLaw4 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw4.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem modelsLaw5 : basisLaw5.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw5.map toFinThree).map Fin.val = basisLaw5 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw5.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem modelsLaw6 : basisLaw6.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw6.map toFinThree).map Fin.val = basisLaw6 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw6.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem modelsLaw7 : basisLaw7.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw7.map toFinThree).map Fin.val = basisLaw7 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw7.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem modelsLaw8 : basisLaw8.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw8.map toFinThree).map Fin.val = basisLaw8 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw8.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem modelsLaw9 : basisLaw9.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw9.map toFinThree).map Fin.val = basisLaw9 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw9.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem modelsLaw10 : basisLaw10.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw10.map toFinThree).map Fin.val = basisLaw10 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw10.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact modelsLaw0
  · exact modelsLaw1
  · exact modelsLaw2
  · exact modelsLaw3
  · exact modelsLaw4
  · exact modelsLaw5
  · exact modelsLaw6
  · exact modelsLaw7
  · exact modelsLaw8
  · exact modelsLaw9
  · exact modelsLaw10

def rootHom0Map (a : Fin 6) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (2 : Fin 6) else (2 : Fin 6)

def rootHom0 : Hom S6_14680.table.semigroup table.semigroup where
  toFun := rootHom0Map
  map_mul := by decide

def rootHom0Opposite : Hom S6_14680.table.semigroup.opposite table.semigroup.opposite where
  toFun := rootHom0.toFun
  map_mul := fun a b => rootHom0.map_mul b a

def rootHom1Map (a : Fin 6) : Fin 6 :=
  if a = 0 then (2 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (2 : Fin 6) else (5 : Fin 6)

def rootHom1 : Hom S6_14680.table.semigroup table.semigroup where
  toFun := rootHom1Map
  map_mul := by decide

def rootHom1Opposite : Hom S6_14680.table.semigroup.opposite table.semigroup.opposite where
  toFun := rootHom1.toFun
  map_mul := fun a b => rootHom1.map_mul b a

def rootHom2Map (a : Fin 6) : Fin 6 :=
  if a = 0 then (2 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (4 : Fin 6) else if a = 4 then (2 : Fin 6) else (2 : Fin 6)

def rootHom2 : Hom S6_14680.table.semigroup table.semigroup where
  toFun := rootHom2Map
  map_mul := by decide

def rootHom2Opposite : Hom S6_14680.table.semigroup.opposite table.semigroup.opposite where
  toFun := rootHom2.toFun
  map_mul := fun a b => rootHom2.map_mul b a

def rootHomFamily (i : Fin 3) : Hom S6_14680.table.semigroup table.semigroup :=
  if i = 0 then rootHom0 else if i = 1 then rootHom1 else rootHom2

/-- Finite 3-coordinate root-to-leaf embedding. -/
def rootIntoPower : Embedding S6_14680.table.semigroup (table.semigroup.pi (Fin 3)) :=
  Embedding.ofSeparatingHoms rootHomFamily (by decide)

def rootHomFamilyOpposite (i : Fin 3) : Hom S6_14680.table.semigroup.opposite table.semigroup.opposite :=
  if i = 0 then rootHom0Opposite else if i = 1 then rootHom1Opposite else rootHom2Opposite

/-- Finite 3-coordinate root-to-leaf embedding. -/
def rootOppositeIntoPower : Embedding S6_14680.table.semigroup.opposite (table.semigroup.opposite.pi (Fin 3)) :=
  Embedding.ofSeparatingHoms rootHomFamilyOpposite (by decide)

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) :=
  models.oppositeReversed

end S6_14780

end Sigma086fc

namespace Sigma968ea

def basisLaw0 : Identity Nat := ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def basisLaw1 : Identity Nat := ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0]⟩⟩
def basisLaw2 : Identity Nat := ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 0]⟩⟩
def basisLaw3 : Identity Nat := ⟨⟨0, [0, 1, 2, 1]⟩, ⟨0, [1, 2, 0]⟩⟩
def basisLaw4 : Identity Nat := ⟨⟨0, [0, 1, 2, 2]⟩, ⟨0, [1, 2, 0]⟩⟩
def basisLaw5 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩
def basisLaw6 : Identity Nat := ⟨⟨0, [1, 0, 2]⟩, ⟨0, [1, 1, 0, 2]⟩⟩
def basisLaw7 : Identity Nat := ⟨⟨0, [1, 0, 2, 2]⟩, ⟨0, [1, 2, 0]⟩⟩
def basisLaw8 : Identity Nat := ⟨⟨0, [1, 1, 2, 0]⟩, ⟨0, [1, 2, 0]⟩⟩
def basisLaw9 : Identity Nat := ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩
def basisLaw10 : Identity Nat := ⟨⟨0, [1, 2, 1]⟩, ⟨0, [1, 2, 2]⟩⟩

def basis : List (Identity Nat) :=
  [basisLaw0, basisLaw1, basisLaw2, basisLaw3, basisLaw4, basisLaw5, basisLaw6, basisLaw7, basisLaw8, basisLaw9, basisLaw10]

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
  have step0 : Derives leftBasis ⟨0, [0, 1, 0]⟩ ⟨0, [1, 0, 1, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw2.lhs leftBasisLaw2.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives leftBasis ⟨0, [1, 0, 1, 0]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, [0]⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

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
  have step1 : Derives leftBasis ⟨0, [0, 1]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw3.lhs leftBasisLaw3.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw3, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw3 :
    Derives leftBasis basisLaw3.lhs basisLaw3.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 2, 1]⟩ ⟨0, [0, 1, 1, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw3.lhs leftBasisLaw3.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw3, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [0]⟩ instantiated)
  have step1 : Derives leftBasis ⟨0, [0, 1, 1, 2]⟩ ⟨0, [0, 1, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, []⟩)
  have step2 : Derives leftBasis ⟨0, [0, 1, 2]⟩ ⟨0, [1, 2, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw3.lhs leftBasisLaw3.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, [2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw3, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (step2))

theorem leftDerivesLaw4 :
    Derives leftBasis basisLaw4.lhs basisLaw4.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 2, 2]⟩ ⟨0, [0, 1, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | 1 => ⟨0, [0, 1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives leftBasis ⟨0, [0, 1, 2]⟩ ⟨0, [1, 2, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw3.lhs leftBasisLaw3.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, [2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw3, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw5 :
    Derives leftBasis basisLaw5.lhs basisLaw5.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 0]⟩ ⟨1, [1, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw2.lhs leftBasisLaw2.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives leftBasis ⟨1, [1, 0]⟩ ⟨1, [0, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw3.lhs leftBasisLaw3.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw3, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw6 :
    Derives leftBasis basisLaw6.lhs basisLaw6.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 0, 2]⟩ ⟨0, [1, 1, 0, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, [2]⟩)
  exact step0

theorem leftDerivesLaw7 :
    Derives leftBasis basisLaw7.lhs basisLaw7.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 0, 2, 2]⟩ ⟨0, [1, 0, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | 1 => ⟨0, [1, 0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives leftBasis ⟨0, [1, 0, 2]⟩ ⟨0, [0, 1, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw3.lhs leftBasisLaw3.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw3, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, []⟩)
  have step2 : Derives leftBasis ⟨0, [0, 1, 2]⟩ ⟨0, [1, 2, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw3.lhs leftBasisLaw3.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, [2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw3, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (step2))

theorem leftDerivesLaw8 :
    Derives leftBasis basisLaw8.lhs basisLaw8.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 1, 2, 0]⟩ ⟨0, [1, 2, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, [0]⟩)
  exact step0

theorem leftDerivesLaw9 :
    Derives leftBasis basisLaw9.lhs basisLaw9.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 2, 0]⟩ ⟨0, [1, 1, 2, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, [0]⟩)
  have step1 : Derives leftBasis ⟨0, [1, 1, 2, 0]⟩ ⟨0, [2, 1, 2, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw2.lhs leftBasisLaw2.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw2, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, []⟩ instantiated) ⟨0, []⟩)
  have step2 : Derives leftBasis ⟨0, [2, 1, 2, 0]⟩ ⟨0, [2, 2, 1, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw3.lhs leftBasisLaw3.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw3, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, []⟩ instantiated) ⟨0, []⟩)
  have step3 : Derives leftBasis ⟨0, [2, 2, 1, 0]⟩ ⟨0, [2, 1, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [0]⟩)
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (step3)))

theorem leftDerivesLaw10 :
    Derives leftBasis basisLaw10.lhs basisLaw10.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 2, 1]⟩ ⟨0, [1, 2, 2, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  have step1 : Derives leftBasis ⟨0, [1, 2, 2, 1]⟩ ⟨0, [1, 1, 2, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw3.lhs leftBasisLaw3.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨2, [2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw3, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  have step2 : Derives leftBasis ⟨0, [1, 1, 2, 2]⟩ ⟨0, [1, 2, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, [2]⟩)
  exact Derives.trans step0 (Derives.trans step1 (step2))

/-- 11 fixed displayed-law instances. -/
theorem displayedInLeftBasis : FiniteCertificate.DerivesAll leftBasis basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact leftDerivesLaw0
  · exact leftDerivesLaw1
  · exact leftDerivesLaw2
  · exact leftDerivesLaw3
  · exact leftDerivesLaw4
  · exact leftDerivesLaw5
  · exact leftDerivesLaw6
  · exact leftDerivesLaw7
  · exact leftDerivesLaw8
  · exact leftDerivesLaw9
  · exact leftDerivesLaw10

def rightBasisLaw0 : Identity Nat := ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def rightBasisLaw1 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩
def rightBasisLaw2 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩
def rightBasisLaw3 : Identity Nat := ⟨⟨0, [1, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def rightBasis : List (Identity Nat) :=
  [rightBasisLaw0, rightBasisLaw1, rightBasisLaw2, rightBasisLaw3]

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
  have step0 : Derives rightBasis ⟨0, [0, 1, 0]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw3.lhs rightBasisLaw3.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw3, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem rightDerivesLaw2 :
    Derives rightBasis basisLaw2.lhs basisLaw2.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 1]⟩ ⟨0, [0, 1, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  have step1 : Derives rightBasis ⟨0, [0, 1, 0]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw3.lhs rightBasisLaw3.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw3, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw3 :
    Derives rightBasis basisLaw3.lhs basisLaw3.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 2, 1]⟩ ⟨0, [0, 1, 2, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [0]⟩ instantiated)
  have step1 : Derives rightBasis ⟨0, [0, 1, 2, 2]⟩ ⟨0, [0, 1, 2, 2, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [0, 1]⟩ instantiated)
  have step2 : Derives rightBasis ⟨0, [0, 1, 2, 2, 2]⟩ ⟨0, [0, 1, 2, 1, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, [0]⟩ instantiated) ⟨2, []⟩)
  have step3 : Derives rightBasis ⟨0, [0, 1, 2, 1, 2]⟩ ⟨0, [0, 1, 2, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, [2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  have step4 : Derives rightBasis ⟨0, [0, 1, 2, 0]⟩ ⟨0, [1, 2, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw3.lhs rightBasisLaw3.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw3, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (Derives.trans step3 (step4))))

theorem rightDerivesLaw4 :
    Derives rightBasis basisLaw4.lhs basisLaw4.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 2, 2]⟩ ⟨0, [0, 1, 2, 2, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [0, 1]⟩ instantiated)
  have step1 : Derives rightBasis ⟨0, [0, 1, 2, 2, 2]⟩ ⟨0, [0, 1, 2, 1, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, [0]⟩ instantiated) ⟨2, []⟩)
  have step2 : Derives rightBasis ⟨0, [0, 1, 2, 1, 2]⟩ ⟨0, [0, 1, 2, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, [2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  have step3 : Derives rightBasis ⟨0, [0, 1, 2, 0]⟩ ⟨0, [1, 2, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw3.lhs rightBasisLaw3.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw3, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (step3)))

theorem rightDerivesLaw5 :
    Derives rightBasis basisLaw5.lhs basisLaw5.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 0]⟩ ⟨0, [1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives rightBasis ⟨0, [1, 1]⟩ ⟨1, [0, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw2.lhs rightBasisLaw2.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw6 :
    Derives rightBasis basisLaw6.lhs basisLaw6.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 0, 2]⟩ ⟨0, [1, 1, 0, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw3.lhs rightBasisLaw3.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | 2 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw3, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  exact step0

theorem rightDerivesLaw7 :
    Derives rightBasis basisLaw7.lhs basisLaw7.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 0, 2, 2]⟩ ⟨0, [1, 1, 2, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, [2]⟩)
  have step1 : Derives rightBasis ⟨0, [1, 1, 2, 2]⟩ ⟨0, [1, 2, 1, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw2.lhs rightBasisLaw2.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw2, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [1]⟩ instantiated)
  have step2 : Derives rightBasis ⟨0, [1, 2, 1, 2]⟩ ⟨0, [1, 2, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, [2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (step2))

theorem rightDerivesLaw8 :
    Derives rightBasis basisLaw8.lhs basisLaw8.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 1, 2, 0]⟩ ⟨0, [1, 2, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw3.lhs rightBasisLaw3.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨2, []⟩
      | 2 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw3, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  exact step0

theorem rightDerivesLaw9 :
    Derives rightBasis basisLaw9.lhs basisLaw9.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 2, 0]⟩ ⟨0, [1, 2, 1, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, [2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives rightBasis ⟨0, [1, 2, 1, 2]⟩ ⟨0, [1, 2, 2, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, []⟩ instantiated) ⟨2, []⟩)
  have step2 : Derives rightBasis ⟨0, [1, 2, 2, 2]⟩ ⟨0, [2, 1, 2, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw2.lhs rightBasisLaw2.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw2, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, []⟩ instantiated) ⟨2, []⟩)
  have step3 : Derives rightBasis ⟨0, [2, 1, 2, 2]⟩ ⟨0, [2, 1, 2, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [2]⟩ instantiated)
  have step4 : Derives rightBasis ⟨0, [2, 1, 2, 1]⟩ ⟨0, [2, 1, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨2, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (Derives.trans step3 (step4))))

theorem rightDerivesLaw10 :
    Derives rightBasis basisLaw10.lhs basisLaw10.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 2, 1]⟩ ⟨0, [1, 2, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  exact step0

/-- 11 fixed displayed-law instances. -/
theorem displayedInRightBasis : FiniteCertificate.DerivesAll rightBasis basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rightDerivesLaw0
  · exact rightDerivesLaw1
  · exact rightDerivesLaw2
  · exact rightDerivesLaw3
  · exact rightDerivesLaw4
  · exact rightDerivesLaw5
  · exact rightDerivesLaw6
  · exact rightDerivesLaw7
  · exact rightDerivesLaw8
  · exact rightDerivesLaw9
  · exact rightDerivesLaw10

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

private theorem leftModelsLaw4 : basisLaw4.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_6.table.semigroup.opposite := by
  have roundTrip : (basisLaw4.map toFinThree).map Fin.val = basisLaw4 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound leftTable (basisLaw4.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw5 : basisLaw5.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_6.table.semigroup.opposite := by
  have roundTrip : (basisLaw5.map toFinThree).map Fin.val = basisLaw5 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound leftTable (basisLaw5.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw6 : basisLaw6.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_6.table.semigroup.opposite := by
  have roundTrip : (basisLaw6.map toFinThree).map Fin.val = basisLaw6 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound leftTable (basisLaw6.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw7 : basisLaw7.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_6.table.semigroup.opposite := by
  have roundTrip : (basisLaw7.map toFinThree).map Fin.val = basisLaw7 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound leftTable (basisLaw7.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw8 : basisLaw8.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_6.table.semigroup.opposite := by
  have roundTrip : (basisLaw8.map toFinThree).map Fin.val = basisLaw8 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound leftTable (basisLaw8.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw9 : basisLaw9.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_6.table.semigroup.opposite := by
  have roundTrip : (basisLaw9.map toFinThree).map Fin.val = basisLaw9 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound leftTable (basisLaw9.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw10 : basisLaw10.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_6.table.semigroup.opposite := by
  have roundTrip : (basisLaw10.map toFinThree).map Fin.val = basisLaw10 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound leftTable (basisLaw10.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem leftModels : Models SemigroupBasis.Generated.Catalogue.S3_6.table.semigroup.opposite basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact leftModelsLaw0
  · exact leftModelsLaw1
  · exact leftModelsLaw2
  · exact leftModelsLaw3
  · exact leftModelsLaw4
  · exact leftModelsLaw5
  · exact leftModelsLaw6
  · exact leftModelsLaw7
  · exact leftModelsLaw8
  · exact leftModelsLaw9
  · exact leftModelsLaw10

private theorem rightModelsLaw0 : basisLaw0.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup := by
  have roundTrip : (basisLaw0.map toFinThree).map Fin.val = basisLaw0 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_83.table (basisLaw0.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw1 : basisLaw1.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup := by
  have roundTrip : (basisLaw1.map toFinThree).map Fin.val = basisLaw1 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_83.table (basisLaw1.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw2 : basisLaw2.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup := by
  have roundTrip : (basisLaw2.map toFinThree).map Fin.val = basisLaw2 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_83.table (basisLaw2.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw3 : basisLaw3.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup := by
  have roundTrip : (basisLaw3.map toFinThree).map Fin.val = basisLaw3 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_83.table (basisLaw3.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw4 : basisLaw4.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup := by
  have roundTrip : (basisLaw4.map toFinThree).map Fin.val = basisLaw4 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_83.table (basisLaw4.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw5 : basisLaw5.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup := by
  have roundTrip : (basisLaw5.map toFinThree).map Fin.val = basisLaw5 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_83.table (basisLaw5.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw6 : basisLaw6.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup := by
  have roundTrip : (basisLaw6.map toFinThree).map Fin.val = basisLaw6 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_83.table (basisLaw6.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw7 : basisLaw7.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup := by
  have roundTrip : (basisLaw7.map toFinThree).map Fin.val = basisLaw7 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_83.table (basisLaw7.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw8 : basisLaw8.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup := by
  have roundTrip : (basisLaw8.map toFinThree).map Fin.val = basisLaw8 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_83.table (basisLaw8.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw9 : basisLaw9.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup := by
  have roundTrip : (basisLaw9.map toFinThree).map Fin.val = basisLaw9 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_83.table (basisLaw9.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw10 : basisLaw10.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup := by
  have roundTrip : (basisLaw10.map toFinThree).map Fin.val = basisLaw10 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_83.table (basisLaw10.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem rightModels : Models SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rightModelsLaw0
  · exact rightModelsLaw1
  · exact rightModelsLaw2
  · exact rightModelsLaw3
  · exact rightModelsLaw4
  · exact rightModelsLaw5
  · exact rightModelsLaw6
  · exact rightModelsLaw7
  · exact rightModelsLaw8
  · exact rightModelsLaw9
  · exact rightModelsLaw10

namespace S6_1040

/-- Exact catalogue table SHA256 `f9497735435e3a26b5c1ebdf792aa876218bc9f0bdcb45ff97e654a97b8f4119`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 3 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6)) else if a = 4 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

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
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (0 : Fin 5) else if a = 4 then (3 : Fin 5) else (4 : Fin 5)

def ontoRightSection (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.Catalogue.S3_6.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup where
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

def ontoRightOpposite : SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup.opposite where
  toFun := ontoRightMap
  map_mul := fun a b => ontoRight.map_mul b a
  preimage := ontoRightSection
  right_inverse := ontoRight.right_inverse

def pairOpposite : SubdirectPair table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S3_6.table.semigroup.opposite.opposite SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup.opposite where
  left := ontoLeftOpposite
  right := ontoRightOpposite
  jointlyInjective := pair.jointlyInjective

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) :=
  models.oppositeReversed

end S6_1040

namespace S6_1098

/-- Exact catalogue table SHA256 `5e03063e325473f4e36e70d76877d9766037394540c9bbdfbab24418c466ae46`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6)) else if a = 3 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6)) else if a = 4 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def ontoLeftMap (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (1 : Fin 3) else if a = 3 then (1 : Fin 3) else if a = 4 then (0 : Fin 3) else (2 : Fin 3)

def ontoLeftSection (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else (5 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S3_6.table.semigroup.opposite where
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

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.Catalogue.S3_6.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup where
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

def ontoRightOpposite : SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup.opposite where
  toFun := ontoRightMap
  map_mul := fun a b => ontoRight.map_mul b a
  preimage := ontoRightSection
  right_inverse := ontoRight.right_inverse

def pairOpposite : SubdirectPair table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S3_6.table.semigroup.opposite.opposite SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup.opposite where
  left := ontoLeftOpposite
  right := ontoRightOpposite
  jointlyInjective := pair.jointlyInjective

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) :=
  models.oppositeReversed

end S6_1098

end Sigma968ea

namespace Sigma968eb

def basisLaw0 : Identity Nat := ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def basisLaw1 : Identity Nat := ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0]⟩⟩
def basisLaw2 : Identity Nat := ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 0]⟩⟩
def basisLaw3 : Identity Nat := ⟨⟨0, [0, 1, 2, 1]⟩, ⟨0, [1, 2, 0]⟩⟩
def basisLaw4 : Identity Nat := ⟨⟨0, [0, 1, 2, 2]⟩, ⟨0, [1, 2, 0]⟩⟩
def basisLaw5 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩
def basisLaw6 : Identity Nat := ⟨⟨0, [1, 0, 2]⟩, ⟨0, [1, 1, 0, 2]⟩⟩
def basisLaw7 : Identity Nat := ⟨⟨0, [1, 0, 2, 2]⟩, ⟨0, [1, 2, 0]⟩⟩
def basisLaw8 : Identity Nat := ⟨⟨0, [1, 1, 2, 0]⟩, ⟨0, [1, 2, 0]⟩⟩
def basisLaw9 : Identity Nat := ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩
def basisLaw10 : Identity Nat := ⟨⟨0, [1, 2, 1]⟩, ⟨0, [1, 2, 2]⟩⟩

def basis : List (Identity Nat) :=
  [basisLaw0, basisLaw1, basisLaw2, basisLaw3, basisLaw4, basisLaw5, basisLaw6, basisLaw7, basisLaw8, basisLaw9, basisLaw10]

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
  have step0 : Derives leftBasis ⟨0, [0, 1, 0]⟩ ⟨0, [1, 0, 1, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw2.lhs leftBasisLaw2.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives leftBasis ⟨0, [1, 0, 1, 0]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, [0]⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

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
  have step1 : Derives leftBasis ⟨0, [0, 1]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw3.lhs leftBasisLaw3.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw3, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw3 :
    Derives leftBasis basisLaw3.lhs basisLaw3.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 2, 1]⟩ ⟨0, [0, 1, 1, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw3.lhs leftBasisLaw3.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw3, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [0]⟩ instantiated)
  have step1 : Derives leftBasis ⟨0, [0, 1, 1, 2]⟩ ⟨0, [0, 1, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, []⟩)
  have step2 : Derives leftBasis ⟨0, [0, 1, 2]⟩ ⟨0, [1, 2, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw3.lhs leftBasisLaw3.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, [2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw3, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (step2))

theorem leftDerivesLaw4 :
    Derives leftBasis basisLaw4.lhs basisLaw4.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 2, 2]⟩ ⟨0, [0, 1, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | 1 => ⟨0, [0, 1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives leftBasis ⟨0, [0, 1, 2]⟩ ⟨0, [1, 2, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw3.lhs leftBasisLaw3.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, [2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw3, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw5 :
    Derives leftBasis basisLaw5.lhs basisLaw5.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 0]⟩ ⟨1, [1, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw2.lhs leftBasisLaw2.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives leftBasis ⟨1, [1, 0]⟩ ⟨1, [0, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw3.lhs leftBasisLaw3.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw3, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw6 :
    Derives leftBasis basisLaw6.lhs basisLaw6.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 0, 2]⟩ ⟨0, [1, 1, 0, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, [2]⟩)
  exact step0

theorem leftDerivesLaw7 :
    Derives leftBasis basisLaw7.lhs basisLaw7.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 0, 2, 2]⟩ ⟨0, [1, 0, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | 1 => ⟨0, [1, 0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives leftBasis ⟨0, [1, 0, 2]⟩ ⟨0, [0, 1, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw3.lhs leftBasisLaw3.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw3, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, []⟩)
  have step2 : Derives leftBasis ⟨0, [0, 1, 2]⟩ ⟨0, [1, 2, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw3.lhs leftBasisLaw3.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, [2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw3, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (step2))

theorem leftDerivesLaw8 :
    Derives leftBasis basisLaw8.lhs basisLaw8.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 1, 2, 0]⟩ ⟨0, [1, 2, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, [0]⟩)
  exact step0

theorem leftDerivesLaw9 :
    Derives leftBasis basisLaw9.lhs basisLaw9.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 2, 0]⟩ ⟨0, [1, 1, 2, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, [0]⟩)
  have step1 : Derives leftBasis ⟨0, [1, 1, 2, 0]⟩ ⟨0, [2, 1, 2, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw2.lhs leftBasisLaw2.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw2, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, []⟩ instantiated) ⟨0, []⟩)
  have step2 : Derives leftBasis ⟨0, [2, 1, 2, 0]⟩ ⟨0, [2, 2, 1, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw3.lhs leftBasisLaw3.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw3, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, []⟩ instantiated) ⟨0, []⟩)
  have step3 : Derives leftBasis ⟨0, [2, 2, 1, 0]⟩ ⟨0, [2, 1, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [0]⟩)
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (step3)))

theorem leftDerivesLaw10 :
    Derives leftBasis basisLaw10.lhs basisLaw10.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 2, 1]⟩ ⟨0, [1, 2, 2, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  have step1 : Derives leftBasis ⟨0, [1, 2, 2, 1]⟩ ⟨0, [1, 1, 2, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw3.lhs leftBasisLaw3.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨2, [2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw3, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  have step2 : Derives leftBasis ⟨0, [1, 1, 2, 2]⟩ ⟨0, [1, 2, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, [2]⟩)
  exact Derives.trans step0 (Derives.trans step1 (step2))

/-- 11 fixed displayed-law instances. -/
theorem displayedInLeftBasis : FiniteCertificate.DerivesAll leftBasis basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact leftDerivesLaw0
  · exact leftDerivesLaw1
  · exact leftDerivesLaw2
  · exact leftDerivesLaw3
  · exact leftDerivesLaw4
  · exact leftDerivesLaw5
  · exact leftDerivesLaw6
  · exact leftDerivesLaw7
  · exact leftDerivesLaw8
  · exact leftDerivesLaw9
  · exact leftDerivesLaw10

def rightBasisLaw0 : Identity Nat := ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def rightBasisLaw1 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩
def rightBasisLaw2 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩
def rightBasisLaw3 : Identity Nat := ⟨⟨0, [1, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def rightBasis : List (Identity Nat) :=
  [rightBasisLaw0, rightBasisLaw1, rightBasisLaw2, rightBasisLaw3]

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
  have step0 : Derives rightBasis ⟨0, [0, 1, 0]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw3.lhs rightBasisLaw3.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw3, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem rightDerivesLaw2 :
    Derives rightBasis basisLaw2.lhs basisLaw2.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 1]⟩ ⟨0, [0, 1, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  have step1 : Derives rightBasis ⟨0, [0, 1, 0]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw3.lhs rightBasisLaw3.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw3, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw3 :
    Derives rightBasis basisLaw3.lhs basisLaw3.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 2, 1]⟩ ⟨0, [0, 1, 2, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [0]⟩ instantiated)
  have step1 : Derives rightBasis ⟨0, [0, 1, 2, 2]⟩ ⟨0, [0, 1, 2, 2, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [0, 1]⟩ instantiated)
  have step2 : Derives rightBasis ⟨0, [0, 1, 2, 2, 2]⟩ ⟨0, [0, 1, 2, 1, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, [0]⟩ instantiated) ⟨2, []⟩)
  have step3 : Derives rightBasis ⟨0, [0, 1, 2, 1, 2]⟩ ⟨0, [0, 1, 2, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, [2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  have step4 : Derives rightBasis ⟨0, [0, 1, 2, 0]⟩ ⟨0, [1, 2, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw3.lhs rightBasisLaw3.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw3, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (Derives.trans step3 (step4))))

theorem rightDerivesLaw4 :
    Derives rightBasis basisLaw4.lhs basisLaw4.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 2, 2]⟩ ⟨0, [0, 1, 2, 2, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [0, 1]⟩ instantiated)
  have step1 : Derives rightBasis ⟨0, [0, 1, 2, 2, 2]⟩ ⟨0, [0, 1, 2, 1, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, [0]⟩ instantiated) ⟨2, []⟩)
  have step2 : Derives rightBasis ⟨0, [0, 1, 2, 1, 2]⟩ ⟨0, [0, 1, 2, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, [2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  have step3 : Derives rightBasis ⟨0, [0, 1, 2, 0]⟩ ⟨0, [1, 2, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw3.lhs rightBasisLaw3.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw3, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (step3)))

theorem rightDerivesLaw5 :
    Derives rightBasis basisLaw5.lhs basisLaw5.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 0]⟩ ⟨0, [1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives rightBasis ⟨0, [1, 1]⟩ ⟨1, [0, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw2.lhs rightBasisLaw2.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw2, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw6 :
    Derives rightBasis basisLaw6.lhs basisLaw6.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 0, 2]⟩ ⟨0, [1, 1, 0, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw3.lhs rightBasisLaw3.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | 2 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw3, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  exact step0

theorem rightDerivesLaw7 :
    Derives rightBasis basisLaw7.lhs basisLaw7.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 0, 2, 2]⟩ ⟨0, [1, 1, 2, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, [2]⟩)
  have step1 : Derives rightBasis ⟨0, [1, 1, 2, 2]⟩ ⟨0, [1, 2, 1, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw2.lhs rightBasisLaw2.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw2, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [1]⟩ instantiated)
  have step2 : Derives rightBasis ⟨0, [1, 2, 1, 2]⟩ ⟨0, [1, 2, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, [2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (step2))

theorem rightDerivesLaw8 :
    Derives rightBasis basisLaw8.lhs basisLaw8.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 1, 2, 0]⟩ ⟨0, [1, 2, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw3.lhs rightBasisLaw3.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨2, []⟩
      | 2 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw3, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  exact step0

theorem rightDerivesLaw9 :
    Derives rightBasis basisLaw9.lhs basisLaw9.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 2, 0]⟩ ⟨0, [1, 2, 1, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, [2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives rightBasis ⟨0, [1, 2, 1, 2]⟩ ⟨0, [1, 2, 2, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, []⟩ instantiated) ⟨2, []⟩)
  have step2 : Derives rightBasis ⟨0, [1, 2, 2, 2]⟩ ⟨0, [2, 1, 2, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw2.lhs rightBasisLaw2.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw2, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, []⟩ instantiated) ⟨2, []⟩)
  have step3 : Derives rightBasis ⟨0, [2, 1, 2, 2]⟩ ⟨0, [2, 1, 2, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [2]⟩ instantiated)
  have step4 : Derives rightBasis ⟨0, [2, 1, 2, 1]⟩ ⟨0, [2, 1, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨2, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (Derives.trans step1 (Derives.trans step2 (Derives.trans step3 (step4))))

theorem rightDerivesLaw10 :
    Derives rightBasis basisLaw10.lhs basisLaw10.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 2, 1]⟩ ⟨0, [1, 2, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  exact step0

/-- 11 fixed displayed-law instances. -/
theorem displayedInRightBasis : FiniteCertificate.DerivesAll rightBasis basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rightDerivesLaw0
  · exact rightDerivesLaw1
  · exact rightDerivesLaw2
  · exact rightDerivesLaw3
  · exact rightDerivesLaw4
  · exact rightDerivesLaw5
  · exact rightDerivesLaw6
  · exact rightDerivesLaw7
  · exact rightDerivesLaw8
  · exact rightDerivesLaw9
  · exact rightDerivesLaw10

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

private theorem leftModelsLaw4 : basisLaw4.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_6.table.semigroup.opposite := by
  have roundTrip : (basisLaw4.map toFinThree).map Fin.val = basisLaw4 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound leftTable (basisLaw4.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw5 : basisLaw5.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_6.table.semigroup.opposite := by
  have roundTrip : (basisLaw5.map toFinThree).map Fin.val = basisLaw5 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound leftTable (basisLaw5.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw6 : basisLaw6.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_6.table.semigroup.opposite := by
  have roundTrip : (basisLaw6.map toFinThree).map Fin.val = basisLaw6 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound leftTable (basisLaw6.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw7 : basisLaw7.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_6.table.semigroup.opposite := by
  have roundTrip : (basisLaw7.map toFinThree).map Fin.val = basisLaw7 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound leftTable (basisLaw7.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw8 : basisLaw8.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_6.table.semigroup.opposite := by
  have roundTrip : (basisLaw8.map toFinThree).map Fin.val = basisLaw8 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound leftTable (basisLaw8.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw9 : basisLaw9.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_6.table.semigroup.opposite := by
  have roundTrip : (basisLaw9.map toFinThree).map Fin.val = basisLaw9 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound leftTable (basisLaw9.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw10 : basisLaw10.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_6.table.semigroup.opposite := by
  have roundTrip : (basisLaw10.map toFinThree).map Fin.val = basisLaw10 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound leftTable (basisLaw10.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem leftModels : Models SemigroupBasis.Generated.Catalogue.S3_6.table.semigroup.opposite basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact leftModelsLaw0
  · exact leftModelsLaw1
  · exact leftModelsLaw2
  · exact leftModelsLaw3
  · exact leftModelsLaw4
  · exact leftModelsLaw5
  · exact leftModelsLaw6
  · exact leftModelsLaw7
  · exact leftModelsLaw8
  · exact leftModelsLaw9
  · exact leftModelsLaw10

private theorem rightModelsLaw0 : basisLaw0.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup := by
  have roundTrip : (basisLaw0.map toFinThree).map Fin.val = basisLaw0 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_84.table (basisLaw0.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw1 : basisLaw1.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup := by
  have roundTrip : (basisLaw1.map toFinThree).map Fin.val = basisLaw1 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_84.table (basisLaw1.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw2 : basisLaw2.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup := by
  have roundTrip : (basisLaw2.map toFinThree).map Fin.val = basisLaw2 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_84.table (basisLaw2.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw3 : basisLaw3.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup := by
  have roundTrip : (basisLaw3.map toFinThree).map Fin.val = basisLaw3 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_84.table (basisLaw3.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw4 : basisLaw4.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup := by
  have roundTrip : (basisLaw4.map toFinThree).map Fin.val = basisLaw4 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_84.table (basisLaw4.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw5 : basisLaw5.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup := by
  have roundTrip : (basisLaw5.map toFinThree).map Fin.val = basisLaw5 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_84.table (basisLaw5.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw6 : basisLaw6.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup := by
  have roundTrip : (basisLaw6.map toFinThree).map Fin.val = basisLaw6 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_84.table (basisLaw6.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw7 : basisLaw7.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup := by
  have roundTrip : (basisLaw7.map toFinThree).map Fin.val = basisLaw7 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_84.table (basisLaw7.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw8 : basisLaw8.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup := by
  have roundTrip : (basisLaw8.map toFinThree).map Fin.val = basisLaw8 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_84.table (basisLaw8.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw9 : basisLaw9.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup := by
  have roundTrip : (basisLaw9.map toFinThree).map Fin.val = basisLaw9 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_84.table (basisLaw9.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw10 : basisLaw10.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup := by
  have roundTrip : (basisLaw10.map toFinThree).map Fin.val = basisLaw10 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S5_84.table (basisLaw10.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem rightModels : Models SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rightModelsLaw0
  · exact rightModelsLaw1
  · exact rightModelsLaw2
  · exact rightModelsLaw3
  · exact rightModelsLaw4
  · exact rightModelsLaw5
  · exact rightModelsLaw6
  · exact rightModelsLaw7
  · exact rightModelsLaw8
  · exact rightModelsLaw9
  · exact rightModelsLaw10

namespace S6_1042

/-- Exact catalogue table SHA256 `8d74edc3ff3dc36c3a26fb0f0774b11f29a16954b3b51ad9d78e3aefe182f1d2`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 3 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6)) else if a = 4 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

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
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (0 : Fin 5) else if a = 4 then (3 : Fin 5) else (4 : Fin 5)

def ontoRightSection (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.Catalogue.S3_6.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup where
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

def ontoRightOpposite : SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup.opposite where
  toFun := ontoRightMap
  map_mul := fun a b => ontoRight.map_mul b a
  preimage := ontoRightSection
  right_inverse := ontoRight.right_inverse

def pairOpposite : SubdirectPair table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S3_6.table.semigroup.opposite.opposite SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup.opposite where
  left := ontoLeftOpposite
  right := ontoRightOpposite
  jointlyInjective := pair.jointlyInjective

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) :=
  models.oppositeReversed

end S6_1042

namespace S6_1099

/-- Exact catalogue table SHA256 `171db5bca92a593a1004745080c1df1eb84646f7901d4f8f57f490d79264e3f1`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6)) else if a = 3 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6)) else if a = 4 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def ontoLeftMap (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (1 : Fin 3) else if a = 3 then (1 : Fin 3) else if a = 4 then (0 : Fin 3) else (2 : Fin 3)

def ontoLeftSection (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else (5 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S3_6.table.semigroup.opposite where
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

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.Catalogue.S3_6.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup where
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

def ontoRightOpposite : SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup.opposite where
  toFun := ontoRightMap
  map_mul := fun a b => ontoRight.map_mul b a
  preimage := ontoRightSection
  right_inverse := ontoRight.right_inverse

def pairOpposite : SubdirectPair table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S3_6.table.semigroup.opposite.opposite SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup.opposite where
  left := ontoLeftOpposite
  right := ontoRightOpposite
  jointlyInjective := pair.jointlyInjective

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) :=
  models.oppositeReversed

end S6_1099

end Sigma968eb

namespace SigmaF137a

def basisLaw0 : Identity Nat := ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩
def basisLaw1 : Identity Nat := ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0, 1, 1]⟩⟩
def basisLaw2 : Identity Nat := ⟨⟨0, [0, 1]⟩, ⟨0, [1, 1, 0, 1]⟩⟩
def basisLaw3 : Identity Nat := ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩
def basisLaw4 : Identity Nat := ⟨⟨0, [0, 1, 0, 0]⟩, ⟨0, [1, 0]⟩⟩
def basisLaw5 : Identity Nat := ⟨⟨0, [0, 1, 0, 1]⟩, ⟨0, [1, 1]⟩⟩
def basisLaw6 : Identity Nat := ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 0, 1]⟩⟩
def basisLaw7 : Identity Nat := ⟨⟨0, [1, 0, 0, 1]⟩, ⟨0, [1, 1]⟩⟩
def basisLaw8 : Identity Nat := ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1, 2, 2]⟩⟩
def basisLaw9 : Identity Nat := ⟨⟨0, [1, 2]⟩, ⟨0, [2, 2, 1, 2]⟩⟩
def basisLaw10 : Identity Nat := ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def basis : List (Identity Nat) :=
  [basisLaw0, basisLaw1, basisLaw2, basisLaw3, basisLaw4, basisLaw5, basisLaw6, basisLaw7, basisLaw8, basisLaw9, basisLaw10]

def leftBasisLaw0 : Identity Nat := ⟨⟨0, [1]⟩, ⟨0, []⟩⟩

def leftBasis : List (Identity Nat) :=
  [leftBasisLaw0]

theorem leftDerivesLaw0 :
    Derives leftBasis basisLaw0.lhs basisLaw0.rhs := by
  have step0 : Derives leftBasis ⟨0, []⟩ ⟨0, [0, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem leftDerivesLaw1 :
    Derives leftBasis basisLaw1.lhs basisLaw1.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1]⟩ ⟨0, [1]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  have step1 : Derives leftBasis ⟨0, [1]⟩ ⟨0, [1, 0, 1, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, [0, 1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw2 :
    Derives leftBasis basisLaw2.lhs basisLaw2.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1]⟩ ⟨0, [1, 1, 0, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, [1]⟩)
  exact step0

theorem leftDerivesLaw3 :
    Derives leftBasis basisLaw3.lhs basisLaw3.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 0]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [0]⟩)
  have step1 : Derives leftBasis ⟨0, [1, 0]⟩ ⟨0, [1, 0, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [1]⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw4 :
    Derives leftBasis basisLaw4.lhs basisLaw4.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 0, 0]⟩ ⟨0, [1, 0, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [0, 0]⟩)
  have step1 : Derives leftBasis ⟨0, [1, 0, 0]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [1]⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw5 :
    Derives leftBasis basisLaw5.lhs basisLaw5.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 0, 1]⟩ ⟨0, [1, 0, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [0, 1]⟩)
  have step1 : Derives leftBasis ⟨0, [1, 0, 1]⟩ ⟨0, [1, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [1]⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw6 :
    Derives leftBasis basisLaw6.lhs basisLaw6.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 1]⟩ ⟨0, [1, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [1]⟩)
  have step1 : Derives leftBasis ⟨0, [1, 1]⟩ ⟨0, [1, 0, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [1]⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw7 :
    Derives leftBasis basisLaw7.lhs basisLaw7.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 0, 0, 1]⟩ ⟨0, [1, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [1]⟩
      | 1 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  exact step0

theorem leftDerivesLaw8 :
    Derives leftBasis basisLaw8.lhs basisLaw8.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 2]⟩ ⟨0, [2]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, []⟩)
  have step1 : Derives leftBasis ⟨0, [2]⟩ ⟨0, [2, 1, 2, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨2, [1, 2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, []⟩)
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw9 :
    Derives leftBasis basisLaw9.lhs basisLaw9.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 2]⟩ ⟨0, [2, 2, 1, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨2, [2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [2]⟩)
  exact step0

theorem leftDerivesLaw10 :
    Derives leftBasis basisLaw10.lhs basisLaw10.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 2, 1]⟩ ⟨0, [2, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, [1]⟩)
  have step1 : Derives leftBasis ⟨0, [2, 1]⟩ ⟨0, [2, 1, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [2]⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  exact Derives.trans step0 (step1)

/-- 11 fixed displayed-law instances. -/
theorem displayedInLeftBasis : FiniteCertificate.DerivesAll leftBasis basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact leftDerivesLaw0
  · exact leftDerivesLaw1
  · exact leftDerivesLaw2
  · exact leftDerivesLaw3
  · exact leftDerivesLaw4
  · exact leftDerivesLaw5
  · exact leftDerivesLaw6
  · exact leftDerivesLaw7
  · exact leftDerivesLaw8
  · exact leftDerivesLaw9
  · exact leftDerivesLaw10

def rightBasisLaw0 : Identity Nat := ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩
def rightBasisLaw1 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def rightBasis : List (Identity Nat) :=
  [rightBasisLaw0, rightBasisLaw1]

theorem rightDerivesLaw0 :
    Derives rightBasis basisLaw0.lhs basisLaw0.rhs := by
  have step0 : Derives rightBasis ⟨0, []⟩ ⟨0, [0, 0]⟩ := by
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
  have step0 : Derives rightBasis ⟨0, [0, 1]⟩ ⟨0, [0, 1, 1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [0]⟩ instantiated)
  have step1 : Derives rightBasis ⟨0, [0, 1, 1, 1]⟩ ⟨0, [1, 0, 1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, []⟩ instantiated) ⟨1, []⟩)
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw2 :
    Derives rightBasis basisLaw2.lhs basisLaw2.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1]⟩ ⟨0, [0, 1, 1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [0]⟩ instantiated)
  have step1 : Derives rightBasis ⟨0, [0, 1, 1, 1]⟩ ⟨0, [1, 0, 1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, []⟩ instantiated) ⟨1, []⟩)
  have step2 : Derives rightBasis ⟨0, [1, 0, 1, 1]⟩ ⟨0, [1, 1, 0, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨1, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  exact Derives.trans step0 (Derives.trans step1 (step2))

theorem rightDerivesLaw3 :
    Derives rightBasis basisLaw3.lhs basisLaw3.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 0]⟩ ⟨0, [1, 0, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem rightDerivesLaw4 :
    Derives rightBasis basisLaw4.lhs basisLaw4.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 0, 0]⟩ ⟨0, [1, 0, 0, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  have step1 : Derives rightBasis ⟨0, [1, 0, 0, 0]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [1]⟩ instantiated)
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw5 :
    Derives rightBasis basisLaw5.lhs basisLaw5.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 0, 1]⟩ ⟨0, [0, 0, 1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [0]⟩ instantiated)
  have step1 : Derives rightBasis ⟨0, [0, 0, 1, 1]⟩ ⟨0, [1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [1]⟩)
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw6 :
    Derives rightBasis basisLaw6.lhs basisLaw6.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 1]⟩ ⟨0, [1, 0, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  exact step0

theorem rightDerivesLaw7 :
    Derives rightBasis basisLaw7.lhs basisLaw7.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 0, 0, 1]⟩ ⟨0, [0, 0, 1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  have step1 : Derives rightBasis ⟨0, [0, 0, 1, 1]⟩ ⟨0, [1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [1]⟩)
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw8 :
    Derives rightBasis basisLaw8.lhs basisLaw8.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 2]⟩ ⟨0, [1, 2, 2, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [1]⟩ instantiated)
  have step1 : Derives rightBasis ⟨0, [1, 2, 2, 2]⟩ ⟨0, [2, 1, 2, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, []⟩ instantiated) ⟨2, []⟩)
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw9 :
    Derives rightBasis basisLaw9.lhs basisLaw9.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 2]⟩ ⟨0, [1, 2, 2, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [1]⟩ instantiated)
  have step1 : Derives rightBasis ⟨0, [1, 2, 2, 2]⟩ ⟨0, [2, 1, 2, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, []⟩ instantiated) ⟨2, []⟩)
  have step2 : Derives rightBasis ⟨0, [2, 1, 2, 2]⟩ ⟨0, [2, 2, 1, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | 1 => ⟨2, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  exact Derives.trans step0 (Derives.trans step1 (step2))

theorem rightDerivesLaw10 :
    Derives rightBasis basisLaw10.lhs basisLaw10.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 2, 1]⟩ ⟨0, [2, 1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  exact step0

/-- 11 fixed displayed-law instances. -/
theorem displayedInRightBasis : FiniteCertificate.DerivesAll rightBasis basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rightDerivesLaw0
  · exact rightDerivesLaw1
  · exact rightDerivesLaw2
  · exact rightDerivesLaw3
  · exact rightDerivesLaw4
  · exact rightDerivesLaw5
  · exact rightDerivesLaw6
  · exact rightDerivesLaw7
  · exact rightDerivesLaw8
  · exact rightDerivesLaw9
  · exact rightDerivesLaw10

private theorem leftModelsLaw0 : basisLaw0.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_4.table.semigroup := by
  have roundTrip : (basisLaw0.map toFinThree).map Fin.val = basisLaw0 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_4.table (basisLaw0.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw1 : basisLaw1.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_4.table.semigroup := by
  have roundTrip : (basisLaw1.map toFinThree).map Fin.val = basisLaw1 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_4.table (basisLaw1.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw2 : basisLaw2.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_4.table.semigroup := by
  have roundTrip : (basisLaw2.map toFinThree).map Fin.val = basisLaw2 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_4.table (basisLaw2.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw3 : basisLaw3.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_4.table.semigroup := by
  have roundTrip : (basisLaw3.map toFinThree).map Fin.val = basisLaw3 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_4.table (basisLaw3.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw4 : basisLaw4.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_4.table.semigroup := by
  have roundTrip : (basisLaw4.map toFinThree).map Fin.val = basisLaw4 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_4.table (basisLaw4.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw5 : basisLaw5.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_4.table.semigroup := by
  have roundTrip : (basisLaw5.map toFinThree).map Fin.val = basisLaw5 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_4.table (basisLaw5.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw6 : basisLaw6.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_4.table.semigroup := by
  have roundTrip : (basisLaw6.map toFinThree).map Fin.val = basisLaw6 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_4.table (basisLaw6.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw7 : basisLaw7.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_4.table.semigroup := by
  have roundTrip : (basisLaw7.map toFinThree).map Fin.val = basisLaw7 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_4.table (basisLaw7.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw8 : basisLaw8.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_4.table.semigroup := by
  have roundTrip : (basisLaw8.map toFinThree).map Fin.val = basisLaw8 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_4.table (basisLaw8.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw9 : basisLaw9.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_4.table.semigroup := by
  have roundTrip : (basisLaw9.map toFinThree).map Fin.val = basisLaw9 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_4.table (basisLaw9.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw10 : basisLaw10.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_4.table.semigroup := by
  have roundTrip : (basisLaw10.map toFinThree).map Fin.val = basisLaw10 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_4.table (basisLaw10.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem leftModels : Models SemigroupBasis.Generated.Catalogue.S2_4.table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact leftModelsLaw0
  · exact leftModelsLaw1
  · exact leftModelsLaw2
  · exact leftModelsLaw3
  · exact leftModelsLaw4
  · exact leftModelsLaw5
  · exact leftModelsLaw6
  · exact leftModelsLaw7
  · exact leftModelsLaw8
  · exact leftModelsLaw9
  · exact leftModelsLaw10

private def rightTable : FiniteTable where
  order := 4
  mul := fun a b => SemigroupBasis.Generated.Catalogue.S4_95.table.mul b a
  assoc := fun a b c => (SemigroupBasis.Generated.Catalogue.S4_95.table.assoc c b a).symm

private theorem rightModelsLaw0 : basisLaw0.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_95.table.semigroup.opposite := by
  have roundTrip : (basisLaw0.map toFinThree).map Fin.val = basisLaw0 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound rightTable (basisLaw0.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw1 : basisLaw1.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_95.table.semigroup.opposite := by
  have roundTrip : (basisLaw1.map toFinThree).map Fin.val = basisLaw1 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound rightTable (basisLaw1.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw2 : basisLaw2.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_95.table.semigroup.opposite := by
  have roundTrip : (basisLaw2.map toFinThree).map Fin.val = basisLaw2 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound rightTable (basisLaw2.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw3 : basisLaw3.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_95.table.semigroup.opposite := by
  have roundTrip : (basisLaw3.map toFinThree).map Fin.val = basisLaw3 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound rightTable (basisLaw3.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw4 : basisLaw4.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_95.table.semigroup.opposite := by
  have roundTrip : (basisLaw4.map toFinThree).map Fin.val = basisLaw4 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound rightTable (basisLaw4.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw5 : basisLaw5.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_95.table.semigroup.opposite := by
  have roundTrip : (basisLaw5.map toFinThree).map Fin.val = basisLaw5 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound rightTable (basisLaw5.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw6 : basisLaw6.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_95.table.semigroup.opposite := by
  have roundTrip : (basisLaw6.map toFinThree).map Fin.val = basisLaw6 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound rightTable (basisLaw6.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw7 : basisLaw7.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_95.table.semigroup.opposite := by
  have roundTrip : (basisLaw7.map toFinThree).map Fin.val = basisLaw7 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound rightTable (basisLaw7.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw8 : basisLaw8.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_95.table.semigroup.opposite := by
  have roundTrip : (basisLaw8.map toFinThree).map Fin.val = basisLaw8 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound rightTable (basisLaw8.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw9 : basisLaw9.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_95.table.semigroup.opposite := by
  have roundTrip : (basisLaw9.map toFinThree).map Fin.val = basisLaw9 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound rightTable (basisLaw9.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw10 : basisLaw10.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_95.table.semigroup.opposite := by
  have roundTrip : (basisLaw10.map toFinThree).map Fin.val = basisLaw10 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound rightTable (basisLaw10.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem rightModels : Models SemigroupBasis.Generated.Catalogue.S4_95.table.semigroup.opposite basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rightModelsLaw0
  · exact rightModelsLaw1
  · exact rightModelsLaw2
  · exact rightModelsLaw3
  · exact rightModelsLaw4
  · exact rightModelsLaw5
  · exact rightModelsLaw6
  · exact rightModelsLaw7
  · exact rightModelsLaw8
  · exact rightModelsLaw9
  · exact rightModelsLaw10

namespace S6_14814

/-- Exact catalogue table SHA256 `f68a5d89379fd47b87e2e84adfc25ba3409f358e03328add73546aa85149497e`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6)) else if a = 1 then (if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6)) else if a = 2 then (if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6)) else if a = 3 then (if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)) else if a = 4 then (if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6)) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def ontoLeftMap (a : Fin 6) : Fin 2 :=
  if a = 0 then (0 : Fin 2) else if a = 1 then (0 : Fin 2) else if a = 2 then (0 : Fin 2) else if a = 3 then (1 : Fin 2) else if a = 4 then (0 : Fin 2) else (1 : Fin 2)

def ontoLeftSection (a : Fin 2) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else (3 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S2_4.table.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (2 : Fin 4) else if a = 3 then (2 : Fin 4) else if a = 4 then (3 : Fin 4) else (3 : Fin 4)

def ontoRightSection (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (4 : Fin 6)

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S4_95.table.semigroup.opposite where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.Catalogue.S2_4.table.semigroup SemigroupBasis.Generated.Catalogue.S4_95.table.semigroup.opposite where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro a b
    exact by decide +revert

theorem models : Models table.semigroup basis := by
  intro identity member
  exact (pair.satisfiedBy_iff identity).mpr ⟨leftModels identity member, rightModels identity member⟩

def ontoLeftOpposite : SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S2_4.table.semigroup.opposite where
  toFun := ontoLeftMap
  map_mul := fun a b => ontoLeft.map_mul b a
  preimage := ontoLeftSection
  right_inverse := ontoLeft.right_inverse

def ontoRightOpposite : SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S4_95.table.semigroup.opposite.opposite where
  toFun := ontoRightMap
  map_mul := fun a b => ontoRight.map_mul b a
  preimage := ontoRightSection
  right_inverse := ontoRight.right_inverse

def pairOpposite : SubdirectPair table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S2_4.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S4_95.table.semigroup.opposite.opposite where
  left := ontoLeftOpposite
  right := ontoRightOpposite
  jointlyInjective := pair.jointlyInjective

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) :=
  models.oppositeReversed

end S6_14814

end SigmaF137a

namespace SigmaF137b

def basisLaw0 : Identity Nat := ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩
def basisLaw1 : Identity Nat := ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0, 1, 1]⟩⟩
def basisLaw2 : Identity Nat := ⟨⟨0, [0, 1]⟩, ⟨0, [1, 1, 0, 1]⟩⟩
def basisLaw3 : Identity Nat := ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩
def basisLaw4 : Identity Nat := ⟨⟨0, [0, 1, 0, 0]⟩, ⟨0, [1, 0]⟩⟩
def basisLaw5 : Identity Nat := ⟨⟨0, [0, 1, 0, 1]⟩, ⟨0, [1, 1]⟩⟩
def basisLaw6 : Identity Nat := ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 0, 1]⟩⟩
def basisLaw7 : Identity Nat := ⟨⟨0, [1, 0, 0, 1]⟩, ⟨0, [1, 1]⟩⟩
def basisLaw8 : Identity Nat := ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1, 2, 2]⟩⟩
def basisLaw9 : Identity Nat := ⟨⟨0, [1, 2]⟩, ⟨0, [2, 2, 1, 2]⟩⟩
def basisLaw10 : Identity Nat := ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def basis : List (Identity Nat) :=
  [basisLaw0, basisLaw1, basisLaw2, basisLaw3, basisLaw4, basisLaw5, basisLaw6, basisLaw7, basisLaw8, basisLaw9, basisLaw10]

def leftBasisLaw0 : Identity Nat := ⟨⟨0, [1]⟩, ⟨0, []⟩⟩

def leftBasis : List (Identity Nat) :=
  [leftBasisLaw0]

theorem leftDerivesLaw0 :
    Derives leftBasis basisLaw0.lhs basisLaw0.rhs := by
  have step0 : Derives leftBasis ⟨0, []⟩ ⟨0, [0, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem leftDerivesLaw1 :
    Derives leftBasis basisLaw1.lhs basisLaw1.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1]⟩ ⟨0, [1]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  have step1 : Derives leftBasis ⟨0, [1]⟩ ⟨0, [1, 0, 1, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, [0, 1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw2 :
    Derives leftBasis basisLaw2.lhs basisLaw2.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1]⟩ ⟨0, [1, 1, 0, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, [1]⟩)
  exact step0

theorem leftDerivesLaw3 :
    Derives leftBasis basisLaw3.lhs basisLaw3.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 0]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [0]⟩)
  have step1 : Derives leftBasis ⟨0, [1, 0]⟩ ⟨0, [1, 0, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [1]⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw4 :
    Derives leftBasis basisLaw4.lhs basisLaw4.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 0, 0]⟩ ⟨0, [1, 0, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [0, 0]⟩)
  have step1 : Derives leftBasis ⟨0, [1, 0, 0]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [1]⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw5 :
    Derives leftBasis basisLaw5.lhs basisLaw5.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 0, 1]⟩ ⟨0, [1, 0, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [0, 1]⟩)
  have step1 : Derives leftBasis ⟨0, [1, 0, 1]⟩ ⟨0, [1, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [1]⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw6 :
    Derives leftBasis basisLaw6.lhs basisLaw6.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 1]⟩ ⟨0, [1, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [1]⟩)
  have step1 : Derives leftBasis ⟨0, [1, 1]⟩ ⟨0, [1, 0, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [1]⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw7 :
    Derives leftBasis basisLaw7.lhs basisLaw7.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 0, 0, 1]⟩ ⟨0, [1, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [1]⟩
      | 1 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  exact step0

theorem leftDerivesLaw8 :
    Derives leftBasis basisLaw8.lhs basisLaw8.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 2]⟩ ⟨0, [2]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, []⟩)
  have step1 : Derives leftBasis ⟨0, [2]⟩ ⟨0, [2, 1, 2, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨2, [1, 2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, []⟩)
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw9 :
    Derives leftBasis basisLaw9.lhs basisLaw9.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 2]⟩ ⟨0, [2, 2, 1, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨2, [2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [2]⟩)
  exact step0

theorem leftDerivesLaw10 :
    Derives leftBasis basisLaw10.lhs basisLaw10.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 2, 1]⟩ ⟨0, [2, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, [1]⟩)
  have step1 : Derives leftBasis ⟨0, [2, 1]⟩ ⟨0, [2, 1, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [2]⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  exact Derives.trans step0 (step1)

/-- 11 fixed displayed-law instances. -/
theorem displayedInLeftBasis : FiniteCertificate.DerivesAll leftBasis basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact leftDerivesLaw0
  · exact leftDerivesLaw1
  · exact leftDerivesLaw2
  · exact leftDerivesLaw3
  · exact leftDerivesLaw4
  · exact leftDerivesLaw5
  · exact leftDerivesLaw6
  · exact leftDerivesLaw7
  · exact leftDerivesLaw8
  · exact leftDerivesLaw9
  · exact leftDerivesLaw10

def rightBasisLaw0 : Identity Nat := ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩
def rightBasisLaw1 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def rightBasis : List (Identity Nat) :=
  [rightBasisLaw0, rightBasisLaw1]

theorem rightDerivesLaw0 :
    Derives rightBasis basisLaw0.lhs basisLaw0.rhs := by
  have step0 : Derives rightBasis ⟨0, []⟩ ⟨0, [0, 0]⟩ := by
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
  have step0 : Derives rightBasis ⟨0, [0, 1]⟩ ⟨0, [0, 1, 1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [0]⟩ instantiated)
  have step1 : Derives rightBasis ⟨0, [0, 1, 1, 1]⟩ ⟨0, [1, 0, 1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, []⟩ instantiated) ⟨1, []⟩)
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw2 :
    Derives rightBasis basisLaw2.lhs basisLaw2.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1]⟩ ⟨0, [0, 1, 1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [0]⟩ instantiated)
  have step1 : Derives rightBasis ⟨0, [0, 1, 1, 1]⟩ ⟨0, [1, 0, 1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, []⟩ instantiated) ⟨1, []⟩)
  have step2 : Derives rightBasis ⟨0, [1, 0, 1, 1]⟩ ⟨0, [1, 1, 0, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨1, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  exact Derives.trans step0 (Derives.trans step1 (step2))

theorem rightDerivesLaw3 :
    Derives rightBasis basisLaw3.lhs basisLaw3.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 0]⟩ ⟨0, [1, 0, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact step0

theorem rightDerivesLaw4 :
    Derives rightBasis basisLaw4.lhs basisLaw4.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 0, 0]⟩ ⟨0, [1, 0, 0, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  have step1 : Derives rightBasis ⟨0, [1, 0, 0, 0]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [1]⟩ instantiated)
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw5 :
    Derives rightBasis basisLaw5.lhs basisLaw5.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 0, 1]⟩ ⟨0, [0, 0, 1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [0]⟩ instantiated)
  have step1 : Derives rightBasis ⟨0, [0, 0, 1, 1]⟩ ⟨0, [1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [1]⟩)
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw6 :
    Derives rightBasis basisLaw6.lhs basisLaw6.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 1]⟩ ⟨0, [1, 0, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  exact step0

theorem rightDerivesLaw7 :
    Derives rightBasis basisLaw7.lhs basisLaw7.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 0, 0, 1]⟩ ⟨0, [0, 0, 1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  have step1 : Derives rightBasis ⟨0, [0, 0, 1, 1]⟩ ⟨0, [1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [1]⟩)
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw8 :
    Derives rightBasis basisLaw8.lhs basisLaw8.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 2]⟩ ⟨0, [1, 2, 2, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [1]⟩ instantiated)
  have step1 : Derives rightBasis ⟨0, [1, 2, 2, 2]⟩ ⟨0, [2, 1, 2, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, []⟩ instantiated) ⟨2, []⟩)
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw9 :
    Derives rightBasis basisLaw9.lhs basisLaw9.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 2]⟩ ⟨0, [1, 2, 2, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [1]⟩ instantiated)
  have step1 : Derives rightBasis ⟨0, [1, 2, 2, 2]⟩ ⟨0, [2, 1, 2, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | 1 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, []⟩ instantiated) ⟨2, []⟩)
  have step2 : Derives rightBasis ⟨0, [2, 1, 2, 2]⟩ ⟨0, [2, 2, 1, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | 1 => ⟨2, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  exact Derives.trans step0 (Derives.trans step1 (step2))

theorem rightDerivesLaw10 :
    Derives rightBasis basisLaw10.lhs basisLaw10.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 2, 1]⟩ ⟨0, [2, 1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, []⟩ instantiated)
  exact step0

/-- 11 fixed displayed-law instances. -/
theorem displayedInRightBasis : FiniteCertificate.DerivesAll rightBasis basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rightDerivesLaw0
  · exact rightDerivesLaw1
  · exact rightDerivesLaw2
  · exact rightDerivesLaw3
  · exact rightDerivesLaw4
  · exact rightDerivesLaw5
  · exact rightDerivesLaw6
  · exact rightDerivesLaw7
  · exact rightDerivesLaw8
  · exact rightDerivesLaw9
  · exact rightDerivesLaw10

private theorem leftModelsLaw0 : basisLaw0.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_4.table.semigroup := by
  have roundTrip : (basisLaw0.map toFinThree).map Fin.val = basisLaw0 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_4.table (basisLaw0.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw1 : basisLaw1.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_4.table.semigroup := by
  have roundTrip : (basisLaw1.map toFinThree).map Fin.val = basisLaw1 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_4.table (basisLaw1.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw2 : basisLaw2.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_4.table.semigroup := by
  have roundTrip : (basisLaw2.map toFinThree).map Fin.val = basisLaw2 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_4.table (basisLaw2.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw3 : basisLaw3.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_4.table.semigroup := by
  have roundTrip : (basisLaw3.map toFinThree).map Fin.val = basisLaw3 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_4.table (basisLaw3.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw4 : basisLaw4.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_4.table.semigroup := by
  have roundTrip : (basisLaw4.map toFinThree).map Fin.val = basisLaw4 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_4.table (basisLaw4.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw5 : basisLaw5.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_4.table.semigroup := by
  have roundTrip : (basisLaw5.map toFinThree).map Fin.val = basisLaw5 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_4.table (basisLaw5.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw6 : basisLaw6.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_4.table.semigroup := by
  have roundTrip : (basisLaw6.map toFinThree).map Fin.val = basisLaw6 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_4.table (basisLaw6.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw7 : basisLaw7.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_4.table.semigroup := by
  have roundTrip : (basisLaw7.map toFinThree).map Fin.val = basisLaw7 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_4.table (basisLaw7.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw8 : basisLaw8.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_4.table.semigroup := by
  have roundTrip : (basisLaw8.map toFinThree).map Fin.val = basisLaw8 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_4.table (basisLaw8.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw9 : basisLaw9.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_4.table.semigroup := by
  have roundTrip : (basisLaw9.map toFinThree).map Fin.val = basisLaw9 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_4.table (basisLaw9.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw10 : basisLaw10.SatisfiedBy SemigroupBasis.Generated.Catalogue.S2_4.table.semigroup := by
  have roundTrip : (basisLaw10.map toFinThree).map Fin.val = basisLaw10 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S2_4.table (basisLaw10.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem leftModels : Models SemigroupBasis.Generated.Catalogue.S2_4.table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact leftModelsLaw0
  · exact leftModelsLaw1
  · exact leftModelsLaw2
  · exact leftModelsLaw3
  · exact leftModelsLaw4
  · exact leftModelsLaw5
  · exact leftModelsLaw6
  · exact leftModelsLaw7
  · exact leftModelsLaw8
  · exact leftModelsLaw9
  · exact leftModelsLaw10

private def rightTable : FiniteTable where
  order := 5
  mul := fun a b => SemigroupBasis.Generated.Catalogue.S5_994.table.mul b a
  assoc := fun a b c => (SemigroupBasis.Generated.Catalogue.S5_994.table.assoc c b a).symm

private theorem rightModelsLaw0 : basisLaw0.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_994.table.semigroup.opposite := by
  have roundTrip : (basisLaw0.map toFinThree).map Fin.val = basisLaw0 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound rightTable (basisLaw0.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw1 : basisLaw1.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_994.table.semigroup.opposite := by
  have roundTrip : (basisLaw1.map toFinThree).map Fin.val = basisLaw1 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound rightTable (basisLaw1.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw2 : basisLaw2.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_994.table.semigroup.opposite := by
  have roundTrip : (basisLaw2.map toFinThree).map Fin.val = basisLaw2 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound rightTable (basisLaw2.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw3 : basisLaw3.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_994.table.semigroup.opposite := by
  have roundTrip : (basisLaw3.map toFinThree).map Fin.val = basisLaw3 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound rightTable (basisLaw3.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw4 : basisLaw4.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_994.table.semigroup.opposite := by
  have roundTrip : (basisLaw4.map toFinThree).map Fin.val = basisLaw4 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound rightTable (basisLaw4.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw5 : basisLaw5.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_994.table.semigroup.opposite := by
  have roundTrip : (basisLaw5.map toFinThree).map Fin.val = basisLaw5 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound rightTable (basisLaw5.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw6 : basisLaw6.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_994.table.semigroup.opposite := by
  have roundTrip : (basisLaw6.map toFinThree).map Fin.val = basisLaw6 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound rightTable (basisLaw6.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw7 : basisLaw7.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_994.table.semigroup.opposite := by
  have roundTrip : (basisLaw7.map toFinThree).map Fin.val = basisLaw7 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound rightTable (basisLaw7.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw8 : basisLaw8.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_994.table.semigroup.opposite := by
  have roundTrip : (basisLaw8.map toFinThree).map Fin.val = basisLaw8 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound rightTable (basisLaw8.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw9 : basisLaw9.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_994.table.semigroup.opposite := by
  have roundTrip : (basisLaw9.map toFinThree).map Fin.val = basisLaw9 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound rightTable (basisLaw9.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw10 : basisLaw10.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_994.table.semigroup.opposite := by
  have roundTrip : (basisLaw10.map toFinThree).map Fin.val = basisLaw10 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound rightTable (basisLaw10.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem rightModels : Models SemigroupBasis.Generated.Catalogue.S5_994.table.semigroup.opposite basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rightModelsLaw0
  · exact rightModelsLaw1
  · exact rightModelsLaw2
  · exact rightModelsLaw3
  · exact rightModelsLaw4
  · exact rightModelsLaw5
  · exact rightModelsLaw6
  · exact rightModelsLaw7
  · exact rightModelsLaw8
  · exact rightModelsLaw9
  · exact rightModelsLaw10

namespace S6_14833

/-- Exact catalogue table SHA256 `ea37f29fe33f552561e931326e6f01a78d1c6392cfb2c27f30c892488aeec333`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if a = 1 then (if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if a = 2 then (if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)) else if a = 3 then (if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6)) else if a = 4 then (if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def ontoLeftMap (a : Fin 6) : Fin 2 :=
  if a = 0 then (0 : Fin 2) else if a = 1 then (0 : Fin 2) else if a = 2 then (0 : Fin 2) else if a = 3 then (1 : Fin 2) else if a = 4 then (0 : Fin 2) else (0 : Fin 2)

def ontoLeftSection (a : Fin 2) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else (3 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S2_4.table.semigroup where
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

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_994.table.semigroup.opposite where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.Catalogue.S2_4.table.semigroup SemigroupBasis.Generated.Catalogue.S5_994.table.semigroup.opposite where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro a b
    exact by decide +revert

theorem models : Models table.semigroup basis := by
  intro identity member
  exact (pair.satisfiedBy_iff identity).mpr ⟨leftModels identity member, rightModels identity member⟩

def ontoLeftOpposite : SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S2_4.table.semigroup.opposite where
  toFun := ontoLeftMap
  map_mul := fun a b => ontoLeft.map_mul b a
  preimage := ontoLeftSection
  right_inverse := ontoLeft.right_inverse

def ontoRightOpposite : SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_994.table.semigroup.opposite.opposite where
  toFun := ontoRightMap
  map_mul := fun a b => ontoRight.map_mul b a
  preimage := ontoRightSection
  right_inverse := ontoRight.right_inverse

def pairOpposite : SubdirectPair table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S2_4.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_994.table.semigroup.opposite.opposite where
  left := ontoLeftOpposite
  right := ontoRightOpposite
  jointlyInjective := pair.jointlyInjective

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) :=
  models.oppositeReversed

end S6_14833

end SigmaF137b

namespace SigmaF137c

def basisLaw0 : Identity Nat := ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩
def basisLaw1 : Identity Nat := ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0, 1, 1]⟩⟩
def basisLaw2 : Identity Nat := ⟨⟨0, [0, 1]⟩, ⟨0, [1, 1, 0, 1]⟩⟩
def basisLaw3 : Identity Nat := ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩
def basisLaw4 : Identity Nat := ⟨⟨0, [0, 1, 0, 0]⟩, ⟨0, [1, 0]⟩⟩
def basisLaw5 : Identity Nat := ⟨⟨0, [0, 1, 0, 1]⟩, ⟨0, [1, 1]⟩⟩
def basisLaw6 : Identity Nat := ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 0, 1]⟩⟩
def basisLaw7 : Identity Nat := ⟨⟨0, [1, 0, 0, 1]⟩, ⟨0, [1, 1]⟩⟩
def basisLaw8 : Identity Nat := ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1, 2, 2]⟩⟩
def basisLaw9 : Identity Nat := ⟨⟨0, [1, 2]⟩, ⟨0, [2, 2, 1, 2]⟩⟩
def basisLaw10 : Identity Nat := ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def basis : List (Identity Nat) :=
  [basisLaw0, basisLaw1, basisLaw2, basisLaw3, basisLaw4, basisLaw5, basisLaw6, basisLaw7, basisLaw8, basisLaw9, basisLaw10]

def leftBasisLaw0 : Identity Nat := ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩
def leftBasisLaw1 : Identity Nat := ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def leftBasis : List (Identity Nat) :=
  [leftBasisLaw0, leftBasisLaw1]

theorem leftDerivesLaw0 :
    Derives leftBasis basisLaw0.lhs basisLaw0.rhs := by
  have step0 : Derives leftBasis ⟨0, []⟩ ⟨0, [0, 0]⟩ := by
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
  have step0 : Derives leftBasis ⟨0, [0, 1]⟩ ⟨0, [0, 1, 1, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [0]⟩ instantiated)
  have step1 : Derives leftBasis ⟨0, [0, 1, 1, 1]⟩ ⟨0, [1, 0, 1, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [1]⟩)
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw2 :
    Derives leftBasis basisLaw2.lhs basisLaw2.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1]⟩ ⟨0, [0, 1, 1, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [0]⟩ instantiated)
  have step1 : Derives leftBasis ⟨0, [0, 1, 1, 1]⟩ ⟨0, [1, 1, 0, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1, 1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw3 :
    Derives leftBasis basisLaw3.lhs basisLaw3.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 0]⟩ ⟨0, [1, 0, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, []⟩)
  exact step0

theorem leftDerivesLaw4 :
    Derives leftBasis basisLaw4.lhs basisLaw4.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 0, 0]⟩ ⟨0, [1, 0, 0, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨0, [0]⟩)
  have step1 : Derives leftBasis ⟨0, [1, 0, 0, 0]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [1]⟩ instantiated)
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw5 :
    Derives leftBasis basisLaw5.lhs basisLaw5.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 0, 1]⟩ ⟨0, [0, 0, 1, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [0, 1]⟩
      | 1 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  have step1 : Derives leftBasis ⟨0, [0, 0, 1, 1]⟩ ⟨0, [1, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [1]⟩)
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw6 :
    Derives leftBasis basisLaw6.lhs basisLaw6.rhs := by
  have step0 : Derives leftBasis ⟨0, [0, 1, 1]⟩ ⟨0, [1, 0, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | 1 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  exact step0

theorem leftDerivesLaw7 :
    Derives leftBasis basisLaw7.lhs basisLaw7.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 0, 0, 1]⟩ ⟨0, [0, 0, 1, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [1]⟩
      | 1 => ⟨0, [0]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  have step1 : Derives leftBasis ⟨0, [0, 0, 1, 1]⟩ ⟨0, [1, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [1]⟩)
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw8 :
    Derives leftBasis basisLaw8.lhs basisLaw8.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 2]⟩ ⟨0, [1, 2, 2, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [1]⟩ instantiated)
  have step1 : Derives leftBasis ⟨0, [1, 2, 2, 2]⟩ ⟨0, [2, 1, 2, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, []⟩ instantiated) ⟨2, [2]⟩)
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw9 :
    Derives leftBasis basisLaw9.lhs basisLaw9.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 2]⟩ ⟨0, [1, 2, 2, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw0.lhs leftBasisLaw0.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [1]⟩ instantiated)
  have step1 : Derives leftBasis ⟨0, [1, 2, 2, 2]⟩ ⟨0, [2, 2, 1, 2]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨2, [2]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, []⟩ instantiated) ⟨2, []⟩)
  exact Derives.trans step0 (step1)

theorem leftDerivesLaw10 :
    Derives leftBasis basisLaw10.lhs basisLaw10.rhs := by
  have step0 : Derives leftBasis ⟨0, [1, 2, 1]⟩ ⟨0, [2, 1, 1]⟩ := by
    have base : Derives leftBasis leftBasisLaw1.lhs leftBasisLaw1.rhs :=
      Derives.fromBasis (by simp [leftBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [leftBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, []⟩ instantiated) ⟨1, []⟩)
  exact step0

/-- 11 fixed displayed-law instances. -/
theorem displayedInLeftBasis : FiniteCertificate.DerivesAll leftBasis basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact leftDerivesLaw0
  · exact leftDerivesLaw1
  · exact leftDerivesLaw2
  · exact leftDerivesLaw3
  · exact leftDerivesLaw4
  · exact leftDerivesLaw5
  · exact leftDerivesLaw6
  · exact leftDerivesLaw7
  · exact leftDerivesLaw8
  · exact leftDerivesLaw9
  · exact leftDerivesLaw10

def rightBasisLaw0 : Identity Nat := ⟨⟨0, []⟩, ⟨0, [0]⟩⟩
def rightBasisLaw1 : Identity Nat := ⟨⟨2, [1, 0]⟩, ⟨2, [0, 1, 0]⟩⟩

def rightBasis : List (Identity Nat) :=
  [rightBasisLaw0, rightBasisLaw1]

theorem rightDerivesLaw0 :
    Derives rightBasis basisLaw0.lhs basisLaw0.rhs := by
  have step0 : Derives rightBasis ⟨0, []⟩ ⟨0, [0]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives rightBasis ⟨0, [0]⟩ ⟨0, [0, 0]⟩ := by
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
  have step0 : Derives rightBasis ⟨0, [0, 1]⟩ ⟨0, [0, 1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [0]⟩ instantiated)
  have step1 : Derives rightBasis ⟨0, [0, 1, 1]⟩ ⟨0, [1, 0, 1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | 2 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw2 :
    Derives rightBasis basisLaw2.lhs basisLaw2.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1]⟩ ⟨0, [1, 0, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | 2 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives rightBasis ⟨0, [1, 0, 1]⟩ ⟨0, [1, 1, 0, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, []⟩ instantiated) ⟨0, [1]⟩)
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw3 :
    Derives rightBasis basisLaw3.lhs basisLaw3.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 0]⟩ ⟨0, [0, 1, 0, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [0, 1]⟩ instantiated)
  have step1 : Derives rightBasis ⟨0, [0, 1, 0, 0]⟩ ⟨0, [1, 0, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [0, 0]⟩)
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw4 :
    Derives rightBasis basisLaw4.lhs basisLaw4.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 0, 0]⟩ ⟨0, [1, 0, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [0, 0]⟩)
  have step1 : Derives rightBasis ⟨0, [1, 0, 0]⟩ ⟨0, [1, 0]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [1]⟩ instantiated)
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw5 :
    Derives rightBasis basisLaw5.lhs basisLaw5.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 0, 1]⟩ ⟨0, [0, 1, 0, 1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [0, 1, 0]⟩ instantiated)
  have step1 : Derives rightBasis ⟨0, [0, 1, 0, 1, 1]⟩ ⟨0, [1, 0, 1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, [0, 1, 1]⟩)
  have step2 : Derives rightBasis ⟨0, [1, 0, 1, 1]⟩ ⟨0, [1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  exact Derives.trans step0 (Derives.trans step1 (step2))

theorem rightDerivesLaw6 :
    Derives rightBasis basisLaw6.lhs basisLaw6.rhs := by
  have step0 : Derives rightBasis ⟨0, [0, 1, 1]⟩ ⟨0, [0, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [0]⟩ instantiated)
  have step1 : Derives rightBasis ⟨0, [0, 1]⟩ ⟨0, [1, 0, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨0, []⟩
      | 2 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw7 :
    Derives rightBasis basisLaw7.lhs basisLaw7.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 0, 0, 1]⟩ ⟨0, [1, 0, 0, 1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [1, 0, 0]⟩ instantiated)
  have step1 : Derives rightBasis ⟨0, [1, 0, 0, 1, 1]⟩ ⟨0, [1, 0, 1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, [1]⟩ instantiated) ⟨1, [1]⟩)
  have step2 : Derives rightBasis ⟨0, [1, 0, 1, 1]⟩ ⟨0, [1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨0, [1]⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  exact Derives.trans step0 (Derives.trans step1 (step2))

theorem rightDerivesLaw8 :
    Derives rightBasis basisLaw8.lhs basisLaw8.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 2]⟩ ⟨0, [1, 2, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [1]⟩ instantiated)
  have step1 : Derives rightBasis ⟨0, [1, 2, 2]⟩ ⟨0, [2, 1, 2, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨2, []⟩)
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw9 :
    Derives rightBasis basisLaw9.lhs basisLaw9.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 2]⟩ ⟨0, [2, 1, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | 1 => ⟨1, []⟩
      | 2 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using instantiated
  have step1 : Derives rightBasis ⟨0, [2, 1, 2]⟩ ⟨0, [2, 2, 1, 2]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨2, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight (Derives.prepend ⟨0, []⟩ instantiated) ⟨1, [2]⟩)
  exact Derives.trans step0 (step1)

theorem rightDerivesLaw10 :
    Derives rightBasis basisLaw10.lhs basisLaw10.rhs := by
  have step0 : Derives rightBasis ⟨0, [1, 2, 1]⟩ ⟨0, [1, 2, 1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw0.lhs rightBasisLaw0.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst base substitution
    simpa [rightBasisLaw0, substitution, Word.bind, Word.append, Word.singleton] using (Derives.prepend ⟨0, [1, 2]⟩ instantiated)
  have step1 : Derives rightBasis ⟨0, [1, 2, 1, 1]⟩ ⟨0, [2, 1, 1]⟩ := by
    have base : Derives rightBasis rightBasisLaw1.lhs rightBasisLaw1.rhs :=
      Derives.fromBasis (by simp [rightBasis])
    let substitution : Nat → Word Nat := fun
      | 0 => ⟨1, []⟩
      | 1 => ⟨2, []⟩
      | 2 => ⟨0, []⟩
      | n => Word.singleton n
    have instantiated := Derives.subst (Derives.symm base) substitution
    simpa [rightBasisLaw1, substitution, Word.bind, Word.append, Word.singleton] using (Derives.appendRight instantiated ⟨1, []⟩)
  exact Derives.trans step0 (step1)

/-- 11 fixed displayed-law instances. -/
theorem displayedInRightBasis : FiniteCertificate.DerivesAll rightBasis basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rightDerivesLaw0
  · exact rightDerivesLaw1
  · exact rightDerivesLaw2
  · exact rightDerivesLaw3
  · exact rightDerivesLaw4
  · exact rightDerivesLaw5
  · exact rightDerivesLaw6
  · exact rightDerivesLaw7
  · exact rightDerivesLaw8
  · exact rightDerivesLaw9
  · exact rightDerivesLaw10

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

private theorem leftModelsLaw3 : basisLaw3.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup := by
  have roundTrip : (basisLaw3.map toFinThree).map Fin.val = basisLaw3 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S3_11.table (basisLaw3.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw4 : basisLaw4.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup := by
  have roundTrip : (basisLaw4.map toFinThree).map Fin.val = basisLaw4 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S3_11.table (basisLaw4.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw5 : basisLaw5.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup := by
  have roundTrip : (basisLaw5.map toFinThree).map Fin.val = basisLaw5 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S3_11.table (basisLaw5.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw6 : basisLaw6.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup := by
  have roundTrip : (basisLaw6.map toFinThree).map Fin.val = basisLaw6 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S3_11.table (basisLaw6.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw7 : basisLaw7.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup := by
  have roundTrip : (basisLaw7.map toFinThree).map Fin.val = basisLaw7 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S3_11.table (basisLaw7.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw8 : basisLaw8.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup := by
  have roundTrip : (basisLaw8.map toFinThree).map Fin.val = basisLaw8 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S3_11.table (basisLaw8.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw9 : basisLaw9.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup := by
  have roundTrip : (basisLaw9.map toFinThree).map Fin.val = basisLaw9 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S3_11.table (basisLaw9.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem leftModelsLaw10 : basisLaw10.SatisfiedBy SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup := by
  have roundTrip : (basisLaw10.map toFinThree).map Fin.val = basisLaw10 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound SemigroupBasis.Generated.Catalogue.S3_11.table (basisLaw10.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem leftModels : Models SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact leftModelsLaw0
  · exact leftModelsLaw1
  · exact leftModelsLaw2
  · exact leftModelsLaw3
  · exact leftModelsLaw4
  · exact leftModelsLaw5
  · exact leftModelsLaw6
  · exact leftModelsLaw7
  · exact leftModelsLaw8
  · exact leftModelsLaw9
  · exact leftModelsLaw10

private def rightTable : FiniteTable where
  order := 4
  mul := fun a b => SemigroupBasis.Generated.Catalogue.S4_120.table.mul b a
  assoc := fun a b c => (SemigroupBasis.Generated.Catalogue.S4_120.table.assoc c b a).symm

private theorem rightModelsLaw0 : basisLaw0.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup.opposite := by
  have roundTrip : (basisLaw0.map toFinThree).map Fin.val = basisLaw0 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound rightTable (basisLaw0.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw1 : basisLaw1.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup.opposite := by
  have roundTrip : (basisLaw1.map toFinThree).map Fin.val = basisLaw1 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound rightTable (basisLaw1.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw2 : basisLaw2.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup.opposite := by
  have roundTrip : (basisLaw2.map toFinThree).map Fin.val = basisLaw2 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound rightTable (basisLaw2.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw3 : basisLaw3.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup.opposite := by
  have roundTrip : (basisLaw3.map toFinThree).map Fin.val = basisLaw3 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound rightTable (basisLaw3.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw4 : basisLaw4.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup.opposite := by
  have roundTrip : (basisLaw4.map toFinThree).map Fin.val = basisLaw4 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound rightTable (basisLaw4.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw5 : basisLaw5.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup.opposite := by
  have roundTrip : (basisLaw5.map toFinThree).map Fin.val = basisLaw5 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound rightTable (basisLaw5.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw6 : basisLaw6.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup.opposite := by
  have roundTrip : (basisLaw6.map toFinThree).map Fin.val = basisLaw6 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound rightTable (basisLaw6.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw7 : basisLaw7.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup.opposite := by
  have roundTrip : (basisLaw7.map toFinThree).map Fin.val = basisLaw7 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound rightTable (basisLaw7.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw8 : basisLaw8.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup.opposite := by
  have roundTrip : (basisLaw8.map toFinThree).map Fin.val = basisLaw8 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound rightTable (basisLaw8.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw9 : basisLaw9.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup.opposite := by
  have roundTrip : (basisLaw9.map toFinThree).map Fin.val = basisLaw9 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound rightTable (basisLaw9.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem rightModelsLaw10 : basisLaw10.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup.opposite := by
  have roundTrip : (basisLaw10.map toFinThree).map Fin.val = basisLaw10 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound rightTable (basisLaw10.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem rightModels : Models SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup.opposite basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rightModelsLaw0
  · exact rightModelsLaw1
  · exact rightModelsLaw2
  · exact rightModelsLaw3
  · exact rightModelsLaw4
  · exact rightModelsLaw5
  · exact rightModelsLaw6
  · exact rightModelsLaw7
  · exact rightModelsLaw8
  · exact rightModelsLaw9
  · exact rightModelsLaw10

namespace S6_11915

/-- Exact catalogue table SHA256 `945dc469432deb8daecd14ad638486ab62d705c52a4a9b853c5c06d5fe438231`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if a = 1 then (if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if a = 2 then (if b = 0 then (2 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if a = 3 then (if b = 0 then (3 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if a = 4 then (if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def ontoLeftMap (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (1 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (1 : Fin 3) else if a = 4 then (2 : Fin 3) else (2 : Fin 3)

def ontoLeftSection (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (4 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (a : Fin 6) : Fin 4 :=
  if a = 0 then (1 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (2 : Fin 4) else if a = 3 then (2 : Fin 4) else if a = 4 then (0 : Fin 4) else (3 : Fin 4)

def ontoRightSection (a : Fin 4) : Fin 6 :=
  if a = 0 then (4 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (2 : Fin 6) else (5 : Fin 6)

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup.opposite where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup.opposite where
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

def ontoRightOpposite : SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup.opposite.opposite where
  toFun := ontoRightMap
  map_mul := fun a b => ontoRight.map_mul b a
  preimage := ontoRightSection
  right_inverse := ontoRight.right_inverse

def pairOpposite : SubdirectPair table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup.opposite.opposite where
  left := ontoLeftOpposite
  right := ontoRightOpposite
  jointlyInjective := pair.jointlyInjective

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) :=
  models.oppositeReversed

end S6_11915

namespace S6_14689

/-- Exact catalogue table SHA256 `ba597459da19838c80b17f50423321024cec3fe858a292bd2a6ed1c83a57ea58`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if a = 1 then (if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if a = 3 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if a = 4 then (if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

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

private theorem modelsLaw3 : basisLaw3.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw3.map toFinThree).map Fin.val = basisLaw3 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw3.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem modelsLaw4 : basisLaw4.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw4.map toFinThree).map Fin.val = basisLaw4 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw4.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem modelsLaw5 : basisLaw5.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw5.map toFinThree).map Fin.val = basisLaw5 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw5.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem modelsLaw6 : basisLaw6.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw6.map toFinThree).map Fin.val = basisLaw6 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw6.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem modelsLaw7 : basisLaw7.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw7.map toFinThree).map Fin.val = basisLaw7 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw7.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem modelsLaw8 : basisLaw8.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw8.map toFinThree).map Fin.val = basisLaw8 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw8.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem modelsLaw9 : basisLaw9.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw9.map toFinThree).map Fin.val = basisLaw9 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw9.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem modelsLaw10 : basisLaw10.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw10.map toFinThree).map Fin.val = basisLaw10 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw10.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact modelsLaw0
  · exact modelsLaw1
  · exact modelsLaw2
  · exact modelsLaw3
  · exact modelsLaw4
  · exact modelsLaw5
  · exact modelsLaw6
  · exact modelsLaw7
  · exact modelsLaw8
  · exact modelsLaw9
  · exact modelsLaw10

def rootHom0Map (a : Fin 6) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (1 : Fin 6) else if a = 4 then (4 : Fin 6) else (5 : Fin 6)

def rootHom0 : Hom S6_11915.table.semigroup table.semigroup where
  toFun := rootHom0Map
  map_mul := by decide

def rootHom0Opposite : Hom S6_11915.table.semigroup.opposite table.semigroup.opposite where
  toFun := rootHom0.toFun
  map_mul := fun a b => rootHom0.map_mul b a

def rootHom1Map (a : Fin 6) : Fin 6 :=
  if a = 0 then (2 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6)

def rootHom1 : Hom S6_11915.table.semigroup table.semigroup where
  toFun := rootHom1Map
  map_mul := by decide

def rootHom1Opposite : Hom S6_11915.table.semigroup.opposite table.semigroup.opposite where
  toFun := rootHom1.toFun
  map_mul := fun a b => rootHom1.map_mul b a

def rootHomFamily (i : Fin 2) : Hom S6_11915.table.semigroup table.semigroup :=
  if i = 0 then rootHom0 else rootHom1

/-- Finite 2-coordinate root-to-leaf embedding. -/
def rootIntoPower : Embedding S6_11915.table.semigroup (table.semigroup.pi (Fin 2)) :=
  Embedding.ofSeparatingHoms rootHomFamily (by decide)

def rootHomFamilyOpposite (i : Fin 2) : Hom S6_11915.table.semigroup.opposite table.semigroup.opposite :=
  if i = 0 then rootHom0Opposite else rootHom1Opposite

/-- Finite 2-coordinate root-to-leaf embedding. -/
def rootOppositeIntoPower : Embedding S6_11915.table.semigroup.opposite (table.semigroup.opposite.pi (Fin 2)) :=
  Embedding.ofSeparatingHoms rootHomFamilyOpposite (by decide)

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) :=
  models.oppositeReversed

end S6_14689

namespace S6_14851

/-- Exact catalogue table SHA256 `92905656195cdc0506c7b16ae64fd7510fc5569b23a54b69ae1e086f4468d69b`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if a = 1 then (if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if a = 2 then (if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if a = 3 then (if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if a = 4 then (if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

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

private theorem modelsLaw3 : basisLaw3.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw3.map toFinThree).map Fin.val = basisLaw3 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw3.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem modelsLaw4 : basisLaw4.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw4.map toFinThree).map Fin.val = basisLaw4 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw4.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem modelsLaw5 : basisLaw5.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw5.map toFinThree).map Fin.val = basisLaw5 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw5.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem modelsLaw6 : basisLaw6.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw6.map toFinThree).map Fin.val = basisLaw6 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw6.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem modelsLaw7 : basisLaw7.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw7.map toFinThree).map Fin.val = basisLaw7 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw7.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem modelsLaw8 : basisLaw8.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw8.map toFinThree).map Fin.val = basisLaw8 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw8.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem modelsLaw9 : basisLaw9.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw9.map toFinThree).map Fin.val = basisLaw9 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw9.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

private theorem modelsLaw10 : basisLaw10.SatisfiedBy table.semigroup := by
  have roundTrip : (basisLaw10.map toFinThree).map Fin.val = basisLaw10 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound table (basisLaw10.map toFinThree) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact modelsLaw0
  · exact modelsLaw1
  · exact modelsLaw2
  · exact modelsLaw3
  · exact modelsLaw4
  · exact modelsLaw5
  · exact modelsLaw6
  · exact modelsLaw7
  · exact modelsLaw8
  · exact modelsLaw9
  · exact modelsLaw10

def rootHom0Map (a : Fin 6) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (1 : Fin 6) else if a = 4 then (4 : Fin 6) else (5 : Fin 6)

def rootHom0 : Hom S6_11915.table.semigroup table.semigroup where
  toFun := rootHom0Map
  map_mul := by decide

def rootHom0Opposite : Hom S6_11915.table.semigroup.opposite table.semigroup.opposite where
  toFun := rootHom0.toFun
  map_mul := fun a b => rootHom0.map_mul b a

def rootHom1Map (a : Fin 6) : Fin 6 :=
  if a = 0 then (2 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (4 : Fin 6) else (4 : Fin 6)

def rootHom1 : Hom S6_11915.table.semigroup table.semigroup where
  toFun := rootHom1Map
  map_mul := by decide

def rootHom1Opposite : Hom S6_11915.table.semigroup.opposite table.semigroup.opposite where
  toFun := rootHom1.toFun
  map_mul := fun a b => rootHom1.map_mul b a

def rootHomFamily (i : Fin 2) : Hom S6_11915.table.semigroup table.semigroup :=
  if i = 0 then rootHom0 else rootHom1

/-- Finite 2-coordinate root-to-leaf embedding. -/
def rootIntoPower : Embedding S6_11915.table.semigroup (table.semigroup.pi (Fin 2)) :=
  Embedding.ofSeparatingHoms rootHomFamily (by decide)

def rootHomFamilyOpposite (i : Fin 2) : Hom S6_11915.table.semigroup.opposite table.semigroup.opposite :=
  if i = 0 then rootHom0Opposite else rootHom1Opposite

/-- Finite 2-coordinate root-to-leaf embedding. -/
def rootOppositeIntoPower : Embedding S6_11915.table.semigroup.opposite (table.semigroup.opposite.pi (Fin 2)) :=
  Embedding.ofSeparatingHoms rootHomFamilyOpposite (by decide)

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) :=
  models.oppositeReversed

end S6_14851

namespace S6_14852

/-- Exact catalogue table SHA256 `e7c1ea37d0336d7281e6e3d9b548b944913d8028b75f65d264c06c8c1a64e3c9`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if a = 1 then (if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if a = 2 then (if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if a = 3 then (if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if a = 4 then (if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def ontoLeftMap (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (1 : Fin 3) else if a = 2 then (2 : Fin 3) else if a = 3 then (2 : Fin 3) else if a = 4 then (2 : Fin 3) else (2 : Fin 3)

def ontoLeftSection (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (2 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (a : Fin 6) : Fin 4 :=
  if a = 0 then (1 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else if a = 4 then (0 : Fin 4) else (3 : Fin 4)

def ontoRightSection (a : Fin 4) : Fin 6 :=
  if a = 0 then (4 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (3 : Fin 6) else (5 : Fin 6)

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup.opposite where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup.opposite where
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

def ontoRightOpposite : SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup.opposite.opposite where
  toFun := ontoRightMap
  map_mul := fun a b => ontoRight.map_mul b a
  preimage := ontoRightSection
  right_inverse := ontoRight.right_inverse

def pairOpposite : SubdirectPair table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S4_120.table.semigroup.opposite.opposite where
  left := ontoLeftOpposite
  right := ontoRightOpposite
  jointlyInjective := pair.jointlyInjective

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) :=
  models.oppositeReversed

end S6_14852

end SigmaF137c

end SemigroupBasis.CoRoots.Order6Sunday.LateFinite
