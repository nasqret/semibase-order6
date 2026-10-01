import SemigroupBasis.InjectiveMulSemigroup
import SemigroupBasis.TransferPower

namespace SemigroupBasis

/-- A finite term-function automaton presented by right multiplication with
generators.  The certificate stores one representative nonempty word for each
state and embeds the resulting multiplication into a direct power. -/
structure RightGeneratedPowerCertificate {U : Type u} {G : Type v}
    {I : Type w} {B : Type z} (target : Semigroup B) where
  stateVector : U -> I -> B
  generatorVector : G -> I -> B
  transition : U -> G -> U
  representativeHead : U -> G
  representativeTail : U -> List G
  injective : Function.Injective stateVector
  transition_map : forall state generator coordinate,
    stateVector (transition state generator) coordinate =
      target.mul (stateVector state coordinate)
        (generatorVector generator coordinate)
  representative_map : forall state coordinate,
    stateVector state coordinate =
      (representativeTail state).foldl
        (fun value generator =>
          target.mul value (generatorVector generator coordinate))
        (generatorVector (representativeHead state) coordinate)

namespace RightGeneratedPowerCertificate

/-- Follow a sequence of right-generator transitions from a state. -/
def rightMultiplyWord {U : Type u} {G : Type v} {I : Type w} {B : Type z}
    {target : Semigroup B}
    (certificate : RightGeneratedPowerCertificate (U := U) (G := G) (I := I) target)
    (state : U) (word : List G) : U :=
  word.foldl certificate.transition state

theorem stateVector_rightMultiplyWord
    {U : Type u} {G : Type v} {I : Type w} {B : Type z}
    {target : Semigroup B}
    (certificate : RightGeneratedPowerCertificate (U := U) (G := G) (I := I) target)
    (state : U) (word : List G) (coordinate : I) :
    certificate.stateVector
        (certificate.rightMultiplyWord state word) coordinate =
      word.foldl
        (fun value generator =>
          target.mul value (certificate.generatorVector generator coordinate))
        (certificate.stateVector state coordinate) := by
  induction word generalizing state with
  | nil => rfl
  | cons generator word ih =>
      change
        certificate.stateVector
            (certificate.rightMultiplyWord
              (certificate.transition state generator) word) coordinate =
          word.foldl
            (fun value nextGenerator =>
              target.mul value
                (certificate.generatorVector nextGenerator coordinate))
            (target.mul (certificate.stateVector state coordinate)
              (certificate.generatorVector generator coordinate))
      rw [ih]
      rw [certificate.transition_map]

private theorem foldl_generator_assoc
    {U : Type u} {G : Type v} {I : Type w} {B : Type z}
    {target : Semigroup B}
    (certificate : RightGeneratedPowerCertificate (U := U) (G := G) (I := I) target)
    (coordinate : I) (left right : B) (word : List G) :
    word.foldl
        (fun value generator =>
          target.mul value (certificate.generatorVector generator coordinate))
        (target.mul left right) =
      target.mul left
        (word.foldl
          (fun value generator =>
            target.mul value (certificate.generatorVector generator coordinate))
          right) := by
  induction word generalizing right with
  | nil => rfl
  | cons generator word ih =>
      simp only [List.foldl_cons]
      rw [target.assoc]
      exact ih (target.mul right
        (certificate.generatorVector generator coordinate))

/-- Multiplication obtained by appending a representative word for the right
state to a representative word for the left state. -/
def mul {U : Type u} {G : Type v} {I : Type w} {B : Type z}
    {target : Semigroup B}
    (certificate : RightGeneratedPowerCertificate (U := U) (G := G) (I := I) target)
    (left right : U) : U :=
  certificate.rightMultiplyWord
    (certificate.transition left (certificate.representativeHead right))
    (certificate.representativeTail right)

theorem stateVector_mul
    {U : Type u} {G : Type v} {I : Type w} {B : Type z}
    {target : Semigroup B}
    (certificate : RightGeneratedPowerCertificate (U := U) (G := G) (I := I) target)
    (left right : U) (coordinate : I) :
    certificate.stateVector (certificate.mul left right) coordinate =
      target.mul (certificate.stateVector left coordinate)
        (certificate.stateVector right coordinate) := by
  rw [mul, certificate.stateVector_rightMultiplyWord]
  rw [certificate.transition_map]
  rw [foldl_generator_assoc]
  exact congrArg (target.mul (certificate.stateVector left coordinate))
    (certificate.representative_map right coordinate).symm

/-- The multiplicative injective map into the target power. -/
def mulCertificate
    {U : Type u} {G : Type v} {I : Type w} {B : Type z}
    {target : Semigroup B}
    (certificate : RightGeneratedPowerCertificate (U := U) (G := G) (I := I) target) :
    InjectiveMulSemigroup certificate.mul (target.pi I) where
  toFun := certificate.stateVector
  injective := certificate.injective
  map_mul := by
    intro left right
    funext coordinate
    exact certificate.stateVector_mul left right coordinate

/-- The associative source semigroup induced by the term-function automaton. -/
def semigroup
    {U : Type u} {G : Type v} {I : Type w} {B : Type z}
    {target : Semigroup B}
    (certificate : RightGeneratedPowerCertificate (U := U) (G := G) (I := I) target) :
    Semigroup U :=
  certificate.mulCertificate.semigroup

@[simp]
theorem semigroup_mul
    {U : Type u} {G : Type v} {I : Type w} {B : Type z}
    {target : Semigroup B}
    (certificate : RightGeneratedPowerCertificate (U := U) (G := G) (I := I) target)
    (left right : U) :
    certificate.semigroup.mul left right = certificate.mul left right :=
  rfl

/-- The term-function states embed into the recorded target power. -/
def embedding
    {U : Type u} {G : Type v} {I : Type w} {B : Type z}
    {target : Semigroup B}
    (certificate : RightGeneratedPowerCertificate (U := U) (G := G) (I := I) target) :
    Embedding certificate.semigroup (target.pi I) :=
  certificate.mulCertificate.embedding

end RightGeneratedPowerCertificate

end SemigroupBasis
