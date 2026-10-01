import SemigroupBasis.FiniteTable

namespace SemigroupBasis.Generated.Catalogue

namespace S1_1

def mul (a b : Fin 1) : Fin 1 :=
  (0 : Fin 1)

def table : FiniteTable where
  order := 1
  mul := mul
  assoc := by decide

end S1_1

end SemigroupBasis.Generated.Catalogue
