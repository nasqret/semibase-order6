import SemigroupBasis.FiniteTable

namespace SemigroupBasis.Generated.Catalogue

namespace S2_1

def mul (a b : Fin 2) : Fin 2 :=
  if a = 0 then if b = 0 then (0 : Fin 2) else (0 : Fin 2) else if b = 0 then (0 : Fin 2) else (0 : Fin 2)

def table : FiniteTable where
  order := 2
  mul := mul
  assoc := by decide

end S2_1

namespace S2_2

def mul (a b : Fin 2) : Fin 2 :=
  if a = 0 then if b = 0 then (0 : Fin 2) else (1 : Fin 2) else if b = 0 then (1 : Fin 2) else (0 : Fin 2)

def table : FiniteTable where
  order := 2
  mul := mul
  assoc := by decide

end S2_2

namespace S2_3

def mul (a b : Fin 2) : Fin 2 :=
  if a = 0 then if b = 0 then (0 : Fin 2) else (0 : Fin 2) else if b = 0 then (0 : Fin 2) else (1 : Fin 2)

def table : FiniteTable where
  order := 2
  mul := mul
  assoc := by decide

end S2_3

namespace S2_4

def mul (a b : Fin 2) : Fin 2 :=
  if a = 0 then if b = 0 then (0 : Fin 2) else (0 : Fin 2) else if b = 0 then (1 : Fin 2) else (1 : Fin 2)

def table : FiniteTable where
  order := 2
  mul := mul
  assoc := by decide

end S2_4

end SemigroupBasis.Generated.Catalogue
