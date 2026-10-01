import SemigroupBasis.FiniteTable

namespace SemigroupBasis.Generated.Catalogue

namespace S3_1

def mul (a b : Fin 3) : Fin 3 :=
  if a = 0 then if b = 0 then (0 : Fin 3) else if b = 1 then (0 : Fin 3) else (0 : Fin 3) else if a = 1 then if b = 0 then (0 : Fin 3) else if b = 1 then (0 : Fin 3) else (0 : Fin 3) else if b = 0 then (0 : Fin 3) else if b = 1 then (0 : Fin 3) else (0 : Fin 3)

def table : FiniteTable where
  order := 3
  mul := mul
  assoc := by decide

end S3_1

namespace S3_2

def mul (a b : Fin 3) : Fin 3 :=
  if a = 0 then if b = 0 then (0 : Fin 3) else if b = 1 then (0 : Fin 3) else (2 : Fin 3) else if a = 1 then if b = 0 then (0 : Fin 3) else if b = 1 then (0 : Fin 3) else (2 : Fin 3) else if b = 0 then (2 : Fin 3) else if b = 1 then (2 : Fin 3) else (0 : Fin 3)

def table : FiniteTable where
  order := 3
  mul := mul
  assoc := by decide

end S3_2

namespace S3_3

def mul (a b : Fin 3) : Fin 3 :=
  if a = 0 then if b = 0 then (0 : Fin 3) else if b = 1 then (1 : Fin 3) else (1 : Fin 3) else if a = 1 then if b = 0 then (1 : Fin 3) else if b = 1 then (0 : Fin 3) else (0 : Fin 3) else if b = 0 then (1 : Fin 3) else if b = 1 then (0 : Fin 3) else (0 : Fin 3)

def table : FiniteTable where
  order := 3
  mul := mul
  assoc := by decide

end S3_3

namespace S3_4

def mul (a b : Fin 3) : Fin 3 :=
  if a = 0 then if b = 0 then (0 : Fin 3) else if b = 1 then (0 : Fin 3) else (0 : Fin 3) else if a = 1 then if b = 0 then (0 : Fin 3) else if b = 1 then (0 : Fin 3) else (0 : Fin 3) else if b = 0 then (0 : Fin 3) else if b = 1 then (0 : Fin 3) else (1 : Fin 3)

def table : FiniteTable where
  order := 3
  mul := mul
  assoc := by decide

end S3_4

namespace S3_5

def mul (a b : Fin 3) : Fin 3 :=
  if a = 0 then if b = 0 then (0 : Fin 3) else if b = 1 then (0 : Fin 3) else (0 : Fin 3) else if a = 1 then if b = 0 then (0 : Fin 3) else if b = 1 then (0 : Fin 3) else (0 : Fin 3) else if b = 0 then (0 : Fin 3) else if b = 1 then (0 : Fin 3) else (2 : Fin 3)

def table : FiniteTable where
  order := 3
  mul := mul
  assoc := by decide

end S3_5

namespace S3_6

def mul (a b : Fin 3) : Fin 3 :=
  if a = 0 then if b = 0 then (0 : Fin 3) else if b = 1 then (0 : Fin 3) else (0 : Fin 3) else if a = 1 then if b = 0 then (0 : Fin 3) else if b = 1 then (0 : Fin 3) else (0 : Fin 3) else if b = 0 then (0 : Fin 3) else if b = 1 then (1 : Fin 3) else (2 : Fin 3)

def table : FiniteTable where
  order := 3
  mul := mul
  assoc := by decide

end S3_6

namespace S3_7

def mul (a b : Fin 3) : Fin 3 :=
  if a = 0 then if b = 0 then (0 : Fin 3) else if b = 1 then (0 : Fin 3) else (0 : Fin 3) else if a = 1 then if b = 0 then (0 : Fin 3) else if b = 1 then (0 : Fin 3) else (0 : Fin 3) else if b = 0 then (2 : Fin 3) else if b = 1 then (2 : Fin 3) else (2 : Fin 3)

def table : FiniteTable where
  order := 3
  mul := mul
  assoc := by decide

end S3_7

namespace S3_8

def mul (a b : Fin 3) : Fin 3 :=
  if a = 0 then if b = 0 then (0 : Fin 3) else if b = 1 then (0 : Fin 3) else (0 : Fin 3) else if a = 1 then if b = 0 then (0 : Fin 3) else if b = 1 then (0 : Fin 3) else (1 : Fin 3) else if b = 0 then (0 : Fin 3) else if b = 1 then (1 : Fin 3) else (2 : Fin 3)

def table : FiniteTable where
  order := 3
  mul := mul
  assoc := by decide

end S3_8

namespace S3_9

def mul (a b : Fin 3) : Fin 3 :=
  if a = 0 then if b = 0 then (0 : Fin 3) else if b = 1 then (0 : Fin 3) else (2 : Fin 3) else if a = 1 then if b = 0 then (0 : Fin 3) else if b = 1 then (0 : Fin 3) else (2 : Fin 3) else if b = 0 then (2 : Fin 3) else if b = 1 then (2 : Fin 3) else (2 : Fin 3)

def table : FiniteTable where
  order := 3
  mul := mul
  assoc := by decide

end S3_9

namespace S3_10

def mul (a b : Fin 3) : Fin 3 :=
  if a = 0 then if b = 0 then (0 : Fin 3) else if b = 1 then (1 : Fin 3) else (0 : Fin 3) else if a = 1 then if b = 0 then (1 : Fin 3) else if b = 1 then (0 : Fin 3) else (1 : Fin 3) else if b = 0 then (0 : Fin 3) else if b = 1 then (1 : Fin 3) else (2 : Fin 3)

def table : FiniteTable where
  order := 3
  mul := mul
  assoc := by decide

end S3_10

namespace S3_11

def mul (a b : Fin 3) : Fin 3 :=
  if a = 0 then if b = 0 then (0 : Fin 3) else if b = 1 then (1 : Fin 3) else (2 : Fin 3) else if a = 1 then if b = 0 then (1 : Fin 3) else if b = 1 then (0 : Fin 3) else (2 : Fin 3) else if b = 0 then (2 : Fin 3) else if b = 1 then (2 : Fin 3) else (2 : Fin 3)

def table : FiniteTable where
  order := 3
  mul := mul
  assoc := by decide

end S3_11

namespace S3_12

def mul (a b : Fin 3) : Fin 3 :=
  if a = 0 then if b = 0 then (0 : Fin 3) else if b = 1 then (0 : Fin 3) else (0 : Fin 3) else if a = 1 then if b = 0 then (0 : Fin 3) else if b = 1 then (1 : Fin 3) else (0 : Fin 3) else if b = 0 then (0 : Fin 3) else if b = 1 then (0 : Fin 3) else (2 : Fin 3)

def table : FiniteTable where
  order := 3
  mul := mul
  assoc := by decide

end S3_12

namespace S3_13

def mul (a b : Fin 3) : Fin 3 :=
  if a = 0 then if b = 0 then (0 : Fin 3) else if b = 1 then (0 : Fin 3) else (0 : Fin 3) else if a = 1 then if b = 0 then (0 : Fin 3) else if b = 1 then (1 : Fin 3) else (0 : Fin 3) else if b = 0 then (2 : Fin 3) else if b = 1 then (2 : Fin 3) else (2 : Fin 3)

def table : FiniteTable where
  order := 3
  mul := mul
  assoc := by decide

end S3_13

namespace S3_14

def mul (a b : Fin 3) : Fin 3 :=
  if a = 0 then if b = 0 then (0 : Fin 3) else if b = 1 then (0 : Fin 3) else (0 : Fin 3) else if a = 1 then if b = 0 then (0 : Fin 3) else if b = 1 then (1 : Fin 3) else (1 : Fin 3) else if b = 0 then (0 : Fin 3) else if b = 1 then (1 : Fin 3) else (2 : Fin 3)

def table : FiniteTable where
  order := 3
  mul := mul
  assoc := by decide

end S3_14

namespace S3_15

def mul (a b : Fin 3) : Fin 3 :=
  if a = 0 then if b = 0 then (0 : Fin 3) else if b = 1 then (0 : Fin 3) else (0 : Fin 3) else if a = 1 then if b = 0 then (0 : Fin 3) else if b = 1 then (1 : Fin 3) else (1 : Fin 3) else if b = 0 then (0 : Fin 3) else if b = 1 then (2 : Fin 3) else (2 : Fin 3)

def table : FiniteTable where
  order := 3
  mul := mul
  assoc := by decide

end S3_15

namespace S3_16

def mul (a b : Fin 3) : Fin 3 :=
  if a = 0 then if b = 0 then (0 : Fin 3) else if b = 1 then (0 : Fin 3) else (0 : Fin 3) else if a = 1 then if b = 0 then (0 : Fin 3) else if b = 1 then (1 : Fin 3) else (2 : Fin 3) else if b = 0 then (2 : Fin 3) else if b = 1 then (2 : Fin 3) else (2 : Fin 3)

def table : FiniteTable where
  order := 3
  mul := mul
  assoc := by decide

end S3_16

namespace S3_17

def mul (a b : Fin 3) : Fin 3 :=
  if a = 0 then if b = 0 then (0 : Fin 3) else if b = 1 then (0 : Fin 3) else (0 : Fin 3) else if a = 1 then if b = 0 then (1 : Fin 3) else if b = 1 then (1 : Fin 3) else (1 : Fin 3) else if b = 0 then (2 : Fin 3) else if b = 1 then (2 : Fin 3) else (2 : Fin 3)

def table : FiniteTable where
  order := 3
  mul := mul
  assoc := by decide

end S3_17

namespace S3_18

def mul (a b : Fin 3) : Fin 3 :=
  if a = 0 then if b = 0 then (0 : Fin 3) else if b = 1 then (1 : Fin 3) else (2 : Fin 3) else if a = 1 then if b = 0 then (1 : Fin 3) else if b = 1 then (2 : Fin 3) else (0 : Fin 3) else if b = 0 then (2 : Fin 3) else if b = 1 then (0 : Fin 3) else (1 : Fin 3)

def table : FiniteTable where
  order := 3
  mul := mul
  assoc := by decide

end S3_18

end SemigroupBasis.Generated.Catalogue
