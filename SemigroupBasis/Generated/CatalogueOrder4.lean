import SemigroupBasis.FiniteTable

namespace SemigroupBasis.Generated.Catalogue

namespace S4_1

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_1

namespace S4_2

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (1 : Fin 4) else (0 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_2

namespace S4_3

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (1 : Fin 4) else (0 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_3

namespace S4_4

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (3 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (3 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (3 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (3 : Fin 4) else (0 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_4

namespace S4_5

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_5

namespace S4_6

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (1 : Fin 4) else (1 : Fin 4) else if a = 1 then if b = 0 then (1 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (1 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if b = 0 then (1 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_6

namespace S4_7

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if a = 1 then if b = 0 then (1 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (3 : Fin 4) else (2 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (1 : Fin 4) else (0 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_7

namespace S4_8

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_8

namespace S4_9

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (1 : Fin 4) else (1 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_9

namespace S4_10

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (1 : Fin 4) else (1 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_10

namespace S4_11

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (2 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_11

namespace S4_12

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (0 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (1 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_12

namespace S4_13

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_13

namespace S4_14

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_14

namespace S4_15

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_15

namespace S4_16

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (1 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_16

namespace S4_17

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_17

namespace S4_18

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_18

namespace S4_19

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_19

namespace S4_20

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (0 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_20

namespace S4_21

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_21

namespace S4_22

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (1 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_22

namespace S4_23

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_23

namespace S4_24

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_24

namespace S4_25

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (3 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (3 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (3 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_25

namespace S4_26

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (0 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_26

namespace S4_27

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (0 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_27

namespace S4_28

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (0 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_28

namespace S4_29

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (0 : Fin 4) else (3 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_29

namespace S4_30

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (1 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (1 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (1 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (1 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_30

namespace S4_31

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (1 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (1 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (1 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_31

namespace S4_32

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (1 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (1 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (1 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_32

namespace S4_33

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (1 : Fin 4) else (3 : Fin 4) else if a = 1 then if b = 0 then (1 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (3 : Fin 4) else if a = 2 then if b = 0 then (1 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (3 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_33

namespace S4_34

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (1 : Fin 4) else (0 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_34

namespace S4_35

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (1 : Fin 4) else (0 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (1 : Fin 4) else (1 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_35

namespace S4_36

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (1 : Fin 4) else (1 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (1 : Fin 4) else (1 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_36

namespace S4_37

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if a = 1 then if b = 0 then (1 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (3 : Fin 4) else (2 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (1 : Fin 4) else (0 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_37

namespace S4_38

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (1 : Fin 4) else (0 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_38

namespace S4_39

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (1 : Fin 4) else (0 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_39

namespace S4_40

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (1 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_40

namespace S4_41

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (3 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (3 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (1 : Fin 4) else (3 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_41

namespace S4_42

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_42

namespace S4_43

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (3 : Fin 4) else (2 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_43

namespace S4_44

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_44

namespace S4_45

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (3 : Fin 4) else (2 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_45

namespace S4_46

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_46

namespace S4_47

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (1 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_47

namespace S4_48

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (1 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (3 : Fin 4) else (2 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_48

namespace S4_49

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (3 : Fin 4) else (2 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_49

namespace S4_50

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (1 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (1 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (3 : Fin 4) else (2 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_50

namespace S4_51

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4) else if a = 1 then if b = 0 then (1 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (1 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if b = 0 then (1 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (3 : Fin 4) else (2 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_51

namespace S4_52

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4) else if a = 1 then if b = 0 then (1 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (1 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (3 : Fin 4) else (2 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_52

namespace S4_53

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (0 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_53

namespace S4_54

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (0 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (0 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_54

namespace S4_55

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (0 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_55

namespace S4_56

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_56

namespace S4_57

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_57

namespace S4_58

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_58

namespace S4_59

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_59

namespace S4_60

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (0 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_60

namespace S4_61

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_61

namespace S4_62

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_62

namespace S4_63

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_63

namespace S4_64

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_64

namespace S4_65

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_65

namespace S4_66

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_66

namespace S4_67

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (0 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (0 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_67

namespace S4_68

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_68

namespace S4_69

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (0 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_69

namespace S4_70

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (1 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_70

namespace S4_71

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_71

namespace S4_72

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_72

namespace S4_73

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_73

namespace S4_74

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (0 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_74

namespace S4_75

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_75

namespace S4_76

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_76

namespace S4_77

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (2 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_77

namespace S4_78

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (1 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_78

namespace S4_79

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (1 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_79

namespace S4_80

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (3 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (3 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_80

namespace S4_81

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (3 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (3 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_81

namespace S4_82

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (3 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (3 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_82

namespace S4_83

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (3 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (1 : Fin 4) else (3 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_83

namespace S4_84

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_84

namespace S4_85

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_85

namespace S4_86

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_86

namespace S4_87

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_87

namespace S4_88

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (1 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (1 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (0 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (0 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_88

namespace S4_89

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (1 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (1 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_89

namespace S4_90

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (1 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (1 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_90

namespace S4_91

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (0 : Fin 4) else (3 : Fin 4) else if a = 1 then if b = 0 then (1 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (1 : Fin 4) else (3 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_91

namespace S4_92

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if a = 1 then if b = 0 then (1 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_92

namespace S4_93

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if a = 1 then if b = 0 then (1 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_93

namespace S4_94

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if a = 1 then if b = 0 then (1 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_94

namespace S4_95

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if a = 1 then if b = 0 then (1 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_95

namespace S4_96

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if a = 1 then if b = 0 then (1 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_96

namespace S4_97

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (3 : Fin 4) else (0 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (0 : Fin 4) else (2 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_97

namespace S4_98

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (0 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_98

namespace S4_99

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (0 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_99

namespace S4_100

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_100

namespace S4_101

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_101

namespace S4_102

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_102

namespace S4_103

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_103

namespace S4_104

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_104

namespace S4_105

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_105

namespace S4_106

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (0 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_106

namespace S4_107

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_107

namespace S4_108

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (0 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_108

namespace S4_109

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (2 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_109

namespace S4_110

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (0 : Fin 4) else (3 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (0 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_110

namespace S4_111

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (0 : Fin 4) else (3 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_111

namespace S4_112

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (1 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (1 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (1 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_112

namespace S4_113

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (1 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (1 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_113

namespace S4_114

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (1 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_114

namespace S4_115

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (1 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_115

namespace S4_116

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (1 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_116

namespace S4_117

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (1 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_117

namespace S4_118

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (1 : Fin 4) else (3 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_118

namespace S4_119

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (1 : Fin 4) else (3 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_119

namespace S4_120

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_120

namespace S4_121

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_121

namespace S4_122

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (1 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (1 : Fin 4) else (1 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_122

namespace S4_123

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if a = 1 then if b = 0 then (1 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if b = 0 then (1 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (3 : Fin 4) else (3 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_123

namespace S4_124

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if a = 2 then if b = 0 then (0 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (3 : Fin 4) else (1 : Fin 4) else if b = 0 then (0 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (1 : Fin 4) else (2 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_124

namespace S4_125

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (3 : Fin 4) else (0 : Fin 4) else if b = 0 then (3 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (0 : Fin 4) else (2 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_125

namespace S4_126

def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if a = 1 then if b = 0 then (1 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (1 : Fin 4) else (1 : Fin 4) else if b = 0 then (2 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (1 : Fin 4) else (1 : Fin 4)

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

end S4_126

end SemigroupBasis.Generated.Catalogue
