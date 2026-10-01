import SemigroupBasis.CoRoots.Order6Day15.B33.B33Moves

namespace SemigroupBasis.CoRoots.Order6Day15.B33

/-- Literal catalogue orientation, rows 111111/111111/111331/121456/121546/666666. -/
def mul6225 (a b : Fin 6) : Fin 6 :=
  match a.val with
  | 0 => 0
  | 1 => 0
  | 2 => if b = 3 ∨ b = 4 then 2 else 0
  | 3 => if b = 2 then 0 else b
  | 4 => if b = 2 then 0 else if b = 3 then 4 else if b = 4 then 3 else b
  | _ => 5

/-- Literal catalogue orientation, rows 111111/111111/123455/124355/555555/556655. -/
def mul9878 (a b : Fin 6) : Fin 6 :=
  match a.val with
  | 0 => 0
  | 1 => 0
  | 2 => if b = 5 then 4 else b
  | 3 => if b = 5 then 4 else if b = 2 then 3 else if b = 3 then 2 else b
  | 4 => 4
  | _ => if b = 2 ∨ b = 3 then 5 else 4

def table6225 : FiniteTable := ⟨6,mul6225,by decide⟩
def table9878 : FiniteTable := ⟨6,mul9878,by decide⟩

end SemigroupBasis.CoRoots.Order6Day15.B33
