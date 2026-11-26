import FormalConjectures.OEIS.«1818»

namespace OMA.R_OeisA1818_a_2_R1

def H1 : Prop := (2 : ℕ) = 2

def H2 : Prop := OeisA1818.a 2 = 9

theorem main : H1 → H2 → type_of% @OeisA1818.a_2 := by
  intro _ h
  exact h

end OMA.R_OeisA1818_a_2_R1
