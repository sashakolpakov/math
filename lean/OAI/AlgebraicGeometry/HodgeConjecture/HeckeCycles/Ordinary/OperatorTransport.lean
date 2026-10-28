import OAI.RepresentationTheory.Hecke.CubicRelation

/-! # Operator Transport -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.OperatorTransport.CM

noncomputable section

/-! Transport the native ordinary operators through a proved point
bijection. The three raw neighbor multisets retain their exact integer
multiplicities, and the Frobenius operator is the specified one. -/

variable {A B : Type} (e : A ≃ B)

def pointOperator (Z : B → B) (x : A) : A := e.symm (Z (e x))

def multisetOperator (Y : B → Multiset B) (x : A) : Multiset A := (Y (e x)).map e.symm

theorem rawNeighbors (q : ℕ) (X : A → A) (X' Z : B → B) (Y : B → Multiset B)
    (hX : ∀ x, e (X x) = X' (e x)) (i : Fin 3) (x : A) :
    (RepresentationTheory.Hecke.CubicRelation.ordinaryRawNeighbors q X (pointOperator e Z) (multisetOperator e Y) i x).map e =
      RepresentationTheory.Hecke.CubicRelation.ordinaryRawNeighbors q X' Z Y i (e x) := by
  fin_cases i <;>
    simp [RepresentationTheory.Hecke.CubicRelation.ordinaryRawNeighbors, pointOperator, multisetOperator,
      Multiset.map_nsmul, Multiset.map_map, hX]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.OperatorTransport.CM
