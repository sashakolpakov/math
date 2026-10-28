import OAI.RepresentationTheory.Hecke.CubicRelation

/-! # Counts -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Counts.CM.OrdinaryRaw

/-! Package the three explicit native reduction counts as one raw
neighbor-multiset identity, retaining the integer multiplicities. -/

variable {O S : Type} (q : ℕ) (X Z : O → O) (Y : O → Multiset O)
  (v : O → S) (x : O) (red : Fin 3 → Multiset S)

theorem rawNeighbors
    (h₀ : red 0 = {v (X x)} + q • ((Y x).map v))
    (h₁ : red 1 = (Y (X x)).map v + q ^ 2 • ({v (Z x)} : Multiset S))
    (h₂ : red 2 = {v (Z (X x))}) (i : Fin 3) :
    red i = (RepresentationTheory.Hecke.CubicRelation.ordinaryRawNeighbors q X Z Y i x).map v := by
  fin_cases i
  · simpa [RepresentationTheory.Hecke.CubicRelation.ordinaryRawNeighbors, Multiset.map_nsmul] using h₀
  · simpa [RepresentationTheory.Hecke.CubicRelation.ordinaryRawNeighbors, Multiset.map_nsmul] using h₁
  · simpa [RepresentationTheory.Hecke.CubicRelation.ordinaryRawNeighbors] using h₂

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Counts.CM.OrdinaryRaw
