import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.FactorSquares

/-! # Point Presentation Factors -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting

noncomputable section

/-! An equality of ambient presentations gives the literal all-test
factor criterion without rebuilding the predicate at a concrete PEL point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Intrinsic.Neighbors.KernelPresentation.point_factor_iff {S : Scheme} {A : Over S}
    (P Q : Intrinsic.Neighbors.KernelPresentation A) (h : P = Q) (T : Over S) (a : T ⟶ A) :
    (∃ z : T ⟶ P.carrier, z ≫ P.inclusion = a) ↔
      ∃ z : T ⟶ Q.carrier, z ≫ Q.inclusion = a :=
  Iff.of_eq (congrArg (fun K : Intrinsic.Neighbors.KernelPresentation A =>
    ∃ z : T ⟶ K.carrier, z ≫ K.inclusion = a) h)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting
