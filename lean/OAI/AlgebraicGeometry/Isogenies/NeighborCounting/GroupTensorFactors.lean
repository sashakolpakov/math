import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.FactorSquares

/-! # Group Tensor Factors -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupTensorFactors

noncomputable section

/-! The two underlying presentations of a product of group objects
give the same ambient factor criterion, proved before concrete groups are substituted. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

theorem tensor_carrier_factor_iff {S : Scheme} (M N : Grp (Over S)) {A : Over S}
    (i : (M ⊗ N).X ⟶ A) (T : Over S) (a : T ⟶ A) :
    (∃ h : T ⟶ M.X ⊗ N.X, h ≫ i = a) ↔
      ∃ h : T ⟶ (M ⊗ N).X, h ≫ i = a := Iff.rfl

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupTensorFactors
