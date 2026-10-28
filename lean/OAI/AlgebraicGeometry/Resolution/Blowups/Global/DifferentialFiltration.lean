import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialIdealSheaf
import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.UnitCriterion

/-! # Differential Filtration -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.DifferentialFiltration.Construction

noncomputable section

/-! Increasing global differential orders and terminal bound propagation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]

theorem smoothDifferentialIdealSheaf_monotone_order (J : X.IdealSheafData) :
    Monotone (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J) := by
  intro m n h U
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  exact Coefficient.UnitCriterion.Construction.iteratedRelativeDifferentialIdeal_monotone_order ℂ (J.ideal U) h

theorem smoothDifferentialIdealSheaf_top_of_le (J : X.IdealSheafData) {m n : ℕ}
    (hmn : m ≤ n) (h : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J m = ⊤) :
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n = ⊤ := by
  have hle := smoothDifferentialIdealSheaf_monotone_order f J hmn
  rw [h] at hle
  exact top_le_iff.mp hle

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.DifferentialFiltration.Construction
