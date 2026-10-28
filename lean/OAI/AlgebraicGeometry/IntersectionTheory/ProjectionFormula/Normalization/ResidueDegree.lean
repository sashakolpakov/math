import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Charts
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ResidueDegree

/-! # Residue Degree -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.ResidueDegree

noncomputable section

/-! Every branch of the actual finite normalization has a positive
native residue-field degree. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Charts

theorem positive {k : Type} [Field k] [CharZero k] (X : Scheme) [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (y : Normalization.Scheme.normalization X) :
    0 < (Normalization.Scheme.normalizationMap X).residueDegree y := by
  obtain ⟨U, hU, hxU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (Opens.mem_top (Normalization.Scheme.normalizationMap X y))
  let : Nonempty U := ⟨⟨Normalization.Scheme.normalizationMap X y, hxU⟩⟩
  let A := Γ(X, U)
  let B := integralClosure A X.functionField
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let := Foundations.Scheme.AffineSectionFiniteType.specSectionScalarAlgebra_finiteType f U hU
  let := functionField_isFractionRing_of_isAffineOpen X U hU
  let : Module.Finite A B := ProjectionFormula.Finite.Normalization.finite_integralClosure k A X.functionField
  have hr : y ∈ Set.range (Charts.normalizationChartMap X U hU) := by
    rw [Charts.normalizationChartMap_range]
    exact hxU
  obtain ⟨q, hq⟩ := hr
  rw [← hq, ← Support.Map.residueDegree_pre_immersion (Charts.normalizationChartMap X U hU)
      (Normalization.Scheme.normalizationMap X) q, Charts.normalizationChartMap_comp,
    Support.Map.residueDegree_post_immersion, Affine.ResidueDegree.residueDegree_eq_inertiaDeg]
  exact q.asIdeal.inertiaDeg_pos A

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.ResidueDegree
