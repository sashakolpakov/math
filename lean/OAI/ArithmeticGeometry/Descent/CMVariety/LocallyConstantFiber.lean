import OAI.ArithmeticGeometry.Descent.CMVariety.SmoothDensity
import OAI.ArithmeticGeometry.Descent.CMVariety.AbelianFiber

/-! # Locally Constant Fiber -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.LocallyConstantFiber.Abelian

noncomputable section

/-! Local constancy of an actual arithmetic abelian fiber, combined with
dense number-field points, gives the exact number-field group model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Filter
open scoped _root_.Topology

theorem abelian_fiber_descends_of_local_group_isomorphisms
    {S : Scheme} (f : S ⟶ Spec (CommRingCat.of ℚ)) [Smooth f]
    {g : ℕ} (U : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (p : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ S)
    (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (hlocal : ∀ᶠ s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (ComplexParameter.Abelian.arithmeticComplexBase f)
      in 𝓝 (ComplexParameter.Abelian.arithmeticComplexPoint f p),
      ∃ e : (U.pullback (ChartDensity.Abelian.arithmeticPointProjection f s)).scheme ≅ A.toOver,
        IsMonHom e.hom) : AbelianFiber.HasNumberFieldModel A := by
  obtain ⟨s, hs, e, he⟩ := (SmoothDensity.Abelian.smooth_rational_scheme_numberField_points_dense f).inter_nhds_nonempty hlocal
  have : IsMonHom e.hom := he
  exact AbelianFiber.abelian_fiber_descends_of_parameter_descends U (ChartDensity.Abelian.arithmeticPointProjection f s) A e hs

end

end OAI.ArithmeticGeometry.Descent.CMVariety.LocallyConstantFiber.Abelian
