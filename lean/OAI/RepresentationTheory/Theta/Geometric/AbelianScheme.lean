import OAI.RepresentationTheory.Theta.Geometric.Torus.AbelianModel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes
import OAI.ArithmeticGeometry.Models.SpreadingOut.GeometricFieldComponents

/-! # Abelian Scheme -/

namespace OAI.RepresentationTheory.Theta.Geometric.AbelianScheme

noncomputable section

/-! The actual abelian model is an abelian scheme over the complex point.
Its relative dimension is determined by the derivative of the period
comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

/-- The native smooth relative dimension and geometric connectedness give
the abelian-scheme structure without replacing its scheme or group law. -/
def abelianSchemeOfVariety (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom) AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase where
  scheme := A.toOver
  group := A.group
  commutative := A.commutative
  proper := A.variety.presentation.projective.isProper
  smoothDimension := AlgebraicGeometry.Betti.SmoothDimension.Realization.smoothOfFunctionFieldDimension A.toOver.hom
  connected := ArithmeticGeometry.Models.SpreadingOut.GeometricFieldComponents.Construction.integral_geometricallyConnected_over_algClosed A.toOver.hom

theorem abelian_model_dimension (Φ : Torus.Data.CM.ProjectivePeriodData)
    (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.space),
      𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom) → ℂ)⟯
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) :
    AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom = Module.finrank ℂ Φ.space := by
  let d := (e.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv
    (x := (0 : Φ.periodTorus)) (by trivial)
  have h := d.toLinearEquiv.finrank_eq
  change Module.finrank ℂ Φ.space = Module.finrank ℂ (Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom) → ℂ) at h
  exact (Module.finrank_fin_fun ℂ).symm.trans h.symm

end

end OAI.RepresentationTheory.Theta.Geometric.AbelianScheme
