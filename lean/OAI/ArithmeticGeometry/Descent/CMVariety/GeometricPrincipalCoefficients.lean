import OAI.ArithmeticGeometry.Descent.CMVariety.HypersurfaceGeometricCoefficients
import OAI.ArithmeticGeometry.Models.SpreadingOut.NoetherHypersurface

/-! # Geometric Principal Coefficients -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.GeometricPrincipalCoefficients.Abelian

noncomputable section

/-! Dense principal opens in geometrically integral affine schemes admit
geometrically integral coefficient models. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

open OAI.ArithmeticGeometry.Models.SpreadingOut.NoetherHypersurface.Construction

theorem geometrically_integral_affine_has_geometric_principal_model
    (R K A : Type) [CommRing R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] :
    ∃ (b : A), b ≠ 0 ∧ ∃ M : AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Models.Coefficients.CoefficientModel R K (Models.SpreadingOut.Affine.Construction.affineOver K (Localization.Away b)),
      GeometricallyConnected M.model.hom ∧ GeometricallyIrreducible M.model.hom := by
  have : IsDomain (K ⊗[K] A) := (Algebra.TensorProduct.lid K A).toMulEquiv.isDomain
  obtain ⟨n, p, d, b, hmonic, hdegree, hd, hb, hirr, ⟨e⟩⟩ :=
    Models.SpreadingOut.NoetherHypersurface.Construction.finiteType_domain_has_hypersurface_open K K A
  obtain ⟨M, hconn, hirred⟩ := HypersurfaceGeometricCoefficients.Abelian.monic_hypersurface_chart_has_geometric_model
    R K n p hmonic hdegree d hd hirr
  exact ⟨b, hb, M.transport (Models.SpreadingOut.Affine.Construction.affineOverIso e), hconn, hirred⟩

end

end OAI.ArithmeticGeometry.Descent.CMVariety.GeometricPrincipalCoefficients.Abelian
