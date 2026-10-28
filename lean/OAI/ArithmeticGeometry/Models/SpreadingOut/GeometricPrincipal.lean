import OAI.ArithmeticGeometry.Models.SpreadingOut.HypersurfaceGeometric
import OAI.ArithmeticGeometry.Models.SpreadingOut.NoetherHypersurface

/-! # Geometric Principal -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.GeometricPrincipal.Construction

noncomputable section

/-! Dense principal opens in geometrically integral affine schemes admit
geometrically integral coefficient models. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

theorem geometrically_integral_affine_has_geometric_principal_model
    (K A : Type u) [Field K] [NumberField K]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A]
    [IsDomain (AlgebraicClosure K ⊗[K] A)] :
    ∃ (b : A), b ≠ 0 ∧ ∃ M : Foundations.Constructions.CoefficientModel K (Affine.Construction.affineOver K (Localization.Away b)),
      GeometricallyConnected M.model.hom ∧ GeometricallyIrreducible M.model.hom := by
  obtain ⟨n, p, d, b, hmonic, hdegree, hd, hb, hirr, ⟨e⟩⟩ :=
    NoetherHypersurface.Construction.finiteType_domain_has_hypersurface_open K (AlgebraicClosure K) A
  obtain ⟨M, hconn, hirred⟩ := HypersurfaceGeometric.Construction.monic_hypersurface_chart_has_geometric_model
    K n p hmonic hdegree d hd hirr
  exact ⟨b, hb, M.transport (Affine.Construction.affineOverIso e), hconn, hirred⟩

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.GeometricPrincipal.Construction
