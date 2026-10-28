import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularChartTangent
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalPointNormalDerivation

/-! # Intrinsic Parameter Differential -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicParameterDifferential.Constructions

noncomputable section

/-!
# DegreeTwo: divisor transversality in any native regular chart

Local algebraic smoothness of the divisor forces surjectivity of the
actual parameter differential in every prescribed regular affine chart.
-/

open scoped ContDiff _root_.Topology

variable {S : Type*} [CommRing S] [IsDomain S] [Algebra ℂ S] [Algebra.Smooth ℂ S]

/-- The actual local divisor parameter is transverse in any of the
manifold's regular affine charts. -/
theorem parameter_fderiv_surjective_in_regularChart (p b : S) (hp : p ≠ 0)
    [Algebra.Smooth ℂ (Localization.Away (Ideal.Quotient.mk (Ideal.span {p}) b))]
    {k : ℕ} (f : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (Fin k → ℂ))
    (hf : f ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas S k) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (hxf : x ∈ f.source)
    (hxp : x p = 0) (hxb : x b ≠ 0) :
    Function.Surjective (fderiv ℂ (fun z => f.symm z p) (f x)) := by
  let := x.toRingHom.toAlgebra
  obtain ⟨δ, hδ⟩ := LocalPointNormalDerivation.Constructions.exists_local_point_normal_derivation p b hp x hxp hxb
  obtain ⟨w, hw⟩ := RegularChartTangent.Constructions.exists_tangent_in_regular_chart f hf x hxf δ
  intro c
  refine ⟨c • w, ?_⟩
  rw [map_smul, hw p, hδ, smul_eq_mul, mul_one]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicParameterDifferential.Constructions
