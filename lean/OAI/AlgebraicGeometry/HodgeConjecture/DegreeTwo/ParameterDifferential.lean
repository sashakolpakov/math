import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmoothChartTangent
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalDerivation

/-! # Parameter Differential -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ParameterDifferential.Constructions

noncomputable section

/-!
# DegreeTwo: a smooth principal divisor has a surjective analytic differential

The actual regular parameter admits a normalized algebraic point derivation.
Realizing that derivation in a native analytic chart proves surjectivity of
the parameter's actual complex Fréchet derivative.
-/

open scoped ContDiff _root_.Topology

variable {S : Type*} [CommRing S] [IsDomain S] [Algebra ℂ S] [Algebra.Smooth ℂ S]

/-- The defining function of a smooth principal hypersurface has an actual
surjective complex derivative in a smooth affine point chart. -/
theorem exists_parameter_submersion_chart (p : S) (hp : p ≠ 0)
    [Algebra.FormallySmooth ℂ (S ⧸ Ideal.span {p})]
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (hxp : x p = 0) :
    ∃ (g : S) (n m : ℕ)
      (P : Algebra.SubmersivePresentation ℂ (Localization.Away g) (Fin n) (Fin m))
      (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ)),
      x ∈ e.source ∧
      (∀ a : S, ContDiffOn ℂ ω (fun z => e.symm z a) e.target) ∧
      Function.Surjective (fderiv ℂ (fun z => e.symm z p) (e x)) := by
  let := x.toRingHom.toAlgebra
  obtain ⟨δ, hδ⟩ := NormalDerivation.Constructions.exists_point_normal_derivation ℂ S ℂ p hp hxp
  obtain ⟨g, n, m, P, e, v, hx, hi, hv⟩ :=
    SmoothChartTangent.Constructions.exists_smoothAffine_chart_realizing_derivation x δ
  refine ⟨g, n, m, P, e, hx, hi, ?_⟩
  intro c
  refine ⟨c • v, ?_⟩
  rw [map_smul, hv p, hδ, smul_eq_mul, mul_one]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ParameterDifferential.Constructions
