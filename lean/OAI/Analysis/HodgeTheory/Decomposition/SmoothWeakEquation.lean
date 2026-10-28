import OAI.Analysis.HodgeTheory.Decomposition.EnergyLocalizationPair
import OAI.Analysis.HodgeTheory.Decomposition.WeakEquation

/-! # Smooth Weak Equation -/

namespace OAI.Analysis.HodgeTheory.Decomposition.SmoothWeakEquation.Constructions

noncomputable section

/-! On genuine smooth forms, the completed weak equation is equivalent to
the classical Hodge Laplacian equation. -/

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] (n : ℕ)

theorem projectiveEnergyDerivative_smooth_laplacian_pair
    (a b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :
    inner ℂ (EnergyDomain.Constructions.projectiveEnergyDerivative V n (SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n a))
      (EnergyDomain.Constructions.projectiveEnergyDerivative V n (SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n b)) =
        Form.Constructions.projectiveL2Pair V (n + 1) (AdjointAlgebra.Constructions.projectivePositiveLaplacian V n a) b := by
  rw [EnergyLocalizationPair.Constructions.projectiveEnergyDerivative_smooth_pair, AdjointAlgebra.Constructions.projectivePositiveLaplacian_pair, add_comm]

theorem projective_smooth_weak_equation_iff
    (a f : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :
    WeakEquation.Constructions.IsProjectiveWeakHodgeSolution V n (SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n a)
      (Form.Constructions.smoothToProjectiveL2 V (n + 1) f) ↔ AdjointAlgebra.Constructions.projectivePositiveLaplacian V n a = f := by
  constructor
  · intro h
    apply AdjointAlgebra.Constructions.projectiveL2Pair_separates_left V (n + 1)
    intro b
    have hb := h (SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n b)
    rw [projectiveEnergyDerivative_smooth_laplacian_pair,
      SmoothEnergyInclusion.Constructions.projectiveEnergyInclusion_on_smooth, Form.Constructions.smoothToProjectiveL2_inner] at hb
    exact hb
  · intro h v
    have hclosed : IsClosed {w : EnergyDomain.Constructions.ProjectiveEnergyDomain V n |
        inner ℂ (EnergyDomain.Constructions.projectiveEnergyDerivative V n (SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n a))
          (EnergyDomain.Constructions.projectiveEnergyDerivative V n w) =
            inner ℂ (Form.Constructions.smoothToProjectiveL2 V (n + 1) f) (EnergyDomain.Constructions.projectiveEnergyInclusion V n w)} :=
      isClosed_eq (continuous_const.inner (EnergyDomain.Constructions.projectiveEnergyDerivative V n).continuous)
        (continuous_const.inner (EnergyDomain.Constructions.projectiveEnergyInclusion V n).continuous)
    refine (SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy_dense V n).induction_on v hclosed (fun b => ?_)
    change inner ℂ (EnergyDomain.Constructions.projectiveEnergyDerivative V n (SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n a))
      (EnergyDomain.Constructions.projectiveEnergyDerivative V n (SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n b)) = _
    rw [projectiveEnergyDerivative_smooth_laplacian_pair, h,
      SmoothEnergyInclusion.Constructions.projectiveEnergyInclusion_on_smooth, Form.Constructions.smoothToProjectiveL2_inner]

end

end OAI.Analysis.HodgeTheory.Decomposition.SmoothWeakEquation.Constructions
