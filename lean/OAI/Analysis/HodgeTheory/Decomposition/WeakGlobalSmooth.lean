import OAI.Analysis.HodgeTheory.Decomposition.WeakSmoothCutoffNeighborhood
import OAI.Analysis.HodgeTheory.Decomposition.SmoothGlobal

/-! # Weak Global Smooth -/

namespace OAI.Analysis.HodgeTheory.Decomposition.WeakGlobalSmooth.Constructions

noncomputable section

/-! Unconditional global smooth regularity for the actual completed Hodge
equation with genuine smooth manifold forcing. -/

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] (n : ℕ)

theorem projective_weak_solution_has_smooth_representative
    (u : EnergyDomain.Constructions.ProjectiveEnergyDomain V n)
    (f : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1))
    (hsol : WeakEquation.Constructions.IsProjectiveWeakHodgeSolution V n u (Form.Constructions.smoothToProjectiveL2 V (n + 1) f)) :
    ∃ a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1),
      Form.Constructions.smoothToProjectiveL2 V (n + 1) a = EnergyDomain.Constructions.projectiveEnergyInclusion V n u :=
  SmoothGlobal.Constructions.projective_smooth_representative_of_local_cutoffs V (n + 1) (EnergyDomain.Constructions.projectiveEnergyInclusion V n u)
    (WeakSmoothCutoffNeighborhood.Constructions.exists_projective_weak_smooth_cutoff_neighborhood V n u f hsol)

theorem projective_weak_solution_is_smooth
    (u : EnergyDomain.Constructions.ProjectiveEnergyDomain V n)
    (f : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1))
    (hsol : WeakEquation.Constructions.IsProjectiveWeakHodgeSolution V n u (Form.Constructions.smoothToProjectiveL2 V (n + 1) f)) :
    ∃ a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1),
      SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n a = u := by
  obtain ⟨a, ha⟩ := projective_weak_solution_has_smooth_representative V n u f hsol
  refine ⟨a, EnergyDomain.Constructions.projectiveEnergyInclusion_injective V n ?_⟩
  exact ha

end

end OAI.Analysis.HodgeTheory.Decomposition.WeakGlobalSmooth.Constructions
