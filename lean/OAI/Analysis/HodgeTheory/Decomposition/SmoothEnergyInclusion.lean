import OAI.Analysis.HodgeTheory.Decomposition.EnergyDomain

/-! # Smooth Energy Inclusion -/

namespace OAI.Analysis.HodgeTheory.Decomposition.SmoothEnergyInclusion.Constructions

noncomputable section

/-! Genuine smooth forms are dense in the actual completed Hodge energy domain. -/

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] (n : ℕ)

def smoothToProjectiveEnergy :
    DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1) →ₗ[ℂ] EnergyDomain.Constructions.ProjectiveEnergyDomain V n :=
  (EnergyDomain.Constructions.projectiveGraphEmbedding V n).codRestrict (EnergyDomain.Constructions.ProjectiveEnergyDomain V n)
    (fun a => (EnergyDomain.Constructions.projectiveGraphEmbedding V n).range.le_topologicalClosure ⟨a, rfl⟩)

theorem smoothToProjectiveEnergy_dense : DenseRange (smoothToProjectiveEnergy V n) := by
  intro u
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨_, ⟨a, rfl⟩, ha⟩ := Metric.mem_closure_iff.mp u.property ε hε
  exact ⟨smoothToProjectiveEnergy V n a, ⟨a, rfl⟩, ha⟩

theorem smoothToProjectiveEnergy_norm
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :
    ‖smoothToProjectiveEnergy V n a‖ = ‖EnergyDomain.Constructions.projectiveGraphEmbedding V n a‖ := rfl

theorem projectiveEnergyInclusion_on_smooth
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :
    EnergyDomain.Constructions.projectiveEnergyInclusion V n (smoothToProjectiveEnergy V n a) = Form.Constructions.smoothToProjectiveL2 V (n + 1) a := rfl

end

end OAI.Analysis.HodgeTheory.Decomposition.SmoothEnergyInclusion.Constructions
