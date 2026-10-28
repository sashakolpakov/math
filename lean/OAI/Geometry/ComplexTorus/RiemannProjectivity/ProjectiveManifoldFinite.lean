import OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectiveManifoldIs
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeNormalization
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicDimension
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.AlgebraicCone

/-! # Projective Manifold Finite -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectiveManifoldFinite.Constructions.ProjectiveManifoldEquations

noncomputable section

/-! # RiemannProjectivity: finite homogeneous equations for embedded compact complex manifolds -/

open Set
open scoped _root_.Manifold
open OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectiveManifoldIs.Constructions.ProjectiveManifoldCone
attribute [local instance] Classical.propDecidable

variable {V M ι : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [TopologicalSpace M] [ChartedSpace V M] [IsManifold (𝓘(ℂ, V)) 1 M] [Fintype ι]

theorem finite_homogeneous_equations [Nonempty M]
    (f : M → Projectivization ℂ (ι → ℂ)) (hf : Topology.IsClosedEmbedding f)
    (hd : ∀ i x, x ∈ ProjectiveManifoldIs.Constructions.ProjectiveManifoldCone.chartDomain f i →
      MDifferentiableAt (𝓘(ℂ, V)) (𝓘(ℂ, {j : ι // j ≠ i} → ℂ)) (ProjectiveManifoldIs.Constructions.ProjectiveManifoldCone.chartMap f i) x ∧
      Function.Injective (mfderiv (𝓘(ℂ, V)) (𝓘(ℂ, {j : ι // j ≠ i} → ℂ)) (ProjectiveManifoldIs.Constructions.ProjectiveManifoldCone.chartMap f i) x)) :
    ∃ Q : Finset (MvPolynomial ι ℂ), (∀ q ∈ Q, ∃ d, q.IsHomogeneous d) ∧
      AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) = {v | ∀ q ∈ Q, MvPolynomial.eval v q = 0} := by
  let S := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)
  have hz : 0 ∈ S := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.zero_mem_projectiveCone _
  have hc : IsClosed S := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.isClosed_projectiveCone _ hf.isClosed_range
  have hs : ∀ (c : ℂ) ⦃v⦄, v ∈ S → c • v ∈ S := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.smul_mem_projectiveCone _
  have hl := ProjectiveManifoldIs.Constructions.ProjectiveManifoldCone.local_equations f hf.isEmbedding hd
  have hp := ProjectiveManifoldIs.Constructions.ProjectiveManifoldCone.local_parameters f hf.isEmbedding (fun i x hx => (hd i x hx).1)
  obtain ⟨d, L, _, _, hfinite, _, hsurj, C, _, hbound⟩ :=
    AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeNormalization.Constructions.Cone.exists_finite_surjective_projection_finiteDimensional hz hc hs hl
  have hdim : Module.finrank ℂ (V × ℂ) = Module.finrank ℂ (Fin d → ℂ) :=
    AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicDimension.Constructions.Dimension.finrank_eq_of_finite_surjective_parametrized_set L hsurj hfinite
      (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeParametrization.Constructions.Cone.exists_nonzero_mem_projectiveCone (range_nonempty f)) hp
  have hdpos : 0 < d := by
    have h := hdim
    simp only [Module.finrank_prod, Module.finrank_self, Module.finrank_pi, Fintype.card_fin] at h
    omega
  have hk : ∀ v ∈ S, L v = 0 → v = 0 := by
    intro v hv hLv
    apply norm_le_zero_iff.mp
    simpa only [hLv, norm_zero, mul_zero] using hbound v hv
  exact AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.AlgebraicCone.Constructions.Cone.finite_equations_of_parametrized_cone hdpos hdim hz hc hs hl L hk hfinite hsurj hp

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectiveManifoldFinite.Constructions.ProjectiveManifoldEquations
