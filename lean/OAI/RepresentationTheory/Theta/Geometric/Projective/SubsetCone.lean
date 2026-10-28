import OAI.RepresentationTheory.Theta.Geometric.Projective.OpenImageCharts
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeNormalization
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.AlgebraicCone
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicDimension

/-! # Subset Cone -/

namespace OAI.RepresentationTheory.Theta.Geometric.Projective.SubsetCone

noncomputable section

/-! The cone of a compact open part of an actual projective variety
has genuine analytic equations and parametrizations away from its vertex. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open scoped Classical _root_.Manifold

open OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions

variable (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (U : Set X.analyticSpace)

def projectiveSubsetCone : Set (IntrinsicEmbedding.ProjectiveAmbientCoordinates X → ℂ) :=
  AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (IntrinsicEmbedding.projectiveNativeEmbedding X '' U)

theorem projectiveSubsetCone_zero : 0 ∈ projectiveSubsetCone X U := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.zero_mem_projectiveCone _

theorem projectiveSubsetCone_smul (c : ℂ) {v : IntrinsicEmbedding.ProjectiveAmbientCoordinates X → ℂ}
    (hv : v ∈ projectiveSubsetCone X U) : c • v ∈ projectiveSubsetCone X U :=
  AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.smul_mem_projectiveCone _ c hv

theorem projectiveSubsetCone_isClosed (hU : IsClosed U) : IsClosed (projectiveSubsetCone X U) :=
  AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.isClosed_projectiveCone _
    ((hU.isCompact.image (IntrinsicEmbedding.projectiveNativeEmbedding_isClosedEmbedding X).continuous).isClosed)

theorem projectiveSubsetCone_local_equations (hU : IsOpen U)
    (v : IntrinsicEmbedding.ProjectiveAmbientCoordinates X → ℂ) (hv : v ∈ projectiveSubsetCone X U) (hv0 : v ≠ 0) :
    AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt (projectiveSubsetCone X U) v := by
  apply AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.CoordinateCone.Constructions.Cone.holomorphicZeroSetAt_coordinateCone _ ?_ v hv hv0
  intro i p hp hpatch
  obtain ⟨x, hx, rfl⟩ := hp
  have h := OpenImageCharts.projectiveSubsetChart_local_equations X U hU i (x := x) ⟨hx, hpatch⟩
  rwa [OpenImageCharts.projectiveSubsetChart_image, IntrinsicEmbedding.projectiveNativeCoordinates_eq] at h

theorem projectiveSubsetCone_local_parametrization (hU : IsOpen U)
    (v : IntrinsicEmbedding.ProjectiveAmbientCoordinates X → ℂ) (hv : v ∈ projectiveSubsetCone X U) (hv0 : v ≠ 0) :
    ∃ (O : Set (IntrinsicEmbedding.ProjectiveAmbientCoordinates X → ℂ)) (V : Set (X.analyticModel × ℂ))
      (φ : X.analyticModel × ℂ → (IntrinsicEmbedding.ProjectiveAmbientCoordinates X → ℂ)),
      IsOpen O ∧ v ∈ O ∧ IsOpen V ∧ DifferentiableOn ℂ φ V ∧
      projectiveSubsetCone X U ∩ O ⊆ φ '' V ∧ MapsTo φ V (projectiveSubsetCone X U) ∧ InjOn φ V := by
  apply AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeParametrization.Constructions.Cone.local_parametrization_of_coordinateCone _ _ v hv hv0
  intro i p hp hpatch
  obtain ⟨x, hx, rfl⟩ := hp
  have h := OpenImageCharts.projectiveSubsetChart_local_parametrization X U hU i (x := x) ⟨hx, hpatch⟩
  have hi := (OpenImageCharts.projectiveSubsetChart_image X U i).trans
    (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.CoordinateCone.Constructions.Cone.projectiveChart_image_eq_preimage i (IntrinsicEmbedding.projectiveNativeEmbedding X '' U))
  rw [hi] at h
  simpa only [IntrinsicEmbedding.projectiveNativeCoordinates_eq] using h

theorem projectiveSubsetCone_homogeneous_equations (hU : IsClopen U) (hne : U.Nonempty) :
    ∃ Q : Finset (MvPolynomial (IntrinsicEmbedding.ProjectiveAmbientCoordinates X) ℂ),
      (∀ p ∈ Q, ∃ d, p.IsHomogeneous d) ∧
      projectiveSubsetCone X U = {v | ∀ p ∈ Q, MvPolynomial.eval v p = 0} := by
  obtain ⟨d, L, _, _, hfinite, _, hsurj, C, _, hbound⟩ :=
    AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeNormalization.Constructions.Cone.exists_finite_surjective_projection_finiteDimensional
      (projectiveSubsetCone_zero X U) (projectiveSubsetCone_isClosed X U hU.1)
      (projectiveSubsetCone_smul X U) (projectiveSubsetCone_local_equations X U hU.2)
  have hn := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeParametrization.Constructions.Cone.exists_nonzero_mem_projectiveCone (hne.image (IntrinsicEmbedding.projectiveNativeEmbedding X))
  have hd := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicDimension.Constructions.Dimension.finrank_eq_of_finite_surjective_parametrized_set
    (E := X.analyticModel × ℂ) L hsurj hfinite hn (projectiveSubsetCone_local_parametrization X U hU.2)
  have hpos : 0 < d := by
    have hh : X.complexDimension + 1 = d := by
      simpa only [Module.finrank_prod, AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.analyticModel_complex_finrank,
        Module.finrank_self, Module.finrank_fin_fun] using hd
    omega
  have hk : ∀ v ∈ projectiveSubsetCone X U, L v = 0 → v = 0 := by
    intro v hv hv0
    apply norm_le_zero_iff.mp
    simpa only [hv0, norm_zero, mul_zero] using hbound v hv
  exact AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.AlgebraicCone.Constructions.Cone.finite_equations_of_parametrized_cone hpos hd
    (projectiveSubsetCone_zero X U) (projectiveSubsetCone_isClosed X U hU.1)
    (projectiveSubsetCone_smul X U) (projectiveSubsetCone_local_equations X U hU.2)
    L hk hfinite hsurj (projectiveSubsetCone_local_parametrization X U hU.2)

end

end OAI.RepresentationTheory.Theta.Geometric.Projective.SubsetCone
