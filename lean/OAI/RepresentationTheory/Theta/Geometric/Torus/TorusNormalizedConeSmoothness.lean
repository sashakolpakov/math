import OAI.RepresentationTheory.Theta.Geometric.Torus.Affine
import OAI.RepresentationTheory.Theta.Geometric.Torus.TorusCone
import OAI.RepresentationTheory.Theta.Geometric.Torus.Manifold
import OAI.Geometry.ComplexTorus.RiemannProjectivity.AffineCone

/-! # Torus Normalized Cone Smoothness -/

namespace OAI.RepresentationTheory.Theta.Geometric.Torus.TorusNormalizedConeSmoothness.CM.Algebraization.NormalizedConeSmoothness

noncomputable section

open Set
open OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent OAI.Geometry.ComplexTorus.RiemannProjectivity.SmoothReferencePoint.Constructions.SmoothPointLocalization

variable {n : ℕ}

theorem mem_smoothLocus_at_parameter (Φ : Data.CM.ProjectivePeriodData)
    (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ)) (hf : Topology.IsClosedEmbedding f)
    (hd : ∀ (z : Φ.space) (i : Fin (n + 1)),
      f (QuotientAddGroup.mk z) ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
      DifferentiableAt ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z ∧
      Function.Injective (fderiv ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z))
    (i : Fin (n + 1)) (z : Φ.space)
    (hi : f (QuotientAddGroup.mk z) ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source)
    (v : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f))
    (hv : v.val = Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.parameterization i (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) (z, 1)) :
    Geometry.ComplexTorus.RiemannProjectivity.SmoothReferencePoint.Constructions.SmoothPointLocalization.pointPrime (Geometry.ComplexTorus.RiemannProjectivity.AffineCone.Constructions.AffineCoordinateSmoothness.point (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) v.val v.property) ∈
      Algebra.smoothLocus ℂ
        (MvPolynomial (Fin (n + 1)) ℂ ⧸ MvPolynomial.vanishingIdeal ℂ (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f))) := by
  obtain ⟨m, e, q, hq, hsm⟩ := Affine.CM.Algebraization.AffineConeSmoothPoint.exists_at_parameter Φ f hf hd i z hi v hv
  let a := e.trans (LinearEquiv.sumArrowLequivProdArrow
    (Fin (Module.finrank ℂ (Φ.space) + 1)) (Fin m) ℂ ℂ).symm.toContinuousLinearEquiv
  exact Geometry.ComplexTorus.RiemannProjectivity.AffineCone.Constructions.AffineCoordinateSmoothness.mem_smoothLocus_of_coordinates a
    (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) v.val v.property q hq hsm

end

end OAI.RepresentationTheory.Theta.Geometric.Torus.TorusNormalizedConeSmoothness.CM.Algebraization.NormalizedConeSmoothness
