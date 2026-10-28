import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.Affine
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicCone
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.TorusManifold
import OAI.Geometry.ComplexTorus.RiemannProjectivity.AffineCone

/-! # Algebraic Normalized Cone Smoothness -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicNormalizedConeSmoothness.CM.Abelian.Algebraization.NormalizedConeSmoothness

noncomputable section

open Set
open OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent OAI.Geometry.ComplexTorus.RiemannProjectivity.SmoothReferencePoint.Constructions.SmoothPointLocalization

variable {n : ℕ}

theorem mem_smoothLocus_at_parameter (Φ : ProjectiveTorusData.CM.Abelian.ProjectivePeriodData)
    (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ)) (hf : Topology.IsClosedEmbedding f)
    (hd : ∀ (z : Φ.space) (i : Fin (n + 1)),
      f (QuotientAddGroup.mk z) ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
      DifferentiableAt ℂ (fun w => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z ∧
      Function.Injective (fderiv ℂ (fun w => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z))
    (i : Fin (n + 1)) (z : Φ.space)
    (hi : f (QuotientAddGroup.mk z) ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source)
    (v : ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f))
    (hv : v.val = Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.parameterization i (fun w => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) (z, 1)) :
    Geometry.ComplexTorus.RiemannProjectivity.SmoothReferencePoint.Constructions.SmoothPointLocalization.pointPrime (Geometry.ComplexTorus.RiemannProjectivity.AffineCone.Constructions.AffineCoordinateSmoothness.point (ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) v.val v.property) ∈
      Algebra.smoothLocus ℂ
        (MvPolynomial (Fin (n + 1)) ℂ ⧸ MvPolynomial.vanishingIdeal ℂ (ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f))) := by
  obtain ⟨m, e, q, hq, hsm⟩ := Affine.CM.Abelian.Algebraization.AffineConeSmoothPoint.exists_at_parameter Φ f hf hd i z hi v hv
  let a := e.trans (LinearEquiv.sumArrowLequivProdArrow
    (Fin (Module.finrank ℂ (Φ.space) + 1)) (Fin m) ℂ ℂ).symm.toContinuousLinearEquiv
  exact Geometry.ComplexTorus.RiemannProjectivity.AffineCone.Constructions.AffineCoordinateSmoothness.mem_smoothLocus_of_coordinates a
    (ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) v.val v.property q hq hsm

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicNormalizedConeSmoothness.CM.Abelian.Algebraization.NormalizedConeSmoothness
