import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Potential
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Reality
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.CurvaturePotential

/-! # Prescribed Curvature -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.PrescribedCurvature

noncomputable section

/-! An exact change to an imaginary (1,1) representative is realized by an actual metric on the original bundle. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem exists_holomorphic_metric_with_curvature (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (F : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2)
    (hF : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 1 F.val)
    (hreal : ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm F = -F)
    (hexact : ∃ a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1,
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = F - h.curvature) :
    ∃ k : HolomorphicMetric.Data.HolomorphicLineMetricData u, k.curvature = F := by
  have htype : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 1 (F - h.curvature).val :=
    HolomorphicMetric.Reality.manifoldTwoMixed_sub F h.curvature hF h.curvature_type
  have hi : ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm (F - h.curvature) = -(F - h.curvature) := by
    apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
    intro x
    ext v
    have ha := congrArg (fun a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2 => a x v) hreal
    have hb := congrArg (fun a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2 => a x v) h.curvature_conjugate
    change star (F x v) = -(F x v) at ha
    change star (h.curvature x v) = -(h.curvature x v) at hb
    change star (F x v - h.curvature x v) = -(F x v - h.curvature x v)
    rw [star_sub, ha, hb]
    ring
  obtain ⟨f, hf, hcurv⟩ := Projective.CurvaturePotential.exists_real_scalar_curvature_potential V (F - h.curvature) htype hi hexact
  refine ⟨h.withPotential f, ?_⟩
  rw [h.withPotential_curvature f hf, hcurv]
  abel

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.PrescribedCurvature
