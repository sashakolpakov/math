import OAI.AlgebraicGeometry.DivisorClass.Chern.GlobalScalarConjugation

/-! # Curvature Potential -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.CurvaturePotential

noncomputable section

/-! Every exact imaginary (1,1)-form on the actual projective manifold has a real scalar curvature potential. -/

open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

theorem exists_scalar_curvature_potential_of_mixed
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 1 (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a).val) :
    ∃ f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0,
      ScalarPotential.globalScalarCurvature f = Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a := by
  obtain ⟨f, hf⟩ := ScalarPotential.exists_antiholomorphic_mixed_potential V a ha
  have hc : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 1
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm a)).val := by
    rw [ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.d_conjugateSmoothForm]
    exact RepresentationTheory.Theta.Geometric.AntiholomorphicClosedRepresentative.conjugate_type11 V (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) ha
  obtain ⟨g, hg⟩ := ScalarPotential.exists_antiholomorphic_mixed_potential V (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm a) hc
  have hh : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.oneFormHolomorphicPart a) =
      (-2 : ℂ) • ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm (ScalarPotential.globalScalarCurvature g) := by
    have H := congrArg ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm hg
    rw [← ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.d_conjugateSmoothForm, GlobalScalarConjugation.conjugate_oneFormAntiholomorphicPart, ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm_involutive] at H
    have hs : ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm ((-2 : ℂ) • ScalarPotential.globalScalarCurvature g) =
        (-2 : ℂ) • ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm (ScalarPotential.globalScalarCurvature g) := by
      apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
      intro x
      ext v
      change star ((-2 : ℂ) * (ScalarPotential.globalScalarCurvature g x v)) =
        (-2 : ℂ) * star (ScalarPotential.globalScalarCurvature g x v)
      simp
    exact H.trans hs
  have hk : ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm (ScalarPotential.globalScalarCurvature g) = -ScalarPotential.globalScalarCurvature (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm g) := by
    rw [GlobalScalarConjugation.globalScalarCurvature_conjugate, neg_neg]
  have hp := congrArg Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.oneForm_parts_add a)
  rw [map_add, hh, hf, hk] at hp
  refine ⟨(2 : ℂ) • ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm g - (2 : ℂ) • f, ?_⟩
  calc
    _ = (-2 : ℂ) • (-ScalarPotential.globalScalarCurvature (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm g)) +
        (-2 : ℂ) • ScalarPotential.globalScalarCurvature f := by
      rw [map_sub, map_smul, map_smul]
      module
    _ = _ := hp

theorem exists_real_scalar_curvature_potential
    (F : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2)
    (hF : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 1 F.val)
    (hreal : ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm F = -F)
    (hexact : ∃ a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = F) :
    ∃ f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0,
      ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm f = f ∧ ScalarPotential.globalScalarCurvature f = F := by
  obtain ⟨a, ha⟩ := hexact
  obtain ⟨f, hf⟩ := exists_scalar_curvature_potential_of_mixed V a (by rw [ha]; exact hF)
  have hff : ScalarPotential.globalScalarCurvature f = F := hf.trans ha
  have him : ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm (ScalarPotential.globalScalarCurvature f) = -ScalarPotential.globalScalarCurvature f := by
    rw [hff]
    exact hreal
  exact ⟨GlobalScalarConjugation.realScalarPotentialPart f, GlobalScalarConjugation.realScalarPotentialPart_conjugate f,
    (GlobalScalarConjugation.globalScalarCurvature_realPart f him).trans hff⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.CurvaturePotential
