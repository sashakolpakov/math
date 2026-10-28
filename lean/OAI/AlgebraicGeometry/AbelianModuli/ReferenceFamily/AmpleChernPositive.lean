import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SectionEmbeddedVariety
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ChernTensorPowers
import OAI.AlgebraicGeometry.Foundations.Scheme.ClosedProjective
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.VarietyMetric

/-! # Ample Chern Positive -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AmpleChernPositive

noncomputable section

section

/-! A positive integer multiple of the original ample Chern class is
the Fubini–Study class of an actual embedding of the same complex scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.Foundations.Scheme.ClosedProjective
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.VarietyMetric.CM.Construction

def reembeddedVariety (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (Q : Foundations.Scheme.SmoothProjective.ProjectivePresentation V.carrier V.structureMap) : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety :=
  ⟨{V.presentation with projective := Q}, V.property⟩

theorem ample_fubiniStudy_multiple (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (L : HilbertConstruction.Line.Bundles.LineBundle V.toOver.left) (hL : L.IsAmple) :
    ∃ (d : ℕ), 0 < d ∧ ∃ (Q : Foundations.Scheme.SmoothProjective.ProjectivePresentation V.carrier V.structureMap),
      ComplexMultiplication.HodgeComparison.ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClassQ (reembeddedVariety V Q) = d • Intrinsic.ChernClasses.lineBundleChernClass V.presentation L := by
  have : IsProper V.toOver.hom := V.presentation.isProper
  obtain ⟨d, e, hd, he, n, s, hs, hc⟩ := AmpleSectionEmbedding.ample_exists_sections_embedding L hL V.toOver.hom
  let W := SectionEmbeddedVariety.sectionEmbeddedVariety V s hs hc
  refine ⟨e * d, Nat.mul_pos he hd, W.presentation.projective, ?_⟩
  have h := SectionEmbeddedVariety.sectionEmbeddedVariety_chern V ((L.tensorPower d).tensorPower e) s hs hc
  have hp := (ChernTensorPowers.lineBundleChernClass_tensorPower V.presentation (L.tensorPower d) e).trans
    ((congrArg (fun z => e • z) (ChernTensorPowers.lineBundleChernClass_tensorPower V.presentation L d)).trans
      (smul_smul e d (Intrinsic.ChernClasses.lineBundleChernClass V.presentation L)))
  exact h.trans hp

end

/-! The original ample Chern class has an actual real, closed, strictly
positive (1,1) representative on the native complex manifold. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.Foundations.Scheme.ClosedProjective
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.VarietyMetric.CM.Construction
open scoped _root_.Manifold ContDiff

theorem ampleChern_positive_representative (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (L : HilbertConstruction.Line.Bundles.LineBundle V.toOver.left) (hL : L.IsAmple) :
    ∃ α : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 2,
      (V.deRhamBettiIso 2).hom (V.deRhamClass 2 α) =
        V.rationalCohomologyInclusion 2 (Intrinsic.ChernClasses.lineBundleChernClass V.presentation L) ∧
      Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 1 α.val.val ∧
      (∀ (x : V.analyticSpace) (u : TangentSpace 𝓘(ℝ, V.analyticModel) x), u ≠ 0 →
        0 < (α.val x ![u, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I u]).re) ∧
      ∀ (x : V.analyticSpace) (v : Fin 2 → TangentSpace 𝓘(ℝ, V.analyticModel) x),
        (α.val x v).im = 0 := by
  obtain ⟨d, hd, Q, hQ⟩ := ample_fubiniStudy_multiple V L hL
  let W := reembeddedVariety V Q
  let c : ℂ := ((d : ℝ)⁻¹ : ℝ)
  let α : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 2 := c • ComplexMultiplication.HodgeComparison.ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClosedForm W
  have hc : c = (d : ℂ)⁻¹ := by simp only [c, Complex.ofReal_inv, Complex.ofReal_natCast]
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  have hclass : (V.deRhamBettiIso 2).hom (V.deRhamClass 2 (ComplexMultiplication.HodgeComparison.ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClosedForm W)) =
      d • V.rationalCohomologyInclusion 2 (Intrinsic.ChernClasses.lineBundleChernClass V.presentation L) :=
    (ComplexMultiplication.HodgeComparison.ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClassQ_comparison W).trans
      ((congrArg (fun z => W.rationalCohomologyInclusion 2 z) hQ).trans
        (map_nsmul (W.rationalCohomologyInclusion 2).hom d (Intrinsic.ChernClasses.lineBundleChernClass V.presentation L)))
  refine ⟨α, ?_, (ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm_hasBidegree W).const_smul c, ?_, ?_⟩
  · have h₁ := (V.deRhamClass 2).map_smul c (ComplexMultiplication.HodgeComparison.ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClosedForm W)
    have h₂ := (V.deRhamBettiIso 2).hom.hom.map_smul c (V.deRhamClass 2 (ComplexMultiplication.HodgeComparison.ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClosedForm W))
    have h₃ : c • (d • V.rationalCohomologyInclusion 2 (Intrinsic.ChernClasses.lineBundleChernClass V.presentation L)) =
        V.rationalCohomologyInclusion 2 (Intrinsic.ChernClasses.lineBundleChernClass V.presentation L) := by
      rw [hc, ← Nat.cast_smul_eq_nsmul ℂ d]
      exact inv_smul_smul₀ hdC _
    exact (congrArg (fun z => (V.deRhamBettiIso 2).hom z) h₁).trans
      (h₂.trans ((congrArg (fun z => c • z) hclass).trans h₃))
  · intro x u hu
    let w := ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm W x ![u, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul (E := V.analyticModel) x Complex.I u]
    have hp : 0 < w.re := ComplexMultiplication.HodgeComparison.VarietyMetric.CM.Construction.varietyFubiniStudyForm_positive W x u hu
    change 0 < (((((d : ℝ)⁻¹ : ℝ) : ℂ) * w).re)
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos (inv_pos.mpr (Nat.cast_pos.mpr hd)) hp
  · intro x v
    change (c * ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm W x v).im = 0
    change (((((d : ℝ)⁻¹ : ℝ) : ℂ) * ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm W x v).im) = 0
    rw [Complex.mul_im, Complex.ofReal_im, ComplexMultiplication.HodgeComparison.VarietyMetric.CM.Construction.varietyFubiniStudyForm_real W x v, mul_zero, zero_mul, add_zero]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AmpleChernPositive
