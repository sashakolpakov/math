import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.AffineFormFaithfulness
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FormsAffineLocality
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AffineEvaluation
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerGluing
import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.FormNaturality
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineOpenDifferential
import OAI.Topology.Euclidean.OpenCoordinateTransport

/-! # Global Form Faithfulness -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GlobalFormFaithfulness

noncomputable section

/-! The genuine smooth realization detects all affine-test one-forms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.Comparison.Betti.Smooth.FormNaturality
open scoped _root_.Manifold ContDiff

attribute [local instance] Comparison.Betti.Algebraic.Sheaves.sectionAlgebra

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (U : X.left.Opens) (hU : IsAffineOpen U)

def affineOpenAnalyticMap :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U) → Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U :=
  fun x => ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X U hU x, by
    have h : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X U hU x ∈
        Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X U hU) := ⟨x, rfl⟩
    rwa [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_affineOpenPointMap] at h⟩

theorem affineOpenAnalyticMap_evaluation
    (a : Γ(X.left, U)) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)) :
    x a = Comparison.Betti.Open.AffineIsoEvaluation.sectionEvaluationOn X U a (affineOpenAnalyticMap X U hU x) := by
  have : IsOpenImmersion (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU).left := by
    change IsOpenImmersion hU.fromSpec
    infer_instance
  have he : HodgeConjecture.CMExtraction.AffineEvaluation.Kaehler.affineOpenCharacter X U hU (affineOpenAnalyticMap X U hU x) = x :=
    (ComplexPoints.Analytic.SmoothSchemeManifold.isOpenEmbedding_affinePointMap _ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU)).injective
      (HodgeConjecture.CMExtraction.AffineEvaluation.Kaehler.affineOpenCharacter_point X U hU _)
  exact (congrArg (fun y => y a) he).symm.trans
    (HodgeConjecture.CMExtraction.AffineEvaluation.Kaehler.affineOpenCharacter_evaluation X U hU _ a)

variable [IsIntegral X.left] [Smooth X.hom] [Nonempty U]

variable [Algebra.Smooth ℂ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)]

theorem affineOpenAnalyticMap_smooth :
    ContMDiff
      𝓘(ℝ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)) → ℂ)
      𝓘(ℝ, Comparison.Betti.RegularSmoothness.NativeModel X) ∞ (affineOpenAnalyticMap X U hU) := by
  apply (Topology.Euclidean.OpenCoordinateTransport.Globalization.contMDiff_subtypeVal_comp_iff_order (Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U) _).mp
  exact ComplexPoints.Analytic.AffineOpenDifferential.real_contMDiff_affinePointMap _ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU) ∞

theorem affineOpenRealization_pullback (form : FormConstants.OneForms X) :
    AffineFormFaithfulness.affineKaehlerRealization (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
      (form.val _ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU)) =
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (affineOpenAnalyticMap X U hU) (affineOpenAnalyticMap_smooth X U hU)
      (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (Comparison.Betti.RegularSmoothness.NativeModel X) (Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U) 1
        (HodgeConjecture.CMExtraction.Kaehler.affineSmoothForm X U hU form)) := by
  let R := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U
  have hopen : Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (Comparison.Betti.RegularSmoothness.NativeModel X) (Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U) 1
      (HodgeConjecture.CMExtraction.Kaehler.affineSmoothForm X U hU form) =
    Comparison.Betti.Smooth.FormRealization.oneFormMap (Comparison.Betti.Open.AffineIsoEvaluation.sectionEvaluationOn X U) (Comparison.Betti.Open.SmoothEvaluation.sectionEvaluationOn_smooth X U)
      (HodgeConjecture.CMExtraction.Kaehler.affineForm X U hU form) := by
    change (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (Comparison.Betti.RegularSmoothness.NativeModel X) (Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U) 1)
      ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (Comparison.Betti.RegularSmoothness.NativeModel X) (Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U) 1).symm
        (Comparison.Betti.Smooth.CochainMap.smoothFormMap (Comparison.Betti.Open.AffineIsoEvaluation.sectionEvaluationOn X U) (Comparison.Betti.Open.SmoothEvaluation.sectionEvaluationOn_smooth X U) 1
          (HodgeConjecture.CMExtraction.Kaehler.affineForm X U hU form))) = _
    rw [LinearEquiv.apply_symm_apply, Comparison.Betti.Smooth.CochainMap.smoothFormMap_one]
  rw [hopen]
  have hn := Comparison.Betti.Smooth.FormNaturality.oneFormMap_naturality (AffineFormFaithfulness.affineEvaluation R) (AffineFormFaithfulness.affineEvaluation_smooth R)
    (Comparison.Betti.Open.AffineIsoEvaluation.sectionEvaluationOn X U) (Comparison.Betti.Open.SmoothEvaluation.sectionEvaluationOn_smooth X U) (AlgHom.id ℂ R)
    (affineOpenAnalyticMap X U hU) (affineOpenAnalyticMap_smooth X U hU)
    (affineOpenAnalyticMap_evaluation X U hU) (HodgeConjecture.CMExtraction.Kaehler.affineForm X U hU form)
  have hid : Comparison.Betti.Algebraic.Forms.pullback (AlgHom.id ℂ R) 1 (HodgeConjecture.CMExtraction.Kaehler.affineForm X U hU form) =
      HodgeConjecture.CMExtraction.Kaehler.affineForm X U hU form :=
    congrArg (fun L : Comparison.Betti.Algebraic.Forms.Form R 1 →ₗ[ℂ] Comparison.Betti.Algebraic.Forms.Form R 1 =>
      L (HodgeConjecture.CMExtraction.Kaehler.affineForm X U hU form)) (Comparison.Betti.Algebraic.Forms.pullback_id (A := R) 1)
  exact (congrArg (Comparison.Betti.Smooth.FormRealization.oneFormMap (AffineFormFaithfulness.affineEvaluation R) (AffineFormFaithfulness.affineEvaluation_smooth R)) hid).symm.trans hn

omit [Nonempty U] [Algebra.Smooth ℂ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)] in
theorem globalSmoothForm_eq_zero [X.left.IsSeparated] (form : FormConstants.OneForms X)
    (hform : HodgeConjecture.CMExtraction.KaehlerGluing.globalSmoothForm X form = 0) : form = 0 := by
  apply FormsAffineLocality.oneForm_eq_zero_of_affineOpens form
  intro V hV
  classical
  by_cases hVn : Nonempty V
  · let : Nonempty V := hVn
    let : Algebra.Smooth ℂ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V) :=
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_smooth X V hV
    apply (AffineFormFaithfulness.affineKaehlerRealization_injective (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V))
    rw [map_zero, affineOpenRealization_pullback X V hV]
    have ha : HodgeConjecture.CMExtraction.Kaehler.affineSmoothForm X V hV form = 0 := by
      rw [← HodgeConjecture.CMExtraction.KaehlerGluing.globalSmoothForm_onAffine, hform, map_zero]
    rw [ha, map_zero, map_zero]
  · have hV0 : V = ⊥ := by
      apply le_antisymm _ bot_le
      intro p hp
      exact (hVn ⟨⟨p, hp⟩⟩).elim
    subst V
    have : Subsingleton (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X ⊥) :=
      inferInstanceAs (Subsingleton Γ(X.left, ⊥))
    exact Subsingleton.elim _ _

omit [Nonempty U] [Algebra.Smooth ℂ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)] in
theorem globalSmoothForm_injective [X.left.IsSeparated] : Function.Injective (HodgeConjecture.CMExtraction.KaehlerGluing.globalSmoothForm X) := by
  intro form η h
  apply sub_eq_zero.mp
  apply globalSmoothForm_eq_zero X (form - η)
  rw [map_sub, h, sub_self]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GlobalFormFaithfulness
