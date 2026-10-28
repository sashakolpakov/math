import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.KaehlerPointDetection
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.IntrinsicAffineTangent
import OAI.AlgebraicGeometry.Comparison.Betti.KaehlerEquivalence
import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.FormRealization
import OAI.Analysis.DifferentialForms.Manifold.Holomorphic

/-! # Affine Form Faithfulness -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.AffineFormFaithfulness

noncomputable section

/-! Faithfulness of the actual smooth realization of affine Kähler one-forms. -/

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.IntrinsicAffineTangent
open scoped _root_.Manifold ContDiff

variable (R : Type) [CommRing R] [Algebra ℂ R] [IsDomain R] [Algebra.Smooth ℂ R]

local notation "Model" => (Fin (OAI.AlgebraicGeometry.Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ R) → ℂ)

def affineEvaluation : R →ₐ[ℂ] C(Foundations.Scheme.AffineComplexPoints.affineComplexPoints R, ℂ) where
  toFun a := ⟨fun x => x a, Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_eval a⟩
  map_zero' := by ext x; exact x.map_zero
  map_one' := by ext x; exact x.map_one
  map_add' a b := by ext x; exact x.map_add a b
  map_mul' a b := by ext x; exact x.map_mul a b
  commutes' c := by ext x; exact x.commutes c

theorem affineEvaluation_smooth (a : R) :
    ContMDiff 𝓘(ℝ, Model) 𝓘(ℝ, ℂ) ∞ (affineEvaluation R a) :=
  Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex (AbelianModuli.ReferenceFamily.Regular.IntrinsicAffineTangent.contMDiff_affineEvaluation a ∞)

def affineKaehlerRealization :
    KaehlerDifferential ℂ R →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm Model (Foundations.Scheme.AffineComplexPoints.affineComplexPoints R) 1 :=
  (Comparison.Betti.Smooth.FormRealization.oneFormMap (affineEvaluation R) (affineEvaluation_smooth R)).comp
    (Comparison.Betti.KaehlerEquivalence.kaehlerToOneForm R)

theorem affineKaehlerRealization_symbol (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints R)
    (a b : R) (v : Model) :
    (affineKaehlerRealization R (a • KaehlerDifferential.D ℂ R b)).val.inChart
      (chartAt Model x) (chartAt Model x x) (fun _ => v) =
      x a * (AbelianModuli.ReferenceFamily.Regular.IntrinsicAffineTangent.nativeAffineTangentDerivations x v).val b := by
  let e := chartAt Model x
  have he : e ∈ atlas Model (Foundations.Scheme.AffineComplexPoints.affineComplexPoints R) := chart_mem_atlas _ x
  have hx : e x ∈ e.target := e.map_source (mem_chart_source _ x)
  change (Comparison.Betti.Smooth.FormRealization.oneFormMap (affineEvaluation R) (affineEvaluation_smooth R)
    (Comparison.Betti.KaehlerEquivalence.kaehlerToOneForm R (a • KaehlerDifferential.D ℂ R b))).val.inChart
      e (e x) (fun _ => v) = _
  rw [Comparison.Betti.KaehlerEquivalence.kaehlerToOneForm_smul_D, Comparison.Betti.KaehlerEquivalence.oneSymbol, Comparison.Betti.Smooth.FormRealization.oneFormMap_symbol]
  change (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.smulFunction (affineEvaluation R a)
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Comparison.Betti.Smooth.FormRealization.zeroFormMap (affineEvaluation R)
      (affineEvaluation_smooth R) b)).val).inChart e (e x) (fun _ => v) = _
  rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_smulFunction]
  change (e.symm (e x)) a *
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Comparison.Betti.Smooth.FormRealization.zeroFormMap (affineEvaluation R)
      (affineEvaluation_smooth R) b)).val.inChart e (e x) (fun _ => v) = _
  rw [e.left_inv (mem_chart_source _ x), Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_inChart _ e he hx]
  change x a * extDeriv ((Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.ofScalar (affineEvaluation R b)).inChart e)
    (e x) (fun _ => v) = _
  have hd : DifferentiableAt ℂ (fun z => e.symm z b) (e x) := by
    have hr : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas R (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ R) := he
    exact ((hr.1 b).contDiffAt (e.open_target.mem_nhds hx)).differentiableAt (by simp)
  rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.ofScalar_inChart, extDeriv_constOfIsEmpty]
  change x a * fderiv ℝ (fun z => e.symm z b) (e x) v = _
  rw [hd.fderiv_restrictScalars ℝ]
  exact congrArg (x a * ·) (AbelianModuli.ReferenceFamily.Regular.IntrinsicAffineTangent.nativeAffineTangentDerivations_chart x v b).symm

theorem affineKaehlerRealization_inChart (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints R)
    (form : KaehlerDifferential ℂ R) (v : Model) :
    (affineKaehlerRealization R form).val.inChart
      (chartAt Model x) (chartAt Model x x) (fun _ => v) =
      KaehlerPointDetection.pointKaehlerValue x (AbelianModuli.ReferenceFamily.Regular.IntrinsicAffineTangent.nativeAffineTangentDerivations x v) form := by
  obtain ⟨r, rfl⟩ := KaehlerDifferential.linearCombination_surjective ℂ R form
  induction r using Finsupp.induction_linear with
  | zero => simp only [map_zero]; rfl
  | add r t hr ht =>
    simp only [map_add]
    have hadd (f g : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm Model (Foundations.Scheme.AffineComplexPoints.affineComplexPoints R) 1) :
        (f + g).val.inChart (chartAt Model x) (chartAt Model x x) (fun _ => v) =
          f.val.inChart (chartAt Model x) (chartAt Model x x) (fun _ => v) +
            g.val.inChart (chartAt Model x) (chartAt Model x x) (fun _ => v) :=
      congrArg (fun q => q (chartAt Model x x) (fun _ => v))
        (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_add f.val g.val (chartAt Model x))
    exact (hadd _ _).trans (congrArg₂ (· + ·) hr ht)
  | single b a =>
    simp only [Finsupp.linearCombination_single]
    rw [affineKaehlerRealization_symbol, KaehlerPointDetection.pointKaehlerValue_smul, KaehlerPointDetection.pointKaehlerValue_D]

theorem affineKaehlerRealization_injective : Function.Injective (affineKaehlerRealization R) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro form hform
  apply KaehlerPointDetection.kaehler_eq_zero_of_pointDerivations form
  intro x D
  obtain ⟨v, rfl⟩ := (AbelianModuli.ReferenceFamily.Regular.IntrinsicAffineTangent.nativeAffineTangentDerivations x).surjective D
  have h := affineKaehlerRealization_inChart R x form v
  rw [hform] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.AffineFormFaithfulness
