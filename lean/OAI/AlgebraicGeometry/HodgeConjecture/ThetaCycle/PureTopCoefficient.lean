import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SmoothConvergence
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallForms
import OAI.Analysis.HodgeTheory.Pure
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior

/-! # Pure Top Coefficient -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PureTopCoefficient.CM

noncomputable section

section

/-! ThetaCycle: a genuine pure top form is its scalar complex-basis coefficient
times the fixed complex area form, in each actual manifold chart. -/

open scoped Classical _root_.Manifold ContDiff _root_.Topology
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.Analysis.HodgeTheory.Pure.Constructions.PolarizedPairing

def ballComplexArea : Analysis.DifferentialForms.Manifold.Basic.FormValue HeckeCycles.GeometricSource.CM.BallChart 2 := RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic.area.restrictScalars ℝ

def ballAreaCoefficient : ℂ →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue HeckeCycles.GeometricSource.CM.BallChart 2 :=
  (ContinuousLinearMap.toSpanSingleton ℂ ballComplexArea).restrictScalars ℝ

theorem ball_area_coefficient_apply (c : ℂ) : ballAreaCoefficient c = c • ballComplexArea := rfl

theorem pure_top_form_from_coefficient (form : Analysis.DifferentialForms.Manifold.Basic.FormValue HeckeCycles.GeometricSource.CM.BallChart 2)
    (hform : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree HeckeCycles.GeometricSource.CM.BallChart 2 0 form) :
    form = ballAreaCoefficient (form (Pi.basisFun ℂ (Fin 2))) := by
  ext v
  rw [Analysis.HodgeTheory.Pure.Constructions.PolarizedPairing.pure_eq_basis_det form hform (Pi.basisFun ℂ (Fin 2)) v]
  simp only [ball_area_coefficient_apply, Pi.basisFun_det_apply]
  rfl

theorem pure_top_chart_from_coefficient {M : Type*} [TopologicalSpace M] [ChartedSpace HeckeCycles.GeometricSource.CM.BallChart M]
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart M 2) (hform : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart M 2 0 form.val)
    (e : SmoothTopology.CM.SmoothAtlasChart HeckeCycles.GeometricSource.CM.BallChart M) (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ e.val.target) :
    form.val.inChart e.val z = ballAreaCoefficient (form.val.inChart e.val z (Pi.basisFun ℂ (Fin 2))) :=
  pure_top_form_from_coefficient _ (hform e e.property z hz)

theorem pure_top_chart_coefficient_locally {M : Type*} [TopologicalSpace M] [ChartedSpace HeckeCycles.GeometricSource.CM.BallChart M]
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart M 2) (hform : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart M 2 0 form.val)
    (e : SmoothTopology.CM.SmoothAtlasChart HeckeCycles.GeometricSource.CM.BallChart M) (f : HeckeCycles.GeometricSource.CM.BallChart → ℂ)
    (hf : ∀ z ∈ e.val.target, form.val.inChart e.val z (Pi.basisFun ℂ (Fin 2)) = f z)
    (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ e.val.target) :
    form.val.inChart e.val =ᶠ[𝓝 z] ballAreaCoefficient ∘ f := by
  filter_upwards [e.val.open_target.mem_nhds hz] with y hy
  rw [pure_top_chart_from_coefficient form hform e y hy, hf y hy]
  rfl

end

/-! ThetaCycle: the scalar complex-basis coefficient controls every actual
chart derivative of a smooth pure top form. -/

open scoped Classical _root_.Manifold ContDiff _root_.Topology
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM Filter

variable {M : Type*} [TopologicalSpace M] [ChartedSpace HeckeCycles.GeometricSource.CM.BallChart M]

theorem top_chart_coefficient_smoothAt (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart M 2)
    (e : SmoothTopology.CM.SmoothAtlasChart HeckeCycles.GeometricSource.CM.BallChart M) (f : HeckeCycles.GeometricSource.CM.BallChart → ℂ)
    (hf : ∀ z ∈ e.val.target, form.val.inChart e.val z (Pi.basisFun ℂ (Fin 2)) = f z)
    (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ e.val.target) : ContDiffAt ℝ ∞ f z := by
  let E := ContinuousAlternatingMap.apply ℝ HeckeCycles.GeometricSource.CM.BallChart ℂ (Pi.basisFun ℂ (Fin 2))
  have hform : ContDiffOn ℝ ∞ (form.val.inChart e.val) e.val.target := by
    simpa only [Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain, Set.preimage_univ, Set.inter_univ] using form.property e e.property
  have hc : ContDiffAt ℝ ∞ (E ∘ form.val.inChart e.val) z :=
    E.contDiff.contDiffAt.comp z (hform.contDiffAt (e.val.open_target.mem_nhds hz))
  apply hc.congr_of_eventuallyEq
  filter_upwards [e.val.open_target.mem_nhds hz] with y hy
  exact (hf y hy).symm

theorem pure_top_chart_jet (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart M 2)
    (hform : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart M 2 0 form.val)
    (e : SmoothTopology.CM.SmoothAtlasChart HeckeCycles.GeometricSource.CM.BallChart M) (f : HeckeCycles.GeometricSource.CM.BallChart → ℂ)
    (hf : ∀ z ∈ e.val.target, form.val.inChart e.val z (Pi.basisFun ℂ (Fin 2)) = f z)
    (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ e.val.target) (m : ℕ) :
    iteratedFDeriv ℝ m (form.val.inChart e.val) z =
      ballAreaCoefficient.compContinuousMultilinearMap (iteratedFDeriv ℝ m f z) := by
  rw [((pure_top_chart_coefficient_locally form hform e f hf z hz).iteratedFDeriv ℝ m).self_of_nhds]
  have hsm : ContDiffAt ℝ m f z := (top_chart_coefficient_smoothAt form e f hf z hz).of_le
    (by exact_mod_cast le_top (a := (m : ℕ∞)))
  exact ballAreaCoefficient.iteratedFDeriv_comp_left hsm le_rfl

theorem pure_top_chart_jet_convergence {P : Type*} (l : Filter P)
    (forms : P → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart M 2) (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart M 2)
    (hforms : ∀ p, Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart M 2 0 (forms p).val)
    (hform : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart M 2 0 form.val)
    (e : SmoothTopology.CM.SmoothAtlasChart HeckeCycles.GeometricSource.CM.BallChart M) (f : P → HeckeCycles.GeometricSource.CM.BallChart → ℂ) (g : HeckeCycles.GeometricSource.CM.BallChart → ℂ)
    (hf : ∀ p z, z ∈ e.val.target → (forms p).val.inChart e.val z (Pi.basisFun ℂ (Fin 2)) = f p z)
    (hg : ∀ z ∈ e.val.target, form.val.inChart e.val z (Pi.basisFun ℂ (Fin 2)) = g z)
    (m : ℕ) (S : Set HeckeCycles.GeometricSource.CM.BallChart) (hS : S ⊆ e.val.target)
    (hlim : TendstoUniformlyOn (fun p z => iteratedFDeriv ℝ m (f p) z)
      (fun z => iteratedFDeriv ℝ m g z) l S) :
    TendstoUniformlyOn (fun p z => iteratedFDeriv ℝ m ((forms p).val.inChart e.val) z)
      (fun z => iteratedFDeriv ℝ m (form.val.inChart e.val) z) l S := by
  let A : (HeckeCycles.GeometricSource.CM.BallChart [×m]→L[ℝ] ℂ) →L[ℝ] (HeckeCycles.GeometricSource.CM.BallChart [×m]→L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue HeckeCycles.GeometricSource.CM.BallChart 2) := by
    simpa only using! ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin m => HeckeCycles.GeometricSource.CM.BallChart)
      ℂ (Analysis.DifferentialForms.Manifold.Basic.FormValue HeckeCycles.GeometricSource.CM.BallChart 2) ballAreaCoefficient
  let Ah : (HeckeCycles.GeometricSource.CM.BallChart [×m]→L[ℝ] ℂ) →+ (HeckeCycles.GeometricSource.CM.BallChart [×m]→L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue HeckeCycles.GeometricSource.CM.BallChart 2) := {
    toFun := A
    map_zero' := A.map_zero
    map_add' := A.map_add }
  have hA : UniformContinuous Ah := uniformContinuous_addMonoidHom_of_continuous A.continuous
  have h := hA.comp_tendstoUniformlyOn hlim
  have h' := h.congr (Filter.Eventually.of_forall (fun p z hz =>
    (pure_top_chart_jet (forms p) (hforms p) e (f p) (hf p) z (hS hz) m).symm))
  exact h'.congr_right (fun z hz => (pure_top_chart_jet form hform e g hg z (hS hz) m).symm)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PureTopCoefficient.CM
