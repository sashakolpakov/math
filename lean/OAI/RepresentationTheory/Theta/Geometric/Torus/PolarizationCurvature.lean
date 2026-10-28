import OAI.RepresentationTheory.Theta.Geometric.PolarizationCurvature
import OAI.RepresentationTheory.Theta.Geometric.Torus.RealManifold
import OAI.Analysis.DifferentialForms.Manifold.ChartEquiv
import OAI.Analysis.DifferentialForms.Manifold.CovectorAction

/-! # Polarization Curvature -/

namespace OAI.RepresentationTheory.Theta.Geometric.Torus

noncomputable section

/-! Polarization curvature descends to the actual tangent bundle of
the period torus, preserving closedness, type, and positivity. -/

open scoped _root_.Manifold ContDiff
open _root_.Topology Filter OAI.RepresentationTheory.Theta.Geometric.PolarizationCurvature

variable (Φ : Data.CM.ProjectivePeriodData) (H : Φ.space →ₗ⋆[ℂ] Φ.space →ₗ[ℂ] ℂ)

def Data.CM.ProjectivePeriodData.torusCurvatureRaw : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm Φ.space Φ.periodTorus 2 :=
  fun q => Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.fromChart (Φ.periodChart q) (PolarizationCurvature.polarizationCurvature H) q

theorem Data.CM.ProjectivePeriodData.torusCurvatureRaw_eq_chart (i q : Φ.periodTorus) (hq : q ∈ (Φ.periodChart i).source) :
    Φ.torusCurvatureRaw H q = Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.fromChart (Φ.periodChart i) (PolarizationCurvature.polarizationCurvature H) q := by
  change ((PolarizationCurvature.polarizationCurvature H) (Φ.periodChart q q)).compContinuousLinearMap
    (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap (Φ.periodChart q) q) =
      ((PolarizationCurvature.polarizationCurvature H) (Φ.periodChart i q)).compContinuousLinearMap
        (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap (Φ.periodChart i) q)
  have hc : PolarizationCurvature.polarizationCurvature H (Φ.periodChart q q) = PolarizationCurvature.polarizationCurvature H (Φ.periodChart i q) := by
    ext v
    rw [PolarizationCurvature.polarizationCurvature_apply, PolarizationCurvature.polarizationCurvature_apply]
  rw [hc, Φ.periodChart_tangentMap_eq q i q (Φ.mem_periodChart_source q) hq]

theorem Data.CM.ProjectivePeriodData.torusCurvatureRaw_inChart (i : Φ.periodTorus) (z : Φ.space) (hz : z ∈ (Φ.periodChart i).target) :
    (Φ.torusCurvatureRaw H).inChart (Φ.periodChart i) z = PolarizationCurvature.polarizationCurvature H z := by
  calc
    _ = (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.fromChart (Φ.periodChart i) (PolarizationCurvature.polarizationCurvature H)).inChart (Φ.periodChart i) z := by
      unfold Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart
      rw [Φ.torusCurvatureRaw_eq_chart H i _ ((Φ.periodChart i).map_target hz)]
    _ = _ := Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_fromChart_apply (Φ.periodChart i) (Φ.periodChart_mem_atlas i)
      (PolarizationCurvature.polarizationCurvature H) hz

theorem Data.CM.ProjectivePeriodData.torusCurvatureRaw_smooth : Analysis.DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn (Φ.torusCurvatureRaw H) Set.univ := by
  intro e he
  obtain ⟨i, rfl⟩ := he
  apply (PolarizationCurvature.polarizationCurvature H).smooth.contDiffOn.congr
  intro z hz
  exact Φ.torusCurvatureRaw_inChart H i z hz.1

def Data.CM.ProjectivePeriodData.torusCurvature : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm Φ.space Φ.periodTorus 2 :=
  ⟨Φ.torusCurvatureRaw H, Φ.torusCurvatureRaw_smooth H⟩

theorem Data.CM.ProjectivePeriodData.torusCurvature_closed : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Φ.torusCurvature H) = 0 := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro q
  have heq : (Φ.torusCurvatureRaw H).inChart (Φ.periodChart q)
      =ᶠ[𝓝 (Φ.periodChart q q)] (PolarizationCurvature.polarizationCurvature H : Analysis.DifferentialForms.Manifold.Basic.RawForm Φ.space 2) := by
    filter_upwards [(Φ.periodChart q).open_target.mem_nhds
      ((Φ.periodChart q).map_source (Φ.mem_periodChart_source q))] with z hz
    exact Φ.torusCurvatureRaw_inChart H q z hz
  change (extDeriv ((Φ.torusCurvatureRaw H).inChart (Φ.periodChart q))
    (Φ.periodChart q q)).compContinuousLinearMap (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap (Φ.periodChart q) q) = 0
  rw [heq.extDeriv_eq]
  have hd : extDeriv (PolarizationCurvature.polarizationCurvature H : Analysis.DifferentialForms.Manifold.Basic.RawForm Φ.space 2) (Φ.periodChart q q) = 0 :=
    congrArg (fun f : Analysis.DifferentialForms.Manifold.Basic.SmoothForm Φ.space 3 => f (Φ.periodChart q q)) (PolarizationCurvature.polarizationCurvature_closed H)
  rw [hd]
  ext v
  rfl

theorem Data.CM.ProjectivePeriodData.torusCurvature_hasManifoldBidegree :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree Φ.space Φ.periodTorus 1 1 (Φ.torusCurvatureRaw H) := by
  intro e he z hz
  obtain ⟨i, rfl⟩ := he
  rw [Φ.torusCurvatureRaw_inChart H i z hz]
  exact PolarizationCurvature.polarizationCurvature_hasBidegree H z

theorem Data.CM.ProjectivePeriodData.torusCurvature_hasTangentBidegree :
    Analysis.DifferentialForms.Manifold.CovectorAction.HasTangentBidegree Φ.space Φ.periodTorus 1 1 (Φ.torusCurvatureRaw H) :=
  (Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree (E := Φ.space) (M := Φ.periodTorus)
    (p := 1) (q := 1) (Φ.torusCurvatureRaw H)).mp (Φ.torusCurvature_hasManifoldBidegree H)

theorem Data.CM.ProjectivePeriodData.torusCurvature_positive (hsym : ∀ u v, H v u = star (H u v))
    (hpos : ∀ u : Φ.space, u ≠ 0 → 0 < (H u u).re) (q : Φ.periodTorus)
    (v : TangentSpace 𝓘(ℝ, Φ.space) q) (hv : v ≠ 0) :
    0 < ((Complex.I / (2 * (Real.pi : ℂ))) *
      Φ.torusCurvature H q ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul q Complex.I v]).re := by
  let e := Φ.periodChart q
  have he : e ∈ atlas Φ.space Φ.periodTorus := Φ.periodChart_mem_atlas q
  have hq : q ∈ e.source := Φ.mem_periodChart_source q
  have hw : Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e q v ≠ 0 := by
    intro hz
    apply hv
    apply (Analysis.DifferentialForms.Manifold.TangentCoordinates.chartTangentEquiv e he q hq).injective
    simpa only [Analysis.DifferentialForms.Manifold.TangentCoordinates.chartTangentEquiv_apply, map_zero] using hz
  have h := PolarizationCurvature.polarizationCurvature_positive H hsym hpos (e q) (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e q v) hw
  change 0 < ((Complex.I / (2 * (Real.pi : ℂ))) * PolarizationCurvature.polarizationCurvature H (e q)
    (fun k => Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e q (![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul q Complex.I v] k))).re
  have ht : (fun k => Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e q (![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul q Complex.I v] k)) =
      ![Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e q v, Complex.I • Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e q v] := by
    funext k
    fin_cases k
    · rfl
    · exact Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul_inChart e he q hq Complex.I v
  rw [ht]
  exact h

end

end OAI.RepresentationTheory.Theta.Geometric.Torus
