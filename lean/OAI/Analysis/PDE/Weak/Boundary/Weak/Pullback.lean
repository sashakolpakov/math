import OAI.Analysis.PDE.Weak.Boundary.Weak.ChartTest
import Mathlib.MeasureTheory.Function.Jacobian

/-! The divergence-form weak equation under a genuine local smooth
coordinate change, including the Jacobian weight. -/

noncomputable section
open Set Filter _root_.MeasureTheory
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Weak

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def WeakFluxEquation (μ : Measure E) (Ω : Set E) (H : E → E) (f : E → ℝ) : Prop :=
  ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    (∫ x, fderiv ℝ φ x (H x) ∂μ) = ∫ x, f x * φ x ∂μ

theorem WeakFluxEquation.pullback (μ : Measure E) [μ.IsAddHaarMeasure]
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {G P : E → E} (hG : ContDiff ℝ ∞ G) (hP : ContDiff ℝ ∞ P)
    (hGU : MapsTo G U V) (hPV : MapsTo P V U)
    (hPG : ∀ x ∈ U, P (G x) = x) (hGP : ∀ x ∈ V, G (P x) = x)
    {H : E → E} {f : E → ℝ} (hweak : WeakFluxEquation μ V H f) :
    WeakFluxEquation μ U
      (fun y => |(fderiv ℝ G y).det| • (fderiv ℝ P (G y) (H (G y))))
      (fun y => |(fderiv ℝ G y).det| * f (G y)) := by
  have himage : G '' U = V := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hGU hy
    · intro hx
      exact ⟨P x, hPV hx, hGP x hx⟩
  have hinj : InjOn G U := by
    intro x hx y hy hxy
    have hh := congrArg P hxy
    simpa only [hPG x hx, hPG y hy] using hh
  have hchange (k : E → ℝ) : (∫ x in V, k x ∂μ) =
      ∫ y in U, |(fderiv ℝ G y).det| * k (G y) ∂μ := by
    rw [← himage]
    simpa only [smul_eq_mul] using integral_image_eq_integral_abs_det_fderiv_smul μ
      hU.measurableSet (fun y _ => (hG.differentiable (by simp) y).hasFDerivAt.hasFDerivWithinAt)
      hinj k
  intro φ hφ hs hφU
  obtain ⟨ψ, hψ, hψs, hψV, hψG, hdψG⟩ :=
    exists_compact_chart_test hU hV hVb hG hP hGU hPG φ hφ hs hφU
  have hJQ (y) (hy : y ∈ U) :
      (fderiv ℝ G y).comp (fderiv ℝ P (G y)) = ContinuousLinearMap.id ℝ E := by
    have he : (fun x => G (P x)) =ᶠ[𝓝 (G y)] id := by
      filter_upwards [hV.mem_nhds (hGU hy)] with x hx
      exact hGP x hx
    have hc := ((hG.differentiable (by simp) (P (G y))).hasFDerivAt.comp (G y)
      (hP.differentiable (by simp) (G y)).hasFDerivAt).fderiv
    rw [hPG y hy] at hc
    have hh := hc.symm.trans he.fderiv_eq
    simpa using hh
  have hpull (y) (hy : y ∈ U) :
      fderiv ℝ φ y (fderiv ℝ P (G y) (H (G y))) = fderiv ℝ ψ (G y) (H (G y)) := by
    have hd := congrArg (fun T => T (fderiv ℝ P (G y) (H (G y)))) (hdψG y hy)
    have hi := congrArg (fun T => T (H (G y))) (hJQ y hy)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hd hi
    rw [hi] at hd
    exact hd.symm
  have hψleft : (∫ x in V, fderiv ℝ ψ x (H x) ∂μ) =
      ∫ x, fderiv ℝ ψ x (H x) ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [fderiv_of_notMem_tsupport ℝ (fun ht => hx (hψV ht))]
    rfl
  have hψright : (∫ x in V, f x * ψ x ∂μ) = ∫ x, f x * ψ x ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hψV ht))]
    ring
  have hφleft : (∫ y in U, fderiv ℝ φ y
      (|(fderiv ℝ G y).det| • fderiv ℝ P (G y) (H (G y))) ∂μ) =
      ∫ y, fderiv ℝ φ y (|(fderiv ℝ G y).det| • fderiv ℝ P (G y) (H (G y))) ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [fderiv_of_notMem_tsupport ℝ (fun ht => hy (hφU ht))]
    rfl
  have hφright : (∫ y in U, (|(fderiv ℝ G y).det| * f (G y)) * φ y ∂μ) =
      ∫ y, (|(fderiv ℝ G y).det| * f (G y)) * φ y ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hy (hφU ht))]
    ring
  rw [← hφleft, ← hφright]
  calc
    (∫ y in U, fderiv ℝ φ y (|(fderiv ℝ G y).det| • fderiv ℝ P (G y) (H (G y))) ∂μ) =
        ∫ y in U, |(fderiv ℝ G y).det| * fderiv ℝ ψ (G y) (H (G y)) ∂μ := by
      apply setIntegral_congr_fun hU.measurableSet
      intro y hy
      dsimp only
      rw [map_smul, smul_eq_mul, hpull y hy]
    _ = ∫ x in V, fderiv ℝ ψ x (H x) ∂μ :=
      (hchange (fun x => fderiv ℝ ψ x (H x))).symm
    _ = ∫ x in V, f x * ψ x ∂μ := by rw [hψleft, hψright]; exact hweak ψ hψ hψs hψV
    _ = ∫ y in U, (|(fderiv ℝ G y).det| * f (G y)) * φ y ∂μ := by
      rw [hchange]
      apply setIntegral_congr_fun hU.measurableSet
      intro y hy
      dsimp only
      rw [hψG y hy]
      ring

end OAI.Analysis.PDE.Weak
