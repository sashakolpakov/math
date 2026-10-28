import OAI.Analysis.Calculus.SmoothExtension.Periodic.TangentExtension
import OAI.Analysis.PDE.Elliptic.PeriodicChartCoverage
import OAI.Analysis.PDE.Elliptic.Boundary.Chart.Fields

noncomputable section
open Set Filter Metric Module
open scoped Topology ContDiff
namespace OAI.Analysis.Calculus.SmoothExtension

open OAI.Analysis.PDE.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem contDiff_chartTangentField_infty {G P : E → E}
    (hG : ContDiff ℝ ∞ G) (hP : ContDiff ℝ ∞ P) (v : E) :
    ContDiff ℝ ∞ (OAI.Analysis.PDE.Elliptic.chartTangentField G P v) := by
  have hDG : ContDiff ℝ ∞ (fderiv ℝ G) := hG.fderiv_right (by simp)
  exact (hDG.comp hP).clm_apply contDiff_const

omit [FiniteDimensional ℝ E] in
theorem chartTangentField_tangent_of_linear_level
    {G P : E → E} {r : E → ℝ} (hG : Differentiable ℝ G) (hr : Differentiable ℝ r)
    {U W : Set E} (hW : IsOpen W) (hmap : MapsTo P U W)
    (hinv : ∀ x ∈ U, G (P x) = x)
    (ℓ : E →L[ℝ] ℝ) (c : ℝ) (hlevel : ∀ z ∈ W, r (G z) = c + ℓ z)
    (v : E) (hv : ℓ v = 0) :
    ∀ x ∈ U, fderiv ℝ r x (OAI.Analysis.PDE.Elliptic.chartTangentField G P v x) = 0 := by
  intro x hx
  have hlocal : (fun z ↦ r (G z)) =ᶠ[𝓝 (P x)] (fun z ↦ c + ℓ z) := by
    filter_upwards [hW.mem_nhds (hmap hx)] with z hz
    exact hlevel z hz
  have hleft : HasFDerivAt (fun z ↦ r (G z))
      ((fderiv ℝ r (G (P x))).comp (fderiv ℝ G (P x))) (P x) :=
    (hr (G (P x))).hasFDerivAt.comp (P x) (hG (P x)).hasFDerivAt
  have hright : HasFDerivAt (fun z ↦ c + ℓ z) ℓ (P x) := by
    exact ℓ.hasFDerivAt.const_add c
  have hd : (fderiv ℝ r (G (P x))).comp (fderiv ℝ G (P x)) = ℓ :=
    hleft.fderiv.symm.trans (hlocal.fderiv_eq.trans hright.fderiv)
  have he := congrArg (fun A : E →L[ℝ] ℝ ↦ A v) hd
  simpa only [ContinuousLinearMap.comp_apply, hinv x hx, OAI.Analysis.PDE.Elliptic.chartTangentField, hv] using he

variable {m : ℕ} {P₀ V₀ ι : Type*}
  [NormedAddCommGroup P₀] [NormedSpace ℝ P₀]
  [NormedAddCommGroup V₀] [NormedSpace ℝ V₀] [Fintype ι]

/-- A genuine coordinate tangent field has a globally smooth periodic
extension agreeing in a physical neighborhood, and tangent at every point
of the entire periodic boundary. -/
theorem exists_latticePeriodic_chart_tangent
    (e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] P₀ × V₀) (lat : Basis ι ℝ P₀)
    (k : Fin m) {r : EuclideanSpace ℝ (Fin m) → ℝ}
    (hr : ContDiff ℝ ∞ r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat r)
    {G P : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    (hG : ContDiff ℝ ∞ G) (hP : ContDiff ℝ ∞ P)
    {a : EuclideanSpace ℝ (Fin m)} (hG0 : G 0 = a)
    (hinv : (fun z ↦ P (G z)) =ᶠ[𝓝 (0 : EuclideanSpace ℝ (Fin m))] id)
    (c : ℝ) (hlevel : ∀ z ∈ closedBall 0 2, r (G z) - r a = -c * z k)
    (v : EuclideanSpace ℝ (Fin m)) (hv : v k = 0) :
    ∃ T : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m),
      ContDiff ℝ ∞ T ∧ OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat T ∧
      (∀ x, r x = 0 → fderiv ℝ r x (T x) = 0) ∧
      ∃ O : Set (EuclideanSpace ℝ (Fin m)), IsOpen O ∧ a ∈ O ∧
        EqOn T (OAI.Analysis.PDE.Elliptic.chartTangentField G P v) O := by
  obtain ⟨hPa, R, hR, U, hU, haU, hRU, hGP, hPU⟩ :=
    OAI.Analysis.PDE.Elliptic.exists_inverse_chart_neighborhood (hP.of_le (by simp)) (hG.of_le (by simp))
      hG0 hinv (show (0 : ℝ) < 1 by norm_num)
  have ht := chartTangentField_tangent_of_linear_level
    (hG.differentiable (by simp)) (hr.differentiable (by simp)) isOpen_ball hPU hGP
    ((-c) • EuclideanSpace.proj k) (r a) (by
      intro z hz
      have hz2 : z ∈ closedBall (0 : EuclideanSpace ℝ (Fin m)) 2 :=
        ball_subset_closedBall ((ball_subset_ball (show (1 : ℝ) ≤ 2 by norm_num)) hz)
      have he := hlevel z hz2
      change r (G z) = r a + -c * z k
      linarith) v (by simp [hv])
  obtain ⟨T, hT, hTp, hTtan, O, hO, haO, hOU, heq⟩ :=
    exists_latticePeriodic_tangent_extension e lat r hrp hU haU
      (OAI.Analysis.PDE.Elliptic.chartTangentField G P v) (contDiff_chartTangentField_infty hG hP v)
      (fun x hx _ ↦ ht x hx)
  exact ⟨T, hT, hTp, hTtan, O, hO, haO, heq⟩

end OAI.Analysis.Calculus.SmoothExtension
