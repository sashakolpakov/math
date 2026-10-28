import OAI.Analysis.PDE.Dirichlet.Boundary.ChartSchauder
import OAI.Analysis.PDE.Elliptic.DirichletCoordinateChart
import OAI.Analysis.PDE.Elliptic.PeriodicChartCoverage
import OAI.Analysis.PDE.Dirichlet.Periodic.Chart.SchauderReturn

open Set Metric InnerProductSpace
open scoped Topology Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.PDE.Elliptic OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

/-- At a regular boundary point, the actual physical solution has a
uniform local Schauder estimate. The radius precedes the small error,
and all constants precede the coefficients, forcing, and solution. -/
theorem boundary_pointwise_schauder (hm : 3 ≤ m) (k : Fin m)
    (r : E → ℝ) (hr : ContDiff ℝ 3 r) (a : E)
    (hra : r a = 0) (hreg : fderiv ℝ r a ≠ 0)
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    {ell Λ N α : ℝ} (hell : 0 < ell) (hΛ : 0 ≤ Λ) (hN : 0 ≤ N)
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ δ > 0, ∀ ε > 0, ∃ D > 0,
      ∀ A : E → E →L[ℝ] E, Continuous A →
      (∀ x, r x ≤ 0 → (A x).toLinearMap.IsSymmetric) →
      (∀ x, r x ≤ 0 → ∀ v : E, ell * ‖v‖^2 ≤ inner ℝ v (A x v)) →
      (∀ x, r x ≤ 0 → ∀ v : E, inner ℝ v (A x v) ≤ Λ * ‖v‖^2) →
      (∀ x, r x ≤ 0 → ‖A x‖ ≤ N) →
      (∀ x, r x ≤ 0 → ∀ y, r y ≤ 0 → ‖A x-A y‖ ≤ N * dist x y^α) →
      ∀ u : E → ℝ, ContDiff ℝ 3 u →
      (∀ x, r x = 0 → u x = 0) →
      ∀ (F : E → ℝ) (B M : ℝ), 0 ≤ B → 0 ≤ M →
      (∀ x, r x ≤ 0 → |F x| ≤ B) →
      (∀ x, r x ≤ 0 → ∀ y, r y ≤ 0 → |F x-F y| ≤ B * dist x y^α) →
      (∀ x, r x ≤ 0 → |u x| ≤ M) →
      (∀ x, r x ≤ 0 → OAI.Analysis.PDE.Elliptic.ellipticTrace A u x = F x) →
      ∀ U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α,
      (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.value U x = u x) →
      (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x = fderiv ℝ u x) →
      (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x = fderiv ℝ (fderiv ℝ u) x) →
      SchauderJetBoundsOn u (closedBall a δ ∩ {x | r x ≤ 0})
        α (ε*‖U‖+D*(B+M)) := by
  obtain ⟨c, C, G, P, hc, hC, hG, hP, hG0, hchart⟩ :=
    OAI.Analysis.PDE.Elliptic.exists_bounded_coordinate_chart k hr a hreg isOpen_univ (mem_univ a)
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have h0 : (0 : E) ∈ closedBall 0 2 := mem_closedBall_self (by norm_num)
  have hsmall (z : E) (hz : z ∈ OAI.Analysis.PDE.Elliptic.closedCoordinateHalfPatch k 0 (1/2)) :
      z ∈ closedBall 0 2 := (closedBall_subset_closedBall (by norm_num)) hz.1
  have hlevel (z : E) (hz : z ∈ closedBall 0 2) : r (G z) = -c*z k := by
    simpa only [hra, sub_zero] using (hchart z hz).2.2.1
  have himage : MapsTo G (OAI.Analysis.PDE.Elliptic.closedCoordinateHalfPatch k 0 (1/2)) {x | r x ≤ 0} := by
    intro z hz
    change r (G z) ≤ 0
    rw [hlevel z (hsmall z hz)]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) hz.2
  obtain ⟨δ₀, hδ₀, hlocal⟩ := boundary_chart_schauder hm k G P hG hP
    (hΩK := hΩD) himage (fun z hz => (hchart z (hsmall z hz)).2.1)
    hCpos (hchart 0 h0).2.2.2.1 (hchart 0 h0).2.2.2.2.2.2
    hell hΛ hN hα hα1
  obtain ⟨_, δ, hδ, V, hV, _, hδV, hGP, _, hPS⟩ :=
    OAI.Analysis.PDE.Elliptic.exists_coordinate_chart_coverage k hc hP hG hG0 (hchart 0 h0).2.1
      (fun z hz => (hchart z hz).2.2.1) hra hδ₀
  have hPSc : MapsTo P (closedBall a δ ∩ {x | r x ≤ 0})
      (OAI.Analysis.PDE.Elliptic.closedCoordinateHalfPatch k 0 δ₀) := by
    intro x hx
    exact ⟨ball_subset_closedBall (hPS hx).1, (hPS hx).2⟩
  obtain ⟨CR, hCR, hreturn⟩ := exists_closedBall_chart_schauder_return_bound G P hG hP a δ
    (OAI.Analysis.PDE.Elliptic.convex_closedCoordinateHalfPatch k 0 δ₀) hPSc hV (fun x hx => hδV hx.1) hGP hα.le hα1.le
  refine ⟨δ, hδ, ?_⟩
  intro ε hε
  obtain ⟨D, hD, hestimate⟩ := hlocal (ε/(CR+1)) (div_pos hε (by positivity))
  refine ⟨CR*D, mul_pos hCR hD, ?_⟩
  intro A hA hAs hAl hAu hAn hAh u hu hu0 F B M hB hM hFn hFh hun heq U hU0 hU1 hU2
  have hzero (z : E) (hz : z ∈ OAI.Analysis.PDE.Elliptic.closedCoordinateHalfPatch k 0 (1/2)) (hzk : z k = 0) :
      u (G z) = 0 := by
    apply hu0
    rw [hlevel z (hsmall z hz), hzk, mul_zero]
  have hb := hestimate A hA hAs hAl hAu hAn hAh u hu hzero F B M hB hM
    hFn hFh hun heq U hU0 hU1 hU2
  have hbound : 0 ≤ ε/(CR+1)*‖U‖+D*(B+M) := by positivity
  obtain ⟨h0, h1, h2, hH⟩ := hreturn u (hu.of_le (by norm_num)) _ hbound
    hb.value hb.first hb.second hb.second_holder
  have hback : SchauderJetBoundsOn u (closedBall a δ ∩ {x | r x ≤ 0}) α
      (CR*(ε/(CR+1)*‖U‖+D*(B+M))) := ⟨h0, h1, h2, hH⟩
  apply hback.mono_bound
  have hcsmall : CR/(CR+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hsmall' := mul_le_mul_of_nonneg_right hcsmall (mul_nonneg hε.le (norm_nonneg U))
  calc
    _ = (CR/(CR+1))*(ε*‖U‖)+(CR*D)*(B+M) := by ring
    _ ≤ ε*‖U‖+(CR*D)*(B+M) :=
      add_le_add (by simpa only [one_mul] using hsmall') le_rfl

end OAI.Analysis.PDE.Dirichlet
