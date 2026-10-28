import OAI.Analysis.PDE.Dirichlet.Rough.GeometricBoundary
import OAI.Analysis.PDE.Elliptic.Calculus.SmoothCoordinateChart
import OAI.Analysis.PDE.Elliptic.PeriodicChartCoverage
import OAI.Analysis.PDE.Dirichlet.Moore.GlobalSchauderGeometry

noncomputable section
open Set Filter Metric Module
open scoped Topology ContDiff Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Elliptic

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "X" => EuclideanSpace ℝ (Fin (n*4))
local notation "Y" => CoordinateSpace n 4

/-- At every regular physical boundary point, the genuine geometric
solution curves produce an actual C⁴ extension. The normalized chart,
two-way inverse neighborhood and smaller physical patch are constructed
inside the proof. -/
theorem HasGeometricSolutionCurves.exists_C4_boundary_representative
    [Nontrivial Y] (hn : 1 ≤ n)
    {e : Y ≃L[ℝ] P × V} {b : Basis ι ℝ P} {r ψ B : Y → ℝ}
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (hc : HasGeometricSolutionCurves e b r ψ B hΩD α)
    (hr : ContDiff ℝ ∞ r) (hrp : LatticePeriodic e b r)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hψ : ContDiff ℝ 2 ψ) (hB : ContDiff ℝ ∞ B)
    (load : Y → ℝ) (hl : ContDiff ℝ ∞ load)
    (hpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)
    (he : ∀ x, r x ≤ 0 → OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) = load x)
    {a : Y} (ha : r a = 0) :
    ∃ O : Set Y, IsOpen O ∧ a ∈ O ∧ ∃ g : Y → ℝ, ContDiff ℝ 4 g ∧
      ∀ x ∈ O, r x ≤ 0 → g x = ψ x := by
  let j : X ≃ₗᵢ[ℝ] Y := (flattenFourSlots n).symm
  let r' : X → ℝ := r ∘ j
  let a' : X := j.symm a
  let k : Fin (n*4) := ⟨0,by omega⟩
  have hr' : ContDiff ℝ ∞ r' := hr.comp j.toContinuousLinearEquiv.contDiff
  have ha' : r' a' = 0 := by simpa [r',a'] using ha
  have hreg' := regular_level_comp_equiv j.toContinuousLinearEquiv
    (hr.differentiable (by simp)) hreg
  obtain ⟨c,C,G₀,P₀,hcpos,hC,hG₀,hP₀,hGzero,hchart⟩ :=
    OAI.Analysis.PDE.Elliptic.exists_smooth_bounded_coordinate_chart k hr' a' (hreg' a' ha') isOpen_univ (mem_univ a')
  have hinv := (hchart 0 (mem_closedBall_self (by norm_num))).2.1
  obtain ⟨hPa,RV,hRV,W,hW,haW,hballW,hGP₀,hPW⟩ :=
    OAI.Analysis.PDE.Elliptic.exists_inverse_chart_neighborhood (hP₀.of_le (by simp)) (hG₀.of_le (by simp))
      hGzero hinv (show (0 : ℝ) < 1 by norm_num)
  have hpre : IsOpen (G₀ ⁻¹' W) := hW.preimage hG₀.continuous
  have hzero : (0 : X) ∈ G₀ ⁻¹' W := by simpa only [mem_preimage,hGzero] using haW
  obtain ⟨ε,hε,hεW⟩ := Metric.isOpen_iff.mp hpre 0 hzero
  let R : ℝ := min 1 ε
  have hR : 0 < R := lt_min zero_lt_one hε
  have hR1 : R ≤ 1 := min_le_left _ _
  have hRε : R ≤ ε := min_le_right _ _
  let G : X → Y := j ∘ G₀
  let P' : Y → X := P₀ ∘ j.symm
  have hG : ContDiff ℝ ∞ G := j.toContinuousLinearEquiv.contDiff.comp hG₀
  have hP : ContDiff ℝ ∞ P' := hP₀.comp j.symm.toContinuousLinearEquiv.contDiff
  have hG0 : G 0 = a := by simp [G,hGzero,a']
  have hlevel (z : X) (hz : z ∈ ball 0 1) : r (G z) = -c * z k := by
    have hb : z ∈ closedBall 0 2 := ball_subset_closedBall (ball_subset_ball (by norm_num) hz)
    have hh := (hchart z hb).2.2.1
    simpa only [ha',sub_zero,r',G,Function.comp_apply] using hh
  have hside (z : X) (hz : z ∈ ({z | 0 ≤ z k} ∩ ball 0 R)) : r (G z) ≤ 0 := by
    rw [hlevel z (ball_subset_ball hR1 hz.2)]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hcpos.le) hz.1
  have hPG (z : X) (hz : z ∈ ({z | 0 ≤ z k} ∩ ball 0 R)) :
      (fun y ↦ P' (G y)) =ᶠ[𝓝 z] id := by
    have hb : z ∈ closedBall 0 2 :=
      ball_subset_closedBall (ball_subset_ball (hR1.trans (by norm_num)) hz.2)
    simpa only [G,P',Function.comp_apply,j.symm_apply_apply] using (hchart z hb).2.1
  have hGP (z : X) (hz : z ∈ ({z | 0 ≤ z k} ∩ ball 0 R)) :
      (fun y ↦ G (P' y)) =ᶠ[𝓝 (G z)] id := by
    have hzW : G₀ z ∈ W := hεW (ball_subset_ball hRε hz.2)
    have hw : G z ∈ j.symm ⁻¹' W := by simpa [G] using hzW
    filter_upwards [(hW.preimage j.symm.continuous).mem_nhds hw] with y hy
    change j (G₀ (P₀ (j.symm y))) = y
    rw [hGP₀ _ hy,j.apply_symm_apply]
  obtain ⟨ρ,hρ,hρR,g,hg,hgeq⟩ := hc.exists_C4_chart_representative j
    (hr.of_le (by simp)) hrp hreg hψ hB G P' hG hP load hl
    (EuclideanSpace.proj k) (EuclideanSpace.single k 1) (by simp) hR
    hside hPG hGP c hlevel (fun z hz ↦ hpos _ (hside z hz)) (fun z hz ↦ he _ (hside z hz))
  let O : Set Y := (j.symm ⁻¹' W) ∩ P' ⁻¹' ball 0 ρ
  have hO : IsOpen O := (hW.preimage j.symm.continuous).inter (isOpen_ball.preimage hP.continuous)
  have haO : a ∈ O := by
    refine ⟨haW,?_⟩
    change dist (P₀ (j.symm a)) 0 < ρ
    rw [show P₀ (j.symm a) = 0 from hPa,dist_self]
    exact hρ
  refine ⟨O,hO,haO,fun x ↦ g (P' x),hg.comp (hP.of_le (by simp)),?_⟩
  intro x hx hxr
  have hGPx : G (P' x) = x := by
    change j (G₀ (P₀ (j.symm x))) = x
    rw [hGP₀ _ hx.1,j.apply_symm_apply]
  have hPx1 : P' x ∈ ball 0 1 := ball_subset_ball (hρR.trans hR1) hx.2
  have hsign : 0 ≤ (P' x) k := by
    have hh := hlevel (P' x) hPx1
    rw [hGPx] at hh
    nlinarith
  exact (hgeq ⟨hsign,ball_subset_closedBall hx.2⟩).trans (congrArg ψ hGPx)

end OAI.Analysis.PDE.Dirichlet
