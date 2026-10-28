import OAI.Analysis.PDE.Schauder.Dirichlet.PathFourthChart
import OAI.Analysis.Calculus.SmoothExtension.Periodic.ChartFiniteFields
import OAI.Analysis.PDE.Elliptic.Boundary.PhysicalSmoothChart
import OAI.Analysis.PDE.Elliptic.Boundary.HalfPatchClosure
import OAI.Analysis.PDE.Elliptic.Boundary.Fourth.Coverage
import OAI.Analysis.PDE.Elliptic.Boundary.Fourth.Restriction
import OAI.Analysis.Calculus.SmoothExtension.BoundaryFourthPeriodicChart

noncomputable section
open Set Filter Metric Module
open scoped ContDiff Topology ComplexOrder
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Elliptic OAI.LinearAlgebra.Moore OAI.Analysis.Calculus.SmoothExtension

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Nontrivial V]
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n+1) 4
local notation "X" => EuclideanSpace ℝ (Fin ((n+1)*4))
local instance pathFourthBoundary1Group : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance pathFourthBoundary1Space : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance pathFourthBoundary2Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pathFourthBoundary2Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pathFourthBoundary3Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pathFourthBoundary3Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- The actual full nonlinear potential has a uniform fourth-order bound
near every boundary point. The neighborhood and constant precede the solution. -/
theorem InteriorThirdPathData.boundary_fourth_estimate
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK)
    (hr : ContDiff ℝ ∞ r) (hB₀ : ContDiff ℝ 5 B₀)
    (hF₀ : ContDiff ℝ 3 F₀) (hF₁ : ContDiff ℝ 3 F₁)
    (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat r) (hBp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat B₀)
    (hp₀ : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat F₀) (hp₁ : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat F₁)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K) [Nonempty {x | r x ≤ 0}]
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hrpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x)
    {a : E} (hra : r a = 0) :
    ∃ ρ > 0, ∃ C > 0, ∀ s : OAI.Analysis.PDE.Dirichlet.SmoothPathSolution e lat r B₀ F₀ F₁,
      OAI.Analysis.PDE.Elliptic.HasFourthHolderBound (closedBall a ρ ∩ {x | r x ≤ 0}) (d.exponent/2)
        (fun y => B₀ y+s.u y) C := by
  classical
  let e₀ : X ≃ₗᵢ[ℝ] E := (OAI.Analysis.PDE.Dirichlet.flattenFourSlots (n+1)).symm
  let k : Fin ((n+1)*4) := ⟨0,by omega⟩
  obtain ⟨c,G,Q,δ,T,hc,hG,hQ,hG0,hchart,hδ,hT,hTp,htan,hTg⟩ :=
    OAI.Analysis.Calculus.SmoothExtension.exists_periodic_fourth_boundary_chart e lat e₀ k hr hrp a (hreg a hra)
  have h0 : (0 : E) ∈ closedBall 0 2 := mem_closedBall_self (by norm_num)
  let S := OAI.Analysis.PDE.Elliptic.positiveIsometryHalfPatch e₀ k
  let D := closure S ∩ closedBall 0 δ
  have hSC : IsCompact (closure S) := OAI.Analysis.PDE.Elliptic.isCompact_closure_positiveIsometryHalfPatch e₀ k
  have hSc : Convex ℝ S := OAI.Analysis.PDE.Elliptic.convex_positiveIsometryHalfPatch e₀ k
  obtain ⟨hball,hGK,hGΩ⟩ := OAI.Analysis.Calculus.SmoothExtension.fourth_positive_chart_properties e₀ k hra hc G
    (fun z hz => (hchart z hz).2)
  obtain ⟨M,hM,hfourth⟩ := d.uniform_fourth_chart_estimate e lat hK hr hB₀ hF₀ hF₁
    hrp hBp hp₀ hp₁ hbounded hreg hrpos hpos₀ hpos₁ e₀ k G Q
    (hG.of_le (by simp)) (hQ.of_le (by simp)) (OAI.Analysis.PDE.Elliptic.isOpen_positiveIsometryHalfPatch e₀ k)
    hSc hSC (OAI.Analysis.PDE.Elliptic.diameter_positiveIsometryHalfPatch e₀ k) hGK hGΩ
    (hSC.inter_right isClosed_closedBall) (hSc.closure.inter (convex_closedBall 0 δ))
    (fun _ hx => hx.1) (fun z hz => (hchart z (hball hz.1)).1)
    T (fun i => (hT i).of_le (by simp)) hTp htan (fun i z hz => hTg i z hz.2)
  have hne : {x | r x ≤ 0}.Nonempty := ⟨a,hra.le⟩
  obtain ⟨L,hL,hlower⟩ := d.uniform_subtracted_chart_jets (by omega) e lat hK hr
    (hB₀.of_le (by norm_num)) (hF₀.of_le (by norm_num)) (hF₁.of_le (by norm_num))
    hrp hBp hp₀ hp₁ hbounded hne hreg hpos₀ hpos₁ G (hG.of_le (by simp))
    (OAI.Analysis.PDE.Elliptic.isOpen_positiveIsometryHalfPatch e₀ k) hSc hSC (OAI.Analysis.PDE.Elliptic.diameter_positiveIsometryHalfPatch e₀ k) hGK hGΩ
  let ε := min δ (1/2)
  have hε : 0 < ε := lt_min hδ (by norm_num)
  let A := ball (0 : E) ε ∩ {z | 0 ≤ (e₀.symm z) k}
  have hAS : A ⊆ closure S := by
    intro z hz
    rw [OAI.Analysis.PDE.Elliptic.closure_positiveIsometryHalfPatch]
    refine ⟨?_,hz.2⟩
    have hzε : ‖z‖ < ε := by simpa only [mem_ball,dist_zero_right] using hz.1
    simpa only [mem_closedBall,dist_zero_right,e₀.symm.norm_map] using
      hzε.le.trans (min_le_right δ (1/2))
  have hAD : A ⊆ D := by
    intro z hz
    exact ⟨hAS hz,closedBall_subset_closedBall (min_le_left δ (1/2))
      (ball_subset_closedBall hz.1)⟩
  have hα : 0 ≤ d.exponent/2 := (half_pos d.exponent_pos).le
  have hα1 : d.exponent/2 ≤ 1 := by linarith [d.exponent_lt_one]
  obtain ⟨ρ,hρ,C,hC,hreturn⟩ := OAI.Analysis.PDE.Elliptic.exists_physical_fourth_return hc hr.continuous
    (hQ.of_le (by simp)) (hG.of_le (by simp)) hG0 (hchart 0 h0).1
    (fun z hz => (hchart z hz).2) hra B₀ hB₀ hα hα1 hε
  refine ⟨ρ,hρ,C*(1+L+M),mul_pos hC (by positivity),?_⟩
  intro s
  obtain ⟨hlo,Ds,hDs,hDsn⟩ := hlower s
  have heq : (fun z => (B₀ (G z)+s.u (G z))-B₀ (G z)) = s.u ∘ G := by
    funext z; dsimp only [Function.comp_apply]; ring
  apply hreturn _ ((hB₀.of_le (by norm_num)).add s.smooth) L M hL.le hM.le
  · rw [heq]
    exact ⟨fun x hx => hlo.value x (hAS hx),fun x hx => hlo.first x (hAS hx),
      fun x hx => hlo.second x (hAS hx),fun x hx y hy => hlo.value_sub x (hAS hx) y (hAS hy),
      fun x hx y hy => hlo.first_sub x (hAS hx) y (hAS hy),
      fun x hx y hy => hlo.second_sub x (hAS hx) y (hAS hy)⟩
  · rw [heq]
    intro z hz
    rw [← hDs ⟨z,hAS hz⟩]
    exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le Ds _).trans hDsn
  · rw [heq]
    intro z hz w hw
    rw [← hDs ⟨z,hAS hz⟩,← hDs ⟨w,hAS hw⟩]
    exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le Ds _ _).trans (by
      simpa only [Subtype.dist_eq,dist_eq_norm] using
        mul_le_mul_of_nonneg_right hDsn (Real.rpow_nonneg (dist_nonneg (x := (⟨z,hAS hz⟩ : closure S))
          (y := ⟨w,hAS hw⟩)) (d.exponent/2)))
  · rw [heq]
    exact (hfourth s).restrict hAD hα

end OAI.Analysis.PDE.Schauder
