import OAI.Analysis.PDE.Schauder.Dirichlet.PathFourthFrame
import OAI.Analysis.PDE.Schauder.Dirichlet.PathFourthCoefficient
import OAI.Analysis.PDE.Schauder.Dirichlet.PathFourthLower
import OAI.Analysis.PDE.Elliptic.Boundary.Fourth.PhysicalData

noncomputable section
open Set Filter Module
open scoped ContDiff Topology ComplexOrder
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Elliptic OAI.LinearAlgebra.Moore OAI.Analysis.Calculus.SmoothExtension

variable {n m : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Nontrivial V]
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n+1) 4
local instance pathFourthChart1Group : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance pathFourthChart1Space : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance pathFourthChart2Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pathFourthChart2Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pathFourthChart3Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pathFourthChart3Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pathFourthChartEndGroup : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance pathFourthChartEndSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance

/-- The fourth-order chart estimate instantiated with actual nonlinear
path solutions. No derivative bounds on the unknown are assumed. -/
theorem InteriorThirdPathData.uniform_fourth_chart_estimate
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
    (e₀ : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] E) (k : Fin m)
    (G Q : E → E) (hG : ContDiff ℝ 4 G) (hQ : ContDiff ℝ 3 Q)
    {S D : Set E} (hS : IsOpen S) (hSc : Convex ℝ S)
    (hcompact : IsCompact (closure S))
    (hdiam : ∀ x ∈ closure S, ∀ y ∈ closure S, ‖x-y‖ ≤ 1)
    (hGK : MapsTo G (closure S) {x | r x ≤ 0}) (hGΩ : MapsTo G S {x | r x < 0})
    (hD : IsCompact D) (hDc : Convex ℝ D) (hDS : D ⊆ closure S)
    (hinv : ∀ z ∈ D, (fun y => Q (G y)) =ᶠ[𝓝 z] id)
    (T : Fin m → E → E) (hT : ∀ i, ContDiff ℝ 4 (T i))
    (hTp : ∀ i, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat (T i))
    (htan : ∀ i, i ≠ k → ∀ x, r x=0 → fderiv ℝ r x (T i x)=0)
    (hTg : ∀ i z, z ∈ D →
      T i =ᶠ[𝓝 (G z)] OAI.Analysis.PDE.Elliptic.chartTangentField G Q (e₀ (EuclideanSpace.single i 1))) :
    ∃ C > 0, ∀ s : OAI.Analysis.PDE.Dirichlet.SmoothPathSolution e lat r B₀ F₀ F₁,
      OAI.Analysis.PDE.Elliptic.HasFourthHolderBound D (d.exponent/2) (s.u ∘ G) C := by
  have hα : 0 ≤ d.exponent/2 := (half_pos d.exponent_pos).le
  have hα1 : d.exponent/2 ≤ 1 := by linarith [d.exponent_lt_one]
  have hne : {x | r x ≤ 0}.Nonempty := by
    obtain ⟨x⟩ := (inferInstance : Nonempty {x | r x ≤ 0})
    exact ⟨x,x.property⟩
  obtain ⟨L,hL,hlower⟩ := d.uniform_subtracted_chart_jets (by omega) e lat hK hr
    (hB₀.of_le (by norm_num)) (hF₀.of_le (by norm_num)) (hF₁.of_le (by norm_num))
    hrp hBp hp₀ hp₁ hbounded hne hreg hpos₀ hpos₁ G hG hS hSc hcompact hdiam hGK hGΩ
  obtain ⟨M,hM,R,hR,hframe⟩ := d.uniform_fourth_frame_data e lat hK hr hB₀ hF₀ hF₁
    hrp hBp hp₀ hp₁ hbounded hreg hrpos hpos₀ hpos₁ T hT hTp k htan
  obtain ⟨N,hN,hcoeff⟩ := d.uniform_det_coefficient_half
  obtain ⟨C,hC,hchart⟩ := OAI.Analysis.PDE.Elliptic.exists_fourth_chart_bound_of_physical_data e₀ hG hQ hD hDc
    (fun x hx => hGK (hDS hx)) (hΩK := hΩK)
    (fun x hx y hy => hdiam x (hDS hx) y (hDS hy)) hinv hα hα1
    d.lower_pos d.upper_nonneg hN.le
  refine ⟨C*(M+R+L),mul_pos hC (by positivity),?_⟩
  intro s
  obtain ⟨_,Ds,hDs,hDsn⟩ := hlower s
  let g : D → closure S := fun x => ⟨x,hDS x.property⟩
  have hg : Isometry g := fun x y => rfl
  let D' := holderIsometricPullback hα g hg Ds
  have hD'n : ‖D'‖ ≤ L := (norm_holderIsometricPullback_le hα g hg Ds).trans hDsn
  have hD' (x : D) : OAI.Analysis.Normed.Function.Holder.HolderMap.value D' x =
      fderiv ℝ (fderiv ℝ (fderiv ℝ (s.u ∘ G))) x := hDs (g x)
  obtain ⟨A,hA,hAn⟩ := hcoeff s
  obtain ⟨hjets,Fs,hFsn,hFs⟩ := hframe s
  exact hchart s.u s.smooth T (fun i => (hT i).of_le (by norm_num)) k hTg
    (fun y => OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun z => B₀ z+s.u z) y))
    A hA hAn (fun _ _ => OAI.Analysis.PDE.Dirichlet.detRealOperator_isSymmetric _)
    (fun x hx v => (d.closed_coefficient_bounds (hr.of_le (by simp)) hreg
      (hB₀.of_le (by norm_num)) s x hx v).1)
    (fun x hx v => (d.closed_coefficient_bounds (hr.of_le (by simp)) hreg
      (hB₀.of_le (by norm_num)) s x hx v).2)
    D' hD' M R L hM.le hR.le hL.le hD'n hjets Fs hFsn hFs

end OAI.Analysis.PDE.Schauder
