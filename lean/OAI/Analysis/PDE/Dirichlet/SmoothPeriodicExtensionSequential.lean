import OAI.Analysis.PDE.Dirichlet.SmoothPeriodicExtensionPath
import OAI.Analysis.PDE.Dirichlet.Path.FourthRegularity
import OAI.Analysis.PDE.Dirichlet.Path.ClosedBanachLimit

/-! Sequential closedness of the actual smooth solution family. The
only extra higher-regularity input is an explicit uniform D³/D⁴ bound. -/

noncomputable section
open Set Module Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore OAI.Analysis.Normed.Function.Holder

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => CoordinateSpace (n+1) 4

local instance seqFirstGroup (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    NormedAddCommGroup (X →L[ℝ] ℝ) := inferInstance
local instance seqFirstSpace (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    NormedSpace ℝ (X →L[ℝ] ℝ) := inferInstance
local instance seqSecondGroup (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    NormedAddCommGroup (X →L[ℝ] X →L[ℝ] ℝ) := inferInstance
local instance seqSecondSpace (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    NormedSpace ℝ (X →L[ℝ] X →L[ℝ] ℝ) := inferInstance
local instance seqThirdGroup (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    NormedAddCommGroup (X →L[ℝ] X →L[ℝ] X →L[ℝ] ℝ) := inferInstance
local instance seqThirdSpace (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    NormedSpace ℝ (X →L[ℝ] X →L[ℝ] X →L[ℝ] ℝ) := inferInstance
local instance seqFourthGroup (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    NormedAddCommGroup (X →L[ℝ] X →L[ℝ] X →L[ℝ] X →L[ℝ] ℝ) := inferInstance
local instance seqFourthSpace (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    NormedSpace ℝ (X →L[ℝ] X →L[ℝ] X →L[ℝ] X →L[ℝ] ℝ) := inferInstance

theorem exists_smoothPathSolution_of_parameter_limit
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : E → ℝ} (hr : ContDiff ℝ ∞ r)
    (hB₀ : ContDiff ℝ 4 B₀) (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    (hrp : LatticePeriodic e b r) (hBp : LatticePeriodic e b B₀)
    (hp₀ : LatticePeriodic e b F₀) (hp₁ : LatticePeriodic e b F₁)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K) (hne : {x | r x ≤ 0}.Nonempty)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x)
    (hbase : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x)).PosSemidef)
    (hdet : ∀ x, r x ≤ 0 → OAI.LinearAlgebra.Moore.mooreDet (n+1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x) = 0)
    (hconvex : ∀ x, r x ≤ 0 →
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x - r₀ •
        (1 : Matrix (Fin (n+1)) (Fin (n+1)) Q))).PosSemidef)
    (s : ℕ → SmoothPathSolution e b r B₀ F₀ F₁) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hlim : Tendsto (fun j => (s j).t) atTop (𝓝 t))
    {γ C₃ C₄ M₃ M₄ : ℝ} (hγ : 0 < γ) (hM₃ : 0 ≤ M₃) (hM₄ : 0 ≤ M₄)
    (h₃ : ∀ j x, r x ≤ 0 →
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => B₀ y+(s j).u y))) x‖ ≤ M₃)
    (h₄ : ∀ j x, r x ≤ 0 →
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => B₀ y+(s j).u y)))) x‖ ≤ M₄)
    (hholder₃ : ∀ j x, r x ≤ 0 → ∀ y, r y ≤ 0 →
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun z => B₀ z+(s j).u z))) x -
        fderiv ℝ (fderiv ℝ (fderiv ℝ (fun z => B₀ z+(s j).u z))) y‖ ≤ C₃*dist x y^γ)
    (hholder₄ : ∀ j x, r x ≤ 0 → ∀ y, r y ≤ 0 →
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fun z => B₀ z+(s j).u z)))) x -
        fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fun z => B₀ z+(s j).u z)))) y‖ ≤ C₄*dist x y^γ) :
    ∃ S : SmoothPathSolution e b r B₀ F₀ F₁, S.t = t := by
  let hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0} :=
    fun x hx => (show r x ≤ 0 from le_of_lt hx)
  have hr₃ : ContDiff ℝ 3 r := hr.of_le (by simp)
  obtain ⟨α, M, hα, hα1, hM, Φ, hΦ⟩ := uniform_banach_bound_densityPath_lattice
    (hΩK := hΩD) e b hK hr₃ hB₀ hF₀ hF₁ hrp hBp hp₀ hp₁ hbounded hne hreg
    hr₀ hpos₀ hpos₁ hbase hdet hconvex
  obtain ⟨L⟩ := nonempty_densityPath_banach_limit_of_bound
    (e := e) (lat := b) (hK := hK) (hr := hr₃) (hB₀ := hB₀)
    (hF₀ := hF₀) (hF₁ := hF₁) (hrper := hrp) (hBper := hBp)
    (hbounded := hbounded) (hreg := hreg) (hpos₀ := hpos₀) (hpos₁ := hpos₁)
    (hα := hα) (hN := hM.le) (s := s) (ht := ht) (hslim := hlim) (Φ := Φ) (hΦ := hΦ)
  have h₀ : ∀ j x, r x ≤ 0 → ‖B₀ x+(s j).u x‖ ≤ M := by
    intro j x hx
    rw [← (hΦ (s j)).2.1 ⟨x, hx⟩]
    exact ((OAI.Analysis.Normed.Function.Holder.C2Holder.value (Φ (s j))).norm_coe_le_norm _).trans
      ((OAI.Analysis.Normed.Function.Holder.C2Holder.norm_value_le (Φ (s j))).trans (hΦ (s j)).1)
  have h₁ : ∀ j x, r x ≤ 0 → ‖fderiv ℝ (fun y => B₀ y+(s j).u y) x‖ ≤ M := by
    intro j x hx
    rw [← (hΦ (s j)).2.2.1 ⟨x, hx⟩]
    exact ((OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative (Φ (s j))).norm_coe_le_norm _).trans
      ((OAI.Analysis.Normed.Function.Holder.C2Holder.norm_firstDerivative_le (Φ (s j))).trans (hΦ (s j)).1)
  have h₂ : ∀ j x, r x ≤ 0 → ‖fderiv ℝ (fderiv ℝ (fun y => B₀ y+(s j).u y)) x‖ ≤ M := by
    intro j x hx
    rw [← (hΦ (s j)).2.2.2.1 ⟨x, hx⟩]
    exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le (OAI.Analysis.Normed.Function.Holder.C2Holder.hessianCLM (Φ (s j))) ⟨x, hx⟩).trans
      ((OAI.Analysis.Normed.Function.Holder.C2Holder.norm_hessianCLM_apply_le (Φ (s j))).trans (hΦ (s j)).1)
  have hfour := L.contDiffOn_four_closed (by omega) hr₃ hB₀ hreg hγ
    hM.le hM.le hM₃ hM₄ h₀ h₁ h₂ h₃ h₄ hholder₃ hholder₄
  obtain ⟨S, hSt, _⟩ := L.exists_smoothPathSolution_of_closed_contDiff (by omega)
    e b hK hr hrp hbounded hreg hB₀ hBp ht hfour
  exact ⟨S, hSt⟩

end OAI.Analysis.PDE.Dirichlet
