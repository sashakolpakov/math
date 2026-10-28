import OAI.Analysis.PDE.Dirichlet.Path.BanachSubsequence
import OAI.Analysis.PDE.Dirichlet.Path.LimitData

open Set Module Filter
open scoped Topology BoundedContinuousFunction Matrix.Norms.Elementwise ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore OAI.Analysis.Normed.Function.Holder

local instance pathFirstNormedGroup (n : ℕ) :
    NormedAddCommGroup (CoordinateSpace (n + 1) 4 →L[ℝ] ℝ) := inferInstance
local instance pathFirstNormedSpace (n : ℕ) :
    NormedSpace ℝ (CoordinateSpace (n + 1) 4 →L[ℝ] ℝ) := inferInstance
local instance pathSecondNormedGroup (n : ℕ) :
    NormedAddCommGroup (CoordinateSpace (n + 1) 4 →L[ℝ] CoordinateSpace (n + 1) 4 →L[ℝ] ℝ) :=
  inferInstance
local instance pathSecondNormedSpace (n : ℕ) :
    NormedSpace ℝ (CoordinateSpace (n + 1) 4 →L[ℝ] CoordinateSpace (n + 1) 4 →L[ℝ] ℝ) :=
  inferInstance

variable {n : ℕ} {P V ι : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    (e : CoordinateSpace (n + 1) 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : CoordinateSpace (n + 1) 4 → ℝ} (hr : ContDiff ℝ 3 r)
    (hB₀ : ContDiff ℝ 4 B₀) (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    (hrper : LatticePeriodic e lat r) (hBper : LatticePeriodic e lat B₀)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x)
    {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α N : ℝ} (hα : 0 < α) (hN : 0 ≤ N)
    (s : ℕ → SmoothPathSolution e lat r B₀ F₀ F₁)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hslim : Tendsto (fun k ↦ (s k).t) atTop (𝓝 t))
    (Φ : SmoothPathSolution e lat r B₀ F₀ F₁ → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α)
    (hΦ : ∀ s, ‖Φ s‖ ≤ N ∧
      (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.value (Φ s) x = B₀ x + s.u x) ∧
      (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative (Φ s) x =
        fderiv ℝ (fun z ↦ B₀ z + s.u z) x) ∧
      (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative (Φ s) x =
        fderiv ℝ (fderiv ℝ (fun z ↦ B₀ z + s.u z)) x) ∧
      LatticePeriodic e lat (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value (Φ s))))

include hK hr hB₀ hF₀ hF₁ hrper hBper hbounded hreg hpos₀ hpos₁ hα hN ht hslim hΦ

theorem nonempty_densityPath_banach_limit_of_bound :
    Nonempty (BanachPathLimit e lat r B₀ F₀ F₁ hΩK (α / 2) s t) := by
  have hsub := exists_densityPath_banach_subsequence
    (n := n) (P := P) (V := V) (ι := ι) (K := K) (r := r) (B₀ := B₀)
    (F₀ := F₀) (F₁ := F₁) (hΩK := hΩK) (α := α) (N := N)
    e lat hK hr hB₀ hrper hBper hbounded hreg hα hN s Φ hΦ
  obtain ⟨g, φ, hφ, hlim⟩ := hsub
  obtain ⟨hp, hbdy, heq, hpoint⟩ := densityPath_banach_limit_properties e lat hr hB₀ hF₀ hF₁
    hreg hpos₀ hpos₁ (fun k ↦ s (φ k)) ht (hslim.comp hφ.tendsto_atTop)
    (fun k ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.lowerHalf hα.le (Φ (s (φ k)))) g hlim
    (fun k ↦ (hΦ (s (φ k))).2.1) (fun k ↦ (hΦ (s (φ k))).2.2.2.1)
    (fun k ↦ (hΦ (s (φ k))).2.2.2.2)
  exact ⟨⟨g, hp, hbdy, heq, φ, hφ, hpoint⟩⟩

end OAI.Analysis.PDE.Dirichlet
