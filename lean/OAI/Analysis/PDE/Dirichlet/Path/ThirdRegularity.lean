import OAI.Analysis.PDE.Schauder.Dirichlet.PathThirdGlobal
import OAI.Analysis.PDE.Dirichlet.Path.ThirdLimit
import OAI.Analysis.PDE.Dirichlet.Closed.HigherRegularity

open Set Module Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => CoordinateSpace n 4
local instance pathRegThirdFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance pathRegThirdFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance pathRegThirdSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pathRegThirdSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pathRegThirdThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pathRegThirdThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- The actual Banach path limit is C³ on the entire closed physical
domain once the remaining boundary-center estimate has been proved. All
lower-derivative bounds come from the already constructed path data. -/
theorem BanachPathLimit.contDiffOn_three_closed_of_boundary
    (hn : 1 ≤ n) (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : OAI.Analysis.PDE.Schauder.InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK)
    (hr : ContDiff ℝ 3 r) (hB₀ : ContDiff ℝ 4 B₀)
    (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    (hrp : LatticePeriodic e lat r) (hBp : LatticePeriodic e lat B₀)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hb : OAI.Analysis.PDE.Schauder.BoundaryThirdPathEstimate d)
    {β t : ℝ} {s : ℕ → SmoothPathSolution e lat r B₀ F₀ F₁}
    (L : BanachPathLimit e lat r B₀ F₀ F₁ hΩK β s t) :
    ContDiffOn ℝ 3 (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value L.value)) {x | r x ≤ 0} := by
  let : NeZero n := ⟨by omega⟩
  obtain ⟨M,hM,hbound⟩ := d.uniform_third_bounds_of_boundary
    e lat hK (by omega) hr.continuous hB₀ hF₀ hF₁ hrp hBp hbounded hb
  have h₀ (j : ℕ) (x : E) (hx : r x ≤ 0) :
      ‖B₀ x+(s j).u x‖ ≤ d.normBound := by
    rw [← d.jet_value (s j) ⟨x,hx⟩]
    exact ((OAI.Analysis.Normed.Function.Holder.C2Holder.value (d.jets (s j))).norm_coe_le_norm ⟨x,hx⟩).trans
      ((OAI.Analysis.Normed.Function.Holder.C2Holder.norm_value_le (d.jets (s j))).trans (d.jet_norm (s j)))
  have h₁ (j : ℕ) (x : E) (hx : r x ≤ 0) :
      ‖fderiv ℝ (fun y => B₀ y+(s j).u y) x‖ ≤ d.normBound := by
    rw [← d.jet_first (s j) ⟨x,hx⟩]
    exact ((OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative (d.jets (s j))).norm_coe_le_norm ⟨x,hx⟩).trans
      ((OAI.Analysis.Normed.Function.Holder.C2Holder.norm_firstDerivative_le (d.jets (s j))).trans (d.jet_norm (s j)))
  have h₂ (j : ℕ) (x : E) (hx : r x ≤ 0) :
      ‖fderiv ℝ (fderiv ℝ (fun y => B₀ y+(s j).u y)) x‖ ≤ d.normBound := by
    rw [← d.jet_second (s j) ⟨x,hx⟩]
    have hnorm : ‖OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative (d.jets (s j)) ⟨x,hx⟩‖ ≤ ‖d.jets (s j)‖ :=
      (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le (d.jets (s j)).val.2.2 ⟨x,hx⟩).trans
        ((le_max_right _ _).trans (le_max_right _ _))
    exact hnorm.trans (d.jet_norm (s j))
  have hu (j : ℕ) : ContDiff ℝ 3 (fun x => B₀ x+(s (L.subsequence j)).u x) :=
    (hB₀.add ((s (L.subsequence j)).smooth)).of_le (by norm_num)
  have hv (x : E) (hx : r x < 0) :
      Tendsto (fun j => B₀ x+(s (L.subsequence j)).u x) atTop
        (𝓝 (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value L.value) x)) := by
    rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply (OAI.Analysis.Normed.Function.Holder.C2Holder.value L.value) (x := x) hx.le]
    exact L.converges ⟨x,hx.le⟩
  obtain ⟨hC₃,T,_,hT⟩ := exists_closed_third_derivative_of_uniform_bound
    hr hreg _ hu _ hv d.exponent_pos d.normBound_pos.le d.normBound_pos.le hM.le
    (fun j => h₀ (L.subsequence j)) (fun j => h₁ (L.subsequence j))
    (fun j => h₂ (L.subsequence j)) (fun j => (hbound (s (L.subsequence j))).1)
    (fun j => (hbound (s (L.subsequence j))).2)
  exact OAI.Analysis.PDE.Dirichlet.C2Holder.contDiffOn_three_closed_of_trace hr hreg L.value hC₃ (OAI.Analysis.Normed.Function.Holder.HolderMap.value T) hT

end OAI.Analysis.PDE.Dirichlet
