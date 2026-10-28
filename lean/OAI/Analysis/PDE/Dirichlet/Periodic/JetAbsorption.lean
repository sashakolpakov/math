import OAI.Analysis.PDE.Dirichlet.Periodic.SchauderAbsorption
import OAI.Analysis.Normed.Function.Holder.C2HolderNorm

open Set Metric Module
open scoped BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

variable {E P V F ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]
local instance periodicAbsorbFirstGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance periodicAbsorbFirstSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance periodicAbsorbSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance periodicAbsorbSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance

/-- Global C²,α absorption for actual periodic jets from a fixed local
cover of the thickened fundamental cell. Only the top derivative requires
local Hölder differences; the lower jets require local supremum bounds. -/
theorem lattice_C2Holder_norm_absorption
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : Continuous r) (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (ρ : ↥(cthickening 1 (latticeSublevelCell e b K r) ∩ {x | r x ≤ 0}) → ℝ)
    (hρ : ∀ x, 0 < ρ x)
    {α : ℝ} (hα : 0 < α) {I : Type*}
    (u : I → E → F) (hup : ∀ i, LatticePeriodic e b (u i))
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (v : I → OAI.Analysis.Normed.Function.Holder.C2Holder (F := F) hΩD α)
    (hv₀ : ∀ i x, OAI.Analysis.Normed.Function.Holder.C2Holder.value (v i) x = u i x)
    (hv₁ : ∀ i x, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative (v i) x = fderiv ℝ (u i) x)
    (hv₂ : ∀ i x, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative (v i) x = fderiv ℝ (fderiv ℝ (u i)) x)
    (N : I → ℝ) (hN : ∀ i, 0 ≤ N i)
    (hlocal : ∀ ε > 0, ∃ D > 0, ∀ i
      (x y : ↥(cthickening 1 (latticeSublevelCell e b K r) ∩ {x | r x ≤ 0})),
      dist y x ≤ ρ x →
        ‖u i y‖ ≤ ε * ‖v i‖ + D * N i ∧
        ‖fderiv ℝ (u i) y‖ ≤ ε * ‖v i‖ + D * N i ∧
        ‖fderiv ℝ (fderiv ℝ (u i)) y‖ ≤ ε * ‖v i‖ + D * N i ∧
      ∀ z : ↥(cthickening 1 (latticeSublevelCell e b K r) ∩ {x | r x ≤ 0}),
        dist z x ≤ ρ x →
          ‖fderiv ℝ (fderiv ℝ (u i)) y - fderiv ℝ (fderiv ℝ (u i)) z‖ ≤
            (ε * ‖v i‖ + D * N i) * dist y z ^ α) :
    ∃ C > 0, ∀ i, ‖v i‖ ≤ C * N i := by
  let S := cthickening 1 (latticeSublevelCell e b K r) ∩ {x | r x ≤ 0}
  have hS : IsCompact S :=
    (isCompact_latticeSublevelCell e b hK hr).cthickening.inter_right
      (isClosed_le hr continuous_const)
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  obtain ⟨A, hA, hcover⟩ := OAI.Analysis.PDE.Schauder.compact_fixed_cover_holder_constant
    (E := E →L[ℝ] E →L[ℝ] F) ρ hρ hα
  let J := 3*A+1
  have hJ : 0 < J := by dsimp [J]; positivity
  obtain ⟨D, hD, hloc⟩ := hlocal (1/(2*J)) (by positivity)
  refine ⟨2*J*D, by positivity, ?_⟩
  intro i
  have hNi := hN i
  let M := (1/(2*J))*‖v i‖+D*N i
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hpoint (x : S) := hloc i x x (by simpa using (hρ x).le)
  have hzero := lattice_norm_le_of_thickened_cell e b hrp hbounded (u i) (hup i)
    (fun x hx => (hpoint ⟨x, hx⟩).1)
  have hfirst := lattice_norm_le_of_thickened_cell e b hrp hbounded
    (fderiv ℝ (u i)) (hup i).fderiv (fun x hx => (hpoint ⟨x, hx⟩).2.1)
  obtain ⟨hn, hh⟩ := hcover (fun x : S => fderiv ℝ (fderiv ℝ (u i)) x) M hM
    (fun x y hy => (hloc i x y hy).2.2)
  have htop : ‖(v i).val.2.2‖ ≤ 3*(A*M) :=
    lattice_holder_norm_le_of_thickened_cell e b hrp hbounded hα.le
      (mul_nonneg hA.le hM) (fderiv ℝ (fderiv ℝ (u i))) (hup i).fderiv.fderiv
      (v i).val.2.2 (hv₂ i) (fun x hx => hn ⟨x, hx⟩)
      (fun x hx y hy => hh ⟨x, hx⟩ ⟨y, hy⟩)
  have hzeroN : ‖(v i).val.1‖ ≤ M := (BoundedContinuousFunction.norm_le hM).mpr (by
    intro x
    change ‖OAI.Analysis.Normed.Function.Holder.C2Holder.value (v i) x‖ ≤ M
    rw [hv₀]
    exact hzero x x.property)
  have hfirstN : ‖(v i).val.2.1‖ ≤ M := (BoundedContinuousFunction.norm_le hM).mpr (by
    intro x
    change ‖OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative (v i) x‖ ≤ M
    rw [hv₁]
    exact hfirst x x.property)
  have hMJ : M ≤ J*M := by dsimp [J]; nlinarith
  have hAM : 3*(A*M) ≤ J*M := by dsimp [J]; nlinarith
  have hnorm : ‖v i‖ ≤ J*M :=
    max_le (hzeroN.trans hMJ) (max_le (hfirstN.trans hMJ) (htop.trans hAM))
  have hid : J*M = ‖v i‖/2+J*D*N i := by dsimp [M]; field_simp
  rw [hid] at hnorm
  nlinarith only [hnorm]

end OAI.Analysis.PDE.Dirichlet
