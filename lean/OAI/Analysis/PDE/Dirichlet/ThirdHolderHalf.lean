import OAI.Analysis.PDE.Dirichlet.Fourth.Limit

noncomputable section
open Set Module
open scoped ContDiff
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => CoordinateSpace n 4
attribute [local instance] flG1 flS1 flG2 flS2 flG3 flS3

theorem _root_.OAI.Analysis.PDE.Schauder.InteriorThirdPathData.uniform_third_holder_fields_half
    (hn : 1 ≤ n) (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : OAI.Analysis.PDE.Schauder.InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK)
    (hr : ContDiff ℝ ∞ r) (hB₀ : ContDiff ℝ 4 B₀)
    (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    (hrp : LatticePeriodic e lat r) (hBp : LatticePeriodic e lat B₀)
    (hp₀ : LatticePeriodic e lat F₀) (hp₁ : LatticePeriodic e lat F₁)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K) (hne : {x | r x ≤ 0}.Nonempty)
    (hreg : ∀ x, r x=0 → fderiv ℝ r x ≠ 0)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x) :
    ∃ M > 0, ∀ a : SmoothPathSolution e lat r B₀ F₀ F₁,
      ∃ T : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (d.exponent/2),
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x =
          fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => B₀ y+a.u y))) x) ∧ ‖T‖ ≤ M := by
  obtain ⟨R,hR,hthird⟩ := d.uniform_third_bounds e lat hK (by omega) hr hB₀ hF₀ hF₁
    hrp hBp hp₀ hp₁ hbounded hne hreg hpos₀ hpos₁
  refine ⟨2*R,mul_pos (by norm_num) hR,?_⟩
  intro a
  let f3 := fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => B₀ y+a.u y)))
  have hf3 : Continuous f3 := by
    exact ((((hB₀.add a.smooth).fderiv_right (m := 3) (by norm_num)).fderiv_right
      (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).continuous
  exact exists_holder_field_half_of_bounds d.exponent_pos.le hR.le
    (fun x : {x | r x ≤ 0} => f3 x) (hf3.comp continuous_subtype_val)
    (fun x => (hthird a).1 x x.property)
    (fun x y => (hthird a).2 x x.property y y.property)

end OAI.Analysis.PDE.Dirichlet
