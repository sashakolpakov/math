import OAI.Analysis.Normed.Function.Holder.Boundary.Gradient.Field
import OAI.Analysis.PDE.Schauder.Dirichlet.UniformThirdRegularity

noncomputable section
open Set Module
open scoped BoundedContinuousFunction ContDiff
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => CoordinateSpace n 4
local instance lowerJets1Group : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance lowerJets1Space : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance lowerJets2Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance lowerJets2Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance lowerJets3Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance lowerJets3Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem exists_holder_field_of_continuous_bounds {X F : Type*} [MetricSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {α M : ℝ} (hα : 0 ≤ α) (hM : 0 ≤ M)
    (f : X → F) (hf : Continuous f) (hb : ∀ x, ‖f x‖ ≤ M)
    (hh : ∀ x y, ‖f x-f y‖ ≤ M*dist x y^α) :
    ∃ U : OAI.Analysis.Normed.Function.Holder.HolderMap X F α, (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value U x=f x) ∧ ‖U‖ ≤ M := by
  let v : X →ᵇ F := BoundedContinuousFunction.ofNormedAddCommGroup f hf M hb
  let U := OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα v hh
  refine ⟨U, fun _ => rfl, ?_⟩
  exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_ofBounded_le hα v hM hh).trans
    (max_le (BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ hM _) le_rfl)

/-- The actual first three derivatives of every retained path solution
are Hölder fields with one common norm bound. There is no fourth-order input. -/
theorem _root_.OAI.Analysis.PDE.Schauder.InteriorThirdPathData.uniform_lower_jet_fields
    (hn : 1 ≤ n) (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : OAI.Analysis.PDE.Schauder.InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK)
    (hr : ContDiff ℝ ∞ r) (hB₀ : ContDiff ℝ 4 B₀)
    (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    (hrp : LatticePeriodic e lat r) (hBp : LatticePeriodic e lat B₀)
    (hp₀ : LatticePeriodic e lat F₀) (hp₁ : LatticePeriodic e lat F₁)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K) (hne : {x | r x ≤ 0}.Nonempty)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x) :
    ∃ R > 0, ∀ s : SmoothPathSolution e lat r B₀ F₀ F₁,
      ∃ (U1 : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] ℝ) d.exponent)
        (U2 : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] ℝ) d.exponent)
        (U3 : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) d.exponent),
        ‖U1‖ ≤ R ∧ ‖U2‖ ≤ R ∧ ‖U3‖ ≤ R ∧
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value U1 x = fderiv ℝ (fun y => B₀ y+s.u y) x) ∧
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value U2 x = fderiv ℝ (fderiv ℝ (fun y => B₀ y+s.u y)) x) ∧
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value U3 x =
          fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => B₀ y+s.u y))) x) := by
  obtain ⟨C,hC,hgrad⟩ := OAI.Analysis.Normed.Function.Holder.C2Holder.exists_uniform_periodic_gradient_field (by omega)
    e lat hK hr hrp hbounded hreg hΩK d.exponent_pos d.exponent_lt_one.le
  obtain ⟨M,hM,hthird⟩ := d.uniform_third_bounds e lat hK (by omega) hr hB₀ hF₀ hF₁
    hrp hBp hp₀ hp₁ hbounded hne hreg hpos₀ hpos₁
  have hdN := d.normBound_pos
  let R := 1+C*d.normBound+d.normBound+M
  have hR : 0 < R := by dsimp [R]; positivity
  have h1R : C*d.normBound ≤ R := by
    dsimp [R]
    linarith only [hdN.le,hM.le]
  have h2R : d.normBound ≤ R := by
    dsimp [R]
    linarith only [mul_nonneg hC.le hdN.le,hM.le]
  have h3R : M ≤ R := by
    dsimp [R]
    linarith only [mul_nonneg hC.le hdN.le,hdN.le]
  refine ⟨R,hR,?_⟩
  intro s
  have hjp : LatticePeriodic e lat (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value (d.jets s))) :=
    OAI.Analysis.Normed.Function.Holder.latticePeriodic_of_value_eq (hrp.comp (fun t => t ≤ 0)) (d.jets s)
      (fun y => B₀ y+s.u y) (hBp.add s.periodic) (d.jet_value s)
  obtain ⟨U1,hU1,hU1n⟩ := hgrad (d.jets s) hjp
  let U2 := OAI.Analysis.Normed.Function.Holder.C2Holder.hessianCLM (d.jets s)
  have hU2n : ‖U2‖ ≤ d.normBound :=
    (OAI.Analysis.Normed.Function.Holder.C2Holder.norm_hessianCLM_apply_le (d.jets s)).trans (d.jet_norm s)
  let f3 := fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => B₀ y+s.u y)))
  have hf3 : Continuous f3 := by
    exact ((((hB₀.add s.smooth).fderiv_right (m := 3) (by norm_num)).fderiv_right
      (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).continuous
  obtain ⟨U3,eU3,hU3n⟩ := exists_holder_field_of_continuous_bounds d.exponent_pos.le hM.le
    (fun x : {x | r x ≤ 0} => f3 x) (hf3.comp continuous_subtype_val)
    (fun x => (hthird s).1 x x.property)
    (fun x y => (hthird s).2 x x.property y y.property)
  refine ⟨U1,U2,U3,?_,?_,?_,?_,?_,eU3⟩
  · exact (hU1n.trans (mul_le_mul_of_nonneg_left (d.jet_norm s) hC.le)).trans h1R
  · exact hU2n.trans h2R
  · exact hU3n.trans h3R
  · intro x
    rw [hU1]
    exact d.jet_first s x
  · exact d.jet_second s

end OAI.Analysis.PDE.Dirichlet
