import OAI.Analysis.PDE.Dirichlet.Fourth.SourceUniform
import OAI.Analysis.PDE.Dirichlet.Fourth.LowerJets
import OAI.Analysis.PDE.Dirichlet.Fourth.FieldData
import OAI.Analysis.PDE.Dirichlet.Fourth.Density

noncomputable section
open Set Module
open scoped BoundedContinuousFunction ContDiff
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => CoordinateSpace n 4
local instance psG1 : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance psS1 : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance psG2 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance psS2 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance psG3 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance psS3 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance psV1 : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance psW1 : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance psV2 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance psW2 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance psV3 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance psW3 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance

/-- Uniform actual twice-field forcing along the nonlinear path. The fields
are fixed in advance and need not be tangent to the boundary for this estimate. -/
theorem _root_.OAI.Analysis.PDE.Schauder.InteriorThirdPathData.uniform_second_field_forcing
    (hn : 1 ≤ n) (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : OAI.Analysis.PDE.Schauder.InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK)
    (hr : ContDiff ℝ ∞ r) (hB₀ : ContDiff ℝ 4 B₀)
    (hF₀ : ContDiff ℝ 3 F₀) (hF₁ : ContDiff ℝ 3 F₁)
    (hrp : LatticePeriodic e lat r) (hBp : LatticePeriodic e lat B₀)
    (hp₀ : LatticePeriodic e lat F₀) (hp₁ : LatticePeriodic e lat F₁)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K) (hne : {x | r x ≤ 0}.Nonempty)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x)
    (T S : E → E) (hT : ContDiff ℝ 4 T) (hS : ContDiff ℝ 4 S)
    (hTp : LatticePeriodic e lat T) (hSp : LatticePeriodic e lat S) :
    ∃ C > 0, ∀ s : SmoothPathSolution e lat r B₀ F₀ F₁,
      ∃ F : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} ℝ d.exponent,
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value F x = mooreSecondFieldForcing (fun y => B₀ y+s.u y)
          (densityPath F₀ F₁ s.t) T S x) ∧ ‖F‖ ≤ C := by
  obtain ⟨R0,hR0,hjet⟩ := d.uniform_lower_jet_fields hn e lat hK hr hB₀
    (hF₀.of_le (by norm_num)) (hF₁.of_le (by norm_num)) hrp hBp hp₀ hp₁
    hbounded hne hreg hpos₀ hpos₁
  obtain ⟨RT,hRT,T0,T1,T2,T3,nT0,nT1,nT2,nT3,eT0,eT1,eT2,eT3⟩ :=
    exists_periodic_field_four_jets e lat hK hr.continuous hrp hbounded T hT hTp
      d.exponent_pos.le d.exponent_lt_one.le
  obtain ⟨RS,hRS,S0,S1,S2,S3,nS0,nS1,nS2,nS3,eS0,eS1,eS2,eS3⟩ :=
    exists_periodic_field_four_jets e lat hK hr.continuous hrp hbounded S hS hSp
      d.exponent_pos.le d.exponent_lt_one.le
  obtain ⟨RF,hRF,hF2⟩ := exists_densityPath_hessian_holder e lat hK hr.continuous hrp hbounded
    F₀ F₁ hF₀ hF₁ hp₀ hp₁ d.exponent_pos.le d.exponent_lt_one.le
  let R := R0+RT+RS+RF+d.densityBound
  have hdB := d.densityBound_nonneg
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have h0R : R0 ≤ R := by dsimp [R]; linarith
  have hTR : RT ≤ R := by dsimp [R]; linarith
  have hSR : RS ≤ R := by dsimp [R]; linarith
  have hFR : RF ≤ R := by dsimp [R]; linarith
  have hBR : d.densityBound ≤ R := by dsimp [R]; linarith
  obtain ⟨C,hC,hsource⟩ := exists_uniform_moore_second_source_bound (n := n)
    (X := {x | r x ≤ 0}) d.exponent_pos.le hR
  refine ⟨C+1,by linarith,?_⟩
  intro s
  obtain ⟨U1,U2,U3,nU1,nU2,nU3,eU1,eU2,eU3⟩ := hjet s
  obtain ⟨H2,eH2,nH2⟩ := hF2 s.t s.parameter
  have hf : ContDiff ℝ 2 (densityPath F₀ F₁ s.t) :=
    contDiff_densityPath (hF₀.of_le (by norm_num)) (hF₁.of_le (by norm_num)) s.t
  obtain ⟨H1,eH1,nH1⟩ := exists_holder_field_of_continuous_bounds d.exponent_pos.le hdB
    (fun x : {x | r x ≤ 0} => fderiv ℝ (densityPath F₀ F₁ s.t) x)
    ((hf.continuous_fderiv (by norm_num)).comp continuous_subtype_val)
    (fun x => d.density_norm s.t s.parameter x x.property)
    (fun x y => d.density_holder s.t s.parameter x x.property y y.property)
  obtain ⟨F,eF,nF⟩ := hsource (fun y => B₀ y+s.u y) (densityPath F₀ F₁ s.t) T S
    ((hB₀.add s.smooth).of_le (by norm_num)) hf (hT.of_le (by norm_num)) Subtype.val
    ⟨U1,U2,U3,T0,T1,T2,T3,S0,S1,S2,H1,H2⟩
    ⟨nU1.trans h0R,nU2.trans h0R,nU3.trans h0R,
      nT0.trans hTR,nT1.trans hTR,nT2.trans hTR,nT3.trans hTR,
      nS0.trans hSR,nS1.trans hSR,nS2.trans hSR,nH1.trans hBR,nH2.trans hFR⟩
    ⟨eU1,eU2,eU3,eT0,eT1,eT2,eT3,eS0,eS1,eS2,eH1,eH2⟩
  exact ⟨F,eF,nF.trans (by linarith)⟩

end OAI.Analysis.PDE.Dirichlet
