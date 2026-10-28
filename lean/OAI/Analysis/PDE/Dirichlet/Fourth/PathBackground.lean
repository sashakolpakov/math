import OAI.Analysis.PDE.Dirichlet.Fourth.PathSource
import OAI.Analysis.PDE.Dirichlet.Fourth.BackgroundBound

noncomputable section
open Set Module
open scoped BoundedContinuousFunction ContDiff
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Nonlinear OAI.Analysis.PDE.Elliptic OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => CoordinateSpace n 4
local instance pbG1 : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance pbS1 : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance pbG2 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pbS2 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pbV1 : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance pbW1 : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance pbV2 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance pbW2 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

/-- The right-hand side of the zero-boundary twice-tangent equation has a
uniform norm in the actual periodic Hölder space. The background is fixed;
the unknown is only C4 and only its first three jets enter the bound. -/
theorem _root_.OAI.Analysis.PDE.Schauder.InteriorThirdPathData.uniform_second_background_forcing
    (hn : 1 ≤ n) (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : OAI.Analysis.PDE.Schauder.InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK)
    (hr : ContDiff ℝ ∞ r) (hB₀ : ContDiff ℝ 5 B₀)
    (hF₀ : ContDiff ℝ 3 F₀) (hF₁ : ContDiff ℝ 3 F₁)
    (hrp : LatticePeriodic e lat r) (hBp : LatticePeriodic e lat B₀)
    (hp₀ : LatticePeriodic e lat F₀) (hp₁ : LatticePeriodic e lat F₁)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K) (hne : {x | r x ≤ 0}.Nonempty)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x)
    (T S : E → E) (hT : ContDiff ℝ 4 T) (hS : ContDiff ℝ 4 S)
    (hTp : LatticePeriodic e lat T) (hSp : LatticePeriodic e lat S) :
    ∃ C > 0, ∀ s : SmoothPathSolution e lat r B₀ F₀ F₁,
      ∃ F : OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := {x | r x ≤ 0}) (α := d.exponent) e lat,
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value F.val x = mooreSecondBackgroundForcing
          (fun y => B₀ y+s.u y) B₀ (densityPath F₀ F₁ s.t) T S x) ∧ ‖F‖ ≤ C := by
  obtain ⟨C,hC,hsource⟩ := d.uniform_second_field_forcing hn e lat hK hr
    (hB₀.of_le (by norm_num)) hF₀ hF₁ hrp hBp hp₀ hp₁ hbounded hne hreg hpos₀ hpos₁ T S hT hS hTp hSp
  let w := OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative B₀ T) S
  have hw : ContDiff ℝ 3 w := OAI.Analysis.PDE.Elliptic.contDiff_fieldDerivative
    (OAI.Analysis.PDE.Elliptic.contDiff_fieldDerivative hB₀ hT (by norm_num)) (hS.of_le (by norm_num)) (by norm_num)
  have hwp : LatticePeriodic e lat w := (hBp.fieldDerivative hTp).fieldDerivative hSp
  obtain ⟨W,eW⟩ := exists_periodic_holder_field e lat hK hr.continuous hrp hbounded
    (fderiv ℝ (fderiv ℝ w)) ((hw.fderiv_right (m := 2) (by norm_num)).fderiv_right (by norm_num))
    hwp.fderiv.fderiv d.exponent_pos.le d.exponent_lt_one.le
  let R := d.normBound+‖W‖
  have hdN := d.normBound_pos
  have hR : 0 ≤ R := add_nonneg hdN.le (norm_nonneg W)
  obtain ⟨B,hB,htrace⟩ := exists_moore_trace_holder_bound (n := n)
    (X := {x | r x ≤ 0}) d.exponent_pos.le hR
  refine ⟨C+B,add_pos_of_pos_of_nonneg hC hB,?_⟩
  intro s
  obtain ⟨F,eF,nF⟩ := hsource s
  let U2 := OAI.Analysis.Normed.Function.Holder.C2Holder.hessianCLM (d.jets s)
  have nU2 : ‖U2‖ ≤ R := ((OAI.Analysis.Normed.Function.Holder.C2Holder.norm_hessianCLM_apply_le (d.jets s)).trans
    (d.jet_norm s)).trans (le_add_of_nonneg_right (norm_nonneg W))
  have nW : ‖W‖ ≤ R := le_add_of_nonneg_left hdN.le
  obtain ⟨G,eG,nG⟩ := htrace U2 W nU2 nW
  have eH : ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.HolderMap.value (F-G) x =
      mooreSecondBackgroundForcing (fun y => B₀ y+s.u y) B₀ (densityPath F₀ F₁ s.t) T S x := by
    intro x
    change OAI.Analysis.Normed.Function.Holder.HolderMap.value F x - OAI.Analysis.Normed.Function.Holder.HolderMap.value G x = _
    rw [eF,eG]
    have hU2 : OAI.Analysis.Normed.Function.Holder.HolderMap.value U2 x =
        fderiv ℝ (fderiv ℝ (fun y => B₀ y+s.u y)) x := d.jet_second s x
    rw [hU2,eW,mooreTraceJetExpression_actual]
    rfl
  have hperiodic := periodic_mooreSecondBackgroundForcing (hBp.add s.periodic) hBp
    (densityPath_periodic e lat hp₀ hp₁ s.t) hTp hSp
  have hp : F-G ∈ OAI.Analysis.Normed.Function.Holder.latticeHolder (K := {x | r x ≤ 0}) (α := d.exponent) e lat :=
    latticePeriodic_restriction_zeroExtension e lat (hrp.comp (fun t => t ≤ 0))
      _ hperiodic (OAI.Analysis.Normed.Function.Holder.HolderMap.value (F-G)) eH
  refine ⟨⟨F-G,hp⟩,eH,?_⟩
  exact (norm_sub_le F G).trans (add_le_add nF nG)

end OAI.Analysis.PDE.Dirichlet
