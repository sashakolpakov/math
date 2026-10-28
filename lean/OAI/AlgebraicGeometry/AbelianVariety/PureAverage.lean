import OAI.AlgebraicGeometry.AbelianVariety.BettiNumbers
import OAI.Analysis.DifferentialForms.Manifold.PurePullback
import Mathlib.Analysis.Convex.Integral

/-! # Pure Average -/

namespace OAI.AlgebraicGeometry.AbelianVariety.PureAverage.Constructions.ExteriorCohomology

noncomputable section

section

open scoped _root_.Manifold ContDiff _root_.Topology
open Set Filter _root_.MeasureTheory

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup 𝓘(ℝ, E) ∞ G] [LieGroup 𝓘(ℂ, E) ∞ G]
  [MeasurableSpace G] [BorelSpace G] [CompactSpace G]
  (μ : Measure G) [IsProbabilityMeasure μ] [Measure.IsMulRightInvariant μ]
  {p q : ℕ}

theorem averageForms_pure (form : OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G (p + q))
    (hf : OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E G p q form.val) :
    OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E G p q (Averaging.Constructions.ExteriorCohomology.averageForms μ form).val := by
  intro c hc y hy
  rw [AveragingDerivative.Constructions.ExteriorCohomology.averageForms_inChart_eq_integral]
  let : FiniteDimensional ℂ (E [⋀^Fin (p + q)]→L[ℝ] ℂ) :=
    BettiNumbers.Constructions.ExteriorCohomology.finiteDimensional_covectors E (p + q)
  let S := OAI.Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E p q
  have hS : IsClosed (S : Set (E [⋀^Fin (p + q)]→L[ℝ] ℂ)) := S.closed_of_finiteDimensional
  exact (S.restrictScalars ℝ).convex.integral_mem hS (ae_of_all _ (fun g =>
    hf.pullback (fun x : G => g * x)
      (contMDiff_mul_left (I := 𝓘(ℂ, E)) (n := ∞)) c hc y hy))
    ((AveragingDerivative.Constructions.ExteriorCohomology.translatedInChart_continuous form c y).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))

omit [FiniteDimensional ℝ E] [MeasurableSpace G] [BorelSpace G] [CompactSpace G] in
theorem invariantForm_pure_iff (form : InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := E) (G := G) (p + q)) :
    OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E G p q form.val.val ↔
      OAI.Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E p q (form.val.val.inChart (chartAt E (1 : G)) (chartAt E (1 : G) 1)) := by
  constructor
  · intro hf
    exact (OAI.Analysis.DifferentialForms.Manifold.BidegreeInvariant.hasManifoldBidegree_iff_chartAt _).mp hf 1
  · intro hf c hc y hy
    let x := c.symm y
    let d := chartAt E (1 : G)
    have hd : d ∈ atlas E G := chart_mem_atlas E (1 : G)
    have h1 : (1 : G) ∈ d.source := mem_chart_source E _
    have hx : x⁻¹ * c.symm y = 1 := inv_mul_cancel x
    have hi := (InvariantClosed.Constructions.ExteriorCohomology.mem_invariantForms_iff form.val).mp form.property x⁻¹
    have hip : form.val.val.pullback (fun z : G => x⁻¹ * z) = form.val.val :=
      congrArg Subtype.val hi
    have hb := form.val.val.pullback_inChart (fun z : G => x⁻¹ * z) c d hc hd hy
      (by rw [hx]; exact h1)
      ((contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiableAt (by simp))
    rw [hip, hx] at hb
    rw [hb]
    have hhol := (OAI.Analysis.DifferentialForms.Manifold.Holomorphic.complexContDiffAt_manifoldMap_inChart (fun z : G => x⁻¹ * z)
      c d hc hd hy (by rw [hx]; exact h1)
      (contMDiff_mul_left (I := 𝓘(ℂ, E)) (n := ∞)).contMDiffAt).differentiableAt (by simp)
    rw [hhol.fderiv_restrictScalars ℝ]
    exact AlgebraicTopology.DeRham.Comparison.BidegreeRestriction.hasBidegree_pullback hf (fderiv ℂ (d ∘ (fun z : G => x⁻¹ * z) ∘ c.symm) y)

variable [T2Space G] [ConnectedSpace G] [IsMulCommutative G]

theorem invariantDeRham_mem_pure_iff (form : InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := E) (G := G) (p + q)) :
    InvariantCohomology.Constructions.Exterior.invariantDeRham (p + q) form ∈ AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.manifoldPureDeRhamImage E G p q ↔
      OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E G p q form.val.val := by
  rw [AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.mem_manifoldPureDeRhamImage_iff]
  constructor
  · rintro ⟨a, ha, he⟩
    let μ₀ := Averaging.Constructions.ExteriorCohomology.compactGroupHaar (E := E) (G := G)
    let b : InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := E) (G := G) (p + q) :=
      ⟨Averaging.Constructions.ExteriorCohomology.averageForms μ₀ a.val, Averaging.Constructions.ExteriorCohomology.averageForms_mem μ₀ a.val⟩
    have hb : InvariantCohomology.Constructions.Exterior.invariantDeRham (p + q) b = InvariantCohomology.Constructions.Exterior.invariantDeRham (p + q) form :=
      (CyclePeriods.Constructions.ExteriorCohomology.averageClosedForm_deRhamClass μ₀ a).trans he
    have hbf := InvariantCohomology.Constructions.Exterior.invariantDeRham_injective_compact (p + q) hb
    have htype : OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E G p q b.val.val := averageForms_pure μ₀ a.val ha
    rw [hbf] at htype
    exact htype
  · intro hf
    exact ⟨InvariantCohomology.Constructions.Exterior.invariantClosedInclusion (p + q) form, hf, rfl⟩

end

open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def covectorPullbackEquiv (e : E ≃L[ℝ] F) (n : ℕ) :
    (F [⋀^Fin n]→L[ℝ] ℂ) ≃ₗ[ℂ] (E [⋀^Fin n]→L[ℝ] ℂ) where
  toFun form := form.compContinuousLinearMap e.toContinuousLinearMap
  invFun form := form.compContinuousLinearMap e.symm.toContinuousLinearMap
  left_inv form := by ext v; simp [Function.comp_def]
  right_inv form := by ext v; simp [Function.comp_def]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup 𝓘(ℝ, E) ∞ G]

def invariantChartEvalEquiv (n : ℕ) :
    InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := E) (G := G) n ≃ₗ[ℂ] (E [⋀^Fin n]→L[ℝ] ℂ) :=
  (InvariantClosed.Constructions.ExteriorCohomology.invariantFormsEvalEquiv n).trans
    (covectorPullbackEquiv (E := E) (F := E)
      (show E ≃L[ℝ] E from (OAI.Analysis.DifferentialForms.Manifold.TangentCoordinates.preferredTangentEquiv (E := E) (1 : G)).symm) n)

theorem invariantChartEvalEquiv_apply (n : ℕ)
    (form : InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := E) (G := G) n) :
    invariantChartEvalEquiv n form =
      form.val.val.inChart (chartAt E (1 : G)) (chartAt E (1 : G) 1) := by
  ext v
  exact (form.val.val.inChart_at (chartAt E (1 : G)) (chart_mem_atlas E _)
    1 (mem_chart_source E _) v).symm

def abelianModelCovectorBettiEquiv (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) :
    (A.variety.analyticModel [⋀^Fin n]→L[ℝ] ℂ) ≃ₗ[ℂ]
      A.variety.complexCohomology n :=
  (invariantChartEvalEquiv (E := A.variety.analyticModel)
    (G := A.variety.analyticSpace) n).symm.trans
    ((DeRham.Constructions.ExteriorCohomology.abelianInvariantDeRhamEquiv A n).trans (A.variety.deRhamBettiIso n).toLinearEquiv)

theorem abelianModelCovectorBettiEquiv_pure (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (p q : ℕ)
    (form : A.variety.analyticModel [⋀^Fin (p + q)]→L[ℝ] ℂ) :
    abelianModelCovectorBettiEquiv A (p + q) form ∈ A.variety.pureBettiSubspace p q ↔
      OAI.Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree A.variety.analyticModel p q form := by
  let : ConnectedSpace A.variety.analyticSpace := PowerImage.Constructions.ExteriorCohomology.abelianPoint_connectedSpace A
  let : MeasurableSpace A.variety.analyticSpace := borel _
  let : BorelSpace A.variety.analyticSpace := ⟨rfl⟩
  let a := (invariantChartEvalEquiv (E := A.variety.analyticModel)
    (G := A.variety.analyticSpace) (p + q)).symm form
  have hmem : abelianModelCovectorBettiEquiv A (p + q) form ∈
      A.variety.pureBettiSubspace p q ↔
      InvariantCohomology.Constructions.Exterior.invariantDeRham (p + q) a ∈ A.variety.pureDeRhamSubspace p q := by
    change (A.variety.deRhamBettiIso (p + q)).toLinearEquiv
      (InvariantCohomology.Constructions.Exterior.invariantDeRham (p + q) a) ∈
      (A.variety.pureDeRhamSubspace p q).map
        (A.variety.deRhamBettiIso (p + q)).toLinearEquiv.toLinearMap ↔ _
    constructor
    · rintro ⟨b, hb, he⟩
      have hba := (A.variety.deRhamBettiIso (p + q)).toLinearEquiv.injective he
      exact hba ▸ hb
    · intro ha
      exact ⟨_, ha, rfl⟩
  rw [hmem, invariantDeRham_mem_pure_iff, invariantForm_pure_iff,
    ← invariantChartEvalEquiv_apply]
  exact iff_of_eq (congrArg (OAI.Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree A.variety.analyticModel p q)
    ((invariantChartEvalEquiv (p + q)).apply_symm_apply form))

end

end OAI.AlgebraicGeometry.AbelianVariety.PureAverage.Constructions.ExteriorCohomology
