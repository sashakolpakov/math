import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.UnsignedChartIntegral
import OAI.AlgebraicTopology.FundamentalClass.ChartLocalEvaluation

/-! # Integral Chart Partition -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntegralChartPartition.CM

noncomputable section

/-! ThetaCycle: local simplex evaluation extends over a compact chart and then
over the actual finite smooth chart partition. -/

open _root_.CategoryTheory Set _root_.MeasureTheory _root_.TopologicalSpace
open OAI.AlgebraicTopology.FundamentalClass.ChartLocalEvaluation.IntegrationConstruction
open scoped _root_.Manifold ContDiff

variable {d : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin d → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ M] [T2Space M]

structure UnsignedSmallChartRegion (e : OpenPartialHomeomorph M (Fin d → ℝ)) where
  domain : Opens M
  a : Fin d → ℝ
  r : ℝ
  positive : 0 < r
  parameter : (Fin d → ℝ) → M
  smooth : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ∞ parameter
  source : ∀ x, x + AlgebraicTopology.FundamentalClass.SimplexGeometry.IntegrationConstruction.simplexBarycenter d ∈ AlgebraicTopology.DeRham.Comparison.StokesF.SingularCubeStokes.unitCube d → parameter x ∈ e.source
  coordinates : ∀ x, x + AlgebraicTopology.FundamentalClass.SimplexGeometry.IntegrationConstruction.simplexBarycenter d ∈ AlgebraicTopology.DeRham.Comparison.StokesF.SingularCubeStokes.unitCube d →
    e (parameter x) = AlgebraicTopology.FundamentalClass.AffineOrientation.IntegrationConstruction.positiveAffine (Fin d → ℝ) a r x
  domain_source : (domain : Set M) ⊆ e.source
  domain_image : e '' (domain : Set M) ⊆ AlgebraicTopology.FundamentalClass.AffineOrientation.IntegrationConstruction.affineInterior d a r

omit [T2Space M] in
theorem exists_unsigned_small_chart_region (e : OpenPartialHomeomorph M (Fin d → ℝ))
    (he : e ∈ atlas (Fin d → ℝ) M) (x : M) (hx : x ∈ e.source) :
    ∃ D : UnsignedSmallChartRegion e, x ∈ D.domain := by
  obtain ⟨r, hr, hcube⟩ := AlgebraicTopology.FundamentalClass.ChartIntegral.IntegrationConstruction.exists_small_affine_cube d e.target e.open_target (e x) (e.map_source hx)
  obtain ⟨g, hg, hagree⟩ := AlgebraicTopology.FundamentalClass.ChartIntegral.IntegrationConstruction.exists_smooth_chart_simplex_parameter e he (e x) r hcube
  let V : Opens M := ⟨e.source ∩ e ⁻¹' AlgebraicTopology.FundamentalClass.AffineOrientation.IntegrationConstruction.affineInterior d (e x) r,
    e.isOpen_inter_preimage (AlgebraicTopology.FundamentalClass.ChartLocalEvaluation.IntegrationConstruction.affineInterior_isOpen d (e x) r hr)⟩
  refine ⟨⟨V, e x, r, hr, g, hg, ?_, ?_, (fun _ hy => hy.1), ?_⟩, ?_⟩
  · intro y hy
    exact (hagree y hy).2
  · intro y hy
    have ht : AlgebraicTopology.FundamentalClass.AffineOrientation.IntegrationConstruction.positiveAffine (Fin d → ℝ) (e x) r y ∈ e.target := by
      simpa only [add_sub_cancel_right] using hcube (y + AlgebraicTopology.FundamentalClass.SimplexGeometry.IntegrationConstruction.simplexBarycenter d) hy
    rw [(hagree y hy).1, e.right_inv ht]
  · rintro _ ⟨y, hy, rfl⟩
    exact hy.2
  · exact ⟨hx, AlgebraicTopology.FundamentalClass.ChartLocalEvaluation.IntegrationConstruction.affineCenter_mem d (e x) r⟩

omit [IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ M] [T2Space M] in
theorem unsigned_small_chart_affine_target (e : OpenPartialHomeomorph M (Fin d → ℝ))
    (D : UnsignedSmallChartRegion e) : AlgebraicTopology.FundamentalClass.AffineOrientation.IntegrationConstruction.affineInterior d D.a D.r ⊆ e.target := by
  rintro _ ⟨x, hx, rfl⟩
  rw [← D.coordinates x (AlgebraicTopology.FundamentalClass.ChartIntegral.IntegrationConstruction.positiveInterior_shift_mem_cube d x hx)]
  exact e.map_source (D.source x (AlgebraicTopology.FundamentalClass.ChartIntegral.IntegrationConstruction.positiveInterior_shift_mem_cube d x hx))

theorem integral_cycle_evaluation_small_region
    (z : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of M)).homology d)
    (e : OpenPartialHomeomorph M (Fin d → ℝ)) (he : e ∈ atlas (Fin d → ℝ) M)
    (D : UnsignedSmallChartRegion e) (K : Set M) (hK : IsCompact K) (hKD : K ⊆ D.domain)
    (hchart : HomologicalComplex.homologyMap (CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection (TopCat.of M) Kᶜ) d z =
      AlgebraicTopology.FundamentalClass.IntegrationOrientation.Geometry.chartCompactClass e K hK (hKD.trans D.domain_source))
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin d → ℝ) M d) (hform : ∀ x, x ∉ K → form.val x = 0) :
    IntegralEvaluation.CM.integralCycleEvaluation z form = ∫ y, UnsignedChartIntegral.CM.unsignedChartIntegrand e form y := by
  have h := IntegralEvaluation.CM.integral_cycle_evaluation_small_chart z e he K hK (hKD.trans D.domain_source)
    hchart D.a D.r D.positive ((image_mono hKD).trans D.domain_image)
    D.parameter D.smooth D.source D.coordinates form hform
  exact h.trans (UnsignedChartIntegral.CM.unsigned_chart_integral_supported e K (AlgebraicTopology.FundamentalClass.AffineOrientation.IntegrationConstruction.affineInterior d D.a D.r)
    (AlgebraicTopology.FundamentalClass.ChartLocalEvaluation.IntegrationConstruction.affineInterior_isOpen d D.a D.r D.positive).measurableSet
    (unsigned_small_chart_affine_target e D) ((image_mono hKD).trans D.domain_image) form hform)

variable [CompactSpace M]

theorem integral_cycle_evaluation_supported_chart
    (z : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of M)).homology d)
    (e : OpenPartialHomeomorph M (Fin d → ℝ)) (he : e ∈ atlas (Fin d → ℝ) M)
    (hchart : ∀ (K : Set M) (hK : IsCompact K) (hKs : K ⊆ e.source),
      HomologicalComplex.homologyMap (CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection (TopCat.of M) Kᶜ) d z =
        AlgebraicTopology.FundamentalClass.IntegrationOrientation.Geometry.chartCompactClass e K hK hKs)
    (K : Set M) (hK : IsCompact K) (hKs : K ⊆ e.source)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin d → ℝ) M d) (hform : ∀ x, x ∉ K → form.val x = 0) :
    IntegralEvaluation.CM.integralCycleEvaluation z form = ∫ y, UnsignedChartIntegral.CM.unsignedChartIntegrand e form y := by
  classical
  choose D hD using fun x : K => exists_unsigned_small_chart_region e he x (hKs x.property)
  have hcover : K ⊆ ⋃ x : K, (D x).domain := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hD ⟨x, hx⟩⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K => ((D x).domain : Set M))
    (fun x => (D x).domain.isOpen) hcover
  have hcover' : K ⊆ ⋃ i : s, (D i.val).domain := by
    intro x hx
    obtain ⟨i, hi, hix⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hix⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, Fin d → ℝ)) hK.isClosed (fun i : s => ((D i.val).domain : Set M))
    (fun i => (D i.val).domain.isOpen) hcover'
  have hρsource (i : s) : tsupport (ρ i) ⊆ e.source := (hρ i).trans (D i.val).domain_source
  have hlocal (i : s) : IntegralEvaluation.CM.integralCycleEvaluation z (AlgebraicTopology.FundamentalClass.FormPartition.IntegrationConstruction.weightForm (ρ i) (ρ i).contMDiff form) =
      ∫ y, UnsignedChartIntegral.CM.unsignedChartIntegrand e (AlgebraicTopology.FundamentalClass.FormPartition.IntegrationConstruction.weightForm (ρ i) (ρ i).contMDiff form) y :=
    integral_cycle_evaluation_small_region z e he (D i.val) (tsupport (ρ i))
      isClosed_closure.isCompact (hρ i) (hchart _ _ _)
      (AlgebraicTopology.FundamentalClass.FormPartition.IntegrationConstruction.weightForm (ρ i) (ρ i).contMDiff form)
      (AlgebraicTopology.FundamentalClass.FormPartition.IntegrationConstruction.weightForm_zero_of_notMem_tsupport (ρ i) (ρ i).contMDiff form)
  have hsum : (∑ i : s, UnsignedChartIntegral.CM.unsignedChartIntegrand e (AlgebraicTopology.FundamentalClass.FormPartition.IntegrationConstruction.weightForm (ρ i) (ρ i).contMDiff form)) =
      UnsignedChartIntegral.CM.unsignedChartIntegrand e form := by
    rw [← map_sum, AlgebraicTopology.FundamentalClass.FormPartition.IntegrationConstruction.sum_weightForm K ρ form hform]
  rw [AlgebraicTopology.FundamentalClass.FormPartition.IntegrationConstruction.linearFunctional_partition K ρ (IntegralEvaluation.CM.integralCycleEvaluation z) form hform]
  simp_rw [hlocal]
  rw [← integral_finsetSum Finset.univ (fun i _ =>
    UnsignedChartIntegral.CM.unsigned_chart_integrand_weight_integrable e he (ρ i) (ρ i).contMDiff (hρsource i) form)]
  apply integral_congr_ae
  filter_upwards [] with y
  simpa only [Finset.sum_apply] using congrFun hsum y

theorem integral_cycle_evaluation_chart_partition
    (z : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of M)).homology d)
    (D : Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.FiniteChartPartition (Fin d → ℝ) M)
    (hchart : ∀ (i : D.centers) (K : Set M) (hK : IsCompact K)
      (hKs : K ⊆ (chartAt (Fin d → ℝ) i.val).source),
      HomologicalComplex.homologyMap (CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection (TopCat.of M) Kᶜ) d z =
        AlgebraicTopology.FundamentalClass.IntegrationOrientation.Geometry.chartCompactClass (chartAt (Fin d → ℝ) i.val) K hK hKs)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin d → ℝ) M d) :
    IntegralEvaluation.CM.integralCycleEvaluation z form = ∑ i : D.centers, ∫ y,
      Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.chartCutoff (chartAt (Fin d → ℝ) i.val) (D.partition i)
        (fun y => form.val.inChart (chartAt (Fin d → ℝ) i.val) y (Pi.basisFun ℝ (Fin d))) y := by
  rw [AlgebraicTopology.FundamentalClass.FormPartition.IntegrationConstruction.linearFunctional_partition univ D.partition (IntegralEvaluation.CM.integralCycleEvaluation z) form
    (fun x hx => False.elim (hx (mem_univ x)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_cycle_evaluation_supported_chart z (chartAt (Fin d → ℝ) i.val)
    (chart_mem_atlas (Fin d → ℝ) i.val) (hchart i) (tsupport (D.partition i))
    isClosed_closure.isCompact (D.subordinate i)
    (AlgebraicTopology.FundamentalClass.FormPartition.IntegrationConstruction.weightForm (D.partition i) (D.partition i).contMDiff form)
    (AlgebraicTopology.FundamentalClass.FormPartition.IntegrationConstruction.weightForm_zero_of_notMem_tsupport (D.partition i) (D.partition i).contMDiff form),
    UnsignedChartIntegral.CM.unsigned_chart_integrand_weight]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntegralChartPartition.CM
