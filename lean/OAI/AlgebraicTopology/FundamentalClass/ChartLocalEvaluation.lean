import OAI.AlgebraicTopology.FundamentalClass.AffineCycle
import OAI.AlgebraicTopology.FundamentalClass.ChartIntegral
import OAI.AlgebraicTopology.FundamentalClass.FundamentalRestriction
import OAI.AlgebraicTopology.FundamentalClass.RelativeSimplexEvaluation
import OAI.AlgebraicTopology.FundamentalClass.TopEvaluation

/-! # Chart Local Evaluation -/

namespace OAI.AlgebraicTopology.FundamentalClass.ChartLocalEvaluation.IntegrationConstruction

noncomputable section

section

/-! Fundamental-class evaluation equals the chart Lebesgue integral for
forms supported in a single small oriented affine chart simplex. -/

open _root_.CategoryTheory Opposite Set _root_.MeasureTheory _root_.TopologicalSpace
open scoped Simplicial _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {d : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin d → ℝ) M]
    [IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ M] [T2Space M] [CompactSpace M]

theorem fundamentalEvaluation_small_chart (o : IntegrationOrientation.Orientation d M) (center : M)
    (K : Set M) (hK : IsCompact K) (hKs : K ⊆ (chartAt (Fin d → ℝ) center).source)
    (sign : ℤˣ) (hsign : ∀ x (hx : x ∈ K), o.chartSign center ⟨x, hKs hx⟩ = sign)
    (a : Fin d → ℝ) (r : ℝ) (hr : 0 < r)
    (hKi : (chartAt (Fin d → ℝ) center) '' K ⊆ AffineOrientation.IntegrationConstruction.affineInterior d a r)
    (g : (Fin d → ℝ) → M) (hg : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ∞ g)
    (hsource : ∀ x, x + SimplexGeometry.IntegrationConstruction.simplexBarycenter d ∈ DeRham.Comparison.StokesF.SingularCubeStokes.unitCube d →
      g x ∈ (chartAt (Fin d → ℝ) center).source)
    (hcoords : ∀ x, x + SimplexGeometry.IntegrationConstruction.simplexBarycenter d ∈ DeRham.Comparison.StokesF.SingularCubeStokes.unitCube d →
      (chartAt (Fin d → ℝ) center) (g x) = AffineOrientation.IntegrationConstruction.positiveAffine (Fin d → ℝ) a r x)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin d → ℝ) M d) (hform : ∀ x, x ∉ K → form.val x = 0) :
    TopEvaluation.IntegrationConstruction.fundamentalEvaluation d M o form =
      (sign : ℤ) • ∫ y in AffineOrientation.IntegrationConstruction.affineInterior d a r,
        form.val.inChart (chartAt (Fin d → ℝ) center) y (Pi.basisFun ℝ (Fin d)) := by
  let e := chartAt (Fin d → ℝ) center
  let σ : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex (Fin d → ℝ) M).toSSet _⦋d⦌ :=
    (Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothSingularMap (Fin d → ℝ) (Fin d → ℝ) g hg).app _ (SimplexGeometry.IntegrationConstruction.positiveSmoothSimplex d)
  have hσsource : ∀ t, (TopCat.of M).toSSetObjEquiv (op ⦋d⦌) σ.val t ∈ e.source := by
    intro t
    exact hsource (LocalSimplex.IntegrationGeometry.positiveSimplex d t) (ChartIntegral.IntegrationConstruction.positiveSimplex_shift_mem_cube d t)
  have hσcoords : ∀ t, e ((TopCat.of M).toSSetObjEquiv (op ⦋d⦌) σ.val t) =
      AffineOrientation.IntegrationConstruction.positiveAffine (Fin d → ℝ) a r (LocalSimplex.IntegrationGeometry.positiveSimplex d t) := by
    intro t
    exact hcoords (LocalSimplex.IntegrationGeometry.positiveSimplex d t) (ChartIntegral.IntegrationConstruction.positiveSimplex_shift_mem_cube d t)
  have hfaces := AffineCycle.IntegrationConstruction.chartSimplex_faces_avoid (X := TopCat.of M) e K a r hr hKi σ.val hσcoords
  let U : Opens M := ⟨Kᶜ, hK.isClosed.isOpen_compl⟩
  have hclass : (sign : ℤ) • ProjectedClasses.IntegrationConstruction.projectedClass (TopCat.of M) U d
      (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj (TopCat.of M)) σ.val)
      (SimplexCycles.IntegrationConstruction.integralSimplex_relative_cycle _ _ d σ.val hfaces) =
      HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection (TopCat.of M) U) d
        (IntegrationOrientation.integralFundamentalClass o) := by
    exact (congrArg (fun z : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology (TopCat.of M) Kᶜ d => (sign : ℤ) • z)
      (AffineCycle.IntegrationConstruction.chartProjectedSimplex_eq_chartCompactClass (X := TopCat.of M)
        e K hK hKs a r hr hKi σ.val hσsource hσcoords)).trans
      (FundamentalRestriction.IntegrationConstruction.integralFundamentalClass_restrict_chart o center K hK hKs sign hsign).symm
  have heval := RelativeSimplexEvaluation.IntegrationConstruction.evaluation_on_integral_relative_simplex (Fin d → ℝ) M U d
    (TopEvaluation.IntegrationConstruction.closedTopForm d M form) (fun x => hform x x.property)
    (TopEvaluation.IntegrationConstruction.topIntegrationClass d M form) (TopEvaluation.IntegrationConstruction.topIntegrationClass_restriction d M form)
    (IntegrationOrientation.integralFundamentalClass o) σ hfaces (sign : ℤ) hclass
  change TopEvaluation.IntegrationConstruction.fundamentalEvaluation d M o form = (sign : ℤ) • DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration σ form at heval
  rw [heval]
  congr 1
  exact ChartIntegral.IntegrationConstruction.smoothSimplexIntegration_affine_chart g hg e (chart_mem_atlas (Fin d → ℝ) center)
    a r hr (fun x hx => hsource x (ChartIntegral.IntegrationConstruction.positiveInterior_shift_mem_cube d x hx))
    (fun x hx => hcoords x (ChartIntegral.IntegrationConstruction.positiveInterior_shift_mem_cube d x hx)) form

end

open _root_.CategoryTheory Set _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

theorem affineInterior_isOpen (d : ℕ) (a : Fin d → ℝ) (r : ℝ) (hr : 0 < r) :
    IsOpen (AffineOrientation.IntegrationConstruction.affineInterior d a r) := by
  have heq : AffineOrientation.IntegrationConstruction.affineInterior d a r = (fun y => r⁻¹ • (y - a)) ⁻¹' SimplexGeometry.IntegrationConstruction.positiveInterior d := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change r⁻¹ • (a + r • x - a) ∈ SimplexGeometry.IntegrationConstruction.positiveInterior d
      simpa only [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr.ne', one_smul] using hx
    · intro hy
      refine ⟨r⁻¹ • (y - a), hy, ?_⟩
      change a + r • (r⁻¹ • (y - a)) = y
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      abel
  rw [heq]
  exact (SimplexGeometry.IntegrationConstruction.positiveInterior_isOpen d).preimage (by fun_prop)

theorem affineCenter_mem (d : ℕ) (a : Fin d → ℝ) (r : ℝ) : a ∈ AffineOrientation.IntegrationConstruction.affineInterior d a r :=
  ⟨0, SimplexGeometry.IntegrationConstruction.zero_mem_positiveInterior d, by simp [AffineOrientation.IntegrationConstruction.positiveAffine]⟩

variable {d : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin d → ℝ) M]
    [IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ M] [T2Space M] [CompactSpace M]

structure SmallChartRegion (o : IntegrationOrientation.Orientation d M) (center : M) where
  domain : Opens M
  sign : ℤˣ
  a : Fin d → ℝ
  r : ℝ
  positive : 0 < r
  parameter : (Fin d → ℝ) → M
  smooth : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ∞ parameter
  source : ∀ x, x + SimplexGeometry.IntegrationConstruction.simplexBarycenter d ∈ DeRham.Comparison.StokesF.SingularCubeStokes.unitCube d →
    parameter x ∈ (chartAt (Fin d → ℝ) center).source
  coordinates : ∀ x, x + SimplexGeometry.IntegrationConstruction.simplexBarycenter d ∈ DeRham.Comparison.StokesF.SingularCubeStokes.unitCube d →
    (chartAt (Fin d → ℝ) center) (parameter x) = AffineOrientation.IntegrationConstruction.positiveAffine (Fin d → ℝ) a r x
  domain_source : (domain : Set M) ⊆ (chartAt (Fin d → ℝ) center).source
  domain_image : (chartAt (Fin d → ℝ) center) '' (domain : Set M) ⊆ AffineOrientation.IntegrationConstruction.affineInterior d a r
  domain_sign : ∀ x (hx : x ∈ domain), o.chartSign center ⟨x, domain_source hx⟩ = sign

omit [CompactSpace M] in
theorem exists_smallChartRegion (o : IntegrationOrientation.Orientation d M) (center x : M)
    (hx : x ∈ (chartAt (Fin d → ℝ) center).source) :
    ∃ D : SmallChartRegion o center, x ∈ D.domain := by
  let e := chartAt (Fin d → ℝ) center
  obtain ⟨r, hr, hcube⟩ := ChartIntegral.IntegrationConstruction.exists_small_affine_cube d e.target e.open_target (e x) (e.map_source hx)
  obtain ⟨g, hg, hagree⟩ := ChartIntegral.IntegrationConstruction.exists_smooth_chart_simplex_parameter e
    (chart_mem_atlas (Fin d → ℝ) center) (e x) r hcube
  let sign := o.chartSign center ⟨x, hx⟩
  let S : Set M := Subtype.val '' {y : e.source | o.chartSign center y = sign}
  have hS : IsOpen S := e.open_source.isOpenMap_subtype_val _
    ((o.chartSign center).isLocallyConstant.isOpen_fiber sign)
  let V : Opens M := ⟨S ∩ (e.source ∩ e ⁻¹' AffineOrientation.IntegrationConstruction.affineInterior d (e x) r),
    hS.inter (e.isOpen_inter_preimage (affineInterior_isOpen d (e x) r hr))⟩
  have hVs : (V : Set M) ⊆ e.source := fun _ hy => hy.2.1
  refine ⟨⟨V, sign, e x, r, hr, g, hg, ?_, ?_, hVs, ?_, ?_⟩, ?_⟩
  · intro y hy
    exact (hagree y hy).2
  · intro y hy
    have htarget : AffineOrientation.IntegrationConstruction.positiveAffine (Fin d → ℝ) (e x) r y ∈ e.target := by
      simpa only [add_sub_cancel_right] using hcube (y + SimplexGeometry.IntegrationConstruction.simplexBarycenter d) hy
    rw [(hagree y hy).1, e.right_inv htarget]
  · rintro _ ⟨y, hy, rfl⟩
    exact hy.2.2
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := hy.1
    exact hz
  · exact ⟨⟨⟨x, hx⟩, rfl, rfl⟩, hx, affineCenter_mem d (e x) r⟩

theorem SmallChartRegion.evaluation (o : IntegrationOrientation.Orientation d M) (center : M) (D : SmallChartRegion o center)
    (K : Set M) (hK : IsCompact K) (hKD : K ⊆ D.domain)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin d → ℝ) M d) (hform : ∀ x, x ∉ K → form.val x = 0) :
    TopEvaluation.IntegrationConstruction.fundamentalEvaluation d M o form =
      (D.sign : ℤ) • ∫ y in AffineOrientation.IntegrationConstruction.affineInterior d D.a D.r,
        form.val.inChart (chartAt (Fin d → ℝ) center) y (Pi.basisFun ℝ (Fin d)) :=
  fundamentalEvaluation_small_chart o center K hK (hKD.trans D.domain_source)
    D.sign (fun x hx => D.domain_sign x (hKD hx)) D.a D.r D.positive
    ((image_mono hKD).trans D.domain_image) D.parameter D.smooth D.source D.coordinates form hform

end

end OAI.AlgebraicTopology.FundamentalClass.ChartLocalEvaluation.IntegrationConstruction
