import OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicLocalPeriods
import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicHolomorphicExponentialOn
import OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicLocalPeriodFamily

/-! # Intrinsic Holomorphic Local Periods -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicHolomorphicLocalPeriods.IntrinsicFamilyPeriods

noncomputable section

/-! Actual native period sections are holomorphic on open base
neighborhoods, with exact central values and full exponential-kernel
control. The native fiber charts and their complex regularity are retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set _root_.Metric
open scoped Classical ContDiff _root_.Manifold _root_.CategoryTheory.MonObj NNReal

open OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicLocalPeriods.Abelian.FamilyPoints

variable {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {E F : Type}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [CompleteSpace E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
  [CompleteSpace F] [FiniteDimensional ℂ F]

/-- A normalized actual relative chart supplies native fiber charts,
continuous genuine exponentials, and a common continuous local logarithm. -/
theorem exists_native_holomorphic_local_period_family
    (G : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left)
    (present : ∀ s : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback s.left))
    (V : (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G).left.Opens) (hV : IsAffineOpen V)
    {R : Type} [CommRing R] [Algebra ℂ R]
    [Algebra R (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V)]
    [IsScalarTower ℂ R (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V)]
    (b : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ S) [IsOpenImmersion b.left]
    (hi : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V hV ≫ ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G =
      Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V)
        (IsScalarTower.toAlgHom ℂ R (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V)) ≫ b)
    (σ : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V →ₐ[ℂ] R)
    (hσ : Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V) R σ ≫
          ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V hV = b ≫ ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.identitySection S G)
    {x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V)}
    (N : ArithmeticGeometry.Descent.CMVariety.RegularSectionCharts.Abelian.RelativeCharts.SectionNormalizedCharts (E := E) (F := F) x σ) :
    let s := fun q : F => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap
      (CommAlgCat.of ℂ R) b (N.charts.base.symm q)
    let : ∀ q : F, IsIntegral (G.pullback (s q).left).scheme.left := fun q => (present (s q)).isIntegral
    let L := fun q : F => Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension (G.pullback (s q).left).scheme.hom) → ℂ
    let : ∀ q : F, T2Space (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q).left).scheme) :=
      fun q => (present (s q)).t2Space
    let : ∀ q : F, LieGroup (𝓘(ℝ, L q)) ∞ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q).left).scheme) :=
      fun q => (present (s q)).nativeRealLieGroup
    let e := ArithmeticGeometry.Descent.CMVariety.AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V hV) N.charts.total
    let q₀ := N.charts.base (x.comp
      (IsScalarTower.toAlgHom ℂ R (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V)))
    ∃ c : ∀ q : F, OpenPartialHomeomorph (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q).left).scheme) E,
      (∀ q ∈ N.neighborhood,
        (1 : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q).left).scheme) ∈ (c q).source ∧ c q 1 = 0 ∧
        (c q).MDifferentiable (𝓘(ℝ, L q)) (𝓘(ℝ, E)) ∧
        (c q).source = (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (s q))) ⁻¹' e.source ∧
        (c q).target = {v | (q, v) ∈ e.target} ∧
        (∀ z ∈ (c q).source, c q z = (e (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map
          (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (s q)) z)).2) ∧
        (∀ v ∈ (c q).target, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (s q)) ((c q).symm v) =
          e.symm (q, v)) ∧
        ContMDiffOn (𝓘(ℂ, L q)) (𝓘(ℂ, E)) ω (c q) (c q).source ∧
        ContMDiffOn (𝓘(ℂ, E)) (𝓘(ℂ, L q)) ω (c q).symm (c q).target) ∧
      ArithmeticGeometry.Descent.CMVariety.LocalPeriod.Abelian.LocalPeriodFamily (fun q : F => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q).left).scheme)
        (fun q => ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L q) (c q))
        (fun q z => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (s q)) z)
        q₀ ∧
      ∀ v : E, ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L q₀) (c q₀) v = 1 →
        ∃ (U : Set F) (period : F → E), IsOpen U ∧ q₀ ∈ U ∧
          DifferentiableOn ℂ period U ∧ period q₀ = v ∧
          ∀ q ∈ U, ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L q) (c q) (period q) = 1 := by
  dsimp only
  let A := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V
  let i := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V hV
  let s := fun q : F => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ R) b (N.charts.base.symm q)
  let H := fun q : F => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q).left).scheme
  let : ∀ q : F, IsIntegral (G.pullback (s q).left).scheme.left := fun q => (present (s q)).isIntegral
  let L := fun q : F => Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension (G.pullback (s q).left).scheme.hom) → ℂ
  let : ∀ q : F, T2Space (H q) := fun q => (present (s q)).t2Space
  let : ∀ q : F, LieGroup (𝓘(ℝ, L q)) ∞ (H q) := fun q => (present (s q)).nativeRealLieGroup
  let e := ArithmeticGeometry.Descent.CMVariety.AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart A i N.charts.total
  let q₀ := N.charts.base (x.comp (IsScalarTower.toAlgHom ℂ R A))
  obtain ⟨c₀, hc₀, ⟨B, hB, hqB, hBN, hExp, _, hExpHol⟩,
    W, δ, r, logarithm, hW, hqW, hWN, hδ, hr, hrδ, hlog, hlogHol, hright, hleft⟩ :=
    IntrinsicHolomorphicExponentialOn.IntrinsicFamilyPeriods.exists_native_holomorphic_exponential_on G present V hV b hi σ hσ N
  let c : ∀ q : F, OpenPartialHomeomorph (H q) E := c₀
  have hc : ∀ q ∈ N.neighborhood,
      (1 : H q) ∈ (c q).source ∧ c q 1 = 0 ∧
      (c q).MDifferentiable (𝓘(ℝ, L q)) (𝓘(ℝ, E)) ∧
      (c q).source = (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (s q))) ⁻¹' e.source ∧
      (c q).target = {v | (q, v) ∈ e.target} ∧
      (∀ z ∈ (c q).source, c q z = (e (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map
        (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (s q)) z)).2) ∧
      ∀ v ∈ (c q).target, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (s q)) ((c q).symm v) =
        e.symm (q, v) := hc₀
  let embed := fun q : F => fun z : H q =>
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (s q)) z
  have hinc (q : F) : Function.Injective (embed q) :=
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion
      (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (s q))).injective
  have hproj (q : F) (hq : q ∈ W) (v : E)
      (hv : embed q (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L q) (c q) v) ∈ e.source) :
      (e (embed q (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L q) (c q) v))).1 = q :=
    ArithmeticGeometry.Descent.CMVariety.FiberChartProjection.Abelian.RelativeCharts.native_fiber_chart_base_coordinate (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) b i hi N.charts q
      (N.withinBase (hWN hq)) (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L q) (G := H q) (c q) v) hv
  have hunit : embed q₀ 1 ∈ e.source := by
    have h := (hc q₀ N.center).1
    rw [(hc q₀ N.center).2.2.2.1] at h
    exact h
  have hunit₀ : e (embed q₀ 1) = (q₀, (0 : E)) := by
    apply Prod.ext
    · exact ArithmeticGeometry.Descent.CMVariety.FiberChartProjection.Abelian.RelativeCharts.native_fiber_chart_base_coordinate (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) b i hi N.charts q₀
        (N.withinBase N.center) (1 : H q₀) hunit
    · exact ((hc q₀ N.center).2.2.2.2.2.1 1 (hc q₀ N.center).1).symm.trans (hc q₀ N.center).2.1
  have hExpChart : DifferentiableOn ℂ
      (fun q : F × E => (e (embed q.1 (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L q.1) (c q.1) q.2))).2)
      (((W ∩ B) ×ˢ Set.univ) ∩ (fun q : F × E =>
        embed q.1 (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L q.1) (c q.1) q.2)) ⁻¹' e.source) := by
    apply (hExpHol.mono (fun q hq => ⟨⟨hq.1.1.2, hq.1.2⟩, hq.2⟩)).congr
    intro q hq
    apply ((hc q.1 (hBN hq.1.1.2)).2.2.2.2.2.1 _ ?_).symm
    rw [(hc q.1 (hBN hq.1.1.2)).2.2.2.1]
    exact hq.2
  have hdata := HolomorphicLocalPeriodFamily.localPeriodFamily_with_holomorphic_continuation_of_logarithm H
    (fun q => ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L q) (c q))
    (fun q => ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential_zero (E := L q) (c q))
    (fun q => ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential_add (E := L q) (c q)) embed hinc q₀
    (fun q => c q) e (W ∩ B) (hW.inter hB) ⟨hqW, hqB⟩
    (hExp.mono (fun q hq => ⟨hq.1.2, hq.2⟩)) hExpChart
    (fun q hq => (hc q (hWN hq.1)).2.1) δ r hδ hr hrδ logarithm
    (hlog.mono (Set.prod_mono inter_subset_left subset_rfl))
    (hlogHol.mono (Set.prod_mono inter_subset_left subset_rfl))
    (fun q hq y hy => (hright q hq.1 y hy).2.2.2)
    (fun q hq => hleft q hq.1) (fun q hq => hproj q hq.1) hunit hunit₀
  have hcomplex (q : F) (hq : q ∈ N.neighborhood) :
      ContMDiffOn (𝓘(ℂ, L q)) (𝓘(ℂ, E)) ω (c q) (c q).source ∧
      ContMDiffOn (𝓘(ℂ, E)) (𝓘(ℂ, L q)) ω (c q).symm (c q).target := by
    obtain ⟨d, _, _, _, hds, hdt, hdf, hdi, hdC, hdInv⟩ :=
      ArithmeticGeometry.Descent.CMVariety.SectionFiberCharts.Abelian.FamilyPoints.exists_identity_fiber_chart G V hV b hi σ hσ N q hq
    have hs : (c q).source = d.source := (hc q hq).2.2.2.1.trans hds.symm
    have ht : (c q).target = d.target := (hc q hq).2.2.2.2.1.trans hdt.symm
    constructor
    · have h : ContMDiffOn (𝓘(ℂ, L q)) (𝓘(ℂ, E)) ω d (c q).source := by rw [hs]; exact hdC
      apply h.congr
      intro z hz
      exact ((hc q hq).2.2.2.2.2.1 z hz).trans (hdf z (hs ▸ hz)).symm
    · have h : ContMDiffOn (𝓘(ℂ, E)) (𝓘(ℂ, L q)) ω d.symm (c q).target := by rw [ht]; exact hdInv
      apply h.congr
      intro v hv
      apply (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion
        (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (s q))).injective
      exact ((hc q hq).2.2.2.2.2.2 v hv).trans (hdi v (ht ▸ hv)).symm
  exact ⟨c, fun q hq => ⟨(hc q hq).1, (hc q hq).2.1, (hc q hq).2.2.1,
    (hc q hq).2.2.2.1, (hc q hq).2.2.2.2.1, (hc q hq).2.2.2.2.2.1,
    (hc q hq).2.2.2.2.2.2, (hcomplex q hq).1, (hcomplex q hq).2⟩, hdata⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicHolomorphicLocalPeriods.IntrinsicFamilyPeriods
