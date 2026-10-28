import OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicFamilyLogarithm
import OAI.ArithmeticGeometry.Descent.CMVariety.LocalPeriod
import OAI.ArithmeticGeometry.Descent.CMVariety.FiberChartProjection

/-! # Intrinsic Local Periods -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicLocalPeriods.Abelian.FamilyPoints

noncomputable section

/-!
Derive local period continuation and uniform small-kernel exclusion for
the actual native exponential of an abelian-scheme family.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set _root_.Metric
open scoped Classical ContDiff _root_.Manifold _root_.CategoryTheory.MonObj NNReal

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {E F : Type}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
  [CompleteSpace F]

/-- A normalized actual relative chart supplies native fiber charts,
continuous genuine exponentials, and a common continuous local logarithm. -/
theorem exists_native_local_period_family
    (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left)
    (present : ∀ s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback s.left))
    (V : (AbelianFamilyPoints.FamilyPoints.total S G).left.Opens) (hV : IsAffineOpen V)
    {R : Type} [CommRing R] [Algebra ℂ R]
    [Algebra R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V)]
    [IsScalarTower ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V)]
    (b : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ S) [IsOpenImmersion b.left]
    (hi : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap (AbelianFamilyPoints.FamilyPoints.total S G) V hV ≫ AbelianFamilyPoints.FamilyPoints.projection S G =
      AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V)
        (IsScalarTower.toAlgHom ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V)) ≫ b)
    (σ : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V →ₐ[ℂ] R)
    (hσ : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V) R σ ≫
          AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap (AbelianFamilyPoints.FamilyPoints.total S G) V hV = b ≫ AbelianFamilyPoints.FamilyPoints.identitySection S G)
    {x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V)}
    (N : RegularSectionCharts.Abelian.RelativeCharts.SectionNormalizedCharts (E := E) (F := F) x σ) :
    let s := fun q : F => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap
      (CommAlgCat.of ℂ R) b (N.charts.base.symm q)
    let : ∀ q : F, IsIntegral (G.pullback (s q).left).scheme.left := fun q => (present (s q)).isIntegral
    let L := fun q : F => Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (G.pullback (s q).left).scheme.hom) → ℂ
    let : ∀ q : F, T2Space (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q).left).scheme) :=
      fun q => (present (s q)).t2Space
    let : ∀ q : F, LieGroup (𝓘(ℝ, L q)) ∞ (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q).left).scheme) :=
      fun q => (present (s q)).nativeRealLieGroup
    let e := AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V)
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap (AbelianFamilyPoints.FamilyPoints.total S G) V hV) N.charts.total
    ∃ c : ∀ q : F, OpenPartialHomeomorph (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q).left).scheme) E,
      (∀ q ∈ N.neighborhood,
        (1 : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q).left).scheme) ∈ (c q).source ∧ c q 1 = 0 ∧
        (c q).MDifferentiable (𝓘(ℝ, L q)) (𝓘(ℝ, E)) ∧
        (c q).source = (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) (s q))) ⁻¹' e.source ∧
        (c q).target = {v | (q, v) ∈ e.target} ∧
        (∀ z ∈ (c q).source, c q z = (e (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map
          (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) (s q)) z)).2) ∧
        (∀ v ∈ (c q).target, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) (s q)) ((c q).symm v) =
          e.symm (q, v)) ∧
        ContMDiffOn (𝓘(ℂ, L q)) (𝓘(ℂ, E)) ω (c q) (c q).source ∧
        ContMDiffOn (𝓘(ℂ, E)) (𝓘(ℂ, L q)) ω (c q).symm (c q).target) ∧
      LocalPeriod.Abelian.LocalPeriodFamily (fun q : F => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q).left).scheme)
        (fun q => ChartEndomorphismDerivative.Abelian.chartExponential (E := L q) (c q))
        (fun q z => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) (s q)) z)
        (N.charts.base (x.comp
          (IsScalarTower.toAlgHom ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V)))) := by
  dsimp only
  let A := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V
  let i := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap (AbelianFamilyPoints.FamilyPoints.total S G) V hV
  let s := fun q : F => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ R) b (N.charts.base.symm q)
  let H := fun q : F => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q).left).scheme
  let : ∀ q : F, IsIntegral (G.pullback (s q).left).scheme.left := fun q => (present (s q)).isIntegral
  let L := fun q : F => Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (G.pullback (s q).left).scheme.hom) → ℂ
  let : ∀ q : F, T2Space (H q) := fun q => (present (s q)).t2Space
  let : ∀ q : F, LieGroup (𝓘(ℝ, L q)) ∞ (H q) := fun q => (present (s q)).nativeRealLieGroup
  let e := AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart A i N.charts.total
  let q₀ := N.charts.base (x.comp (IsScalarTower.toAlgHom ℂ R A))
  obtain ⟨c₀, hc₀, hall, W, δ, logarithm, hW, hqW, hWN, hδ, hlog, hright, hleft⟩ :=
    IntrinsicFamilyLogarithm.Abelian.FamilyPoints.exists_native_relative_logarithm G present V hV b hi σ hσ N
  let c : ∀ q : F, OpenPartialHomeomorph (H q) E := c₀
  have hc : ∀ q ∈ N.neighborhood,
      (1 : H q) ∈ (c q).source ∧ c q 1 = 0 ∧
      (c q).MDifferentiable (𝓘(ℝ, L q)) (𝓘(ℝ, E)) ∧
      (c q).source = (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) (s q))) ⁻¹' e.source ∧
      (c q).target = {v | (q, v) ∈ e.target} ∧
      (∀ z ∈ (c q).source, c q z = (e (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map
        (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) (s q)) z)).2) ∧
      ∀ v ∈ (c q).target, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) (s q)) ((c q).symm v) =
        e.symm (q, v) := hc₀
  let embed := fun q : F => fun z : H q =>
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) (s q)) z
  have hinc (q : F) : Function.Injective (embed q) :=
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion
      (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) (s q))).injective
  have hproj (q : F) (hq : q ∈ W) (v : E)
      (hv : embed q (ChartEndomorphismDerivative.Abelian.chartExponential (E := L q) (c q) v) ∈ e.source) :
      (e (embed q (ChartEndomorphismDerivative.Abelian.chartExponential (E := L q) (c q) v))).1 = q :=
    FiberChartProjection.Abelian.RelativeCharts.native_fiber_chart_base_coordinate (AbelianFamilyPoints.FamilyPoints.projection S G) b i hi N.charts q
      (N.withinBase (hWN hq)) (ChartEndomorphismDerivative.Abelian.chartExponential (E := L q) (G := H q) (c q) v) hv
  have hunit : embed q₀ 1 ∈ e.source := by
    have h := (hc q₀ N.center).1
    rw [(hc q₀ N.center).2.2.2.1] at h
    exact h
  have hunit₀ : e (embed q₀ 1) = (q₀, (0 : E)) := by
    apply Prod.ext
    · exact FiberChartProjection.Abelian.RelativeCharts.native_fiber_chart_base_coordinate (AbelianFamilyPoints.FamilyPoints.projection S G) b i hi N.charts q₀
        (N.withinBase N.center) (1 : H q₀) hunit
    · exact ((hc q₀ N.center).2.2.2.2.2.1 1 (hc q₀ N.center).1).symm.trans (hc q₀ N.center).2.1
  have hdata : LocalPeriod.Abelian.LocalPeriodFamily H (fun q => ChartEndomorphismDerivative.Abelian.chartExponential (E := L q) (c q)) embed q₀ :=
    LocalPeriod.Abelian.localPeriodFamily_of_logarithm H (fun q => ChartEndomorphismDerivative.Abelian.chartExponential (E := L q) (c q))
      (fun q => ChartEndomorphismDerivative.Abelian.chartExponential_zero (E := L q) (c q))
      (fun q => ChartEndomorphismDerivative.Abelian.chartExponential_add (E := L q) (c q)) embed hinc q₀ hall
      (fun q => c q) e W hW hqW (fun q hq => (hc q (hWN hq)).2.1)
      δ hδ logarithm hlog (fun q hq y hy => (hright q hq y hy).2.2) hleft hproj hunit hunit₀
  have hcomplex (q : F) (hq : q ∈ N.neighborhood) :
      ContMDiffOn (𝓘(ℂ, L q)) (𝓘(ℂ, E)) ω (c q) (c q).source ∧
      ContMDiffOn (𝓘(ℂ, E)) (𝓘(ℂ, L q)) ω (c q).symm (c q).target := by
    obtain ⟨d, _, _, _, hds, hdt, hdf, hdi, hdC, hdInv⟩ :=
      SectionFiberCharts.Abelian.FamilyPoints.exists_identity_fiber_chart G V hV b hi σ hσ N q hq
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
      apply (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion
        (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) (s q))).injective
      exact ((hc q hq).2.2.2.2.2.2 v hv).trans (hdi v (ht ▸ hv)).symm
  exact ⟨c, fun q hq => ⟨(hc q hq).1, (hc q hq).2.1, (hc q hq).2.2.1,
    (hc q hq).2.2.2.1, (hc q hq).2.2.2.2.1, (hc q hq).2.2.2.2.2.1,
    (hc q hq).2.2.2.2.2.2, (hcomplex q hq).1, (hcomplex q hq).2⟩, hdata⟩

end

end OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicLocalPeriods.Abelian.FamilyPoints
