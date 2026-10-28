import OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicFamilyLogarithm
import OAI.ArithmeticGeometry.Descent.CMVariety.FiberChartProjection
import OAI.ArithmeticGeometry.Descent.CMVariety.LogarithmicTorsionRigidity

/-! # Intrinsic Torsion Rigidity -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicTorsionRigidity.Abelian.FamilyPoints

noncomputable section

/-!
Local uniqueness of positive-order torsion sections in an actual
abelian-scheme family. The common logarithm and the uniform gap in its
actual exponential kernels are constructed from the normalized chart.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set _root_.Metric
open scoped Classical ContDiff _root_.Manifold _root_.CategoryTheory.MonObj NNReal _root_.Topology

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {E F : Type}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
  [CompleteSpace F]

theorem native_torsion_section_locally_one
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
    (N : RegularSectionCharts.Abelian.RelativeCharts.SectionNormalizedCharts (E := E) (F := F) x σ)
    (n : ℕ) (hn : 0 < n) :
    let s := fun q : F => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap
      (CommAlgCat.of ℂ R) b (N.charts.base.symm q)
    let q₀ := N.charts.base (x.comp
      (IsScalarTower.toAlgHom ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V)))
    ∀ z : ∀ q : F, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q).left).scheme,
      z q₀ = 1 →
      ContinuousAt (fun q => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map
        (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) (s q)) (z q)) q₀ →
      (∀ᶠ q in 𝓝 q₀, z q ^ n = 1) → ∀ᶠ q in 𝓝 q₀, z q = 1 := by
  dsimp only
  let A := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V
  let i := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap (AbelianFamilyPoints.FamilyPoints.total S G) V hV
  let s := fun q : F => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap
    (CommAlgCat.of ℂ R) b (N.charts.base.symm q)
  let H := fun q : F => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q).left).scheme
  let : ∀ q : F, IsIntegral (G.pullback (s q).left).scheme.left :=
    fun q => (present (s q)).isIntegral
  let L := fun q : F => Fin
    (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (G.pullback (s q).left).scheme.hom) → ℂ
  let : ∀ q : F, T2Space (H q) := fun q => (present (s q)).t2Space
  let : ∀ q : F, LieGroup (𝓘(ℝ, L q)) ∞ (H q) :=
    fun q => (present (s q)).nativeRealLieGroup
  let e := AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart A i N.charts.total
  let q₀ := N.charts.base (x.comp (IsScalarTower.toAlgHom ℂ R A))
  intro z hz₀ hzcont hztorsion
  obtain ⟨c, hc, _, W, δ, logarithm, hW, hqW, hWN, hδ, hlog, hright, hleft⟩ :=
    IntrinsicFamilyLogarithm.Abelian.FamilyPoints.exists_native_relative_logarithm G present V hV b hi σ hσ N
  let exponential := fun q : F => ChartEndomorphismDerivative.Abelian.chartExponential (E := L q) (G := H q) (c q)
  let embed := fun q : F => fun z : H q =>
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) (s q)) z
  have hinc (q : F) : Function.Injective (embed q) :=
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion
      (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) (s q))).injective
  have hproj (q : F) (hq : q ∈ W) (u : H q)
      (hu : embed q u ∈ e.source) : (e (embed q u)).1 = q :=
    FiberChartProjection.Abelian.RelativeCharts.native_fiber_chart_base_coordinate (AbelianFamilyPoints.FamilyPoints.projection S G) b i hi N.charts q
      (N.withinBase (hWN hq)) u hu
  have hunit : embed q₀ 1 ∈ e.source := by
    have h := (hc q₀ N.center).1
    rw [(hc q₀ N.center).2.2.2.1] at h
    exact h
  have hunit₀ : e (embed q₀ 1) = (q₀, (0 : E)) := by
    apply Prod.ext
    · exact hproj q₀ hqW 1 hunit
    · exact ((hc q₀ N.center).2.2.2.2.2.1 1 (hc q₀ N.center).1).symm.trans
        (hc q₀ N.center).2.1
  have hlog₀ : logarithm (q₀, 0) = 0 := by
    have h := hleft q₀ hqW 0 (mem_closedBall_self (le_of_lt hδ))
    rw [ChartEndomorphismDerivative.Abelian.chartExponential_zero, (hc q₀ N.center).2.1] at h
    exact h (mem_closedBall_self (le_of_lt (half_pos hδ)))
  obtain ⟨l, hlcont, hlzero, hl⟩ := LogarithmicTorsionRigidity.Abelian.exists_continuous_section_logarithm H exponential
    embed hinc e W hW q₀ hqW δ hδ logarithm hlog hlog₀
    (fun q hq y hy => (hright q hq y hy).2.2) hproj hunit hunit₀ z hz₀ hzcont
  apply LogarithmicTorsionRigidity.Abelian.torsion_section_eq_one_of_continuous_logarithm H exponential
    (fun q => ChartEndomorphismDerivative.Abelian.chartExponential_zero (E := L q) (c q))
    (fun q => ChartEndomorphismDerivative.Abelian.chartExponential_add (E := L q) (c q)) q₀ W (hW.mem_nhds hqW) δ hδ
    _ z l hlcont hlzero hl n hn hztorsion
  intro q hq
  exact PeriodContinuation.Abelian.no_small_periods_of_local_logarithm (exponential q)
    (ChartEndomorphismDerivative.Abelian.chartExponential_zero (E := L q) (c q)) (c q) (hc q (hWN hq)).2.1
    δ (le_of_lt hδ) (fun y => logarithm (q, y)) (hleft q hq)

end

end OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicTorsionRigidity.Abelian.FamilyPoints
