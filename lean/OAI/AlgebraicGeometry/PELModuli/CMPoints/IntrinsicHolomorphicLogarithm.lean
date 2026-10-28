import OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicFamilyLogarithm
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ContinuousFamilyPeriods
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ConstructedHolomorphicLogarithm

/-! # Intrinsic Holomorphic Logarithm -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicHolomorphicLogarithm.IntrinsicFamilyPeriods

noncomputable section

/-! Construct a holomorphic common logarithm for the literal native
abelian fibers. The actual exponential, analytic algebraic group law,
full open-neighborhood continuity, and both inverse equations are retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set _root_.Metric
open scoped Classical ContDiff _root_.Manifold _root_.CategoryTheory.MonObj NNReal

open OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicFamilyLogarithm.Abelian.FamilyPoints

variable {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {E F : Type}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [CompleteSpace E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
  [CompleteSpace F] [FiniteDimensional ℂ F]

/-- A normalized actual relative chart supplies native fiber charts,
continuous genuine exponentials, and a common continuous local logarithm. -/
theorem exists_native_holomorphic_relative_logarithm
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
    ∃ c : ∀ q : F, OpenPartialHomeomorph (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q).left).scheme) E,
      (∀ q ∈ N.neighborhood,
        (1 : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q).left).scheme) ∈ (c q).source ∧ c q 1 = 0 ∧
        (c q).MDifferentiable (𝓘(ℝ, L q)) (𝓘(ℝ, E)) ∧
        (c q).source = (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (s q))) ⁻¹' e.source ∧
        (c q).target = {v | (q, v) ∈ e.target} ∧
        (∀ z ∈ (c q).source, c q z = (e (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map
          (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (s q)) z)).2) ∧
        ∀ v ∈ (c q).target,
          ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (s q)) ((c q).symm v) =
            e.symm (q, v)) ∧
        (∃ B : Set F, IsOpen B ∧
          N.charts.base (x.comp
            (IsScalarTower.toAlgHom ℂ R (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V))) ∈ B ∧
          ContinuousOn
            (fun q : F × E => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (s q.1))
              (HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.exp (E := L q.1) (G := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q.1).left).scheme)
                (ArithmeticGeometry.Descent.CMVariety.ExponentialChartODE.Abelian.chartVelocity (E := L q.1) (c q.1) q.2)))
            (B ×ˢ Set.univ)) ∧
        ∃ (W : Set F) (δ r : ℝ) (logarithm : F × E → E),
          IsOpen W ∧ N.charts.base (x.comp
            (IsScalarTower.toAlgHom ℂ R (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V))) ∈ W ∧
          W ⊆ N.neighborhood ∧ 0 < δ ∧ 0 < r ∧ r ≤ δ / 2 ∧
          ContinuousOn logarithm (W ×ˢ closedBall (0 : E) (δ / 2)) ∧
          DifferentiableOn ℂ logarithm (W ×ˢ ball (0 : E) r) ∧
          (∀ q ∈ W, ∀ y ∈ closedBall (0 : E) (δ / 2),
            logarithm (q, y) ∈ closedBall (0 : E) δ ∧
            ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L q) (c q) (logarithm (q, y)) ∈ (c q).source ∧
            c q (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L q) (c q) (logarithm (q, y))) = y ∧
            ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (s q))
              (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L q) (G := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q).left).scheme)
                (c q) (logarithm (q, y))) = e.symm (q, y)) ∧
          ∀ q ∈ W, ∀ v ∈ closedBall (0 : E) δ,
            c q (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L q) (c q) v) ∈ closedBall (0 : E) (δ / 2) →
              logarithm (q, c q (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L q) (c q) v)) = v := by
  intro s hIntegral L hT2 hLie e
  let A := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V
  let i := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V hV
  let H := fun q : F => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q).left).scheme
  let q₀ := N.charts.base (x.comp (IsScalarTower.toAlgHom ℂ R A))
  obtain ⟨c₀, hc₀, r, hr, ε, hε, hexp, _⟩ :=
    ArithmeticGeometry.Descent.CMVariety.IntrinsicExponentialFamily.Abelian.FamilyPoints.exists_native_relative_exponential G present V hV b hi σ hσ N
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
  have hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i x =
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i x ≫ ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) ≫ ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.identitySection S G := by
    have he := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comap A (CommAlgCat.of ℂ R) σ i
      (x.comp (IsScalarTower.toAlgHom ℂ R A))
    have hxσ : Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap σ (x.comp (IsScalarTower.toAlgHom ℂ R A)) = x := N.onSection
    rw [hσ, hxσ, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comp] at he
    have hb := ArithmeticGeometry.Descent.CMVariety.FiberChartProjection.Abelian.RelativeCharts.nativeAffinePoint_base (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) b i hi x
    change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i x ≫ ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G = _ at hb
    rw [hb]
    exact he.symm
  obtain ⟨f, D, hf, hD, hD₀, hpair, hm, _, hproduct⟩ :=
    ArithmeticGeometry.Descent.CMVariety.LocalizedFamily.Abelian.RelativeCharts.exists_local_analytic_familyMultiplication G b i hi N hx
  let m : F × (E × E) → E := fun z =>
    (ArithmeticGeometry.Descent.CMVariety.LocalizedFamily.Abelian.RelativeCharts.familyMultiplicationCoordinates G b i hi N f z).2
  obtain ⟨U, hU, hU₀, htimeOne⟩ := ArithmeticGeometry.Descent.CMVariety.ExponentialScaling.Abelian.exists_open_exponential_neighborhood L H c
    (fun q => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (s q)))
    q₀ r hr ε hε hexp
  have hlog := ConstructedHolomorphicLogarithm.exists_holomorphic_total_chart_logarithm L H c
    (fun q => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (s q)))
    e N.neighborhood N.isOpen q₀ N.center
    (fun q hq => (hc q hq).2.2.1) (fun q hq => (hc q hq).1) (fun q hq => (hc q hq).2.1)
    (fun q hq => (hc q hq).2.2.2.1) (fun q hq => (hc q hq).2.2.2.2.2.1)
    (fun q hq => (hc q hq).2.2.2.2.2.2)
    U hU hU₀ htimeOne m D hD hD₀ (hm.snd.of_le (by simp)) (by
      intro q hq u v huv
      exact ArithmeticGeometry.Descent.CMVariety.FiberGroupLaws.Abelian.RelativeCharts.familyMultiplicationCoordinates_eq_fiber_chart G b i hi N f hf q (s q) (c q)
        (hc q hq).2.2.2.1 (hc q hq).2.2.2.2.1 (hc q hq).2.2.2.2.2.1
        (hc q hq).2.2.2.2.2.2 u v (hpair huv) (hproduct _ huv))
  let B : Set F := {q | (q, (0 : E)) ∈ U}
  have hB : IsOpen B := hU.preimage (continuous_id.prodMk continuous_const)
  have hfull := ContinuousFamilyPeriods.continuousOn_exponential_above_zero_section L H c
    (fun q => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (s q)))
    (fun n => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.FamilyPowerMaps.Abelian.FamilyPoints.familyPowerMap S G n))
    (ArithmeticGeometry.Descent.CMVariety.FamilyPowerMaps.Abelian.FamilyPoints.familyPowerMap_continuous S G)
    (fun n q u => ArithmeticGeometry.Descent.CMVariety.FamilyPowerMaps.Abelian.FamilyPoints.familyPowerMap_fiber S G n (s q) u) U hU htimeOne
  refine ⟨c, hc, ⟨B, hB, hU₀, ?_⟩, hlog⟩
  exact hfull.mono (fun q hq => hq.1)

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicHolomorphicLogarithm.IntrinsicFamilyPeriods
