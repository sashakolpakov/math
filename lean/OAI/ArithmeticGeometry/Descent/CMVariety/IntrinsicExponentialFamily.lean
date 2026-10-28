import OAI.ArithmeticGeometry.Descent.CMVariety.SectionFiberCharts
import OAI.ArithmeticGeometry.Descent.CMVariety.FiberGroupLaws
import OAI.ArithmeticGeometry.Descent.CMVariety.LocalExponentialFamily
import OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicFiberLieGroup
import OAI.ArithmeticGeometry.Descent.CMVariety.ExponentialScaling
import OAI.ArithmeticGeometry.Descent.CMVariety.FamilyPowerMaps

/-! # Intrinsic Exponential Family -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicExponentialFamily.Abelian.FamilyPoints

noncomputable section

/-!
Construct a continuous actual exponential family at every tangent velocity
over the central base in the constructed normalized relative charts. The fiber
charts and multiplication comparison are derived from the actual scheme;
no exponential continuity or analytic uniformization is assumed.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set _root_.Metric
open scoped Classical ContDiff _root_.Manifold _root_.CategoryTheory.MonObj NNReal

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {E F : Type}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
  [CompleteSpace F]

/-- A normalized actual relative chart supplies native fiber charts and
a continuous family of the genuine invariant exponentials near zero. -/
theorem exists_native_relative_exponential
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
        ∀ v ∈ (c q).target,
          AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) (s q)) ((c q).symm v) =
            e.symm (q, v)) ∧
      ∃ r : ℝ≥0, 0 < r ∧ ∃ ε : ℝ, 0 < ε ∧
        ContinuousOn
          (fun z : (F × E) × ℝ =>
            AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) (s z.1.1))
              (AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.exp (E := L z.1.1) (G := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s z.1.1).left).scheme)
                (z.2 • ExponentialChartODE.Abelian.chartVelocity (E := L z.1.1) (c z.1.1) z.1.2)))
          (closedBall (N.charts.base (x.comp
            (IsScalarTower.toAlgHom ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V))),
              (0 : E)) r ×ˢ Ioo (-ε) ε) ∧
        ∀ v : E, ContinuousAt
          (fun q : F × E => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) (s q.1))
            (AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.exp (E := L q.1) (G := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q.1).left).scheme)
              (ExponentialChartODE.Abelian.chartVelocity (E := L q.1) (c q.1) q.2)))
          (N.charts.base (x.comp
            (IsScalarTower.toAlgHom ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V))), v) := by
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
  have hcharts (q : F) : ∃ c : OpenPartialHomeomorph (H q) E, q ∈ N.neighborhood →
      (1 : H q) ∈ c.source ∧ c 1 = 0 ∧ c.MDifferentiable (𝓘(ℝ, L q)) (𝓘(ℝ, E)) ∧
      c.source = (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) (s q))) ⁻¹' e.source ∧
      c.target = {v | (q, v) ∈ e.target} ∧
      (∀ z ∈ c.source, c z = (e (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map
        (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) (s q)) z)).2) ∧
      ∀ v ∈ c.target, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) (s q)) (c.symm v) =
        e.symm (q, v) := by
    by_cases hq : q ∈ N.neighborhood
    · obtain ⟨c, hc1, hc0, hmd, hs, ht, hf, hi, _, _⟩ :=
        SectionFiberCharts.Abelian.FamilyPoints.exists_identity_fiber_chart G V hV b hi σ hσ N q hq
      exact ⟨c, fun _ => ⟨hc1, hc0, hmd, hs, ht, hf, hi⟩⟩
    · let emptyChart : OpenPartialHomeomorph (H q) E := {
        toFun := fun _ => 0
        invFun := fun _ => 1
        source := ∅
        target := ∅
        map_source' := mapsTo_empty _ _
        map_target' := mapsTo_empty _ _
        left_inv' := eqOn_empty _ _
        right_inv' := eqOn_empty _ _
        continuousOn_toFun := continuousOn_empty _
        continuousOn_invFun := continuousOn_empty _
        open_source := isOpen_empty
        open_target := isOpen_empty }
      exact ⟨emptyChart, fun h => (hq h).elim⟩
  choose c hc using hcharts
  have hx : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i x =
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i x ≫ AbelianFamilyPoints.FamilyPoints.projection S G) ≫ AbelianFamilyPoints.FamilyPoints.identitySection S G := by
    have he := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comap A (CommAlgCat.of ℂ R) σ i
      (x.comp (IsScalarTower.toAlgHom ℂ R A))
    have hxσ : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap σ (x.comp (IsScalarTower.toAlgHom ℂ R A)) = x := N.onSection
    rw [hσ, hxσ, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comp] at he
    have hb := FiberChartProjection.Abelian.RelativeCharts.nativeAffinePoint_base (AbelianFamilyPoints.FamilyPoints.projection S G) b i hi x
    change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i x ≫ AbelianFamilyPoints.FamilyPoints.projection S G = _ at hb
    rw [hb]
    exact he.symm
  obtain ⟨f, D, hf, hD, hD₀, hpair, hm, _, hproduct⟩ :=
    LocalizedFamily.Abelian.RelativeCharts.exists_local_analytic_familyMultiplication G b i hi N hx
  let m : F × (E × E) → E := fun z =>
    (LocalizedFamily.Abelian.RelativeCharts.familyMultiplicationCoordinates G b i hi N f z).2
  have hm' : ContDiffAt ℝ 2 m (q₀, (0, 0)) :=
    ((hm.snd.restrict_scalars ℝ).contDiffAt (hD.mem_nhds hD₀)).of_le (by simp)
  have he₀ : (q₀, (0 : E)) ∈ e.target := by
    have he := N.charts.total.map_source N.charts.point
    rw [N.center_coordinates] at he
    exact he
  obtain ⟨r, hr, ε, hε, _, hexp⟩ := LocalExponentialFamily.Abelian.exists_continuous_local_exponential_family L H c
    (fun q => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) (s q)))
    e.symm N.neighborhood N.isOpen q₀ N.center e.target e.open_target he₀
    (fun q hq => (hc q hq).2.2.1) (fun q hq => (hc q hq).1)
    (fun q hq => (hc q hq).2.1) (fun q hq => (hc q hq).2.2.2.2.1)
    e.symm.continuousOn (fun q hq => (hc q hq).2.2.2.2.2.2)
    m hm' D hD hD₀ (by
      intro q hq u v huv
      exact FiberGroupLaws.Abelian.RelativeCharts.familyMultiplicationCoordinates_eq_fiber_chart G b i hi N f hf q (s q) (c q)
        (hc q hq).2.2.2.1 (hc q hq).2.2.2.2.1 (hc q hq).2.2.2.2.2.1
        (hc q hq).2.2.2.2.2.2 u v (hpair huv) (hproduct _ huv))
  obtain ⟨U, hU, hU₀, htimeOne⟩ := ExponentialScaling.Abelian.exists_open_exponential_neighborhood L H c
    (fun q => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) (s q)))
    q₀ r hr ε hε hexp
  have hall (v : E) := ExponentialScaling.Abelian.continuousAt_exponential_of_power_maps L H c
    (fun q => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) (s q)))
    (fun n => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FamilyPowerMaps.Abelian.FamilyPoints.familyPowerMap S G n))
    (FamilyPowerMaps.Abelian.FamilyPoints.familyPowerMap_continuous S G)
    (fun n q u => FamilyPowerMaps.Abelian.FamilyPoints.familyPowerMap_fiber S G n (s q) u)
    q₀ U hU hU₀ htimeOne v
  exact ⟨c, hc, r, hr, ε, hε, hexp, hall⟩

end

end OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicExponentialFamily.Abelian.FamilyPoints
