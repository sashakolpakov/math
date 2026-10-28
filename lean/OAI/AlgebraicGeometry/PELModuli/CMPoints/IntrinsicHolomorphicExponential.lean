import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicHolomorphicLogarithm
import OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicExponentialCoordinates

/-! # Intrinsic Holomorphic Exponential -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicHolomorphicExponential.IntrinsicFamilyPeriods

noncomputable section

/-! The actual native chart exponential is holomorphic jointly in base
and velocity near the identity. The same native charts and the constructed
holomorphic logarithm with both inverse equations are retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set _root_.Metric
open scoped Classical ContDiff _root_.Manifold _root_.CategoryTheory.MonObj NNReal

variable {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {E F : Type}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [CompleteSpace E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
  [CompleteSpace F] [FiniteDimensional ℂ F]

/-- A normalized actual relative chart supplies native fiber charts,
continuous genuine exponentials, and a common continuous local logarithm. -/
theorem exists_native_holomorphic_exponential
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
        (∃ U : Set (F × E), IsOpen U ∧
          (N.charts.base (x.comp
            (IsScalarTower.toAlgHom ℂ R (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V))), (0 : E)) ∈ U ∧
          DifferentiableOn ℂ (fun q : F × E => c q.1 (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L q.1) (c q.1) q.2)) U) ∧
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
  obtain ⟨c, hc, ⟨B, hB, hqB, hFull⟩, W, δ, r, logarithm,
    hW, hqW, hWN, hδ, hr, hrδ, hcont, hhol, hright, hleft⟩ :=
    IntrinsicHolomorphicLogarithm.IntrinsicFamilyPeriods.exists_native_holomorphic_relative_logarithm G present V hV b hi σ hσ N
  have htotal : ContinuousAt (fun q : F × E =>
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (s q.1))
        (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L q.1) (G := H q.1) (c q.1) q.2)) (q₀, 0) :=
    hFull.continuousAt ((hB.prod isOpen_univ).mem_nhds
      (show (q₀, (0 : E)) ∈ B ×ˢ Set.univ from ⟨hqB, mem_univ (0 : E)⟩))
  obtain ⟨U, hU, hqU, hExp⟩ := HolomorphicExponentialCoordinates.exists_holomorphic_chart_exponential_coordinates L H c
    (fun q => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (s q))) e W hW q₀ hqW
    (fun q hq => (hc q (hWN hq)).2.2.1)
    (fun q hq => (hc q (hWN hq)).1) (fun q hq => (hc q (hWN hq)).2.1)
    (fun q hq => (hc q (hWN hq)).2.2.2.1)
    (fun q hq => (hc q (hWN hq)).2.2.2.2.2.1)
    htotal δ r hδ hr hrδ logarithm hhol
    (fun q hq y hy => (hright q hq y hy).2.2.1) hleft
  exact ⟨c, hc, ⟨B, hB, hqB, hFull⟩, ⟨U, hU, hqU, hExp⟩,
    W, δ, r, logarithm, hW, hqW, hWN, hδ, hr, hrδ, hcont, hhol, hright, hleft⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicHolomorphicExponential.IntrinsicFamilyPeriods
