import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicHolomorphicExponential
import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicMorphismOverlap
import OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicPowerContinuation
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ChartExponentialPowers
import OAI.ArithmeticGeometry.Descent.CMVariety.FiberChartProjection

/-! # Intrinsic Holomorphic Exponential On -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicHolomorphicExponentialOn.IntrinsicFamilyPeriods

noncomputable section

/-! The actual native exponential is jointly holomorphic on its entire
intersection with the original total-space chart over an open base
neighborhood. Algebraic power maps supply the continuation from zero. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set _root_.Metric
open scoped Classical ContDiff _root_.Manifold _root_.CategoryTheory.MonObj NNReal

variable {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {E F : Type}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [CompleteSpace E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
  [CompleteSpace F] [FiniteDimensional ℂ F]

/-- A normalized actual relative chart supplies native fiber charts,
continuous genuine exponentials, and a common continuous local logarithm. -/
theorem exists_native_holomorphic_exponential_on
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
        (let φ := fun q : F × E => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map
          (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (s q.1))
          (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L q.1)
            (G := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q.1).left).scheme) (c q.1) q.2)
        ∃ B : Set F, IsOpen B ∧
          N.charts.base (x.comp
            (IsScalarTower.toAlgHom ℂ R (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V))) ∈ B ∧
          B ⊆ N.neighborhood ∧ ContinuousOn φ (B ×ˢ Set.univ) ∧
          IsOpen ((B ×ˢ Set.univ) ∩ φ ⁻¹' e.source) ∧
          DifferentiableOn ℂ (fun q : F × E =>
            c q.1 (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L q.1) (c q.1) q.2))
            ((B ×ˢ Set.univ) ∩ φ ⁻¹' e.source)) ∧
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
  let φ := fun (c : ∀ q : F, OpenPartialHomeomorph (H q) E) (q : F × E) =>
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (s q.1))
      (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L q.1) (G := H q.1) (c q.1) q.2)
  obtain ⟨c, hc, ⟨B₀, hB₀, hqB₀, hFull⟩, ⟨U, hU, hqU, hExp⟩,
    W, δ, r, logarithm, hW, hqW, hWN, hδ, hr, hrδ, hcont, hhol, hright, hleft⟩ :=
    IntrinsicHolomorphicExponential.IntrinsicFamilyPeriods.exists_native_holomorphic_exponential G present V hV b hi σ hσ N
  let f := fun q : F × E => c q.1 (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L q.1) (c q.1) q.2)
  let power := fun n => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.FamilyPowerMaps.Abelian.FamilyPoints.familyPowerMap S G n)
  have hpower (n : ℕ) := IntrinsicMorphismOverlap.native_morphism_coordinates_contDiffOn A i N.charts.total
    N.forwardTotal N.charts.regularTotal (ArithmeticGeometry.Descent.CMVariety.FamilyPowerMaps.Abelian.FamilyPoints.familyPowerMap S G n)
  have hscale (n : ℕ) (hn : 0 < n) (q : F × E) :
      power n (φ c (q.1, (n : ℝ)⁻¹ • q.2)) = φ c q := by
    dsimp only [power, φ]
    rw [ArithmeticGeometry.Descent.CMVariety.FamilyPowerMaps.Abelian.FamilyPoints.familyPowerMap_fiber]
    exact congrArg (fun z : H q.1 =>
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (s q.1)) z)
      (ChartExponentialPowers.chartExponential_inv_nat_smul_pow (L := L q.1) (G := H q.1) (c q.1) n hn q.2)
  have hcoord (q : F × E) (hq : q.1 ∈ N.neighborhood ∩ B₀)
      (hs : φ c q ∈ e.source) : e (φ c q) = (q.1, f q) := by
    apply Prod.ext
    · exact ArithmeticGeometry.Descent.CMVariety.FiberChartProjection.Abelian.RelativeCharts.native_fiber_chart_base_coordinate (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) b i hi N.charts q.1
        (N.withinBase hq.1) (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L q.1) (G := H q.1) (c q.1) q.2) hs
    · apply ((hc q.1 hq.1).2.2.2.2.2.1 _ ?_).symm
      rw [(hc q.1 hq.1).2.2.2.1]
      exact hs
  have hsource₀ : φ c (q₀, 0) ∈ e.source := by
    dsimp only [φ]
    rw [ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential_zero]
    have h := (hc q₀ N.center).1
    rw [(hc q₀ N.center).2.2.2.1] at h
    exact h
  obtain ⟨B, hB, hqB, hBB₀, hD, hDiff⟩ := HolomorphicPowerContinuation.exists_holomorphic_power_domain
    (φ c) f e power (fun n => (hpower n).2.differentiableOn (by simp))
    (fun n => (hpower n).1) hscale (N.neighborhood ∩ B₀) (N.isOpen.inter hB₀)
    q₀ ⟨N.center, hqB₀⟩ hcoord
    (hFull.mono (fun q hq => ⟨hq.1.2, hq.2⟩)) U hU hqU hExp hsource₀
  refine ⟨c, hc, ⟨B, hB, hqB, fun _ h => (hBB₀ h).1, ?_, hD, hDiff⟩,
    W, δ, r, logarithm, hW, hqW, hWN, hδ, hr, hrδ, hcont, hhol, hright, hleft⟩
  exact hFull.mono (fun q hq => ⟨(hBB₀ hq.1).2, hq.2⟩)

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicHolomorphicExponentialOn.IntrinsicFamilyPeriods
