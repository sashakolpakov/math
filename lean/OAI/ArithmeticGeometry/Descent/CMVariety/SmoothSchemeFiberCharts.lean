import OAI.ArithmeticGeometry.Descent.CMVariety.ClosedFiberAffine
import OAI.ArithmeticGeometry.Descent.CMVariety.QuotientFiberCharts
import OAI.ArithmeticGeometry.Descent.CMVariety.AnalyticIntrinsicCharts

/-! # Smooth Scheme Fiber Charts -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.SmoothSchemeFiberCharts.Abelian.FamilyPoints

noncomputable section

/-!
Construct differentiable charts on literal smooth integral scheme fibers
from the actual relative affine product chart. The coordinate quotient,
its surjectivity, its point image, and native manifold compatibility are
all supplied by the preceding actual-scheme constructions.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open scoped Classical ContDiff _root_.Manifold

variable {X S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {E F : Type}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem exists_differentiable_schemeFiber_chart
    (p : X ⟶ S) (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    [IsIntegral (AbelianFamilyPoints.FamilyPoints.fiber p s).left] [Smooth (AbelianFamilyPoints.FamilyPoints.fiber p s).hom]
    (V : X.left.Opens) (hV : IsAffineOpen V)
    {R : Type} [CommRing R] [Algebra ℂ R]
    [Algebra R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V)]
    [IsScalarTower ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V)]
    (b : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ S) [IsOpenImmersion b.left]
    (hi : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X V hV ≫ p =
      AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V)
        (IsScalarTower.toAlgHom ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V)) ≫ b)
    (y₀ : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ClosedFiberAffine.Abelian.FamilyPoints.fiberAffineAlgebra p s V))
    (C : SmoothRelativeNeighborhoods.Abelian.RelativeCharts.CompatibleRelativeCharts (R := R)
      (y₀.comp (AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback (AbelianFamilyPoints.FamilyPoints.fiberInclusion p s) V)) (Prod.fst : F × E → F))
    (hforward : RegularRelativeCharts.Abelian.RelativeCharts.HasAnalyticCoordinates C.total) :
    ∃ c : OpenPartialHomeomorph (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (AbelianFamilyPoints.FamilyPoints.fiber p s)) E,
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap (AbelianFamilyPoints.FamilyPoints.fiber p s)
        ((AbelianFamilyPoints.FamilyPoints.fiberInclusion p s).left ⁻¹ᵁ V) (hV.preimage (AbelianFamilyPoints.FamilyPoints.fiberInclusion p s).left) y₀ ∈ c.source ∧
      (∀ z ∈ c.source, c z =
        (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V)
          (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X V hV) C.total
            (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion p s) z)).2) ∧
      c.MDifferentiable
        (𝓘(ℝ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (AbelianFamilyPoints.FamilyPoints.fiber p s).hom) → ℂ))
        (𝓘(ℝ, E)) ∧
      c.source = (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion p s)) ⁻¹'
        (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V)
          (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X V hV) C.total).source ∧
      c.target = {v | (C.base ((y₀.comp (AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback (AbelianFamilyPoints.FamilyPoints.fiberInclusion p s) V)).comp
        (IsScalarTower.toAlgHom ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V))), v) ∈
          C.total.target} ∧
      (∀ v ∈ c.target, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion p s) (c.symm v) =
        (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V)
          (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X V hV) C.total).symm
            (C.base ((y₀.comp (AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback (AbelianFamilyPoints.FamilyPoints.fiberInclusion p s) V)).comp
              (IsScalarTower.toAlgHom ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V))), v)) ∧
      ContMDiffOn
        (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (AbelianFamilyPoints.FamilyPoints.fiber p s).hom) → ℂ))
        (𝓘(ℂ, E)) ω c c.source ∧
      ContMDiffOn (𝓘(ℂ, E))
        (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (AbelianFamilyPoints.FamilyPoints.fiber p s).hom) → ℂ))
        ω c.symm c.target := by
  let Z := AbelianFamilyPoints.FamilyPoints.fiber p s
  let φ := AbelianFamilyPoints.FamilyPoints.fiberInclusion p s
  let W := φ.left ⁻¹ᵁ V
  have hW : IsAffineOpen W := hV.preimage φ.left
  let A := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V
  let B := ClosedFiberAffine.Abelian.FamilyPoints.fiberAffineAlgebra p s V
  let i := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X V hV
  let j := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap Z W hW
  let h := AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback φ V
  have hmem : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap Z W hW y₀) ∈ W := by
    have hm : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap Z W hW y₀ ∈
        Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap Z W hW) := ⟨y₀, rfl⟩
    rw [AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_affineOpenPointMap] at hm
    exact hm
  let : Nonempty W := ⟨⟨_, hmem⟩⟩
  let : IsDomain B := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_isDomain Z W
  let : Algebra.Smooth ℂ B := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_smooth Z W hW
  obtain ⟨cB, hcB, hsB, hfB, haB, hiB, htB, hinvB⟩ := QuotientFiberCharts.Abelian.RelativeCharts.exists_analytic_quotient_fiber_chart
    h (AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback_surjective φ V hV) y₀ C hforward
    (ClosedFiberAffine.Abelian.FamilyPoints.fiberAffinePullback_range_over_base p s V hV b hi y₀)
  let c := AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart B j cB
  have hmd : c.MDifferentiable
      (𝓘(ℝ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Z.hom) → ℂ)) (𝓘(ℝ, E)) :=
    ⟨(AnalyticIntrinsicCharts.Abelian.RelativeCharts.nativeAffineChart_real_contMDiffOn B j cB haB).mdifferentiableOn (by simp),
      (AnalyticIntrinsicCharts.Abelian.RelativeCharts.nativeAffineChart_symm_real_contMDiffOn B j cB hiB).mdifferentiableOn (by simp)⟩
  have hsquare (y : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) :
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B j y) =
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (y.comp h) :=
    AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback_point_square φ V hV hW y
  refine ⟨c, ⟨y₀, hcB, rfl⟩, ?_, hmd, ?_, htB, ?_,
    AnalyticIntrinsicCharts.Abelian.RelativeCharts.nativeAffineChart_contMDiffOn B j cB haB,
    AnalyticIntrinsicCharts.Abelian.RelativeCharts.nativeAffineChart_symm_contMDiffOn B j cB hiB⟩
  · intro z hz
    obtain ⟨y, _, rfl⟩ := hz
    change c (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B j y) =
      (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart A i C.total
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B j y))).2
    rw [hsquare]
    change (cB.lift_openEmbedding (AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.isOpenEmbedding_affinePointMap B j))
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B j y) =
      ((C.total.lift_openEmbedding (AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.isOpenEmbedding_affinePointMap A i))
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (y.comp h))).2
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply, OpenPartialHomeomorph.lift_openEmbedding_apply]
    exact hfB y
  · ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hsB] at hy
      exact ⟨y.comp h, hy, (hsquare y).symm⟩
    · rintro ⟨x, hx, he⟩
      have hzW : z ∈ Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap Z W hW) := by
        rw [AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_affineOpenPointMap]
        have hm : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ z ∈
            Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X V hV) := ⟨x, he⟩
        rw [AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_affineOpenPointMap] at hm
        exact hm
      obtain ⟨y, rfl⟩ := hzW
      have hxy : y.comp h = x :=
        (AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.isOpenEmbedding_affinePointMap A i).injective ((hsquare y).symm.trans he.symm)
      refine ⟨y, ?_, rfl⟩
      rw [hsB]
      change y.comp h ∈ C.total.source
      rw [hxy]
      exact hx
  · intro v hv
    change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B j (cB.symm v)) =
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i
        (C.total.symm (C.base ((y₀.comp h).comp (IsScalarTower.toAlgHom ℂ R A)), v))
    rw [hsquare, hinvB v hv]

end

end OAI.ArithmeticGeometry.Descent.CMVariety.SmoothSchemeFiberCharts.Abelian.FamilyPoints
