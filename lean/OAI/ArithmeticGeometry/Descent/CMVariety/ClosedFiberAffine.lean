import OAI.ArithmeticGeometry.Descent.CMVariety.FiberChartProjection
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion

/-! # Closed Fiber Affine -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.ClosedFiberAffine.Abelian.FamilyPoints

noncomputable section

/-!
The actual affine coordinate map of a scheme fiber is surjective, and its
characters have exactly the expected fiber image. This supplies the quotient
and range data used by the analytic fiber-chart construction.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion Set
open scoped Classical

variable {X S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}

abbrev fiberAffineAlgebra (p : X ⟶ S) (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (V : X.left.Opens) :
    CommAlgCat ℂ :=
  AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.fiber p s) ((AbelianFamilyPoints.FamilyPoints.fiberInclusion p s).left ⁻¹ᵁ V)

theorem fiberAffinePullback_range (p : X ⟶ S) (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (V : X.left.Opens) (hV : IsAffineOpen V) :
    Set.range (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap (AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback (AbelianFamilyPoints.FamilyPoints.fiberInclusion p s) V)) =
      {y : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V) |
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X V hV y) = s} := by
  let φ := AbelianFamilyPoints.FamilyPoints.fiberInclusion p s
  let Z := AbelianFamilyPoints.FamilyPoints.fiber p s
  let W := φ.left ⁻¹ᵁ V
  have hW : IsAffineOpen W := hV.preimage φ.left
  let h := AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback φ V
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    have he := AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback_point_square φ V hV hW z
    change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X V hV (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h z)) = s
    rw [← he]
    exact (AbelianFamilyPoints.FamilyPoints.fiberHomeomorph p s (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap Z W hW z)).property
  · intro hy
    have hyrange : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X V hV y ∈
        Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ) := by
      rw [AbelianFamilyPoints.FamilyPoints.fiberInclusion_range]
      exact hy
    obtain ⟨z, hz⟩ := hyrange
    have hmap : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ z ∈
        Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X V hV) := ⟨y, hz.symm⟩
    rw [AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_affineOpenPointMap] at hmap
    have hzW : z ∈ Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap Z W hW) := by
      rw [AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_affineOpenPointMap]
      exact hmap
    obtain ⟨w, hw⟩ := hzW
    refine ⟨w, ?_⟩
    apply (AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.isOpenEmbedding_affinePointMap (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V)
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X V hV)).injective
    exact (AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback_point_square φ V hV hW w).symm.trans
      ((congrArg (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ) hw).trans hz)

/-- The coordinate map of the actual affine fiber is a surjective algebra
map; its characters are precisely the native points over the specified base. -/
theorem fiberAffinePullback_surjective_and_range (p : X ⟶ S) (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (V : X.left.Opens) (hV : IsAffineOpen V) :
    Function.Surjective (AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback (AbelianFamilyPoints.FamilyPoints.fiberInclusion p s) V) ∧
      Set.range (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap (AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback (AbelianFamilyPoints.FamilyPoints.fiberInclusion p s) V)) =
        {y : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V) |
          AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X V hV y) = s} :=
  ⟨AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback_surjective (AbelianFamilyPoints.FamilyPoints.fiberInclusion p s) V hV,
    fiberAffinePullback_range p s V hV⟩

/-- In an actual affine base diagram, the native fiber condition is
exactly equality of the base-algebra characters. -/
theorem fiberAffinePullback_range_over_base
    (p : X ⟶ S) (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (V : X.left.Opens) (hV : IsAffineOpen V)
    {R : Type} [CommRing R] [Algebra ℂ R]
    [Algebra R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V)]
    [IsScalarTower ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V)]
    (b : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ S) [IsOpenImmersion b.left]
    (hi : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X V hV ≫ p =
      AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V)
        (IsScalarTower.toAlgHom ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V)) ≫ b)
    (y₀ : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints (fiberAffineAlgebra p s V)) :
    Set.range (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap (AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback (AbelianFamilyPoints.FamilyPoints.fiberInclusion p s) V)) =
      {y : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V) |
        y.comp (IsScalarTower.toAlgHom ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V)) =
          (y₀.comp (AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback (AbelianFamilyPoints.FamilyPoints.fiberInclusion p s) V)).comp
            (IsScalarTower.toAlgHom ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V))} := by
  let A := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V
  let i := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X V hV
  let h := AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback (AbelianFamilyPoints.FamilyPoints.fiberInclusion p s) V
  let x₀ := y₀.comp h
  have h₀ : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X V hV x₀) = s := by
    have hm : x₀ ∈ Set.range (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h) := ⟨y₀, rfl⟩
    rw [fiberAffinePullback_range] at hm
    exact hm
  have hbase (y : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :=
    FiberChartProjection.Abelian.RelativeCharts.nativeAffinePoint_base p b i hi y
  rw [fiberAffinePullback_range]
  ext y
  constructor
  · intro hy
    apply (AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.isOpenEmbedding_affinePointMap (CommAlgCat.of ℂ R) b).injective
    exact (hbase y).symm.trans (hy.trans (h₀.symm.trans (hbase x₀)))
  · intro hy
    exact (hbase y).trans
      ((congrArg (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ R) b) hy).trans
        ((hbase x₀).symm.trans h₀))

end

end OAI.ArithmeticGeometry.Descent.CMVariety.ClosedFiberAffine.Abelian.FamilyPoints
