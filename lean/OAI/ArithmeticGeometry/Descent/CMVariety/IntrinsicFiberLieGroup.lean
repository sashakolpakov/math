import OAI.ArithmeticGeometry.Descent.CMVariety.StandardModuli
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicProductMaps
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveVarietyCompactness

/-! # Intrinsic Fiber Lie Group -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicFiberLieGroup.Abelian

noncomputable section

/-!
The actual native complex points of a smooth integral group scheme form
a Lie group. Actual complex abelian-fiber presentations supply integrality
of the literal scheme fiber, rather than a substitute analytic carrier.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

variable (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom] [GrpObj X]

local notation "NativeModel" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)

/-- The given algebraic group operations are jointly analytic on the
actual native manifold, supplying its complex Lie-group structure. -/
theorem nativeScheme_complexLieGroup :
    LieGroup (𝓘(ℂ, NativeModel)) ∞ (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) where
  contMDiff_mul :=
    (AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicProductMaps.Constructions.contMDiff_product_map (MonObj.mul (X := X))).of_le le_top
  contMDiff_inv := AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (GrpObj.inv (X := X)) ∞

theorem nativeScheme_realLieGroup :
    LieGroup (𝓘(ℝ, NativeModel)) ∞ (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) where
  contMDiff_mul :=
    (AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicProductMaps.Constructions.real_contMDiff_product_map (MonObj.mul (X := X))).of_le le_top
  contMDiff_inv := AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map (GrpObj.inv (X := X)) ∞

namespace ComplexAbelianPresentation

variable {g : ℕ} {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}

/-- The geometric presentation proves that the literal abelian fiber
scheme is integral, through its actual group-preserving scheme isomorphism. -/
theorem _root_.OAI.ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation.isIntegral (c : StandardModuli.Abelian.ComplexAbelianPresentation A) : IsIntegral A.scheme.left := by
  let : IsIntegral c.variety.toOver.left := c.variety.variety.property
  let e : A.scheme.left ≅ c.variety.toOver.left := (Over.forget AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase).mapIso c.comparison
  exact IsIntegral.of_isIso e.inv

/-- The literal fiber has the actual Hausdorff point topology inherited
through its algebraic isomorphism with the geometric presentation. -/
theorem _root_.OAI.ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation.t2Space (c : StandardModuli.Abelian.ComplexAbelianPresentation A) : T2Space (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme) := by
  let : T2Space (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints c.variety.toOver) :=
    c.variety.variety.presentation.complexPoints_t2Space
  let e : A.scheme.left ≅ c.variety.toOver.left := (Over.forget AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase).mapIso c.comparison
  let : IsIso c.comparison.hom.left := e.isIso_hom
  exact (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion c.comparison.hom).isEmbedding.t2Space

theorem _root_.OAI.ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation.nativeRealLieGroup (c : StandardModuli.Abelian.ComplexAbelianPresentation A) :
    let : IsIntegral A.scheme.left := c.isIntegral
    LieGroup (𝓘(ℝ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.scheme.hom) → ℂ)) ∞
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme) := by
  let : IsIntegral A.scheme.left := c.isIntegral
  exact nativeScheme_realLieGroup A.scheme

theorem _root_.OAI.ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation.nativeComplexLieGroup (c : StandardModuli.Abelian.ComplexAbelianPresentation A) :
    let : IsIntegral A.scheme.left := c.isIntegral
    LieGroup (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.scheme.hom) → ℂ)) ∞
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme) := by
  let : IsIntegral A.scheme.left := c.isIntegral
  exact nativeScheme_complexLieGroup A.scheme

end ComplexAbelianPresentation

end

end OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicFiberLieGroup.Abelian
