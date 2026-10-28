import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalEvaluation
import OAI.AlgebraicGeometry.CycleClass.Thom.AnalyticProductMaps
import OAI.AlgebraicGeometry.CycleClass.Thom.HolomorphicHomeomorph
import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.ProductIs

/-! # Diagonal Submersion -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalSubmersion.Constructions

noncomputable section

/-! The genuine affine diagonal section vector is holomorphic and
submersive in the native manifold of the scheme product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.CartesianMonoidalCategory
open scoped MonoidalCategory TensorProduct _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalEvaluation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.EtaleSectionVector.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.VectorHeadChange.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.AnalyticCoordinateDifference.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PointProduct.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.AnalyticProductMaps.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.HolomorphicHomeomorph.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left] [IsIntegral X.left] [Smooth X.hom]

local instance : IsIntegral (X ⊗ X).left := ProductIs.Constructions.affineProduct_isIntegral X X
local instance : Smooth (X ⊗ X).hom :=
  inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.fst X.hom X.hom ≫ X.hom))

local notation "MX" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ
abbrev productModel := Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension (X ⊗ X).hom) → ℂ
local notation "MP" => OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalSubmersion.Constructions.productModel X

local instance (priority := low) : ChartedSpace (MX × MX) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :=
  prodChartedSpace MX (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) MX (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)

theorem pointProduct_analytic :
    ContMDiff 𝓘(ℂ, MP) 𝓘(ℂ, MX × MX) ω (Scheme.PointProduct.Constructions.schemePointProductHomeomorph X X) := by
  rw [modelWithCornersSelf_prod]
  exact (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (fst X X) ω).prodMk (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (snd X X) ω)

theorem pointProduct_symm_analytic :
    ContMDiff 𝓘(ℂ, MX × MX) 𝓘(ℂ, MP) ω (Scheme.PointProduct.Constructions.schemePointProductHomeomorph X X).symm := by
  rw [modelWithCornersSelf_prod]
  have h := AnalyticProductMaps.Constructions.contMDiff_schemePairMap (𝟙 (X ⊗ X)) ω
  simp only [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_id] at h
  exact h

theorem pointProduct_differential_bijective (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (X ⊗ X)) :
    Function.Bijective (mfderiv 𝓘(ℂ, MP) 𝓘(ℂ, MX × MX) (Scheme.PointProduct.Constructions.schemePointProductHomeomorph X X) x) :=
  HolomorphicHomeomorph.Constructions.homeomorph_mfderiv_bijective (Scheme.PointProduct.Constructions.schemePointProductHomeomorph X X)
    ((pointProduct_analytic X).mdifferentiable (by simp))
    ((pointProduct_symm_analytic X).mdifferentiable (by simp)) x

variable (n : ℕ) [Algebra (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]
  [IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]

theorem diagonalVector_analytic : ContMDiff 𝓘(ℂ, MP) 𝓘(ℂ, Fin n → ℂ) ω (DiagonalEvaluation.Constructions.diagonalVector X n) := by
  rw [DiagonalEvaluation.Constructions.diagonalVector_eq_difference]
  exact (AnalyticCoordinateDifference.Constructions.coordinateDifference_analytic n _ (EtaleSectionVector.Constructions.coordinateVector_analytic X n)).comp (pointProduct_analytic X)

variable [Algebra.FormallyEtale (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]

theorem diagonalVector_submersion (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (X ⊗ X)) :
    Function.Surjective (mfderiv 𝓘(ℂ, MP) 𝓘(ℂ, Fin n → ℂ) (DiagonalEvaluation.Constructions.diagonalVector X n) x) := by
  rw [DiagonalEvaluation.Constructions.diagonalVector_eq_difference]
  have h := mfderiv_comp x
    ((AnalyticCoordinateDifference.Constructions.coordinateDifference_analytic n _ (EtaleSectionVector.Constructions.coordinateVector_analytic X n)).mdifferentiableAt (by simp))
    ((pointProduct_analytic X).mdifferentiableAt (by simp))
  exact (congrArg (fun L : MP →L[ℂ] (Fin n → ℂ) => Function.Surjective L) h).mpr
    ((AnalyticCoordinateDifference.Constructions.coordinateDifference_submersion n _ (EtaleSectionVector.Constructions.coordinateVector_analytic X n)
      (fun y => (EtaleSectionVector.Constructions.coordinateVector_differential_bijective X n y).2) _).comp
        (pointProduct_differential_bijective X x).2)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalSubmersion.Constructions
