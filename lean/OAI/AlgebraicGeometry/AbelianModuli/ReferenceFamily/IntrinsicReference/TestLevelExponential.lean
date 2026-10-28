import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicReference.TestLevel
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.RationalExponential
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceIntrinsic.MarkedAction

/-! # Test Level Exponential -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicReference.TestLevelExponential.FinePELModel

noncomputable section

/-! Ordered test-family level labels are exponentials of the exactly
divided vectors of the constructed native reference period marking. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] Complex.BallPeriods.restrictComplexBase
open OAI.RepresentationTheory.Theta.Geometric.Intrinsic.RationalExponential

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

attribute [local irreducible] Models.FinePELModel.complexTestFamily Models.FinePELModel.referenceTestFiberIso Models.FinePELModel.nativeReferenceTestFiberIso

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ)
    (hP : P.IsAdmissible) (hκ : κ.comp iota = P.μ)
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : S ⟶ M.complexFiber κ)
    (a : P.domain) (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (hy : y ≫ f = M.referencePoint hM κ hP hκ a)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.nativeReferenceTestRationalMarking_level (v : P.lattice) :
    RepresentationTheory.Theta.Geometric.Intrinsic.LevelTransport.presentedFullLevelPoint (M.complexTestFamily κ f).polarized.level y
      (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (M.complexTestFamily κ f).polarized y)
      (Multiplicative.ofAdd (P.fixedLevelLabel hP N v)) =
        HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints
          (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (M.complexTestFamily κ f).polarized y).variety.toOver)
          ((N : ℝ)⁻¹ • (M.nativeReferenceTestRationalMarking hM κ hP hκ f a y hy v.val).val) := by
  let R := Reference.AlgebraicModel.referenceAlgebraicModel (Reference.Fiber.referenceAnalyticFiber P hP a) hP
  let e := M.nativeReferenceTestFiberIso hM κ hP hκ f a y hy
  have : IsMonHom e.hom := M.nativeReferenceTestFiberIso_group hM κ hP hκ f a y hy
  have he := M.nativeReferenceTestFiberIso_level hM κ hP hκ f a y hy
    (Multiplicative.ofAdd (P.fixedLevelLabel hP N v))
  change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.hom
    (((R.fixedFullLevel N).hom.app (.op (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))))
      (LocallyConstant.const Foundations.Scheme.ProjectiveSpace.complexBase (Multiplicative.ofAdd (P.fixedLevelLabel hP N v)))).val = _ at he
  rw [R.fixedFullLevel_native_reference] at he
  exact he.symm.trans (RepresentationTheory.Theta.Geometric.Intrinsic.RationalExponential.nativeMap_rational_exp e.hom (N : ℝ)⁻¹ (R.nativeReferenceMarking v.val))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicReference.TestLevelExponential.FinePELModel
