import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicReference.TestRationalMarking
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.LevelTransport

/-! # Test Level -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The actual native comparison carries every ordered prescribed
reference level label to the corresponding test-family level point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] Complex.BallPeriods.restrictComplexBase
open OAI.RepresentationTheory.Theta.Geometric.Intrinsic.LevelTransport

attribute [local irreducible] Models.FinePELModel.complexTestFamily Models.FinePELModel.referenceTestFiberIso Models.FinePELModel.nativeReferenceTestFiberIso

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ)
    (hP : P.IsAdmissible) (hκ : κ.comp iota = P.μ)
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : S ⟶ M.complexFiber κ)
    (a : P.domain) (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (hy : y ≫ f = M.referencePoint hM κ hP hκ a)

theorem Models.FinePELModel.nativeReferenceTestFiberIso_level
    (c : Multiplicative (Fin (2 * (3 * s)) → ZMod N)) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (M.nativeReferenceTestFiberIso hM κ hP hκ f a y hy).hom
      ((((Reference.AlgebraicModel.referenceAlgebraicModel (Reference.Fiber.referenceAnalyticFiber P hP a) hP).fixedFullLevel N).hom.app
        (.op (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)))) (LocallyConstant.const Foundations.Scheme.ProjectiveSpace.complexBase c)).val =
      RepresentationTheory.Theta.Geometric.Intrinsic.LevelTransport.presentedFullLevelPoint (M.complexTestFamily κ f).polarized.level y
        (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (M.complexTestFamily κ f).polarized y) c := by
  let A := M.complexTestFamily κ f
  let Q := RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A.polarized y
  have he := (M.referenceTestFiberIso hM κ hP hκ f a y hy).polarized.level
    (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) (LocallyConstant.const Foundations.Scheme.ProjectiveSpace.complexBase c)
  have hh := congrArg (fun u : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (A.polarized.pullback y.left).abelian.scheme =>
    u ≫ Q.comparison.hom) he
  unfold Models.FinePELModel.nativeReferenceTestFiberIso
  exact (Category.assoc _ _ _).symm.trans hh

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
