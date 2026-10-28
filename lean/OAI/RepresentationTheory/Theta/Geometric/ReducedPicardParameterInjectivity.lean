import OAI.RepresentationTheory.Theta.Geometric.ParameterizedPicardClass
import OAI.AlgebraicGeometry.Albanese.Construction.ClosedPoints
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs

/-! # Reduced Picard Parameter Injectivity -/

namespace OAI.RepresentationTheory.Theta.Geometric.ReducedPicardParameterInjectivity

noncomputable section

/-! Complex parameter separation extends to every reduced test scheme
locally of finite type by naturality and native morphism detection. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs
open _root_.CategoryTheory.MonoidalCategory

theorem parameterPicardClass_reduced_injective {A P : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    [LocallyOfFiniteType P.hom] [IsSeparated P.hom]
    (Q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A).left)
    (hinj : Function.Injective (fun p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P => ParameterizedPicardClass.parameterPicardClass Q p))
    (T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType T.hom] [IsReduced T.left] :
    Function.Injective (fun t : T ⟶ P => ParameterizedPicardClass.parameterPicardClass Q t) := by
  intro x y hxy
  apply AlgebraicGeometry.Albanese.Construction.ClosedPoints.hom_ext_of_points T P x y
  intro p
  apply hinj
  exact (ParameterizedPicardClass.parameterPicardClass_naturality Q x p).symm.trans
    ((congrArg ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).obj.map p.op) hxy).trans
      (ParameterizedPicardClass.parameterPicardClass_naturality Q y p))

end

end OAI.RepresentationTheory.Theta.Geometric.ReducedPicardParameterInjectivity
