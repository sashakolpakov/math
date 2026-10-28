import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.ClassMorphism
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ParameterPoincareSquare
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ParameterDeformationClass

/-! # Parameter Class Morphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ParameterClassMorphism

noncomputable section

/-! An original Poincare pullback square intertwines the actual
parameter deformation classes with native structure-sheaf H1 pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {X Y P Q : Over Foundations.Scheme.ProjectiveSpace.complexBase} [GrpObj P] [GrpObj Q]
    [LocallyOfFiniteType X.hom] [IsReduced X.left] [LocallyOfFiniteType Y.hom] [IsReduced Y.left]
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ X).left))]
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ Y).left))]
    (f : X ⟶ Y) (d : Q ⟶ P) [IsMonHom d]
    (L : HilbertConstruction.Line.Bundles.LineBundle (P ⊗ X).left) (K : HilbertConstruction.Line.Bundles.LineBundle (Q ⊗ Y).left)
    (eL : (L.pullback (lift (1 : X ⟶ P) (𝟙 X)).left).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule X.left)
    (eK : (K.pullback (lift (1 : Y ⟶ Q) (𝟙 Y)).left).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule Y.left)

theorem dualParameterDeformationClass_morphism
    (h : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (d ⊗ₘ 𝟙 X).left (HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 Q ⊗ₘ f).left (HilbertConstruction.Line.Bundles.LineBundle.classOf K))
    (t : DualOpen.Lifts.DualSchemePoints Q 1) :
    ParameterDeformationClass.dualParameterDeformationClass L eL (ParameterPoincareSquare.dualPointPostcompose d t) =
      StructurePullback.nativeStructureH1Pullback f (ParameterDeformationClass.dualParameterDeformationClass K eK t) :=
  (congrArg (DualLine.ClassKernel.dualLineKernelCohomology X) (ParameterPoincareSquare.dualParameterLineKernel_poincareSquare f d L K eL eK h t)).trans
    (DualLine.ClassMorphism.dualLineKernelCohomology_morphism f (ParameterLineKernel.dualParameterLineKernel K eK t))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ParameterClassMorphism
