import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RigidifiedRelativeClassDetection

/-! # Rigidified Product Class Multiplication -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RigidifiedProductClassMultiplication.Construction

noncomputable section

/-! Multiplicativity of the relative values of a rigidified product
family gives multiplication of its actual line-bundle classes. The
identity-axis frames remove the ambiguity of a parameter line. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  {A C : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A] [GrpObj C]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  (Q : FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A C)
  {T : Over (Spec (.of k))} [IsLocallyNoetherian T.left]
  (x y : T ⟶ C)

set_option backward.isDefEq.respectTransparency false in
theorem rigidifiedProductLine_class_mul
    (h : Q.relativeValue (x * y) = Q.relativeValue x * Q.relativeValue y) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (Q.line (x * y)) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (Q.line x) * AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (Q.line y) := by
  let M := (Q.line x).tensor (Q.line y)
  let a := (lift (𝟙 T) (1 : T ⟶ A)).left
  let eM : (Scheme.Modules.pullback a).obj M.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left :=
    Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.tensorIso a (Q.line x) (Q.line y) ≪≫
      AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (Q.frame x) (Q.frame y) ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left)
  apply RigidifiedRelativeClassDetection.Construction.rigidified_class_eq_of_relative_class_eq A (Q.line (x * y)) M (Q.frame (x * y)) eM
  exact h.trans (Picard.Homomorphisms.RelativeGroup.Construction.toRelativePicard_mul A T (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (Q.line x))
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (Q.line y))).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RigidifiedProductClassMultiplication.Construction
