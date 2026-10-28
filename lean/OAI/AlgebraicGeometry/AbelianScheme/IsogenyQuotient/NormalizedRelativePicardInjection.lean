import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RigidifiedRelativeClassDetection
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.LineNormalization

/-! # Normalized Relative Picard Injection -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NormalizedRelativePicardInjection.Construction

noncomputable section

/-! Equality of relative Picard sections is equality of the normalized
actual family classes over a locally noetherian parameter scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  {T : Over (Spec (.of k))} [IsLocallyNoetherian T.left]

set_option backward.isDefEq.respectTransparency false in
theorem normalizedProductClass_eq_of_relative_eq (c d : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A).left)
    (h : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op T) c = (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op T) d) :
    FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductClass A T c = FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductClass A T d := by
  let L := FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle A T c.out
  let M := FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle A T d.out
  have hl : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L = FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductClass A T c :=
    (FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle_class A T c.out).trans
      (congrArg (FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductClass A T) (Quotient.out_eq c))
  have hm : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M = FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductClass A T d :=
    (FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle_class A T d.out).trans
      (congrArg (FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductClass A T) (Quotient.out_eq d))
  have he : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M) := by
    rw [hl, hm, FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductClass_relative, FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductClass_relative]
    exact h
  exact hl.symm.trans ((RigidifiedRelativeClassDetection.Construction.rigidified_class_eq_of_relative_class_eq A L M
    (FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle_axis A T c.out)
    (FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle_axis A T d.out) he).trans hm)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NormalizedRelativePicardInjection.Construction
