import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomogeneousBaseTwists
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomogeneityLineBaseChange

/-! # Normalized Rigidified Family -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.NormalizedRigidifiedFamily.Geometric

noncomputable section

/-! Normalize any original line family into an actual relative
rigidified family. Its value in the original Picard sheaf and its
all-test homogeneity are preserved by the proved normalization maps. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction

variable {S : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (U : Over S)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (U ⊗ A.scheme).left)

def normalizedRigidifiedFamily : AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A.scheme U where
  bundle := FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle A.scheme U L
  axis := FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle_axis A.scheme U L

theorem normalizedRigidifiedFamily_value_id :
    (normalizedRigidifiedFamily A U L).relativeValue (𝟙 U) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) := by
  change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U)
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 U ⊗ₘ 𝟙 A.scheme).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle A.scheme U L))) = _
  rw [id_tensorHom_id]
  change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U)
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 (U ⊗ A.scheme).left)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle A.scheme U L))) = _
  exact (congrArg (fun q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (U ⊗ A.scheme).left =>
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U) q)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle A.scheme U L)))).trans
    (AbelianModuli.ReferenceFamily.HomogeneityLineBaseChange.normalizedProductBundle_relative A.scheme U L)

theorem normalizedRigidifiedFamily_homogeneous
    (hL : A.IsHomogeneousPicardClass U (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) :
    A.IsHomogeneousPicardClass U (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (normalizedRigidifiedFamily A U L).bundle) :=
  AbelianModuli.ReferenceFamily.HomogeneousBaseTwists.normalizedProductBundle_homogeneous A L hL

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.NormalizedRigidifiedFamily.Geometric
