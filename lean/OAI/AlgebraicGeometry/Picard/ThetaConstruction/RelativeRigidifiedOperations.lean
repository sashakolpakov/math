import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine
import OAI.RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard
import OAI.AlgebraicGeometry.Picard.Homomorphisms.LineBundleDual
import OAI.AlgebraicGeometry.Picard.Homomorphisms.RelativeGroup

/-! # Relative Rigidified Operations -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeRigidifiedOperations.Geometric

noncomputable section

/-! Pullback and division of actual rigidified lines over the original
base. Their values are computed in the original relative Picard sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction OAI.RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard

variable {S : Scheme} {A B C : Over S} [GrpObj A]

def relativeRigidifiedPullback (D : AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A B) (f : C ⟶ B) :
    AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A C := ⟨D.line f, D.frame f⟩

theorem relativeRigidifiedPullback_value (D : AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A B)
    (f : C ⟶ B) {U : Over S} (a : U ⟶ C) :
    (relativeRigidifiedPullback D f).relativeValue a = D.relativeValue (a ≫ f) :=
  congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op U))
    (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass_baseChange D.bundle f a).symm

def relativeRigidifiedQuotient (D L : AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A B) :
    AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A B where
  bundle := D.bundle.tensor (Homomorphisms.LineBundleDual.Construction.lineBundleDual L.bundle)
  axis := by
    let σ := (lift (𝟙 B) (1 : B ⟶ A)).left
    have hD : RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback σ (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.bundle) = 1 :=
      Quotient.sound ⟨D.axis⟩
    have hL : RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback σ (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L.bundle) = 1 :=
      Quotient.sound ⟨L.axis⟩
    have hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf
        ((D.bundle.tensor (Homomorphisms.LineBundleDual.Construction.lineBundleDual L.bundle)).pullback σ) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass B.left := by
      change RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback σ
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.bundle * (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L.bundle)⁻¹) = 1
      rw [map_mul, map_inv, hD, hL, inv_one, mul_one]
    exact Classical.choice (Quotient.exact hc)

theorem relativeRigidifiedQuotient_value (D L : AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A B)
    {U : Over S} (a : U ⟶ B) :
    (relativeRigidifiedQuotient D L).relativeValue a =
      D.relativeValue a * (L.relativeValue a)⁻¹ := by
  let σ : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor A).obj U ⟶ (B ⊗ A).left := (a ⊗ₘ 𝟙 A).left
  let q := (Homomorphisms.RelativeGroup.Construction.toRelativePicardHom A U).comp (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback σ)
  change q (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.bundle * (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L.bundle)⁻¹) =
    q (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.bundle) * (q (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L.bundle))⁻¹
  rw [map_mul, map_inv]

theorem relativeRigidifiedQuotient_zero_iff (D L : AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A B)
    {U : Over S} (a : U ⟶ B) :
    (relativeRigidifiedQuotient D L).relativeValue a = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A U ↔
      D.relativeValue a = L.relativeValue a := by
  rw [relativeRigidifiedQuotient_value, Homomorphisms.RelativeGroup.Construction.trivialPicardClass_eq_one, mul_inv_eq_one]

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeRigidifiedOperations.Geometric
