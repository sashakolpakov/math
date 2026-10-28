import OAI.RepresentationTheory.Theta.Geometric.PoincareFormulaPullback
import OAI.AlgebraicGeometry.Picard.Homomorphisms.SchemeGroup

/-! # Algebraic Difference Bundle -/

namespace OAI.RepresentationTheory.Theta.Geometric.AlgebraicDifferenceBundle

noncomputable section

/-! The actual algebraic difference bundle of a line bundle, with its
native tensor identity. Identifying it with a pulled-back Poincare bundle is
a separate geometric assertion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.Homomorphisms.SchemeGroup.Construction
universe u

def algebraicDifferenceBundle {X Z : Scheme.{u}} (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (p₁ p₂ m : Z ⟶ X) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Z :=
  ((L.pullback m).tensor (AlgebraicGeometry.Picard.Homomorphisms.LineBundleDual.Construction.lineBundleDual (L.pullback p₁))).tensor (AlgebraicGeometry.Picard.Homomorphisms.LineBundleDual.Construction.lineBundleDual (L.pullback p₂))

theorem algebraicDifferenceBundle_formula {X Z : Scheme.{u}} (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (p₁ p₂ m : Z ⟶ X) :
    Nonempty (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (algebraicDifferenceBundle L p₁ p₂ m).sheaf (L.pullback p₁).sheaf)
      (L.pullback p₂).sheaf ≅ (L.pullback m).sheaf) := by
  have h : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (((algebraicDifferenceBundle L p₁ p₂ m).tensor
      (L.pullback p₁)).tensor (L.pullback p₂)) = AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback m) := by
    change (((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback m) * (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback p₁))⁻¹) *
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback p₂))⁻¹) * AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback p₁)) *
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback p₂) = _
    calc
      _ = AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback m) *
          ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback p₁))⁻¹ * AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback p₁)) *
          ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback p₂))⁻¹ * AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback p₂)) := by ac_rfl
      _ = _ := by rw [inv_mul_cancel, inv_mul_cancel, mul_one, mul_one]
  exact Quotient.exact h

end

end OAI.RepresentationTheory.Theta.Geometric.AlgebraicDifferenceBundle
