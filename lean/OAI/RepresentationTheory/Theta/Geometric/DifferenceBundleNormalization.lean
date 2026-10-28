import OAI.RepresentationTheory.Theta.Geometric.Picard.PicardPullback
import OAI.RepresentationTheory.Theta.Geometric.LineBundleFieldTriviality

/-! # Difference Bundle Normalization -/

namespace OAI.RepresentationTheory.Theta.Geometric.DifferenceBundleNormalization

noncomputable section

/-! The algebraic difference bundle is trivial along either identity axis
when its underlying line bundle has trivial identity fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem picardPullback_constant_eq_one {X S : Scheme.{u}} (p : X ⟶ S) (z : S ⟶ X)
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (hz : Nonempty ((L.pullback z).sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)) :
    Picard.PicardPullback.picardPullback (p ≫ z) (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = 1 := by
  have h : Picard.PicardPullback.picardPullback z (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = 1 := Quotient.sound hz
  rw [← Picard.PicardPullback.picardPullback_comp, h, map_one]

theorem algebraicDifferenceBundle_axis_left {X Z S : Scheme.{u}}
    (p : X ⟶ S) (z : S ⟶ X) (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (hz : Nonempty ((L.pullback z).sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S))
    (p₁ p₂ m : Z ⟶ X) (a : X ⟶ Z)
    (h₁ : a ≫ p₁ = 𝟙 X) (h₂ : a ≫ p₂ = p ≫ z) (hm : a ≫ m = 𝟙 X) :
    Nonempty (((AlgebraicDifferenceBundle.algebraicDifferenceBundle L p₁ p₂ m).pullback a).sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) := by
  have h := Picard.PicardPullback.algebraicDifferenceBundle_pullback_class L p₁ p₂ m a
  rw [h₁, h₂, hm, Picard.PicardPullback.picardPullback_id, picardPullback_constant_eq_one p z L hz,
    inv_one, mul_inv_cancel, one_mul] at h
  exact Quotient.exact h

theorem algebraicDifferenceBundle_axis_right {X Z S : Scheme.{u}}
    (p : X ⟶ S) (z : S ⟶ X) (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (hz : Nonempty ((L.pullback z).sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S))
    (p₁ p₂ m : Z ⟶ X) (a : X ⟶ Z)
    (h₁ : a ≫ p₁ = p ≫ z) (h₂ : a ≫ p₂ = 𝟙 X) (hm : a ≫ m = 𝟙 X) :
    Nonempty (((AlgebraicDifferenceBundle.algebraicDifferenceBundle L p₁ p₂ m).pullback a).sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) := by
  have h := Picard.PicardPullback.algebraicDifferenceBundle_pullback_class L p₁ p₂ m a
  rw [h₁, h₂, hm, Picard.PicardPullback.picardPullback_id, picardPullback_constant_eq_one p z L hz,
    inv_one, mul_one, mul_inv_cancel] at h
  exact Quotient.exact h

end

end OAI.RepresentationTheory.Theta.Geometric.DifferenceBundleNormalization
