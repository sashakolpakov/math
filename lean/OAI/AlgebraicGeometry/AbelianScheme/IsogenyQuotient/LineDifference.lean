import OAI.AlgebraicGeometry.Picard.Homomorphisms.SchemeGroup
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.ClassMonoid

/-! # Line Difference -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LineDifference.Construction

noncomputable section

/-! The difference of two actual line bundles tests equality of their
classes after every scheme pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.Homomorphisms.SchemeGroup.Construction

universe u

def lineDifference {X : Scheme.{u}} (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X :=
  L.tensor (Picard.Homomorphisms.LineBundleDual.Construction.lineBundleDual M)

theorem lineDifference_class {X : Scheme.{u}} (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (lineDifference L M) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L / AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M := rfl

theorem lineDifference_pullback_class {X Y : Scheme.{u}} (f : X ⟶ Y) (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (lineDifference L M)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) /
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M) := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClassMonoidHom f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (lineDifference L M)) = _
  rw [lineDifference_class, map_div]
  rfl

theorem lineDifference_pullback_trivial_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (lineDifference L M)) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass X ↔
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M) := by
  rw [lineDifference_pullback_class]
  exact div_eq_one

def lineDifferencePullbackFrame {X Y : Scheme.{u}} (f : X ⟶ Y) (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)
    (h : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M)) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ ((lineDifference L M).pullback f).sheaf :=
  (Classical.choice (Quotient.exact ((lineDifference_pullback_trivial_iff f L M).mpr h))).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LineDifference.Construction
