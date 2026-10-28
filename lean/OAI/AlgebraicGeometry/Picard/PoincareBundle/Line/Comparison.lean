import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Bundles
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

/-! # Comparison -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle

noncomputable section

/-! The PoincareBundle and shared geometric line-bundle APIs describe the same actual module sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- Retain the actual sheaf and its local frames in the shared line-bundle API. -/
def toShared {X : Scheme.{u}} (L : Bundles.LineBundle X) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X :=
  ⟨L.sheaf, L.isLine⟩

/-- Retain the same sheaf and frames in the PoincareBundle line-bundle API. -/
def fromShared {X : Scheme.{u}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) : Bundles.LineBundle X :=
  ⟨L.sheaf, L.locallyTrivial⟩

/-- The comparison is an equivalence of actual line-bundle presentations. -/
def lineEquiv (X : Scheme.{u}) : Bundles.LineBundle X ≃ AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X where
  toFun := toShared
  invFun := fromShared
  left_inv _ := rfl
  right_inv _ := rfl

/-- The induced equivalence identifies actual isomorphism classes. -/
def classEquiv (X : Scheme.{u}) : Bundles.LineBundleClass X ≃ AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X where
  toFun := Quotient.map toShared (fun _ _ h => h)
  invFun := Quotient.map fromShared (fun _ _ h => h)
  left_inv q := by induction q using Quotient.inductionOn with | _ L => rfl
  right_inv q := by induction q using Quotient.inductionOn with | _ L => rfl

/-- The comparison commutes with arbitrary scheme pullback. -/
theorem classEquiv_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) (q : Bundles.LineBundleClass Y) :
    classEquiv X (Bundles.LineBundleClass.pullback f q) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (classEquiv Y q) := by
  induction q using Quotient.inductionOn with
  | _ L => rfl

/-- The comparison identifies the actual trivial line classes. -/
theorem classEquiv_trivial (X : Scheme.{u}) :
    classEquiv X (Bundles.LineBundleClass.mk (Bundles.LineBundle.trivial X)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass X := rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle
