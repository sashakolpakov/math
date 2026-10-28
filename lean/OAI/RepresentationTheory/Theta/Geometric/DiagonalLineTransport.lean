import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BiextensionFormulaTransport

/-! # Diagonal Line Transport -/

namespace OAI.RepresentationTheory.Theta.Geometric.DiagonalLineTransport

noncomputable section

/-! The diagonal restriction of an actual product line bundle commutes
with changing both factors by the same scheme map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable {S : Scheme.{0}} {X Y : Over S}

theorem diagonal_tensor_square (f : X ⟶ Y) :
    lift (𝟙 X) (𝟙 X) ≫ (f ⊗ₘ f) = f ≫ lift (𝟙 Y) (𝟙 Y) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · simp

def diagonalLineTransportIso (f : X ⟶ Y) (B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Y ⊗ Y).left) :
    ((B.pullback (f ⊗ₘ f).left).pullback (lift (𝟙 X) (𝟙 X)).left).sheaf ≅
      ((B.pullback (lift (𝟙 Y) (𝟙 Y)).left).pullback f.left).sheaf :=
  AlgebraicGeometry.AbelianModuli.ReferenceFamily.BiextensionFormulaTransport.lineBundlePullbackSquareIso (lift (𝟙 X) (𝟙 X)).left (f ⊗ₘ f).left
    f.left (lift (𝟙 Y) (𝟙 Y)).left (congrArg Over.Hom.left (diagonal_tensor_square f)) B

end

end OAI.RepresentationTheory.Theta.Geometric.DiagonalLineTransport
