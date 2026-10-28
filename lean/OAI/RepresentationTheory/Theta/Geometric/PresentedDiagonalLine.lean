import OAI.RepresentationTheory.Theta.Geometric.Relative.DiagonalLine
import OAI.RepresentationTheory.Theta.Geometric.DiagonalLineTransport
import OAI.ArithmeticGeometry.Descent.CMVariety.StandardModuli

/-! # Presented Diagonal Line -/

namespace OAI.RepresentationTheory.Theta.Geometric.PresentedDiagonalLine

noncomputable section

/-! The total polarization diagonal restricts to the exact diagonal
biextension on every original presented complex fiber. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

open OAI.ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian

variable {g : ℕ} {S : Scheme.{0}} {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (D : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme) (s : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ S)
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (A.pullback s))

def presentedRelativeDiagonalLine : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle P.variety.toOver.left :=
  (Relative.DiagonalLine.relativeDiagonalLine D p).pullback (P.comparison.inv.left ≫ pullback.fst A.scheme.hom s)

def presentedRelativeBiextension : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (P.variety.toOver ⊗ P.variety.toOver).left :=
  (AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.polarizationBiextensionAt D p s).pullback (P.comparison.inv ⊗ₘ P.comparison.inv).left

def presentedRelativeDiagonalIso :
    ((presentedRelativeBiextension D p s P).pullback
      (lift (𝟙 P.variety.toOver) (𝟙 P.variety.toOver)).left).sheaf ≅
        (presentedRelativeDiagonalLine D p s P).sheaf :=
  DiagonalLineTransport.diagonalLineTransportIso P.comparison.inv (AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.polarizationBiextensionAt D p s) ≪≫
    (Scheme.Modules.pullback P.comparison.inv.left).mapIso (Relative.DiagonalLine.relativeDiagonalLine_fiber_iso D p s) ≪≫
      (Scheme.Modules.pullbackComp P.comparison.inv.left (pullback.fst A.scheme.hom s)).app
        (Relative.DiagonalLine.relativeDiagonalLine D p).sheaf

end

end OAI.RepresentationTheory.Theta.Geometric.PresentedDiagonalLine
