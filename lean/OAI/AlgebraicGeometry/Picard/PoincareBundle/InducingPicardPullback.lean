import OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingMap
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.PicardPullback
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.FamilyMap
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames

/-! # Inducing Picard Pullback -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingPicardPullback

noncomputable section

/-! Actual product-line recovery proves the required dual-pullback equation for the homomorphism induced by the quotient line. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedRepresentation
open OAI.AlgebraicGeometry.Picard.PoincareBundle.CubicalInducingProducts OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor

variable {k : Type} [Field k] [IsAlgClosed k] {a : ℕ}
  {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))} (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
  (f : A.scheme ⟶ B.scheme) [IsMonHom f] (p : A.scheme ⟶ DA.abelian.scheme)
  (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.scheme.left)

local instance abelianIntegral : GeometricallyIntegral B.scheme.hom :=
  AbelianGeometricIntegrality.geometricallyIntegral B

/-- The equation follows from the actual sheaf recovery and Picard representation. -/
theorem equation
    (e : (Scheme.Modules.pullback (f ⊗ₘ f).left).obj (InducingClass.Bundle.line B.scheme L).sheaf ≅
      (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared DA.poincare) p).sheaf) :
    f ≫ InducingMap.hom DB L ≫ DualMaps.representedDualMap
      (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA)) (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)) f = p := by
  let Dv := AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication DA
  let Fv := Poincare.TransverseFrames.sourceVertical p (Line.Comparison.Bundle.fromShared DA.poincare) Dv
  have h := Product.PicardPullback.representedMap_pullback f f (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared DA.poincare) p)
    (Line.Comparison.Bundle.fromShared (InducingClass.Bundle.line B.scheme L)) e
    (Vertical.ProductParameters.globalProduct A.scheme A.scheme (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared DA.poincare) p) Fv)
    (Vertical.ProductParameters.globalProduct_isIso A.scheme A.scheme (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared DA.poincare) p) Fv)
    (CubicalInducingProducts.vertical B.scheme L) (CubicalInducingProducts.vertical_isIso B.scheme L)
    (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA)) (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB))
  exact h.trans (Product.FamilyMap.Family.representedMap_familyLine (Line.Comparison.Bundle.fromShared DA.poincare) p
    (Vertical.ProductParameters.globalProduct DA.abelian.scheme A.scheme (Line.Comparison.Bundle.fromShared DA.poincare) Dv)
    (Vertical.ProductParameters.globalProduct_isIso DA.abelian.scheme A.scheme (Line.Comparison.Bundle.fromShared DA.poincare) Dv)
    (Vertical.ProductParameters.globalProduct A.scheme A.scheme (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared DA.poincare) p) Fv)
    (Vertical.ProductParameters.globalProduct_isIso A.scheme A.scheme (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared DA.poincare) p) Fv)
    (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA)) (SharedRepresentation.universalClass (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA) _ _))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingPicardPullback
