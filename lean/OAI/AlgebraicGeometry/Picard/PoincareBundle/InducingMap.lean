import OAI.AlgebraicGeometry.Picard.PoincareBundle.CubicalInducingProducts
import OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingNormalization
import OAI.AlgebraicGeometry.Picard.PoincareBundle.AbelianGeometricIntegrality
import OAI.AlgebraicGeometry.Picard.PoincareBundle.RepresentedFamilyIsomorphism
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications
import OAI.AlgebraicGeometry.Picard.PoincareBundle.PositiveFormulaIsomorphism

/-! # Inducing Map -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingMap

noncomputable section

/-! An actual ample inducing line constructs its Picard homomorphism and the normalized positive Poincare formula. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedRepresentation OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction
open OAI.AlgebraicGeometry.Picard.PoincareBundle.CubicalInducingProducts

variable {k : Type} [Field k] [IsAlgClosed k] {a : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)

local instance abelianIntegral : GeometricallyIntegral A.scheme.hom :=
  AbelianGeometricIntegrality.geometricallyIntegral A

/-- The actual difference line and its cube-derived products determine the represented map. -/
def hom : A.scheme ⟶ D.abelian.scheme :=
  Product.Map.representedMap (Line.Comparison.Bundle.fromShared (InducingClass.Bundle.line A.scheme L))
    (CubicalInducingProducts.vertical A.scheme L) (CubicalInducingProducts.vertical_isIso A.scheme L) (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D))

/-- The two constructed products prove that the represented map preserves the group law. -/
theorem hom_isMonHom : IsMonHom (InducingMap.hom D L) :=
  Product.Homomorphism.representedMap_isMonHom (Line.Comparison.Bundle.fromShared D.poincare)
    (Vertical.ProductParameters.globalProduct D.abelian.scheme A.scheme (Line.Comparison.Bundle.fromShared D.poincare)
      (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication D))
    (Vertical.ProductParameters.globalProduct_isIso D.abelian.scheme A.scheme (Line.Comparison.Bundle.fromShared D.poincare)
      (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication D))
    (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D)) (SharedRepresentation.universalClass (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D) _ _)
    (Line.Comparison.Bundle.fromShared (InducingClass.Bundle.line A.scheme L))
    (CubicalInducingProducts.vertical A.scheme L) (CubicalInducingProducts.vertical_isIso A.scheme L) (CubicalInducingProducts.horizontal A.scheme L) (CubicalInducingProducts.horizontal_isIso A.scheme L)
    (Product.ParameterSchemes.globalProduct D.abelian.scheme A.scheme (Line.Comparison.Bundle.fromShared D.poincare)
      (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D))
    (Product.ParameterSchemes.globalProduct_isIso D.abelian.scheme A.scheme (Line.Comparison.Bundle.fromShared D.poincare)
      (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D))

/-- The original difference line is the actual Poincare family of the constructed homomorphism. -/
theorem exists_familyIso (o : (L.pullback η[A.scheme].left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Spec (.of k))) :
    Nonempty ((InducingClass.Bundle.line A.scheme L).sheaf ≅
      (D.poincare.pullback (InducingMap.hom D L ⊗ₘ 𝟙 A.scheme).left).sheaf) := by
  have : CompactSpace A.scheme.left := QuasiCompact.compactSpace_of_compactSpace A.scheme.hom
  have : QuasiSeparatedSpace A.scheme.left := quasiSeparatedSpace_of_quasiSeparated A.scheme.hom
  obtain ⟨e, _⟩ := RepresentedFamilyIsomorphism.Family.normalized_iso A (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D)
    (Line.Comparison.Bundle.fromShared (InducingClass.Bundle.line A.scheme L)) (CubicalInducingProducts.vertical A.scheme L) (CubicalInducingProducts.vertical_isIso A.scheme L)
    (Vertical.ProductParameters.globalProduct D.abelian.scheme A.scheme (Line.Comparison.Bundle.fromShared D.poincare)
      (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication D))
    (Vertical.ProductParameters.globalProduct_isIso D.abelian.scheme A.scheme (Line.Comparison.Bundle.fromShared D.poincare)
      (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication D))
    (InducingNormalization.Bundle.firstAxis A.scheme L o)
  exact ⟨e⟩

/-- Ampleness and the actual inducing formula prove positivity of the represented homomorphism over the ground field. -/
theorem positive_formula (hL : L.IsAmple)
    (o : (L.pullback η[A.scheme].left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Spec (.of k))) :
    AbelianScheme.IsogenyQuotient.PositiveFormula.Construction.PositivePoincareFormula A.scheme (D.poincare.pullback (InducingMap.hom D L ⊗ₘ 𝟙 A.scheme).left) := by
  obtain ⟨e⟩ := exists_familyIso D L o
  exact PositiveFormulaIsomorphism.of_iso A.scheme (InducingClass.Bundle.line A.scheme L)
    (D.poincare.pullback (InducingMap.hom D L ⊗ₘ 𝟙 A.scheme).left) e
    ⟨L, hL, ⟨o⟩, ⟨InducingClass.Bundle.formula A.scheme L⟩⟩

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingMap
