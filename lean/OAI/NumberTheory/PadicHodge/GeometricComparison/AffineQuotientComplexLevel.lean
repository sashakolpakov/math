import OAI.NumberTheory.PadicHodge.GeometricComparison.OrdinaryAffineTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.QuotientLevel

/-! # Affine Quotient Complex Level -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.AffineQuotientComplexLevel.OrdinaryAffineQuotientComplexLevel

noncomputable section

/-! The original affine-diagram and open-presheaf quotient complex
coordinates commute with coefficient-ideal transitions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  (I J : Ideal R) (hIJ : I ≤ J)

local notation "D" => CategoryTheory.Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left) ⋙ OAI.NumberTheory.PadicHodge.GeometricComparison.OrdinarySection.OrdinarySectionComplexAssembly.diagram R X

def diagramMap : OrdinaryAffineTotal.OrdinaryAffineQuotientCech.diagram R X I ⟶ OrdinaryAffineTotal.OrdinaryAffineQuotientCech.diagram R X J :=
  Functor.whiskerLeft D ((IntegralComparison.Module.IdealQuotientTransition.transformation R I J hIJ).mapHomologicalComplex (.up ℕ))

def presheafMap : OrdinaryAffineTotal.OrdinaryAffineQuotientCech.quotientComplex R X I ⟶ OrdinaryAffineTotal.OrdinaryAffineQuotientCech.quotientComplex R X J :=
  ((IntegralCech.QuotientLevel.IntegralCechQuotientLevel.presheaves R X I J hIJ).mapHomologicalComplex (.up ℕ)).app (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)

theorem natural : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (diagramMap R X I J hIJ) ≫
    (OrdinaryAffineTotal.OrdinaryAffineQuotientCech.complexIso R X J).hom =
    (OrdinaryAffineTotal.OrdinaryAffineQuotientCech.complexIso R X I).hom ≫
      ((NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{0} R)
        (Affine.OpenProducts.AffineOpenProducts.inclusion X.left)).mapHomologicalComplex (.up ℕ)).map (presheafMap R X I J hIJ) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := (I • (⊤ : Submodule R (((D).obj U).X i))).mkQ_surjective x
  rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.AffineQuotientComplexLevel.OrdinaryAffineQuotientComplexLevel
