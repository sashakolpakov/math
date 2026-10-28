import OAI.NumberTheory.PadicHodge.GeometricComparison.AffineQuotientComplexLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.CechQuotientLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBicomplexNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.TotalFunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology

/-! # Affine Quotient Cech Level -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.AffineQuotientCechLevel.OrdinaryAffineQuotientCechLevel

noncomputable section

/-! The original affine-to-open-cover quotient Cech total isomorphisms
respect coefficient-ideal level transitions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R))) [X.left.IsSeparated]
  {ι : Type} (U : ι → X.left.affineOpens) (I J : Ideal R) (hIJ : I ≤ J)

abbrev Values := ModuleCat.{0} R
local notation "inc" => OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left
local notation "F" => Functor.mapHomologicalComplex (OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.complexFunctor (A := OAI.NumberTheory.PadicHodge.GeometricComparison.AffineQuotientCechLevel.OrdinaryAffineQuotientCechLevel.Values R) U) (ComplexShape.up ℕ)
local notation "a" => OAI.NumberTheory.PadicHodge.GeometricComparison.AffineQuotientComplexLevel.OrdinaryAffineQuotientComplexLevel.diagramMap R X I J hIJ
local notation "b" => OAI.NumberTheory.PadicHodge.GeometricComparison.AffineQuotientComplexLevel.OrdinaryAffineQuotientComplexLevel.presheafMap R X I J hIJ
local notation "pull" => Functor.mapHomologicalComplex (OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := OAI.NumberTheory.PadicHodge.GeometricComparison.AffineQuotientCechLevel.OrdinaryAffineQuotientCechLevel.Values R) inc) (ComplexShape.up ℕ)

local instance tuple_preserves (q : ℕ) (t : Fin (q + 1) → ι) : PreservesLimit (Discrete.functor (U ∘ t)) inc :=
  Affine.OpenProductPreservation.AffineOpenProductPreservation.inclusion_preserves X.left (U ∘ t)

def bicomplexMap :
    CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.bicomplex (IntegralComparison.NonemptyCechNerve.nerve U)
      (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (OrdinaryAffineTotal.OrdinaryAffineQuotientCech.diagram R X I)) ⟶
    CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.bicomplex (IntegralComparison.NonemptyCechNerve.nerve U)
      (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (OrdinaryAffineTotal.OrdinaryAffineQuotientCech.diagram R X J)) :=
  (F).map (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) a)

theorem first_square : bicomplexMap R X U I J hIJ ≫ (F).map (OrdinaryAffineTotal.OrdinaryAffineQuotientCech.complexIso R X J).hom =
    (F).map (OrdinaryAffineTotal.OrdinaryAffineQuotientCech.complexIso R X I).hom ≫ (F).map ((pull).map b) :=
  ((F).map_comp (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) a) (OrdinaryAffineTotal.OrdinaryAffineQuotientCech.complexIso R X J).hom).symm.trans
    ((congrArg (F).map (AffineQuotientComplexLevel.OrdinaryAffineQuotientComplexLevel.natural R X I J hIJ)).trans
      ((F).map_comp (OrdinaryAffineTotal.OrdinaryAffineQuotientCech.complexIso R X I).hom ((pull).map b)))

theorem bicomplex : bicomplexMap R X U I J hIJ ≫ (OrdinaryAffineTotal.OrdinaryAffineQuotientCech.bicomplexIso R X U J).hom =
    (OrdinaryAffineTotal.OrdinaryAffineQuotientCech.bicomplexIso R X U I).hom ≫
      IntegralCech.CechQuotientLevel.IntegralCechQuotientLevel.bicomplexMap R X (fun i => (U i).val) I J hIJ :=
  ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ (first_square R X U I J hIJ)
    (NonemptyCech.ProductBicomplexNaturality.NonemptyCechProductBicomplexNaturality.natural (A := Values R) inc U b)

theorem natural : (CechAssembly.TotalFunctor.CechAssemblyTotalFunctor.functor (IntegralComparison.NonemptyCechNerve.nerve U)).map a ≫
    (OrdinaryAffineTotal.OrdinaryAffineQuotientCech.totalIso R X U J).hom =
    (OrdinaryAffineTotal.OrdinaryAffineQuotientCech.totalIso R X U I).hom ≫
      IntegralCech.CechQuotientLevel.IntegralCechQuotientLevel.map R X (fun i => (U i).val) I J hIJ := by
  let T := HomologicalComplex₂.totalFunctor (ModuleCat.{0} R) (.up ℕ) (.up ℕ) (.up ℕ)
  exact (T.map_comp (bicomplexMap R X U I J hIJ) (OrdinaryAffineTotal.OrdinaryAffineQuotientCech.bicomplexIso R X U J).hom).symm.trans
    ((congrArg T.map (bicomplex R X U I J hIJ)).trans
      (T.map_comp (OrdinaryAffineTotal.OrdinaryAffineQuotientCech.bicomplexIso R X U I).hom
        (IntegralCech.CechQuotientLevel.IntegralCechQuotientLevel.bicomplexMap R X (fun i => (U i).val) I J hIJ)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.AffineQuotientCechLevel.OrdinaryAffineQuotientCechLevel
