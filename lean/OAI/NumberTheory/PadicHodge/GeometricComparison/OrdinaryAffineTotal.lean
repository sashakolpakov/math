import OAI.NumberTheory.PadicHodge.GeometricComparison.OrdinarySection
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.Iso
import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProductPreservation
import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBicomplex
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.CechQuotientTotal

/-! # Ordinary Affine Total -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.OrdinaryAffineTotal.OrdinaryAffineQuotientCech

noncomputable section

/-! The ordinary coefficient-quotient diagram on affine opens gives the
original full de Rham quotient Cech total on the same open cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R))) [X.left.IsSeparated]
  {ι : Type} (U : ι → X.left.affineOpens) (I : Ideal R)

local notation "inclusion" => OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left
local notation "quotient" => OAI.NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotient.functor R I

def diagram := (inclusion).op ⋙ OrdinarySection.OrdinarySectionComplexAssembly.diagram R X ⋙
  (quotient).mapHomologicalComplex (.up ℕ)

def quotientComplex := ((IntegralCech.QuotientTotal.IntegralCechQuotientTotal.presheaves R X I).mapHomologicalComplex (.up ℕ)).obj
  (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)

def complexIso : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (diagram R X I) ≅
    ((NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{0} R) inclusion).mapHomologicalComplex (.up ℕ)).obj
      (quotientComplex R X I) :=
  (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyTrans.ComplexAssemblyTransport.iso (inclusion).op quotient (.up ℕ)
    (OrdinarySection.OrdinarySectionComplexAssembly.diagram R X)).symm ≪≫
    ((AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyTrans.ComplexAssemblyTransport.transport (inclusion).op quotient).mapHomologicalComplex (.up ℕ)).mapIso
      (OrdinarySection.OrdinarySectionComplexAssembly.iso R X)

local instance tuple_preserves (n : ℕ) (t : Fin (n + 1) → ι) :
    PreservesLimit (Discrete.functor (U ∘ t)) inclusion :=
  Affine.OpenProductPreservation.AffineOpenProductPreservation.inclusion_preserves X.left (U ∘ t)

def bicomplexIso :
    CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.bicomplex (IntegralComparison.NonemptyCechNerve.nerve U)
      (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (diagram R X I)) ≅
    IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal.bicomplex R X (fun i => (U i).val) I :=
  ((IntegralComparison.NonemptyCechNerve.complexFunctor U).mapHomologicalComplex (.up ℕ)).mapIso (complexIso R X I) ≪≫
    NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso inclusion U (quotientComplex R X I)

def totalIso : CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.total (IntegralComparison.NonemptyCechNerve.nerve U) (diagram R X I) ≅
    (IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal.bicomplex R X (fun i => (U i).val) I).total (.up ℕ) :=
  HomologicalComplex₂.total.mapIso (bicomplexIso R X U I) (.up ℕ)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.OrdinaryAffineTotal.OrdinaryAffineQuotientCech
