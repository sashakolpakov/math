import OAI.NumberTheory.PadicHodge.GeometricComparison.OrdinaryAffineTotal

/-! # Indexed Ordinary Cech -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IndexedOrdinaryCech.IndexedOrdinaryQuotientCech

noncomputable section

/-! Ordinary quotient Cech coordinates work for any indexing
category of actual opens preserving the nonempty tuple products. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe v
variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  {C : Type} [Category.{v} C] [HasBinaryProducts C] (F : C ⥤ X.left.Opens)
  {ι : Type} (U : ι → C) (I : Ideal R)
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]

local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotient.functor R I

def diagram := F.op ⋙ OrdinarySection.OrdinarySectionComplexAssembly.diagram R X ⋙ (Q).mapHomologicalComplex (.up ℕ)

def complexIso : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (diagram R X F I) ≅
    ((NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{0} R) F).mapHomologicalComplex (.up ℕ)).obj
      (OrdinaryAffineTotal.OrdinaryAffineQuotientCech.quotientComplex R X I) :=
  (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyTrans.ComplexAssemblyTransport.iso F.op Q (.up ℕ) (OrdinarySection.OrdinarySectionComplexAssembly.diagram R X)).symm ≪≫
    ((AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyTrans.ComplexAssemblyTransport.transport F.op Q).mapHomologicalComplex (.up ℕ)).mapIso
      (OrdinarySection.OrdinarySectionComplexAssembly.iso R X)

def bicomplexIso : CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.bicomplex (IntegralComparison.NonemptyCechNerve.nerve U)
    (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (diagram R X F I)) ≅
      IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal.bicomplex R X (F.obj ∘ U) I :=
  ((IntegralComparison.NonemptyCechNerve.complexFunctor U).mapHomologicalComplex (.up ℕ)).mapIso (complexIso R X F I) ≪≫
    NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso F U (OrdinaryAffineTotal.OrdinaryAffineQuotientCech.quotientComplex R X I)

def totalIso : CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.total (IntegralComparison.NonemptyCechNerve.nerve U) (diagram R X F I) ≅
    (IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal.bicomplex R X (F.obj ∘ U) I).total (.up ℕ) :=
  HomologicalComplex₂.total.mapIso (bicomplexIso R X F U I) (.up ℕ)

variable [X.left.IsSeparated] {κ : Type} (V : κ → X.left.affineOpens)

theorem original : totalIso R X (Affine.OpenProducts.AffineOpenProducts.inclusion X.left) V I =
    OrdinaryAffineTotal.OrdinaryAffineQuotientCech.totalIso R X V I := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IndexedOrdinaryCech.IndexedOrdinaryQuotientCech
