import OAI.NumberTheory.PadicHodge.IntegralComparison.Small.OrdinaryCechTotal

/-! # Indexed Ordinary Cech -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IndexedOrdinaryCech.Ordinary

noncomputable section

/-! Ordinary de Rham Cech coordinates for any category indexing
actual open subsets and preserving their nonempty intersections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u c v
variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  {C : Type c} [Category.{v} C] [HasBinaryProducts C] (F : C ⥤ X.left.Opens)
  {ι : Type} (U : ι → C)
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]

def diagram := F.op ⋙ GeometricComparison.OrdinarySection.OrdinarySectionComplexAssembly.diagram R X

def complexIso : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (diagram R X F) ≅
    ((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{u} R) F).mapHomologicalComplex (.up ℕ)).obj
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X) :=
  (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyTrans.ComplexAssemblyTransport.iso F.op (𝟭 (ModuleCat.{u} R)) (.up ℕ)
    (GeometricComparison.OrdinarySection.OrdinarySectionComplexAssembly.diagram R X)).symm ≪≫
      ((AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyTrans.ComplexAssemblyTransport.transport F.op (𝟭 (ModuleCat.{u} R))).mapHomologicalComplex
        (.up ℕ)).mapIso (GeometricComparison.OrdinarySection.OrdinarySectionComplexAssembly.iso R X)

def bicomplexIso : GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.bicomplex (NonemptyCechNerve.nerve U)
    (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (diagram R X F)) ≅
      GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.bicomplex (NonemptyCechNerve.nerve (F.obj ∘ U))
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X) :=
  ((NonemptyCechNerve.complexFunctor U).mapHomologicalComplex (.up ℕ)).mapIso
      (complexIso R X F) ≪≫
    GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso F U (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)

def totalIso : GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.total (NonemptyCechNerve.nerve U) (diagram R X F) ≅
    (GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.bicomplex (NonemptyCechNerve.nerve (F.obj ∘ U))
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)).total (.up ℕ) :=
  HomologicalComplex₂.total.mapIso (bicomplexIso R X F U) (.up ℕ)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IndexedOrdinaryCech.Ordinary
