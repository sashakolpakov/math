import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismSectionAlgebraPullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.OrdinarySection
import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBicomplex

/-! # Morphism Ordinary Forms -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismOrdinaryForms.AffineMorphismOrdinaryForms

noncomputable section

/-! The actual ordinary section-algebra map on affine pairs has
the original geometric de Rham pullback as each form component. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u
variable (R : Type u) [CommRing R]
  {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)

def sourceOpens := MorphismPairs.AffineMorphismPairs.source f.left ⋙ NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left
def targetOpens := MorphismPairs.AffineMorphismPairs.target f.left ⋙ NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion Y.left
def sourcePullback := NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{u} R) (sourceOpens R f)
def targetPullback := NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{u} R) (targetOpens R f)

instance source_additive : (sourcePullback R f).Additive := by
  dsimp only [sourcePullback]
  infer_instance
instance target_additive : (targetPullback R f).Additive := by
  dsimp only [targetPullback]
  infer_instance

def transformation := Functor.whiskerRight (MorphismSectionAlgebraPullback.AffineMorphismSectionAlgebraPullback.transformation R f)
  (NumberTheory.PadicHodge.IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.functor R)

def sourceIso : ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ)
    ((sourceOpens R f).op ⋙ NumberTheory.PadicHodge.GeometricComparison.OrdinarySection.OrdinarySectionComplexAssembly.diagram R X) ≅
      ((sourcePullback R f).mapHomologicalComplex (.up ℕ)).obj (DeRhamGlobalId.DeRhamGlobal.presheafComplex R X) :=
  ((sourcePullback R f).mapHomologicalComplex (.up ℕ)).mapIso (NumberTheory.PadicHodge.GeometricComparison.OrdinarySection.OrdinarySectionComplexAssembly.iso R X)
def targetIso : ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ)
    ((targetOpens R f).op ⋙ NumberTheory.PadicHodge.GeometricComparison.OrdinarySection.OrdinarySectionComplexAssembly.diagram R Y) ≅
      ((targetPullback R f).mapHomologicalComplex (.up ℕ)).obj (DeRhamGlobalId.DeRhamGlobal.presheafComplex R Y) :=
  ((targetPullback R f).mapHomologicalComplex (.up ℕ)).mapIso (NumberTheory.PadicHodge.GeometricComparison.OrdinarySection.OrdinarySectionComplexAssembly.iso R Y)

def map := (targetIso R f).inv ≫ ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (transformation R f) ≫ (sourceIso R f).hom

theorem component (q : ℕ) (U : (MorphismPairs.AffineMorphismPairs.Charts f.left)ᵒᵖ) :
    ((AffineMorphismOrdinaryForms.map R f).f q).app U = OpenSectionGeometricPullback.DeRhamPullback.formsPullbackLE f U.unop.val.2.val U.unop.val.1.val U.unop.property q := by
  change 𝟙 _ ≫ OpenSectionGeometricPullback.DeRhamPullback.formsPullbackLE f U.unop.val.2.val U.unop.val.1.val U.unop.property q ≫ 𝟙 _ = _
  simp only [Category.comp_id, Category.id_comp]

theorem original_pullback (q : ℕ) (U : (MorphismPairs.AffineMorphismPairs.Charts f.left)ᵒᵖ) :
    ((AffineMorphismOrdinaryForms.map R f).f q).app U =
      ((DeRhamPullbackTo.DeRhamPullback.presheafPullback f).f q).app (op U.unop.val.2.val) ≫
        (DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X q).map (homOfLE U.unop.property).op :=
  (component R f q U).trans (OpenSectionGeometricPullback.DeRhamPullback.formsPullbackLE_eq f U.unop.val.2.val U.unop.val.1.val U.unop.property q)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismOrdinaryForms.AffineMorphismOrdinaryForms
