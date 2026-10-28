import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.PairSectionAlgebraPullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.OrdinarySection
import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBicomplex

/-! # Pair Ordinary Forms -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.PairOrdinaryForms.AffinePairOrdinaryForms

noncomputable section

/-! The actual ordinary section-algebra map on affine pairs has
the original geometric de Rham pullback as each form component. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (R : Type) [CommRing R]
  {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)

def sourceOpens := MapPairs.AffineMapPairs.source f.left ⋙ OpenProducts.AffineOpenProducts.inclusion X.left
def targetOpens := MapPairs.AffineMapPairs.target f.left ⋙ OpenProducts.AffineOpenProducts.inclusion Y.left
def sourcePullback := NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{0} R) (sourceOpens R f)
def targetPullback := NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{0} R) (targetOpens R f)

instance source_additive : (sourcePullback R f).Additive := by
  dsimp only [sourcePullback]
  infer_instance
instance target_additive : (targetPullback R f).Additive := by
  dsimp only [targetPullback]
  infer_instance

def transformation := Functor.whiskerRight (PairSectionAlgebraPullback.AffinePairSectionAlgebraPullback.transformation R f)
  (IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.functor R)

def sourceIso : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ)
    ((sourceOpens R f).op ⋙ OrdinarySection.OrdinarySectionComplexAssembly.diagram R X) ≅
      ((sourcePullback R f).mapHomologicalComplex (.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X) :=
  ((sourcePullback R f).mapHomologicalComplex (.up ℕ)).mapIso (OrdinarySection.OrdinarySectionComplexAssembly.iso R X)
def targetIso : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ)
    ((targetOpens R f).op ⋙ OrdinarySection.OrdinarySectionComplexAssembly.diagram R Y) ≅
      ((targetPullback R f).mapHomologicalComplex (.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R Y) :=
  ((targetPullback R f).mapHomologicalComplex (.up ℕ)).mapIso (OrdinarySection.OrdinarySectionComplexAssembly.iso R Y)

def map := (targetIso R f).inv ≫ AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (transformation R f) ≫ (sourceIso R f).hom

theorem component (q : ℕ) (U : (MapPairs.AffineMapPairs.Charts f.left)ᵒᵖ) :
    ((AffinePairOrdinaryForms.map R f).f q).app U = OpenSectionPullback.DeRham.formsPullbackLE f U.unop.val.2.val U.unop.val.1.val U.unop.property q := by
  change 𝟙 _ ≫ OpenSectionPullback.DeRham.formsPullbackLE f U.unop.val.2.val U.unop.val.1.val U.unop.property q ≫ 𝟙 _ = _
  simp only [Category.comp_id, Category.id_comp]

theorem original_pullback (q : ℕ) (U : (MapPairs.AffineMapPairs.Charts f.left)ᵒᵖ) :
    ((AffinePairOrdinaryForms.map R f).f q).app U =
      ((DeRham.Int.presheafPullback f).f q).app (op U.unop.val.2.val) ≫
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X q).map (homOfLE U.unop.property).op :=
  (component R f q U).trans (OpenSectionPullback.DeRham.formsPullbackLE_eq f U.unop.val.2.val U.unop.val.1.val U.unop.property q)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.PairOrdinaryForms.AffinePairOrdinaryForms
