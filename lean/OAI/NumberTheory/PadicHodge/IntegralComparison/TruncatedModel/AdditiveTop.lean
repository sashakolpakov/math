import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ModelSheafComparison
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.TopSingle
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.AdditiveCechConcentration

/-! # Additive Top -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AdditiveTop.Comparison

noncomputable section

/-! The actual native sheaf comparison on top forms, after forgetting
scalars. Its source is the original single coefficient sheaf with the
same two universe lifts as the crystalline coefficient functor. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev lift : AddCommGrpCat.{0} ⥤ AddCommGrpCat.{2} :=
  AddCommGrpCat.uliftFunctor.{1,0} ⋙ AddCommGrpCat.uliftFunctor.{2,1}

instance lift_additive : lift.Additive := by infer_instance
instance lift_preservesLimits : PreservesLimitsOfSize.{0,0} lift := by infer_instance
instance lift_preservesHomology : lift.PreservesHomology := by infer_instance

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

abbrev forget : ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) ⥤
    AddCommGrpCat.{2} := forget₂ _ _

def coefficientIso :
    forget₂ (ModuleCat (Truncated.Witt.Ring p k n)) AddCommGrpCat ⋙ lift ≅
      OrdinarySectionMap.Ordinary.coefficients p k n ⋙ forget p k := Iso.refl _

abbrev underlying :
    Sheaf (Opens.grothendieckTopology X.left)
      (ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ⥤
    X.left.Opensᵒᵖ ⥤ AddCommGrpCat.{2} :=
  sheafToPresheaf (Opens.grothendieckTopology X.left) _ ⋙
    (Functor.whiskeringRight X.left.Opensᵒᵖ _ _).obj (forget p k)

abbrev target := ((underlying p k n X).mapHomologicalComplex (.up ℕ)).obj
  (ModelSheafComparison.target p k n X Y f I)

abbrev source := ((underlying p k n X).mapHomologicalComplex (.up ℕ)).obj
  (ModelSheafComparison.source p k n X)

def deRhamMap : source p k n X ⟶ target p k n X Y f I :=
  ((underlying p k n X).mapHomologicalComplex (.up ℕ)).map
    (ModelSheafComparison.map p k n X Y f hp I)

variable (g : ℕ) [SmoothOfRelativeDimension g X.hom]

abbrev originalTop := Relative.AdditiveCechConcentration.coefficients
  ((single X.left.Modules (.up ℕ) g).obj
    (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (Truncated.Witt.Ring p k n) X g))

def sheafTopMap :
    ((AlgebraSheafScalars.functor (Truncated.Witt.Ring p k n) X).mapHomologicalComplex
      (.up ℕ)).obj ((single X.left.Modules (.up ℕ) g).obj
        (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (Truncated.Witt.Ring p k n) X g)) ⟶
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex (Truncated.Witt.Ring p k n) X :=
  (singleMapHomologicalComplex
    (AlgebraSheafScalars.functor (Truncated.Witt.Ring p k n) X) (.up ℕ) g).hom.app
      (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (Truncated.Witt.Ring p k n) X g) ≫
    IntrinsicDeRham.TopSingle.Intrinsic.sheafMap (Truncated.Witt.Ring p k n) X g

def topUnit : AugmentedCech.CoefficientTotal.mapped lift (originalTop p k n X g) ⟶
    source p k n X :=
  ((underlying p k n X).mapHomologicalComplex (.up ℕ)).map
    (((ModelSheafComparison.sourceFunctor p k n X).mapHomologicalComplex
      (.up ℕ)).map (sheafTopMap p k n X g))

def map : AugmentedCech.CoefficientTotal.mapped lift (originalTop p k n X g) ⟶
    target p k n X Y f I :=
  topUnit p k n X g ≫ deRhamMap p k n X Y f hp I

theorem factorization : Comparison.map p k n X Y f hp I g =
    topUnit p k n X g ≫ deRhamMap p k n X Y f hp I := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AdditiveTop.Comparison
