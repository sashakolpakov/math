import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.Cech
import OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.Functor

/-! # Cech Bicomplex -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.CechBicomplex.CrystallineZariskiCechBicomplex

noncomputable section

/-!
# Čech descent in every degree of a native injective resolution

The original crystalline injective resolution maps to an actual
Zariski sheaf complex. Its functorial Čech resolution is a double
complex with canonical row augmentations, all quasi-isomorphisms.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k)))

instance directImage_additive : (Image.CrystallineZariskiImage.functor p k X).Additive := by
  have : ((ResidualCover.CrystallineResidualCover.functor p k X).op.ran :
      ((Site.Object p k X)ᵒᵖ ⥤ ModuleCat.{u + 1} (Site.CoefficientRing p k)) ⥤
        (X.left.Opensᵒᵖ ⥤ ModuleCat.{u + 1} (Site.CoefficientRing p k))).IsRightAdjoint :=
    ((ResidualCover.CrystallineResidualCover.functor p k X).op.ranAdjunction
      (ModuleCat.{u + 1} (Site.CoefficientRing p k))).isRightAdjoint
  have : ((ResidualCover.CrystallineResidualCover.functor p k X).op.ran :
      ((Site.Object p k X)ᵒᵖ ⥤ ModuleCat.{u + 1} (Site.CoefficientRing p k)) ⥤
        (X.left.Opensᵒᵖ ⥤ ModuleCat.{u + 1} (Site.CoefficientRing p k))).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (Image.CrystallineZariskiImage.functor p k X ⋙
      sheafToPresheaf (Opens.grothendieckTopology X.left)
        (ModuleCat.{u + 1} (Site.CoefficientRing p k))).Additive :=
    Functor.additive_of_iso
      ((ResidualCover.CrystallineResidualCover.functor p k X).sheafPushforwardCocontinuousCompSheafToPresheafIso
        (ModuleCat.{u + 1} (Site.CoefficientRing p k)) (Site.topology p k X)
        (Opens.grothendieckTopology X.left)).symm
  exact Functor.additive_of_comp_faithful (Image.CrystallineZariskiImage.functor p k X)
    (sheafToPresheaf (Opens.grothendieckTopology X.left)
      (ModuleCat.{u + 1} (Site.CoefficientRing p k)))

variable {ι : Type u} (U : ι → X.left.Opens)
  (F : Sheaf (Site.topology p k X) (ModuleCat.{u + 1} (Site.CoefficientRing p k)))
  (I : InjectiveResolution F)

def imageComplex : CochainComplex (Sheaf (Opens.grothendieckTopology X.left)
    (ModuleCat.{u + 1} (Site.CoefficientRing p k))) ℕ :=
  ((Image.CrystallineZariskiImage.functor p k X).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    I.cocomplex

def bicomplex : HomologicalComplex₂ (Sheaf (Opens.grothendieckTopology X.left)
    (ModuleCat.{u + 1} (Site.CoefficientRing p k))) (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  ((MixedCech.Functor.MixedCechFunctor.sheafFunctor (Site.CoefficientRing p k) X.left U).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (imageComplex p k X F I)

def singleBicomplex : HomologicalComplex₂ (Sheaf (Opens.grothendieckTopology X.left)
    (ModuleCat.{u + 1} (Site.CoefficientRing p k))) (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  ((CochainComplex.single₀ _).mapHomologicalComplex (ComplexShape.up ℕ)).obj (imageComplex p k X F I)

def augmentation : singleBicomplex p k X F I ⟶ bicomplex p k X U F I :=
  ((MixedCech.Functor.MixedCechFunctor.sheafAugmentation (Site.CoefficientRing p k) X.left U).mapHomologicalComplex
    (ComplexShape.up ℕ)).app (imageComplex p k X F I)

theorem row_quasiIso (hU : iSup U = ⊤) (q : ℕ) : QuasiIso ((augmentation p k X U F I).f q) :=
  MixedCech.Functor.MixedCechFunctor.sheafAugmentation_quasiIso (Site.CoefficientRing p k) X.left U hU
    ((Image.CrystallineZariskiImage.functor p k X).obj (I.cocomplex.X q))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.CechBicomplex.CrystallineZariskiCechBicomplex
