import OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.SheafResolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.DerivedSections
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ProperAffineCharts

/-! # Cech -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.Cech.CrystallineZariskiCech

noncomputable section

/-!
# Čech descent for the actual native crystalline direct image

The canonical augmentation resolves its Zariski direct image as sheaves
of the original lifted Witt modules. Properness supplies a finite family
of actual affine open charts to which this resolution applies.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) {ι : Type u} (U : ι → X.left.Opens)
  (F : Sheaf (Site.topology p k X) (ModuleCat.{u + 1} (Site.CoefficientRing p k)))

def complex :
    CochainComplex (Sheaf (Opens.grothendieckTopology X.left)
      (ModuleCat.{u + 1} (Site.CoefficientRing p k))) ℕ :=
  MixedCech.Presheaf.MixedCechPresheaf.sheafComplex (Site.CoefficientRing p k) X.left U
    ((Image.CrystallineZariskiImage.functor p k X).obj F).obj

def augmentation :
    (CochainComplex.single₀ (Sheaf (Opens.grothendieckTopology X.left)
      (ModuleCat.{u + 1} (Site.CoefficientRing p k)))).obj
        ((Image.CrystallineZariskiImage.functor p k X).obj F) ⟶ complex p k X U F :=
  MixedCech.SheafResolution.MixedCechSheafResolution.augmentation (Site.CoefficientRing p k) X.left U
    ((Image.CrystallineZariskiImage.functor p k X).obj F)

theorem augmentation_quasiIso (hU : iSup U = ⊤) : QuasiIso (augmentation p k X U F) :=
  MixedCech.SheafResolution.MixedCechSheafResolution.quasiIso (Site.CoefficientRing p k) X.left U
    ((Image.CrystallineZariskiImage.functor p k X).obj F) hU

variable [IsProper X.hom]

def properComplex := complex p k X
  (fun i : ProperAffineCharts.CrystallineProperAffineCharts.Index k X =>
    (ProperAffineCharts.CrystallineProperAffineCharts.inclusion k X i).left.opensRange) F

theorem proper_augmentation_quasiIso :
    QuasiIso (augmentation p k X
      (fun i : ProperAffineCharts.CrystallineProperAffineCharts.Index k X =>
        (ProperAffineCharts.CrystallineProperAffineCharts.inclusion k X i).left.opensRange) F) :=
  augmentation_quasiIso p k X _ F (ProperAffineCharts.CrystallineProperAffineCharts.covering k X)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.Cech.CrystallineZariskiCech
