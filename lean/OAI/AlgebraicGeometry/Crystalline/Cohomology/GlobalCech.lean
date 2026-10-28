import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.CechSections
import OAI.AlgebraicGeometry.Crystalline.Cohomology.GlobalExtSections
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.RationalComparison

/-! # Global Cech -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.GlobalCech.CrystallineGlobalCechCohomology

noncomputable section

/-!
# The original integral and rational crystalline groups from global Čech cochains

The native total section complex is lifted only to the universe of the
specified Ext groups. Its comparison is built from the canonical Čech
augmentation and the original Zariski global-sections isomorphism.
Flat Witt fraction-field extension gives the rational computation.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]

def liftCoefficients : ModuleCat.{u + 1} (Site.CoefficientRing p k) ⥤
    ModuleCat.{u + 2} (Site.CoefficientRing p k) :=
  ModuleCat.uliftFunctor.{u + 2, u + 1} (Site.CoefficientRing p k)

instance lift_additive : (liftCoefficients p k).Additive := by
  unfold liftCoefficients
  infer_instance

instance lift_preservesHomology : (liftCoefficients p k).PreservesHomology := by
  unfold liftCoefficients
  infer_instance

variable (X : Over (Spec (CommRingCat.of k))) {ι : Type u} [Finite ι] (U : ι → X.left.Opens)
  (I : InjectiveResolution (Site.structureSheaf p k X))

def integralComplex : CochainComplex (ModuleCat.{u + 2} (Site.CoefficientRing p k)) ℕ :=
  ((liftCoefficients p k).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (CrystallineZariski.CechSections.CrystallineZariskiCechSections.sectionTotal p k X U (Site.structureSheaf p k X) I)

def comparison : GlobalExtSections.CrystallineGlobalExtSections.complex p k X (Site.structureSheaf p k X) I ⟶
    integralComplex p k X U I :=
  (((liftCoefficients p k).mapHomologicalComplex (ComplexShape.up ℕ)).mapIso
    (CrystallineZariski.GlobalSections.CrystallineZariskiGlobalSections.complexIso p k X I.cocomplex).symm).hom ≫
      ((liftCoefficients p k).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (CrystallineZariski.CechSections.CrystallineZariskiCechSections.comparison p k X U (Site.structureSheaf p k X) I)

theorem comparison_quasiIso (hU : iSup U = ⊤) : QuasiIso (comparison p k X U I) := by
  have : QuasiIso (CrystallineZariski.CechSections.CrystallineZariskiCechSections.comparison p k X U
      (Site.structureSheaf p k X) I) :=
    CrystallineZariski.CechSections.CrystallineZariskiCechSections.comparison_quasiIso p k X U (Site.structureSheaf p k X) I hU
  have hm : QuasiIso (((liftCoefficients p k).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (CrystallineZariski.CechSections.CrystallineZariskiCechSections.comparison p k X U (Site.structureSheaf p k X) I)) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology
      (CrystallineZariski.CechSections.CrystallineZariskiCechSections.comparison p k X U (Site.structureSheaf p k X) I)
      (liftCoefficients p k)
  let e := ((liftCoefficients p k).mapHomologicalComplex (ComplexShape.up ℕ)).mapIso
    (CrystallineZariski.GlobalSections.CrystallineZariskiGlobalSections.complexIso p k X I.cocomplex).symm
  have : QuasiIso e.hom := inferInstance
  exact quasiIso_comp e.hom
    (((liftCoefficients p k).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (CrystallineZariski.CechSections.CrystallineZariskiCechSections.comparison p k X U (Site.structureSheaf p k X) I)) (hφ' := hm)

def integralHomologyIso (hU : iSup U = ⊤) (n : ℕ) :
    (integralComplex p k X U I).homology n ≅
      ModuleCat.of (Site.CoefficientRing p k) (Site.integralCohomology p k X n) := by
  have : QuasiIso (comparison p k X U I) := comparison_quasiIso p k X U I hU
  exact (isoOfQuasiIsoAt (comparison p k X U I) n).symm ≪≫
    GlobalExtSections.CrystallineGlobalExtSections.homologyIso p k X I n

variable [PerfectRing k p]

def rationalComplex : CochainComplex (ModuleCat.{u + 2} (FractionRing (WittVector p k))) ℕ :=
  ((Affine.RationalComparison.AffineRationalCrystallineComparison.coefficients p k).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (integralComplex p k X U I)

def rationalHomologyIso (hU : iSup U = ⊤) (n : ℕ) :
    (rationalComplex p k X U I).homology n ≅ Site.rationalCohomology p k X n :=
  Cech.SheafExactness.CechSheafExactness.mapHomologyIso (Affine.RationalComparison.AffineRationalCrystallineComparison.coefficients p k)
    (integralComplex p k X U I) n ≪≫
      (Affine.RationalComparison.AffineRationalCrystallineComparison.coefficients p k).mapIso
        (integralHomologyIso p k X U I hU n)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.GlobalCech.CrystallineGlobalCechCohomology
