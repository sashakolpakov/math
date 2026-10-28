import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

/-! # Global Sections -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.GlobalSections.CrystallineZariskiGlobalSections

noncomputable section

/-!
# Global sections of the original native Zariski direct image

The right Kan limit isomorphism identifies global sections naturally.
On the original crystalline injective resolution it identifies the
whole section complex, and hence computes native derived global sections.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k)))

local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "Z" => Opens.grothendieckTopology X.left
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.Image.CrystallineZariskiImage.functor p k X

local instance coefficientLimits : HasLimitsOfSize.{u, u} V :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}

def iso : D ⋙ Sheaf.Γ Z V ≅ Sheaf.Γ J V :=
  Functor.isoWhiskerLeft D (Sheaf.ΓNatIsoLim Z V) ≪≫
    (Functor.associator D (sheafToPresheaf Z V) lim).symm ≪≫
      Functor.isoWhiskerRight
        ((ResidualCover.CrystallineResidualCover.functor p k X).sheafPushforwardCocontinuousCompSheafToPresheafIso V J Z) lim ≪≫
          Functor.associator (sheafToPresheaf J V) (ResidualCover.CrystallineResidualCover.functor p k X).op.ran lim ≪≫
            Functor.isoWhiskerLeft (sheafToPresheaf J V)
              (Functor.ranCompLimIso (ResidualCover.CrystallineResidualCover.functor p k X).op) ≪≫
                (Sheaf.ΓNatIsoLim J V).symm

instance nativeSections_additive : (Sheaf.Γ J V).Additive :=
  Functor.additive_of_preserves_binary_products _

instance zariskiSections_additive : (Sheaf.Γ Z V).Additive :=
  Functor.additive_of_preserves_binary_products _

def complexIso (K : CochainComplex (Sheaf (Site.topology p k X)
    (ModuleCat.{u + 1} (Site.CoefficientRing p k))) ℕ) :
    ((Sheaf.Γ Z V).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (((D).mapHomologicalComplex (ComplexShape.up ℕ)).obj K) ≅
        ((Sheaf.Γ J V).mapHomologicalComplex (ComplexShape.up ℕ)).obj K :=
  HomologicalComplex.Hom.isoOfComponents (fun q => (iso p k X).app (K.X q))
    (fun q r _ => ((iso p k X).hom.naturality (K.d q r)).symm)

variable (F : Sheaf (Site.topology p k X)
  (ModuleCat.{u + 1} (Site.CoefficientRing p k))) (I : InjectiveResolution F)

def homologyIso (n : ℕ) :
    (((Sheaf.Γ Z V).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (CechBicomplex.CrystallineZariskiCechBicomplex.imageComplex p k X F I)).homology n ≅
        ((Sheaf.Γ J V).rightDerived n).obj F :=
  (HomologicalComplex.homologyFunctor V (ComplexShape.up ℕ) n).mapIso (complexIso p k X I.cocomplex) ≪≫
    (I.isoRightDerivedObj (Sheaf.Γ J V) n).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.GlobalSections.CrystallineZariskiGlobalSections
