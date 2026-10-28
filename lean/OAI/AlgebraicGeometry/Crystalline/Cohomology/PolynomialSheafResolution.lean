import OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialResolution
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # Polynomial Sheaf Resolution -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialSheafResolution.CrystallinePolynomialSheafResolution

noncomputable section

/-!
# A polynomial coordinate resolution of the native crystalline structure sheaf

The coefficient-universe lift and sheafification are exact. Applying them
to the proved presheaf augmentation gives a quasi-isomorphic resolution
of Cohomology's actual crystalline structure sheaf, in every cohomological degree.
-/

open _root_.CategoryTheory Limits

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (AlgebraicGeometry.Spec (CommRingCat.of k))) (σ : Type u) [Fintype σ]

local notation "W" => WittVector p k
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.Object p k X
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
abbrev Presheaves := Cᵒᵖ ⥤ ModuleCat.{u} W
abbrev Sheaves := Sheaf J (ModuleCat.{u + 1} R)

local notation "P" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialSheafResolution.CrystallinePolynomialSheafResolution.Presheaves p k X
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialSheafResolution.CrystallinePolynomialSheafResolution.Sheaves p k X

def coefficientLift : ModuleCat.{u} W ⥤ ModuleCat.{u + 1} R :=
  ModuleCat.uliftFunctor.{u + 1} W ⋙
    ModuleCat.restrictScalars (ULift.ringEquiv : R ≃+* W).toRingHom

instance coefficientLift_additive : (coefficientLift p k).Additive := by
  unfold coefficientLift
  infer_instance

instance coefficientLift_preservesFiniteLimits : PreservesFiniteLimits (coefficientLift p k) := by
  unfold coefficientLift
  exact comp_preservesFiniteLimits _ _

instance coefficientLift_preservesFiniteColimits : PreservesFiniteColimits (coefficientLift p k) := by
  unfold coefficientLift
  exact comp_preservesFiniteColimits _ _

def toSheaf : P ⥤ V :=
  (Functor.whiskeringRight Cᵒᵖ (ModuleCat.{u} W) (ModuleCat.{u + 1} R)).obj (coefficientLift p k) ⋙
    presheafToSheaf J (ModuleCat.{u + 1} R)

instance toSheaf_additive : (toSheaf p k X).Additive := by
  unfold toSheaf
  infer_instance

instance toSheaf_preservesFiniteLimits : PreservesFiniteLimits (toSheaf p k X) := by
  unfold toSheaf
  have : PreservesFiniteLimits
      ((Functor.whiskeringRight Cᵒᵖ (ModuleCat.{u} W) (ModuleCat.{u + 1} R)).obj (coefficientLift p k)) :=
    ⟨fun _ _ _ => by infer_instance⟩
  exact comp_preservesFiniteLimits _ _

instance toSheaf_preservesFiniteColimits : PreservesFiniteColimits (toSheaf p k X) := by
  unfold toSheaf
  have : PreservesFiniteColimits
      ((Functor.whiskeringRight Cᵒᵖ (ModuleCat.{u} W) (ModuleCat.{u + 1} R)).obj (coefficientLift p k)) :=
    ⟨fun _ _ _ => by infer_instance⟩
  exact comp_preservesFiniteColimits _ _

def coefficientIso : (toSheaf p k X).obj (Site.functions p k X) ≅ Site.structureSheaf p k X :=
  Iso.refl _

def complex : CochainComplex V ℕ :=
  ((toSheaf p k X).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (PolynomialResolution.CrystallinePolynomialResolution.complex p k X σ)

/-- The augmentation starts at the native Cohomology structure sheaf. -/
def augmentation : (CochainComplex.single₀ V).obj (Site.structureSheaf p k X) ⟶
    complex p k X σ :=
  (CochainComplex.single₀ V).map (coefficientIso p k X).inv ≫
    (HomologicalComplex.singleMapHomologicalComplex (toSheaf p k X) (ComplexShape.up ℕ) 0).inv.app
      (Site.functions p k X) ≫
    ((toSheaf p k X).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (PolynomialResolution.CrystallinePolynomialResolution.augmentation p k X σ)

instance augmentation_quasiIso : QuasiIso (augmentation p k X σ) := by
  have hmap : QuasiIso (((toSheaf p k X).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (PolynomialResolution.CrystallinePolynomialResolution.augmentation p k X σ)) := by infer_instance
  have hinner : QuasiIso
      ((HomologicalComplex.singleMapHomologicalComplex (toSheaf p k X) (ComplexShape.up ℕ) 0).inv.app
        (Site.functions p k X) ≫
        ((toSheaf p k X).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (PolynomialResolution.CrystallinePolynomialResolution.augmentation p k X σ)) := quasiIso_comp
    ((HomologicalComplex.singleMapHomologicalComplex (toSheaf p k X) (ComplexShape.up ℕ) 0).inv.app
      (Site.functions p k X))
    (((toSheaf p k X).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (PolynomialResolution.CrystallinePolynomialResolution.augmentation p k X σ))
  exact quasiIso_comp ((CochainComplex.single₀ V).map (coefficientIso p k X).inv) _ (hφ' := hinner)

def degreeZeroHomologyIso : (complex p k X σ).homology 0 ≅ Site.structureSheaf p k X := by
  letI : QuasiIsoAt (augmentation p k X σ) 0 := (augmentation_quasiIso p k X σ).quasiIsoAt 0
  exact (isoOfQuasiIsoAt (augmentation p k X σ) 0).symm ≪≫
    HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0 (Site.structureSheaf p k X)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialSheafResolution.CrystallinePolynomialSheafResolution
