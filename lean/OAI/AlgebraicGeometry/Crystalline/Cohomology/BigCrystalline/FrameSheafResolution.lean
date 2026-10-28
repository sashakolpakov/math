import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameResolution
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # Frame Sheaf Resolution -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution

noncomputable section

/-! # The original big crystalline structure sheaf has a polynomial frame resolution

Exact coefficient lifting and sheafification carry the integral frame
contraction to an actual augmented sheaf resolution on the big site.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts

variable (p : ℕ) (W A : Type u) [CommRing W] [CommRing A]
  (I : Ideal W) (δ : DividedPowers I) (base : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of W))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W A I δ base
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.Object.topology (p := p) (B := W)
  (J := I) (δ := δ) (f := base)
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.modulePresheaf
  (p := p) (J := I) (δ := δ) base
local notation "O" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.structureSheaf
  (p := p) (J := I) (δ := δ) base

abbrev Presheaves := Cᵒᵖ ⥤ ModuleCat.{u} W
abbrev Sheaves := Sheaf T (ModuleCat.{u + 1} R)

local notation "P" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.Presheaves p W A I δ base
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.Sheaves p W A I δ base

def coefficientLift : ModuleCat.{u} W ⥤ ModuleCat.{u + 1} R :=
  ModuleCat.uliftFunctor.{u + 1} W ⋙
    ModuleCat.restrictScalars (ULift.ringEquiv : R ≃+* W).toRingHom

instance coefficientLift_additive : (coefficientLift W).Additive := by
  unfold coefficientLift
  infer_instance

instance coefficientLift_preservesFiniteLimits : PreservesFiniteLimits (coefficientLift W) := by
  unfold coefficientLift
  exact comp_preservesFiniteLimits _ _

instance coefficientLift_preservesFiniteColimits : PreservesFiniteColimits (coefficientLift W) := by
  unfold coefficientLift
  exact comp_preservesFiniteColimits _ _

def toSheaf : P ⥤ V :=
  (Functor.whiskeringRight Cᵒᵖ (ModuleCat.{u} W) (ModuleCat.{u + 1} R)).obj (coefficientLift W) ⋙
    presheafToSheaf T (ModuleCat.{u + 1} R)

instance toSheaf_additive : (toSheaf p W A I δ base).Additive := by
  unfold toSheaf
  infer_instance

instance toSheaf_preservesFiniteLimits : PreservesFiniteLimits (toSheaf p W A I δ base) := by
  unfold toSheaf
  have : PreservesFiniteLimits
      ((Functor.whiskeringRight Cᵒᵖ (ModuleCat.{u} W) (ModuleCat.{u + 1} R)).obj (coefficientLift W)) :=
    ⟨fun _ _ _ => by infer_instance⟩
  exact comp_preservesFiniteLimits _ _

instance toSheaf_preservesFiniteColimits : PreservesFiniteColimits (toSheaf p W A I δ base) := by
  unfold toSheaf
  have : PreservesFiniteColimits
      ((Functor.whiskeringRight Cᵒᵖ (ModuleCat.{u} W) (ModuleCat.{u + 1} R)).obj (coefficientLift W)) :=
    ⟨fun _ _ _ => by infer_instance⟩
  exact comp_preservesFiniteColimits _ _

def coefficientIso : (toSheaf p W A I δ base).obj (G) ≅ O :=
  Iso.refl _

variable {σ : Type u} (a : σ → A) [Fintype σ]

def complex : CochainComplex V ℕ :=
  ((toSheaf p W A I δ base).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := I) (δ := δ) (base := base) a)

/-- The augmentation starts at the original big crystalline structure sheaf. -/
def augmentation : (CochainComplex.single₀ V).obj (O) ⟶
    complex p W A I δ base a :=
  (CochainComplex.single₀ V).map (coefficientIso p W A I δ base).inv ≫
    (HomologicalComplex.singleMapHomologicalComplex (toSheaf p W A I δ base) (ComplexShape.up ℕ) 0).inv.app
      (G) ≫
    ((toSheaf p W A I δ base).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (FrameResolution.BigCrystallineFrameResolution.augmentation (p := p) (J := I) (δ := δ) (base := base) a)

instance augmentation_quasiIso : QuasiIso (augmentation p W A I δ base a) := by
  have hmap : QuasiIso (((toSheaf p W A I δ base).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (FrameResolution.BigCrystallineFrameResolution.augmentation (p := p) (J := I) (δ := δ) (base := base) a)) := by infer_instance
  have hinner : QuasiIso
      ((HomologicalComplex.singleMapHomologicalComplex (toSheaf p W A I δ base) (ComplexShape.up ℕ) 0).inv.app
        (G) ≫
        ((toSheaf p W A I δ base).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (FrameResolution.BigCrystallineFrameResolution.augmentation (p := p) (J := I) (δ := δ) (base := base) a)) := quasiIso_comp
    ((HomologicalComplex.singleMapHomologicalComplex (toSheaf p W A I δ base) (ComplexShape.up ℕ) 0).inv.app
      (G))
    (((toSheaf p W A I δ base).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (FrameResolution.BigCrystallineFrameResolution.augmentation (p := p) (J := I) (δ := δ) (base := base) a))
  exact quasiIso_comp ((CochainComplex.single₀ V).map (coefficientIso p W A I δ base).inv) _ (hφ' := hinner)

def degreeZeroHomologyIso : (complex p W A I δ base a).homology 0 ≅ O := by
  letI : QuasiIsoAt (augmentation p W A I δ base a) 0 := (augmentation_quasiIso p W A I δ base a).quasiIsoAt 0
  exact (isoOfQuasiIsoAt (augmentation p W A I δ base a) 0).symm ≪≫
    HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0 (O)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution
