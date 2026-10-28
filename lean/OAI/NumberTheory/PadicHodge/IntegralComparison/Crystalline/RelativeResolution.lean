import OAI.NumberTheory.PadicHodge.IntegralComparison.Divided.CoordinatesModulePoincare
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.DeRham

/-! # Relative Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RelativeResolution

noncomputable section

/-!
# IntegralComparison: a relative divided-coordinate resolution of the original structure sheaf

The proved module-presheaf resolution is transferred through the actual
coefficient universe lift and crystalline sheafification. Its source is
the same structure sheaf used by the original crystalline Ext cohomology.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} (σ : Type u)

def coefficientEquivalence : ModuleCat.{u + 1} B ≌ ModuleCat.{u + 1} (ExactRestriction.Coeff (B := B)) :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv (ULift.ringEquiv : ExactRestriction.Coeff (B := B) ≃+* B)

abbrev coefficientRestriction := (coefficientEquivalence (B := B)).functor

instance coefficientRestriction_leftAdjoint : (coefficientRestriction (B := B)).IsLeftAdjoint :=
  (coefficientEquivalence (B := B)).isLeftAdjoint_functor

instance coefficientRestriction_rightAdjoint : (coefficientRestriction (B := B)).IsRightAdjoint :=
  (coefficientEquivalence (B := B)).symm.isRightAdjoint_inverse

abbrev coefficientFunctor : ModuleCat.{u} B ⥤ ModuleCat.{u + 1} (ExactRestriction.Coeff (B := B)) :=
  ModuleCat.uliftFunctor.{u + 1, u} B ⋙ coefficientRestriction

def coefficientPresheaves :
    ((BigCrystallineSite.Object p B J δ f)ᵒᵖ ⥤ ModuleCat.{u} B) ⥤
      ((BigCrystallineSite.Object p B J δ f)ᵒᵖ ⥤ ModuleCat.{u + 1} (ExactRestriction.Coeff (B := B))) :=
  (Functor.whiskeringRight _ _ _).obj (coefficientFunctor (B := B))

local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RelativeResolution.coefficientPresheaves (p := p) (B := B) (J := J) (δ := δ) (f := f)
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.DeRham.sheafificationFunctor (p := p) (J := J) (δ := δ) f
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.modulePresheaf (p := p) (J := J) (δ := δ) f
local notation "O" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) f

instance coefficientPresheaves_preservesFiniteLimits : PreservesFiniteLimits L where
  preservesFiniteLimits T _ _ := by
    dsimp [coefficientPresheaves]
    infer_instance

instance coefficientPresheaves_preservesFiniteColimits : PreservesFiniteColimits L where
  preservesFiniteColimits T _ _ := by
    dsimp [coefficientPresheaves]
    infer_instance

instance sheafification_additive : (F).Additive := by
  dsimp [DeRham.sheafificationFunctor]
  infer_instance

instance sheafification_preservesHomology : (F).PreservesHomology := by
  change (L ⋙ presheafToSheaf BigCrystallineSite.Object.topology (ModuleCat.{u + 1} (ExactRestriction.Coeff (B := B)))).PreservesHomology
  infer_instance

def complex : CochainComplex (ExactRestriction.ModuleSheaf (p := p) (J := J) (δ := δ) f) ℕ :=
  ((F).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (Divided.CoordinatesModuleComplex.complex σ)

def sourceIso :
    ((F).mapHomologicalComplex (ComplexShape.up ℕ)).obj ((CochainComplex.single₀ _).obj A) ≅
      (CochainComplex.single₀ _).obj O :=
  (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℕ) 0).app A

/-- This augmentation starts at the original crystalline structure sheaf. -/
def augmentation : (CochainComplex.single₀ _).obj O ⟶ complex σ :=
  (sourceIso).inv ≫ ((F).mapHomologicalComplex (ComplexShape.up ℕ)).map
    (Divided.CoordinatesModuleComplex.augmentation σ)

/-- Exactness of the canonical relative resolution in the actual crystalline sheaf category. -/
instance augmentation_quasiIso [Fintype σ] :
    QuasiIso (augmentation (p := p) (B := B) (J := J) (δ := δ) (f := f) σ) := by
  have : QuasiIso (Divided.CoordinatesModuleComplex.augmentation
      (p := p) (B := B) (J := J) (δ := δ) (f := f) σ) :=
    Divided.CoordinatesModulePoincare.augmentation_quasiIso σ
  exact inferInstanceAs (QuasiIso ((sourceIso).inv ≫
    ((F).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (Divided.CoordinatesModuleComplex.augmentation σ)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RelativeResolution
