import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModelNaturality
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleSwitchMorphisms
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleEffectiveDescent

/-! # Gluing Morphisms -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.GluingMorphisms

noncomputable section

/-!
# Coaction-compatible module maps preserve the original affine Čech gluing
-/

open _root_.CategoryTheory _root_.ModuleCat TensorProduct
open scoped TensorProduct ChangeOfRings

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModuleModels OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.Switch OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModelNaturality OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleEffectiveDescent

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  {M N : ModuleCat.{u} S} (a : M ⟶ N)

theorem switch_firstModel (σ : ModuleModels.firstPullback R S M ≅ ModuleModels.secondPullback R S M)
    (z : ModuleModels.firstPullback R S M) :
    Switch.gluingSwitch R S M σ (ModuleModels.firstModel R S M z) = ModuleModels.secondModel R S M (σ.hom z) := by
  change ModuleModels.secondModel R S M (σ.hom ((ModuleModels.firstModel R S M).symm (ModuleModels.firstModel R S M z))) = _
  rw [AddEquiv.symm_apply_apply]

/-- The tensor-model compatibility of a map implies compatibility with the exact gluing maps. -/
theorem gluing_compatible_of_switch
    (σ : ModuleModels.firstPullback R S M ≅ ModuleModels.secondPullback R S M)
    (τ : ModuleModels.firstPullback R S N ≅ ModuleModels.secondPullback R S N)
    (h : ∀ z, ModelNaturality.tensorMap R S a (Switch.gluingSwitch R S M σ z) =
      Switch.gluingSwitch R S N τ (ModelNaturality.tensorMap R S a z)) :
    (extendScalars (ModuleModels.firstMap R S)).map a ≫ τ.hom =
      σ.hom ≫ (extendScalars (ModuleModels.secondMap R S)).map a := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply (ModuleModels.secondModel R S N).injective
  change ModuleModels.secondModel R S N (τ.hom ((extendScalars (ModuleModels.firstMap R S)).map a z)) =
    ModuleModels.secondModel R S N ((extendScalars (ModuleModels.secondMap R S)).map a (σ.hom z))
  calc
    _ = Switch.gluingSwitch R S N τ (ModuleModels.firstModel R S N ((extendScalars (ModuleModels.firstMap R S)).map a z)) :=
      (switch_firstModel R S τ _).symm
    _ = Switch.gluingSwitch R S N τ (ModelNaturality.tensorMap R S a (ModuleModels.firstModel R S M z)) :=
      congrArg (Switch.gluingSwitch R S N τ) (ModelNaturality.firstModel_naturality R S a z)
    _ = ModelNaturality.tensorMap R S a (Switch.gluingSwitch R S M σ (ModuleModels.firstModel R S M z)) :=
      (h (ModuleModels.firstModel R S M z)).symm
    _ = ModelNaturality.tensorMap R S a (ModuleModels.secondModel R S M (σ.hom z)) :=
      congrArg (ModelNaturality.tensorMap R S a) (switch_firstModel R S σ z)
    _ = _ := (ModelNaturality.secondModel_naturality R S a (σ.hom z)).symm

/-- Coaction compatibility retains compatibility with the complete original Čech gluing. -/
theorem gluing_compatible_of_coaction (D : CocycleEffectiveDescent.CechCocycle R S M) (E : CocycleEffectiveDescent.CechCocycle R S N)
    (h : ∀ m, ModelNaturality.tensorMap R S a (D.toSwitch.coaction m) = E.toSwitch.coaction (a m)) :
    (extendScalars (ModuleModels.firstMap R S)).map a ≫ E.gluing.hom =
      D.gluing.hom ≫ (extendScalars (ModuleModels.secondMap R S)).map a := by
  apply gluing_compatible_of_switch R S a D.gluing E.gluing
  exact CocycleSwitchMorphisms.switch_compatible D.toSwitch E.toSwitch a.hom h

/-- Compatibility with the original gluing is equivalent to compatibility in the tensor model. -/
theorem switch_compatible_of_gluing
    (σ : ModuleModels.firstPullback R S M ≅ ModuleModels.secondPullback R S M)
    (τ : ModuleModels.firstPullback R S N ≅ ModuleModels.secondPullback R S N)
    (h : (extendScalars (ModuleModels.firstMap R S)).map a ≫ τ.hom =
      σ.hom ≫ (extendScalars (ModuleModels.secondMap R S)).map a)
    (z : S ⊗[R] (restrictScalars (algebraMap R S)).obj M) :
    ModelNaturality.tensorMap R S a (Switch.gluingSwitch R S M σ z) = Switch.gluingSwitch R S N τ (ModelNaturality.tensorMap R S a z) := by
  let x := (ModuleModels.firstModel R S M).symm z
  have hx : ModuleModels.firstModel R S M x = z := (ModuleModels.firstModel R S M).apply_symm_apply z
  have hp : τ.hom ((extendScalars (ModuleModels.firstMap R S)).map a x) =
      (extendScalars (ModuleModels.secondMap R S)).map a (σ.hom x) := ConcreteCategory.congr_hom h x
  calc
    _ = ModelNaturality.tensorMap R S a (Switch.gluingSwitch R S M σ (ModuleModels.firstModel R S M x)) :=
      congrArg (fun t => ModelNaturality.tensorMap R S a (Switch.gluingSwitch R S M σ t)) hx.symm
    _ = ModelNaturality.tensorMap R S a (ModuleModels.secondModel R S M (σ.hom x)) :=
      congrArg (ModelNaturality.tensorMap R S a) (switch_firstModel R S σ x)
    _ = ModuleModels.secondModel R S N ((extendScalars (ModuleModels.secondMap R S)).map a (σ.hom x)) :=
      (ModelNaturality.secondModel_naturality R S a (σ.hom x)).symm
    _ = ModuleModels.secondModel R S N (τ.hom ((extendScalars (ModuleModels.firstMap R S)).map a x)) :=
      congrArg (ModuleModels.secondModel R S N) hp.symm
    _ = Switch.gluingSwitch R S N τ (ModuleModels.firstModel R S N ((extendScalars (ModuleModels.firstMap R S)).map a x)) :=
      (switch_firstModel R S τ _).symm
    _ = Switch.gluingSwitch R S N τ (ModelNaturality.tensorMap R S a (ModuleModels.firstModel R S M x)) :=
      congrArg (Switch.gluingSwitch R S N τ) (ModelNaturality.firstModel_naturality R S a x)
    _ = _ := congrArg (fun t => Switch.gluingSwitch R S N τ (ModelNaturality.tensorMap R S a t)) hx

/-- Morphisms preserve the extracted coaction exactly when they preserve the original gluing. -/
theorem gluing_compatible_iff_coaction (D : CocycleEffectiveDescent.CechCocycle R S M) (E : CocycleEffectiveDescent.CechCocycle R S N) :
    ((extendScalars (ModuleModels.firstMap R S)).map a ≫ E.gluing.hom =
      D.gluing.hom ≫ (extendScalars (ModuleModels.secondMap R S)).map a) ↔
      ∀ m, ModelNaturality.tensorMap R S a (D.toSwitch.coaction m) = E.toSwitch.coaction (a m) := by
  constructor
  · intro h
    exact CocycleSwitchMorphisms.coaction_compatible D.toSwitch E.toSwitch a.hom
      (switch_compatible_of_gluing R S a D.gluing E.gluing h)
  · exact gluing_compatible_of_coaction R S a D E

/-- The original affine Čech compatibility of an actual module morphism. -/
def PreservesGluing (D : CocycleEffectiveDescent.CechCocycle R S M) (E : CocycleEffectiveDescent.CechCocycle R S N) : Prop :=
  (extendScalars (ModuleModels.firstMap R S)).map a ≫ E.gluing.hom =
    D.gluing.hom ≫ (extendScalars (ModuleModels.secondMap R S)).map a

/-- This named geometric condition is exactly coaction compatibility. -/
theorem preservesGluing_iff_coaction (D : CocycleEffectiveDescent.CechCocycle R S M) (E : CocycleEffectiveDescent.CechCocycle R S N) :
    PreservesGluing R S a D E ↔
      ∀ m, ModelNaturality.tensorMap R S a (D.toSwitch.coaction m) = E.toSwitch.coaction (a m) :=
  gluing_compatible_iff_coaction R S a D E

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.GluingMorphisms
