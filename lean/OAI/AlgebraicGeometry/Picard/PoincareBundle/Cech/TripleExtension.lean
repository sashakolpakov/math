import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModelLinearity

/-! # Triple Extension -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.TripleExtension

noncomputable section

/-!
# Extending actual affine gluing to three tensor factors
-/

open _root_.CategoryTheory _root_.ModuleCat TensorProduct
open scoped TensorProduct ChangeOfRings

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModuleModels OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.Switch OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModelLinearity
open OAI.AlgebraicGeometry.Picard.PoincareBundle.ModuleBaseChangeFunctor

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (M : ModuleCat.{u} S)

local notation "U" => S ⊗[R] S

/-- The common three-factor tensor model, as a module over its leading coefficient ring. -/
abbrev tripleModule : ModuleCat.{u} S :=
  of S (S ⊗[R] (S ⊗[R] (restrictScalars (algebraMap R S)).obj M))

/-- Extend the first Čech tensor model by an additional coefficient factor. -/
def firstPreModel : (ModuleBaseChangeFunctor.sourceFunctor R U S).obj (ModuleModels.firstPullback R S M) ≅ tripleModule R S M :=
  ModuleBaseChangeFunctor.sourceModelIso R U S (ModuleModels.firstPullback R S M) ≪≫
    (AlgebraTensorModule.congr (LinearEquiv.refl S S) (ModelLinearity.firstLinearModel R S M)).toModuleIso

/-- Extend the second Čech tensor model by an additional coefficient factor. -/
def secondPreModel : (ModuleBaseChangeFunctor.sourceFunctor R U S).obj (ModuleModels.secondPullback R S M) ≅ tripleModule R S M :=
  ModuleBaseChangeFunctor.sourceModelIso R U S (ModuleModels.secondPullback R S M) ≪≫
    (AlgebraTensorModule.congr (LinearEquiv.refl S S) (ModelLinearity.secondLinearModel R S M)).toModuleIso

/-- The actual extension of the first pullback to the three-factor coordinate ring. -/
def firstTripleModel : (ModuleBaseChangeFunctor.targetFunctor R U S).obj (ModuleModels.firstPullback R S M) ≅ tripleModule R S M :=
  (ModuleBaseChangeFunctor.objectIso R U S (ModuleModels.firstPullback R S M)).symm ≪≫ firstPreModel R S M

/-- The actual extension of the second pullback to the three-factor coordinate ring. -/
def secondTripleModel : (ModuleBaseChangeFunctor.targetFunctor R U S).obj (ModuleModels.secondPullback R S M) ≅ tripleModule R S M :=
  (ModuleBaseChangeFunctor.objectIso R U S (ModuleModels.secondPullback R S M)).symm ≪≫ secondPreModel R S M

/-- The switch on the last two factors is linear over the leading coefficient ring. -/
def tripleSwitch (σ : ModuleModels.firstPullback R S M ≅ ModuleModels.secondPullback R S M) :
    tripleModule R S M ⟶ tripleModule R S M :=
  ofHom ((Switch.gluingSwitch R S M σ).toLinearMap.baseChange S)

/-- Extension followed by the two tensor models carries gluing to the last-factor switch. -/
theorem preModel_naturality (σ : ModuleModels.firstPullback R S M ≅ ModuleModels.secondPullback R S M) :
    (firstPreModel R S M).hom ≫ tripleSwitch R S M σ =
      (ModuleBaseChangeFunctor.sourceFunctor R U S).map σ.hom ≫ (secondPreModel R S M).hom := by
  apply ModuleCat.ExtendScalars.hom_ext (f := algebraMap R S)
  intro p
  change (1 : S) ⊗ₜ[R] (Switch.gluingSwitch R S M σ (ModelLinearity.firstLinearModel R S M p)) =
    (1 : S) ⊗ₜ[R] (ModelLinearity.secondLinearModel R S M (σ.hom p))
  change (1 : S) ⊗ₜ[R] (ModuleModels.secondModel R S M (σ.hom
    ((ModuleModels.firstModel R S M).symm (ModuleModels.firstModel R S M p)))) = _
  erw [AddEquiv.symm_apply_apply]
  rfl

/-- Actual scalar extension of the gluing map becomes the three-factor switch. -/
theorem tripleModel_naturality (σ : ModuleModels.firstPullback R S M ≅ ModuleModels.secondPullback R S M) :
    (ModuleBaseChangeFunctor.targetFunctor R U S).map σ.hom ≫ (secondTripleModel R S M).hom =
      (firstTripleModel R S M).hom ≫ tripleSwitch R S M σ := by
  apply (cancel_epi (ModuleBaseChangeFunctor.objectIso R U S (ModuleModels.firstPullback R S M)).hom).mp
  change (ModuleBaseChangeFunctor.objectIso R U S (ModuleModels.firstPullback R S M)).hom ≫
      ((ModuleBaseChangeFunctor.targetFunctor R U S).map σ.hom ≫
        ((ModuleBaseChangeFunctor.objectIso R U S (ModuleModels.secondPullback R S M)).inv ≫ (secondPreModel R S M).hom)) =
    (ModuleBaseChangeFunctor.objectIso R U S (ModuleModels.firstPullback R S M)).hom ≫
      (((ModuleBaseChangeFunctor.objectIso R U S (ModuleModels.firstPullback R S M)).inv ≫ (firstPreModel R S M).hom) ≫
        tripleSwitch R S M σ)
  rw [← Category.assoc, ← ModuleBaseChangeFunctor.objectIso_naturality]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact (preModel_naturality R S M σ).symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.TripleExtension
