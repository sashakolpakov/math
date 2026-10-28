import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModelUnits
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.CoalgebraMorphisms

/-! # Unit Coaction -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.UnitCoaction

noncomputable section

/-!
# Unit values of the coaction extracted from Čech gluing
-/

open _root_.CategoryTheory _root_.ModuleCat TensorProduct
open scoped TensorProduct ChangeOfRings

universe u

section

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.ExtensionUnits OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModuleModels OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModelUnits OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleEffectiveDescent

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- A gluing unit gives the usual coaction unit, in the exact affine tensor model. -/
theorem coaction_unit_of_gluing {X : ModuleCat.{u} S} (D : CocycleEffectiveDescent.CechCocycle R S X) (x : X)
    (h : D.gluing.hom (Scalar.ExtensionUnits.unit (ModuleModels.firstMap R S) X x) = Scalar.ExtensionUnits.unit (ModuleModels.secondMap R S) X x) :
    D.toSwitch.coaction x =
      (1 : S) ⊗ₜ[R] (show (restrictScalars (algebraMap R S)).obj X from x) := by
  change ModuleModels.secondModel R S X (D.gluing.hom ((ModuleModels.firstModel R S X).symm
    ((1 : S) ⊗ₜ[R] (show (restrictScalars (algebraMap R S)).obj X from x)))) = _
  exact (congrArg (fun z => ModuleModels.secondModel R S X (D.gluing.hom z))
    (ModelUnits.firstModel_symm_unit R S X x)).trans
      ((congrArg (ModuleModels.secondModel R S X) h).trans (ModelUnits.secondModel_unit R S X x))

/-- A Čech coaction fixes the unit copy of the original base module. -/
def HasUnitCoaction (M : ModuleCat.{u} R)
    (D : CocycleEffectiveDescent.CechCocycle R S ((extendScalars (algebraMap R S)).obj M)) : Prop :=
  ∀ m, D.toSwitch.coaction (Scalar.ExtensionUnits.unit (algebraMap R S) M m) =
    (1 : S) ⊗ₜ[R]
      (show (restrictScalars (algebraMap R S)).obj ((extendScalars (algebraMap R S)).obj M)
        from Scalar.ExtensionUnits.unit (algebraMap R S) M m)

/-- Preservation of the original module under gluing implies the canonical coaction units. -/
theorem hasUnitCoaction_of_gluingUnits (M : ModuleCat.{u} R)
    (D : CocycleEffectiveDescent.CechCocycle R S ((extendScalars (algebraMap R S)).obj M))
    (h : Scalar.ExtensionUnits.PreservesUnits (algebraMap R S) (ModuleModels.firstMap R S) (ModuleModels.secondMap R S) M D.gluing.hom) :
    HasUnitCoaction R S M D :=
  fun m => coaction_unit_of_gluing R S D (Scalar.ExtensionUnits.unit (algebraMap R S) M m) (h m)

end

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.ExtensionUnits OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleEffectiveDescent

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (M : ModuleCat.{u} R)

/-- The standard comparison coalgebra has the expected value on each unit generator. -/
theorem comparison_coaction_unit (m : M) :
    ((Comonad.comparison (extendRestrictScalarsAdj f)).obj M).a (Scalar.ExtensionUnits.unit f M m) =
      Scalar.ExtensionUnits.unit f ((restrictScalars f).obj ((extendScalars f).obj M)) (Scalar.ExtensionUnits.unit f M m) := rfl

/-- Coaction units determine the actual canonical descent coaction. -/
theorem coaction_eq_of_units (D : CocycleEffectiveDescent.RingMapDatum f ((extendScalars f).obj M))
    (h : letI := f.toAlgebra; HasUnitCoaction R S M D) :
    (CocycleEffectiveDescent.moduleDatum f ((extendScalars f).obj M) D).a =
      ((Comonad.comparison (extendRestrictScalarsAdj f)).obj M).a := by
  apply Scalar.ExtensionUnits.hom_ext f M
  intro m
  let := f.toAlgebra
  have h₁ := CoalgebraMorphisms.coaction_apply f ((extendScalars f).obj M) D
    (Scalar.ExtensionUnits.unit f M m)
  exact h₁.trans ((h m).trans (comparison_coaction_unit f M m).symm)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.UnitCoaction
