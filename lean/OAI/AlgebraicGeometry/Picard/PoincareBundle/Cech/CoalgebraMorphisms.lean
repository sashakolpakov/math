import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.GluingMorphisms
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CoalgebraMapCoordinates

/-! # Coalgebra Morphisms -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.CoalgebraMorphisms

noncomputable section

/-!
# Actual morphisms of extracted descent coalgebras preserve the original Čech gluing
-/

open _root_.CategoryTheory _root_.ModuleCat

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleEffectiveDescent

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- The extracted categorical coaction has the original tensor-switch coordinates. -/
theorem coaction_apply (M : ModuleCat.{u} S) (D : CocycleEffectiveDescent.RingMapDatum f M) (m : M) :
    letI := f.toAlgebra
    (CocycleEffectiveDescent.moduleDatum f M D).a m = D.toSwitch.coaction m := rfl

variable (M N : ModuleCat.{u} S) (D : CocycleEffectiveDescent.RingMapDatum f M) (E : CocycleEffectiveDescent.RingMapDatum f N)

/-- The underlying S-linear map of an actual descent-coalgebra morphism. -/
def underlyingMap (a : CocycleEffectiveDescent.moduleDatum f M D ⟶ CocycleEffectiveDescent.moduleDatum f N E) : M ⟶ N := a.f

/-- Such a morphism has the exact tensor-coordinate coaction compatibility. -/
theorem coaction_compatible (a : CocycleEffectiveDescent.moduleDatum f M D ⟶ CocycleEffectiveDescent.moduleDatum f N E) (m : M) :
    letI := f.toAlgebra
    ModelNaturality.tensorMap R S (underlyingMap f M N D E a) (D.toSwitch.coaction m) =
      E.toSwitch.coaction ((underlyingMap f M N D E a) m) := by
  let := f.toAlgebra
  have hp := CoalgebraMapCoordinates.compatibility_apply f (CocycleEffectiveDescent.moduleDatum f M D).a
    (CocycleEffectiveDescent.moduleDatum f N E).a (underlyingMap f M N D E a) a.h m
  erw [coaction_apply f M D m,
    coaction_apply f N E ((underlyingMap f M N D E a) m)] at hp
  exact hp

/-- No original Čech compatibility is lost when morphisms are expressed as coalgebra morphisms. -/
theorem preservesGluing (a : CocycleEffectiveDescent.moduleDatum f M D ⟶ CocycleEffectiveDescent.moduleDatum f N E) :
    letI := f.toAlgebra
    GluingMorphisms.PreservesGluing R S (underlyingMap f M N D E a) D E := by
  let := f.toAlgebra
  apply (GluingMorphisms.preservesGluing_iff_coaction R S
    (underlyingMap f M N D E a) D E).mpr
  exact coaction_compatible f M N D E a

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.CoalgebraMorphisms
