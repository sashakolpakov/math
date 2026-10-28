import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.CoalgebraMorphisms

/-! # Coalgebra Fullness -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.CoalgebraFullness

noncomputable section

/-!
# Original Čech-compatible morphisms give actual descent-coalgebra morphisms
-/

open _root_.CategoryTheory _root_.ModuleCat

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleEffectiveDescent

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  {M N : ModuleCat.{u} S}

/-- Tensor-coordinate compatibility gives the categorical coaction equation. -/
theorem compatibility_of_apply
    (α : M ⟶ (extendRestrictScalarsAdj.{u,u,u} f).toComonad.obj M)
    (β : N ⟶ (extendRestrictScalarsAdj.{u,u,u} f).toComonad.obj N) (a : M ⟶ N)
    (h : letI := f.toAlgebra
      ∀ m, ModelNaturality.tensorMap R S a (α m) = β (a m)) :
    α ≫ (extendRestrictScalarsAdj.{u,u,u} f).toComonad.map a = a ≫ β := by
  let := f.toAlgebra
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  exact (CoalgebraMapCoordinates.map_apply f a (α m)).trans (h m)

variable (M N) (D : CocycleEffectiveDescent.RingMapDatum f M) (E : CocycleEffectiveDescent.RingMapDatum f N) (a : M ⟶ N)

/-- Compatibility with the original gluing implies the actual coaction compatibility. -/
theorem compatibility
    (h : letI := f.toAlgebra; GluingMorphisms.PreservesGluing R S a D E) :
    (CocycleEffectiveDescent.moduleDatum f M D).a ≫ (extendRestrictScalarsAdj f).toComonad.map a =
      a ≫ (CocycleEffectiveDescent.moduleDatum f N E).a := by
  apply compatibility_of_apply f (CocycleEffectiveDescent.moduleDatum f M D).a (CocycleEffectiveDescent.moduleDatum f N E).a a
  let := f.toAlgebra
  have hc := (GluingMorphisms.preservesGluing_iff_coaction R S a D E).mp h
  intro m
  exact (congrArg (ModelNaturality.tensorMap R S a)
    (CoalgebraMorphisms.coaction_apply f M D m)).trans
      ((hc m).trans (CoalgebraMorphisms.coaction_apply f N E (a m)).symm)

/-- The exact original module morphism, now equipped with its proved descent compatibility. -/
def ofGluing
    (h : letI := f.toAlgebra; GluingMorphisms.PreservesGluing R S a D E) :
    CocycleEffectiveDescent.moduleDatum f M D ⟶ CocycleEffectiveDescent.moduleDatum f N E where
  f := a
  h := compatibility f M N D E a h

theorem ofGluing_f
    (h : letI := f.toAlgebra; GluingMorphisms.PreservesGluing R S a D E) :
    (ofGluing f M N D E a h).f = a := rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.CoalgebraFullness
