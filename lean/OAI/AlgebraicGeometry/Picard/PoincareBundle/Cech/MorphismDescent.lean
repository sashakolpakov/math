import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.CoalgebraFullness
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.CechCoaction
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FullyFaithfulLift

/-! # Morphism Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.MorphismDescent

noncomputable section

/-!
# Effective descent of morphisms compatible with the original Čech gluing
-/

open _root_.CategoryTheory _root_.ModuleCat

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleEffectiveDescent

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

theorem comparisonIso_inv_f (M : ModuleCat.{u} R) :
    (Canonical.CechCoaction.comparisonIso f M).inv.f = 𝟙 _ := rfl

/-- Forget a comparison-coalgebra factorization while retaining its exact module maps. -/
theorem forget_fac {M A : ModuleCat.{u} R} {D : Affine.Descent.ModuleDatum f}
    (e : (Comonad.comparison (extendRestrictScalarsAdj f)).obj A ≅ D)
    (a : (Comonad.comparison (extendRestrictScalarsAdj f)).obj M ⟶ D) (b : M ⟶ A)
    (h : (Comonad.comparison (extendRestrictScalarsAdj f)).map b ≫ e.hom = a) :
    (extendScalars f).map b ≫ e.hom.f = a.f :=
  congrArg Comonad.Coalgebra.Hom.f h

variable (M : ModuleCat.{u} R) (N : ModuleCat.{u} S) (D : CocycleEffectiveDescent.RingMapDatum f N)
  (a : (extendScalars f).obj M ⟶ N)
  (h : letI := f.toAlgebra
    GluingMorphisms.PreservesGluing R S a (Canonical.CechCoaction.datum f M) D)

/-- Original Čech compatibility gives a morphism from the actual comparison coalgebra. -/
def compatibleHom : (Comonad.comparison (extendRestrictScalarsAdj f)).obj M ⟶ CocycleEffectiveDescent.moduleDatum f N D :=
  (Canonical.CechCoaction.comparisonIso f M).inv ≫
    CoalgebraFullness.ofGluing f ((extendScalars f).obj M) N
      (Canonical.CechCoaction.datum f M) D a h

theorem compatibleHom_f : (compatibleHom f M N D a h).f = a := by
  change (Canonical.CechCoaction.comparisonIso f M).inv.f ≫
    (CoalgebraFullness.ofGluing f ((extendScalars f).obj M) N
      (Canonical.CechCoaction.datum f M) D a h).f = a
  rw [comparisonIso_inv_f, CoalgebraFullness.ofGluing_f]
  exact Category.id_comp _

/-- The descended module morphism is constructed using faithfully flat comonadicity. -/
def lift (hf : f.FaithfullyFlat) : M ⟶ CocycleEffectiveDescent.descendedModule f N hf D := by
  have : (Comonad.comparison (extendRestrictScalarsAdj f)).IsEquivalence :=
    (comonadicExtendScalars hf).eqv
  exact FullyFaithfulLift.lift (Comonad.comparison (extendRestrictScalarsAdj f))
    (CocycleEffectiveDescent.descentDataIso f N hf D) (compatibleHom f M N D a h)

theorem lift_fac_coalgebra (hf : f.FaithfullyFlat) :
    (Comonad.comparison (extendRestrictScalarsAdj f)).map (lift f M N D a h hf) ≫
      (CocycleEffectiveDescent.descentDataIso f N hf D).hom = compatibleHom f M N D a h := by
  have : (Comonad.comparison (extendRestrictScalarsAdj f)).IsEquivalence :=
    (comonadicExtendScalars hf).eqv
  exact FullyFaithfulLift.lift_fac (Comonad.comparison (extendRestrictScalarsAdj f))
    (CocycleEffectiveDescent.descentDataIso f N hf D) (compatibleHom f M N D a h)

/-- Pulling back the descended map recovers the exact original Čech-compatible map. -/
theorem lift_fac (hf : f.FaithfullyFlat) :
    (extendScalars f).map (lift f M N D a h hf) ≫ (CocycleEffectiveDescent.baseChangeIso f N hf D).hom = a :=
  (forget_fac f (CocycleEffectiveDescent.descentDataIso f N hf D) (compatibleHom f M N D a h)
    (lift f M N D a h hf) (lift_fac_coalgebra f M N D a h hf)).trans
      (compatibleHom_f f M N D a h)

/-- This descended morphism is uniquely determined by the original compatible map. -/
theorem lift_unique (hf : f.FaithfullyFlat) (b : M ⟶ CocycleEffectiveDescent.descendedModule f N hf D)
    (hb : (extendScalars f).map b ≫ (CocycleEffectiveDescent.baseChangeIso f N hf D).hom = a) :
    b = lift f M N D a h hf := by
  have : (Comonad.comparison (extendRestrictScalarsAdj f)).IsEquivalence :=
    (comonadicExtendScalars hf).eqv
  apply FullyFaithfulLift.lift_unique (Comonad.comparison (extendRestrictScalarsAdj f))
    (CocycleEffectiveDescent.descentDataIso f N hf D) (compatibleHom f M N D a h) b
  apply Comonad.Coalgebra.Hom.ext
  exact hb.trans (compatibleHom_f f M N D a h).symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.MorphismDescent
