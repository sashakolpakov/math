import OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.CechCoaction

/-! # Descent Recovery -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.DescentRecovery

noncomputable section

/-!
# Effective affine descent recovers the full original Čech gluing
-/

open _root_.CategoryTheory _root_.ModuleCat

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleEffectiveDescent

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (M : ModuleCat.{u} S) (hf : f.FaithfullyFlat) (D : CocycleEffectiveDescent.RingMapDatum f M)

/-- Recovery identifies the original coalgebra with the canonical Čech datum of its descent. -/
def dataIso :
    CocycleEffectiveDescent.moduleDatum f ((extendScalars f).obj (CocycleEffectiveDescent.descendedModule f M hf D))
      (Canonical.CechCoaction.datum f (CocycleEffectiveDescent.descendedModule f M hf D)) ≅ CocycleEffectiveDescent.moduleDatum f M D :=
  Canonical.CechCoaction.comparisonIso f (CocycleEffectiveDescent.descendedModule f M hf D) ≪≫
    CocycleEffectiveDescent.descentDataIso f M hf D

/-- The recovered module isomorphism retains the original descent datum. -/
def recoveryIso : (extendScalars f).obj (CocycleEffectiveDescent.descendedModule f M hf D) ≅ M :=
  (extendRestrictScalarsAdj f).toComonad.forget.mapIso (dataIso f M hf D)

/-- Its underlying module isomorphism is the original faithfully flat descent comparison. -/
theorem recoveryIso_eq_baseChangeIso : recoveryIso f M hf D = CocycleEffectiveDescent.baseChangeIso f M hf D := by
  apply Iso.ext
  change (Canonical.CechCoaction.comparisonIso f (CocycleEffectiveDescent.descendedModule f M hf D)).hom.f ≫
    (CocycleEffectiveDescent.descentDataIso f M hf D).hom.f = (CocycleEffectiveDescent.descentDataIso f M hf D).hom.f
  rw [Canonical.CechCoaction.comparisonIso_hom_f]
  exact Category.id_comp _

/-- The actual recovered comparison preserves the entire original overlap gluing. -/
theorem preservesGluing :
    letI := f.toAlgebra
    GluingMorphisms.PreservesGluing R S (recoveryIso f M hf D).hom
      (Canonical.CechCoaction.datum f (CocycleEffectiveDescent.descendedModule f M hf D)) D :=
  CoalgebraMorphisms.preservesGluing f
    ((extendScalars f).obj (CocycleEffectiveDescent.descendedModule f M hf D)) M
    (Canonical.CechCoaction.datum f (CocycleEffectiveDescent.descendedModule f M hf D)) D (dataIso f M hf D).hom

/-- Thus the original base-change isomorphism itself preserves the original Čech gluing. -/
theorem baseChangeIso_preservesGluing :
    letI := f.toAlgebra
    GluingMorphisms.PreservesGluing R S (CocycleEffectiveDescent.baseChangeIso f M hf D).hom
      (Canonical.CechCoaction.datum f (CocycleEffectiveDescent.descendedModule f M hf D)) D := by
  rw [← recoveryIso_eq_baseChangeIso f M hf D]
  exact preservesGluing f M hf D

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.DescentRecovery
