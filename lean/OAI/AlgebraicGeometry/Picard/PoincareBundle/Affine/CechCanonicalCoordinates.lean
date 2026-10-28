import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CanonicalGluing
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.DescentRecovery

/-! # Cech Canonical Coordinates -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CechCanonicalCoordinates

noncomputable section

/-!
# Canonical affine Čech gluing in the actual ring-map coordinates
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.ModuleCat TensorProduct
open scoped TensorProduct

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModuleModels OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CanonicalGluing OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleEffectiveDescent

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- First overlap projection in the scalar structures supplied by the affine map. -/
def firstProjection : letI := f.hom.toAlgebra; S ⟶ CommRingCat.of (S ⊗[R] S) := by
  letI := f.hom.toAlgebra
  exact CommRingCat.ofHom (Cech.ModuleModels.firstMap R S)

/-- Second overlap projection in those same scalar structures. -/
def secondProjection : letI := f.hom.toAlgebra; S ⟶ CommRingCat.of (S ⊗[R] S) := by
  letI := f.hom.toAlgebra
  exact CommRingCat.ofHom (Cech.ModuleModels.secondMap R S)

/-- Both overlap coordinates have the same image on the base ring. -/
theorem baseEquation :
    letI := f.hom.toAlgebra
    f ≫ firstProjection f = f ≫ secondProjection f := by
  let := f.hom.toAlgebra
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact Cech.ModuleModels.projection_base_eq R S

/-- The canonical ring-map Čech datum has precisely the explicit scalar transition. -/
theorem canonical_datum_gluing (A : ModuleCat.{u} R) :
    letI := f.hom.toAlgebra
    (Canonical.CechCoaction.datum f.hom A).gluing =
      Scalar.ExtensionUnits.transition f.hom (Cech.ModuleModels.firstMap R S) (Cech.ModuleModels.secondMap R S)
        (RingHom.ext (Cech.ModuleModels.projection_base_eq R S)) A := rfl

/-- Categorical affine coordinates recover the exact canonical Čech gluing isomorphism. -/
theorem moduleTransition_eq_canonical (A : ModuleCat.{u} R) :
    letI := f.hom.toAlgebra
    CanonicalGluing.moduleTransition f (firstProjection f) (secondProjection f) (baseEquation f) A =
      (Canonical.CechCoaction.datum f.hom A).gluing := by
  let := f.hom.toAlgebra
  have h := CanonicalGluing.moduleTransition_eq_scalar f (firstProjection f) (secondProjection f) (baseEquation f) A
  exact h.trans (canonical_datum_gluing f A).symm

/-- The recovered module comparison preserves Čech gluing in the actual affine coordinates. -/
theorem recovery_compatible (M : ModuleCat.{u} S) (hf : f.hom.FaithfullyFlat)
    (D : CocycleEffectiveDescent.RingMapDatum f.hom M) :
    letI := f.hom.toAlgebra
    (extendScalars (firstProjection f).hom).map (CocycleEffectiveDescent.baseChangeIso f.hom M hf D).hom ≫ D.gluing.hom =
      (CanonicalGluing.moduleTransition f (firstProjection f) (secondProjection f) (baseEquation f)
        (CocycleEffectiveDescent.descendedModule f.hom M hf D)).hom ≫
          (extendScalars (secondProjection f).hom).map (CocycleEffectiveDescent.baseChangeIso f.hom M hf D).hom := by
  let := f.hom.toAlgebra
  rw [moduleTransition_eq_canonical]
  exact Cech.DescentRecovery.baseChangeIso_preservesGluing f.hom M hf D

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CechCanonicalCoordinates
