import OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.CechCocycle
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.UnitCoaction

/-! # Cech Coaction -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.CechCoaction

noncomputable section

/-!
# Canonical Čech gluing has the standard scalar-extension descent coaction
-/

open _root_.CategoryTheory _root_.ModuleCat TensorProduct
open scoped TensorProduct ChangeOfRings

universe u

section

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.ExtensionUnits OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModuleModels OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModelUnits

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (M : ModuleCat.{u} R)

/-- Canonical Čech gluing has the canonical unit coaction. -/
theorem coaction_units :
    Cech.UnitCoaction.HasUnitCoaction R S M (CechCocycle.datum R S M) :=
  Cech.UnitCoaction.hasUnitCoaction_of_gluingUnits R S M
    (CechCocycle.datum R S M) (CechCocycle.gluing_units R S M)

end

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.ExtensionUnits OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleEffectiveDescent

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (M : ModuleCat.{u} R)

/-- Canonical gluing for an arbitrary scalar-extension ring map. -/
def datum : CocycleEffectiveDescent.RingMapDatum f ((extendScalars f).obj M) := by
  letI := f.toAlgebra
  exact CechCocycle.datum R S M

/-- Extracting the coaction from canonical Čech gluing gives the actual comparison coaction. -/
theorem coaction_eq :
    (CocycleEffectiveDescent.moduleDatum f ((extendScalars f).obj M) (datum f M)).a =
      ((Comonad.comparison (extendRestrictScalarsAdj f)).obj M).a := by
  apply Cech.UnitCoaction.coaction_eq_of_units f M (datum f M)
  let := f.toAlgebra
  exact coaction_units R S M

/-- The canonical Čech coalgebra is identified with the comparison coalgebra by the identity. -/
def comparisonIso :
    CocycleEffectiveDescent.moduleDatum f ((extendScalars f).obj M) (datum f M) ≅
      (Comonad.comparison (extendRestrictScalarsAdj f)).obj M :=
  Comonad.Coalgebra.isoMk (Iso.refl _) (by
    change (CocycleEffectiveDescent.moduleDatum f ((extendScalars f).obj M) (datum f M)).a ≫
      (extendRestrictScalarsAdj f).toComonad.map (𝟙 _) =
        𝟙 _ ≫ ((Comonad.comparison (extendRestrictScalarsAdj f)).obj M).a
    rw [(extendRestrictScalarsAdj f).toComonad.map_id, Category.comp_id, Category.id_comp]
    exact coaction_eq f M)

/-- This coaction identification leaves the underlying module map equal to the identity. -/
theorem comparisonIso_hom_f : (comparisonIso f M).hom.f = 𝟙 _ := rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.CechCoaction
