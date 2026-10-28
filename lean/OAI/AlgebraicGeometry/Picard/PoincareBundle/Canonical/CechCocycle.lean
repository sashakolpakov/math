import OAI.AlgebraicGeometry.Picard.PoincareBundle.ExtendedTransitionUnits
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleEffectiveDescent

/-! # Cech Cocycle -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.CechCocycle

noncomputable section

/-!
# The canonical Čech cocycle on a module pulled back from the base
-/

open _root_.CategoryTheory _root_.ModuleCat TensorProduct
open scoped TensorProduct ChangeOfRings

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.ExtensionUnits OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModuleModels OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.TripleGluing

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (M : ModuleCat.{u} R)

/-- The two overlap pullbacks identify through scalar extension from the original base. -/
def gluing : Cech.ModuleModels.firstPullback R S ((extendScalars (algebraMap R S)).obj M) ≅
    Cech.ModuleModels.secondPullback R S ((extendScalars (algebraMap R S)).obj M) :=
  Scalar.ExtensionUnits.transition (algebraMap R S) (Cech.ModuleModels.firstMap R S) (Cech.ModuleModels.secondMap R S)
    (RingHom.ext (Cech.ModuleModels.projection_base_eq R S)) M

/-- The canonical overlap identification fixes the original module's unit generators. -/
theorem gluing_units :
    Scalar.ExtensionUnits.PreservesUnits (algebraMap R S) (Cech.ModuleModels.firstMap R S) (Cech.ModuleModels.secondMap R S) M (CechCocycle.gluing R S M).hom :=
  Scalar.ExtensionUnits.transition_preservesUnits (algebraMap R S) (Cech.ModuleModels.firstMap R S) (Cech.ModuleModels.secondMap R S)
    (RingHom.ext (Cech.ModuleModels.projection_base_eq R S)) M

theorem gluing12_units :
    Scalar.ExtensionUnits.PreservesUnits (algebraMap R S) (Cech.TripleGluing.slot1 R S) (Cech.TripleGluing.slot2 R S) M
      (Cech.TripleGluing.gluing12 R S ((extendScalars (algebraMap R S)).obj M) (CechCocycle.gluing R S M)) :=
  ExtendedTransitionUnits.extend_preservesUnits (algebraMap R S)
    (Cech.ModuleModels.firstMap R S) (Cech.ModuleModels.secondMap R S) (Cech.TripleGluing.pair12 R S) M (CechCocycle.gluing R S M).hom
    (gluing_units R S M)

theorem gluing13_units :
    Scalar.ExtensionUnits.PreservesUnits (algebraMap R S) (Cech.TripleGluing.slot1 R S) (Cech.TripleGluing.slot3 R S) M
      (Cech.TripleGluing.gluing13 R S ((extendScalars (algebraMap R S)).obj M) (CechCocycle.gluing R S M)) :=
  ExtendedTransitionUnits.transported_extend_preservesUnits (algebraMap R S)
    (Cech.ModuleModels.firstMap R S) (Cech.ModuleModels.secondMap R S) (Cech.TripleGluing.pair13 R S) (Cech.TripleGluing.slot1 R S) (Cech.TripleGluing.slot3 R S)
    (Cech.TripleGluing.pair13_first R S) (Cech.TripleGluing.pair13_second R S) M (CechCocycle.gluing R S M).hom
    (gluing_units R S M)

theorem gluing23_units :
    Scalar.ExtensionUnits.PreservesUnits (algebraMap R S) (Cech.TripleGluing.slot2 R S) (Cech.TripleGluing.slot3 R S) M
      (Cech.TripleGluing.gluing23 R S ((extendScalars (algebraMap R S)).obj M) (CechCocycle.gluing R S M)) :=
  ExtendedTransitionUnits.transported_extend_preservesUnits (algebraMap R S)
    (Cech.ModuleModels.firstMap R S) (Cech.ModuleModels.secondMap R S) (Cech.TripleGluing.pair23 R S) (Cech.TripleGluing.slot2 R S) (Cech.TripleGluing.slot3 R S)
    (Cech.TripleGluing.pair23_first R S) (Cech.TripleGluing.pair23_second R S) M (CechCocycle.gluing R S M).hom
    (gluing_units R S M)

/-- The canonical gluing satisfies the full triple-overlap cocycle. -/
theorem cocycle :
    Cech.TripleGluing.gluing12 R S ((extendScalars (algebraMap R S)).obj M) (CechCocycle.gluing R S M) ≫
      Cech.TripleGluing.gluing23 R S ((extendScalars (algebraMap R S)).obj M) (CechCocycle.gluing R S M) =
        Cech.TripleGluing.gluing13 R S ((extendScalars (algebraMap R S)).obj M) (CechCocycle.gluing R S M) :=
  Scalar.ExtensionUnits.composition_eq_of_units (algebraMap R S) (Cech.TripleGluing.slot1 R S) (Cech.TripleGluing.slot2 R S) (Cech.TripleGluing.slot3 R S) M
    _ _ _ (gluing12_units R S M) (gluing23_units R S M) (gluing13_units R S M)

/-- Actual canonical descent data, whose cocycle is proved from scalar-extension comparisons. -/
def datum : CocycleEffectiveDescent.CechCocycle R S
    ((extendScalars (algebraMap R S)).obj M) where
  gluing := CechCocycle.gluing R S M
  cocycle := CechCocycle.cocycle R S M

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.CechCocycle
