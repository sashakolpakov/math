import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Scalar Restriction -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.ScalarRestriction.ScalarRestrictionIso

noncomputable section

/-!
# Restricting scalars along a compatible algebra action

The identity on a module identifies its given smaller-ring action with
the action obtained by restricting its larger-ring module structure.
-/

open _root_.CategoryTheory Limits

universe u

variable (R S M : Type u) [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

def iso : ModuleCat.of R M ≅ (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S M) :=
  LinearEquiv.toModuleIso <|
    @AddEquiv.toLinearEquiv _ _ _ _ _ _ (inferInstance : Module R M)
      (((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S M)).isModule)
      (AddEquiv.refl M) (fun r x => (IsScalarTower.algebraMap_smul S r x).symm)

theorem restrictScalars_preservesHomology {A B : Type u} [Ring A] [Ring B] (f : A →+* B) :
    (ModuleCat.restrictScalars.{u} f).PreservesHomology where
  preservesKernels {_ _} g := ModuleCat.preservesLimit_restrictScalars f (parallelPair g 0)
  preservesCokernels {_ _} g := ModuleCat.preservesColimit_restrictScalars f (parallelPair g 0)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.ScalarRestriction.ScalarRestrictionIso
