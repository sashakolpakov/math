import OAI.AlgebraicGeometry.Comparison.Betti.ReflectiveColimitPreservation
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.Topology.Sheaves.Abelian

/-! # Sheaf Forget Additive -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Module.SheafForgetAdditive.Local

noncomputable section

section

/-! Forgetting the ring action on actual sheaves of modules is exact and preserves finite sums. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {X : TopCat.{0}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{0})

instance moduleSheafForget_preservesColimitsOfShape (J : Type) [SmallCategory J] :
    PreservesColimitsOfShape J (SheafOfModules.toSheaf.{0} R) := by
  let F := PresheafOfModules.sheafification.{0} (𝟙 R.obj)
  let G := SheafOfModules.toSheaf.{0} R
  let adj := PresheafOfModules.sheafificationAdjunction.{0} (𝟙 R.obj)
  let : PreservesColimitsOfShape J (F ⋙ G) :=
    preservesColimitsOfShape_of_natIso (PresheafOfModules.sheafificationCompToSheaf (𝟙 R.obj)).symm
  exact ReflectiveColimitPreservation.Category.preservesColimitsOfShape_of_reflective F _ G (asIso adj.counit)

instance moduleSheafForget_preservesFiniteColimits : PreservesFiniteColimits (SheafOfModules.toSheaf.{0} R) where
  preservesFiniteColimits _ := inferInstance

instance moduleSheafForget_preservesHomology : (SheafOfModules.toSheaf.{0} R).PreservesHomology := by
  infer_instance

end

/-! The original module-sheaf forgetful functor preserves addition of maps. -/

open _root_.CategoryTheory _root_.TopologicalSpace

instance moduleSheafForget_additive {X : TopCat.{0}}
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{0}) :
    (SheafOfModules.toSheaf.{0} R).Additive where
  map_add := by
    intro M N f g
    apply Sheaf.hom_ext
    rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Module.SheafForgetAdditive.Local
