import Mathlib

/-! # Sheaf Universes -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafUniverses

noncomputable section

/-!
# IntegralComparison: module-sheaf exactness and injectives at the required universes

Choosing a coefficient-module universe large enough for the site gives
exact sheafification and enough injectives. The construction includes
small coefficient rings, such as the integers, on the larger IntegralComparison sites.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w

variable {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
  (R : Type (max u v w)) [Ring R]

theorem hasSheafify : HasSheafify J (ModuleCat.{max u v w} R) := by
  have : PreservesFilteredColimitsOfSize.{max v w, max v w}
      (forget (ModuleCat.{max u v w} R)) :=
    preservesFilteredColimitsOfSize_of_univLE.{max u v w, max u v w, max v w, max v w} _
  exact HasSheafify.mk' _ _ (plusPlusAdjunction J (ModuleCat.{max u v w} R))

theorem isGrothendieckAbelian :
    letI := hasSheafify.{u, v, w} J R
    IsGrothendieckAbelian.{max u v w} (Sheaf J (ModuleCat.{max u v w} R)) := by
  let := hasSheafify.{u, v, w} J R
  let : SmallCategory (SmallModel.{max u v w} C) :=
    smallCategorySmallModel.{max u v w, w, v} C
  let e := equivSmallModel.{max u v w} C
  let K := e.inverse.inducedTopology J
  have : HasSheafify K (ModuleCat.{max u v w} R) :=
    HasSheafify.mk' _ _ (plusPlusAdjunction K (ModuleCat.{max u v w} R))
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall.{max u v w, max u v w, w, (max u v w) + 1, v}
    J (ModuleCat.{max u v w} R)

theorem enoughInjectives : EnoughInjectives (Sheaf J (ModuleCat.{max u v w} R)) := by
  let := hasSheafify.{u, v, w} J R
  have := isGrothendieckAbelian.{u, v, w} J R
  infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafUniverses
