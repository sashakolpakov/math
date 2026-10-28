import Mathlib

/-! # Abelian Sheaf Universes -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AbelianSheafUniverses

noncomputable section

/-! # IntegralComparison: abelian sheaves at the actual enlarged coefficient universe -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w

variable {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)

theorem hasSheafify : HasSheafify J AddCommGrpCat.{max u v w} := by
  have : PreservesFilteredColimitsOfSize.{max v w, max v w}
      (forget AddCommGrpCat.{max u v w}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max u v w, max u v w, max v w, max v w} _
  exact HasSheafify.mk' _ _ (plusPlusAdjunction J AddCommGrpCat.{max u v w})

theorem isGrothendieckAbelian :
    letI := hasSheafify.{u, v, w} J
    IsGrothendieckAbelian.{max u v w} (Sheaf J AddCommGrpCat.{max u v w}) := by
  let := hasSheafify.{u, v, w} J
  let : SmallCategory (SmallModel.{max u v w} C) :=
    smallCategorySmallModel.{max u v w, w, v} C
  let e := equivSmallModel.{max u v w} C
  let K := e.inverse.inducedTopology J
  have : HasSheafify K AddCommGrpCat.{max u v w} :=
    HasSheafify.mk' _ _ (plusPlusAdjunction K AddCommGrpCat.{max u v w})
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall.{max u v w, max u v w, w, (max u v w) + 1, v}
    J AddCommGrpCat.{max u v w}

theorem enoughInjectives : EnoughInjectives (Sheaf J AddCommGrpCat.{max u v w}) := by
  let := hasSheafify.{u, v, w} J
  have := isGrothendieckAbelian.{u, v, w} J
  infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AbelianSheafUniverses
