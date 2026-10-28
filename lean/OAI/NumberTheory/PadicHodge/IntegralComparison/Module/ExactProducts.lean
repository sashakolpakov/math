import Mathlib.Algebra.Category.ModuleCat.AB

/-! # Exact Products -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Module.ExactProducts

noncomputable section

/-! Exact products for the actual module category, with independent coefficient and carrier universes. -/

open _root_.CategoryTheory Limits

universe u v w

variable (R : Type u) [CommRing R]

instance products : AB4Star (ModuleCat.{max u w} R) where
  ofShape J := HasExactLimitsOfShape.domain_of_functor (Discrete J)
    (forget₂ (ModuleCat.{max u w} R) AddCommGrpCat.{max u w})

theorem smallProducts [HasProducts.{v} (ModuleCat.{max u v w} R)] :
    AB4StarOfSize.{v} (ModuleCat.{max u v w} R) where
  ofShape J :=
    let _ : AB4Star (ModuleCat.{max u v w} R) := products.{u, max v w} R
    HasExactLimitsOfShape.of_domain_equivalence (ModuleCat.{max u v w} R)
      (Discrete.equivalence (Equiv.ulift : ULift.{max u w} J ≃ J))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Module.ExactProducts
