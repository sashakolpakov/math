import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.CycleForms
import OAI.AlgebraicTopology.Kunneth.ProjectiveCupPurity

/-! # Cup Purity -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.CupPurity.CM.Abelian

noncomputable section

/-! Complementary pure classes have zero cup product when their total type is off diagonal. -/

theorem complexCohomology_cast_eq_zero_iff (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {m n : ℕ} (h : m = n) (a : X.complexCohomology m) :
    cast (congrArg (fun k => (X.complexCohomology k : Type)) h) a = 0 ↔ a = 0 := by
  subst n
  rfl

theorem pure_top_cup_eq_zero (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q r s : ℕ)
    (hdim : (p + q) + (r + s) = 2 * X.complexDimension)
    (hneq : p + r ≠ q + s)
    (a : X.complexCohomology (p + q)) (b : X.complexCohomology (r + s))
    (ha : a ∈ X.pureBettiSubspace p q) (hb : b ∈ X.pureBettiSubspace r s) :
    AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace X.toOver) (p + q) (r + s) a b = 0 := by
  have hc := AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveCup_mem_pure X p q r s a b ha hb
  have hz := CycleForms.CM.Abelian.pureBettiClass_eq_zero_of_offDiagonal_top X (p + r) (q + s)
    (by omega) hneq _ hc
  exact (complexCohomology_cast_eq_zero_iff X (add_add_add_comm p q r s) _).mp hz

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.CupPurity.CM.Abelian
