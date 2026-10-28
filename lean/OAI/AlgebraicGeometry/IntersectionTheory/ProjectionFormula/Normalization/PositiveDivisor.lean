import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PositiveCycle
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.DivisorComparison
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorRestriction

/-! # Positive Divisor -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.PositiveDivisor

noncomputable section

/-! Normalization preserves the actual zero cycle of a rational
parameter whenever the parameter or its inverse is regular at each point.
This is the local chart condition supplied by a map to the projective line. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Fields OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PositiveCycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DivisorNorm

theorem positiveDivisor (Z : Scheme) [IsIntegral Z] [AlgebraicGeometry.IsNoetherian Z]
    (π : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType π] (g : Z.functionField) (hg : g ≠ 0)
    (hreg : ∀ x : Z,
      (∃ u : Z.presheaf.stalk x, algebraMap (Z.presheaf.stalk x) Z.functionField u = g) ∨
      (∃ u : Z.presheaf.stalk x, algebraMap (Z.presheaf.stalk x) Z.functionField u = g⁻¹)) :
    letI := DivisorComparison.normalization_noetherian Z π
    CyclePushforward.pointPushforward (Normalization.Scheme.normalizationMap Z)
      (PositiveCycle.positivePart (Affine.DivisorNorm.rationalPrincipalDivisor (Normalization.Scheme.normalization Z) ((Fields.normalizationFieldIso Z).hom g))) =
        PositiveCycle.positivePart (Affine.DivisorNorm.rationalPrincipalDivisor Z g) := by
  let := DivisorComparison.normalization_noetherian Z π
  have hsign : ∀ x : Z,
      (∀ z : Normalization.Scheme.normalization Z, Normalization.Scheme.normalizationMap Z z = x →
        0 ≤ Affine.DivisorNorm.rationalPrincipalDivisor (Normalization.Scheme.normalization Z) ((Fields.normalizationFieldIso Z).hom g) z) ∨
      (∀ z : Normalization.Scheme.normalization Z, Normalization.Scheme.normalizationMap Z z = x →
        Affine.DivisorNorm.rationalPrincipalDivisor (Normalization.Scheme.normalization Z) ((Fields.normalizationFieldIso Z).hom g) z ≤ 0) := by
    intro x
    rcases hreg x with ⟨u, hu⟩ | ⟨u, hu⟩
    · left
      intro z hz
      subst x
      have hn := Regular.FunctionOrder.stalk_nonneg z ((Normalization.Scheme.normalizationMap Z).stalkMap z u)
      rw [← Divisor.DivisorRestriction.genericFieldMap_stalk (Normalization.Scheme.normalizationMap Z)
        (Fields.normalizationMap_genericPoint Z) z u, hu] at hn
      change 0 ≤ (Normalization.Scheme.normalization Z).ord ((Fields.normalizationFieldIso Z).hom g) z at hn
      change 0 ≤ ((Normalization.Scheme.normalization Z).ord ((Fields.normalizationFieldIso Z).hom g) z : ℚ)
      exact_mod_cast hn
    · right
      intro z hz
      subst x
      have hn := Regular.FunctionOrder.stalk_nonneg z ((Normalization.Scheme.normalizationMap Z).stalkMap z u)
      rw [← Divisor.DivisorRestriction.genericFieldMap_stalk (Normalization.Scheme.normalizationMap Z)
        (Fields.normalizationMap_genericPoint Z) z u, hu, map_inv₀, Principal.DivisorInverse.ord_inv] at hn
      change 0 ≤ -(Normalization.Scheme.normalization Z).ord ((Fields.normalizationFieldIso Z).hom g) z at hn
      change ((Normalization.Scheme.normalization Z).ord ((Fields.normalizationFieldIso Z).hom g) z : ℚ) ≤ 0
      exact_mod_cast (neg_nonneg.mp hn)
  rw [PositiveCycle.Pushforward.positivePart_comm (Normalization.Scheme.normalizationMap Z) _ hsign,
    DivisorComparison.normalization_principalDivisor Z π g hg]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.PositiveDivisor
