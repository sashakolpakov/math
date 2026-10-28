import OAI.RepresentationTheory.Theta.Geometric.Theorem
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Action
import OAI.AlgebraicGeometry.Albanese.Construction.Mon
import OAI.Algebra.Modules.ElementaryDivisors
import OAI.RepresentationTheory.Hecke.SphericalAction

/-! # Geometry -/

namespace OAI.RepresentationTheory.Hecke.Geometry.GaloisValuation

noncomputable section

/-! Construct the complete GeometricTheta output and its TateComparison input from the existing
geometric datum. The one-step IsogenyQuotient realization remains explicitly visible. -/

open OAI.AlgebraicGeometry.Albanese.Construction.Mon

private theorem albanese_proved : AlgebraicGeometry.PELModuli.IntegralModel.Albanese.ConstructionInput := by
  intro X _ x
  exact AlgebraicGeometry.Albanese.Construction.Mon.exists_albanese X x

private theorem elementary_divisors_proved (q : ℕ) [Fact q.Prime] :
    AlgebraicGeometry.AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q] := by
  intro n π hπ L M hL hM
  let := hL
  let := hM
  exact Algebra.Modules.ElementaryDivisors.lattices_elementary_divisors π hπ L M

theorem hecke_action_proved
    {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) : Theta.Geometric.TateComparison.TateComparisonOutput D hg hq hIsogenyQuotient := by
  exact AlgebraicGeometry.AbelianScheme.TateComparison.Action.spherical_hecke_algebra_action_constructed s hs hdegree q D
    hg hq hIsogenyQuotient albanese_proved (elementary_divisors_proved q)

theorem theta_covariance_proved : SphericalAction.GeometricThetaInput := by
  intro E K _ _ _ _ _ _ s q _ hs hdegree Index Ga MpR MpF MpA _ _ _ _ _ _ _ _
    D hg hq hIsogenyQuotient hTateComparison hc hh ha hdense
  exact Theta.Geometric.Theorem.active_hecke_action_and_finite_weil_covariance_constructed
    hs hdegree D hg hq hIsogenyQuotient hTateComparison hc hh ha hdense

end

end OAI.RepresentationTheory.Hecke.Geometry.GaloisValuation
