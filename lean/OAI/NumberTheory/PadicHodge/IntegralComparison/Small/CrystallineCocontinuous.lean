import OAI.NumberTheory.PadicHodge.IntegralComparison.Small.CrystallinePullback
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CoverRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.SiteCocontinuity

/-! # Crystalline Cocontinuous -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Small.CrystallineCocontinuous

noncomputable section

/-!
# IntegralComparison: cocontinuity of the small-site inclusion

Principal refinements pull back to the actual principal coverings in
the original small crystalline site.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Site
open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Localization OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LocalizationLift
open OAI.NumberTheory.PadicHodge.IntegralComparison.Small.CrystallineLocalization OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CoverRefinement
open OAI.NumberTheory.PadicHodge.IntegralComparison.SiteCocontinuity

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}

lemma generator_pullback {U : BigCrystallineSite.Object p B J δ f} {V : Crystalline.Site.AffineThickening p B J δ f}
    (R : Presieve U) (hR : R ∈ BigCrystallineSite.Object.precoverage U) (α : BigCrystallineSite.fromSmall.obj V ⟶ U) :
    ((Sieve.generate R).pullback α).functorPullback BigCrystallineSite.fromSmall ∈ Crystalline.Site.AffineThickening.topology V := by
  obtain ⟨r, hr, hgen⟩ := Crystalline.CoverRefinement.principal_refinement R hR
  let φ : U.ring →+* V.ring := α.ringMap.toRingHom
  let a : PrimeSpectrum U.ring → V.ring := fun i => φ (r i)
  have ha : Ideal.span (Set.range a) = ⊤ := by
    have h := congrArg (Ideal.map φ) hr
    rw [Ideal.map_span, ← Set.range_comp, Ideal.map_top] at h
    exact h
  apply Crystalline.Site.AffineThickening.topology.superset_covering ?_
    (Crystalline.Site.AffineThickening.precoverage.generate_mem_toGrothendieck (CrystallineLocalization.small_covering V a ha))
  apply (Sieve.generate_le_iff _ _).mpr
  intro W b hb
  cases hb with
  | mk i =>
    let β := BigCrystallineSite.fromSmall.map (CrystallineLocalization.smallHom V (a i)) ≫ α
    have hu : IsUnit (β.ringMap (r i)) :=
      IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (a i)) (a i)
    change Sieve.generate R β
    rw [← Crystalline.LocalizationLift.liftHom_comp β (r i) hu]
    exact (Sieve.generate R).downward_closed (hgen i) (Crystalline.LocalizationLift.liftHom β (r i) hu)

instance fromSmall_cocontinuous :
    (BigCrystallineSite.fromSmall (p := p) (J := J) (δ := δ) (f := f)).IsCocontinuous
      Crystalline.Site.AffineThickening.topology BigCrystallineSite.Object.topology :=
  SiteCocontinuity.cocontinuous_of_generating_pullbacks BigCrystallineSite.fromSmall Crystalline.Site.AffineThickening.topology BigCrystallineSite.Object.precoverage
    (fun R hR α => generator_pullback R hR α)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Small.CrystallineCocontinuous
