import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CoverRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Continuous
import OAI.NumberTheory.PadicHodge.IntegralComparison.SiteCocontinuity

/-! # Cocontinuous -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Cocontinuous

noncomputable section

/-!
# IntegralComparison: cocontinuity of crystalline postcomposition

Pullbacks of generating covers contain actual principal covering families
from the source site. Induction on the generated Grothendieck topology
then proves cocontinuity without assuming a site comparison theorem.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Localization
open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LocalizationLift OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CoverRefinement
open OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Covers OAI.NumberTheory.PadicHodge.IntegralComparison.SiteCocontinuity

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
variable {fY : Y ⟶ Spec (CommRingCat.of B)}
variable (g : X ⟶ Y) (hg : g ≫ fY = f)

lemma generator_pullback {U : BigCrystallineSite.Object p B J δ fY} {V : BigCrystallineSite.Object p B J δ f}
    (R : Presieve U) (hR : R ∈ BigCrystallineSite.Object.precoverage U) (α : (BigCrystallineSite.postcompose g hg).obj V ⟶ U) :
    ((Sieve.generate R).pullback α).functorPullback (BigCrystallineSite.postcompose g hg) ∈ BigCrystallineSite.Object.topology V := by
  obtain ⟨r, hr, hgen⟩ := CoverRefinement.principal_refinement R hR
  let φ : U.ring →+* V.ring := α.ringMap.toRingHom
  let a : PrimeSpectrum U.ring → V.ring := fun i => φ (r i)
  have ha : Ideal.span (Set.range a) = ⊤ := by
    have h := congrArg (Ideal.map φ) hr
    rw [Ideal.map_span, ← Set.range_comp, Ideal.map_top] at h
    exact h
  apply BigCrystallineSite.Object.topology.superset_covering ?_ (CrystallinePrincipal.Covers.coveringSieve V a ha)
  apply (Sieve.generate_le_iff _ _).mpr
  intro W b hb
  cases hb with
  | mk i =>
    let β := (BigCrystallineSite.postcompose g hg).map (Localization.hom V (a i)) ≫ α
    have hu : IsUnit (β.ringMap (r i)) :=
      IsLocalization.Away.algebraMap_isUnit (S := Localization.Ring V (a i)) (a i)
    change Sieve.generate R β
    rw [← LocalizationLift.liftHom_comp β (r i) hu]
    exact (Sieve.generate R).downward_closed (hgen i) (LocalizationLift.liftHom β (r i) hu)

instance postcompose_cocontinuous :
    (BigCrystallineSite.postcompose (p := p) (J := J) (δ := δ) g hg).IsCocontinuous BigCrystallineSite.Object.topology BigCrystallineSite.Object.topology :=
  SiteCocontinuity.cocontinuous_of_generating_pullbacks (BigCrystallineSite.postcompose g hg) BigCrystallineSite.Object.topology BigCrystallineSite.Object.precoverage
    (fun R hR α => generator_pullback g hg R hR α)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Cocontinuous
