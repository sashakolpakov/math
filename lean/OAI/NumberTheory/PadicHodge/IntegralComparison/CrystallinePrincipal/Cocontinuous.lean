import OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Neighborhood
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CoverRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.SiteCocontinuity

/-! # Cocontinuous -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Cocontinuous

noncomputable section

/-!
# IntegralComparison: lifting crystalline covers to principal opens

Pullbacks of the original crystalline covering families are covering on
the principal-open basis. The argument uses principal neighborhoods for
arbitrary incoming crystalline morphisms, so it also applies to the
generated Grothendieck topology.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Localization OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LocalizationLift
open OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalOpens.Category (Principal)
open OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Functor

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} (U : BigCrystallineSite.Object p B J δ f)

abbrev toCrystalline := Functor.inclusion U ⋙ Over.forget U

theorem generator_pullback {V : BigCrystallineSite.Object p B J δ f} {r : PrincipalOpens.Category.Principal U.ring}
    (R : Presieve V) (hR : R ∈ BigCrystallineSite.Object.precoverage V)
    (β : (toCrystalline U).obj r ⟶ V) :
    ((Sieve.generate R).pullback β).functorPullback (toCrystalline U) ∈
      Principal.Topology.topology U.ring r := by
  obtain ⟨t, ht, hgen⟩ := Crystalline.CoverRefinement.principal_refinement R hR
  apply (Principal.Topology.covering_iff U.ring _).mpr
  intro z hz
  rw [← Crystalline.Localization.hom_range U r.function] at hz
  obtain ⟨w, rfl⟩ := hz
  have hcover : (⨆ i, PrimeSpectrum.basicOpen (t i)) = ⊤ :=
    PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr ht
  have hw : BigCrystallineSite.Object.ambient.map β w ∈ ⨆ i, PrimeSpectrum.basicOpen (t i) := by
    rw [hcover]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hw
  obtain ⟨s, a, hs, hu⟩ := Neighborhood.neighborhood U β (t i) w hi
  refine ⟨s, a, ?_, hs⟩
  change Sieve.generate R (((Functor.inclusion U).map a).left ≫ β)
  rw [← Crystalline.LocalizationLift.liftHom_comp (((Functor.inclusion U).map a).left ≫ β) (t i) hu]
  exact (Sieve.generate R).downward_closed (hgen i)
    (Crystalline.LocalizationLift.liftHom (((Functor.inclusion U).map a).left ≫ β) (t i) hu)

instance toCrystalline_cocontinuous : (toCrystalline U).IsCocontinuous
    (Principal.Topology.topology U.ring) BigCrystallineSite.Object.topology :=
  SiteCocontinuity.cocontinuous_of_generating_pullbacks (toCrystalline U)
    (Principal.Topology.topology U.ring) BigCrystallineSite.Object.precoverage
    (fun R hR β => generator_pullback U R hR β)

instance inclusion_cocontinuous : (Functor.inclusion U).IsCocontinuous
    (Principal.Topology.topology U.ring) (BigCrystallineSite.Object.topology.over U) where
  cover_lift {r S} hS := by
    have h := (toCrystalline U).cover_lift (J := Principal.Topology.topology U.ring)
      (K := BigCrystallineSite.Object.topology) hS
    change ((S.functorPushforward (Over.forget U)).functorPullback
      (Functor.inclusion U ⋙ Over.forget U)) ∈ _ at h
    rw [Sieve.functorPullback_comp, Sieve.functorPullback_functorPushforward_overForget] at h
    exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Cocontinuous
