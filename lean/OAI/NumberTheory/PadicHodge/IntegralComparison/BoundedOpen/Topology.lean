import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology

/-! # Topology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Topology

noncomputable section

/-!
# IntegralComparison: the chart equivalence preserves the actual bounded crystalline topologies
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) [Mono g] (hg : g ≫ fY = f) (n : ℕ)

local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.openFunctor (p := p) (J := J) (δ := δ) g hg n
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Subsite.inclusion (p := p) (J := J) (δ := δ) fY g n
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n
local notation "JX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology (p := p) (J := J) (δ := δ) f n
local notation "JY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology (p := p) (J := J) (δ := δ) fY n
local notation "JO" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Subsite.topology (p := p) (J := J) (δ := δ) fY g n

omit [Mono g] in
theorem coverPreserving : CoverPreserving JX JO E where
  cover_preserve {U S} hS := by
    apply Functor.mem_restrictedTopology_of_functorPushforward_mem
    have he : (S.functorPushforward E).functorPushforward Q = S.functorPushforward F :=
      (Sieve.functorPushforward_comp E Q S).symm
    exact he.symm ▸ (Bounded.PostcomposeTopology.coverPreserving g hg n).cover_preserve hS

instance continuous : (E).IsContinuous JX JO :=
  Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat JO E) (coverPreserving g hg n)

instance cocontinuous : (E).IsCocontinuous JX JO where
  cover_lift {U S} hS := by
    have h := (F).cover_lift JX JY ((CoverPreserving.of_isContinuous Q JO JY).cover_preserve hS)
    have he : (S.functorPushforward Q).functorPullback F = S.functorPullback E := by
      change (S.functorPushforward Q).functorPullback (E ⋙ Q) = _
      rw [Sieve.functorPullback_comp, Sieve.functorPullback_functorPushforward_eq]
    exact he ▸ h

instance dense : (E).IsDenseSubsite JX JO where
  functorPushforward_mem_iff := by
    intro U S
    constructor
    · intro hS
      have h := (E).cover_lift JX JO hS
      change (S.functorPushforward E).functorPullback E ∈ JX U at h
      simpa only [Sieve.functorPullback_functorPushforward_eq] using h
    · exact (coverPreserving g hg n).cover_preserve

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Topology
