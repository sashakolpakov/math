import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationChartMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationTransitions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.ExistentialComposition

/-! # Polarization Overlap Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationOverlapTransport

noncomputable section

/-! Transport across the original stable Hilbert overlap, first constructed
as an existential map over the actual chart arrows. The chosen map is the
original pullback-tower transport. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def namedPullbackTowerTransportMap
    {C : Type*} [Category* C] [HasPullbacks C]
    {P F H P' F' H' O : C}
    (p : P ⟶ F) (f : F ⟶ H) (l : O ⟶ H)
    (q : P' ⟶ F') (g : F' ⟶ H') (r : O ⟶ H')
    (t : pullback f l ⟶ pullback g r)
    (s : pullback p (pullback.fst f l) ⟶ pullback q (t ≫ pullback.fst g r))
    (a : P ⟶ H) (ha : a = p ≫ f) : pullback a l ⟶ P' := by
  subst a
  exact Pullback.ExistentialComposition.pullbackTowerTransportMap p f l q g r t s

theorem namedPullbackTowerTransportMap_eq_original
    {C : Type*} [Category* C] [HasPullbacks C]
    {P F H P' F' H' O : C}
    (p : P ⟶ F) (f : F ⟶ H) (l : O ⟶ H)
    (q : P' ⟶ F') (g : F' ⟶ H') (r : O ⟶ H')
    (t : pullback f l ⟶ pullback g r)
    (s : pullback p (pullback.fst f l) ⟶ pullback q (t ≫ pullback.fst g r)) :
    namedPullbackTowerTransportMap p f l q g r t s (p ≫ f) rfl =
      Pullback.ExistentialComposition.pullbackTowerTransportMap p f l q g r t s := rfl

private theorem exists_named_pullback_tower_transport
    {C : Type*} [Category* C] [HasPullbacks C]
    {P F H P' F' H' O : C}
    (p : P ⟶ F) (f : F ⟶ H) (l : O ⟶ H)
    (q : P' ⟶ F') (g : F' ⟶ H') (r : O ⟶ H')
    (t : pullback f l ⟶ pullback g r)
    (ht : t ≫ pullback.snd g r = pullback.snd f l)
    (s : pullback p (pullback.fst f l) ⟶ pullback q (t ≫ pullback.fst g r))
    (hs : s ≫ pullback.snd q (t ≫ pullback.fst g r) =
      pullback.snd p (pullback.fst f l))
    (a : P ⟶ H) (b : P' ⟶ H') (ha : a = p ≫ f) (hb : b = q ≫ g) :
    ∃ e : pullback a l ⟶ P', e ≫ b = pullback.snd a l ≫ r := by
  subst a b
  exact ⟨Pullback.ExistentialComposition.pullbackTowerTransportMap p f l q g r t s,
    Pullback.ExistentialComposition.pullback_tower_transport p f l q g r t ht s hs⟩

private theorem choose_named_pullback_tower_transport_eq
    {C : Type*} [Category* C] [HasPullbacks C]
    {P F H P' F' H' O : C}
    (p : P ⟶ F) (f : F ⟶ H) (l : O ⟶ H)
    (q : P' ⟶ F') (g : F' ⟶ H') (r : O ⟶ H')
    (t : pullback f l ⟶ pullback g r)
    (ht : t ≫ pullback.snd g r = pullback.snd f l)
    (s : pullback p (pullback.fst f l) ⟶ pullback q (t ≫ pullback.fst g r))
    (hs : s ≫ pullback.snd q (t ≫ pullback.fst g r) =
      pullback.snd p (pullback.fst f l))
    (a : P ⟶ H) (b : P' ⟶ H') (ha : a = p ≫ f) (hb : b = q ≫ g)
    [Mono b] (h : ∃ e : pullback a l ⟶ P', e ≫ b = pullback.snd a l ≫ r) :
    h.choose = namedPullbackTowerTransportMap p f l q g r t s a ha := by
  subst a b
  exact (cancel_mono (q ≫ g)).mp
    (h.choose_spec.trans (Pullback.ExistentialComposition.pullback_tower_transport p f l q g r t ht s hs).symm)

namespace StableHilbertPolarizationOverlapTransport
variable (R : Type) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} n D H) H)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{0} n H ≤ D)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (qR : Spec (.of R) ⟶ Spec (.of ℚ))
    (d : ℕ) (hd : 0 < d) (δ : Fin g → ℕ) (hδ : ∀ k, 0 < δ k)
    (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m)

theorem exists_transport_toHilbert :
    ∃ e : pullback
        (PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ)
        (IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD) ⟶
      PolarizationParameter.StableHilbertPolarization.parameter R i k D H hH g Hm Hi N labels qR d hd δ hδ,
      e ≫ PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i k D H hH g Hm Hi N labels qR d hd δ hδ =
        pullback.snd
          (PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ)
          (IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD) ≫
            IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD :=
  exists_named_pullback_tower_transport (C := Over (Spec (.of R)))
    (PolarizationParameter.StableHilbertPolarization.inclusion R i j D H hH g Hm Hi N labels qR d hd δ hδ)
    (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels)
    (IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD)
    (PolarizationParameter.StableHilbertPolarization.inclusion R i k D H hH g Hm Hi N labels qR d hd δ hδ)
    (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels)
    (IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD)
    (LevelTransitions.StableHilbertFullLevelTransition.forward (n := n) (m := m) R i D H hH hD g Hm Hi N labels j k)
    (LevelTransitions.StableHilbertFullLevelTransition.forward_base (n := n) (m := m) R i D H hH hD g Hm Hi N labels j k)
    (PolarizationTransitions.StableHilbertPolarizationTransition.forward (n := n) (m := m) R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k)
    (PolarizationTransitions.StableHilbertPolarizationTransition.forward_base (n := n) (m := m) R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k)
    (PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ)
    (PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i k D H hH g Hm Hi N labels qR d hd δ hδ)
    rfl rfl

def transport :=
  (exists_transport_toHilbert (n := n) (m := m) R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k).choose

theorem transport_toHilbert :
    (exists_transport_toHilbert (n := n) (m := m) R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k).choose ≫ (PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i k D H hH g Hm Hi N labels qR d hd δ hδ) =
      pullback.snd (PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) (IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD) ≫ (IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD) :=
  (exists_transport_toHilbert (n := n) (m := m) R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k).choose_spec

theorem transport_eq_original :
    (exists_transport_toHilbert (n := n) (m := m) R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k).choose =
      namedPullbackTowerTransportMap (C := Over (Spec (.of R)))
        (PolarizationParameter.StableHilbertPolarization.inclusion R i j D H hH g Hm Hi N labels qR d hd δ hδ) (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels) (IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD)
        (PolarizationParameter.StableHilbertPolarization.inclusion R i k D H hH g Hm Hi N labels qR d hd δ hδ) (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels) (IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD)
        (LevelTransitions.StableHilbertFullLevelTransition.forward (n := n) (m := m) R i D H hH hD g Hm Hi N labels j k) (PolarizationTransitions.StableHilbertPolarizationTransition.forward (n := n) (m := m) R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k) (PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) rfl :=
  choose_named_pullback_tower_transport_eq (C := Over (Spec (.of R)))
    (PolarizationParameter.StableHilbertPolarization.inclusion R i j D H hH g Hm Hi N labels qR d hd δ hδ)
    (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels)
    (IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD)
    (PolarizationParameter.StableHilbertPolarization.inclusion R i k D H hH g Hm Hi N labels qR d hd δ hδ)
    (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels)
    (IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD)
    (LevelTransitions.StableHilbertFullLevelTransition.forward (n := n) (m := m) R i D H hH hD g Hm Hi N labels j k)
    (LevelTransitions.StableHilbertFullLevelTransition.forward_base (n := n) (m := m) R i D H hH hD g Hm Hi N labels j k)
    (PolarizationTransitions.StableHilbertPolarizationTransition.forward (n := n) (m := m) R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k)
    (PolarizationTransitions.StableHilbertPolarizationTransition.forward_base (n := n) (m := m) R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k)
    (PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ)
    (PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i k D H hH g Hm Hi N labels qR d hd δ hδ)
    rfl rfl
    (exists_transport_toHilbert (n := n) (m := m) R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k)

end StableHilbertPolarizationOverlapTransport

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationOverlapTransport
