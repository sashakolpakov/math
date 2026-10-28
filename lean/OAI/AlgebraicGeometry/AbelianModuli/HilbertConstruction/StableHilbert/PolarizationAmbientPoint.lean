import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationChartMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.ExistentialComposition

/-! # Polarization Ambient Point -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationAmbientPoint

noncomputable section

/-! The original point of the stable Hilbert intersection is obtained
with both of its projection equations before selecting its map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem eq_originalSquareLift
    {C : Type*} [Category* C] {P X Y Z T : C}
    {l : P ⟶ X} {r : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (sq : IsPullback l r f g) (a : T ⟶ X) (b : T ⟶ Y)
    (hab : a ≫ f = b ≫ g) (e : T ⟶ P)
    (hl : e ≫ l = a) (hr : e ≫ r = b) :
    e = Pullback.ExistentialComposition.isPullbackLiftMap sq a b hab :=
  sq.hom_ext (hl.trans (Pullback.ExistentialComposition.isPullbackLiftMap_fst sq a b hab).symm)
    (hr.trans (Pullback.ExistentialComposition.isPullbackLiftMap_snd sq a b hab).symm)

namespace StableHilbertPolarizationOverlap
variable (R : Type) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} n D H) H)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{0} n H ≤ D)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (qR : Spec (.of R) ⟶ Spec (.of ℚ))
    (d : ℕ) (hd : 0 < d) (δ : Fin g → ℕ) (hδ : ∀ k, 0 < δ k)
    (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m)

theorem ambientRankEquation :
    (pullback.fst ((PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) ≫ (Scheme.stableHilbertChartOver R i D H hH hD j)) (Scheme.stableHilbertChartOver R i D H hH hD k) ≫ (PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ)) ≫ ChartPullbacks.stableHilbertChartToRank R i j D H =
      (pullback.snd ((PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) ≫ (Scheme.stableHilbertChartOver R i D H hH hD j)) (Scheme.stableHilbertChartOver R i D H hH hD k)) ≫ ChartPullbacks.stableHilbertChartToRank R i k D H := by
  have h := congrArg (fun z => z ≫ Scheme.stableHilbertRankParameterOver R i D H hH hD)
    (pullback.condition (f := ((PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) ≫ (Scheme.stableHilbertChartOver R i D H hH hD j))) (g := (Scheme.stableHilbertChartOver R i D H hH hD k)))
  simpa only [Category.assoc, Scheme.stableHilbertChartOver_rankParameter] using h

theorem exists_ambientBasePoint :
    ∃ e : pullback ((PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) ≫ (Scheme.stableHilbertChartOver R i D H hH hD j)) (Scheme.stableHilbertChartOver R i D H hH hD k) ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D H,
      e ≫ (IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD) = (pullback.fst ((PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) ≫ (Scheme.stableHilbertChartOver R i D H hH hD j)) (Scheme.stableHilbertChartOver R i D H hH hD k) ≫ (PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ)) ∧ e ≫ (IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD) = (pullback.snd ((PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) ≫ (Scheme.stableHilbertChartOver R i D H hH hD j)) (Scheme.stableHilbertChartOver R i D H hH hD k)) :=
  (ChartPullbacks.stableHilbertChartIntersection_isPullback R i j k D H hH hD).exists_lift (pullback.fst ((PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) ≫ (Scheme.stableHilbertChartOver R i D H hH hD j)) (Scheme.stableHilbertChartOver R i D H hH hD k) ≫ (PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ)) (pullback.snd ((PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) ≫ (Scheme.stableHilbertChartOver R i D H hH hD j)) (Scheme.stableHilbertChartOver R i D H hH hD k)) (ambientRankEquation (n := n) (m := m) R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k)

def ambientBasePoint := (exists_ambientBasePoint (n := n) (m := m) R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k).choose

theorem ambientBasePoint_left :
    (exists_ambientBasePoint (n := n) (m := m) R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k).choose ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD =
      (pullback.fst ((PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) ≫ (Scheme.stableHilbertChartOver R i D H hH hD j)) (Scheme.stableHilbertChartOver R i D H hH hD k) ≫ (PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ)) := (exists_ambientBasePoint (n := n) (m := m) R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k).choose_spec.1

theorem ambientBasePoint_right :
    (exists_ambientBasePoint (n := n) (m := m) R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k).choose ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD =
      (pullback.snd ((PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) ≫ (Scheme.stableHilbertChartOver R i D H hH hD j)) (Scheme.stableHilbertChartOver R i D H hH hD k)) := (exists_ambientBasePoint (n := n) (m := m) R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k).choose_spec.2

theorem ambientBasePoint_eq_originalLift :
    (exists_ambientBasePoint (n := n) (m := m) R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k).choose =
      Pullback.ExistentialComposition.isPullbackLiftMap (ChartPullbacks.stableHilbertChartIntersection_isPullback R i j k D H hH hD)
        (pullback.fst ((PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) ≫ (Scheme.stableHilbertChartOver R i D H hH hD j)) (Scheme.stableHilbertChartOver R i D H hH hD k) ≫ (PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ)) (pullback.snd ((PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) ≫ (Scheme.stableHilbertChartOver R i D H hH hD j)) (Scheme.stableHilbertChartOver R i D H hH hD k)) (ambientRankEquation (n := n) (m := m) R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k) :=
  eq_originalSquareLift (C := Over (Spec (.of R)))
    (ChartPullbacks.stableHilbertChartIntersection_isPullback R i j k D H hH hD)
    (pullback.fst ((PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) ≫ (Scheme.stableHilbertChartOver R i D H hH hD j)) (Scheme.stableHilbertChartOver R i D H hH hD k) ≫ (PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ))
    (pullback.snd ((PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) ≫ (Scheme.stableHilbertChartOver R i D H hH hD j)) (Scheme.stableHilbertChartOver R i D H hH hD k))
    (ambientRankEquation (n := n) (m := m) R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k)
    (exists_ambientBasePoint (n := n) (m := m) R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k).choose
    (exists_ambientBasePoint (n := n) (m := m) R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k).choose_spec.1
    (exists_ambientBasePoint (n := n) (m := m) R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k).choose_spec.2

end StableHilbertPolarizationOverlap

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationAmbientPoint
