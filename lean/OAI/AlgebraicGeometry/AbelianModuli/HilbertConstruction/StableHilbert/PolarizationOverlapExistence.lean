import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationOverlapTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationAmbientPoint
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.ExistentialComposition

/-! # Polarization Overlap Existence -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationOverlapExistence.StableHilbertPolarizationOverlap

/-! The constructed full-level and polarization transitions give an
actual lift of the polarization chart over every original stable
Hilbert overlap. The two component constructions retain their proved
identities with the original pullback maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} n D H) H)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{0} n H ≤ D)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (qR : Spec (.of R) ⟶ Spec (.of ℚ))
    (d : ℕ) (hd : 0 < d) (δ : Fin g → ℕ) (hδ : ∀ k, 0 < δ k)
    (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m)

abbrev transport :=
  PolarizationOverlapTransport.StableHilbertPolarizationOverlapTransport.transport (n := n) (m := m) R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k

export PolarizationOverlapTransport.StableHilbertPolarizationOverlapTransport
  (transport_toHilbert transport_eq_original)

/-- The original intersection point and original transport give the
complete chart lift on the actual ambient open intersection. -/
def ambientLift : pullback ((PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) ≫ (Scheme.stableHilbertChartOver R i D H hH hD j)) (Scheme.stableHilbertChartOver R i D H hH hD k) ⟶
    PolarizationParameter.StableHilbertPolarization.parameter R i k D H hH g Hm Hi N labels qR d hd δ hδ :=
  Pullback.ExistentialComposition.composeExistentialPullbackLifts (C := Over (Spec (.of R)))
    (PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ)
    (IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD)
    (IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD)
    (PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i k D H hH g Hm Hi N labels qR d hd δ hδ)
    (pullback.fst ((PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) ≫ (Scheme.stableHilbertChartOver R i D H hH hD j)) (Scheme.stableHilbertChartOver R i D H hH hD k))
    (pullback.snd ((PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) ≫ (Scheme.stableHilbertChartOver R i D H hH hD j)) (Scheme.stableHilbertChartOver R i D H hH hD k))
    (PolarizationAmbientPoint.StableHilbertPolarizationOverlap.exists_ambientBasePoint (n := n) (m := m) R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k)
    (PolarizationOverlapTransport.StableHilbertPolarizationOverlapTransport.exists_transport_toHilbert (n := n) (m := m) R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k)

theorem ambientLift_toHilbert :
    (Pullback.ExistentialComposition.composeExistentialPullbackLifts (C := Over (Spec (.of R)))
    (PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ)
    (IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD)
    (IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD)
    (PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i k D H hH g Hm Hi N labels qR d hd δ hδ)
    (pullback.fst ((PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) ≫ (Scheme.stableHilbertChartOver R i D H hH hD j)) (Scheme.stableHilbertChartOver R i D H hH hD k))
    (pullback.snd ((PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) ≫ (Scheme.stableHilbertChartOver R i D H hH hD j)) (Scheme.stableHilbertChartOver R i D H hH hD k))
    (PolarizationAmbientPoint.StableHilbertPolarizationOverlap.exists_ambientBasePoint (n := n) (m := m) R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k)
    (PolarizationOverlapTransport.StableHilbertPolarizationOverlapTransport.exists_transport_toHilbert (n := n) (m := m) R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k)) ≫
      (PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i k D H hH g Hm Hi N labels qR d hd δ hδ) =
        (pullback.snd ((PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) ≫ (Scheme.stableHilbertChartOver R i D H hH hD j)) (Scheme.stableHilbertChartOver R i D H hH hD k)) :=
  Pullback.ExistentialComposition.composeExistentialPullbackLifts_over (C := Over (Spec (.of R)))
    (PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ)
    (IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD)
    (IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD)
    (PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i k D H hH g Hm Hi N labels qR d hd δ hδ)
    (pullback.fst ((PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) ≫ (Scheme.stableHilbertChartOver R i D H hH hD j)) (Scheme.stableHilbertChartOver R i D H hH hD k))
    (pullback.snd ((PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) ≫ (Scheme.stableHilbertChartOver R i D H hH hD j)) (Scheme.stableHilbertChartOver R i D H hH hD k))
    (PolarizationAmbientPoint.StableHilbertPolarizationOverlap.exists_ambientBasePoint (n := n) (m := m) R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k)
    (PolarizationOverlapTransport.StableHilbertPolarizationOverlapTransport.exists_transport_toHilbert (n := n) (m := m) R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k)

end AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationOverlapExistence.StableHilbertPolarizationOverlap

namespace AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationOverlapExistence

/-! The complete native overlap lift, packaged as an existential
before the monomorphic chart record is specialized. Its chosen witness
is the exact previously constructed composition. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem exists_composedOverlapLift
    {C : Type*} [Category* C] [HasPullbacks C] {X B O Y T Z : C}
    (a : X ⟶ B) (l : O ⟶ B) (r : O ⟶ Z) (k : Y ⟶ Z)
    (p : T ⟶ X) (q : T ⟶ Z)
    (hb : ∃ b : T ⟶ O, b ≫ l = p ≫ a ∧ b ≫ r = q)
    (ht : ∃ t : pullback a l ⟶ Y, t ≫ k = pullback.snd a l ≫ r) :
    ∃ e : T ⟶ Y, e ≫ k = q :=
  ⟨Pullback.ExistentialComposition.composeExistentialPullbackLifts a l r k p q hb ht,
    Pullback.ExistentialComposition.composeExistentialPullbackLifts_over a l r k p q hb ht⟩

private theorem chosen_composedOverlapLift_eq
    {C : Type*} [Category* C] [HasPullbacks C] {X B O Y T Z : C}
    (a : X ⟶ B) (l : O ⟶ B) (r : O ⟶ Z) (k : Y ⟶ Z)
    (p : T ⟶ X) (q : T ⟶ Z)
    (hb : ∃ b : T ⟶ O, b ≫ l = p ≫ a ∧ b ≫ r = q)
    (ht : ∃ t : pullback a l ⟶ Y, t ≫ k = pullback.snd a l ≫ r)
    [Mono k] (he : ∃ e : T ⟶ Y, e ≫ k = q) :
    he.choose = Pullback.ExistentialComposition.composeExistentialPullbackLifts a l r k p q hb ht :=
  (cancel_mono k).mp
    (he.choose_spec.trans (Pullback.ExistentialComposition.composeExistentialPullbackLifts_over a l r k p q hb ht).symm)

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

theorem exists_ambientLift :
    ∃ e : pullback ((PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) ≫ (Scheme.stableHilbertChartOver R i D H hH hD j)) (Scheme.stableHilbertChartOver R i D H hH hD k) ⟶
      PolarizationParameter.StableHilbertPolarization.parameter R i k D H hH g Hm Hi N labels qR d hd δ hδ,
      e ≫ (PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i k D H hH g Hm Hi N labels qR d hd δ hδ) = (pullback.snd ((PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) ≫ (Scheme.stableHilbertChartOver R i D H hH hD j)) (Scheme.stableHilbertChartOver R i D H hH hD k)) :=
  exists_composedOverlapLift (C := Over (Spec (.of R)))
    (PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ)
    (IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD)
    (IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD)
    (PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i k D H hH g Hm Hi N labels qR d hd δ hδ)
    (pullback.fst ((PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) ≫ (Scheme.stableHilbertChartOver R i D H hH hD j)) (Scheme.stableHilbertChartOver R i D H hH hD k))
    (pullback.snd ((PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) ≫ (Scheme.stableHilbertChartOver R i D H hH hD j)) (Scheme.stableHilbertChartOver R i D H hH hD k))
    (PolarizationAmbientPoint.StableHilbertPolarizationOverlap.exists_ambientBasePoint (n := n) (m := m) R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k)
    (PolarizationOverlapTransport.StableHilbertPolarizationOverlapTransport.exists_transport_toHilbert (n := n) (m := m) R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k)

/-- The selected overlap map equals the original composition of the
original intersection lift and the original polarization transport. -/
theorem chosen_ambientLift_eq_original :
    (exists_ambientLift (n := n) (m := m) R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k).choose =
      Pullback.ExistentialComposition.composeExistentialPullbackLifts (C := Over (Spec (.of R)))
    (PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ)
    (IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD)
    (IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD)
    (PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i k D H hH g Hm Hi N labels qR d hd δ hδ)
    (pullback.fst ((PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) ≫ (Scheme.stableHilbertChartOver R i D H hH hD j)) (Scheme.stableHilbertChartOver R i D H hH hD k))
    (pullback.snd ((PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) ≫ (Scheme.stableHilbertChartOver R i D H hH hD j)) (Scheme.stableHilbertChartOver R i D H hH hD k))
    (PolarizationAmbientPoint.StableHilbertPolarizationOverlap.exists_ambientBasePoint (n := n) (m := m) R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k)
    (PolarizationOverlapTransport.StableHilbertPolarizationOverlapTransport.exists_transport_toHilbert (n := n) (m := m) R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k) :=
  chosen_composedOverlapLift_eq (C := Over (Spec (.of R)))
    (PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ)
    (IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD)
    (IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD)
    (PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i k D H hH g Hm Hi N labels qR d hd δ hδ)
    (pullback.fst ((PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) ≫ (Scheme.stableHilbertChartOver R i D H hH hD j)) (Scheme.stableHilbertChartOver R i D H hH hD k))
    (pullback.snd ((PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) ≫ (Scheme.stableHilbertChartOver R i D H hH hD j)) (Scheme.stableHilbertChartOver R i D H hH hD k))
    (PolarizationAmbientPoint.StableHilbertPolarizationOverlap.exists_ambientBasePoint (n := n) (m := m) R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k)
    (PolarizationOverlapTransport.StableHilbertPolarizationOverlapTransport.exists_transport_toHilbert (n := n) (m := m) R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k)
    (exists_ambientLift (n := n) (m := m) R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k)

end StableHilbertPolarizationOverlap

end AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationOverlapExistence

end

end OAI
