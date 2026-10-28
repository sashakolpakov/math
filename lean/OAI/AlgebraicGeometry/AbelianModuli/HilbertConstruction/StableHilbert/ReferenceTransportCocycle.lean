import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelReferenceTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.FamilyTransportLaws

/-! # Reference Transport Cocycle -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.ReferenceTransportCocycle

noncomputable section

/-! Cocycle laws for the same original-family comparisons used by the
full-level chart transitions. These are identities on arbitrary tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

private theorem recovered_cocycle {C : Type*} [Category* C]
    {U V W A B D X Y Z : C}
    (r : U ≅ A) (s : V ≅ B) (t : W ≅ D)
    (a : U ≅ X) (b : V ≅ Y) (c : W ≅ Z)
    (e : X ≅ Y) (f : Y ≅ Z) (g : X ≅ Z) (h : e ≪≫ f = g) :
    (r.symm ≪≫ a ≪≫ e ≪≫ b.symm ≪≫ s) ≪≫
      (s.symm ≪≫ b ≪≫ f ≪≫ c.symm ≪≫ t) =
    r.symm ≪≫ a ≪≫ g ≪≫ c.symm ≪≫ t := by
  rw [← h]
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc, Iso.symm_self_id_assoc]

private theorem conjugated_cocycle {C : Type*} [Category* C]
    {A B D X Y Z : C} (a : A ≅ X) (b : B ≅ Y) (c : D ≅ Z)
    (e : X ≅ Y) (f : Y ≅ Z) (g : X ≅ Z) (h : e ≪≫ f = g) :
    (a ≪≫ e ≪≫ b.symm) ≪≫ (b ≪≫ f ≪≫ c.symm) = a ≪≫ g ≪≫ c.symm := by
  rw [← h]
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]

variable (R : Type u) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D H) H)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n H ≤ D)
    (j k l : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    {T : Over (Spec (.of R))}
    (a : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)
    (b : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i k D H)
    (c : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i l D H)
    (hab : a ≫ ChartPullbacks.stableHilbertChartToRank R i j D H = b ≫ ChartPullbacks.stableHilbertChartToRank R i k D H)
    (hbc : b ≫ ChartPullbacks.stableHilbertChartToRank R i k D H = c ≫ ChartPullbacks.stableHilbertChartToRank R i l D H)
    (hac : a ≫ ChartPullbacks.stableHilbertChartToRank R i j D H = c ≫ ChartPullbacks.stableHilbertChartToRank R i l D H)

theorem stableHilbertOriginalFamilyTransport_cocycle :
    ReferenceFamilyTransport.stableHilbertOriginalFamilyTransport R i D H hH hD j k a b hab ≪≫
      ReferenceFamilyTransport.stableHilbertOriginalFamilyTransport R i D H hH hD k l b c hbc =
    ReferenceFamilyTransport.stableHilbertOriginalFamilyTransport R i D H hH hD j l a c hac := by
  let X := HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n
  exact recovered_cocycle
    (ClassifyingMap.stableConfigurationHilbertNativePullbackRecovery R i j D H hH a)
    (ClassifyingMap.stableConfigurationHilbertNativePullbackRecovery R i k D H hH b)
    (ClassifyingMap.stableConfigurationHilbertNativePullbackRecovery R i l D H hH c)
    (Intrinsic.FamilyPullbackIso.nativeFamilyPullbackIso X a (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D H))
    (Intrinsic.FamilyPullbackIso.nativeFamilyPullbackIso X b (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i k D H))
    (Intrinsic.FamilyPullbackIso.nativeFamilyPullbackIso X c (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i l D H))
    (FamilyTransport.stableHilbertFamilyTransport R i D H hH hD j k a b hab)
    (FamilyTransport.stableHilbertFamilyTransport R i D H hH hD k l b c hbc)
    (FamilyTransport.stableHilbertFamilyTransport R i D H hH hD j l a c hac)
    (FamilyTransportLaws.stableHilbertFamilyTransport_cocycle R i D H hH hD j k l a b c hab hbc hac)

namespace StableHilbertFullLevelOriginalTransport
variable (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (x y z : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter (Spec (.of R)) n H g Hm Hi N)
    (hx : x ≫ HilbertLevel.PullbackParameter.HilbertLevelPullback.forget (Spec (.of R)) n H g Hm Hi N =
      a ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH)
    (hy : y ≫ HilbertLevel.PullbackParameter.HilbertLevelPullback.forget (Spec (.of R)) n H g Hm Hi N =
      b ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i k D H hH)
    (hz : z ≫ HilbertLevel.PullbackParameter.HilbertLevelPullback.forget (Spec (.of R)) n H g Hm Hi N =
      c ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i l D H hH)

theorem cocycle :
    LevelReferenceTransport.StableHilbertFullLevelOriginalTransport.iso R i D H hH hD g Hm Hi N j k a b hab x hx y hy ≪≫
      LevelReferenceTransport.StableHilbertFullLevelOriginalTransport.iso R i D H hH hD g Hm Hi N k l b c hbc y hy z hz =
    LevelReferenceTransport.StableHilbertFullLevelOriginalTransport.iso R i D H hH hD g Hm Hi N j l a c hac x hx z hz := by
  exact conjugated_cocycle
    (HilbertLevel.PointNaturality.HilbertLevelPullback.pointHilbertIso (Spec (.of R)) n H g Hm Hi N x
      (a ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH) hx)
    (HilbertLevel.PointNaturality.HilbertLevelPullback.pointHilbertIso (Spec (.of R)) n H g Hm Hi N y
      (b ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i k D H hH) hy)
    (HilbertLevel.PointNaturality.HilbertLevelPullback.pointHilbertIso (Spec (.of R)) n H g Hm Hi N z
      (c ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i l D H hH) hz)
    (ReferenceFamilyTransport.stableHilbertOriginalFamilyTransport R i D H hH hD j k a b hab)
    (ReferenceFamilyTransport.stableHilbertOriginalFamilyTransport R i D H hH hD k l b c hbc)
    (ReferenceFamilyTransport.stableHilbertOriginalFamilyTransport R i D H hH hD j l a c hac)
    (stableHilbertOriginalFamilyTransport_cocycle R i D H hH hD j k l a b c hab hbc hac)

end StableHilbertFullLevelOriginalTransport

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.ReferenceTransportCocycle
