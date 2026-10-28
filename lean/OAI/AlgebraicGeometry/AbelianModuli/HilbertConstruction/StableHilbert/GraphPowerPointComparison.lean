import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerParameter

/-! # Graph Power Point Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerPointComparison

noncomputable section

/-! The polarized comparisons on actual points of the constructed
stable polarization loci, with their full cocycle. The comparison uses
the existing universal enhancements and original universal families. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

private theorem conjugated_moduli_iso_abelian
    {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
    {A B C D : PolarizationData.PolarizedAbelianWithFullLevel g δ N S}
    (r : Moduli.Isomorphisms.LevelPreservingIso A B) (e : Moduli.Isomorphisms.LevelPreservingIso B C) (s : Moduli.Isomorphisms.LevelPreservingIso D C)
    (f : B.abelian.scheme ≅ C.abelian.scheme) (he : e.abelian = f) :
    (r.trans (e.trans s.symm)).abelian = r.abelian ≪≫ f ≪≫ s.abelian.symm :=
  congrArg (fun q => r.abelian ≪≫ q ≪≫ s.abelian.symm) he

private theorem conjugated_iso_cocycle {C : Type*} [Category* C]
    {A B D X Y Z : C} (a : A ≅ X) (b : B ≅ Y) (c : D ≅ Z)
    {e : X ≅ Y} {f : Y ≅ Z} {g : X ≅ Z} (h : e ≪≫ f = g) :
    (a ≪≫ e ≪≫ b.symm) ≪≫ (b ≪≫ f ≪≫ c.symm) = a ≪≫ g ≪≫ c.symm := by
  rw [← h]
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]

private theorem moduli_cocycle_of_abelian
    {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
    {A B C : PolarizationData.PolarizedAbelianWithFullLevel g δ N S}
    (e : Moduli.Isomorphisms.LevelPreservingIso A B) (f : Moduli.Isomorphisms.LevelPreservingIso B C) (q : Moduli.Isomorphisms.LevelPreservingIso A C)
    (h : e.abelian ≪≫ f.abelian = q.abelian) : e.trans f = q :=
  Moduli.Isomorphisms.LevelPreservingIso.ext_abelian _ _ (congrArg Iso.hom h)

namespace StableHilbertGraphPowerPointComparison
variable (R : Type) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} n D H) H)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{0} n H ≤ D)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (d : ℕ) (δ : Fin g → ℕ) (Φ : GraphPower.LocusPresentation.GraphPowerLocusFactory R g N d δ)
    (hd : 0 < d) (hδ : ∀ k, 0 < δ k)

variable (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m)
    {T : Over (Spec (.of R))} [IsLocallyNoetherian T.left]
    (a : T ⟶ (GraphPowerParameter.StableHilbertGraphPower.parameter R i j D H hH g Hm Hi N labels d δ Φ)) (b : T ⟶ (GraphPowerParameter.StableHilbertGraphPower.parameter R i k D H hH g Hm Hi N labels d δ Φ))
    (hab : ((a ≫ (GraphPowerParameter.StableHilbertGraphPower.inclusion R i j D H hH g Hm Hi N labels d δ Φ)) ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels)) ≫ ChartPullbacks.stableHilbertChartToRank R i j D H =
      ((b ≫ (GraphPowerParameter.StableHilbertGraphPower.inclusion R i k D H hH g Hm Hi N labels d δ Φ)) ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels)) ≫ ChartPullbacks.stableHilbertChartToRank R i k D H)

def iso : Moduli.Isomorphisms.LevelPreservingIso (((GraphPowerParameter.StableHilbertGraphPower.universalFamily R i j D H hH g Hm Hi N labels d δ Φ)).pullback a.left) (((GraphPowerParameter.StableHilbertGraphPower.universalFamily R i k D H hH g Hm Hi N labels d δ Φ)).pullback b.left) :=
  ((GraphPowerParameter.StableHilbertGraphPower.pointEnhancementIso R i j D H hH g Hm Hi N labels d δ Φ a)).trans
    ((PolarizationComparison.StableHilbertPolarizationComparison.enhancementIso R i D H hH hD g Hm Hi N labels d hd δ hδ
      j k (a ≫ (GraphPowerParameter.StableHilbertGraphPower.inclusion R i j D H hH g Hm Hi N labels d δ Φ)) (b ≫ (GraphPowerParameter.StableHilbertGraphPower.inclusion R i k D H hH g Hm Hi N labels d δ Φ)) hab (GraphPowerParameter.StableHilbertGraphPower.pointEnhancement R i j D H hH g Hm Hi N labels d δ Φ a) (GraphPowerParameter.StableHilbertGraphPower.pointEnhancement R i k D H hH g Hm Hi N labels d δ Φ b)).trans ((GraphPowerParameter.StableHilbertGraphPower.pointEnhancementIso R i k D H hH g Hm Hi N labels d δ Φ b)).symm)

theorem iso_abelian :
    (iso R i D H hH hD g Hm Hi N labels d δ Φ hd hδ j k a b hab).abelian =
      ((GraphPowerParameter.StableHilbertGraphPower.pointEnhancementIso R i j D H hH g Hm Hi N labels d δ Φ a)).abelian ≪≫
        LevelComparison.StableHilbertLevelComparison.familyIso R i D H hH hD g Hm Hi N labels j k
          (a ≫ (GraphPowerParameter.StableHilbertGraphPower.inclusion R i j D H hH g Hm Hi N labels d δ Φ)) (b ≫ (GraphPowerParameter.StableHilbertGraphPower.inclusion R i k D H hH g Hm Hi N labels d δ Φ)) hab ≪≫ ((GraphPowerParameter.StableHilbertGraphPower.pointEnhancementIso R i k D H hH g Hm Hi N labels d δ Φ b)).abelian.symm := by
  exact conjugated_moduli_iso_abelian (GraphPowerParameter.StableHilbertGraphPower.pointEnhancementIso R i j D H hH g Hm Hi N labels d δ Φ a)
    (PolarizationComparison.StableHilbertPolarizationComparison.enhancementIso R i D H hH hD g Hm Hi N labels d hd δ hδ
      j k (a ≫ (GraphPowerParameter.StableHilbertGraphPower.inclusion R i j D H hH g Hm Hi N labels d δ Φ)) (b ≫ (GraphPowerParameter.StableHilbertGraphPower.inclusion R i k D H hH g Hm Hi N labels d δ Φ)) hab (GraphPowerParameter.StableHilbertGraphPower.pointEnhancement R i j D H hH g Hm Hi N labels d δ Φ a) (GraphPowerParameter.StableHilbertGraphPower.pointEnhancement R i k D H hH g Hm Hi N labels d δ Φ b)) (GraphPowerParameter.StableHilbertGraphPower.pointEnhancementIso R i k D H hH g Hm Hi N labels d δ Φ b) _
    (PolarizationComparison.StableHilbertPolarizationComparison.enhancementIso_abelian R i D H hH hD g Hm Hi N labels d hd δ hδ
      j k (a ≫ (GraphPowerParameter.StableHilbertGraphPower.inclusion R i j D H hH g Hm Hi N labels d δ Φ)) (b ≫ (GraphPowerParameter.StableHilbertGraphPower.inclusion R i k D H hH g Hm Hi N labels d δ Φ)) hab (GraphPowerParameter.StableHilbertGraphPower.pointEnhancement R i j D H hH g Hm Hi N labels d δ Φ a) (GraphPowerParameter.StableHilbertGraphPower.pointEnhancement R i k D H hH g Hm Hi N labels d δ Φ b))

theorem cocycle (l : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) (c : T ⟶ (GraphPowerParameter.StableHilbertGraphPower.parameter R i l D H hH g Hm Hi N labels d δ Φ))
    (hbc : ((b ≫ (GraphPowerParameter.StableHilbertGraphPower.inclusion R i k D H hH g Hm Hi N labels d δ Φ)) ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels)) ≫ ChartPullbacks.stableHilbertChartToRank R i k D H =
      ((c ≫ (GraphPowerParameter.StableHilbertGraphPower.inclusion R i l D H hH g Hm Hi N labels d δ Φ)) ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i l D H hH g Hm Hi N labels)) ≫ ChartPullbacks.stableHilbertChartToRank R i l D H)
    (hac : ((a ≫ (GraphPowerParameter.StableHilbertGraphPower.inclusion R i j D H hH g Hm Hi N labels d δ Φ)) ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels)) ≫ ChartPullbacks.stableHilbertChartToRank R i j D H =
      ((c ≫ (GraphPowerParameter.StableHilbertGraphPower.inclusion R i l D H hH g Hm Hi N labels d δ Φ)) ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i l D H hH g Hm Hi N labels)) ≫ ChartPullbacks.stableHilbertChartToRank R i l D H) :
    (iso R i D H hH hD g Hm Hi N labels d δ Φ hd hδ j k a b hab).trans
      (iso R i D H hH hD g Hm Hi N labels d δ Φ hd hδ k l b c hbc) =
    iso R i D H hH hD g Hm Hi N labels d δ Φ hd hδ j l a c hac := by
  apply moduli_cocycle_of_abelian
  exact Affine.IsoCocycleDetection.AffineIsoCocycleDetection.isoCocycle_of_comparisons
    (iso_abelian R i D H hH hD g Hm Hi N labels d δ Φ hd hδ j k a b hab)
    (iso_abelian R i D H hH hD g Hm Hi N labels d δ Φ hd hδ k l b c hbc)
    (iso_abelian R i D H hH hD g Hm Hi N labels d δ Φ hd hδ j l a c hac)
    (conjugated_iso_cocycle ((GraphPowerParameter.StableHilbertGraphPower.pointEnhancementIso R i j D H hH g Hm Hi N labels d δ Φ a)).abelian ((GraphPowerParameter.StableHilbertGraphPower.pointEnhancementIso R i k D H hH g Hm Hi N labels d δ Φ b)).abelian ((GraphPowerParameter.StableHilbertGraphPower.pointEnhancementIso R i l D H hH g Hm Hi N labels d δ Φ c)).abelian
      (LevelComparison.StableHilbertLevelComparison.familyIso_cocycle R i D H hH hD g Hm Hi N labels j k
        (a ≫ (GraphPowerParameter.StableHilbertGraphPower.inclusion R i j D H hH g Hm Hi N labels d δ Φ)) (b ≫ (GraphPowerParameter.StableHilbertGraphPower.inclusion R i k D H hH g Hm Hi N labels d δ Φ)) hab l (c ≫ (GraphPowerParameter.StableHilbertGraphPower.inclusion R i l D H hH g Hm Hi N labels d δ Φ)) hbc hac))

end StableHilbertGraphPowerPointComparison

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerPointComparison
