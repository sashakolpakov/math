import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationPointEnhancement

/-! # Polarization Point Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationPointComparison

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

namespace StableHilbertPolarizationPointComparison
variable (R : Type) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} n D H) H)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{0} n H ≤ D)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (qR : Spec (.of R) ⟶ Spec (.of ℚ))
    (d : ℕ) (hd : 0 < d) (δ : Fin g → ℕ) (hδ : ∀ k, 0 < δ k)

variable (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m)
    {T : Over (Spec (.of R))} [IsLocallyNoetherian T.left]
    (a : T ⟶ (PolarizationParameter.StableHilbertPolarization.parameter R i j D H hH g Hm Hi N labels qR d hd δ hδ)) (b : T ⟶ (PolarizationParameter.StableHilbertPolarization.parameter R i k D H hH g Hm Hi N labels qR d hd δ hδ))
    (hab : ((a ≫ (PolarizationParameter.StableHilbertPolarization.inclusion R i j D H hH g Hm Hi N labels qR d hd δ hδ)) ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels)) ≫ ChartPullbacks.stableHilbertChartToRank R i j D H =
      ((b ≫ (PolarizationParameter.StableHilbertPolarization.inclusion R i k D H hH g Hm Hi N labels qR d hd δ hδ)) ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels)) ≫ ChartPullbacks.stableHilbertChartToRank R i k D H)

def iso : Moduli.Isomorphisms.LevelPreservingIso (((PolarizationParameter.StableHilbertPolarization.universalFamily R i j D H hH g Hm Hi N labels qR d hd δ hδ)).pullback a.left) (((PolarizationParameter.StableHilbertPolarization.universalFamily R i k D H hH g Hm Hi N labels qR d hd δ hδ)).pullback b.left) :=
  ((PolarizationPointEnhancement.StableHilbertPolarization.pointEnhancementIso R i D H hH g Hm Hi N labels qR d hd δ hδ j a)).trans
    ((PolarizationComparison.StableHilbertPolarizationComparison.enhancementIso R i D H hH hD g Hm Hi N labels d hd δ hδ
      j k (a ≫ (PolarizationParameter.StableHilbertPolarization.inclusion R i j D H hH g Hm Hi N labels qR d hd δ hδ)) (b ≫ (PolarizationParameter.StableHilbertPolarization.inclusion R i k D H hH g Hm Hi N labels qR d hd δ hδ)) hab (PolarizationPointEnhancement.StableHilbertPolarization.pointEnhancement R i D H hH g Hm Hi N labels qR d hd δ hδ j a) (PolarizationPointEnhancement.StableHilbertPolarization.pointEnhancement R i D H hH g Hm Hi N labels qR d hd δ hδ k b)).trans ((PolarizationPointEnhancement.StableHilbertPolarization.pointEnhancementIso R i D H hH g Hm Hi N labels qR d hd δ hδ k b)).symm)

theorem iso_abelian :
    (iso R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k a b hab).abelian =
      ((PolarizationPointEnhancement.StableHilbertPolarization.pointEnhancementIso R i D H hH g Hm Hi N labels qR d hd δ hδ j a)).abelian ≪≫
        LevelComparison.StableHilbertLevelComparison.familyIso R i D H hH hD g Hm Hi N labels j k
          (a ≫ (PolarizationParameter.StableHilbertPolarization.inclusion R i j D H hH g Hm Hi N labels qR d hd δ hδ)) (b ≫ (PolarizationParameter.StableHilbertPolarization.inclusion R i k D H hH g Hm Hi N labels qR d hd δ hδ)) hab ≪≫ ((PolarizationPointEnhancement.StableHilbertPolarization.pointEnhancementIso R i D H hH g Hm Hi N labels qR d hd δ hδ k b)).abelian.symm := by
  exact conjugated_moduli_iso_abelian (PolarizationPointEnhancement.StableHilbertPolarization.pointEnhancementIso R i D H hH g Hm Hi N labels qR d hd δ hδ j a)
    (PolarizationComparison.StableHilbertPolarizationComparison.enhancementIso R i D H hH hD g Hm Hi N labels d hd δ hδ
      j k (a ≫ (PolarizationParameter.StableHilbertPolarization.inclusion R i j D H hH g Hm Hi N labels qR d hd δ hδ)) (b ≫ (PolarizationParameter.StableHilbertPolarization.inclusion R i k D H hH g Hm Hi N labels qR d hd δ hδ)) hab (PolarizationPointEnhancement.StableHilbertPolarization.pointEnhancement R i D H hH g Hm Hi N labels qR d hd δ hδ j a) (PolarizationPointEnhancement.StableHilbertPolarization.pointEnhancement R i D H hH g Hm Hi N labels qR d hd δ hδ k b)) (PolarizationPointEnhancement.StableHilbertPolarization.pointEnhancementIso R i D H hH g Hm Hi N labels qR d hd δ hδ k b) _
    (PolarizationComparison.StableHilbertPolarizationComparison.enhancementIso_abelian R i D H hH hD g Hm Hi N labels d hd δ hδ
      j k (a ≫ (PolarizationParameter.StableHilbertPolarization.inclusion R i j D H hH g Hm Hi N labels qR d hd δ hδ)) (b ≫ (PolarizationParameter.StableHilbertPolarization.inclusion R i k D H hH g Hm Hi N labels qR d hd δ hδ)) hab (PolarizationPointEnhancement.StableHilbertPolarization.pointEnhancement R i D H hH g Hm Hi N labels qR d hd δ hδ j a) (PolarizationPointEnhancement.StableHilbertPolarization.pointEnhancement R i D H hH g Hm Hi N labels qR d hd δ hδ k b))

theorem cocycle (l : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) (c : T ⟶ (PolarizationParameter.StableHilbertPolarization.parameter R i l D H hH g Hm Hi N labels qR d hd δ hδ))
    (hbc : ((b ≫ (PolarizationParameter.StableHilbertPolarization.inclusion R i k D H hH g Hm Hi N labels qR d hd δ hδ)) ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels)) ≫ ChartPullbacks.stableHilbertChartToRank R i k D H =
      ((c ≫ (PolarizationParameter.StableHilbertPolarization.inclusion R i l D H hH g Hm Hi N labels qR d hd δ hδ)) ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i l D H hH g Hm Hi N labels)) ≫ ChartPullbacks.stableHilbertChartToRank R i l D H)
    (hac : ((a ≫ (PolarizationParameter.StableHilbertPolarization.inclusion R i j D H hH g Hm Hi N labels qR d hd δ hδ)) ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels)) ≫ ChartPullbacks.stableHilbertChartToRank R i j D H =
      ((c ≫ (PolarizationParameter.StableHilbertPolarization.inclusion R i l D H hH g Hm Hi N labels qR d hd δ hδ)) ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i l D H hH g Hm Hi N labels)) ≫ ChartPullbacks.stableHilbertChartToRank R i l D H) :
    (iso R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k a b hab).trans
      (iso R i D H hH hD g Hm Hi N labels qR d hd δ hδ k l b c hbc) =
    iso R i D H hH hD g Hm Hi N labels qR d hd δ hδ j l a c hac := by
  apply moduli_cocycle_of_abelian
  exact Affine.IsoCocycleDetection.AffineIsoCocycleDetection.isoCocycle_of_comparisons
    (iso_abelian R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k a b hab)
    (iso_abelian R i D H hH hD g Hm Hi N labels qR d hd δ hδ k l b c hbc)
    (iso_abelian R i D H hH hD g Hm Hi N labels qR d hd δ hδ j l a c hac)
    (conjugated_iso_cocycle ((PolarizationPointEnhancement.StableHilbertPolarization.pointEnhancementIso R i D H hH g Hm Hi N labels qR d hd δ hδ j a)).abelian ((PolarizationPointEnhancement.StableHilbertPolarization.pointEnhancementIso R i D H hH g Hm Hi N labels qR d hd δ hδ k b)).abelian ((PolarizationPointEnhancement.StableHilbertPolarization.pointEnhancementIso R i D H hH g Hm Hi N labels qR d hd δ hδ l c)).abelian
      (LevelComparison.StableHilbertLevelComparison.familyIso_cocycle R i D H hH hD g Hm Hi N labels j k
        (a ≫ (PolarizationParameter.StableHilbertPolarization.inclusion R i j D H hH g Hm Hi N labels qR d hd δ hδ)) (b ≫ (PolarizationParameter.StableHilbertPolarization.inclusion R i k D H hH g Hm Hi N labels qR d hd δ hδ)) hab l (c ≫ (PolarizationParameter.StableHilbertPolarization.inclusion R i l D H hH g Hm Hi N labels qR d hd δ hδ)) hbc hac))

end StableHilbertPolarizationPointComparison

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationPointComparison
