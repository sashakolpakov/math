import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.EnhancementFamilyComparison

/-! # Polarization Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationComparison.StableHilbertPolarizationComparison

noncomputable section

/-! Canonical polarization-compatible comparisons of the actual stable
full-level chart families. The normalized Hilbert line is preserved by
the proved family comparison; graph-power uniqueness supplies the dual
and polarization maps and the full cocycle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

private theorem moduli_cocycle_of_comparisons
    {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
    {A B C : PolarizationData.PolarizedAbelianWithFullLevel g δ N S}
    (r : Moduli.Isomorphisms.LevelPreservingIso A B) (s : Moduli.Isomorphisms.LevelPreservingIso B C) (t : Moduli.Isomorphisms.LevelPreservingIso A C)
    (a : A.abelian.scheme ≅ B.abelian.scheme)
    (b : B.abelian.scheme ≅ C.abelian.scheme)
    (c : A.abelian.scheme ≅ C.abelian.scheme)
    (hr : r.abelian = a) (hs : s.abelian = b) (ht : t.abelian = c)
    (h : a ≪≫ b = c) : r.trans s = t := by
  apply Moduli.Isomorphisms.LevelPreservingIso.ext_abelian
  exact congrArg Iso.hom
    (((congrArg₂ (fun x y => x ≪≫ y) hr hs).trans h).trans ht.symm)

variable (R : Type u) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D H) H)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n H ≤ D)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (d : ℕ) (hd : 0 < d) (δ : Fin g → ℕ) (hδ : ∀ i, 0 < δ i)

variable (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    {T : Over (Spec (.of R))} [IsLocallyNoetherian T.left]
    (a : T ⟶ (LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels)) (b : T ⟶ (LevelParameter.StableHilbertLevel.parameter R i k D H hH g Hm Hi N labels))
    (hab : (a ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels)) ≫ ChartPullbacks.stableHilbertChartToRank R i j D H =
      (b ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels)) ≫ ChartPullbacks.stableHilbertChartToRank R i k D H)
    (E : GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ (LevelComparison.StableHilbertLevelComparison.familyAt R i D H hH g Hm Hi N labels j a) (LevelComparison.StableHilbertLevelComparison.lineAt R i D H hH g Hm Hi N labels j a) d)
    (F : GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ (LevelComparison.StableHilbertLevelComparison.familyAt R i D H hH g Hm Hi N labels k b) (LevelComparison.StableHilbertLevelComparison.lineAt R i D H hH g Hm Hi N labels k b) d)

def enhancementIso : Moduli.Isomorphisms.LevelPreservingIso E.object F.object :=
  @GraphPower.EnhancementFamilyComparison.GraphPowerEnhancementFamilyComparison.iso _ _ _ g N δ
    (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (.of R)) n H g Hm Hi N)
    (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (.of R)) n H g Hm Hi N)
    (b ≫ (LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels)).left (LevelComparison.StableHilbertLevelComparison.familyAt R i D H hH g Hm Hi N labels j a) (LevelComparison.StableHilbertLevelComparison.familyAt R i D H hH g Hm Hi N labels k b)
    (LevelPointFamilyIso.StableHilbertLevel.pointFamilyIso R i k D H hH g Hm Hi N labels b).symm
    (Level.IsoConjugation.isoSymm_isMonHom
      (hE := LevelFamilyComparison.StableHilbertLevel.pointFamilyIso_isMonHom R i k D H hH g Hm Hi N labels b)
      (LevelPointFamilyIso.StableHilbertLevel.pointFamilyIso R i k D H hH g Hm Hi N labels b))
    (LevelComparison.StableHilbertLevelComparison.lineAt R i D H hH g Hm Hi N labels j a) (LevelComparison.StableHilbertLevelComparison.lineAt R i D H hH g Hm Hi N labels k b) d
    (LevelComparison.StableHilbertLevelComparison.familyIso R i D H hH hD g Hm Hi N labels j k a b hab)
    (LevelComparison.StableHilbertLevelComparison.familyIso_isMonHom R i D H hH hD g Hm Hi N labels j k a b hab)
    (LevelComparison.StableHilbertLevelComparison.familyIso_line R i D H hH hD g Hm Hi N labels j k a b hab)
    (LevelComparison.StableHilbertLevelComparison.familyIso_level R i D H hH hD g Hm Hi N labels j k a b hab)
    E F hδ hd

theorem enhancementIso_abelian :
    (enhancementIso R i D H hH hD g Hm Hi N labels d hd δ hδ j k a b hab E F).abelian =
      LevelComparison.StableHilbertLevelComparison.familyIso R i D H hH hD g Hm Hi N labels j k a b hab :=
  @GraphPower.EnhancementFamilyComparison.GraphPowerEnhancementFamilyComparison.iso_abelian _ _ _ g N δ
    (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (.of R)) n H g Hm Hi N)
    (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (.of R)) n H g Hm Hi N)
    (b ≫ (LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels)).left (LevelComparison.StableHilbertLevelComparison.familyAt R i D H hH g Hm Hi N labels j a) (LevelComparison.StableHilbertLevelComparison.familyAt R i D H hH g Hm Hi N labels k b)
    (LevelPointFamilyIso.StableHilbertLevel.pointFamilyIso R i k D H hH g Hm Hi N labels b).symm
    (Level.IsoConjugation.isoSymm_isMonHom
      (hE := LevelFamilyComparison.StableHilbertLevel.pointFamilyIso_isMonHom R i k D H hH g Hm Hi N labels b)
      (LevelPointFamilyIso.StableHilbertLevel.pointFamilyIso R i k D H hH g Hm Hi N labels b))
    (LevelComparison.StableHilbertLevelComparison.lineAt R i D H hH g Hm Hi N labels j a) (LevelComparison.StableHilbertLevelComparison.lineAt R i D H hH g Hm Hi N labels k b) d
    (LevelComparison.StableHilbertLevelComparison.familyIso R i D H hH hD g Hm Hi N labels j k a b hab)
    (LevelComparison.StableHilbertLevelComparison.familyIso_isMonHom R i D H hH hD g Hm Hi N labels j k a b hab)
    (LevelComparison.StableHilbertLevelComparison.familyIso_line R i D H hH hD g Hm Hi N labels j k a b hab)
    (LevelComparison.StableHilbertLevelComparison.familyIso_level R i D H hH hD g Hm Hi N labels j k a b hab)
    E F hδ hd

theorem enhancementIso_unique (q : Moduli.Isomorphisms.LevelPreservingIso E.object F.object)
    (hq : q.abelian = LevelComparison.StableHilbertLevelComparison.familyIso R i D H hH hD g Hm Hi N labels j k a b hab) :
    q = enhancementIso R i D H hH hD g Hm Hi N labels d hd δ hδ j k a b hab E F :=
  Moduli.Isomorphisms.LevelPreservingIso.ext_abelian q _ (congrArg Iso.hom
    (hq.trans (enhancementIso_abelian R i D H hH hD g Hm Hi N labels d hd δ hδ j k a b hab E F).symm))

/-- The dual and polarization comparisons satisfy the full cocycle,
not merely equality of their moduli classes. -/
theorem enhancementIso_cocycle
    (l : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) (c : T ⟶ (LevelParameter.StableHilbertLevel.parameter R i l D H hH g Hm Hi N labels))
    (hbc : (b ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels)) ≫ ChartPullbacks.stableHilbertChartToRank R i k D H =
      (c ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i l D H hH g Hm Hi N labels)) ≫ ChartPullbacks.stableHilbertChartToRank R i l D H)
    (hac : (a ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels)) ≫ ChartPullbacks.stableHilbertChartToRank R i j D H =
      (c ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i l D H hH g Hm Hi N labels)) ≫ ChartPullbacks.stableHilbertChartToRank R i l D H)
    (G : GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ (LevelComparison.StableHilbertLevelComparison.familyAt R i D H hH g Hm Hi N labels l c) (LevelComparison.StableHilbertLevelComparison.lineAt R i D H hH g Hm Hi N labels l c) d) :
    (enhancementIso R i D H hH hD g Hm Hi N labels d hd δ hδ j k a b hab E F).trans
      (enhancementIso R i D H hH hD g Hm Hi N labels d hd δ hδ k l b c hbc F G) =
    enhancementIso R i D H hH hD g Hm Hi N labels d hd δ hδ j l a c hac E G := by
  exact moduli_cocycle_of_comparisons
    (enhancementIso R i D H hH hD g Hm Hi N labels d hd δ hδ j k a b hab E F)
    (enhancementIso R i D H hH hD g Hm Hi N labels d hd δ hδ k l b c hbc F G)
    (enhancementIso R i D H hH hD g Hm Hi N labels d hd δ hδ j l a c hac E G)
    (LevelComparison.StableHilbertLevelComparison.familyIso R i D H hH hD g Hm Hi N labels j k a b hab)
    (LevelComparison.StableHilbertLevelComparison.familyIso R i D H hH hD g Hm Hi N labels k l b c hbc)
    (LevelComparison.StableHilbertLevelComparison.familyIso R i D H hH hD g Hm Hi N labels j l a c hac)
    (enhancementIso_abelian R i D H hH hD g Hm Hi N labels d hd δ hδ j k a b hab E F)
    (enhancementIso_abelian R i D H hH hD g Hm Hi N labels d hd δ hδ k l b c hbc F G)
    (enhancementIso_abelian R i D H hH hD g Hm Hi N labels d hd δ hδ j l a c hac E G)
    (LevelComparison.StableHilbertLevelComparison.familyIso_cocycle
    R i D H hH hD g Hm Hi N labels j k a b hab l c hbc hac)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationComparison.StableHilbertPolarizationComparison
