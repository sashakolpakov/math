import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationChartInjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GluedPolarizedFamily
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CommonChartPointEquality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.CommonChartIso

/-! # Polarization Injectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationInjectivity.StableHilbertPolarizationGluing

noncomputable section

/-! Original polarized full-level isomorphisms determine points of the
actual glued uniform stable parameter on locally Noetherian tests.
The proof constructs coordinate changes on affine chart pullbacks and
uses the existing monomorphism to the balanced quotient. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} n D H) H)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{0} n H ≤ D)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (qR : Spec (.of R) ⟶ Spec (.of ℚ))
    (d : ℕ) (hd : 0 < d) (δ : Fin g → ℕ) (hδ : ∀ k, 0 < δ k)

/-- Noetherian-test injectivity of the constructed glued family.
Both the abelian scheme and its dual, Poincare class, polarization and
full ordered level are those of the original LevelPreservingIso. -/
theorem points_eq_of_iso
    (hg : 0 < g) (hN : 3 ≤ N)
    (hd_eq : d = Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
    (hn : n + 1 = Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ)
    {T : Over (Spec (.of R))} [IsLocallyNoetherian T.left]
    (a b : T ⟶ (PolarizationGluing.StableHilbertPolarizationGluing.parameter R i D H hH hD g Hm Hi N labels qR d hd δ hδ))
    (e : Moduli.Isomorphisms.LevelPreservingIso
      ((GluedPolarizedFamily.StableHilbertPolarizationGluing.universalFamily R i D H hH hD g Hm Hi N labels qR d hd δ hδ hN).pullback a.left)
      ((GluedPolarizedFamily.StableHilbertPolarizationGluing.universalFamily R i D H hH hD g Hm Hi N labels qR d hd δ hδ hN).pullback b.left)) :
    a = b := by
  let A := GluedPolarizedFamily.StableHilbertPolarizationGluing.universalFamily R i D H hH hD g Hm Hi N labels qR d hd δ hδ hN
  apply Affine.CommonChartPointEquality.overHom_eq_of_affine_common_chart_factors
    (fun j => (PolarizationParameter.StableHilbertPolarization.parameter R i j D H hH g Hm Hi N labels qR d hd δ hδ)) (fun j => (PolarizationGluing.StableHilbertPolarizationGluing.chartMap R i D H hH hD g Hm Hi N labels qR d hd δ hδ j))
    (PolarizationGluing.StableHilbertPolarizationGluing.charts_cover R i D H hH hD g Hm Hi N labels qR d hd δ hδ) a b
  intro V _ _ r j k av bv ha hb
  exact PolarizationChartInjectivity.StableHilbertPolarizationGluing.affineChartPoints_eq_of_iso R i D H hH hD g Hm Hi N labels qR d hd δ hδ
    hg hN hd_eq hn j k av bv
    (Polarized.CommonChartIso.polarizedCommonChartIso A
      (PolarizationParameter.StableHilbertPolarization.universalFamily R i j D H hH g Hm Hi N labels qR d hd δ hδ)
      (PolarizationParameter.StableHilbertPolarization.universalFamily R i k D H hH g Hm Hi N labels qR d hd δ hδ)
      (PolarizationGluing.StableHilbertPolarizationGluing.chartMap R i D H hH hD g Hm Hi N labels qR d hd δ hδ j)
      (PolarizationGluing.StableHilbertPolarizationGluing.chartMap R i D H hH hD g Hm Hi N labels qR d hd δ hδ k)
      a b av bv r ha hb
      (GluedPolarizedFamily.StableHilbertPolarizationGluing.universalFamily_chartIso R i D H hH hD g Hm Hi N labels qR d hd δ hδ hN j)
      (GluedPolarizedFamily.StableHilbertPolarizationGluing.universalFamily_chartIso R i D H hH hD g Hm Hi N labels qR d hd δ hδ hN k) e)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationInjectivity.StableHilbertPolarizationGluing
