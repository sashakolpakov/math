import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerChartInjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerGluedFamily
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CommonChartPointEquality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.CommonChartIso

/-! # Graph Power Injectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerInjectivity.StableHilbertGraphPowerGluing

noncomputable section

/-! Original polarized full-level isomorphisms determine points of the
actual glued stable graph-power parameter on locally Noetherian tests.
The proof constructs coordinate changes on affine chart pullbacks and
uses the existing monomorphism to the balanced quotient. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped BigOperators

variable (R : Type) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} n D H) H)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{0} n H ≤ D)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (d : ℕ) (δ : Fin g → ℕ) (Φ : GraphPower.LocusPresentation.GraphPowerLocusFactory R g N d δ)
    (hd : 0 < d) (hδ : ∀ k, 0 < δ k)

/-- Noetherian-test injectivity of the constructed glued family.
Both the abelian scheme and its dual, Poincare class, polarization and
full ordered level are those of the original LevelPreservingIso. -/
theorem points_eq_of_iso
    (hNR : IsUnit (N : R))
    (hg : 0 < g) (hN : 3 ≤ N)
    (hn : n + 1 = (2 : ℕ) ^ g * (∏ k, δ k) * d ^ g)
    {T : Over (Spec (.of R))} [IsLocallyNoetherian T.left]
    (a b : T ⟶ (GraphPowerGluing.StableHilbertGraphPowerGluing.parameter R i D H hH hD g Hm Hi N labels d δ Φ))
    (e : Moduli.Isomorphisms.LevelPreservingIso
      ((GraphPowerGluedFamily.StableHilbertGraphPowerGluing.universalFamily R i D H hH hD g Hm Hi N labels d δ Φ hd hδ hN).pullback a.left)
      ((GraphPowerGluedFamily.StableHilbertGraphPowerGluing.universalFamily R i D H hH hD g Hm Hi N labels d δ Φ hd hδ hN).pullback b.left)) :
    a = b := by
  let A := GraphPowerGluedFamily.StableHilbertGraphPowerGluing.universalFamily R i D H hH hD g Hm Hi N labels d δ Φ hd hδ hN
  apply Affine.CommonChartPointEquality.overHom_eq_of_affine_common_chart_factors
    (fun j => (GraphPowerParameter.StableHilbertGraphPower.parameter R i j D H hH g Hm Hi N labels d δ Φ)) (fun j => (GraphPowerGluing.StableHilbertGraphPowerGluing.chartMap R i D H hH hD g Hm Hi N labels d δ Φ j))
    (GraphPowerGluing.StableHilbertGraphPowerGluing.charts_cover R i D H hH hD g Hm Hi N labels d δ Φ) a b
  intro V _ _ r j k av bv ha hb
  exact GraphPowerChartInjectivity.StableHilbertGraphPowerGluing.affineChartPoints_eq_of_iso R i D H hH hD g Hm Hi N labels d δ Φ
    hd hNR hg hN hn j k av bv
    (Polarized.CommonChartIso.polarizedCommonChartIso A
      (GraphPowerParameter.StableHilbertGraphPower.universalFamily R i j D H hH g Hm Hi N labels d δ Φ)
      (GraphPowerParameter.StableHilbertGraphPower.universalFamily R i k D H hH g Hm Hi N labels d δ Φ)
      (GraphPowerGluing.StableHilbertGraphPowerGluing.chartMap R i D H hH hD g Hm Hi N labels d δ Φ j)
      (GraphPowerGluing.StableHilbertGraphPowerGluing.chartMap R i D H hH hD g Hm Hi N labels d δ Φ k)
      a b av bv r ha hb
      (GraphPowerGluedFamily.StableHilbertGraphPowerGluing.universalFamily_chartIso R i D H hH hD g Hm Hi N labels d δ Φ hd hδ hN j)
      (GraphPowerGluedFamily.StableHilbertGraphPowerGluing.universalFamily_chartIso R i D H hH hD g Hm Hi N labels d δ Φ hd hδ hN k) e)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerInjectivity.StableHilbertGraphPowerGluing
