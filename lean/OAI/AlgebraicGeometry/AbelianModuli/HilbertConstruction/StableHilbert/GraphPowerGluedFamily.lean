import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerFamilyCharts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PolarizedFamilyGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ModeledTargetIsoExistence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RefinedPolarizedChartRecovery

/-! # Graph Power Glued Family -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerGluedFamily.StableHilbertGraphPowerGluing

noncomputable section

/-! The actual universal polarized full-level family on the glued
stable graph-power parameter scheme. The directed refinement is used
only for object descent; every original stable chart is then recovered
as an original LevelPreservingIso on all test schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} n D H) H)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{0} n H ≤ D)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (d : ℕ) (δ : Fin g → ℕ) (Φ : GraphPower.LocusPresentation.GraphPowerLocusFactory R g N d δ)
    (hd : 0 < d) (hδ : ∀ k, 0 < δ k) (hN : 3 ≤ N)

/-- The genuine original moduli object on the actual glued scheme. -/
def universalFamily : PolarizationData.PolarizedAbelianWithFullLevel g δ N (GraphPowerGluing.StableHilbertGraphPowerGluing.parameter R i D H hH hD g Hm Hi N labels d δ Φ).left :=
  Directed.PolarizedFamilyGluing.DirectedPolarizedSchemeGluing.family (GraphPowerFamilyCharts.StableHilbertGraphPowerGluing.familyCover R i D H hH hD g Hm Hi N labels d δ Φ) (GraphPowerFamilyCharts.StableHilbertGraphPowerGluing.refinedFamily R i D H hH hD g Hm Hi N labels d δ Φ) hN (GraphPowerFamilyCharts.StableHilbertGraphPowerGluing.refinedFamilyIso R i D H hH hD g Hm Hi N labels d δ Φ hd hδ)

theorem universalFamily_abelian :
    (universalFamily R i D H hH hD g Hm Hi N labels d δ Φ hd hδ hN).abelian =
      GraphPowerFamilyCharts.StableHilbertGraphPowerGluing.abelian R i D H hH hD g Hm Hi N labels d δ Φ hd hδ hN := rfl

theorem universalFamily_dualAbelian :
    (universalFamily R i D H hH hD g Hm Hi N labels d δ Φ hd hδ hN).dual.abelian =
      GraphPowerFamilyCharts.StableHilbertGraphPowerGluing.dualAbelian R i D H hH hD g Hm Hi N labels d δ Φ hd hδ hN := rfl

theorem universalFamily_level :
    (universalFamily R i D H hH hD g Hm Hi N labels d δ Φ hd hδ hN).level =
      GraphPowerFamilyCharts.StableHilbertGraphPowerGluing.level R i D H hH hD g Hm Hi N labels d δ Φ hd hδ hN := rfl

/-- Exact original recovery on the actual directed refinement. -/
def universalFamily_refinedIso (v : (GraphPowerFamilyCharts.StableHilbertGraphPowerGluing.familyCover R i D H hH hD g Hm Hi N labels d δ Φ).I₀) :
    Moduli.Isomorphisms.LevelPreservingIso ((GraphPowerFamilyCharts.StableHilbertGraphPowerGluing.refinedFamily R i D H hH hD g Hm Hi N labels d δ Φ) v)
      ((universalFamily R i D H hH hD g Hm Hi N labels d δ Φ hd hδ hN).pullback ((GraphPowerFamilyCharts.StableHilbertGraphPowerGluing.familyCover R i D H hH hD g Hm Hi N labels d δ Φ).f v)) :=
  Directed.PolarizedFamilyGluing.DirectedPolarizedSchemeGluing.familyChartIso (GraphPowerFamilyCharts.StableHilbertGraphPowerGluing.familyCover R i D H hH hD g Hm Hi N labels d δ Φ) (GraphPowerFamilyCharts.StableHilbertGraphPowerGluing.refinedFamily R i D H hH hD g Hm Hi N labels d δ Φ) hN (GraphPowerFamilyCharts.StableHilbertGraphPowerGluing.refinedFamilyIso R i D H hH hD g Hm Hi N labels d δ Φ hd hδ) v

private theorem refinedChartMap_original_left
    (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) (k : (GraphPowerParameter.StableHilbertGraphPower.parameter R i j D H hH g Hm Hi N labels d δ Φ).left.directedAffineCover.I₀) :
    (GraphPowerFamilyCharts.StableHilbertGraphPowerGluing.refinedChartMap R i D H hH hD g Hm Hi N labels d δ Φ ⟨j, k⟩).left =
      (GraphPowerParameter.StableHilbertGraphPower.parameter R i j D H hH g Hm Hi N labels d δ Φ).left.directedAffineCover.f k := rfl

private theorem familyCover_original_map
    (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) (k : (GraphPowerParameter.StableHilbertGraphPower.parameter R i j D H hH g Hm Hi N labels d δ Φ).left.directedAffineCover.I₀) :
    (GraphPowerFamilyCharts.StableHilbertGraphPowerGluing.familyCover R i D H hH hD g Hm Hi N labels d δ Φ).f ⟨j, k⟩ = (GraphPowerParameter.StableHilbertGraphPower.parameter R i j D H hH g Hm Hi N labels d δ Φ).left.directedAffineCover.f k ≫ (GraphPowerGluing.StableHilbertGraphPowerGluing.chartMap R i D H hH hD g Hm Hi N labels d δ Φ j).left := rfl

/-- Each original stable chart recovers its original polarized family.
Existence glues from its affine refinement using the already proved
modeled-target isomorphism sheaf and full-level rigidity. -/
def universalFamily_chartIso (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) :
    Moduli.Isomorphisms.LevelPreservingIso (GraphPowerParameter.StableHilbertGraphPower.universalFamily R i j D H hH g Hm Hi N labels d δ Φ)
      ((universalFamily R i D H hH hD g Hm Hi N labels d δ Φ hd hδ hN).pullback (GraphPowerGluing.StableHilbertGraphPowerGluing.chartMap R i D H hH hD g Hm Hi N labels d δ Φ j).left) :=
  Classical.choice (by
    apply ModeledTargetIsoExistence.levelIso_nonempty_of_openCover_modeledTarget
      (universalFamily R i D H hH hD g Hm Hi N labels d δ Φ hd hδ hN)
      (GraphPowerGluing.StableHilbertGraphPowerGluing.chartMap R i D H hH hD g Hm Hi N labels d δ Φ j).left (GraphPowerParameter.StableHilbertGraphPower.universalFamily R i j D H hH g Hm Hi N labels d δ Φ) hN (GraphPowerParameter.StableHilbertGraphPower.parameter R i j D H hH g Hm Hi N labels d δ Φ).left.directedAffineCover
    intro k
    let v : (GraphPowerFamilyCharts.StableHilbertGraphPowerGluing.familyCover R i D H hH hD g Hm Hi N labels d δ Φ).I₀ := ⟨j, k⟩
    let a := GraphPowerFamilyCharts.StableHilbertGraphPowerGluing.refinedChartMap R i D H hH hD g Hm Hi N labels d δ Φ v
    let t := (GraphPowerParameter.StableHilbertGraphPower.parameter R i j D H hH g Hm Hi N labels d δ Φ).left.directedAffineCover.f k
    have hs : a.left = t := refinedChartMap_original_left R i D H hH hD g Hm Hi N labels d δ Φ j k
    have ht : (GraphPowerFamilyCharts.StableHilbertGraphPowerGluing.familyCover R i D H hH hD g Hm Hi N labels d δ Φ).f v = t ≫ (GraphPowerGluing.StableHilbertGraphPowerGluing.chartMap R i D H hH hD g Hm Hi N labels d δ Φ j).left := familyCover_original_map R i D H hH hD g Hm Hi N labels d δ Φ j k
    exact ⟨RefinedPolarizedChartRecovery.refinedPolarizedChartIso
      (universalFamily R i D H hH hD g Hm Hi N labels d δ Φ hd hδ hN)
      (GraphPowerParameter.StableHilbertGraphPower.universalFamily R i j D H hH g Hm Hi N labels d δ Φ) t a.left ((GraphPowerFamilyCharts.StableHilbertGraphPowerGluing.familyCover R i D H hH hD g Hm Hi N labels d δ Φ).f v) (GraphPowerGluing.StableHilbertGraphPowerGluing.chartMap R i D H hH hD g Hm Hi N labels d δ Φ j).left hs ht
      (universalFamily_refinedIso R i D H hH hD g Hm Hi N labels d δ Φ hd hδ hN v)⟩)

/-- Every map into an original chart has the same original moduli
object after composition with the chart inclusion into the glued base. -/
def universalFamily_chartIsoOnTest (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m)
    {T : Scheme.{0}} (t : T ⟶ (GraphPowerParameter.StableHilbertGraphPower.parameter R i j D H hH g Hm Hi N labels d δ Φ).left) :
    Moduli.Isomorphisms.LevelPreservingIso ((GraphPowerParameter.StableHilbertGraphPower.universalFamily R i j D H hH g Hm Hi N labels d δ Φ).pullback t)
      ((universalFamily R i D H hH hD g Hm Hi N labels d δ Φ hd hδ hN).pullback (t ≫ (GraphPowerGluing.StableHilbertGraphPowerGluing.chartMap R i D H hH hD g Hm Hi N labels d δ Φ j).left)) :=
  ((universalFamily_chartIso R i D H hH hD g Hm Hi N labels d δ Φ hd hδ hN j).pullback t).trans
    (Moduli.Isomorphisms.LevelPreservingIso.pullbackComp
      (universalFamily R i D H hH hD g Hm Hi N labels d δ Φ hd hδ hN) (GraphPowerGluing.StableHilbertGraphPowerGluing.chartMap R i D H hH hD g Hm Hi N labels d δ Φ j).left t)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerGluedFamily.StableHilbertGraphPowerGluing
