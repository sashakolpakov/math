import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationFamilyCharts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PolarizedFamilyGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ModeledTargetIsoExistence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RefinedPolarizedChartRecovery

/-! # Glued Polarized Family -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GluedPolarizedFamily.StableHilbertPolarizationGluing

noncomputable section

/-! The actual universal polarized full-level family on the glued
stable normalized-polarization scheme. The directed refinement is used
only for object descent; every original stable chart is then recovered
as an original LevelPreservingIso on all test schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} n D H) H)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{0} n H ≤ D)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (qR : Spec (.of R) ⟶ Spec (.of ℚ))
    (d : ℕ) (hd : 0 < d) (δ : Fin g → ℕ) (hδ : ∀ k, 0 < δ k) (hN : 3 ≤ N)

/-- The genuine original moduli object on the actual glued scheme. -/
def universalFamily : PolarizationData.PolarizedAbelianWithFullLevel g δ N (PolarizationGluing.StableHilbertPolarizationGluing.parameter R i D H hH hD g Hm Hi N labels qR d hd δ hδ).left :=
  Directed.PolarizedFamilyGluing.DirectedPolarizedSchemeGluing.family (PolarizationFamilyCharts.StableHilbertPolarizationGluing.familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ) (PolarizationFamilyCharts.StableHilbertPolarizationGluing.refinedFamily R i D H hH hD g Hm Hi N labels qR d hd δ hδ) hN (PolarizationFamilyCharts.StableHilbertPolarizationGluing.refinedFamilyIso R i D H hH hD g Hm Hi N labels qR d hd δ hδ)

theorem universalFamily_abelian :
    (universalFamily R i D H hH hD g Hm Hi N labels qR d hd δ hδ hN).abelian =
      PolarizationFamilyCharts.StableHilbertPolarizationGluing.abelian R i D H hH hD g Hm Hi N labels qR d hd δ hδ hN := rfl

theorem universalFamily_dualAbelian :
    (universalFamily R i D H hH hD g Hm Hi N labels qR d hd δ hδ hN).dual.abelian =
      PolarizationFamilyCharts.StableHilbertPolarizationGluing.dualAbelian R i D H hH hD g Hm Hi N labels qR d hd δ hδ hN := rfl

theorem universalFamily_level :
    (universalFamily R i D H hH hD g Hm Hi N labels qR d hd δ hδ hN).level =
      PolarizationFamilyCharts.StableHilbertPolarizationGluing.level R i D H hH hD g Hm Hi N labels qR d hd δ hδ hN := rfl

/-- Exact original recovery on the actual directed refinement. -/
def universalFamily_refinedIso (v : (PolarizationFamilyCharts.StableHilbertPolarizationGluing.familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ).I₀) :
    Moduli.Isomorphisms.LevelPreservingIso ((PolarizationFamilyCharts.StableHilbertPolarizationGluing.refinedFamily R i D H hH hD g Hm Hi N labels qR d hd δ hδ) v)
      ((universalFamily R i D H hH hD g Hm Hi N labels qR d hd δ hδ hN).pullback ((PolarizationFamilyCharts.StableHilbertPolarizationGluing.familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ).f v)) :=
  Directed.PolarizedFamilyGluing.DirectedPolarizedSchemeGluing.familyChartIso (PolarizationFamilyCharts.StableHilbertPolarizationGluing.familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ) (PolarizationFamilyCharts.StableHilbertPolarizationGluing.refinedFamily R i D H hH hD g Hm Hi N labels qR d hd δ hδ) hN (PolarizationFamilyCharts.StableHilbertPolarizationGluing.refinedFamilyIso R i D H hH hD g Hm Hi N labels qR d hd δ hδ) v

private theorem refinedChartMap_original_left
    (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) (k : (PolarizationParameter.StableHilbertPolarization.parameter R i j D H hH g Hm Hi N labels qR d hd δ hδ).left.directedAffineCover.I₀) :
    (PolarizationFamilyCharts.StableHilbertPolarizationGluing.refinedChartMap R i D H hH hD g Hm Hi N labels qR d hd δ hδ ⟨j, k⟩).left =
      (PolarizationParameter.StableHilbertPolarization.parameter R i j D H hH g Hm Hi N labels qR d hd δ hδ).left.directedAffineCover.f k := rfl

private theorem familyCover_original_map
    (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) (k : (PolarizationParameter.StableHilbertPolarization.parameter R i j D H hH g Hm Hi N labels qR d hd δ hδ).left.directedAffineCover.I₀) :
    (PolarizationFamilyCharts.StableHilbertPolarizationGluing.familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ).f ⟨j, k⟩ = (PolarizationParameter.StableHilbertPolarization.parameter R i j D H hH g Hm Hi N labels qR d hd δ hδ).left.directedAffineCover.f k ≫ (PolarizationGluing.StableHilbertPolarizationGluing.chartMap R i D H hH hD g Hm Hi N labels qR d hd δ hδ j).left := rfl

/-- Each original stable chart recovers its original polarized family.
Existence glues from its affine refinement using the already proved
modeled-target isomorphism sheaf and full-level rigidity. -/
def universalFamily_chartIso (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) :
    Moduli.Isomorphisms.LevelPreservingIso (PolarizationParameter.StableHilbertPolarization.universalFamily R i j D H hH g Hm Hi N labels qR d hd δ hδ)
      ((universalFamily R i D H hH hD g Hm Hi N labels qR d hd δ hδ hN).pullback (PolarizationGluing.StableHilbertPolarizationGluing.chartMap R i D H hH hD g Hm Hi N labels qR d hd δ hδ j).left) :=
  Classical.choice (by
    apply ModeledTargetIsoExistence.levelIso_nonempty_of_openCover_modeledTarget
      (universalFamily R i D H hH hD g Hm Hi N labels qR d hd δ hδ hN)
      (PolarizationGluing.StableHilbertPolarizationGluing.chartMap R i D H hH hD g Hm Hi N labels qR d hd δ hδ j).left (PolarizationParameter.StableHilbertPolarization.universalFamily R i j D H hH g Hm Hi N labels qR d hd δ hδ) hN (PolarizationParameter.StableHilbertPolarization.parameter R i j D H hH g Hm Hi N labels qR d hd δ hδ).left.directedAffineCover
    intro k
    let v : (PolarizationFamilyCharts.StableHilbertPolarizationGluing.familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ).I₀ := ⟨j, k⟩
    let a := PolarizationFamilyCharts.StableHilbertPolarizationGluing.refinedChartMap R i D H hH hD g Hm Hi N labels qR d hd δ hδ v
    let t := (PolarizationParameter.StableHilbertPolarization.parameter R i j D H hH g Hm Hi N labels qR d hd δ hδ).left.directedAffineCover.f k
    have hs : a.left = t := refinedChartMap_original_left R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k
    have ht : (PolarizationFamilyCharts.StableHilbertPolarizationGluing.familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ).f v = t ≫ (PolarizationGluing.StableHilbertPolarizationGluing.chartMap R i D H hH hD g Hm Hi N labels qR d hd δ hδ j).left := familyCover_original_map R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k
    exact ⟨RefinedPolarizedChartRecovery.refinedPolarizedChartIso
      (universalFamily R i D H hH hD g Hm Hi N labels qR d hd δ hδ hN)
      (PolarizationParameter.StableHilbertPolarization.universalFamily R i j D H hH g Hm Hi N labels qR d hd δ hδ) t a.left ((PolarizationFamilyCharts.StableHilbertPolarizationGluing.familyCover R i D H hH hD g Hm Hi N labels qR d hd δ hδ).f v) (PolarizationGluing.StableHilbertPolarizationGluing.chartMap R i D H hH hD g Hm Hi N labels qR d hd δ hδ j).left hs ht
      (universalFamily_refinedIso R i D H hH hD g Hm Hi N labels qR d hd δ hδ hN v)⟩)

/-- Every map into an original chart has the same original moduli
object after composition with the chart inclusion into the glued base. -/
def universalFamily_chartIsoOnTest (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m)
    {T : Scheme.{0}} (t : T ⟶ (PolarizationParameter.StableHilbertPolarization.parameter R i j D H hH g Hm Hi N labels qR d hd δ hδ).left) :
    Moduli.Isomorphisms.LevelPreservingIso ((PolarizationParameter.StableHilbertPolarization.universalFamily R i j D H hH g Hm Hi N labels qR d hd δ hδ).pullback t)
      ((universalFamily R i D H hH hD g Hm Hi N labels qR d hd δ hδ hN).pullback (t ≫ (PolarizationGluing.StableHilbertPolarizationGluing.chartMap R i D H hH hD g Hm Hi N labels qR d hd δ hδ j).left)) :=
  ((universalFamily_chartIso R i D H hH hD g Hm Hi N labels qR d hd δ hδ hN j).pullback t).trans
    (Moduli.Isomorphisms.LevelPreservingIso.pullbackComp
      (universalFamily R i D H hH hD g Hm Hi N labels qR d hd δ hδ hN) (PolarizationGluing.StableHilbertPolarizationGluing.chartMap R i D H hH hD g Hm Hi N labels qR d hd δ hδ j).left t)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GluedPolarizedFamily.StableHilbertPolarizationGluing
