import OAI.RepresentationTheory.Theta.Geometric.Universal.HolomorphicTransport
import OAI.RepresentationTheory.Theta.Geometric.Family.ChartOpenImage
import Mathlib.Topology.Compactness.Lindelof

/-! # Countable Universal Charts -/

namespace OAI.RepresentationTheory.Theta.Geometric.CountableUniversalCharts

noncomputable section

/-! Countably many constructed compatible universal-family charts
cover the original complex points of a second-countable smooth base. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
    [SecondCountableTopology (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)] (f : S ⟶ D.complexSpace)

theorem exists_countable_universal_transport_cover :
    ∃ T : Set (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S), T.Countable ∧ ∀ y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S,
      ∃ x : T, ∃ z : (Universal.HolomorphicTransport.complexUniversalHolomorphicTransport D hg f x.val).compatible.neighborhood,
        Intrinsic.FamilyFrames.familyChartParameter (Universal.FamilyPeriodCharts.complexUniversalFamilyCharts D f x.val) z = y := by
  let U (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) := Intrinsic.FamilyFrames.familyChartParameter (Universal.FamilyPeriodCharts.complexUniversalFamilyCharts D f x) ''
    (Universal.HolomorphicTransport.complexUniversalHolomorphicTransport D hg f x).compatible.neighborhood
  have hU (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) : IsOpen (U x) :=
    Family.ChartOpenImage.familyChartParameter_open_image (Universal.FamilyPeriodCharts.complexUniversalFamilyCharts D f x) _
      (Universal.HolomorphicTransport.complexUniversalHolomorphicTransport D hg f x).compatible.isOpen
      (Universal.HolomorphicTransport.complexUniversalHolomorphicTransport D hg f x).compatible.subset_chart
  have hxU (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) : x ∈ U x :=
    ⟨Intrinsic.FamilyFrames.familyChartCenter (Universal.FamilyPeriodCharts.complexUniversalFamilyCharts D f x),
      (Universal.HolomorphicTransport.complexUniversalHolomorphicTransport D hg f x).compatible.center,
      Family.ChartOpenImage.familyChartParameter_center (Universal.FamilyPeriodCharts.complexUniversalFamilyCharts D f x)⟩
  obtain ⟨T, hT, hcover⟩ := isLindelof_univ.elim_countable_subcover U hU
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hxU x⟩)
  refine ⟨T, hT, ?_⟩
  intro y
  obtain ⟨x, hx⟩ := Set.mem_iUnion.mp (hcover (Set.mem_univ y))
  obtain ⟨hxT, hxy⟩ := Set.mem_iUnion.mp hx
  obtain ⟨z, hz, he⟩ := hxy
  exact ⟨⟨x, hxT⟩, ⟨z, hz⟩, he⟩

end

end OAI.RepresentationTheory.Theta.Geometric.CountableUniversalCharts
