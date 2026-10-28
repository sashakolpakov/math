import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicTransport
import OAI.RepresentationTheory.Theta.Geometric.Family.ChartOpenImage
import Mathlib.Topology.Compactness.Lindelof

/-! # Countable Transport Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CountableTransportCover

noncomputable section

/-! Countably many constructed native compatible period charts cover
every second-countable smooth integral base of an actual polarized family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

open OAI.RepresentationTheory.Theta.Geometric.Family.ChartOpenImage

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
    [SecondCountableTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)] {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)

omit [NumberField.IsCMField E] in
theorem exists_countable_native_transport_cover (hN : 0 < N) :
    ∃ (I : Type) (_ : Countable I) (x : I → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
      (C : ∀ i, PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian (x i))
      (F : ∀ i, RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.NativeFamilyPeriodFrame (C i))
      (H : ∀ i, Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport A ρ (F i)),
      ∀ y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, ∃ i, ∃ z : (H i).compatible.neighborhood,
        RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter (C i) z = y := by
  have hex (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) := Intrinsic.HolomorphicTransport.exists_native_family_holomorphic_transport A ρ x hN
  choose C F hH using hex
  let H (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) := Classical.choice (hH x)
  let U (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) := RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter (C x) '' (H x).compatible.neighborhood
  have hU (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) : IsOpen (U x) :=
    RepresentationTheory.Theta.Geometric.Family.ChartOpenImage.familyChartParameter_open_image (C x) _ (H x).compatible.isOpen (H x).compatible.subset_chart
  have hxU (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) : x ∈ U x :=
    ⟨RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter (C x), (H x).compatible.center, RepresentationTheory.Theta.Geometric.Family.ChartOpenImage.familyChartParameter_center (C x)⟩
  obtain ⟨T, hT, hcover⟩ := isLindelof_univ.elim_countable_subcover U hU
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hxU x⟩)
  refine ⟨T, hT.to_subtype, Subtype.val, fun i => C i.val, fun i => F i.val,
    fun i => H i.val, ?_⟩
  intro y
  obtain ⟨x, hx⟩ := Set.mem_iUnion.mp (hcover (Set.mem_univ y))
  obtain ⟨hxT, z, hz, he⟩ := Set.mem_iUnion.mp hx
  exact ⟨⟨x, hxT⟩, ⟨z, hz⟩, he⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CountableTransportCover
