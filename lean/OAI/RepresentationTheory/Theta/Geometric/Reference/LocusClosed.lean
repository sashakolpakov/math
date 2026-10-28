import OAI.RepresentationTheory.Theta.Geometric.Reference.LocusOpen
import OAI.RepresentationTheory.Theta.Geometric.CompatibleReferenceModuli

/-! # Locus Closed -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The original reference moduli locus is closed as well as open:
its full marked reference type persists throughout each compatible chart. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry)
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (f : S ⟶ D.pel.complexSpace)

variable [IsIntegral S.left] [Smooth S.hom]

theorem Data.ActiveHeckeThetaData.referenceLocus_isClosed (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) :
    IsClosed (D.referenceLocus hg f) := by
  apply isOpen_compl_iff.mp
  rw [isOpen_iff_mem_nhds]
  intro x hx
  let C := Universal.FamilyPeriodCharts.complexUniversalFamilyCharts D.pel f x
  let H := Universal.HolomorphicTransport.complexUniversalHolomorphicTransport D.pel hg f x
  have ho := Family.ChartOpenImage.familyChartParameter_open_image C H.compatible.neighborhood H.compatible.isOpen H.compatible.subset_chart
  have hxO : x ∈ Intrinsic.FamilyFrames.familyChartParameter C '' H.compatible.neighborhood :=
    ⟨Intrinsic.FamilyFrames.familyChartCenter C, H.compatible.center, Family.ChartOpenImage.familyChartParameter_center C⟩
  apply Filter.mem_of_superset (ho.mem_nhds hxO)
  rintro y ⟨w, hw, rfl⟩ href
  obtain ⟨a, ha⟩ := href
  let R := D.referencePELPointData hg a
  obtain ⟨b, hb⟩ := R.compatible_reference_moduli_point f H ⟨w, hw⟩ ha hs hdegree
    ⟨Intrinsic.FamilyFrames.familyChartCenter C, H.compatible.center⟩
  apply hx
  refine ⟨b, ?_⟩
  change Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C) ≫ f = D.referenceModuliMap hg b at hb
  simpa only [Family.ChartOpenImage.familyChartParameter_center] using hb

theorem Data.ActiveHeckeThetaData.referenceLocus_isClopen (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) :
    IsClopen (D.referenceLocus hg f) :=
  ⟨D.referenceLocus_isClosed hg f hs hdegree, D.referenceLocus_isOpen hg f hs hdegree⟩

end

end OAI.RepresentationTheory.Theta.Geometric
