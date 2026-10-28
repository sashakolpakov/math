import OAI.RepresentationTheory.Theta.Geometric.Local.ReferenceModuliPeriods
import OAI.RepresentationTheory.Theta.Geometric.Universal.HolomorphicTransport
import OAI.RepresentationTheory.Theta.Geometric.Family.ChartOpenImage

/-! # Locus Open -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The locus of original reference moduli points is open in every
actual smooth integral subspace of the original complex PEL space. -/

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

def Data.ActiveHeckeThetaData.referenceLocus : Set (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :=
  {x | ∃ a : D.domain, x ≫ f = D.referenceModuliMap hg a}

variable [IsIntegral S.left] [Smooth S.hom]

theorem Data.ActiveHeckeThetaData.referenceLocus_isOpen (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) :
    IsOpen (D.referenceLocus hg f) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨a, ha⟩ := hx
  let R := D.referencePELPointData hg a
  let C := Universal.FamilyPeriodCharts.complexUniversalFamilyCharts D.pel f x
  let H := Universal.HolomorphicTransport.complexUniversalHolomorphicTransport D.pel hg f x
  let z₀ : H.compatible.neighborhood := ⟨Intrinsic.FamilyFrames.familyChartCenter C, H.compatible.center⟩
  have hz₀ : Intrinsic.FamilyFrames.familyChartParameter C z₀ ≫ f = R.point := by
    change Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C) ≫ f = R.point
    rw [Family.ChartOpenImage.familyChartParameter_center]
    exact ha
  obtain ⟨O, period, hO, hzO, hOU, _, _, hmod⟩ :=
    R.exists_holomorphic_reference_moduli_periods f H z₀ hz₀ hs hdegree
  have ho := Family.ChartOpenImage.familyChartParameter_open_image C O hO (hOU.trans H.compatible.subset_chart)
  have hxO : x ∈ Intrinsic.FamilyFrames.familyChartParameter C '' O :=
    ⟨Intrinsic.FamilyFrames.familyChartCenter C, hzO, Family.ChartOpenImage.familyChartParameter_center C⟩
  apply Filter.mem_of_superset (ho.mem_nhds hxO)
  rintro y ⟨w, hw, rfl⟩
  obtain ⟨hp, he⟩ := hmod w hw
  exact ⟨⟨period w, hp⟩, he⟩

end

end OAI.RepresentationTheory.Theta.Geometric
