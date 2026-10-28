import OAI.RepresentationTheory.Theta.Geometric.ComponentFormFaithfulness
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet

/-! # Component Labels -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Original complex component labels are unique, and every dual-number
test factors through the component containing its closed point. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.componentComplexInclusion_disjoint (hg : D.pel.HasIntegralModelGeometry) :
    Pairwise (fun i j => Disjoint (Set.range (D.componentComplexInclusion i).left)
      (Set.range (D.componentComplexInclusion j).left)) := by
  let : IsIso D.pel.componentAssembly := hg.decomposition
  have hi (i : Fin D.pel.componentCount) : Sigma.ι D.pel.components.S i ≫
      (asIso D.pel.componentAssembly).hom = D.pel.inclusion i := by
    simp only [asIso_hom, AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.componentAssembly, Sigma.ι_comp_desc]
  intro i j hij
  simp only [Data.ActiveHeckeThetaData.componentComplexInclusion, AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.componentInclusion, AlgebraicGeometry.PELModuli.IntegralModel.Coproduct.baseChange_map_range]
  have H := AlgebraicGeometry.PELModuli.IntegralModel.Coproduct.baseChange_decomposition_disjoint D.pel.components.S D.pel.generic
    (asIso D.pel.componentAssembly) hij
  simp only [hi, AlgebraicGeometry.PELModuli.IntegralModel.Coproduct.baseChange_map_range] at H
  exact H.preimage _

theorem Data.ActiveHeckeThetaData.component_complex_point_label (hg : D.pel.HasIntegralModelGeometry)
    {i j : Fin D.pel.componentCount} (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (D.componentComplex i))
    (y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (D.componentComplex j))
    (h : x ≫ D.componentComplexInclusion i = y ≫ D.componentComplexInclusion j) : i = j := by
  by_contra hij
  have H := D.componentComplexInclusion_disjoint hg hij
  have hx : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (x ≫ D.componentComplexInclusion i) ∈
      Set.range (D.componentComplexInclusion i).left := ⟨AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x, rfl⟩
  have hy : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (y ≫ D.componentComplexInclusion j) ∈
      Set.range (D.componentComplexInclusion j).left := ⟨AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying y, rfl⟩
  rw [h] at hx
  exact Set.disjoint_left.mp H hx hy

theorem Data.ActiveHeckeThetaData.dualTest_component_lift (hg : D.pel.HasIntegralModelGeometry)
    (t : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest ⟶ D.pel.complexSpace) :
    ∃ i : Fin D.pel.componentCount, ∃ l : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest ⟶ D.componentComplex i,
      l ≫ D.componentComplexInclusion i = t := by
  obtain ⟨i, x, hx⟩ := D.exists_component_complex_point hg (AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualClosedPoint ≫ t)
  let : IsOpenImmersion (D.componentComplexInclusion i).left := D.componentComplexInclusion_open hg i
  have hmem : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualClosedPoint ≫ t) ∈
      Set.range (D.componentComplexInclusion i).left := by
    rw [← hx]
    exact ⟨AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x, rfl⟩
  obtain ⟨l, hl⟩ := AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest_lift_open (D.componentComplexInclusion i) t hmem
  exact ⟨i, l, hl⟩

theorem Data.ActiveHeckeThetaData.periodImage_component_iff (j : Fin D.pel.componentCount) (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : X.toOver ≅ D.componentComplex j) (cover : D.domain → X.analyticSpace)
    (hc : Function.Surjective cover) (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace) :
    (∃ z : D.domain, p = D.totalPeriodMap j X e cover z) ↔
      ∃ x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (D.componentComplex j), x ≫ D.componentComplexInclusion j = p := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨cover z ≫ e.hom, Category.assoc _ _ _⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨z, hz⟩ := hc (x ≫ e.inv)
    refine ⟨z, ?_⟩
    rw [Data.ActiveHeckeThetaData.totalPeriodMap, hz, Category.assoc, Iso.inv_hom_id_assoc]

end

end OAI.RepresentationTheory.Theta.Geometric
