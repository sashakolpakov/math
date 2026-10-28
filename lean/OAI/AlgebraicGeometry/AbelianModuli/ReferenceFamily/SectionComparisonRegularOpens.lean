import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SectionComparisonVectors
import OAI.RepresentationTheory.Theta.Geometric.PowerGauge
import OAI.RepresentationTheory.Theta.Geometric.Complex.PointsDetectSections

/-! # Section Comparison Regular Opens -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

section

/-! The enlarged comparison map has genuine algebraic mixed-coordinate
opens. They are exactly the original common section-frame opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates
open scoped _root_.Manifold ContDiff

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {L K : HilbertConstruction.Line.Bundles.LineBundle V.carrier} {n m : ℕ}
    {s : Fin (n + 1) → (HilbertConstruction.Line.Bundles.structureModule V.carrier ⟶ L.sheaf)}
    {t : Fin (m + 1) → (HilbertConstruction.Line.Bundles.structureModule V.carrier ⟶ K.sheaf)}
    {hs : ∀ x : V.carrier, ∃ i, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)}
    {ht : ∀ x : V.carrier, ∃ j, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (t j)}
    (A : SectionComparisonVectors.SectionComparisonAlgebraization V s t hs ht)

local instance SectionComparisonVectors.SectionComparisonAlgebraization.comparisonRegularOpens_integral : IsIntegral V.toOver.left := V.property
local instance SectionComparisonVectors.SectionComparisonAlgebraization.comparisonRegularOpens_smooth : Smooth V.toOver.hom := V.presentation.smooth

def SectionComparisonVectors.SectionComparisonAlgebraization.regularOpen (i : Fin (n + 1) × Fin (m + 1)) : V.carrier.Opens :=
  A.map.left ⁻¹ᵁ SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ)
    (ProjectiveLocalVectors.comparisonCoordinateEquiv n m (.inl i.1)) (ProjectiveLocalVectors.comparisonCoordinateEquiv n m (.inr i.2))

theorem SectionComparisonVectors.SectionComparisonAlgebraization.regularOpen_mem (i : Fin (n + 1) × Fin (m + 1)) (x : V.analyticSpace) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ A.regularOpen i ↔ x ∈ SectionComparisonGauges.sectionComparisonOpen V s t i := by
  obtain ⟨j, hj⟩ := SectionComparisonGauges.sectionComparisonOpen_covers V s t hs ht x
  let p := Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver s hs x
  let q := Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver t ht x
  have hpj : Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch j.1 p := (Intrinsic.SectionCoordinates.nativeSectionCoordinates_inPatch V.presentation s hs j.1 x).mpr hj.1
  have hqj : Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch j.2 q := (Intrinsic.SectionCoordinates.nativeSectionCoordinates_inPatch V.presentation t ht j.2 x).mpr hj.2
  have hg : DivisorClass.Chern.Holomorphic.OpenExtension.holomorphicOpenExtend (A.gauge j).val x ≠ 0 := by
    rw [DivisorClass.Chern.Holomorphic.OpenExtension.holomorphicOpenExtend_apply (A.gauge j).val x hj]
    exact DivisorClass.Chern.Holomorphic.SlitLog.holomorphicUnit_value_ne_zero (A.gauge j) ⟨x, hj⟩
  change (A.map.left (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x) ∈
    SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ)
      (ProjectiveLocalVectors.comparisonCoordinateEquiv n m (.inl i.1)) (ProjectiveLocalVectors.comparisonCoordinateEquiv n m (.inr i.2))) ↔ _
  rw [SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_eq]
  change ((ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map A.map x).left (default : Foundations.Scheme.ProjectiveSpace.complexBase) ∈
      Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (n + m + 1) (ProjectiveLocalVectors.comparisonCoordinateEquiv n m (.inl i.1)) ∧
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map A.map x).left (default : Foundations.Scheme.ProjectiveSpace.complexBase) ∈
      Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (n + m + 1) (ProjectiveLocalVectors.comparisonCoordinateEquiv n m (.inr i.2))) ↔ _
  rw [A.map_value j x hj, ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint_mem_coordinateOpen,
    ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint_mem_coordinateOpen, Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_mk_iff, Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_mk_iff]
  change (ProjectiveLocalVectors.projectiveComparisonVector p q j (DivisorClass.Chern.Holomorphic.OpenExtension.holomorphicOpenExtend (A.gauge j).val x)
      (ProjectiveLocalVectors.comparisonCoordinateEquiv n m (.inl i.1)) ≠ 0 ∧
    ProjectiveLocalVectors.projectiveComparisonVector p q j (DivisorClass.Chern.Holomorphic.OpenExtension.holomorphicOpenExtend (A.gauge j).val x)
      (ProjectiveLocalVectors.comparisonCoordinateEquiv n m (.inr i.2)) ≠ 0) ↔ _
  rw [ProjectiveLocalVectors.projectiveComparisonVector_left, ProjectiveLocalVectors.projectiveComparisonVector_right, div_ne_zero_iff,
    and_iff_left hg, ← Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_iff_ratio_ne_zero j.1 i.1 p hpj,
    ← Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_iff_ratio_ne_zero j.2 i.2 q hqj]
  exact and_congr (Intrinsic.SectionCoordinates.nativeSectionCoordinates_inPatch V.presentation s hs i.1 x)
    (Intrinsic.SectionCoordinates.nativeSectionCoordinates_inPatch V.presentation t ht i.2 x)

theorem SectionComparisonVectors.SectionComparisonAlgebraization.regularOpen_eq (i : Fin (n + 1) × Fin (m + 1)) :
    A.regularOpen i = HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i.1) ⊓ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (t i.2) := by
  apply RepresentationTheory.Theta.Geometric.Complex.PointsDetectSections.opens_eq_of_complex_points V.toOver
  intro x
  exact A.regularOpen_mem i x

theorem SectionComparisonVectors.SectionComparisonAlgebraization.regularOpen_covers : iSup A.regularOpen = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨i, hi⟩ := hs x
  obtain ⟨j, hj⟩ := ht x
  apply Opens.mem_iSup.mpr
  refine ⟨(i, j), ?_⟩
  rw [A.regularOpen_eq]
  exact ⟨hi, hj⟩

end

/-! The enlarged algebraic projective map supplies genuine regular
units whose native values are the inverse holomorphic comparison gauges. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates
open scoped _root_.Manifold ContDiff

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {L K : HilbertConstruction.Line.Bundles.LineBundle V.carrier} {n m : ℕ}
    {s : Fin (n + 1) → (HilbertConstruction.Line.Bundles.structureModule V.carrier ⟶ L.sheaf)}
    {t : Fin (m + 1) → (HilbertConstruction.Line.Bundles.structureModule V.carrier ⟶ K.sheaf)}
    {hs : ∀ x : V.carrier, ∃ i, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)}
    {ht : ∀ x : V.carrier, ∃ j, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (t j)}
    (A : SectionComparisonVectors.SectionComparisonAlgebraization V s t hs ht)

def SectionComparisonVectors.SectionComparisonAlgebraization.regularUnit (i : Fin (n + 1) × Fin (m + 1)) : Γ(V.carrier, A.regularOpen i)ˣ :=
  RepresentationTheory.Theta.Geometric.PowerGauge.projectivePullbackTransitionUnit A.map.left
    (ProjectiveLocalVectors.comparisonCoordinateEquiv n m (.inl i.1)) (ProjectiveLocalVectors.comparisonCoordinateEquiv n m (.inr i.2))

theorem SectionComparisonVectors.SectionComparisonAlgebraization.regularUnit_value (i : Fin (n + 1) × Fin (m + 1)) (x : V.analyticSpace)
    (hi : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ A.regularOpen i) :
    RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue x.left (A.regularOpen i) hi (A.regularUnit i : Γ(V.carrier, A.regularOpen i)) =
      1 / (A.gauge i).val ⟨x, (A.regularOpen_mem i x).mp hi⟩ := by
  have hx := (A.regularOpen_mem i x).mp hi
  have h := RepresentationTheory.Theta.Geometric.PowerGauge.projectivePullbackTransitionUnit_value A.map x _ (A.map_value i x hx)
    (ProjectiveLocalVectors.comparisonCoordinateEquiv n m (.inl i.1)) (ProjectiveLocalVectors.comparisonCoordinateEquiv n m (.inr i.2)) hi
  refine h.trans ?_
  change ProjectiveLocalVectors.projectiveComparisonVector (Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver s hs x)
      (Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver t ht x) i (DivisorClass.Chern.Holomorphic.OpenExtension.holomorphicOpenExtend (A.gauge i).val x)
      (ProjectiveLocalVectors.comparisonCoordinateEquiv n m (.inr i.2)) /
    ProjectiveLocalVectors.projectiveComparisonVector (Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver s hs x)
      (Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver t ht x) i (DivisorClass.Chern.Holomorphic.OpenExtension.holomorphicOpenExtend (A.gauge i).val x)
      (ProjectiveLocalVectors.comparisonCoordinateEquiv n m (.inl i.1)) = _
  rw [ProjectiveLocalVectors.projectiveComparisonVector_left, ProjectiveLocalVectors.projectiveComparisonVector_right,
    show Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i.1 i.1 (Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver s hs x) = 1 from
      (Intrinsic.SectionCoordinates.nativeSectionCoordinates_inPatch V.presentation s hs i.1 x).mpr hx.1,
    show Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i.2 i.2 (Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver t ht x) = 1 from
      (Intrinsic.SectionCoordinates.nativeSectionCoordinates_inPatch V.presentation t ht i.2 x).mpr hx.2,
    div_one, DivisorClass.Chern.Holomorphic.OpenExtension.holomorphicOpenExtend_apply (A.gauge i).val x hx]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
