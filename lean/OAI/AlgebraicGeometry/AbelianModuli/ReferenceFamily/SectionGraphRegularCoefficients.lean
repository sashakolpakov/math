import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SectionGraphNe
import OAI.RepresentationTheory.Theta.Geometric.FrameCoordinates
import OAI.RepresentationTheory.Theta.Geometric.Complex.PointsDetectSections

/-! # Section Graph Regular Coefficients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The algebraic graph map recovers its holomorphic section
coefficients as actual regular sections on the original common frame
cover. Only a first-block coordinate is used as denominator. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates
open scoped _root_.Manifold ContDiff

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {L K : HilbertConstruction.Line.Bundles.LineBundle V.carrier} {n m : ℕ}
    {s : Fin (n + 1) → (HilbertConstruction.Line.Bundles.structureModule V.carrier ⟶ L.sheaf)}
    {t : Fin (m + 1) → (HilbertConstruction.Line.Bundles.structureModule V.carrier ⟶ K.sheaf)}
    {hs : ∀ x : V.carrier, ∃ i, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)}
    {ht : ∀ x : V.carrier, ∃ j, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (t j)}
    {c : ∀ i, DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel) (M := SectionComparisonGauges.sectionComparisonOpen V s t i)}
    (A : SectionGraphNe.SectionGraphAlgebraization V s t hs ht c)

local instance SectionGraphNe.SectionGraphAlgebraization.graphRegularCoefficients_integral : IsIntegral V.toOver.left := V.property
local instance SectionGraphNe.SectionGraphAlgebraization.graphRegularCoefficients_smooth : Smooth V.toOver.hom := V.presentation.smooth

def SectionGraphNe.SectionGraphAlgebraization.coordinateOpen (i : Fin (n + 1)) : V.carrier.Opens :=
  A.map.left ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (n + m + 1) (ProjectiveLocalVectors.comparisonCoordinateEquiv n m (.inl i))

theorem SectionGraphNe.SectionGraphAlgebraization.coordinateOpen_mem (i : Fin (n + 1)) (x : V.analyticSpace) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ A.coordinateOpen i ↔
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i) := by
  obtain ⟨j, hj⟩ := SectionComparisonGauges.sectionComparisonOpen_covers V s t hs ht x
  let p := Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver s hs x
  let q := Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver t ht x
  have hpj : Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch j.1 p := (Intrinsic.SectionCoordinates.nativeSectionCoordinates_inPatch V.presentation s hs j.1 x).mpr hj.1
  change (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map A.map x).left (default : Foundations.Scheme.ProjectiveSpace.complexBase) ∈
    Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (n + m + 1) (ProjectiveLocalVectors.comparisonCoordinateEquiv n m (.inl i)) ↔ _
  rw [A.map_value j x hj, ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint_mem_coordinateOpen, Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_mk_iff]
  change ProjectiveLocalVectors.projectiveSectionVector p q j (DivisorClass.Chern.Holomorphic.OpenExtension.holomorphicOpenExtend (c j) x)
    (ProjectiveLocalVectors.comparisonCoordinateEquiv n m (.inl i)) ≠ 0 ↔ _
  rw [ProjectiveLocalVectors.projectiveSectionVector_left, ← Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_iff_ratio_ne_zero j.1 i p hpj]
  exact Intrinsic.SectionCoordinates.nativeSectionCoordinates_inPatch V.presentation s hs i x

theorem SectionGraphNe.SectionGraphAlgebraization.coordinateOpen_eq (i : Fin (n + 1)) :
    A.coordinateOpen i = HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i) := by
  apply RepresentationTheory.Theta.Geometric.Complex.PointsDetectSections.opens_eq_of_complex_points V.toOver
  exact A.coordinateOpen_mem i

def SectionGraphNe.SectionGraphAlgebraization.regularOpen (_A : SectionGraphNe.SectionGraphAlgebraization V s t hs ht c)
    (i : Fin (n + 1) × Fin (m + 1)) : V.carrier.Opens :=
  HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i.1) ⊓ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (t i.2)

theorem SectionGraphNe.SectionGraphAlgebraization.regularOpen_le_coordinateOpen (i : Fin (n + 1) × Fin (m + 1)) :
    A.regularOpen i ≤ A.coordinateOpen i.1 := by
  rw [A.coordinateOpen_eq]
  exact inf_le_left

theorem SectionGraphNe.SectionGraphAlgebraization.regularOpen_covers : iSup A.regularOpen = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨i, hi⟩ := hs x
  obtain ⟨j, hj⟩ := ht x
  exact Opens.mem_iSup.mpr ⟨(i, j), hi, hj⟩

def SectionGraphNe.SectionGraphAlgebraization.regularCoefficient (i : Fin (n + 1) × Fin (m + 1)) : Γ(V.carrier, A.regularOpen i) :=
  V.carrier.presheaf.map (homOfLE (A.regularOpen_le_coordinateOpen i)).op
    (A.map.left.app (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (n + m + 1) (ProjectiveLocalVectors.comparisonCoordinateEquiv n m (.inl i.1)))
      (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := ℂ)
        (ProjectiveLocalVectors.comparisonCoordinateEquiv n m (.inl i.1)) (ProjectiveLocalVectors.comparisonCoordinateEquiv n m (.inr i.2))))

theorem SectionGraphNe.SectionGraphAlgebraization.regularCoefficient_value (i : Fin (n + 1) × Fin (m + 1)) (x : V.analyticSpace)
    (hi : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ A.regularOpen i) :
    RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue x.left (A.regularOpen i) hi (A.regularCoefficient i) = c i ⟨x, hi⟩ := by
  let v := SectionGraphNe.sectionGraphVector V s t hs ht c i x
  let hn := SectionGraphNe.sectionGraphVector_ne_zero V s t hs ht c i x hi
  let p := Projectivization.mk ℂ v hn
  have hv : v (ProjectiveLocalVectors.comparisonCoordinateEquiv n m (.inl i.1)) = 1 :=
    (ProjectiveLocalVectors.projectiveSectionVector_left _ _ i _ i.1).trans
      ((Intrinsic.SectionCoordinates.nativeSectionCoordinates_inPatch V.presentation s hs i.1 x).mpr hi.1)
  have hp : Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch (ProjectiveLocalVectors.comparisonCoordinateEquiv n m (.inl i.1)) p :=
    (Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_mk_iff _ v hn).mpr (by rw [hv]; exact one_ne_zero)
  have hr := RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue_restrict x.left (A.coordinateOpen i.1) (A.regularOpen i)
    (A.regularOpen_le_coordinateOpen i) hi
    (A.map.left.app (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (n + m + 1) (ProjectiveLocalVectors.comparisonCoordinateEquiv n m (.inl i.1)))
      (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := ℂ)
        (ProjectiveLocalVectors.comparisonCoordinateEquiv n m (.inl i.1)) (ProjectiveLocalVectors.comparisonCoordinateEquiv n m (.inr i.2))))
  have h := RepresentationTheory.Theta.Geometric.FrameCoordinates.projective_pullback_localEquation_value A.map x p (A.map_value i x hi)
    (ProjectiveLocalVectors.comparisonCoordinateEquiv n m (.inl i.1)) (ProjectiveLocalVectors.comparisonCoordinateEquiv n m (.inr i.2)) hp
      (A.regularOpen_le_coordinateOpen i hi)
  refine hr.trans (h.trans ?_)
  change v (ProjectiveLocalVectors.comparisonCoordinateEquiv n m (.inr i.2)) / v (ProjectiveLocalVectors.comparisonCoordinateEquiv n m (.inl i.1)) = _
  rw [hv, div_one]
  change ProjectiveLocalVectors.projectiveSectionVector _ _ i (DivisorClass.Chern.Holomorphic.OpenExtension.holomorphicOpenExtend (c i) x)
    (ProjectiveLocalVectors.comparisonCoordinateEquiv n m (.inr i.2)) = _
  rw [ProjectiveLocalVectors.projectiveSectionVector_right,
    show Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i.2 i.2 (Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver t ht x) = 1 from
      (Intrinsic.SectionCoordinates.nativeSectionCoordinates_inPatch V.presentation t ht i.2 x).mpr hi.2,
    one_mul, DivisorClass.Chern.Holomorphic.OpenExtension.holomorphicOpenExtend_apply (c i) x hi]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
