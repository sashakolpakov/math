import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectiveCoordinatePullback

/-! # Quotient Coordinate Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.QuotientCoordinatePullback

noncomputable section

/-! A factorization of the section-defined projective map through a homogeneous quotient preserves both coordinate opens and their actual ratio functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

variable {X S : Scheme.{u}} {M : X.Modules} {n : ℕ} (f : X ⟶ S)
variable (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ M))
variable (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
variable (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading Γ(S, ⊤) n)) (m : X ⟶ Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))
variable (hm : m ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I = SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs)

include hm

theorem sectionQuotient_coordinate_preimage (i : Fin (n + 1)) :
    m ⁻¹ᵁ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i} = Ample.LineBundles.sectionNonvanishing (s i) := by
  have he := congrArg (fun U => m ⁻¹ᵁ U) (Quotient.CoordinatePullback.projectiveQuotient_coordinate_preimage I i)
  have hf := congrArg (fun q : X ⟶ Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading Γ(S, ⊤) n) =>
    q ⁻¹ᵁ Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading Γ(S, ⊤) n) (MvPolynomial.X i)) hm
  exact he.symm.trans (hf.trans (ProjectiveChart.Preimages.sectionAbsoluteMorphism_preimage f s hs i))

theorem sectionQuotient_coordinate_pullback (i j : Fin (n + 1)) (V : X.Opens)
    (hV : V ≤ m ⁻¹ᵁ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i})
    (hsi : V ≤ Ample.LineBundles.sectionNonvanishing (s i)) :
    Open.SectionPullback.openSectionPullback m (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}) V hV
      (Coordinate.RatioSections.coordinateRatioSection I {i} i j (Finset.mem_singleton_self i)) =
      ComponentRatios.sectionComponentRatio (s i) (s j) V hsi := by
  let U := Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading Γ(S, ⊤) n) (MvPolynomial.X i)
  have hq := (Quotient.CoordinatePullback.projectiveQuotient_coordinate_preimage I i).ge
  have hmq : V ≤ (m ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I) ⁻¹ᵁ U :=
    hV.trans ((TopologicalSpace.Opens.map m.base).monotone hq)
  have hms : V ≤ SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs ⁻¹ᵁ U := by
    rw [ProjectiveChart.Preimages.sectionAbsoluteMorphism_preimage]
    exact hsi
  have he := Open.SectionPullbackComposition.openSectionPullback_comp m (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I) U
    (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}) V hq hV hmq (Quotient.CoordinatePullback.projectiveCoordinateFunction Γ(S, ⊤) i j)
  have hcoord := congrArg (Open.SectionPullback.openSectionPullback m (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}) V hV)
    (Quotient.CoordinatePullback.projectiveQuotient_coordinate_pullback I i j hq)
  exact hcoord.symm.trans (he.trans ((Open.SectionPullbackComposition.openSectionPullback_congr hm U V hmq hms _).trans
    (ProjectiveCoordinatePullback.sectionAbsoluteMorphism_coordinate_pullback f s hs i j V hsi hms)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.QuotientCoordinatePullback
