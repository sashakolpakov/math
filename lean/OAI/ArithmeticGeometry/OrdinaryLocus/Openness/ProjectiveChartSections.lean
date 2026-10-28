import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveChartFunctions
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveCoordinateRatios

/-! # Projective Chart Sections -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveChartSections.Construction

noncomputable section

/-! Coordinate-section ratios pulled back to a normalized projective chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} {T : Scheme.{u}}
attribute [local instance] MvPolynomial.gradedAlgebra

theorem projectiveChart_section_frame (c : R →+* Γ(T, ⊤))
    (v : Fin (n + 1) → Γ(T, ⊤)) (i : Fin (n + 1)) (hi : v i = 1) (j : Fin (n + 1)) :
    IsIso (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (ProjectiveChartFunctions.Construction.projectiveChartToOpen c v i hi ≫
      (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i).ι)
        (AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom (R := R) j i)) := by
  let s := AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom (R := R) j i
  let U := AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i
  have hU : U ≤ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s :=
    (AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom_nonvanishing (R := R) j i).symm.le
  have : IsIso (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.ι s) := AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.PowerLocus.pullbackSection_isIso_of_le hU s
  exact (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Nonvanishing.isIso_pullbackSection_comp_iff U.ι (ProjectiveChartFunctions.Construction.projectiveChartToOpen c v i hi) s).mp inferInstance

theorem projectiveChart_section_coordinate (c : R →+* Γ(T, ⊤))
    (v : Fin (n + 1) → Γ(T, ⊤)) (i : Fin (n + 1)) (hi : v i = 1) (j k : Fin (n + 1)) :
    let f := ProjectiveChartFunctions.Construction.projectiveChartToOpen c v i hi ≫ (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i).ι
    letI := projectiveChart_section_frame c v i hi j
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f (AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom (R := R) j i))
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f (AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom (R := R) j k)) = v k := by
  let s := AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom (R := R) j i
  let t := AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom (R := R) j k
  let U := AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i
  have hU : U ≤ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s :=
    (AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom_nonvanishing (R := R) j i).symm.le
  have : IsIso (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.ι s) := AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.PowerLocus.pullbackSection_isIso_of_le hU s
  have : IsIso (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (ProjectiveChartFunctions.Construction.projectiveChartToOpen c v i hi ≫ U.ι) s) :=
    projectiveChart_section_frame c v i hi j
  change AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (ProjectiveChartFunctions.Construction.projectiveChartToOpen c v i hi ≫ U.ι) s)
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (ProjectiveChartFunctions.Construction.projectiveChartToOpen c v i hi ≫ U.ι) t) = v k
  rw [AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.PullbackCoherence.frameCoordinate_pullbackComp, FrameCoordinatePullback.Construction.frameCoordinate_pullback_any]
  exact (congrArg (ProjectiveChartFunctions.Construction.projectiveChartToOpen c v i hi).appTop
    (ProjectiveCoordinateRatios.Construction.projective_local_frameCoordinate i j k)).trans
      (ProjectiveChartFunctions.Construction.projectiveChartToOpen_coordinate c v i hi k)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveChartSections.Construction
