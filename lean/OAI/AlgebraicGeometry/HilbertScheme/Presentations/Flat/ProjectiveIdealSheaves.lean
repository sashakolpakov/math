import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.QuotientStructure
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.Coordinates

/-! # Projective Ideal Sheaves -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ProjectiveIdealSheaves.GradedHilbert

noncomputable section

/-! Flat projective closed subschemes have eventually finite projective coordinate modules. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

def projectiveIdealSheafIso (J : (Proj (Hilbert.Polynomial.GradedHilbert.grading R n)).IdealSheafData) :
    Presentations.Projective.Quotient.GradedHilbert.projectiveQuotient (ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf J) ≅ J.subscheme := by
  let i := Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf J)
  have h : J.subschemeι.ker = i.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact (Presentations.Projective.IdealEquivalence.GradedHilbert.projectiveQuotient_homogeneousIdealOfSheaf J).symm
  let : IsIso (IsClosedImmersion.lift J.subschemeι i h.le) :=
    IsClosedImmersion.isIso_lift J.subschemeι i h
  exact asIso (IsClosedImmersion.lift J.subschemeι i h.le)

theorem projectiveIdealSheafIso_hom_ι (J : (Proj (Hilbert.Polynomial.GradedHilbert.grading R n)).IdealSheafData) :
    (projectiveIdealSheafIso J).hom ≫ J.subschemeι =
      Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf J) :=
  IsClosedImmersion.lift_fac _ _ _

def projectiveIdealSheafStructure (J : (Proj (Hilbert.Polynomial.GradedHilbert.grading R n)).IdealSheafData) :
    J.subscheme ⟶ Spec (CommRingCat.of R) :=
  J.subschemeι ≫ Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading R n)

theorem projectiveIdealSheafIso_hom_structure (J : (Proj (Hilbert.Polynomial.GradedHilbert.grading R n)).IdealSheafData) :
    (projectiveIdealSheafIso J).hom ≫ projectiveIdealSheafStructure J =
      Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf J)) := by
  rw [projectiveIdealSheafStructure, ← Category.assoc, projectiveIdealSheafIso_hom_ι,
    Presentations.Projective.QuotientStructure.GradedHilbert.projectiveQuotientInclusion_structure]

theorem projectiveIdealSheaf_flat_iff [IsNoetherianRing R]
    (J : (Proj (Hilbert.Polynomial.GradedHilbert.grading R n)).IdealSheafData) :
    Flat (projectiveIdealSheafStructure J) ↔
      ∃ N : ℕ, ∀ d ≥ N, Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf J).toIdeal d) := by
  constructor
  · intro h
    let : Flat (projectiveIdealSheafStructure J) := h
    have hflat : Flat ((projectiveIdealSheafIso J).hom ≫ projectiveIdealSheafStructure J) :=
      Flat.comp _ _
    rw [projectiveIdealSheafIso_hom_structure] at hflat
    exact (ProjectiveCoordinatePieces.GradedHilbert.projectiveQuotient_flat_iff_eventual_coordinatePieces_flat _).mp hflat
  · intro h
    let hflat : Flat (Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf J))) :=
      (ProjectiveCoordinatePieces.GradedHilbert.projectiveQuotient_flat_iff_eventual_coordinatePieces_flat _).mpr h
    have he : projectiveIdealSheafStructure J = (projectiveIdealSheafIso J).inv ≫
        Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf J)) := by
      rw [← projectiveIdealSheafIso_hom_structure, Iso.inv_hom_id_assoc]
    rw [he]
    exact Flat.comp (projectiveIdealSheafIso J).inv _ (hg := hflat)

theorem projectiveIdealSheaf_eventual_projective [IsNoetherianRing R]
    (J : (Proj (Hilbert.Polynomial.GradedHilbert.grading R n)).IdealSheafData) [Flat (projectiveIdealSheafStructure J)] :
    ∃ N : ℕ, ∀ d ≥ N,
      Module.Projective R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf J).toIdeal d) := by
  obtain ⟨N, hN⟩ := (projectiveIdealSheaf_flat_iff J).mp inferInstance
  refine ⟨N, fun d hd => ?_⟩
  let : Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf J).toIdeal d) := hN d hd
  exact Relative.Coordinates.GradedHilbert.degreeQuotient_projective_of_flat (ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf J) d

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ProjectiveIdealSheaves.GradedHilbert
