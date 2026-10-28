import OAI.AlgebraicGeometry.Resolution.Blowups.ClosedProjectiveIdealGenerators

/-! # Projective Section Overlap -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ProjectiveSectionOverlap.Construction

noncomputable section

/-! The common unit relating homogeneous center equations on projective overlaps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

theorem projective_overlap_coordinate_isUnit (i j : Fin (n + 1)) :
    IsUnit (HilbertScheme.Presentations.Projective.ChartOverlap.GradedHilbert.chartOverlapRight (R := R) i j (HilbertScheme.Presentations.Dehomogenization.GradedHilbert.dehomogenize j (X i))) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨HilbertScheme.Presentations.Projective.ChartOverlap.GradedHilbert.chartOverlapLeft i j (HilbertScheme.Presentations.Dehomogenization.GradedHilbert.dehomogenize i (X j)), ?_⟩
  have h := HilbertScheme.Presentations.Projective.ChartOverlap.GradedHilbert.homogeneous_chart_overlap i j (isHomogeneous_X R j)
  simpa only [HilbertScheme.Presentations.Dehomogenization.GradedHilbert.dehomogenize_self, map_one, pow_one] using h.symm

/-- A dehomogenized form as a genuine regular section on the projective chart. -/
def projectiveFormSection (i : Fin (n + 1)) (p : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) :
    Γ(Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n), Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i)) :=
  (Proj.awayToSection (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i)) (HilbertScheme.Presentations.Dehomogenization.GradedHilbert.dehomogenize i p)

def projectiveOverlapLeftRestriction (i j : Fin (n + 1)) :
    Γ(Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n), Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i)) →+*
      Γ(Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n), Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i * X j)) :=
  ((Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)).presheaf.map
    (homOfLE (Proj.basicOpen_mono (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i) (X i * X j) ⟨X j, rfl⟩)).op).hom

def projectiveOverlapRightRestriction (i j : Fin (n + 1)) :
    Γ(Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n), Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X j)) →+*
      Γ(Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n), Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i * X j)) :=
  ((Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)).presheaf.map
    (homOfLE (Proj.basicOpen_mono (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X j) (X i * X j)
      ⟨X i, mul_comm _ _⟩)).op).hom

theorem projectiveOverlapLeftRestriction_form (i j : Fin (n + 1)) (p : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) :
    projectiveOverlapLeftRestriction i j (projectiveFormSection i p) =
      (Proj.awayToSection (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i * X j)) (HilbertScheme.Presentations.Projective.ChartOverlap.GradedHilbert.chartOverlapLeft i j (HilbertScheme.Presentations.Dehomogenization.GradedHilbert.dehomogenize i p)) := by
  exact (congrArg (fun f => f (HilbertScheme.Presentations.Dehomogenization.GradedHilbert.dehomogenize i p))
    (Proj.awayMap_awayToSection (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (isHomogeneous_X R j) rfl)).symm

theorem projectiveOverlapRightRestriction_form (i j : Fin (n + 1)) (p : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) :
    projectiveOverlapRightRestriction i j (projectiveFormSection j p) =
      (Proj.awayToSection (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i * X j)) (HilbertScheme.Presentations.Projective.ChartOverlap.GradedHilbert.chartOverlapRight i j (HilbertScheme.Presentations.Dehomogenization.GradedHilbert.dehomogenize j p)) := by
  exact (congrArg (fun f => f (HilbertScheme.Presentations.Dehomogenization.GradedHilbert.dehomogenize j p))
    (Proj.awayMap_awayToSection (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (isHomogeneous_X R i) (mul_comm (X i) (X j)))).symm

/-- The change between the two chart equations is multiplication by the
same coordinate unit raised to the common degree. -/
theorem projectiveFormSection_overlap (i j : Fin (n + 1))
    {p : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n} {d : ℕ} (hp : p.IsHomogeneous d) :
    projectiveOverlapRightRestriction i j (projectiveFormSection j p) =
      projectiveOverlapRightRestriction i j (projectiveFormSection j (X i)) ^ d *
        projectiveOverlapLeftRestriction i j (projectiveFormSection i p) := by
  rw [projectiveOverlapRightRestriction_form, projectiveOverlapRightRestriction_form,
    projectiveOverlapLeftRestriction_form, HilbertScheme.Presentations.Projective.ChartOverlap.GradedHilbert.homogeneous_chart_overlap i j hp]
  exact map_mul _ _ _ |>.trans (congrArg₂ (· * ·) (map_pow _ _ _) rfl)

theorem projectiveFormSection_overlap_isUnit (i j : Fin (n + 1)) :
    IsUnit (projectiveOverlapRightRestriction (R := R) i j (projectiveFormSection j (X i))) := by
  rw [projectiveOverlapRightRestriction_form]
  exact (projective_overlap_coordinate_isUnit i j).map
    (Proj.awayToSection (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i * X j)).hom

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ProjectiveSectionOverlap.Construction
