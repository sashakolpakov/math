import OAI.AlgebraicGeometry.Resolution.Blowups.ProjectiveSectionOverlap
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Functor

/-! # Closed Projective Section Overlap -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ClosedProjectiveSectionOverlap.Construction

noncomputable section

/-! Common-degree transition units after restriction to the projective subscheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

variable {R : Type u} [CommRing R] {n : ℕ} {X : Scheme.{u}}
variable (e : X ⟶ Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) [IsClosedImmersion e]

/-- Restriction of a pulled-back chart form to an arbitrary smaller affine open. -/
theorem closedProjectiveDehomogenize_restrict {W : X.affineOpens} (i : Fin (n + 1))
    (hWi : W ≤ ClosedProjectiveIdealGenerators.Construction.closedProjectiveAffineOpen e i) (p : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) :
    Blowup.Functor.Construction.affineRestriction hWi (ClosedProjectiveIdealGenerators.Construction.closedProjectiveDehomogenize e i p) =
      e.appLE (Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (MvPolynomial.X i)) W hWi
        (ProjectiveSectionOverlap.Construction.projectiveFormSection i p) := rfl

/-- On any affine open inside two projective charts, the two families of
degree-`D` equations differ by one common unit. -/
theorem closedProjective_forms_common_unit {W : X.affineOpens}
    (i j : Fin (n + 1)) (hWi : W ≤ ClosedProjectiveIdealGenerators.Construction.closedProjectiveAffineOpen e i)
    (hWj : W ≤ ClosedProjectiveIdealGenerators.Construction.closedProjectiveAffineOpen e j) (D : ℕ) :
    ∃ u : Γ(X, W), IsUnit u ∧
      ∀ p : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n, p.IsHomogeneous D →
        Blowup.Functor.Construction.affineRestriction hWj (ClosedProjectiveIdealGenerators.Construction.closedProjectiveDehomogenize e j p) =
          u * Blowup.Functor.Construction.affineRestriction hWi (ClosedProjectiveIdealGenerators.Construction.closedProjectiveDehomogenize e i p) := by
  let V := Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (MvPolynomial.X i * MvPolynomial.X j)
  have hWV : W.1 ≤ e ⁻¹ᵁ V := by
    dsimp only [V]
    rw [Proj.basicOpen_mul, Scheme.Hom.preimage_inf]
    exact le_inf hWi hWj
  let φ := (e.appLE V W hWV).hom
  let c := ProjectiveSectionOverlap.Construction.projectiveOverlapRightRestriction (R := R) i j
    (ProjectiveSectionOverlap.Construction.projectiveFormSection j (MvPolynomial.X i))
  have hi (p : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) :
      φ (ProjectiveSectionOverlap.Construction.projectiveOverlapLeftRestriction i j (ProjectiveSectionOverlap.Construction.projectiveFormSection i p)) =
        Blowup.Functor.Construction.affineRestriction hWi (ClosedProjectiveIdealGenerators.Construction.closedProjectiveDehomogenize e i p) := by
    rw [closedProjectiveDehomogenize_restrict]
    exact congrArg (fun f => f (ProjectiveSectionOverlap.Construction.projectiveFormSection i p))
      (e.map_appLE hWV (homOfLE
        (Proj.basicOpen_mono (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (MvPolynomial.X i)
          (MvPolynomial.X i * MvPolynomial.X j) ⟨MvPolynomial.X j, rfl⟩)).op)
  have hj (p : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) :
      φ (ProjectiveSectionOverlap.Construction.projectiveOverlapRightRestriction i j (ProjectiveSectionOverlap.Construction.projectiveFormSection j p)) =
        Blowup.Functor.Construction.affineRestriction hWj (ClosedProjectiveIdealGenerators.Construction.closedProjectiveDehomogenize e j p) := by
    rw [closedProjectiveDehomogenize_restrict]
    exact congrArg (fun f => f (ProjectiveSectionOverlap.Construction.projectiveFormSection j p))
      (e.map_appLE hWV (homOfLE
        (Proj.basicOpen_mono (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (MvPolynomial.X j)
          (MvPolynomial.X i * MvPolynomial.X j) ⟨MvPolynomial.X i, mul_comm _ _⟩)).op)
  refine ⟨φ c ^ D, ((ProjectiveSectionOverlap.Construction.projectiveFormSection_overlap_isUnit i j).map φ).pow D, ?_⟩
  intro p hp
  rw [← hj p, ProjectiveSectionOverlap.Construction.projectiveFormSection_overlap i j hp, map_mul, map_pow, hi p]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ClosedProjectiveSectionOverlap.Construction
