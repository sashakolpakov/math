import OAI.AlgebraicGeometry.Resolution.Blowups.ProjectiveIdealGenerators
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Closed Projective Ideal Generators -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ClosedProjectiveIdealGenerators.Construction

noncomputable section

/-! Common-degree center equations on an actual closed projective subscheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
variable {X : Scheme.{u}} (e : X ⟶ Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) [IsClosedImmersion e]

/-- The actual affine preimage of a standard projective chart. -/
def closedProjectiveAffineOpen (i : Fin (n + 1)) : X.affineOpens :=
  ⟨e ⁻¹ᵁ Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (MvPolynomial.X i),
    (Proj.isAffineOpen_basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (MvPolynomial.X i)
      (isHomogeneous_X R i) Nat.zero_lt_one).preimage e⟩

/-- Dehomogenization followed by restriction to the closed subscheme. -/
def closedProjectiveDehomogenize (i : Fin (n + 1)) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n →+* Γ(X, closedProjectiveAffineOpen e i) :=
  (e.app (Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (MvPolynomial.X i))).hom.comp
    ((Proj.awayToSection (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (MvPolynomial.X i)).hom.comp (HilbertScheme.Presentations.Dehomogenization.GradedHilbert.dehomogenize i))

omit [IsNoetherianRing R] in
theorem closedProjectiveDehomogenize_generates (J : X.IdealSheafData)
    {ι : Type*} (p : ι → HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (i : Fin (n + 1))
    (hp : Ideal.span (Set.range (fun j => HilbertScheme.Presentations.Dehomogenization.GradedHilbert.dehomogenize i (p j))) =
      HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.projectiveChartIdeal (J.map e) i) :
    Ideal.span (Set.range (fun j => closedProjectiveDehomogenize e i (p j))) =
      J.ideal (closedProjectiveAffineOpen e i) := by
  let U : (Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)).affineOpens :=
    ⟨Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (MvPolynomial.X i),
      Proj.isAffineOpen_basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (MvPolynomial.X i)
        (isHomogeneous_X R i) Nat.zero_lt_one⟩
  let φ := (Proj.awayToSection (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (MvPolynomial.X i)).hom
  let ψ := (e.app U).hom
  have hφ : Function.Surjective φ :=
    (Proj.basicOpenIsoAway (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (MvPolynomial.X i)
      (isHomogeneous_X R i) Nat.zero_lt_one).commRingCatIsoToRingEquiv.surjective
  have hψ : Function.Surjective ψ := e.app_surjective U U.2
  have he : ((HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.projectiveChartIdeal (J.map e) i).map φ).map ψ =
      J.ideal (closedProjectiveAffineOpen e i) := by
    change (((J.map e).ideal U).comap φ |>.map φ).map ψ = _
    rw [Ideal.map_comap_of_surjective φ hφ,
      Scheme.IdealSheafData.ideal_map_of_isAffineHom J e U,
      Ideal.map_comap_of_surjective ψ hψ]
    rfl
  rw [← he, ← hp, Ideal.map_span, Ideal.map_span]
  congr 1
  rw [← Set.range_comp, ← Set.range_comp]
  rfl

/-- Every center ideal on a closed projective subscheme has a single
finite homogeneous generating family of one positive degree on all charts. -/
theorem closedProjective_idealSheaf_exists_common_degree_generators
    (J : X.IdealSheafData) :
    ∃ (m D : ℕ) (p : Fin (m + 1) → HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n),
      0 < D ∧ (∀ j, (p j).IsHomogeneous D) ∧
        ∀ i : Fin (n + 1),
          Ideal.span (Set.range (fun j => closedProjectiveDehomogenize e i (p j))) =
            J.ideal (closedProjectiveAffineOpen e i) := by
  obtain ⟨m, D, p, hD, hhom, hgen⟩ :=
    ProjectiveIdealGenerators.Construction.projective_idealSheaf_exists_fin_common_degree_generators (J.map e)
  exact ⟨m, D, p, hD, hhom, fun i =>
    closedProjectiveDehomogenize_generates e J p i (hgen i)⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ClosedProjectiveIdealGenerators.Construction
