import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ProjectiveChartSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ProjectiveScheme
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ChartCoordinates

/-! # Target Chart Sections -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Segre.TargetChartSections

noncomputable section

/-! The ambient projective ratios of the Segre closed immersion pull
back to the actual normalized entries in each Segre chart ring. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable (R : CommRingCat.{u}) {σ τ : Type u} (p q : σ × τ)

theorem segreTargetChart_section
    (h : ⊤ ≤ ((AbelianModuli.HilbertConstruction.Segre.ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left ≫ AbelianModuli.HilbertConstruction.Segre.ProjectiveScheme.segreProjectiveInclusion R) ⁻¹ᵁ
      Proj.basicOpen (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (σ × τ) R) (X p)) :
    ((AbelianModuli.HilbertConstruction.Segre.ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left ≫ AbelianModuli.HilbertConstruction.Segre.ProjectiveScheme.segreProjectiveInclusion R).appLE
      (Proj.basicOpen (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (σ × τ) R) (X p)) ⊤ h
      (Proj.awayToSection (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (σ × τ) R) (X p) (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p (X q))) =
      (Scheme.ΓSpecIso (CommRingCat.of (AbelianModuli.HilbertConstruction.Segre.ProjectiveCharts.SegreHomogeneousChart R p.1 p.2))).inv
        (AbelianModuli.HilbertConstruction.Segre.ChartCoordinates.segreChartCoordinate R p.1 p.2 q) := by
  let I := AbelianModuli.HilbertConstruction.Segre.HomogeneousRelations.segreHomogeneousIdeal (σ := σ) (τ := τ) R
  let φ := HomogeneousLocalization.Away.map (Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I) (X p)
  have hc : (AbelianModuli.HilbertConstruction.Segre.ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left ≫ AbelianModuli.HilbertConstruction.Segre.ProjectiveScheme.segreProjectiveInclusion R =
      Spec.map (CommRingCat.ofHom φ) ≫ Proj.awayι (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (σ × τ) R) (X p)
        (isHomogeneous_X R p) Nat.zero_lt_one :=
    Proj.awayι_comp_map (Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I) (Homogeneous.Quotient.HomogeneousQuotient.irrelevant_quotient_le_map I)
      Nat.zero_lt_one (X p) (isHomogeneous_X R p)
  have h' : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (σ × τ) R) (X p) (isHomogeneous_X R p) Nat.zero_lt_one) ⁻¹ᵁ
        Proj.basicOpen (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (σ × τ) R) (X p) := hc ▸ h
  have he := Affine.ProjectiveChartSections.affineProjectiveChart_pullback_section (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (σ × τ) R)
    (isHomogeneous_X R p) Nat.zero_lt_one φ h'
  have hv := congrArg (fun k : CommRingCat.of
    (HomogeneousLocalization.Away (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (σ × τ) R) (X p)) ⟶
      Γ(Spec (CommRingCat.of (AbelianModuli.HilbertConstruction.Segre.ProjectiveCharts.SegreHomogeneousChart R p.1 p.2)), ⊤) =>
        k (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p (X q))) he
  have heval : φ (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p (X q)) = AbelianModuli.HilbertConstruction.Segre.ChartCoordinates.segreChartCoordinate R p.1 p.2 q := rfl
  change _ = (Scheme.ΓSpecIso (CommRingCat.of (AbelianModuli.HilbertConstruction.Segre.ProjectiveCharts.SegreHomogeneousChart R p.1 p.2))).inv
    (φ (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p (X q))) at hv
  rw [heval] at hv
  change (Spec.map (CommRingCat.ofHom φ) ≫
    Proj.awayι (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (σ × τ) R) (X p) (isHomogeneous_X R p) Nat.zero_lt_one).appLE
      (Proj.basicOpen (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (σ × τ) R) (X p)) ⊤ h'
      (Proj.awayToSection (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (σ × τ) R) (X p) (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p (X q))) = _ at hv
  simpa only [hc] using! hv

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Segre.TargetChartSections
