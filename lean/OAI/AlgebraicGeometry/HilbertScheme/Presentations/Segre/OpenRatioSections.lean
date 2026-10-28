import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Segre.ChartRatioIdentity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ProjectionPreimages

/-! # Open Ratio Sections -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Segre.OpenRatioSections

noncomputable section

/-! Regular ratio sections on the actual open subschemes of the
Segre equation scheme, with no reducedness assumption. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ProjectionPreimages

universe u
variable (R : CommRingCat.{u}) {n m : ℕ} (p : AbelianModuli.HilbertConstruction.Segre.ChartProjections.SegreProjectiveIndex.{u} n m)

abbrev segreCoordinateOpen : (AbelianModuli.HilbertConstruction.Segre.ProductComparison.segreEquationScheme R n m).Opens :=
  Proj.basicOpen (AbelianModuli.HilbertConstruction.Segre.ChartCoordinates.segreQuotientGrading R) (AbelianModuli.HilbertConstruction.Segre.ChartCoordinates.segreVariable R p).val

theorem segreCoordinateOpen_le_row :
    segreCoordinateOpen R p ≤ AbelianModuli.HilbertConstruction.Segre.ProjectionGluing.segreRowProjection R n m ⁻¹ᵁ
      Proj.basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) (X p.1.down) :=
  (AbelianModuli.HilbertConstruction.Segre.ProjectionPreimages.segreProjections_preimage R p).ge.trans inf_le_left

theorem segreCoordinateOpen_le_column :
    segreCoordinateOpen R p ≤ AbelianModuli.HilbertConstruction.Segre.ProjectionGluing.segreColumnProjection R n m ⁻¹ᵁ
      Proj.basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R m) (X p.2.down) :=
  (AbelianModuli.HilbertConstruction.Segre.ProjectionPreimages.segreProjections_preimage R p).ge.trans inf_le_right

theorem segreChart_top_le_coordinateOpen :
    ⊤ ≤ (AbelianModuli.HilbertConstruction.Segre.ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left ⁻¹ᵁ segreCoordinateOpen R p := by
  change ⊤ ≤ (Proj.awayι (AbelianModuli.HilbertConstruction.Segre.ChartCoordinates.segreQuotientGrading R) (AbelianModuli.HilbertConstruction.Segre.ChartCoordinates.segreVariable R p).val
    (AbelianModuli.HilbertConstruction.Segre.ChartCoordinates.segreVariable R p).property Nat.zero_lt_one) ⁻¹ᵁ segreCoordinateOpen R p
  rw [show segreCoordinateOpen R p =
    (Proj.awayι (AbelianModuli.HilbertConstruction.Segre.ChartCoordinates.segreQuotientGrading R) (AbelianModuli.HilbertConstruction.Segre.ChartCoordinates.segreVariable R p).val
      (AbelianModuli.HilbertConstruction.Segre.ChartCoordinates.segreVariable R p).property Nat.zero_lt_one).opensRange from
        (Proj.opensRange_awayι _ _ _ _).symm, Scheme.Hom.preimage_opensRange]

def segreRowRatioSection (a : Fin (n + 1)) : Γ(AbelianModuli.HilbertConstruction.Segre.ProductComparison.segreEquationScheme R n m, segreCoordinateOpen R p) :=
  (AbelianModuli.HilbertConstruction.Segre.ProjectionGluing.segreRowProjection R n m).appLE (Proj.basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) (X p.1.down))
    (segreCoordinateOpen R p) (segreCoordinateOpen_le_row R p)
    (Proj.awayToSection (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) (X p.1.down) (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p.1.down (X a)))

def segreColumnRatioSection (b : Fin (m + 1)) : Γ(AbelianModuli.HilbertConstruction.Segre.ProductComparison.segreEquationScheme R n m, segreCoordinateOpen R p) :=
  (AbelianModuli.HilbertConstruction.Segre.ProjectionGluing.segreColumnProjection R n m).appLE (Proj.basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R m) (X p.2.down))
    (segreCoordinateOpen R p) (segreCoordinateOpen_le_column R p)
    (Proj.awayToSection (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R m) (X p.2.down) (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p.2.down (X b)))

def segreAmbientRatioSection (q : AbelianModuli.HilbertConstruction.Segre.ChartProjections.SegreProjectiveIndex.{u} n m) :
    Γ(AbelianModuli.HilbertConstruction.Segre.ProductComparison.segreEquationScheme R n m, segreCoordinateOpen R p) :=
  (AbelianModuli.HilbertConstruction.Segre.ProjectiveScheme.segreProjectiveInclusion R).appLE
    (Proj.basicOpen (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (AbelianModuli.HilbertConstruction.Segre.ChartProjections.SegreProjectiveIndex.{u} n m) R) (X p))
    (segreCoordinateOpen R p) le_rfl
    (Proj.awayToSection (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (AbelianModuli.HilbertConstruction.Segre.ChartProjections.SegreProjectiveIndex.{u} n m) R) (X p)
      (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p (X q)))

theorem segreChart_appLE_injective : Function.Injective
    ((AbelianModuli.HilbertConstruction.Segre.ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left.appLE (segreCoordinateOpen R p) ⊤
      (segreChart_top_le_coordinateOpen R p)) := by
  let j := (AbelianModuli.HilbertConstruction.Segre.ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left
  let e := Proj.basicOpenIsoAway (AbelianModuli.HilbertConstruction.Segre.ChartCoordinates.segreQuotientGrading R) (AbelianModuli.HilbertConstruction.Segre.ChartCoordinates.segreVariable R p).val
    (AbelianModuli.HilbertConstruction.Segre.ChartCoordinates.segreVariable R p).property Nat.zero_lt_one
  have he : IsIso (e.hom ≫ j.appLE (segreCoordinateOpen R p) ⊤
      (segreChart_top_le_coordinateOpen R p)) := by
    have h := Projective.ChartSectionPullback.projectiveChart_pullback_section (AbelianModuli.HilbertConstruction.Segre.ChartCoordinates.segreQuotientGrading R)
      (AbelianModuli.HilbertConstruction.Segre.ChartCoordinates.segreVariable R p).property Nat.zero_lt_one (segreChart_top_le_coordinateOpen R p)
    exact h.symm ▸ inferInstanceAs (IsIso (Scheme.ΓSpecIso
      (CommRingCat.of (AbelianModuli.HilbertConstruction.Segre.ProjectiveCharts.SegreHomogeneousChart R p.1 p.2))).inv)
  let : IsIso (j.appLE (segreCoordinateOpen R p) ⊤ (segreChart_top_le_coordinateOpen R p)) :=
    (isIso_comp_left_iff e.hom _).mp he
  exact (ConcreteCategory.bijective_of_isIso _).1

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Segre.OpenRatioSections
