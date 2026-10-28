import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Plucker.ChartAlgebra
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.Chart
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.AffinePoints

/-! # Chart -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Plucker.Chart.Grassmannian

noncomputable section

/-!
The affine schemes of the Plücker projective spectrum are naturally
isomorphic to the quotient-matrix charts of the constructed Grassmannian.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν : Type u} [Fintype ι] [DecidableEq ι]
variable (R : CommRingCat.{u}) (a : ι → ν)

def pluckerChartScheme : Over (Spec R) := Relative.AffinePoints.relativeAffineScheme R (ChartAlgebra.Grassmannian.pluckerHomogeneousChart (R := R) a)

def pluckerChartSchemePointEquiv (T : Over (Spec R)) :
    (T ⟶ pluckerChartScheme R a) ≃ (Normalized.Chart.Grassmannian.normalizedMatrixSubfunctor a (Spec R)).obj (.op T) :=
  (Relative.AffinePoints.relativeAffinePointEquiv R (ChartAlgebra.Grassmannian.pluckerHomogeneousChart (R := R) a) T).trans
    (ChartAlgebra.Grassmannian.pluckerHomogeneousChartPointEquiv (R := R) (B := Relative.AffinePoints.relativeGlobalAlgebra R T) a)

def pluckerChartSchemeRepresentation :
    yoneda.obj (pluckerChartScheme R a) ≅ (Normalized.Chart.Grassmannian.normalizedMatrixSubfunctor a (Spec R)).toFunctor :=
  NatIso.ofComponents (fun T => (pluckerChartSchemePointEquiv R a T.unop).toIso) (by
    intro T U f
    apply ConcreteCategory.hom_ext
    intro g
    change T.unop ⟶ Relative.AffinePoints.relativeAffineScheme R (ChartAlgebra.Grassmannian.pluckerHomogeneousChart (R := R) a) at g
    apply Subtype.ext
    change (ChartAlgebra.Grassmannian.pluckerHomogeneousChartPointEquiv a
      (Relative.AffinePoints.relativeAffinePointEquiv R (ChartAlgebra.Grassmannian.pluckerHomogeneousChart (R := R) a) U.unop (f.unop ≫ g))).val =
      (ChartAlgebra.Grassmannian.pluckerHomogeneousChartPointEquiv a
        (Relative.AffinePoints.relativeAffinePointEquiv R (ChartAlgebra.Grassmannian.pluckerHomogeneousChart (R := R) a) T.unop g)).val.map
          f.unop.left.appTop.hom
    rw [Relative.AffinePoints.relativeAffinePointEquiv_natural, ChartAlgebra.Grassmannian.pluckerHomogeneousChartPointEquiv_natural]
    rfl)

/-- The affine Plücker chart and the Grassmannian matrix chart are isomorphic
as actual schemes over the coefficient ring. -/
def pluckerChartSchemeIso : pluckerChartScheme R a ≅ Normalized.Chart.Grassmannian.normalizedChart a (Spec R) :=
  yoneda.preimageIso (pluckerChartSchemeRepresentation R a ≪≫ (Normalized.Chart.Grassmannian.normalizedChartRepresentation a (Spec R)).symm)

theorem pluckerChartSchemeIso_representation :
    yoneda.map (pluckerChartSchemeIso R a).hom ≫ (Normalized.Chart.Grassmannian.normalizedChartRepresentation a (Spec R)).hom =
      (pluckerChartSchemeRepresentation R a).hom := by
  simp [pluckerChartSchemeIso]

def pluckerChartSection (b : ι → ν) : Γ((pluckerChartScheme R a).left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (ChartAlgebra.Grassmannian.pluckerHomogeneousChart (R := R) a))).inv
    (Polynomial.ChartPresentation.PolynomialProjective.affineChartMap (Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν)) a (MvPolynomial.X b))

theorem pluckerChartSchemePointEquiv_minor (b : ι → ν) {T : Over (Spec R)}
    (f : T ⟶ pluckerChartScheme R a) :
    Determinants.Grassmannian.maximalMinor (pluckerChartSchemePointEquiv R a T f).val b =
      f.left.appTop (pluckerChartSection R a b) :=
  (ChartAlgebra.Grassmannian.pluckerHomogeneousChartPointEquiv_minor a b
    (Relative.AffinePoints.relativeAffinePointEquiv R (ChartAlgebra.Grassmannian.pluckerHomogeneousChart (R := R) a) T f)).trans
    (Relative.AffinePoints.relativeAffinePointEquiv_apply R (ChartAlgebra.Grassmannian.pluckerHomogeneousChart (R := R) a) f _)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Plucker.Chart.Grassmannian
