import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ProjectiveCharts
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.Projective
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.AffinePoints

/-! # Projective Scheme -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ProjectiveScheme

noncomputable section

/-! The projective Segre equation scheme and its explicit affine open charts. -/

open _root_.MvPolynomial _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.AffinePoints
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.Projective.PolynomialProjective

universe u

variable (R : CommRingCat.{u}) {σ τ : Type u}

def segreProjectiveScheme : Scheme.{u} :=
  HilbertScheme.Presentations.Homogeneous.ProjectiveQuotient.HomogeneousQuotient.projectiveQuotient (HomogeneousRelations.segreHomogeneousIdeal (σ := σ) (τ := τ) R)

def segreProjectiveOver : Over (Spec R) :=
  Over.mk (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap
    (HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient.quotientGrading (HomogeneousRelations.segreHomogeneousIdeal (σ := σ) (τ := τ) R)))

def segreProjectiveInclusion : segreProjectiveScheme (σ := σ) (τ := τ) R ⟶
    Proj (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (σ × τ) R) :=
  HilbertScheme.Presentations.Homogeneous.ProjectiveQuotient.HomogeneousQuotient.projectiveQuotientInclusion (HomogeneousRelations.segreHomogeneousIdeal R)

instance segreProjectiveInclusion_isClosedImmersion :
    IsClosedImmersion (segreProjectiveInclusion (σ := σ) (τ := τ) R) :=
  HilbertScheme.Presentations.Homogeneous.ProjectiveQuotient.HomogeneousQuotient.projectiveQuotientInclusion_isClosedImmersion (HomogeneousRelations.segreHomogeneousIdeal R)

instance segreProjectiveOver_isProper [Finite σ] [Finite τ] :
    IsProper (segreProjectiveOver (σ := σ) (τ := τ) R).hom :=
  HilbertScheme.Presentations.Polynomial.Projective.PolynomialProjective.projectiveQuotient_proper (HomogeneousRelations.segreHomogeneousIdeal R)

variable (i : σ) (j : τ)

def segreHomogeneousChartScheme : Over (Spec R) :=
  HilbertScheme.Presentations.Relative.AffinePoints.relativeAffineScheme R (ProjectiveCharts.SegreHomogeneousChart R i j)

def segreAffineChartScheme : Over (Spec R) :=
  HilbertScheme.Presentations.Relative.AffinePoints.relativeAffineScheme R (NormalizedCoordinates.SegreChartRing R i j)

def segreAffineChartSchemeIso :
    segreAffineChartScheme R i j ≅ segreHomogeneousChartScheme R i j :=
  (algSpec R).mapIso (Iso.op
    { hom := CommAlgCat.ofHom (ProjectiveCharts.segreHomogeneousChartEquiv R i j).toAlgHom
      inv := CommAlgCat.ofHom (ProjectiveCharts.segreHomogeneousChartEquiv R i j).symm.toAlgHom
      hom_inv_id := by
        apply ConcreteCategory.hom_ext
        intro x
        exact (ProjectiveCharts.segreHomogeneousChartEquiv R i j).symm_apply_apply x
      inv_hom_id := by
        apply ConcreteCategory.hom_ext
        intro x
        exact (ProjectiveCharts.segreHomogeneousChartEquiv R i j).apply_symm_apply x })

def segreHomogeneousChartMap :
    segreHomogeneousChartScheme R i j ⟶ segreProjectiveOver (σ := σ) (τ := τ) R := by
  let I := HomogeneousRelations.segreHomogeneousIdeal (σ := σ) (τ := τ) R
  let h := (HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I).map_mem (isHomogeneous_X R (i, j))
  exact Over.homMk (Proj.awayι (HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient.quotientGrading I) (HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I (X (i, j)))
    h Nat.zero_lt_one) (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap_away (HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient.quotientGrading I) h)

instance segreHomogeneousChartMap_isOpenImmersion :
    IsOpenImmersion (segreHomogeneousChartMap R i j).left := by
  change IsOpenImmersion (Proj.awayι _ _ _ _)
  infer_instance

def segreAffineChartMap :
    segreAffineChartScheme R i j ⟶ segreProjectiveOver (σ := σ) (τ := τ) R :=
  (segreAffineChartSchemeIso R i j).hom ≫ segreHomogeneousChartMap R i j

instance segreAffineChartMap_isOpenImmersion :
    IsOpenImmersion (segreAffineChartMap R i j).left := by
  have : IsIso (segreAffineChartSchemeIso R i j).hom.left :=
    ((Over.forget (Spec R)).mapIso (segreAffineChartSchemeIso R i j)).isIso_hom
  change IsOpenImmersion ((segreAffineChartSchemeIso R i j).hom.left ≫
    (segreHomogeneousChartMap R i j).left)
  infer_instance

theorem segreHomogeneousCharts_cover (x : segreProjectiveScheme (σ := σ) (τ := τ) R) :
    ∃ i : σ, ∃ j : τ, ∃ y : (segreHomogeneousChartScheme R i j).left,
      (segreHomogeneousChartMap R i j).left y = x := by
  obtain ⟨⟨i, j⟩, y, hy⟩ :=
    (HilbertScheme.Presentations.Polynomial.Projective.PolynomialProjective.projectiveQuotientAffineCover (HomogeneousRelations.segreHomogeneousIdeal R)).openCover.exists_eq x
  exact ⟨i, j, y, hy⟩

theorem segreAffineCharts_cover (x : segreProjectiveScheme (σ := σ) (τ := τ) R) :
    ∃ i : σ, ∃ j : τ, ∃ y : (segreAffineChartScheme R i j).left,
      (segreAffineChartMap R i j).left y = x := by
  obtain ⟨i, j, y, hy⟩ := segreHomogeneousCharts_cover R x
  refine ⟨i, j, (segreAffineChartSchemeIso R i j).inv.left y, ?_⟩
  change (segreHomogeneousChartMap R i j).left
    ((segreAffineChartSchemeIso R i j).hom.left
      ((segreAffineChartSchemeIso R i j).inv.left y)) = x
  have h := congrArg (fun f => f.left y) (segreAffineChartSchemeIso R i j).inv_hom_id
  change (segreAffineChartSchemeIso R i j).hom.left
    ((segreAffineChartSchemeIso R i j).inv.left y) = y at h
  rw [h]
  exact hy

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ProjectiveScheme
