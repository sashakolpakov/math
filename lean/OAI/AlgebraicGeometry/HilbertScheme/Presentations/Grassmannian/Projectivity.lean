import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Plucker.ChartPreimages

/-! # Projectivity -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.Projectivity

noncomputable section

/-!
The quotient-chart Grassmannian is the closed Plücker projective scheme.
The comparison is an actual isomorphism over the coefficient ring, obtained
by verifying its pullbacks along the full open chart cover.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {ι ν : Type u} [Fintype ι] [DecidableEq ι]
variable (R : CommRingCat.{u})

theorem pluckerToGrassmannian_chart_isPullback (a : ι → ν) :
    IsPullback (Plucker.Chart.Grassmannian.pluckerChartSchemeIso R a).hom.left (Plucker.Projective.Grassmannian.pluckerProjectiveChartMap R a).left
      (Gluing.grassmannianChartMap a (Spec R)) (Plucker.ToGrassmannian.Grassmannian.pluckerToGrassmannian (ι := ι) (ν := ν) R) := by
  apply IsOpenImmersion.isPullback
  · exact Plucker.ToGrassmannian.Grassmannian.pluckerToGrassmannian_chart R a
  · exact (Plucker.ChartPreimages.Grassmannian.pluckerToGrassmannian_preimage_chart R a).trans
      (Proj.opensRange_awayι (Plucker.OverlapAlgebra.Grassmannian.pluckerQuotientGrading (R := R) (ι := ι) (ν := ν))
        (Plucker.OverlapAlgebra.Grassmannian.pluckerVariable (R := R) a).val (Plucker.OverlapAlgebra.Grassmannian.pluckerVariable (R := R) a).property Nat.zero_lt_one).symm

instance pluckerToGrassmannian_isIso : IsIso (Plucker.ToGrassmannian.Grassmannian.pluckerToGrassmannian (ι := ι) (ν := ν) R) := by
  apply (IsZariskiLocalAtTarget.iff_of_openCover (P := MorphismProperty.isomorphisms Scheme)
    (Gluing.normalizedGrassmannianGlueData (ι := ι) (ν := ν) (Spec R)).openCover).mpr
  intro a
  change ι → ν at a
  have h := (pluckerToGrassmannian_chart_isPullback R a).flip
  have : IsIso (Plucker.Chart.Grassmannian.pluckerChartSchemeIso R a).hom.left :=
    ((Over.forget (Spec R)).mapIso (Plucker.Chart.Grassmannian.pluckerChartSchemeIso R a)).isIso_hom
  have hc : IsIso (h.isoPullback.inv ≫ (Plucker.Chart.Grassmannian.pluckerChartSchemeIso R a).hom.left) := inferInstance
  change IsIso (pullback.snd (Plucker.ToGrassmannian.Grassmannian.pluckerToGrassmannian (ι := ι) (ν := ν) R) (Gluing.grassmannianChartMap a (Spec R)))
  exact (congrArg (fun f => IsIso f) h.isoPullback_inv_snd).mp hc

instance pluckerToGrassmannianOver_isIso : IsIso (Plucker.ToGrassmannian.Grassmannian.pluckerToGrassmannianOver (ι := ι) (ν := ν) R) := by
  apply (isIso_iff_of_reflects_iso _ (Over.forget (Spec R))).mp
  change IsIso (Plucker.ToGrassmannian.Grassmannian.pluckerToGrassmannian (ι := ι) (ν := ν) R)
  infer_instance

def pluckerGrassmannianIso : Plucker.Projective.Grassmannian.pluckerProjectiveOver (ι := ι) (ν := ν) R ≅
    Gluing.grassmannianOver (ι := ι) (ν := ν) (Spec R) := asIso (Plucker.ToGrassmannian.Grassmannian.pluckerToGrassmannianOver R)

/-- A closed embedding of the Grassmannian into the projective space whose
coordinates are its maximal minors. -/
def grassmannianPluckerEmbedding : Gluing.grassmannianScheme (ι := ι) (ν := ν) (Spec R) ⟶
    Proj (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (ι → ν) R) :=
  (pluckerGrassmannianIso (ι := ι) (ν := ν) R).inv.left ≫ Plucker.Projective.Grassmannian.pluckerProjectiveInclusion (ι := ι) (ν := ν) R

instance grassmannianPluckerEmbedding_isClosedImmersion :
    IsClosedImmersion (grassmannianPluckerEmbedding (ι := ι) (ν := ν) R) := by
  have : IsIso (pluckerGrassmannianIso (ι := ι) (ν := ν) R).inv.left :=
    ((Over.forget (Spec R)).mapIso (pluckerGrassmannianIso (ι := ι) (ν := ν) R)).isIso_inv
  have hi : IsClosedImmersion (pluckerGrassmannianIso (ι := ι) (ν := ν) R).inv.left := inferInstance
  change IsClosedImmersion ((pluckerGrassmannianIso (ι := ι) (ν := ν) R).inv.left ≫
    Plucker.Projective.Grassmannian.pluckerProjectiveInclusion (ι := ι) (ν := ν) R)
  exact @IsClosedImmersion.comp (Gluing.grassmannianScheme (ι := ι) (ν := ν) (Spec R))
    (Plucker.Projective.Grassmannian.pluckerProjectiveScheme (ι := ι) (ν := ν) R) (Proj (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (ι → ν) R))
    (pluckerGrassmannianIso (ι := ι) (ν := ν) R).inv.left
    (Plucker.Projective.Grassmannian.pluckerProjectiveInclusion (ι := ι) (ν := ν) R) hi
    (Plucker.Projective.Grassmannian.pluckerProjectiveInclusion_isClosedImmersion R)

instance grassmannianStructureMap_isProper [Finite ν] :
    IsProper (Gluing.grassmannianStructureMap (ι := ι) (ν := ν) (Spec R)) := by
  have : IsIso (pluckerGrassmannianIso (ι := ι) (ν := ν) R).inv.left :=
    ((Over.forget (Spec R)).mapIso (pluckerGrassmannianIso (ι := ι) (ν := ν) R)).isIso_inv
  have h : IsProper ((pluckerGrassmannianIso (ι := ι) (ν := ν) R).inv.left ≫
      (Plucker.Projective.Grassmannian.pluckerProjectiveOver (ι := ι) (ν := ν) R).hom) := inferInstance
  rw [(pluckerGrassmannianIso (ι := ι) (ν := ν) R).inv.w] at h
  exact h

theorem grassmannianPluckerEmbedding_over :
    grassmannianPluckerEmbedding (ι := ι) (ν := ν) R ≫
      Projective.Flatness.GradedHilbert.projectiveStructureMap (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (ι → ν) R) =
        Gluing.grassmannianStructureMap (ι := ι) (ν := ν) (Spec R) := by
  have hb : Plucker.Projective.Grassmannian.pluckerProjectiveInclusion (ι := ι) (ν := ν) R ≫
      Projective.Flatness.GradedHilbert.projectiveStructureMap (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (ι → ν) R) =
        (Plucker.Projective.Grassmannian.pluckerProjectiveOver (ι := ι) (ν := ν) R).hom :=
    Polynomial.Projective.PolynomialProjective.projectiveQuotientInclusion_over (Plucker.Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν))
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun h => (pluckerGrassmannianIso (ι := ι) (ν := ν) R).inv.left ≫ h) hb).trans
      (pluckerGrassmannianIso (ι := ι) (ν := ν) R).inv.w)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.Projectivity
