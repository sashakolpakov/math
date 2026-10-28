import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Plucker.Overlap

/-! # To Grassmannian -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Plucker.ToGrassmannian.Grassmannian

noncomputable section

/-! Gluing the affine Plücker chart isomorphisms into a global scheme morphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {ι ν : Type u} [Fintype ι] [DecidableEq ι]
variable (R : CommRingCat.{u})

theorem pluckerChartMaps_glue (a b : ι → ν) :
    pullback.fst (Projective.Grassmannian.pluckerProjectiveChartMap R a).left (Projective.Grassmannian.pluckerProjectiveChartMap R b).left ≫
        (Chart.Grassmannian.pluckerChartSchemeIso R a).hom.left ≫ Grassmannian.Gluing.grassmannianChartMap a (Spec R) =
      pullback.snd (Projective.Grassmannian.pluckerProjectiveChartMap R a).left (Projective.Grassmannian.pluckerProjectiveChartMap R b).left ≫
        (Chart.Grassmannian.pluckerChartSchemeIso R b).hom.left ≫ Grassmannian.Gluing.grassmannianChartMap b (Spec R) := by
  let e : pullback (Projective.Grassmannian.pluckerProjectiveChartMap R a).left (Projective.Grassmannian.pluckerProjectiveChartMap R b).left ≅
      (Overlap.Grassmannian.pluckerIntersectionScheme R a b).left :=
    Proj.pullbackAwayιIso (OverlapAlgebra.Grassmannian.pluckerQuotientGrading (R := R) (ι := ι) (ν := ν))
      (OverlapAlgebra.Grassmannian.pluckerVariable (R := R) a).property Nat.zero_lt_one
      (OverlapAlgebra.Grassmannian.pluckerVariable (R := R) b).property Nat.zero_lt_one rfl
  have hfst : e.inv ≫ pullback.fst _ _ = (Overlap.Grassmannian.pluckerIntersectionLeft R a b).left :=
    Proj.pullbackAwayιIso_inv_fst _ _ _ _ _ rfl
  have hsnd : e.inv ≫ pullback.snd _ _ = (Overlap.Grassmannian.pluckerIntersectionRight R a b).left :=
    Proj.pullbackAwayιIso_inv_snd _ _ _ _ _ rfl
  apply (cancel_epi e.inv).mp
  simp only [← Category.assoc, hfst, hsnd]
  exact congrArg (fun f => f.left) (Overlap.Grassmannian.pluckerIntersection_toGrassmannian R a b)

def pluckerToGrassmannian : Projective.Grassmannian.pluckerProjectiveScheme (ι := ι) (ν := ν) R ⟶
    Grassmannian.Gluing.grassmannianScheme (ι := ι) (ν := ν) (Spec R) :=
  (Polynomial.Projective.PolynomialProjective.projectiveQuotientAffineCover (Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν))).openCover.glueMorphisms
    (fun a => (Chart.Grassmannian.pluckerChartSchemeIso R (a : ι → ν)).hom.left ≫ Grassmannian.Gluing.grassmannianChartMap a (Spec R))
    (fun a b => pluckerChartMaps_glue R a b)

theorem pluckerToGrassmannian_chart (a : ι → ν) :
    (Projective.Grassmannian.pluckerProjectiveChartMap R a).left ≫ pluckerToGrassmannian (ι := ι) (ν := ν) R =
      (Chart.Grassmannian.pluckerChartSchemeIso R a).hom.left ≫ Grassmannian.Gluing.grassmannianChartMap a (Spec R) :=
  (Polynomial.Projective.PolynomialProjective.projectiveQuotientAffineCover (Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν))).openCover.ι_glueMorphisms _ _ a

theorem pluckerToGrassmannian_over :
    pluckerToGrassmannian (ι := ι) (ν := ν) R ≫
        Grassmannian.Gluing.grassmannianStructureMap (ι := ι) (ν := ν) (Spec R) =
      (Projective.Grassmannian.pluckerProjectiveOver (ι := ι) (ν := ν) R).hom := by
  apply (Polynomial.Projective.PolynomialProjective.projectiveQuotientAffineCover (Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν))).openCover.hom_ext
  intro a
  change ι → ν at a
  change (Projective.Grassmannian.pluckerProjectiveChartMap R a).left ≫ _ = (Projective.Grassmannian.pluckerProjectiveChartMap R a).left ≫ _
  calc
    _ = ((Projective.Grassmannian.pluckerProjectiveChartMap R a).left ≫ pluckerToGrassmannian (ι := ι) (ν := ν) R) ≫
        Grassmannian.Gluing.grassmannianStructureMap (ι := ι) (ν := ν) (Spec R) := (Category.assoc _ _ _).symm
    _ = ((Chart.Grassmannian.pluckerChartSchemeIso R a).hom.left ≫ Grassmannian.Gluing.grassmannianChartMap a (Spec R)) ≫
        Grassmannian.Gluing.grassmannianStructureMap (ι := ι) (ν := ν) (Spec R) :=
      congrArg (fun f => f ≫ Grassmannian.Gluing.grassmannianStructureMap (ι := ι) (ν := ν) (Spec R))
        (pluckerToGrassmannian_chart R a)
    _ = (Chart.Grassmannian.pluckerChartSchemeIso R a).hom.left ≫ (Normalized.Chart.Grassmannian.normalizedChart a (Spec R)).hom := by
      rw [Category.assoc, Grassmannian.Gluing.grassmannianChartMap_structureMap]
    _ = _ := (Chart.Grassmannian.pluckerChartSchemeIso R a).hom.w.trans (Projective.Grassmannian.pluckerProjectiveChartMap R a).w.symm

def pluckerToGrassmannianOver : Projective.Grassmannian.pluckerProjectiveOver (ι := ι) (ν := ν) R ⟶
    Grassmannian.Gluing.grassmannianOver (ι := ι) (ν := ν) (Spec R) :=
  Over.homMk (pluckerToGrassmannian R) (pluckerToGrassmannian_over R)

theorem pluckerToGrassmannianOver_chart (a : ι → ν) :
    Projective.Grassmannian.pluckerProjectiveChartMap R a ≫ pluckerToGrassmannianOver (ι := ι) (ν := ν) R =
      (Chart.Grassmannian.pluckerChartSchemeIso R a).hom ≫ Grassmannian.Gluing.grassmannianChartOverMap a (Spec R) := by
  apply (Over.forget (Spec R)).map_injective
  exact pluckerToGrassmannian_chart R a

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Plucker.ToGrassmannian.Grassmannian
