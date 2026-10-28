import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ChartProjections

/-! # Projection Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ProjectionGluing

noncomputable section

/-! Gluing the row and column projections of the Segre equation scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable (R : CommRingCat.{u}) {n m : ℕ}

theorem segreRowChartMap_glue (p q : ChartProjections.SegreProjectiveIndex.{u} n m) :
    pullback.fst (ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left
        (ProjectiveScheme.segreHomogeneousChartMap R q.1 q.2).left ≫ ChartProjections.segreRowChartMap R p =
      pullback.snd (ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left
        (ProjectiveScheme.segreHomogeneousChartMap R q.1 q.2).left ≫ ChartProjections.segreRowChartMap R q := by
  let e : pullback (ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left
        (ProjectiveScheme.segreHomogeneousChartMap R q.1 q.2).left ≅
      Spec (CommRingCat.of (OverlapCoordinates.SegreDoubleChart R p q)) :=
    Proj.pullbackAwayιIso (ChartCoordinates.segreQuotientGrading R)
      (ChartCoordinates.segreVariable R p).property Nat.zero_lt_one
      (ChartCoordinates.segreVariable R q).property Nat.zero_lt_one rfl
  have hl : e.inv ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (OverlapCoordinates.segreOverlapLeft R p q).toRingHom) :=
    Proj.pullbackAwayιIso_inv_fst _ _ _ _ _ rfl
  have hr : e.inv ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (OverlapCoordinates.segreOverlapRight R p q).toRingHom) :=
    Proj.pullbackAwayιIso_inv_snd _ _ _ _ _ rfl
  apply (cancel_epi e.inv).mp
  simp only [← Category.assoc, hl, hr]
  exact ChartProjections.segreRowChartMap_overlap R p q

theorem segreColumnChartMap_glue (p q : ChartProjections.SegreProjectiveIndex.{u} n m) :
    pullback.fst (ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left
        (ProjectiveScheme.segreHomogeneousChartMap R q.1 q.2).left ≫ ChartProjections.segreColumnChartMap R p =
      pullback.snd (ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left
        (ProjectiveScheme.segreHomogeneousChartMap R q.1 q.2).left ≫ ChartProjections.segreColumnChartMap R q := by
  let e : pullback (ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left
        (ProjectiveScheme.segreHomogeneousChartMap R q.1 q.2).left ≅
      Spec (CommRingCat.of (OverlapCoordinates.SegreDoubleChart R p q)) :=
    Proj.pullbackAwayιIso (ChartCoordinates.segreQuotientGrading R)
      (ChartCoordinates.segreVariable R p).property Nat.zero_lt_one
      (ChartCoordinates.segreVariable R q).property Nat.zero_lt_one rfl
  have hl : e.inv ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (OverlapCoordinates.segreOverlapLeft R p q).toRingHom) :=
    Proj.pullbackAwayιIso_inv_fst _ _ _ _ _ rfl
  have hr : e.inv ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (OverlapCoordinates.segreOverlapRight R p q).toRingHom) :=
    Proj.pullbackAwayιIso_inv_snd _ _ _ _ _ rfl
  apply (cancel_epi e.inv).mp
  simp only [← Category.assoc, hl, hr]
  exact ChartProjections.segreColumnChartMap_overlap R p q

def segreRowProjection (n m : ℕ) :
    ProjectiveScheme.segreProjectiveScheme (σ := ULift.{u} (Fin (n + 1))) (τ := ULift.{u} (Fin (m + 1))) R ⟶
      (Projective.ProjectivePresentations.affineProjectiveSpace R n).left :=
  (HilbertScheme.Presentations.Polynomial.Projective.PolynomialProjective.projectiveQuotientAffineCover (HomogeneousRelations.segreHomogeneousIdeal R)).openCover.glueMorphisms
    (fun p => ChartProjections.segreRowChartMap R p) (segreRowChartMap_glue R)

def segreColumnProjection (n m : ℕ) :
    ProjectiveScheme.segreProjectiveScheme (σ := ULift.{u} (Fin (n + 1))) (τ := ULift.{u} (Fin (m + 1))) R ⟶
      (Projective.ProjectivePresentations.affineProjectiveSpace R m).left :=
  (HilbertScheme.Presentations.Polynomial.Projective.PolynomialProjective.projectiveQuotientAffineCover (HomogeneousRelations.segreHomogeneousIdeal R)).openCover.glueMorphisms
    (fun p => ChartProjections.segreColumnChartMap R p) (segreColumnChartMap_glue R)

theorem segreRowProjection_chart (p : ChartProjections.SegreProjectiveIndex.{u} n m) :
    (ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left ≫ segreRowProjection R n m = ChartProjections.segreRowChartMap R p :=
  (HilbertScheme.Presentations.Polynomial.Projective.PolynomialProjective.projectiveQuotientAffineCover (HomogeneousRelations.segreHomogeneousIdeal R)).openCover.ι_glueMorphisms _ _ p

theorem segreColumnProjection_chart (p : ChartProjections.SegreProjectiveIndex.{u} n m) :
    (ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left ≫ segreColumnProjection R n m = ChartProjections.segreColumnChartMap R p :=
  (HilbertScheme.Presentations.Polynomial.Projective.PolynomialProjective.projectiveQuotientAffineCover (HomogeneousRelations.segreHomogeneousIdeal R)).openCover.ι_glueMorphisms _ _ p

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ProjectionGluing
