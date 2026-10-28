import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.AtlasMaps
import Mathlib.AlgebraicGeometry.Gluing

/-! # Gluing -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.Gluing

noncomputable section

/-! Gluing the normalized Grassmannian charts along their determinant opens. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {ι ν : Type u} [Fintype ι] [DecidableEq ι]
variable (a b c : ι → ν) (S : Scheme.{u})

instance normalizedOverlapInclusion_mono : Mono (Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a b S) :=
  (Over.forget S).mono_of_mono_map
    (show Mono (Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a b S).left from inferInstance)

def overlapTripleLift {T : Over S}
    (f : T ⟶ Normalized.Overlap.Grassmannian.normalizedChartOverlap a b S) (g : T ⟶ Normalized.Overlap.Grassmannian.normalizedChartOverlap a c S)
    (h : f ≫ Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a b S = g ≫ Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a c S) :
    T ⟶ Normalized.Overlap.Grassmannian.normalizedChartOverlap b c S :=
  Normalized.AtlasMaps.Grassmannian.overlapLift b c S ((f ≫ (Normalized.Overlap.Grassmannian.normalizedOverlapTransition a b S).hom) ≫
    Normalized.Overlap.Grassmannian.normalizedOverlapInclusion b a S) (by
      rw [← Normalized.AtlasMaps.Grassmannian.overlapMatrix_eq_chartMatrix, Normalized.AtlasMaps.Grassmannian.overlapTransition_matrix]
      apply (Normalized.Matrices.Grassmannian.normalizeColumns_pivot_isUnit_iff c b (Normalized.AtlasMaps.Grassmannian.overlapMatrix a b S f)
        (Normalized.AtlasMaps.Grassmannian.overlapMatrix_unit a b S f)).mpr
      have hQ : Normalized.AtlasMaps.Grassmannian.overlapMatrix a b S f = Normalized.AtlasMaps.Grassmannian.overlapMatrix a c S g :=
        congrArg (Normalized.AtlasMaps.Grassmannian.chartMatrix a S) h
      rw [hQ]
      exact Normalized.AtlasMaps.Grassmannian.overlapMatrix_unit a c S g)

theorem overlapTripleLift_inclusion {T : Over S}
    (f : T ⟶ Normalized.Overlap.Grassmannian.normalizedChartOverlap a b S) (g : T ⟶ Normalized.Overlap.Grassmannian.normalizedChartOverlap a c S)
    (h : f ≫ Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a b S = g ≫ Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a c S) :
    overlapTripleLift a b c S f g h ≫ Normalized.Overlap.Grassmannian.normalizedOverlapInclusion b c S =
      (f ≫ (Normalized.Overlap.Grassmannian.normalizedOverlapTransition a b S).hom) ≫ Normalized.Overlap.Grassmannian.normalizedOverlapInclusion b a S :=
  Normalized.AtlasMaps.Grassmannian.overlapLift_inclusion b c S _ _

def overlapTripleMap :
    pullback (Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a b S) (Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a c S) ⟶
      pullback (Normalized.Overlap.Grassmannian.normalizedOverlapInclusion b c S) (Normalized.Overlap.Grassmannian.normalizedOverlapInclusion b a S) :=
  pullback.lift
    (overlapTripleLift a b c S (pullback.fst _ _) (pullback.snd _ _) pullback.condition)
    (pullback.fst _ _ ≫ (Normalized.Overlap.Grassmannian.normalizedOverlapTransition a b S).hom)
    (overlapTripleLift_inclusion a b c S _ _ _)

theorem overlapTripleMap_snd : overlapTripleMap a b c S ≫ pullback.snd _ _ =
    pullback.fst _ _ ≫ (Normalized.Overlap.Grassmannian.normalizedOverlapTransition a b S).hom :=
  pullback.lift_snd _ _ _

theorem overlapTripleMap_fst_chart :
    overlapTripleMap a b c S ≫ pullback.fst _ _ ≫ Normalized.Overlap.Grassmannian.normalizedOverlapInclusion b c S =
      pullback.fst _ _ ≫ (Normalized.Overlap.Grassmannian.normalizedOverlapTransition a b S).hom ≫
        Normalized.Overlap.Grassmannian.normalizedOverlapInclusion b a S := by
  rw [← Category.assoc, overlapTripleMap, pullback.lift_fst, overlapTripleLift_inclusion,
    Category.assoc]

theorem overlapTripleMap_matrix {T : Over S}
    (h : T ⟶ pullback (Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a b S) (Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a c S)) :
    Normalized.AtlasMaps.Grassmannian.overlapMatrix b c S ((h ≫ overlapTripleMap a b c S) ≫ pullback.fst _ _) =
      Normalized.Matrices.Grassmannian.normalizeColumns b (Normalized.AtlasMaps.Grassmannian.overlapMatrix a b S (h ≫ pullback.fst _ _)) := by
  rw [Normalized.AtlasMaps.Grassmannian.overlapMatrix_eq_chartMatrix]
  simp only [Category.assoc, overlapTripleMap_fst_chart]
  exact (Normalized.AtlasMaps.Grassmannian.overlapMatrix_eq_chartMatrix b a S
    ((h ≫ pullback.fst _ _) ≫ (Normalized.Overlap.Grassmannian.normalizedOverlapTransition a b S).hom)).symm.trans
    (Normalized.AtlasMaps.Grassmannian.overlapTransition_matrix a b S (h ≫ pullback.fst _ _))

theorem overlapTripleMap_matrix_id :
    Normalized.AtlasMaps.Grassmannian.overlapMatrix b c S (overlapTripleMap a b c S ≫ pullback.fst _ _) =
      Normalized.Matrices.Grassmannian.normalizeColumns b (Normalized.AtlasMaps.Grassmannian.overlapMatrix a b S (pullback.fst _ _)) := by
  simpa only [Category.id_comp] using overlapTripleMap_matrix a b c S (𝟙 _)

theorem overlapTripleMap_cocycle :
    overlapTripleMap a b c S ≫ overlapTripleMap b c a S ≫ overlapTripleMap c a b S = 𝟙 _ := by
  apply (cancel_mono (pullback.fst (Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a b S)
    (Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a c S))).mp
  apply Normalized.AtlasMaps.Grassmannian.overlapMatrix_injective a b S _
  rw [Category.id_comp, ← Category.assoc (overlapTripleMap a b c S),
    overlapTripleMap_matrix, overlapTripleMap_matrix, overlapTripleMap_matrix_id]
  let Q := Normalized.AtlasMaps.Grassmannian.overlapMatrix a b S (pullback.fst (Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a b S)
    (Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a c S))
  have hb : IsUnit (Normalized.Matrices.Grassmannian.selectedColumns b Q).det := Normalized.AtlasMaps.Grassmannian.overlapMatrix_unit a b S _
  have hc : IsUnit (Normalized.Matrices.Grassmannian.selectedColumns c Q).det := by
    have hQ : Q = Normalized.AtlasMaps.Grassmannian.overlapMatrix a c S (pullback.snd (Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a b S)
        (Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a c S)) := congrArg (Normalized.AtlasMaps.Grassmannian.chartMatrix a S) pullback.condition
    rw [hQ]
    exact Normalized.AtlasMaps.Grassmannian.overlapMatrix_unit a c S _
  change Normalized.Matrices.Grassmannian.normalizeColumns a (Normalized.Matrices.Grassmannian.normalizeColumns c (Normalized.Matrices.Grassmannian.normalizeColumns b Q)) = Q
  rw [Normalized.Matrices.Grassmannian.normalizeColumns_cocycle c b Q hc hb]
  exact Normalized.Matrices.Grassmannian.normalizeColumns_inverse a c Q (Normalized.AtlasMaps.Grassmannian.overlapMatrix_normalized a b S _) hc

def normalizedGlueDataOver : CategoryTheory.GlueData (Over S) where
  J := ι → ν
  U a := Normalized.Chart.Grassmannian.normalizedChart a S
  V p := Normalized.Overlap.Grassmannian.normalizedChartOverlap p.1 p.2 S
  f a b := Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a b S
  t a b := (Normalized.Overlap.Grassmannian.normalizedOverlapTransition a b S).hom
  t_id a := Normalized.AtlasMaps.Grassmannian.normalizedOverlapTransition_self a S
  t' a b c := overlapTripleMap a b c S
  t_fac a b c := overlapTripleMap_snd a b c S
  cocycle a b c := overlapTripleMap_cocycle a b c S

def normalizedGrassmannianGlueData : Scheme.GlueData where
  toGlueData := (normalizedGlueDataOver (ι := ι) (ν := ν) S).mapGlueData (Over.forget S)
  f_open a b := by
    change IsOpenImmersion (Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a b S).left
    exact Normalized.Overlap.Grassmannian.normalizedOverlapInclusion_isOpenImmersion (a : ι → ν) (b : ι → ν) S

/-- The actual scheme obtained by gluing the quotient-matrix charts. -/
def grassmannianScheme : Scheme.{u} :=
  (normalizedGrassmannianGlueData (ι := ι) (ν := ν) S).glued

def grassmannianChartMap : (Normalized.Chart.Grassmannian.normalizedChart a S).left ⟶ grassmannianScheme (ι := ι) (ν := ν) S :=
  (normalizedGrassmannianGlueData (ι := ι) (ν := ν) S).ι a

instance grassmannianChartMap_isOpenImmersion : IsOpenImmersion (grassmannianChartMap a S) :=
  Scheme.GlueData.ι_isOpenImmersion (normalizedGrassmannianGlueData (ι := ι) (ν := ν) S) a

def grassmannianStructureMap : grassmannianScheme (ι := ι) (ν := ν) S ⟶ S := by
  fapply Multicoequalizer.desc
  · exact fun a => (Normalized.Chart.Grassmannian.normalizedChart a S).hom
  rintro ⟨a, b⟩
  change (Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a b S).left ≫ (Normalized.Chart.Grassmannian.normalizedChart a S).hom =
    ((Normalized.Overlap.Grassmannian.normalizedOverlapTransition a b S).hom.left ≫ (Normalized.Overlap.Grassmannian.normalizedOverlapInclusion b a S).left) ≫
      (Normalized.Chart.Grassmannian.normalizedChart b S).hom
  rw [Category.assoc, (Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a b S).w,
    (Normalized.Overlap.Grassmannian.normalizedOverlapInclusion b a S).w, (Normalized.Overlap.Grassmannian.normalizedOverlapTransition a b S).hom.w]

theorem grassmannianChartMap_structureMap :
    grassmannianChartMap a S ≫ grassmannianStructureMap (ι := ι) (ν := ν) S = (Normalized.Chart.Grassmannian.normalizedChart a S).hom :=
  Multicoequalizer.π_desc _ _ _ _ _

def grassmannianOver : Over S := Over.mk (grassmannianStructureMap (ι := ι) (ν := ν) S)

def grassmannianChartOverMap : Normalized.Chart.Grassmannian.normalizedChart a S ⟶ grassmannianOver (ι := ι) (ν := ν) S :=
  Over.homMk (grassmannianChartMap a S) (grassmannianChartMap_structureMap a S)

theorem grassmannianCharts_cover (x : grassmannianScheme (ι := ι) (ν := ν) S) :
    ∃ a : ι → ν, ∃ y : (Normalized.Chart.Grassmannian.normalizedChart a S).left, grassmannianChartMap a S y = x :=
  (normalizedGrassmannianGlueData (ι := ι) (ν := ν) S).ι_jointly_surjective x

theorem grassmannianChart_intersection_isPullback :
    IsPullback (Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a b S).left
      ((Normalized.Overlap.Grassmannian.normalizedOverlapTransition a b S).hom.left ≫ (Normalized.Overlap.Grassmannian.normalizedOverlapInclusion b a S).left)
      (grassmannianChartMap a S) (grassmannianChartMap b S) :=
  IsPullback.of_isLimit
    ((normalizedGrassmannianGlueData (ι := ι) (ν := ν) S).vPullbackConeIsLimit a b)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.Gluing
