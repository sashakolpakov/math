import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.TripleOverlaps
import Mathlib.AlgebraicGeometry.Gluing

/-! # Data -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixRank.Data.Grassmannian

noncomputable section

/-! The actual scheme obtained by gluing finite-matrix pivot charts along their determinant-open overlaps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {ι μ ν : Type u} [Fintype ι] [DecidableEq ι]
variable {S : Scheme.{u}} (M : Over S) (A : Matrix ν μ Γ(M.left, ⊤))

def matrixPivotGlueDataOver : CategoryTheory.GlueData (Over S) where
  J := MatrixPivot.Charts.Grassmannian.MatrixPivotIndex ι μ ν
  U p := MatrixPivot.Charts.Grassmannian.matrixPivotChart M A p
  V p := MatrixPivot.Overlaps.Grassmannian.matrixPivotOverlap M A p.1 p.2
  f p q := MatrixPivot.Overlaps.Grassmannian.matrixPivotOverlapInclusion M A p q
  t p q := MatrixPivot.Overlaps.Grassmannian.matrixPivotOverlapSwap M A p q
  t_id p := MatrixPivot.Overlaps.Grassmannian.matrixPivotOverlapSwap_self M A p
  t' p q r := MatrixPivot.TripleOverlaps.Grassmannian.matrixPivotTripleMap M A p q r
  t_fac p q r := MatrixPivot.TripleOverlaps.Grassmannian.matrixPivotTripleMap_snd M A p q r
  cocycle p q r := MatrixPivot.TripleOverlaps.Grassmannian.matrixPivotTripleMap_cocycle M A p q r

def matrixRankGlueData : Scheme.GlueData where
  toGlueData := (matrixPivotGlueDataOver (ι := ι) M A).mapGlueData (Over.forget S)
  f_open p q := MatrixPivot.Overlaps.Grassmannian.matrixPivotOverlapInclusion_isOpenImmersion M A p q

def matrixRankScheme : Scheme.{u} := (matrixRankGlueData (ι := ι) M A).glued

def matrixRankChartMap (p : MatrixPivot.Charts.Grassmannian.MatrixPivotIndex ι μ ν) : (MatrixPivot.Charts.Grassmannian.matrixPivotChart M A p).left ⟶ matrixRankScheme (ι := ι) M A :=
  (matrixRankGlueData (ι := ι) M A).ι p

instance matrixRankChartMap_isOpenImmersion (p : MatrixPivot.Charts.Grassmannian.MatrixPivotIndex ι μ ν) :
    IsOpenImmersion (matrixRankChartMap M A p) := Scheme.GlueData.ι_isOpenImmersion (matrixRankGlueData M A) p

def matrixRankStructureMap : matrixRankScheme (ι := ι) M A ⟶ M.left := by
  fapply Multicoequalizer.desc
  · exact fun p => (MatrixPivot.Charts.Grassmannian.matrixPivotChartInclusion M A p).left
  · rintro ⟨p, q⟩
    change (MatrixPivot.Overlaps.Grassmannian.matrixPivotOverlapInclusion M A p q ≫ MatrixPivot.Charts.Grassmannian.matrixPivotChartInclusion M A p).left =
      ((MatrixPivot.Overlaps.Grassmannian.matrixPivotOverlapSwap M A p q ≫ MatrixPivot.Overlaps.Grassmannian.matrixPivotOverlapInclusion M A q p) ≫ MatrixPivot.Charts.Grassmannian.matrixPivotChartInclusion M A q).left
    apply congrArg Over.Hom.left
    rw [Category.assoc]
    exact (MatrixPivot.Overlaps.Grassmannian.matrixPivotOverlapSwap_parameter M A p q).symm

theorem matrixRankChartMap_structureMap (p : MatrixPivot.Charts.Grassmannian.MatrixPivotIndex ι μ ν) :
    matrixRankChartMap M A p ≫ matrixRankStructureMap (ι := ι) M A = (MatrixPivot.Charts.Grassmannian.matrixPivotChartInclusion M A p).left :=
  Multicoequalizer.π_desc _ _ _ _ _

def matrixRankOver : Over S := Over.mk (matrixRankStructureMap (ι := ι) M A ≫ M.hom)

def matrixRankParameterMap : matrixRankOver (ι := ι) M A ⟶ M :=
  Over.homMk (matrixRankStructureMap (ι := ι) M A) rfl

def matrixRankChartOverMap (p : MatrixPivot.Charts.Grassmannian.MatrixPivotIndex ι μ ν) : MatrixPivot.Charts.Grassmannian.matrixPivotChart M A p ⟶ matrixRankOver (ι := ι) M A :=
  Over.homMk (matrixRankChartMap M A p) (by
    change matrixRankChartMap M A p ≫ (matrixRankStructureMap M A ≫ M.hom) = (MatrixPivot.Charts.Grassmannian.matrixPivotChart M A p).hom
    rw [← Category.assoc, matrixRankChartMap_structureMap, (MatrixPivot.Charts.Grassmannian.matrixPivotChartInclusion M A p).w])

theorem matrixRankChartOverMap_parameterMap (p : MatrixPivot.Charts.Grassmannian.MatrixPivotIndex ι μ ν) :
    matrixRankChartOverMap M A p ≫ matrixRankParameterMap (ι := ι) M A = MatrixPivot.Charts.Grassmannian.matrixPivotChartInclusion M A p := by
  apply Over.OverMorphism.ext
  exact matrixRankChartMap_structureMap M A p

theorem matrixRankCharts_cover (x : matrixRankScheme (ι := ι) M A) :
    ∃ p : MatrixPivot.Charts.Grassmannian.MatrixPivotIndex ι μ ν, ∃ y : (MatrixPivot.Charts.Grassmannian.matrixPivotChart M A p).left, matrixRankChartMap M A p y = x :=
  (matrixRankGlueData (ι := ι) M A).ι_jointly_surjective x

theorem matrixRankChart_intersection_isPullback (p q : MatrixPivot.Charts.Grassmannian.MatrixPivotIndex ι μ ν) :
    IsPullback (MatrixPivot.Overlaps.Grassmannian.matrixPivotOverlapInclusion M A p q).left
      (MatrixPivot.Overlaps.Grassmannian.matrixPivotOverlapSwap M A p q ≫ MatrixPivot.Overlaps.Grassmannian.matrixPivotOverlapInclusion M A q p).left
      (matrixRankChartMap M A p) (matrixRankChartMap M A q) :=
  IsPullback.of_isLimit ((matrixRankGlueData (ι := ι) M A).vPullbackConeIsLimit p q)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixRank.Data.Grassmannian
