import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.PairChartCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.ChartLoci
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.IdealMatching

/-! # Incidence Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann

noncomputable section

/-!
The normalized incidence ideals agree on all overlaps of the constructed chart
cover. They therefore glue to an actual global quasi-coherent defining ideal.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν κ μ : Type u}
variable [Fintype ι] [Fintype ν] [Fintype κ] [Fintype μ]
variable [DecidableEq ι] [DecidableEq ν] [DecidableEq κ] [DecidableEq μ]
variable {S : Scheme.{u}} {M : Over S}
variable {q : M ⟶ ParameterScheme.grassmannParameterScheme (ι := ι) (ν := ν) S}
variable {k : M ⟶ ParameterScheme.grassmannParameterScheme (ι := κ) (ν := μ) S}

variable (D : PairChartCover.GrassmannPairChartCover q k) (F : Matrix μ ν Γ(M.left, ⊤))

def PairChartCover.GrassmannPairChartCover.incidenceLocalIdeal (i : D.cover.I₀) : (D.cover.X i).IdealSheafData :=
  ChartLoci.grassmannChartIncidenceIdeal (D.sourceColumns i) (D.targetColumns i)
    (D.sourceLift i) (D.targetLift i) (F.map (Embedded.FamilyOpenCover.overOpenCoverMap M D.cover i).left.appTop.hom)

theorem PairChartCover.GrassmannPairChartCover.incidenceLocalIdeal_compatible {T : Over S} (i j : D.cover.I₀)
    (a : T ⟶ Embedded.FamilyOpenCover.overOpenCoverObject M D.cover i) (b : T ⟶ Embedded.FamilyOpenCover.overOpenCoverObject M D.cover j)
    (h : a ≫ Embedded.FamilyOpenCover.overOpenCoverMap M D.cover i = b ≫ Embedded.FamilyOpenCover.overOpenCoverMap M D.cover j) :
    (D.incidenceLocalIdeal F i).comap a.left = (D.incidenceLocalIdeal F j).comap b.left := by
  have hF : (F.map (Embedded.FamilyOpenCover.overOpenCoverMap M D.cover i).left.appTop.hom).map a.left.appTop.hom =
      (F.map (Embedded.FamilyOpenCover.overOpenCoverMap M D.cover j).left.appTop.hom).map b.left.appTop.hom := by
    change F.map (a ≫ Embedded.FamilyOpenCover.overOpenCoverMap M D.cover i).left.appTop.hom =
      F.map (b ≫ Embedded.FamilyOpenCover.overOpenCoverMap M D.cover j).left.appTop.hom
    rw [h]
  change (ChartLoci.grassmannChartIncidenceIdeal (D.sourceColumns i) (D.targetColumns i)
    (D.sourceLift i) (D.targetLift i)
      (F.map (Embedded.FamilyOpenCover.overOpenCoverMap M D.cover i).left.appTop.hom)).comap a.left =
    (ChartLoci.grassmannChartIncidenceIdeal (D.sourceColumns j) (D.targetColumns j)
      (D.sourceLift j) (D.targetLift j)
        (F.map (Embedded.FamilyOpenCover.overOpenCoverMap M D.cover j).left.appTop.hom)).comap b.left
  rw [ChartLoci.grassmannChartIncidenceIdeal_comap, ChartLoci.grassmannChartIncidenceIdeal_comap, hF]
  apply ChartLoci.grassmannChartIncidenceIdeal_chart_independent
  · simp only [Category.assoc, D.source_fac]
    change a ≫ (Embedded.FamilyOpenCover.overOpenCoverMap M D.cover i ≫ q) = b ≫ (Embedded.FamilyOpenCover.overOpenCoverMap M D.cover j ≫ q)
    rw [← Category.assoc, ← Category.assoc, h]
  · simp only [Category.assoc, D.target_fac]
    change a ≫ (Embedded.FamilyOpenCover.overOpenCoverMap M D.cover i ≫ k) = b ≫ (Embedded.FamilyOpenCover.overOpenCoverMap M D.cover j ≫ k)
    rw [← Category.assoc, ← Category.assoc, h]

def PairChartCover.GrassmannPairChartCover.incidenceMatchingData : IdealOpenMatching.IdealOpenMatchingData D.cover :=
  HilbertConstruction.Over.IdealMatching.overIdealOpenMatchingData M D.cover (D.incidenceLocalIdeal F)
    (D.incidenceLocalIdeal_compatible F)

def PairChartCover.GrassmannPairChartCover.incidenceIdeal : M.left.IdealSheafData := (D.incidenceMatchingData F).glue

theorem PairChartCover.GrassmannPairChartCover.incidenceIdeal_comap (i : D.cover.I₀) :
    (D.incidenceIdeal F).comap (D.cover.f i) = D.incidenceLocalIdeal F i :=
  (D.incidenceMatchingData F).glue_comap i

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann
