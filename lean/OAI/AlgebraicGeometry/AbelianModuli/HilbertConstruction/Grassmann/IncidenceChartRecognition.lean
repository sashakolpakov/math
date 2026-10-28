import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.IncidenceBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.IncidenceScheme

/-! # Incidence Chart Recognition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann

noncomputable section

/-!
Recognition of the global incidence ideal on any pair of normalized charts.
This proves that the construction is independent of the chosen chart cover.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν κ μ : Type u}
variable [Fintype ι] [Fintype ν] [Fintype κ] [Fintype μ]
variable [DecidableEq ι] [DecidableEq ν] [DecidableEq κ] [DecidableEq μ]
variable {S : Scheme.{u}} {M : Over S}
variable {q : M ⟶ ParameterScheme.grassmannParameterScheme (ι := ι) (ν := ν) S}
variable {k : M ⟶ ParameterScheme.grassmannParameterScheme (ι := κ) (ν := μ) S}

theorem PairChartCover.GrassmannPairChartCover.incidenceIdeal_eq_chart (D : PairChartCover.GrassmannPairChartCover q k)
    (F : Matrix μ ν Γ(M.left, ⊤)) (a : ι → ν) (b : κ → μ)
    (f : M ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart a S) (g : M ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart b S)
    (hf : f ≫ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap a S = q) (hg : g ≫ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap b S = k) :
    D.incidenceIdeal F = ChartLoci.grassmannChartIncidenceIdeal a b f g F := by
  apply ClosedFamily.OpenEquality.ideal_eq_of_open_cover D.cover
  intro i
  let c := Embedded.FamilyOpenCover.overOpenCoverMap M D.cover i
  change (D.incidenceIdeal F).comap c.left =
    (ChartLoci.grassmannChartIncidenceIdeal a b f g F).comap c.left
  rw [ChartLoci.grassmannChartIncidenceIdeal_comap]
  refine (D.incidenceIdeal_comap F i).trans ?_
  change ChartLoci.grassmannChartIncidenceIdeal (D.sourceColumns i) (D.targetColumns i)
    (D.sourceLift i) (D.targetLift i) (F.map c.left.appTop.hom) =
      ChartLoci.grassmannChartIncidenceIdeal a b (c ≫ f) (c ≫ g) (F.map c.left.appTop.hom)
  apply ChartLoci.grassmannChartIncidenceIdeal_chart_independent
  · exact (D.source_fac i).trans
      ((congrArg (fun h => c ≫ h) hf.symm).trans (Category.assoc _ _ _).symm)
  · exact (D.target_fac i).trans
      ((congrArg (fun h => c ≫ h) hg.symm).trans (Category.assoc _ _ _).symm)

theorem PairChartCover.GrassmannPairChartCover.incidenceIdeal_independent
    (D E : PairChartCover.GrassmannPairChartCover q k) (F : Matrix μ ν Γ(M.left, ⊤)) :
    D.incidenceIdeal F = E.incidenceIdeal F := by
  apply ClosedFamily.OpenEquality.ideal_eq_of_open_cover D.cover
  intro i
  let c := Embedded.FamilyOpenCover.overOpenCoverMap M D.cover i
  refine (D.incidenceIdeal_comap F i).trans ?_
  symm
  exact (E.incidenceIdeal_pullback F c).trans
    ((E.pullback c).incidenceIdeal_eq_chart (F.map c.left.appTop.hom)
      (D.sourceColumns i) (D.targetColumns i) (D.sourceLift i) (D.targetLift i)
      (D.source_fac i) (D.target_fac i))

theorem IncidenceChartRecognition.grassmannIncidenceIdeal_baseChange (F : Matrix μ ν Γ(M.left, ⊤))
    {T : Over S} (f : T ⟶ M) :
    (IncidenceScheme.grassmannIncidenceIdeal q k F).comap f.left =
      IncidenceScheme.grassmannIncidenceIdeal (f ≫ q) (f ≫ k) (F.map f.left.appTop.hom) :=
  ((PairChartCover.grassmannPairChartCover q k).incidenceIdeal_pullback F f).trans
    (PairChartCover.GrassmannPairChartCover.incidenceIdeal_independent _ _ _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann
