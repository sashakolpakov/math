import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.GenerationGluing

/-! # Generation Recognition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann

noncomputable section

/-! A global normalized frame identifies the glued generation locus with its explicit determinant open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν κ μ α : Type u}
variable [Fintype ι] [Fintype ν] [Fintype κ] [Fintype μ] [Fintype α]
variable [DecidableEq ι] [DecidableEq ν] [DecidableEq κ] [DecidableEq μ] [DecidableEq α]
variable {S : Scheme.{u}} {M : Over S}
variable {q : M ⟶ ParameterScheme.grassmannParameterScheme (ι := ι) (ν := ν) S}
variable {k : M ⟶ ParameterScheme.grassmannParameterScheme (ι := κ) (ν := μ) S}

theorem PairChartCover.GrassmannPairChartCover.generationOpen_eq_chart (D : PairChartCover.GrassmannPairChartCover q k)
    (F : α → Matrix μ ν Γ(M.left, ⊤)) (hF : ∀ t, IncidenceCondition.GrassmannIncidenceCondition q k (F t) (𝟙 M))
    (a : ι → ν) (b : κ → μ) (v : M ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart a S) (w : M ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart b S)
    (hv : v ≫ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap a S = q) (hw : w ≫ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap b S = k) :
    D.generationOpen F hF = GenerationCharts.grassmannChartGenerationOpen a b v F := by
  apply Open.SubsetGluing.opens_eq_of_open_cover D.cover
  intro i
  let c := Embedded.FamilyOpenCover.overOpenCoverMap M D.cover i
  rw [D.generationOpen_preimage]
  change D.generationLocalOpen F i = c.left ⁻¹ᵁ GenerationCharts.grassmannChartGenerationOpen a b v F
  rw [GenerationCharts.grassmannChartGenerationOpen_preimage]
  apply GenerationCharts.grassmannChartGenerationOpen_independent (D.sourceColumns i) a (D.targetColumns i) b
    (D.sourceLift i) (c ≫ v) (D.targetLift i) (c ≫ w)
  · exact (D.source_fac i).trans
      ((congrArg (fun f => c ≫ f) hv.symm).trans (Category.assoc _ _ _).symm)
  · exact (D.target_fac i).trans
      ((congrArg (fun f => c ≫ f) hw.symm).trans (Category.assoc _ _ _).symm)
  · intro t
    have ht := hF t (Embedded.FamilyOpenCover.overOpenCoverObject M D.cover i) c
      (D.sourceColumns i) (D.targetColumns i) (D.sourceLift i) (D.targetLift i)
      (by
        simp only [Category.id_comp]
        exact D.source_fac i)
      (by
        simp only [Category.id_comp]
        exact D.target_fac i)
    simp only [Category.comp_id] at ht
    exact ht

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann
