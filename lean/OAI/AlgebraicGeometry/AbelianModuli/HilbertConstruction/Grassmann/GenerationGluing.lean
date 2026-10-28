import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.GenerationCharts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.OpenSubsetMatching
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.IncidenceCondition

/-! # Generation Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann

noncomputable section

/-! Compatible quotient multiplication maps have a globally defined open generation locus. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν κ μ α : Type u}
variable [Fintype ι] [Fintype ν] [Fintype κ] [Fintype μ] [Fintype α]
variable [DecidableEq ι] [DecidableEq ν] [DecidableEq κ] [DecidableEq μ] [DecidableEq α]
variable {S : Scheme.{u}} {M : Over S}
variable {q : M ⟶ ParameterScheme.grassmannParameterScheme (ι := ι) (ν := ν) S}
variable {k : M ⟶ ParameterScheme.grassmannParameterScheme (ι := κ) (ν := μ) S}

variable (D : PairChartCover.GrassmannPairChartCover q k) (F : α → Matrix μ ν Γ(M.left, ⊤))
variable (hF : ∀ t, IncidenceCondition.GrassmannIncidenceCondition q k (F t) (𝟙 M))

def PairChartCover.GrassmannPairChartCover.generationLocalOpen (i : D.cover.I₀) : (D.cover.X i).Opens :=
  GenerationCharts.grassmannChartGenerationOpen (D.sourceColumns i) (D.targetColumns i) (D.sourceLift i)
    (fun t => (F t).map (Embedded.FamilyOpenCover.overOpenCoverMap M D.cover i).left.appTop.hom)

include hF in
theorem PairChartCover.GrassmannPairChartCover.generationLocalOpen_compatible {T : Over S} (i j : D.cover.I₀)
    (a : T ⟶ Embedded.FamilyOpenCover.overOpenCoverObject M D.cover i) (b : T ⟶ Embedded.FamilyOpenCover.overOpenCoverObject M D.cover j)
    (h : a ≫ Embedded.FamilyOpenCover.overOpenCoverMap M D.cover i = b ≫ Embedded.FamilyOpenCover.overOpenCoverMap M D.cover j) :
    a.left ⁻¹ᵁ D.generationLocalOpen F i = b.left ⁻¹ᵁ D.generationLocalOpen F j := by
  have hFi : (fun t => ((F t).map (Embedded.FamilyOpenCover.overOpenCoverMap M D.cover i).left.appTop.hom).map a.left.appTop.hom) =
      (fun t => ((F t).map (Embedded.FamilyOpenCover.overOpenCoverMap M D.cover j).left.appTop.hom).map b.left.appTop.hom) := by
    funext t
    change (F t).map (a ≫ Embedded.FamilyOpenCover.overOpenCoverMap M D.cover i).left.appTop.hom =
      (F t).map (b ≫ Embedded.FamilyOpenCover.overOpenCoverMap M D.cover j).left.appTop.hom
    rw [h]
  change a.left ⁻¹ᵁ GenerationCharts.grassmannChartGenerationOpen (D.sourceColumns i) (D.targetColumns i)
    (D.sourceLift i) _ = b.left ⁻¹ᵁ GenerationCharts.grassmannChartGenerationOpen (D.sourceColumns j) (D.targetColumns j)
      (D.sourceLift j) _
  rw [GenerationCharts.grassmannChartGenerationOpen_preimage, GenerationCharts.grassmannChartGenerationOpen_preimage, ← hFi]
  apply GenerationCharts.grassmannChartGenerationOpen_independent
    (D.sourceColumns i) (D.sourceColumns j) (D.targetColumns i) (D.targetColumns j)
    (a ≫ D.sourceLift i) (b ≫ D.sourceLift j) (a ≫ D.targetLift i) (b ≫ D.targetLift j)
  · simp only [Category.assoc, D.source_fac]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ q) h).trans (Category.assoc _ _ _))
  · simp only [Category.assoc, D.target_fac]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ k) h).trans (Category.assoc _ _ _))
  · intro t
    have ht := hF t T (a ≫ Embedded.FamilyOpenCover.overOpenCoverMap M D.cover i)
      (D.sourceColumns i) (D.targetColumns i) (a ≫ D.sourceLift i) (a ≫ D.targetLift i)
      (by
        simp only [Category.assoc, D.source_fac, Category.id_comp]
        rfl)
      (by
        simp only [Category.assoc, D.target_fac, Category.id_comp]
        rfl)
    simp only [Category.comp_id] at ht
    exact ht

def PairChartCover.GrassmannPairChartCover.generationMatchingData : Open.SubsetGluing.OpenSubsetMatchingData D.cover :=
  HilbertConstruction.Over.OpenSubsetMatching.overOpenSubsetMatchingData M D.cover (D.generationLocalOpen F) (D.generationLocalOpen_compatible F hF)

def PairChartCover.GrassmannPairChartCover.generationOpen : M.left.Opens := (D.generationMatchingData F hF).glue

theorem PairChartCover.GrassmannPairChartCover.generationOpen_preimage (i : D.cover.I₀) :
    (D.cover.f i) ⁻¹ᵁ D.generationOpen F hF = D.generationLocalOpen F i :=
  (D.generationMatchingData F hF).glue_preimage i

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann
