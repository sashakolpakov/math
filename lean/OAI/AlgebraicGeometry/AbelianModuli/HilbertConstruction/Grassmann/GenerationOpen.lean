import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.GenerationBaseChange

/-! # Generation Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann

noncomputable section

/-! A canonical global generation open, independent of the cover and compatible with arbitrary base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν κ μ α : Type u}
variable [Fintype ι] [Fintype ν] [Fintype κ] [Fintype μ] [Fintype α]
variable [DecidableEq ι] [DecidableEq ν] [DecidableEq κ] [DecidableEq μ] [DecidableEq α]
variable {S : Scheme.{u}} {M T : Over S}
variable {q : M ⟶ ParameterScheme.grassmannParameterScheme (ι := ι) (ν := ν) S}
variable {k : M ⟶ ParameterScheme.grassmannParameterScheme (ι := κ) (ν := μ) S}

theorem PairChartCover.GrassmannPairChartCover.generationOpen_independent (D E : PairChartCover.GrassmannPairChartCover q k)
    (F : α → Matrix μ ν Γ(M.left, ⊤)) (hF : ∀ t, IncidenceCondition.GrassmannIncidenceCondition q k (F t) (𝟙 M)) :
    D.generationOpen F hF = E.generationOpen F hF := by
  apply Open.SubsetGluing.opens_eq_of_open_cover D.cover
  intro i
  let c := Embedded.FamilyOpenCover.overOpenCoverMap M D.cover i
  rw [D.generationOpen_preimage]
  symm
  exact (E.generationOpen_pullback F hF c).trans
    ((E.pullback c).generationOpen_eq_chart (fun t => (F t).map c.left.appTop.hom)
      (fun t => GenerationBaseChange.grassmannIncidence_identity_baseChange (F t) (hF t) c)
      (D.sourceColumns i) (D.targetColumns i) (D.sourceLift i) (D.targetLift i)
      (D.source_fac i) (D.target_fac i))

def GenerationOpen.grassmannGenerationOpen
    (q : M ⟶ ParameterScheme.grassmannParameterScheme (ι := ι) (ν := ν) S)
    (k : M ⟶ ParameterScheme.grassmannParameterScheme (ι := κ) (ν := μ) S)
    (F : α → Matrix μ ν Γ(M.left, ⊤)) (hF : ∀ t, IncidenceCondition.GrassmannIncidenceCondition q k (F t) (𝟙 M)) :
    M.left.Opens := (PairChartCover.grassmannPairChartCover q k).generationOpen F hF

theorem GenerationOpen.grassmannGenerationOpen_baseChange
    (F : α → Matrix μ ν Γ(M.left, ⊤)) (hF : ∀ t, IncidenceCondition.GrassmannIncidenceCondition q k (F t) (𝟙 M))
    (f : T ⟶ M) :
    f.left ⁻¹ᵁ GenerationOpen.grassmannGenerationOpen q k F hF =
      GenerationOpen.grassmannGenerationOpen (f ≫ q) (f ≫ k) (fun t => (F t).map f.left.appTop.hom)
        (fun t => GenerationBaseChange.grassmannIncidence_identity_baseChange (F t) (hF t) f) :=
  ((PairChartCover.grassmannPairChartCover q k).generationOpen_pullback F hF f).trans
    (PairChartCover.GrassmannPairChartCover.generationOpen_independent _ _ _ _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann
