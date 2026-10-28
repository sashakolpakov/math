import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.GenerationRecognition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.IncidenceEquivalence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.IncidenceUniversality

/-! # Generation Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann

noncomputable section

/-! The global generation locus commutes with arbitrary parameter base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν κ μ α : Type u}
variable [Fintype ι] [Fintype ν] [Fintype κ] [Fintype μ] [Fintype α]
variable [DecidableEq ι] [DecidableEq ν] [DecidableEq κ] [DecidableEq μ] [DecidableEq α]
variable {S : Scheme.{u}} {M T : Over S}
variable {q : M ⟶ ParameterScheme.grassmannParameterScheme (ι := ι) (ν := ν) S}
variable {k : M ⟶ ParameterScheme.grassmannParameterScheme (ι := κ) (ν := μ) S}

theorem GenerationBaseChange.grassmannIncidence_identity_baseChange (F : Matrix μ ν Γ(M.left, ⊤))
    (hF : IncidenceCondition.GrassmannIncidenceCondition q k F (𝟙 M)) (f : T ⟶ M) :
    IncidenceCondition.GrassmannIncidenceCondition (f ≫ q) (f ≫ k) (F.map f.left.appTop.hom) (𝟙 T) := by
  apply (Affine.IncidenceEquivalence.grassmannIncidenceCondition_pullback q k F f).mp
  have h : IncidenceCondition.GrassmannIncidenceCondition q k F (f ≫ 𝟙 M) :=
    (IncidenceUniversality.grassmannIncidenceSubfunctor q k F).map f.op hF
  rwa [Category.comp_id] at h

theorem PairChartCover.GrassmannPairChartCover.generationOpen_pullback (D : PairChartCover.GrassmannPairChartCover q k)
    (F : α → Matrix μ ν Γ(M.left, ⊤)) (hF : ∀ t, IncidenceCondition.GrassmannIncidenceCondition q k (F t) (𝟙 M))
    (f : T ⟶ M) :
    f.left ⁻¹ᵁ D.generationOpen F hF =
      (D.pullback f).generationOpen (fun t => (F t).map f.left.appTop.hom)
        (fun t => GenerationBaseChange.grassmannIncidence_identity_baseChange (F t) (hF t) f) := by
  apply Open.SubsetGluing.opens_eq_of_open_cover (D.pullback f).cover
  intro i
  change D.cover.I₀ at i
  let l := PairChartPullback.overOpenCoverPullbackProjection f D.cover i
  let c := (D.pullback f).cover.f i
  have hl : l.left ≫ D.cover.f i = c ≫ f.left :=
    congrArg Over.Hom.left (PairChartPullback.overOpenCoverPullbackProjection_fac f D.cover i)
  refine (Scheme.Hom.comp_preimage c f.left (D.generationOpen F hF)).symm.trans ?_
  refine (congrArg (fun g => g ⁻¹ᵁ D.generationOpen F hF) hl.symm).trans ?_
  refine (Scheme.Hom.comp_preimage l.left (D.cover.f i) (D.generationOpen F hF)).trans ?_
  refine (congrArg (fun U => l.left ⁻¹ᵁ U) (D.generationOpen_preimage F hF i)).trans ?_
  refine Eq.trans ?_ ((D.pullback f).generationOpen_preimage _ _ i).symm
  change l.left ⁻¹ᵁ GenerationCharts.grassmannChartGenerationOpen (D.sourceColumns i) (D.targetColumns i)
    (D.sourceLift i) (fun t => (F t).map (Embedded.FamilyOpenCover.overOpenCoverMap M D.cover i).left.appTop.hom) =
      GenerationCharts.grassmannChartGenerationOpen (D.sourceColumns i) (D.targetColumns i) (l ≫ D.sourceLift i)
        (fun t => ((F t).map f.left.appTop.hom).map
          (Embedded.FamilyOpenCover.overOpenCoverMap T (D.pullback f).cover i).left.appTop.hom)
  rw [GenerationCharts.grassmannChartGenerationOpen_preimage]
  apply congrArg (GenerationCharts.grassmannChartGenerationOpen (D.sourceColumns i) (D.targetColumns i) (l ≫ D.sourceLift i))
  funext t
  change (F t).map (l ≫ Embedded.FamilyOpenCover.overOpenCoverMap M D.cover i).left.appTop.hom =
    (F t).map (Embedded.FamilyOpenCover.overOpenCoverMap T (D.pullback f).cover i ≫ f).left.appTop.hom
  exact congrArg (fun g => (F t).map g.left.appTop.hom) (PairChartPullback.overOpenCoverPullbackProjection_fac f D.cover i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann
