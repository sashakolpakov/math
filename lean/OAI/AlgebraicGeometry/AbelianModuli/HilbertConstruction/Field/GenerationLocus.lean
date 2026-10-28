import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.GrassmannFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.GenerationCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.GenerationOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.IncidenceReflection

/-! # Generation Locus -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.GenerationLocus

noncomputable section

/-! Field-valued points of the global generation locus are exactly the compatible quotients whose relations are generated. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν κ μ α : Type u}
variable [Fintype ι] [Fintype ν] [Fintype κ] [Fintype μ] [Fintype α]
variable [DecidableEq ι] [DecidableEq ν] [DecidableEq κ] [DecidableEq μ] [DecidableEq α]
variable {S : Scheme.{u}} (L : Type u) [Field L] (f : Spec (CommRingCat.of L) ⟶ S)
variable (N : Module.Grassmannian L (ν → L) (Fintype.card ι))
variable (K : Module.Grassmannian L (μ → L) (Fintype.card κ)) (F : α → Matrix μ ν L)

theorem grassmannGenerationOpen_field_iff
    (hF : ∀ t, Grassmann.IncidenceCondition.GrassmannIncidenceCondition
      (Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv (CommRingCat.of L) f N)
      (Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv (CommRingCat.of L) f K)
      ((F t).map (Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom) (𝟙 (Over.mk f))) :
    Grassmann.GenerationOpen.grassmannGenerationOpen
      (Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv (CommRingCat.of L) f N)
      (Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv (CommRingCat.of L) f K)
      (fun t => (F t).map (Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom) hF = ⊤ ↔
        K.toSubmodule = ⨆ t, N.toSubmodule.map (Matrix.toLin' (F t)) := by
  let q := Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv (CommRingCat.of L) f N
  let k := Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv (CommRingCat.of L) f K
  obtain ⟨a, b, v, w, hv, hw⟩ := GrassmannFrames.fieldGrassmannPair_global_charts L f q k
  change (Grassmann.PairChartCover.grassmannPairChartCover q k).generationOpen
    (fun t => (F t).map (Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom) hF = ⊤ ↔ _
  rw [(Grassmann.PairChartCover.grassmannPairChartCover q k).generationOpen_eq_chart _ hF a b v w hv hw]
  exact Affine.GenerationCoordinates.grassmannChartGenerationOpen_affine_iff (CommRingCat.of L) f N K a b v w hv hw F
    (fun t => (Affine.IncidenceReflection.grassmannIncidence_affine_relations_iff (CommRingCat.of L) f N K (F t)).mp (hF t))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.GenerationLocus
