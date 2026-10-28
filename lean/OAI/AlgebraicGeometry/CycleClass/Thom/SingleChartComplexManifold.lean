import OAI.AlgebraicGeometry.CycleClass.Thom.LocalDualLocalInverse

/-! # Single Chart Complex Manifold -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SingleChartComplexManifold.Constructions

noncomputable section

/-! A specified global complex chart supplies the actual manifold and point-class transport. -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.CanonicalLocalDual.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.LocalDualLocalInverse.Constructions.CanonicalNaturality

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (d : ℕ) {M : Type} [TopologicalSpace M] [Nonempty M] (e : M ≃ₜ (Fin d → ℂ))

@[instance_reducible]
def coordinateChartedSpace : ChartedSpace (Fin d → ℂ) M := e.isOpenEmbedding.singletonChartedSpace

theorem coordinateManifold :
    letI := coordinateChartedSpace d e
    IsManifold 𝓘(ℂ, Fin d → ℂ) ω M :=
  e.isOpenEmbedding.isManifold_singleton

def coordinateDiffeomorph :
    letI := coordinateChartedSpace d e
    Diffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) M (Fin d → ℂ) ω := by
  letI := coordinateChartedSpace d e
  refine { toEquiv := e.toEquiv
           contMDiff_toFun := contMDiff_isOpenEmbedding e.isOpenEmbedding
           contMDiff_invFun := ?_ }
  have h : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω (e ∘ e.symm) := by
    have hec : e ∘ e.symm = (id : (Fin d → ℂ) → (Fin d → ℂ)) :=
      funext e.apply_symm_apply
    rw [hec]
    exact contMDiff_id
  exact h.of_comp_isOpenEmbedding e.isOpenEmbedding

variable [T2Space M]

theorem pointClass_chart (x : M) :
    letI := coordinateChartedSpace d e
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of (Fin d → ℂ)) e).hom
      (LocalDualLocalInverse.Constructions.CanonicalNaturality.injectivePunctureMapsTo _ e.injective x) (2 * d) (CanonicalLocalDual.Constructions.canonicalLocalDual d (e x)) =
      CanonicalLocalDual.Constructions.canonicalLocalDual d x := by
  let := coordinateChartedSpace d e
  let := coordinateManifold d e
  exact LocalDualLocalInverse.Constructions.CanonicalNaturality.canonicalLocalDual_pullback d
    (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of (Fin d → ℂ)) e).hom
    e.injective (coordinateDiffeomorph d e).isLocalDiffeomorph x

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SingleChartComplexManifold.Constructions
