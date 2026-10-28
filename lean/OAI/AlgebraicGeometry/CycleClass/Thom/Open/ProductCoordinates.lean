import OAI.AlgebraicGeometry.CycleClass.Thom.Product.SliceDifferential
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.InclusionDifferential
import OAI.AlgebraicGeometry.CycleClass.Thom.AnalyticLocalInverseAt
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OpenNormal

/-! # Product Coordinates -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Open.ProductCoordinates.Constructions

noncomputable section

/-! Flattened coordinates on the actual open product are holomorphic local diffeomorphisms. -/

open _root_.TopologicalSpace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OpenNormal.Constructions
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Product.SliceDifferential.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.InclusionDifferential.Constructions.Manifold OAI.AlgebraicGeometry.CycleClass.Thom.AnalyticLocalInverseAt.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {p d : ℕ} (U : Opens (Fin p → ℂ))
  (e : ((Fin p → ℂ) × (Fin d → ℂ)) ≃L[ℂ] (Fin (p + d) → ℂ))

local instance (priority := low) : ChartedSpace ((Fin p → ℂ) × (Fin d → ℂ)) (U × (Fin d → ℂ)) :=
  prodChartedSpace (Fin p → ℂ) U (Fin d → ℂ) (Fin d → ℂ)

def flatOpenCoordinate (z : U × (Fin d → ℂ)) : Fin (p + d) → ℂ := e (z.1.val, z.2)

theorem flatOpenCoordinate_isOpenEmbedding : Topology.IsOpenEmbedding (flatOpenCoordinate U e) :=
  e.toHomeomorph.isOpenEmbedding.comp
    (U.isOpen.isOpenEmbedding_subtypeVal.prodMap Topology.IsOpenEmbedding.id)

theorem productInclusion_analytic :
    ContMDiff 𝓘(ℂ, (Fin p → ℂ) × (Fin d → ℂ)) 𝓘(ℂ, (Fin p → ℂ) × (Fin d → ℂ)) ω
      (fun z : U × (Fin d → ℂ) => (z.1.val, z.2)) := by
  have hf : ContMDiff 𝓘(ℂ, (Fin p → ℂ) × (Fin d → ℂ)) 𝓘(ℂ, Fin p → ℂ) ω
      (fun z : U × (Fin d → ℂ) => z.1.val) := by
    rw [modelWithCornersSelf_prod]
    exact (show ContMDiff 𝓘(ℂ, Fin p → ℂ) 𝓘(ℂ, Fin p → ℂ) ω
      (Subtype.val : U → (Fin p → ℂ)) from contMDiff_subtype_val).comp contMDiff_fst
  have hs : ContMDiff 𝓘(ℂ, (Fin p → ℂ) × (Fin d → ℂ)) 𝓘(ℂ, Fin d → ℂ) ω
      (Prod.snd : U × (Fin d → ℂ) → (Fin d → ℂ)) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_snd
  exact hf.prodMk_space hs

theorem productInclusion_mfderiv (z : U × (Fin d → ℂ)) :
    mfderiv 𝓘(ℂ, (Fin p → ℂ) × (Fin d → ℂ)) 𝓘(ℂ, (Fin p → ℂ) × (Fin d → ℂ))
      (fun a : U × (Fin d → ℂ) => (a.1.val, a.2)) z =
        ContinuousLinearMap.id ℂ ((Fin p → ℂ) × (Fin d → ℂ)) := by
  have hs := (show ContMDiff 𝓘(ℂ, Fin p → ℂ) 𝓘(ℂ, Fin p → ℂ) 1
    (Subtype.val : U → (Fin p → ℂ)) from contMDiff_subtype_val).mdifferentiableAt (x := z.1) one_ne_zero
  have h := Product.SliceDifferential.Constructions.product_slice_mfderiv (Subtype.val : U → (Fin p → ℂ)) z.1 z.2 hs
  rw [InclusionDifferential.Constructions.Manifold.mfderiv_subtypeVal] at h
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact h

theorem flatOpenCoordinate_analytic :
    ContMDiff 𝓘(ℂ, (Fin p → ℂ) × (Fin d → ℂ)) 𝓘(ℂ, Fin (p + d) → ℂ) ω
      (flatOpenCoordinate U e) := e.contDiff.contMDiff.comp (productInclusion_analytic U)

theorem flatOpenCoordinate_mfderiv (z : U × (Fin d → ℂ)) :
    mfderiv 𝓘(ℂ, (Fin p → ℂ) × (Fin d → ℂ)) 𝓘(ℂ, Fin (p + d) → ℂ)
      (flatOpenCoordinate U e) z = e.toContinuousLinearMap := by
  have hs := (productInclusion_analytic U).mdifferentiable (show (ω : ℕ∞ω) ≠ 0 by simp) z
  have hd := (e.toContinuousLinearMap.hasMFDerivAt.comp z hs.hasMFDerivAt).mfderiv
  rw [productInclusion_mfderiv U z] at hd
  exact hd.trans (by ext a; rfl)

theorem flatOpenCoordinate_localInverse (z : U × (Fin d → ℂ)) :
    IsLocalDiffeomorphAt 𝓘(ℂ, (Fin p → ℂ) × (Fin d → ℂ)) 𝓘(ℂ, Fin (p + d) → ℂ) ω
      (flatOpenCoordinate U e) z := by
  let : IsManifold 𝓘(ℂ, (Fin p → ℂ) × (Fin d → ℂ)) ω (U × (Fin d → ℂ)) :=
    Product.Immersion.Constructions.productModel_isManifold
  apply AnalyticLocalInverseAt.Constructions.isLocalDiffeomorphAt_of_bijective_mfderiv _ _ (flatOpenCoordinate_analytic U e z)
  rw [flatOpenCoordinate_mfderiv U e z]
  exact e.bijective

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Open.ProductCoordinates.Constructions
