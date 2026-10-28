import OAI.AlgebraicGeometry.CycleClass.Thom.Product.Immersion

/-! # Slice Differential -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Product.SliceDifferential.Constructions

noncomputable section

/-! Differentials of the actual projection and product of a slice with the identity. -/

open scoped _root_.Manifold

variable {S N L U A F W : Type}
  [NormedAddCommGroup U] [NormedSpace ℂ U]
  [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [TopologicalSpace S] [ChartedSpace U S]
  [TopologicalSpace N] [ChartedSpace A N]
  [TopologicalSpace L] [ChartedSpace W L]

local instance : ChartedSpace (A × F) (N × F) := prodChartedSpace A N F F
local instance : ChartedSpace (U × F) (S × F) := prodChartedSpace U S F F

theorem projection_mfderiv (i : L → N × F) (y : L)
    (hi : MDifferentiableAt 𝓘(ℂ, W) 𝓘(ℂ, A × F) i y) :
    mfderiv 𝓘(ℂ, W) 𝓘(ℂ, A) (Prod.fst ∘ i) y =
      (ContinuousLinearMap.fst ℂ A F).comp (mfderiv 𝓘(ℂ, W) 𝓘(ℂ, A × F) i y) := by
  rw [modelWithCornersSelf_prod] at hi ⊢
  rw [mfderiv_comp y mdifferentiableAt_fst hi, mfderiv_fst]
  rfl

theorem product_slice_mfderiv (s : S → N) (u : S) (v : F)
    (hs : MDifferentiableAt 𝓘(ℂ, U) 𝓘(ℂ, A) s u) :
    mfderiv 𝓘(ℂ, U × F) 𝓘(ℂ, A × F) (Prod.map s (id : F → F)) (u, v) =
      (mfderiv 𝓘(ℂ, U) 𝓘(ℂ, A) s u).prodMap (ContinuousLinearMap.id ℂ F) := by
  rw [modelWithCornersSelf_prod, modelWithCornersSelf_prod,
    mfderiv_prodMap hs mdifferentiableAt_id, mfderiv_id]
  rfl

theorem product_slice_comp_mfderiv {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (s : S → N) (n : N × F → V) (u : S) (v : F)
    (hs : MDifferentiableAt 𝓘(ℂ, U) 𝓘(ℂ, A) s u)
    (hn : MDifferentiableAt 𝓘(ℂ, A × F) 𝓘(ℂ, V) n (s u, v)) :
    mfderiv 𝓘(ℂ, U × F) 𝓘(ℂ, V) (n ∘ Prod.map s (id : F → F)) (u, v) =
      (mfderiv 𝓘(ℂ, A × F) 𝓘(ℂ, V) n (s u, v)).comp
        ((mfderiv 𝓘(ℂ, U) 𝓘(ℂ, A) s u).prodMap (ContinuousLinearMap.id ℂ F)) := by
  have hp : MDifferentiableAt 𝓘(ℂ, U × F) 𝓘(ℂ, A × F)
      (Prod.map s (id : F → F)) (u, v) := by
    rw [modelWithCornersSelf_prod, modelWithCornersSelf_prod]
    exact hs.prodMap mdifferentiableAt_id
  rw [mfderiv_comp (u, v) hn hp, product_slice_mfderiv s u v hs]
  rfl

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Product.SliceDifferential.Constructions
