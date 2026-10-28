import OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion

/-! # Open Embedding -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Product.OpenEmbedding.Constructions

noncomputable section

/-! Taking the product with complex coordinate space preserves an actual open embedding and its bijective holomorphic differential. -/

open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {M N E G F : Type} [TopologicalSpace M] [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E M]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace G N]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  (j : M → N) (hj : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, G) ω j)

local instance (priority := low) : ChartedSpace (E × F) (M × F) := prodChartedSpace E M F F
local instance (priority := low) : ChartedSpace (G × F) (N × F) := prodChartedSpace G N F F

include hj in
theorem productMap_analytic : ContMDiff 𝓘(ℂ, E × F) 𝓘(ℂ, G × F) ω (Prod.map j (id : F → F)) := by
  simp only [modelWithCornersSelf_prod]
  exact hj.prodMap (show ContMDiff 𝓘(ℂ, F) 𝓘(ℂ, F) ω id from contMDiff_id)

omit [ChartedSpace E M] [ChartedSpace G N] [NormedSpace ℂ F] in
theorem productMap_openEmbedding (hji : Topology.IsOpenEmbedding j) :
    Topology.IsOpenEmbedding (Prod.map j (id : F → F)) := hji.prodMap .id

include hj in
theorem productMap_mfderiv_bijective
    (hd : ∀ x, Function.Bijective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G) j x)) (x : M × F) :
    Function.Bijective (mfderiv 𝓘(ℂ, E × F) 𝓘(ℂ, G × F) (Prod.map j (id : F → F)) x) := by
  have hi : MDifferentiableAt 𝓘(ℂ, F) 𝓘(ℂ, F) (id : F → F) x.2 := mdifferentiableAt_id
  rw [modelWithCornersSelf_prod, modelWithCornersSelf_prod,
    mfderiv_prodMap (hj.mdifferentiableAt (by simp)) hi, mfderiv_id]
  change Function.Bijective (Prod.map (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G) j x.1) (id : F → F))
  constructor
  · intro v w hvw
    apply Prod.ext
    · exact (hd x.1).injective (congrArg Prod.fst hvw)
    · exact congrArg (Prod.snd : G × F → F) hvw
  · rintro ⟨v, w⟩
    obtain ⟨a, ha⟩ := (hd x.1).surjective v
    exact ⟨(a, w), Prod.ext ha rfl⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Product.OpenEmbedding.Constructions
