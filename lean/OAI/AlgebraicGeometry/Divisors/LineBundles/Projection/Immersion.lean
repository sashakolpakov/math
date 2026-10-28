import OAI.AlgebraicGeometry.CycleClass.Thom.Product.Immersion

/-! # Immersion -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.Immersion.BundleCycles

noncomputable section

/-! Geometry of the actual product immersion with an identity factor. -/

open OAI.AlgebraicGeometry.CycleClass.Thom.Product.Immersion.Constructions
open scoped _root_.Manifold ContDiff

variable {E F G M B N : Type}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
    [TopologicalSpace B] [ChartedSpace F B] [IsManifold 𝓘(ℂ, F) ω B]
    [TopologicalSpace N] [ChartedSpace G N] [IsManifold 𝓘(ℂ, G) ω N]

local instance : ChartedSpace (F × E) (B × M) := CycleClass.Thom.Product.Immersion.Constructions.productModelCharted F B E M
local instance : ChartedSpace (F × G) (B × N) := CycleClass.Thom.Product.Immersion.Constructions.productModelCharted F B G N

omit [IsManifold 𝓘(ℂ, E) ω M] [IsManifold 𝓘(ℂ, F) ω B] [IsManifold 𝓘(ℂ, G) ω N] in
theorem projectionImmersion_contMDiff (u : M → N) (hu : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, G) ω u) :
    ContMDiff 𝓘(ℂ, F × E) 𝓘(ℂ, F × G) ω (Prod.map (id : B → B) u) :=
  CycleClass.Thom.Product.Immersion.Constructions.productImmersion_contMDiff id u contMDiff_id hu

omit [IsManifold 𝓘(ℂ, E) ω M] [IsManifold 𝓘(ℂ, F) ω B] [IsManifold 𝓘(ℂ, G) ω N] in
theorem projectionImmersion_injective_mfderiv (u : M → N)
    (hu : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, G) ω u)
    (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G) u x)) (z : B × M) :
    Function.Injective (mfderiv 𝓘(ℂ, F × E) 𝓘(ℂ, F × G) (Prod.map (id : B → B) u) z) := by
  apply CycleClass.Thom.Product.Immersion.Constructions.productImmersion_injective_mfderiv id u contMDiff_id hu _ hi z
  intro b
  rw [mfderiv_id]
  exact Function.injective_id

omit [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
    [TopologicalSpace B] [ChartedSpace F B] [IsManifold 𝓘(ℂ, F) ω B]
    [TopologicalSpace N] [ChartedSpace G N] [IsManifold 𝓘(ℂ, G) ω N] in
theorem projectionImmersion_codimension [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    [FiniteDimensional ℂ G] : CycleClass.Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension (F × E) (F × G) =
      CycleClass.Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E G := by
  simp only [CycleClass.Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension, Module.finrank_prod, Nat.add_sub_add_left]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.Immersion.BundleCycles
