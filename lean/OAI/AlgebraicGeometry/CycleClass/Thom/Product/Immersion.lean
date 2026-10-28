import OAI.AlgebraicGeometry.CycleClass.Thom.Product.NormalDifferentiable
import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexNormalAtlas

/-! # Immersion -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Product.Immersion.Constructions

noncomputable section

/-! Actual manifold structures, differential injectivity, and dimensions
for products of complex immersions. -/

open OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexNormalAtlas.Cycles
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The native product atlas, displayed over the underlying product model. -/
abbrev productModelCharted (E M F M' : Type)
    [TopologicalSpace E] [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace F] [TopologicalSpace M'] [ChartedSpace F M'] :
    ChartedSpace (E × F) (M × M') := prodChartedSpace E M F M'

variable {E F G H M M' N N' : Type}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
  [TopologicalSpace M'] [ChartedSpace F M'] [IsManifold 𝓘(ℂ, F) ω M']
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold 𝓘(ℂ, G) ω N]
  [TopologicalSpace N'] [ChartedSpace H N'] [IsManifold 𝓘(ℂ, H) ω N']

local instance (priority := low) : ChartedSpace (E × F) (M × M') := productModelCharted E M F M'
local instance (priority := low) : ChartedSpace (G × H) (N × N') := productModelCharted G N H N'

theorem productModel_isManifold : IsManifold 𝓘(ℂ, E × F) ω (M × M') := by
  rw [modelWithCornersSelf_prod]
  exact inferInstanceAs (IsManifold (𝓘(ℂ, E).prod 𝓘(ℂ, F)) ω (M × M'))

variable (u : M → N) (v : M' → N')
  (hu : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, G) ω u)
  (hv : ContMDiff 𝓘(ℂ, F) 𝓘(ℂ, H) ω v)

include hu hv in
omit [IsManifold 𝓘(ℂ, E) ω M] [IsManifold 𝓘(ℂ, F) ω M']
  [IsManifold 𝓘(ℂ, G) ω N] [IsManifold 𝓘(ℂ, H) ω N'] in
theorem productImmersion_contMDiff :
    ContMDiff 𝓘(ℂ, E × F) 𝓘(ℂ, G × H) ω (Prod.map u v) := by
  rw [modelWithCornersSelf_prod, modelWithCornersSelf_prod]
  exact hu.prodMap hv

include hu hv in
omit [IsManifold 𝓘(ℂ, E) ω M] [IsManifold 𝓘(ℂ, F) ω M']
  [IsManifold 𝓘(ℂ, G) ω N] [IsManifold 𝓘(ℂ, H) ω N'] in
theorem productImmersion_injective_mfderiv
    (hiu : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G) u x))
    (hiv : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, F) 𝓘(ℂ, H) v x))
    (z : M × M') :
    Function.Injective (mfderiv 𝓘(ℂ, E × F) 𝓘(ℂ, G × H) (Prod.map u v) z) := by
  rw [modelWithCornersSelf_prod, modelWithCornersSelf_prod,
    mfderiv_prodMap (hu.mdifferentiable (by simp) z.1) (hv.mdifferentiable (by simp) z.2)]
  intro a b hab
  exact Prod.ext (hiu z.1 (congrArg Prod.fst hab)) (hiv z.2 (congrArg Prod.snd hab))

omit [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
    [TopologicalSpace M'] [ChartedSpace F M'] [IsManifold 𝓘(ℂ, F) ω M']
    [TopologicalSpace N] [ChartedSpace G N] [IsManifold 𝓘(ℂ, G) ω N]
    [TopologicalSpace N'] [ChartedSpace H N'] [IsManifold 𝓘(ℂ, H) ω N'] in
theorem complexImmersionCodimension_prod [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    [FiniteDimensional ℂ G] [FiniteDimensional ℂ H]
    (hEG : Module.finrank ℂ E ≤ Module.finrank ℂ G)
    (hFH : Module.finrank ℂ F ≤ Module.finrank ℂ H) :
    Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension (E × F) (G × H) =
      Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E G + Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension F H := by
  simp only [Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension, Module.finrank_prod]
  omega

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Product.Immersion.Constructions
