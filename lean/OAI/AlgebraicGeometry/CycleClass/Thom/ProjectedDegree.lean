import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree
import OAI.AlgebraicGeometry.CycleClass.Thom.Degree

/-! # Projected Degree -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ProjectedDegree.Constructions

noncomputable section

/-! Changing the displayed codimension of a genuine Thom class commutes
with its actual compact-fiber projection. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass

variable (d : ℕ) (X : TopCat.{0}) {M E F L : Type}
  [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [TopologicalSpace L] [ChartedSpace E L] [IsManifold 𝓘(ℂ, E) ω L]
  [ChartedSpace F (X × M)] [IsManifold 𝓘(ℂ, F) ω (X × M)] [MetrizableSpace (X × M)]
  (f : L → X × M) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω f)
  (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x))
  (he : Topology.IsClosedEmbedding f)
  (S : Set X) (K : Set M) (hK : IsCompact K) (hb : Set.range f ⊆ S ×ˢ K)

theorem projectAt_Thom_codimension (p r s : ℕ)
    (hr : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E F = r) (hs : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E F = s)
    (hn : p + 2 * d = 2 * r) (hm : p + 2 * d = 2 * s) :
    Supported.ProjectionDegree.Constructions.projectAt d X S K hK (Set.range f) hb p (2 * r) hn
      (Degree.Constructions.ThomClass.complexThomClassInDegree f hf hi he r hr) =
    Supported.ProjectionDegree.Constructions.projectAt d X S K hK (Set.range f) hb p (2 * s) hm
      (Degree.Constructions.ThomClass.complexThomClassInDegree f hf hi he s hs) := by
  have h : r = s := hr.symm.trans hs
  cases h
  rfl

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ProjectedDegree.Constructions
