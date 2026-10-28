import OAI.AlgebraicGeometry.CycleClass.Thom.Degree

/-! # Local Ext -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.LocalExt.Constructions.ThomClass

noncomputable section

/-! Supported classes in the Thom degree are determined by their actual normal-chart restrictions. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass

variable {E F M N : Type}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℂ, F) ω N] [MetrizableSpace N]
  (f : M → N) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω f)
  (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x))
  (he : Topology.IsClosedEmbedding f) (p : ℕ) (hp : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E F = p)

include hf hi he hp in
theorem normalPair_ext (P : ∀ x, ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) f x)
    (hP : ∀ x, (P x).ambientChart.MDifferentiable 𝓘(ℂ, F) 𝓘(ℂ, E × (Fin p → ℂ)))
    (a b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ (2 * p))
    (hab : ∀ x, Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (Set.range f)ᶜ (P x).openNeighborhood (2 * p) a =
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N)
        (Set.range f)ᶜ (P x).openNeighborhood (2 * p) b) : a = b := by
  let t := Degree.Constructions.ThomClass.complexThomClassInDegree f hf hi he p hp
  have h : a - b + t = t := Degree.Constructions.ThomClass.complexThomClassInDegree_unique f hf hi he p hp P hP (a - b + t) (by
    intro x
    rw [map_add, map_sub, hab x, sub_self, zero_add]
    exact Degree.Constructions.ThomClass.complexThomClassInDegree_restrict f hf hi he p hp x (P x) (hP x))
  exact sub_eq_zero.mp (add_right_cancel (h.trans (zero_add t).symm))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.LocalExt.Constructions.ThomClass
