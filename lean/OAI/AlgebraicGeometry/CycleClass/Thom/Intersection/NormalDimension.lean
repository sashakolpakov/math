import OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.NormalPair
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Normal Dimension -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.NormalDimension.Constructions

noncomputable section

/-! The tangent model for a transverse intersection has its expected
dimension. Rank-nullity removes the choice of a kernel identification
from the simultaneous normal-pair construction. -/

open scoped ContDiff _root_.Topology _root_.Manifold

open OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.NormalPair.Constructions

variable {M L T N E F D G : Type} [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup D] [NormedSpace ℂ D] [FiniteDimensional ℂ D]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace G N]
  {p q : ℕ} {u : M → N} {v : L → N} {x : M} {y : L}
  (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) u x)
  (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair F (Fin q → ℂ) v y)
  (e : ((Fin p → ℂ) × (Fin q → ℂ)) ≃L[ℂ] (Fin (p + q) → ℂ))

theorem exists_intersection_normalPair_of_dimension (w : T → N) (z : T)
    (hxy : u x = v y) (hxz : u x = w z)
    (hw : Set.range w = Set.range u ∩ Set.range v)
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × (Fin p → ℂ)))
    (hPi : ContMDiffOn 𝓘(ℂ, E × (Fin p → ℂ)) 𝓘(ℂ, G) ω
      P.ambientChart.symm P.ambientChart.target)
    (hQ : ContMDiffOn 𝓘(ℂ, G) 𝓘(ℂ, F × (Fin q → ℂ)) ω
      Q.ambientChart Q.ambientChart.source)
    (hs : Function.Surjective (fderiv ℂ (NormalPair.Constructions.intersectionEquations P Q e) 0))
    (hd : Module.finrank ℂ D + (p + q) = Module.finrank ℂ G) :
    ∃ R : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair D (Fin (p + q) → ℂ) w z,
      R.neighborhood ⊆ P.neighborhood ∩ Q.neighborhood ∧
      R.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, D × (Fin (p + q) → ℂ)) ∧
      ∀ a : R.neighborhood, R.normalCoordinate a =
        e ((P.ambientChart a.val).2, (Q.ambientChart a.val).2) := by
  have hdim := (hP.mfderiv P.point_mem_source).toLinearEquiv.finrank_eq
  change Module.finrank ℂ G = Module.finrank ℂ (E × (Fin p → ℂ)) at hdim
  have hrank := (fderiv ℂ (NormalPair.Constructions.intersectionEquations P Q e) 0).toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_fin_fun] at hrank
  have hk : Module.finrank ℂ (fderiv ℂ (NormalPair.Constructions.intersectionEquations P Q e) 0).ker =
      Module.finrank ℂ D := by omega
  exact NormalPair.Constructions.exists_intersection_normalPair P Q e w z hxy hxz hw hP hPi hQ hs
    (ContinuousLinearEquiv.ofFinrankEq hk)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.NormalDimension.Constructions
