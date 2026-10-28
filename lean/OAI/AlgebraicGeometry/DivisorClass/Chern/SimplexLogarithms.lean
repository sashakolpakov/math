import OAI.AlgebraicGeometry.DivisorClass.Chern.Logarithms
import OAI.AlgebraicGeometry.CycleClass.Geometric.SimplexFillings
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-! # Simplex Logarithms -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.SimplexLogarithms

noncomputable section

/-!
# ChernClass: actual continuous logarithms on singular simplices

The exponential covering map supplies logarithms on the contractible standard
simplex. Logarithm increments between two points are independent of the lift,
because two lifts differ by a constant integral exponential period.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Geometric.SimplexFillings.Cycles OAI.AlgebraicGeometry.DivisorClass.Chern.Logarithms.Construction
open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Covering-space lifting on the actual geometric simplex. -/
theorem exists_simplexLogarithm (n : ℕ)
    (f : C(Convexity.StdSimplex ℝ (Fin (n + 1)), ℂ)) (hf : ∀ x, f x ≠ 0) :
    ∃ l : C(Convexity.StdSimplex ℝ (Fin (n + 1)), ℂ), ∀ x, Complex.exp (l x) = f x := by
  let : ContractibleSpace (Convexity.StdSimplex ℝ (Fin (n + 1))) := CycleClass.Geometric.SimplexFillings.Cycles.stdSimplex_contractible n
  let : LocallyPathConnectedSpace (Convexity.StdSimplex ℝ (Fin (n + 1))) :=
    inferInstance
  let x₀ : Convexity.StdSimplex ℝ (Fin (n + 1)) := Convexity.StdSimplex.single 0
  obtain ⟨l, ⟨_, hl⟩, _⟩ := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts f
    (a₀ := x₀) (Complex.exp_log (hf x₀)) (fun x => hf x)
  exact ⟨l, fun x => congrFun hl x⟩

/-- One continuous logarithm chosen by the proved covering-space lift. -/
def simplexLogarithm (n : ℕ) (f : C(Convexity.StdSimplex ℝ (Fin (n + 1)), ℂ))
    (hf : ∀ x, f x ≠ 0) : C(Convexity.StdSimplex ℝ (Fin (n + 1)), ℂ) :=
  (exists_simplexLogarithm n f hf).choose

theorem exp_simplexLogarithm (n : ℕ) (f : C(Convexity.StdSimplex ℝ (Fin (n + 1)), ℂ))
    (hf : ∀ x, f x ≠ 0) (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    Complex.exp (simplexLogarithm n f hf x) = f x :=
  (exists_simplexLogarithm n f hf).choose_spec x

/-- On a connected domain, two genuine logarithms differ by a constant. -/
theorem logarithm_difference_constant {T : Type} [TopologicalSpace T] [PreconnectedSpace T]
    (l k : C(T, ℂ)) (he : ∀ x, Complex.exp (l x) = Complex.exp (k x)) (x y : T) :
    l x - k x = l y - k y := by
  have hp : ∀ z, Complex.exp ((l - k) z) * Complex.exp 0 = Complex.exp 0 := by
    intro z
    change Complex.exp (l z - k z) * Complex.exp 0 = Complex.exp 0
    rw [Complex.exp_sub, he, div_self (Complex.exp_ne_zero _), one_mul]
  have h := (Logarithms.Construction.isLocallyConstant_logarithmicDefect (l - k) 0 0 hp).apply_eq_of_preconnectedSpace x y
  simp only [ContinuousMap.sub_apply, ContinuousMap.zero_apply] at h
  have hx := Logarithms.Construction.logarithmicDefect_spec ((l - k) x) 0 0 (hp x)
  have hy := Logarithms.Construction.logarithmicDefect_spec ((l - k) y) 0 0 (hp y)
  simp only [add_zero, sub_zero, ContinuousMap.sub_apply] at hx hy
  rw [hx, hy, h]

/-- The logarithm increment does not depend on the chosen continuous lift. -/
theorem logarithm_increment_independent {T : Type} [TopologicalSpace T] [PreconnectedSpace T]
    (l k : C(T, ℂ)) (he : ∀ x, Complex.exp (l x) = Complex.exp (k x)) (x y : T) :
    l y - l x = k y - k x := by
  have h := logarithm_difference_constant l k he x y
  linear_combination -h

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.SimplexLogarithms
