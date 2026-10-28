import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexChartDerivative
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Topology.Algebra.Group.Basic

/-! # Centered Chart Transition -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.CenteredChartTransition.Cycles

noncomputable section

/-!
# Centering actual complex chart transitions

Translations before and after the actual chart transition give an open
partial homeomorphism fixing zero. Its source remains explicit, so a small
ball in that source can be used for the relative-homology comparison.
-/

open scoped _root_.Manifold

variable {E : Type} [NormedAddCommGroup E]
variable {M : Type} [TopologicalSpace M]
variable (e e' : OpenPartialHomeomorph M E)

/-- The actual transition homeomorphism in centered coordinates. -/
def centeredComplexChartChange (z : E) : OpenPartialHomeomorph E E :=
  ((Homeomorph.addRight z).transOpenPartialHomeomorph (e.symm.trans e')).transHomeomorph
    (Homeomorph.addRight (-(e.symm.trans e') z))

@[simp]
theorem centeredComplexChartChange_apply (z v : E) :
    centeredComplexChartChange e e' z v = ComplexChartDerivative.Cycles.centeredComplexChartTransition e e' z v := by
  change (e.symm.trans e') (v + z) + -(e.symm.trans e') z =
    (e.symm.trans e') (v + z) - (e.symm.trans e') z
  exact (sub_eq_add_neg _ _).symm

/-- The actual centered domain is the translate of the original domain. -/
theorem centeredComplexChartChange_source (z : E) :
    (centeredComplexChartChange e e' z).source =
      (fun v : E => v + z) ⁻¹' (e.symm.trans e').source := rfl

theorem centeredComplexChartChange_zero_mem (z : E)
    (hz : z ∈ (e.symm.trans e').source) :
    (0 : E) ∈ (centeredComplexChartChange e e' z).source := by
  simpa only [centeredComplexChartChange_source, Set.mem_preimage, zero_add] using hz

@[simp]
theorem centeredComplexChartChange_zero (z : E) :
    centeredComplexChartChange e e' z 0 = 0 := by
  rw [centeredComplexChartChange_apply, ComplexChartDerivative.Cycles.centeredComplexChartTransition_zero]

/-- The inverse centered transition has the corresponding translated formula. -/
theorem centeredComplexChartChange_symm_apply (z v : E) :
    (centeredComplexChartChange e e' z).symm v =
      (e.symm.trans e').symm (v + (e.symm.trans e') z) - z := by
  change (e.symm.trans e').symm (v + -(-(e.symm.trans e') z)) + -z = _
  simp only [neg_neg, sub_eq_add_neg]

/-- A chart translated so that a specified source point has coordinate zero. -/
def centeredLocalChart (x : M) : OpenPartialHomeomorph M E :=
  e.transHomeomorph (Homeomorph.addRight (-(e x)))

@[simp]
theorem centeredLocalChart_apply (x u : M) :
    centeredLocalChart e x u = e u - e x :=
  (sub_eq_add_neg _ _).symm

@[simp]
theorem centeredLocalChart_source (x : M) : (centeredLocalChart e x).source = e.source := rfl

theorem centeredLocalChart_target (x : M) :
    (centeredLocalChart e x).target = (fun v : E => v + e x) ⁻¹' e.target := by
  ext v
  change (v + -(-e x) ∈ e.target) ↔ (v + e x ∈ e.target)
  rw [neg_neg]

@[simp]
theorem centeredLocalChart_symm_apply (x : M) (v : E) :
    (centeredLocalChart e x).symm v = e.symm (v + e x) := by
  change e.symm (v + -(-e x)) = _
  rw [neg_neg]

@[simp]
theorem centeredLocalChart_at_point (x : M) : centeredLocalChart e x x = 0 := by
  rw [centeredLocalChart_apply, sub_self]

/-- The transition between two centered charts is the actual centered
transition previously used for its derivative. -/
theorem centeredLocalChart_transition (x : M) (hx : x ∈ e.source) :
    (centeredLocalChart e x).symm.trans (centeredLocalChart e' x) =
      centeredComplexChartChange e e' (e x) := by
  apply OpenPartialHomeomorph.ext
  · intro v
    change centeredLocalChart e' x ((centeredLocalChart e x).symm v) = _
    rw [centeredLocalChart_apply, centeredLocalChart_symm_apply,
      centeredComplexChartChange_apply]
    change e' (e.symm (v + e x)) - e' x =
      e' (e.symm (v + e x)) - e' (e.symm (e x))
    rw [e.left_inv hx]
  · intro v
    change centeredLocalChart e x ((centeredLocalChart e' x).symm v) = _
    rw [centeredLocalChart_apply, centeredLocalChart_symm_apply,
      centeredComplexChartChange_symm_apply]
    change e (e'.symm (v + e' x)) - e x =
      e (e'.symm (v + e' (e.symm (e x)))) - e x
    rw [e.left_inv hx]
  · ext v
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      centeredLocalChart_target, centeredLocalChart_source,
      centeredComplexChartChange_source, Set.mem_inter_iff, Set.mem_preimage,
      centeredLocalChart_symm_apply]

variable [NormedSpace ℂ E] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 1 M]
variable (he : e ∈ atlas E M) (he' : e' ∈ atlas E M)

/-- The actual centered partial homeomorphism has the computed invertible
complex derivative at zero. -/
theorem centeredComplexChartChange_hasFDerivAt (z : E)
    (hz : z ∈ (e.symm.trans e').source) :
    HasFDerivAt (centeredComplexChartChange e e' z)
      (ComplexChartDerivative.Cycles.complexChartTransitionDerivative e e' he he' z hz : E →L[ℂ] E) 0 := by
  have hfun : (centeredComplexChartChange e e' z : E → E) =
      ComplexChartDerivative.Cycles.centeredComplexChartTransition e e' z :=
    funext (centeredComplexChartChange_apply e e' z)
  rw [hfun]
  exact ComplexChartDerivative.Cycles.centeredComplexChartTransition_hasFDerivAt e e' he he' z hz

variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- The same derivative restricted to real scalars, as used by the actual
punctured-ball homotopy. -/
theorem centeredComplexChartChange_hasRealFDerivAt (z : E)
    (hz : z ∈ (e.symm.trans e').source) :
    HasFDerivAt (centeredComplexChartChange e e' z)
      ((ComplexChartDerivative.Cycles.complexChartTransitionDerivative e e' he he' z hz).restrictScalars ℝ : E →L[ℝ] E)
      0 :=
  (centeredComplexChartChange_hasFDerivAt e e' he he' z hz).restrictScalars ℝ

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.CenteredChartTransition.Cycles
