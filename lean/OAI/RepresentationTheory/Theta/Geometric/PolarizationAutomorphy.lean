import OAI.RepresentationTheory.Theta.Geometric.LatticeSemicharacter
import OAI.RepresentationTheory.Theta.Geometric.Dual.PeriodProjectivity

/-! # Polarization Automorphy -/

namespace OAI.RepresentationTheory.Theta.Geometric.PolarizationAutomorphy

noncomputable section

section

/-! The original integral polarization has a holomorphic factor, with
the normalized Poincare factor as its multiplication defect. -/

open scoped ContDiff

variable {L I V : Type} [AddCommGroup L] [Module ℤ L] [LinearOrder I]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  (b : Module.Basis I ℤ L) (B : LinearMap.BilinForm ℤ L)
  (e : L →+ V) (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)

def polarizationAutomorphy (l : L) (z : V) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * (Complex.I * (LatticeSemicharacter.latticeQuadraticRefinement b B l : ℂ) +
    H (e l) z + H (e l) (e l) / 2))

theorem polarizationAutomorphy_ne_zero (l : L) (z : V) : polarizationAutomorphy b B e H l z ≠ 0 :=
  Complex.exp_ne_zero _

@[simp] theorem polarizationAutomorphy_zero (z : V) : polarizationAutomorphy b B e H 0 z = 1 := by
  simp [polarizationAutomorphy, LatticeSemicharacter.latticeQuadraticRefinement]

theorem polarizationAutomorphy_add (hB : B.IsAlt)
    (hsym : ∀ u v, H v u = star (H u v))
    (hint : ∀ l m, (H (e l) (e m)).im = (B l m : ℝ)) (l m : L) (z : V) :
    polarizationAutomorphy b B e H (l + m) z =
      polarizationAutomorphy b B e H l (z + e m) * polarizationAutomorphy b B e H m z := by
  have hc := congrArg (fun n : ℤ => (n : ℂ)) (LatticeSemicharacter.latticeQuadraticRefinement_add b B hB l m)
  have hs := Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.hermitian_skew H hsym (e l) (e m)
  rw [hint] at hs
  push_cast at hc hs
  simp only [polarizationAutomorphy, map_add, LinearMap.add_apply]
  rw [← Complex.exp_add]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨LatticeSemicharacter.upperLatticeForm b B m l, ?_⟩
  linear_combination (Real.pi : ℂ) * Complex.I * hc - (Real.pi : ℂ) / 2 * hs

theorem polarizationAutomorphy_poincare (hB : B.IsAlt)
    (hsym : ∀ u v, H v u = star (H u v))
    (hint : ∀ l m, (H (e l) (e m)).im = (B l m : ℝ)) (l m : L) (w z : V) :
    polarizationAutomorphy b B e H (l + m) (w + z) =
      polarizationAutomorphy b B e H l w * polarizationAutomorphy b B e H m z *
        Dual.PeriodProjectivity.poincareAutomorphy H (e l) (e m) w z := by
  have hc := congrArg (fun n : ℤ => (n : ℂ)) (LatticeSemicharacter.latticeQuadraticRefinement_add b B hB l m)
  have hs := Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.hermitian_skew H hsym (e l) (e m)
  rw [hint] at hs
  push_cast at hc hs
  simp only [polarizationAutomorphy, Dual.PeriodProjectivity.poincareAutomorphy, map_add, LinearMap.add_apply]
  rw [← Complex.exp_add, ← Complex.exp_add]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨LatticeSemicharacter.upperLatticeForm b B m l, ?_⟩
  linear_combination (Real.pi : ℂ) * Complex.I * hc - (Real.pi : ℂ) / 2 * hs

theorem polarizationAutomorphy_differentiable [FiniteDimensional ℂ V] (l : L) :
    Differentiable ℂ (polarizationAutomorphy b B e H l) :=
  (((H (e l)).toContinuousLinearMap.differentiable.const_add _).add_const _).const_mul _ |>.cexp

theorem polarizationAutomorphy_contDiff [FiniteDimensional ℂ V] (l : L) :
    ContDiff ℂ ∞ (polarizationAutomorphy b B e H l) := by
  have h : ContDiff ℂ ∞ (fun z => Complex.I * (LatticeSemicharacter.latticeQuadraticRefinement b B l : ℂ) +
      H (e l) z + H (e l) (e l) / 2) :=
    (contDiff_const.add (H (e l)).toContinuousLinearMap.contDiff).add contDiff_const
  exact (contDiff_const.mul h).cexp

end

/-! The standard positive metric is compatible with the original
polarization factor on every lattice translate. -/

variable {L I V : Type} [AddCommGroup L] [Module ℤ L] [LinearOrder I]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  (b : Module.Basis I ℤ L) (B : LinearMap.BilinForm ℤ L)
  (e : L →+ V) (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)

theorem polarizationAutomorphy_norm_sq (l : L) (z : V) :
    ‖polarizationAutomorphy b B e H l z‖ ^ 2 =
      Real.exp (Real.pi * (2 * (H (e l) z).re + (H (e l) (e l)).re)) := by
  rw [polarizationAutomorphy, Complex.norm_exp, pow_two, ← Real.exp_add]
  congr 1
  norm_num [Complex.mul_re, Complex.div_re]
  ring

def polarizationMetricWeight (z : V) : ℝ := Real.exp (-Real.pi * (H z z).re)

theorem polarizationMetricWeight_pos (z : V) : 0 < polarizationMetricWeight H z := Real.exp_pos _

theorem polarizationMetricWeight_continuous [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]
    [FiniteDimensional ℂ V] : Continuous (polarizationMetricWeight H) := by
  let : FiniteDimensional ℝ V := FiniteDimensional.trans ℝ ℂ V
  have hh : Continuous (fun z : V => H z z) :=
    (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.hermitianBilin H).continuous.clm_apply continuous_id
  exact Real.continuous_exp.comp (continuous_const.mul (Complex.continuous_re.comp hh))

theorem polarizationMetricWeight_translation (hsym : ∀ u v, H v u = star (H u v)) (l : L) (z : V) :
    ‖polarizationAutomorphy b B e H l z‖ ^ 2 * polarizationMetricWeight H (z + e l) =
      polarizationMetricWeight H z := by
  rw [polarizationAutomorphy_norm_sq, polarizationMetricWeight, polarizationMetricWeight, ← Real.exp_add]
  congr 1
  simp only [map_add, LinearMap.add_apply, Complex.add_re]
  rw [hsym (e l) z]
  simp only [Complex.star_def, Complex.conj_re]
  ring

theorem polarizationMetric_translation (hsym : ∀ u v, H v u = star (H u v))
    (l : L) (z : V) (v : ℂ) :
    polarizationMetricWeight H (z + e l) * ‖polarizationAutomorphy b B e H l z * v‖ ^ 2 =
      polarizationMetricWeight H z * ‖v‖ ^ 2 := by
  rw [norm_mul, mul_pow]
  calc
    _ = (‖polarizationAutomorphy b B e H l z‖ ^ 2 * polarizationMetricWeight H (z + e l)) * ‖v‖ ^ 2 := by ring
    _ = _ := congrArg (fun r => r * ‖v‖ ^ 2) (polarizationMetricWeight_translation b B e H hsym l z)

end

end OAI.RepresentationTheory.Theta.Geometric.PolarizationAutomorphy
