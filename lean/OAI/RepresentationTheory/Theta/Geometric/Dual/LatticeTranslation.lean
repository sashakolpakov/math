import OAI.RepresentationTheory.Theta.Geometric.PolarizationAutomorphy
import OAI.RepresentationTheory.Theta.Geometric.AutomorphicFamilies

/-! # Lattice Translation -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Translation by a polarization-kernel lift preserves theta sections
after the explicit exponential gauge. -/

open scoped ContDiff

section

variable {L I V : Type} [AddCommGroup L] [Module ℤ L] [LinearOrder I]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  (b : Module.Basis I ℤ L) (B : LinearMap.BilinForm ℤ L)
  (e : L →+ V) (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)

def Dual.LatticeTranslation.polarizationTranslationGauge (a z : V) : ℂ := Complex.exp (-(Real.pi : ℂ) * H a z)

theorem Dual.LatticeTranslation.polarizationTranslationGauge_ne_zero (a z : V) : Dual.LatticeTranslation.polarizationTranslationGauge H a z ≠ 0 :=
  Complex.exp_ne_zero _

theorem Dual.LatticeTranslation.polarizationTranslationGauge_contDiff [FiniteDimensional ℂ V] (a : V) :
    ContDiff ℂ ∞ (Dual.LatticeTranslation.polarizationTranslationGauge H a) :=
  (contDiff_const.mul (H a).toContinuousLinearMap.contDiff).cexp

theorem Dual.LatticeTranslation.polarizationTranslationGauge_automorphy
    (hsym : ∀ u v, H v u = star (H u v)) (a : V) (l : L)
    (hint : ∃ m : ℤ, (H a (e l)).im = (m : ℝ)) (z : V) :
    Dual.LatticeTranslation.polarizationTranslationGauge H a (z + e l) * PolarizationAutomorphy.polarizationAutomorphy b B e H l (z + a) =
      PolarizationAutomorphy.polarizationAutomorphy b B e H l z * Dual.LatticeTranslation.polarizationTranslationGauge H a z := by
  obtain ⟨m, hm⟩ := hint
  have hs := Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.hermitian_skew H hsym a (e l)
  rw [hm] at hs
  simp only [Dual.LatticeTranslation.polarizationTranslationGauge, PolarizationAutomorphy.polarizationAutomorphy, map_add]
  rw [← Complex.exp_add, ← Complex.exp_add]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨-m, ?_⟩
  push_cast at hs ⊢
  linear_combination -(Real.pi : ℂ) * hs

end

variable {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor} {n : ℕ}

def AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.translateByGauge (a : Φ.space) (c : Φ.space → ℂ) (hc : ContDiff ℂ 1 c)
    (htrans : ∀ (l : Φ.periodIntegerLattice) z,
      c (z + l.val) * J.value l (z + a) = J.value l z * c z)
    (s : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J n) : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J n where
  toFun z := c z ^ n * s (z + a)
  regular := (hc.pow n).mul (s.regular.comp (contDiff_id.add contDiff_const))
  translates l z := by
    rw [show (z + l.val) + a = (z + a) + l.val by abel, s.translates,
      ← mul_assoc, ← mul_pow, htrans, mul_pow, mul_assoc]

@[simp]
theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.translateByGauge_apply (a : Φ.space) (c : Φ.space → ℂ) (hc : ContDiff ℂ 1 c)
    (htrans : ∀ (l : Φ.periodIntegerLattice) z,
      c (z + l.val) * J.value l (z + a) = J.value l z * c z)
    (s : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J n) (z : Φ.space) :
    AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.translateByGauge a c hc htrans s z = c z ^ n * s (z + a) := rfl

end

end OAI.RepresentationTheory.Theta.Geometric
