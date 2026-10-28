import OAI.RepresentationTheory.Theta.Geometric.Dual.LatticeTranslation
import OAI.RepresentationTheory.Theta.Geometric.UnitaryAutomorphyRigidity

/-! # Hermitian Translation Character -/

namespace OAI.RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter

noncomputable section

section

/-! The unitary character of a translated polarization, and its exact
integrality criterion. -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)

def hermitianTranslationCharacter (a l : V) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * (H a l - H l a))

theorem hermitianTranslationCharacter_unitary
    (hsym : ∀ u v, H v u = star (H u v)) (a l : V) :
    ‖hermitianTranslationCharacter H a l‖ = 1 := by
  rw [hermitianTranslationCharacter, Complex.norm_exp, hsym a l]
  simp [Complex.mul_re]

theorem hermitianTranslationCharacter_eq_one_iff
    (hsym : ∀ u v, H v u = star (H u v)) (a l : V) :
    hermitianTranslationCharacter H a l = 1 ↔ ∃ m : ℤ, (H a l).im = (m : ℝ) := by
  rw [hermitianTranslationCharacter, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have h := congrArg Complex.im hm
    rw [hsym a l] at h
    simp only [Complex.mul_im, Complex.mul_re, Complex.sub_im, Complex.star_def, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im,
      Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat,
      zero_mul, mul_zero, add_zero, mul_one, sub_neg_eq_add] at h
    nlinarith [Real.pi_pos]
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have h := Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.hermitian_skew H hsym a l
    rw [hm] at h
    push_cast at h
    linear_combination (Real.pi : ℂ) * h

end

/-! An arbitrary holomorphic translation comparison yields a holomorphic
function with the polarization's unitary translation character. -/

variable {L I V : Type} [AddCommGroup L] [Module ℤ L] [LinearOrder I]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  (b : Module.Basis I ℤ L) (B : LinearMap.BilinForm ℤ L)
  (e : L →+ V) (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)

theorem polarizationAutomorphy_translate (l : L) (a z : V) :
    PolarizationAutomorphy.polarizationAutomorphy b B e H l (z + a) =
      PolarizationAutomorphy.polarizationAutomorphy b B e H l z * Complex.exp ((Real.pi : ℂ) * H (e l) a) := by
  simp only [PolarizationAutomorphy.polarizationAutomorphy, map_add]
  rw [← Complex.exp_add]
  congr 1
  ring

def adjustedTranslationGauge (a : V) (c : V → ℂ) (z : V) : ℂ :=
  c z * Complex.exp ((Real.pi : ℂ) * H a z)

theorem adjustedTranslationGauge_differentiable [FiniteDimensional ℂ V]
    (a : V) (c : V → ℂ) (hc : Differentiable ℂ c) :
    Differentiable ℂ (adjustedTranslationGauge H a c) :=
  hc.mul (((H a).toContinuousLinearMap.differentiable.const_mul _).cexp)

theorem translationGauge_translation (a : V) (c : V → ℂ)
    (hc : ∀ (l : L) z, c (z + e l) * PolarizationAutomorphy.polarizationAutomorphy b B e H l (z + a) =
      PolarizationAutomorphy.polarizationAutomorphy b B e H l z * c z) (l : L) (z : V) :
    c (z + e l) * Complex.exp ((Real.pi : ℂ) * H (e l) a) = c z := by
  apply mul_left_cancel₀ (PolarizationAutomorphy.polarizationAutomorphy_ne_zero b B e H l z)
  have Hc := hc l z
  rw [polarizationAutomorphy_translate] at Hc
  exact (by ac_rfl : PolarizationAutomorphy.polarizationAutomorphy b B e H l z *
    (c (z + e l) * Complex.exp ((Real.pi : ℂ) * H (e l) a)) =
      c (z + e l) * (PolarizationAutomorphy.polarizationAutomorphy b B e H l z * Complex.exp ((Real.pi : ℂ) * H (e l) a))).trans Hc

theorem adjustedTranslationGauge_translates (a : V) (c : V → ℂ)
    (hc : ∀ (l : L) z, c (z + e l) * PolarizationAutomorphy.polarizationAutomorphy b B e H l (z + a) =
      PolarizationAutomorphy.polarizationAutomorphy b B e H l z * c z) (l : L) (z : V) :
    adjustedTranslationGauge H a c (z + e l) =
      hermitianTranslationCharacter H a (e l) * adjustedTranslationGauge H a c z := by
  have he : Complex.exp ((Real.pi : ℂ) * H a (z + e l)) =
      Complex.exp ((Real.pi : ℂ) * H (e l) a) * hermitianTranslationCharacter H a (e l) *
        Complex.exp ((Real.pi : ℂ) * H a z) := by
    simp only [hermitianTranslationCharacter, ← Complex.exp_add, map_add]
    congr 1
    ring
  unfold adjustedTranslationGauge
  rw [he]
  calc
    _ = hermitianTranslationCharacter H a (e l) *
        (c (z + e l) * Complex.exp ((Real.pi : ℂ) * H (e l) a)) *
        Complex.exp ((Real.pi : ℂ) * H a z) := by ac_rfl
    _ = _ := by rw [translationGauge_translation b B e H a c hc, mul_assoc]

end

end OAI.RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter
