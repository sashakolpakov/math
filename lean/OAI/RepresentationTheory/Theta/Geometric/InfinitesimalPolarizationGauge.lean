import OAI.RepresentationTheory.Theta.Geometric.AdditiveUnitaryRigidity
import OAI.RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter

/-! # Infinitesimal Polarization Gauge -/

namespace OAI.RepresentationTheory.Theta.Geometric.InfinitesimalPolarizationGauge

noncomputable section

/-! A holomorphic infinitesimal translation comparison forces the
imaginary Hermitian pairing with every period to vanish. -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (L : AddSubgroup V) [CompactSpace (V ⧸ L)]
    (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hsym : ∀ u v, H v u = star (H u v))

include hsym

theorem infinitesimalPolarizationGauge_pairing_zero (a : V) (f : V → ℂ)
    (hf : Differentiable ℂ f)
    (htrans : ∀ (l : L) z, f (z + l.val) + (Real.pi : ℂ) * H l.val a = f z)
    (l : L) : (H a l.val).im = 0 := by
  let g := fun z => f z + (Real.pi : ℂ) * H a z
  let χ := fun m : L => (Real.pi : ℂ) * (H a m.val - H m.val a)
  have hg : Differentiable ℂ g := hf.add ((H a).toContinuousLinearMap.differentiable.const_mul _)
  have hχ (m : L) : (χ m).re = 0 := by
    dsimp only [χ]
    rw [hsym a m.val]
    simp [Complex.mul_re]
  have hshift (m : L) (z : V) : g (z + m.val) = g z + χ m := by
    dsimp only [g, χ]
    rw [map_add]
    linear_combination htrans m z
  have hzero := AdditiveUnitaryRigidity.additiveUnitaryAutomorphy_trivial L g χ hχ hg hshift l
  have him := congrArg Complex.im hzero
  dsimp only [χ] at him
  rw [hsym a l.val] at him
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
    Complex.star_def, Complex.conj_im, Complex.zero_im, sub_neg_eq_add, zero_mul, add_zero] at him
  nlinarith [Real.pi_pos]

end

end OAI.RepresentationTheory.Theta.Geometric.InfinitesimalPolarizationGauge
