import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Flat Equalizer Coefficients -/

namespace OAI.RepresentationTheory.Theta.Geometric.FlatEqualizerCoefficients

noncomputable section

/-! The exact coefficient equalizer persists after a flat affine chart
extension of the parameter algebra. -/

open scoped TensorProduct

variable {A R P T : Type*} [CommRing A] [CommRing R] [CommRing P] [CommRing T]
    [Algebra A R] [Algebra A P] [Algebra A T] [Module.Flat A T]

theorem flat_equalizer_coefficient_lift (f g : R →ₐ[A] P)
    (he : Function.Exact (Algebra.linearMap A R) (f.toLinearMap - g.toLinearMap))
    (x : T ⊗[A] R)
    (hx : Algebra.TensorProduct.map (AlgHom.id A T) f x =
      Algebra.TensorProduct.map (AlgHom.id A T) g x) :
    ∃ t : T, (Algebra.TensorProduct.includeLeft : T →ₐ[A] T ⊗[A] R) t = x := by
  have hk : (f.toLinearMap - g.toLinearMap).lTensor T x = 0 := by
    rw [LinearMap.lTensor_sub, LinearMap.sub_apply]
    exact sub_eq_zero.mpr hx
  obtain ⟨z, hz⟩ := (Module.Flat.lTensor_exact T he x).mp hk
  have h (w : T ⊗[A] A) : (Algebra.linearMap A R).lTensor T w =
      (Algebra.TensorProduct.includeLeft : T →ₐ[A] T ⊗[A] R) (TensorProduct.rid A T w) := by
    induction w using TensorProduct.inductionOn with
    | add u v hu hv => simp only [map_add, hu, hv]
    | tmul t a =>
      change t ⊗ₜ[A] (algebraMap A R a) = (a • t) ⊗ₜ[A] (1 : R)
      rw [TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  exact ⟨TensorProduct.rid A T z, (h z).symm.trans hz⟩

theorem flat_equalizer_coefficient_lift_unique
    (hi : Function.Injective (algebraMap A R)) (f g : R →ₐ[A] P)
    (he : Function.Exact (Algebra.linearMap A R) (f.toLinearMap - g.toLinearMap))
    (x : T ⊗[A] R)
    (hx : Algebra.TensorProduct.map (AlgHom.id A T) f x =
      Algebra.TensorProduct.map (AlgHom.id A T) g x) :
    ∃! t : T, (Algebra.TensorProduct.includeLeft : T →ₐ[A] T ⊗[A] R) t = x := by
  obtain ⟨t, ht⟩ := flat_equalizer_coefficient_lift f g he x hx
  exact ⟨t, ht, fun u hu => Algebra.TensorProduct.includeLeft_injective hi (hu.trans ht.symm)⟩

end

end OAI.RepresentationTheory.Theta.Geometric.FlatEqualizerCoefficients
