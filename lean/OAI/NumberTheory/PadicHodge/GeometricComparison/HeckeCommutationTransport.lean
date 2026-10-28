import OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeCommutation
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Hecke Commutation Transport -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeCommutationTransport.GeneralizedHecke

noncomputable section

/-! Pairwise commutation transports through actual comparisons and descends along a field extension. -/

open scoped TensorProduct

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

theorem commute_transport (e : V ≃ₗ[K] W) (T₁ T₂ : Module.End K V) (U₁ U₂ : Module.End K W)
    (h₁ : ∀ x, e (T₁ x) = U₁ (e x)) (h₂ : ∀ x, e (T₂ x) = U₂ (e x))
    (h : Commute T₁ T₂) : Commute U₁ U₂ := by
  rw [HeckeCommutation.GeneralizedHecke.eq_conjugate e T₁ U₁ h₁, HeckeCommutation.GeneralizedHecke.eq_conjugate e T₂ U₂ h₂]
  exact h.map e.conjRingEquiv.toMonoidHom

theorem commute_reflect (e : V ≃ₗ[K] W) (T₁ T₂ : Module.End K V) (U₁ U₂ : Module.End K W)
    (h₁ : ∀ x, e (T₁ x) = U₁ (e x)) (h₂ : ∀ x, e (T₂ x) = U₂ (e x))
    (h : Commute U₁ U₂) : Commute T₁ T₂ := by
  change T₁ * T₂ = T₂ * T₁
  apply LinearMap.ext
  intro x
  apply e.injective
  change e (T₁ (T₂ x)) = e (T₂ (T₁ x))
  rw [h₁, h₂, h₂, h₁]
  exact LinearMap.congr_fun h.eq (e x)

theorem baseChange_eq_reflect (L : Type*) [Field L] [Algebra K L]
    (f g : Module.End K V) (h : f.baseChange L = g.baseChange L) : f = g := by
  apply LinearMap.ext
  intro x
  have hx : (1 : L) ⊗ₜ[K] (f x - g x) = 0 := by
    rw [TensorProduct.tmul_sub]
    exact sub_eq_zero.mpr (LinearMap.congr_fun h ((1 : L) ⊗ₜ[K] x))
  exact sub_eq_zero.mp ((Module.FaithfullyFlat.one_tmul_eq_zero_iff (R := K) V (A := L) (f x - g x)).mp hx)

theorem commute_baseChange_reflect (L : Type*) [Field L] [Algebra K L]
    (f g : Module.End K V) (h : Commute (f.baseChange L) (g.baseChange L)) : Commute f g := by
  change f * g = g * f
  apply baseChange_eq_reflect L
  exact ((Module.End.baseChangeHom K L V).map_mul f g).trans
    (h.eq.trans ((Module.End.baseChangeHom K L V).map_mul g f).symm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeCommutationTransport.GeneralizedHecke
