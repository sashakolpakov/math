import OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeSummandStability
import OAI.NumberTheory.PadicHodge.GeometricComparison.WeakAdmissibilityTransport

/-! # Hecke Commutation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeCommutation.GeneralizedHecke

noncomputable section

/-! Commutation survives the actual comparison, rational weighted sums, and scalar extension. -/

open scoped TensorProduct

variable {K V W I : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

theorem eq_conjugate (e : V ≃ₗ[K] W) (T : Module.End K V) (U : Module.End K W)
    (h : ∀ x, e (T x) = U (e x)) : U = e.conj T := by
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  simpa only [LinearEquiv.conj_apply_apply, e.symm_apply_apply] using (h x).symm

theorem conjugate_commutes (e : V ≃ₗ[K] W) (T : Module.End K V) (U : Module.End K W)
    (φ : V ≃ₗ[K] V) (hU : ∀ x, e (T x) = U (e x)) (h : Commute T φ.toLinearMap) :
    Commute U (WeakAdmissibilityTransport.FiltrationTransport.conjugateEquiv e φ).toLinearMap := by
  rw [WeakAdmissibilityTransport.FiltrationTransport.conjugateEquiv_toLinearMap, eq_conjugate e T U hU]
  exact h.map e.conjRingEquiv.toMonoidHom

theorem commutes_weighted_sum {A : Type*} [Zero A] (s : I →₀ A) (c : A → K)
    (T : I → Module.End K V) (φ : Module.End K V) (h : ∀ i, Commute (T i) φ) :
    Commute (s.sum (fun i a => c a • T i)) φ := by
  classical
  change (s.sum (fun i a => c a • T i)) * φ = φ * (s.sum (fun i a => c a • T i))
  simp only [Finsupp.sum, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(h i).eq]

theorem commutes_baseChange (L : Type*) [Field L] [Algebra K L]
    (T φ : Module.End K V) (h : Commute T φ) : Commute (T.baseChange L) (φ.baseChange L) :=
  h.map (Module.End.baseChangeHom K L V).toMonoidHom

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeCommutation.GeneralizedHecke
