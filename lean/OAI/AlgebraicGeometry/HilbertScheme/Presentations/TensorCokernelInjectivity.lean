import OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorInjectivityExtensions

/-! # Tensor Cokernel Injectivity -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorCokernelInjectivity

noncomputable section

/-! The tensor diagram chase that exchanges the two presentations in
a first flatness obstruction. -/

open TensorProduct

universe u v w t z z' z''
variable {B : Type u} [CommRing B]
variable {K : Type v} [AddCommGroup K] [Module B K]
variable {F : Type w} [AddCommGroup F] [Module B F]
variable {M : Type t} [AddCommGroup M] [Module B M]
variable {P : Type z} [AddCommGroup P] [Module B P]
variable {N : Type z'} [AddCommGroup N] [Module B N]
variable {Q : Type z''} [AddCommGroup Q] [Module B Q]

theorem tensor_cokernel_injective_transfer
    (f : K →ₗ[B] F) (g : F →ₗ[B] M) (i : P →ₗ[B] N) (j : N →ₗ[B] Q)
    (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (hij : Function.Exact i j) (hj : Function.Surjective j)
    (hfN : Function.Injective (f.rTensor N))
    (hiM : Function.Injective (i.lTensor M)) :
    Function.Injective (f.rTensor Q) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective K hj x
  have hz : j.lTensor F (f.rTensor N y) = 0 := by
    rw [← TensorInjectivityExtensions.tensorMap_exchange, hx]
  obtain ⟨w, hw⟩ := (lTensor_exact F hij hj (f.rTensor N y)).mp hz
  have hwg : g.rTensor P w = 0 := by
    apply hiM
    rw [map_zero, ← TensorInjectivityExtensions.tensorMap_exchange, hw]
    change (g.rTensor N).comp (f.rTensor N) y = 0
    rw [← LinearMap.rTensor_comp, hfg.linearMap_comp_eq_zero, LinearMap.rTensor_zero,
      LinearMap.zero_apply]
  obtain ⟨v, hv⟩ := (rTensor_exact P hfg hg w).mp hwg
  have hyv : i.lTensor K v = y := by
    apply hfN
    rw [TensorInjectivityExtensions.tensorMap_exchange, hv, hw]
  rw [← hyv]
  change (j.lTensor K).comp (i.lTensor K) v = 0
  rw [← LinearMap.lTensor_comp, hij.linearMap_comp_eq_zero, LinearMap.lTensor_zero,
    LinearMap.zero_apply]

theorem tensor_cokernel_injective_iff
    (f : K →ₗ[B] F) (g : F →ₗ[B] M) (i : P →ₗ[B] N) (j : N →ₗ[B] Q)
    [Module.Flat B F] [Module.Flat B N]
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (hi : Function.Injective i) (hij : Function.Exact i j) (hj : Function.Surjective j) :
    Function.Injective (f.rTensor Q) ↔ Function.Injective (i.lTensor M) := by
  constructor
  · intro h
    apply (i.lTensor_inj_iff_rTensor_inj M).mpr
    apply tensor_cokernel_injective_transfer i j f g hij hj hfg hg
      (Module.Flat.rTensor_preserves_injective_linearMap i hi)
    exact (f.lTensor_inj_iff_rTensor_inj Q).mpr h
  · exact tensor_cokernel_injective_transfer f g i j hfg hg hij hj
      (Module.Flat.rTensor_preserves_injective_linearMap f hf)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorCokernelInjectivity
