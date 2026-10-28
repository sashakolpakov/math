import OAI.AlgebraicGeometry.PELModuli.IntegralModel.QuotientUnitKernel

/-! # Nilpotent Module Layer -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.NilpotentModuleLayer

noncomputable section

/-! Passing to the kernel of restriction to a closed subscheme lowers
the annihilating ideal exponent by one, on actual affine modules. -/

open _root_.CategoryTheory

universe u

theorem ideal_power_annihilates_ideal_multiple
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (I : Ideal R) (n : ℕ)
    (h : I ^ (n + 1) ≤ Module.annihilator R M) :
    I ^ n ≤ Module.annihilator R ↥(I • (⊤ : Submodule R M)) := by
  intro r hr
  apply Module.mem_annihilator.mpr
  intro x
  apply Subtype.ext
  change r • x.val = 0
  refine Submodule.smul_induction_on x.property ?_ ?_
  · intro a ha m _
    rw [← mul_smul]
    apply Module.mem_annihilator.mp (h ?_) m
    rw [pow_succ]
    exact Ideal.mul_mem_mul hr ha
  · intro a b ha hb
    rw [smul_add, ha, hb, zero_add]

theorem quotientModule_unit_kernel_power_annihilates
    {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (hf : Function.Surjective f) (M : ModuleCat.{u} R) (n : ℕ)
    (h : (RingHom.ker f) ^ (n + 1) ≤ Module.annihilator R M) :
    (RingHom.ker f) ^ n ≤ Module.annihilator R
      ((ModuleCat.extendRestrictScalarsAdj f).unit.app M).hom.ker := by
  rw [QuotientUnitKernel.quotientModule_unit_kernel f hf M]
  exact ideal_power_annihilates_ideal_multiple M (RingHom.ker f) n h

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.NilpotentModuleLayer
