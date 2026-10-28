import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FiniteKernelDivision
import Mathlib.RingTheory.Flat.TorsionFree

/-! # Isogeny -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Isogeny.Tate

noncomputable section

/-! Rational Tate maps of surjective finite-kernel homomorphisms are
isomorphisms. Integral Tate vectors embed into the rational Tate space. -/

open scoped TensorProduct

universe u
variable (q : ℕ) [Fact q.Prime] {H H' H'' : Type u}
  [AddCommGroup H] [AddCommGroup H'] [AddCommGroup H'']

abbrev RationalModule (H : Type u) [AddCommGroup H] := ℚ_[q] ⊗[ℤ_[q]] Add.Tate.Module (H := H) q

def rationalMap (f : H →+ H') : RationalModule q H →ₗ[ℚ_[q]] RationalModule q H' :=
  (Add.Tate.map q f).baseChange ℚ_[q]

theorem rationalMap_id : rationalMap q (AddMonoidHom.id H) = LinearMap.id := by
  rw [rationalMap, Functor.Tate.map_id, LinearMap.baseChange_id]

theorem rationalMap_comp (f : H →+ H') (g : H' →+ H'') :
    rationalMap q (g.comp f) = (rationalMap q g).comp (rationalMap q f) := by
  rw [rationalMap, Functor.Tate.map_comp, LinearMap.baseChange_comp]
  rfl

theorem rationalMap_nsmul (n : ℕ) (f : H →+ H') :
    rationalMap q (n • f) = n • rationalMap q f := by
  change (LinearMap.baseChangeHom ℤ_[q] ℚ_[q] _ _) (Add.Tate.map q (n • f)) = _
  rw [Functor.Tate.map_nsmul, _root_.map_nsmul]
  rfl

theorem integralEmbedding_injective :
    Function.Injective (TensorProduct.mk ℤ_[q] ℚ_[q] (Add.Tate.Module (H := H) q) 1) :=
  _root_.Module.Flat.tensorProduct_mk_injective ℤ_[q] (Add.Tate.Module (H := H) q) ℚ_[q]

def rationalEquivOfFiniteKernel (f : H →+ H') (hf : Function.Surjective f) [Finite f.ker] :
    RationalModule q H ≃ₗ[ℚ_[q]] RationalModule q H' := by
  let g := FiniteKernelDivision.FiniteKernel.inverseMultiple f hf
  let m := Nat.card f.ker
  have hm : (m : ℚ_[q]) ≠ 0 := Nat.cast_ne_zero.mpr (FiniteKernelDivision.FiniteKernel.card_ne_zero f)
  have hgf : (rationalMap q g).comp (rationalMap q f) = m • LinearMap.id := by
    rw [← rationalMap_comp, FiniteKernelDivision.FiniteKernel.inverseMultiple_comp, rationalMap_nsmul, rationalMap_id]
  have hfg : (rationalMap q f).comp (rationalMap q g) = m • LinearMap.id := by
    rw [← rationalMap_comp, FiniteKernelDivision.FiniteKernel.comp_inverseMultiple, rationalMap_nsmul, rationalMap_id]
  refine LinearEquiv.ofLinearMap (rationalMap q f) ((m : ℚ_[q])⁻¹ • rationalMap q g) ?_ ?_
  · rw [LinearMap.comp_smul, hfg, ← Nat.cast_smul_eq_nsmul ℚ_[q], smul_smul,
      inv_mul_cancel₀ hm, one_smul]
  · rw [LinearMap.smul_comp, hgf, ← Nat.cast_smul_eq_nsmul ℚ_[q], smul_smul,
      inv_mul_cancel₀ hm, one_smul]

theorem rationalEquivOfFiniteKernel_toLinearMap (f : H →+ H')
    (hf : Function.Surjective f) [Finite f.ker] :
    (rationalEquivOfFiniteKernel q f hf).toLinearMap = rationalMap q f := rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Isogeny.Tate
