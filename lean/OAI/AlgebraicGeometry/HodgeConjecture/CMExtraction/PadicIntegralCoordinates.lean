import OAI.RepresentationTheory.Satake.Reduction
import Mathlib.Topology.Algebra.Valued.NormedValued

/-! # Padic Integral Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PadicIntegralCoordinates.Iwasawa

noncomputable section

/-! Identify the valuation ring used in the proved Iwasawa reduction
with the actual p-adic integers, preserving the inclusion into Qq. -/

open scoped Classical

variable (q : ℕ) [Fact q.Prime]

@[instance_reducible] def padicNormRelation : ValuativeRel ℚ_[q] :=
  ValuativeRel.ofValuation (NormedField.valuation (K := ℚ_[q]))

attribute [local instance] padicNormRelation

theorem valuation_integer_iff (x : ℚ_[q]) :
    ValuativeRel.valuation ℚ_[q] x ≤ 1 ↔ ‖x‖ ≤ 1 := by
  rw [← (ValuativeRel.valuation ℚ_[q]).vle_one_iff]
  change NormedField.valuation x ≤ NormedField.valuation (1 : ℚ_[q]) ↔ _
  simp only [NormedField.valuation_apply, nnnorm_one]
  exact NNReal.coe_le_coe.symm

def padicIntegerEquiv : RepresentationTheory.Satake.Reduction.GeneralLinear.O ℚ_[q] ≃+* ℤ_[q] where
  toFun x := ⟨x.val, (valuation_integer_iff q x.val).mp x.property⟩
  invFun x := ⟨x.val, (valuation_integer_iff q x.val).mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem padicIntegerEquiv_coe (x : RepresentationTheory.Satake.Reduction.GeneralLinear.O ℚ_[q]) :
    (padicIntegerEquiv q x : ℚ_[q]) = x.val := rfl

def integralGLMap : Matrix.GeneralLinearGroup (Fin 3) ℤ_[q] →*
    Matrix.GeneralLinearGroup (Fin 3) ℚ_[q] :=
  Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := q))

theorem integralGL_reduction (g : Matrix.GeneralLinearGroup (Fin 3) ℚ_[q]) :
    ∃ U : Matrix.GeneralLinearGroup (Fin 3) ℤ_[q], (g * integralGLMap q U).val.IsUpperTriangular := by
  obtain ⟨U, hU⟩ := RepresentationTheory.Satake.Reduction.GeneralLinear.exists_integral_upperTriangular g
  refine ⟨Matrix.GeneralLinearGroup.map (padicIntegerEquiv q).toRingHom U, ?_⟩
  have he : integralGLMap q (Matrix.GeneralLinearGroup.map (padicIntegerEquiv q).toRingHom U) =
      RepresentationTheory.Satake.Reduction.GeneralLinear.integralMap U := by
    apply Units.ext
    ext i j
    rfl
  rw [he]
  exact hU

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PadicIntegralCoordinates.Iwasawa
