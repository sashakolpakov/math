import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.AdelicTestCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction

/-! # Trace Phase Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TracePhaseCoordinates.CM

noncomputable section

/-! Restriction of scalars in a genuine symplectic polarization uses an
integral basis for positions and its trace-dual basis for momenta. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.AdelicTestCoordinates.CM

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

def momentum : (Fin N → F) ≃ₗ[ℚ] (Finite.AdelicTestCoordinates.CM.Index F N → ℚ) :=
  (LinearEquiv.piCongrRight (fun _ : Fin N => (integralBasis F).traceDual.equivFun)).trans
    (LinearEquiv.curry ℚ ℚ (Fin N) (Module.Free.ChooseBasisIndex ℤ (𝓞 F))).symm

theorem scalar_pairing (x y : F) :
    ∑ i : Module.Free.ChooseBasisIndex ℤ (𝓞 F),
      (integralBasis F).repr x i * (integralBasis F).traceDual.repr y i =
        Algebra.trace ℚ F (x * y) := by
  have h := congrArg (Algebra.traceForm ℚ F y) ((integralBasis F).sum_repr x)
  simp only [map_sum, map_smul, smul_eq_mul] at h
  simp only [Module.Basis.traceDual_repr_apply]
  exact h.trans (by rw [Algebra.traceForm_apply, mul_comm])

theorem position_momentum_pairing (x y : Fin N → F) :
    ∑ i, CMExtraction.IntegralAdelicCoordinates.TestTransport.integralPositionCoordinates F (Fin N) x i * momentum F N y i =
      Algebra.trace ℚ F (∑ j, x j * y j) := by
  change (∑ i : Finite.AdelicTestCoordinates.CM.Index F N,
    (integralBasis F).repr (x i.1) i.2 * (integralBasis F).traceDual.repr (y i.1) i.2) = _
  rw [Fintype.sum_prod_type, map_sum]
  exact Finset.sum_congr rfl (fun j _ => scalar_pairing F (x j) (y j))

def phase : ((Fin N → F) × (Fin N → F)) ≃ₗ[ℚ]
    ((Finite.AdelicTestCoordinates.CM.Index F N → ℚ) × (Finite.AdelicTestCoordinates.CM.Index F N → ℚ)) :=
  (CMExtraction.IntegralAdelicCoordinates.TestTransport.integralPositionCoordinates F (Fin N)).prodCongr (momentum F N)

theorem phase_pairing (x y : (Fin N → F) × (Fin N → F)) :
    (∑ i, ((phase F N x).1 i * (phase F N y).2 i -
      (phase F N y).1 i * (phase F N x).2 i)) =
        Algebra.trace ℚ F (∑ j, (x.1 j * y.2 j - y.1 j * x.2 j)) := by
  change (∑ i, (CMExtraction.IntegralAdelicCoordinates.TestTransport.integralPositionCoordinates F (Fin N) x.1 i * momentum F N y.2 i -
    CMExtraction.IntegralAdelicCoordinates.TestTransport.integralPositionCoordinates F (Fin N) y.1 i * momentum F N x.2 i)) = _
  rw [Finset.sum_sub_distrib, position_momentum_pairing, position_momentum_pairing,
    ← map_sub, ← Finset.sum_sub_distrib]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TracePhaseCoordinates.CM
