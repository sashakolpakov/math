import OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.BalanceIdeal
import OAI.AlgebraicGeometry.CycleClass.Thom.UnramifiedDiagonalLocalization
import OAI.AlgebraicGeometry.CycleClass.Thom.LocalizedCompositeKernel

/-! # Relative Diagonal Ideal -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Local.RelativeDiagonalIdeal.Constructions

noncomputable section

/-! At a point on the diagonal, an unramified intermediate algebra
allows the full diagonal ideal to be replaced by the balancing ideal.
This is equality of ideals in the actual localized tensor algebra. -/

open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.BalanceIdeal.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (k P R : Type u) [CommRing k] [CommRing P] [CommRing R]
  [Algebra k P] [Algebra k R] [Algebra P R] [IsScalarTower k P R]

theorem multiplication_comp_balance :
    (Algebra.TensorProduct.lmul' P (S := R)).toRingHom.comp (Tensor.BalanceIdeal.Constructions.balanceMap k P R).toRingHom =
      (Algebra.TensorProduct.lmul' k (S := R)).toRingHom := by
  have h : (Algebra.TensorProduct.lmul'' P (S := R)).comp (Tensor.BalanceIdeal.Constructions.balanceMap k P R) =
      Algebra.TensorProduct.lmul'' k (S := R) := by
    ext x
    rfl
  exact congrArg AlgHom.toRingHom h

variable [Algebra.FormallyUnramified P R] [IsNoetherianRing (R ⊗[P] R)]

theorem localized_diagonal_eq_balance (q : PrimeSpectrum R) :
    (KaehlerDifferential.ideal k R).map
      (algebraMap (R ⊗[k] R)
        (Localization.AtPrime (q.asIdeal.comap (Algebra.TensorProduct.lmul' k).toRingHom))) =
    (RingHom.ker (Tensor.BalanceIdeal.Constructions.balanceMap k P R).toRingHom).map
      (algebraMap (R ⊗[k] R)
        (Localization.AtPrime (q.asIdeal.comap (Algebra.TensorProduct.lmul' k).toRingHom))) := by
  have hp : (q.asIdeal.comap (Algebra.TensorProduct.lmul' P).toRingHom).comap
      (Tensor.BalanceIdeal.Constructions.balanceMap k P R).toRingHom = q.asIdeal.comap (Algebra.TensorProduct.lmul' k).toRingHom := by
    change q.asIdeal.comap ((Algebra.TensorProduct.lmul' P).toRingHom.comp
      (Tensor.BalanceIdeal.Constructions.balanceMap k P R).toRingHom) = _
    rw [multiplication_comp_balance]
  have h := LocalizedCompositeKernel.Constructions.kernel_comp_map_eq_at (R ⊗[k] R) (R ⊗[P] R) R
    (Tensor.BalanceIdeal.Constructions.balanceMap k P R).toRingHom (Algebra.TensorProduct.lmul' P).toRingHom
    (Algebra.TensorProduct.mapOfCompatibleSMul_surjective P k R R R)
    (PrimeSpectrum.comap (Algebra.TensorProduct.lmul' P).toRingHom q)
    (PrimeSpectrum.comap (Algebra.TensorProduct.lmul' k).toRingHom q) hp
    (UnramifiedDiagonalLocalization.Constructions.local_diagonal_eq_bot P R q)
  rw [multiplication_comp_balance] at h
  exact h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Local.RelativeDiagonalIdeal.Constructions
