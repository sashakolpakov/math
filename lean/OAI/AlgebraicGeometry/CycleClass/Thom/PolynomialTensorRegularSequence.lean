import OAI.AlgebraicGeometry.CycleClass.Thom.PolynomialShiftedRegularSequence
import OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.ProductRightBaseChange
import OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.BalanceIdeal
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! # Polynomial Tensor Regular Sequence -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.PolynomialTensorRegularSequence.Constructions

noncomputable section

/-! When an algebra is flat over polynomial coordinates, the
differences between the left and right coordinate values form a
regular sequence in its tensor square. -/

open scoped TensorProduct
open RingTheory.Sequence _root_.MvPolynomial

open OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.BalanceIdeal.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.ProductRightBaseChange.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R] {σ : Type}
  [Algebra (MvPolynomial σ k) R] [IsScalarTower k (MvPolynomial σ k) R]

def sourceDifference (i : σ) : R ⊗[k] MvPolynomial σ k :=
  algebraMap (MvPolynomial σ k) R (X i) ⊗ₜ[k] 1 - 1 ⊗ₜ[k] X i

omit [IsScalarTower k (MvPolynomial σ k) R] in
theorem source_weaklyRegular (ls : List σ) (hl : ls.Nodup) :
    IsWeaklyRegular (R ⊗[k] MvPolynomial σ k) (ls.map (sourceDifference k R)) := by
  let c : σ → R := fun i => algebraMap (MvPolynomial σ k) R (X i)
  let e := (MvPolynomial.algebraTensorAlgEquiv k R (σ := σ)).symm
  apply (e.toAddEquiv.isWeaklyRegular_congr
    (as := ls.map (fun i => C (c i) - X i)) (bs := ls.map (sourceDifference k R)) ?_).mp
      (PolynomialShiftedRegularSequence.Constructions.reflected_weaklyRegular R c ls hl)
  apply List.forall₂_map_left_iff.mpr
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  intro i _ x
  change e ((C (c i) - X i) * x) = sourceDifference k R i * e x
  rw [map_mul, map_sub]
  congr 1
  change e (algebraMap R (MvPolynomial σ R) (c i)) - e (X i) = _
  rw [AlgEquiv.commutes]
  exact congrArg₂ (· - ·) rfl (MvPolynomial.algebraTensorAlgEquiv_symm_X k R i)

attribute [local instance] Tensor.ProductRightBaseChange.Constructions.baseChangeAlgebra

theorem difference_weaklyRegular [Module.Flat (MvPolynomial σ k) R]
    (ls : List σ) (hl : ls.Nodup) :
    IsWeaklyRegular (R ⊗[k] R)
      (ls.map (fun i => Tensor.BalanceIdeal.Constructions.difference k (MvPolynomial σ k) R (X i))) := by
  let : Module.Flat (R ⊗[k] MvPolynomial σ k) (R ⊗[k] R) :=
    Tensor.ProductRightBaseChange.Constructions.flat k R (MvPolynomial σ k) R
  have h := (source_weaklyRegular k R ls hl).of_flat (S := R ⊗[k] R)
  have hm : ∀ i : σ, algebraMap (R ⊗[k] MvPolynomial σ k) (R ⊗[k] R)
      (sourceDifference k R i) = Tensor.BalanceIdeal.Constructions.difference k (MvPolynomial σ k) R (X i) := by
    intro i
    change Tensor.ProductRightBaseChange.Constructions.baseChangeMap k R (MvPolynomial σ k) R (sourceDifference k R i) = _
    simp only [sourceDifference, Tensor.ProductRightBaseChange.Constructions.baseChangeMap, map_sub, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, map_one, IsScalarTower.toAlgHom_apply, Tensor.BalanceIdeal.Constructions.difference]
  simpa only [List.map_map, Function.comp_def, hm] using h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.PolynomialTensorRegularSequence.Constructions
