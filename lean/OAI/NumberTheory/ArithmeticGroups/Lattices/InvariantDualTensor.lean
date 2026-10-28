import Mathlib.Algebra.Lie.Killing
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-! # Invariant Dual Tensor -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantDualTensor.Construction

noncomputable section

section

/-! Dual-basis trace identities and the adjoint Casimir identity for
a finite-dimensional Lie algebra with nondegenerate Killing form. -/

open scoped Classical
open _root_.Module LieAlgebra

theorem bilinear_dualBasis_pair_repr
    {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V] [Fintype ι]
    (B : LinearMap.BilinForm k V) (hB : B.Nondegenerate) (b : Basis ι k V) (x : V) (i : ι) :
    B (B.dualBasis hB b i) x = b.repr x i := by
  let : FiniteDimensional k V := b.finiteDimensional_of_finite
  simp only [LinearMap.BilinForm.dualBasis, Basis.map_apply,
    LinearMap.BilinForm.apply_toDual_symm_apply, Basis.coe_dualBasis, Basis.coord_apply]

theorem trace_eq_dualBasis_sum
    {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V] [Fintype ι]
    (B : LinearMap.BilinForm k V) (hB : B.Nondegenerate) (b : Basis ι k V)
    (T : V →ₗ[k] V) : LinearMap.trace k V T = ∑ i, B (B.dualBasis hB b i) (T (b i)) := by
  rw [LinearMap.trace_eq_matrix_trace k b]
  change (∑ i, (LinearMap.toMatrix b b T) i i) = _
  simp only [LinearMap.toMatrix_apply', bilinear_dualBasis_pair_repr]

theorem killing_casimir_apply
    {k L ι : Type*} [Field k] [LieRing L] [LieAlgebra k L] [Fintype ι]
    (hB : (killingForm k L).Nondegenerate) (b : Basis ι k L) (x : L) :
    ∑ i, ⁅b i, ⁅(killingForm k L).dualBasis hB b i, x⁆⁆ = x := by
  let : FiniteDimensional k L := b.finiteDimensional_of_finite
  apply ((killingForm k L).toDual hB).injective
  apply LinearMap.ext
  intro y
  change killingForm k L (∑ i, ⁅b i, ⁅(killingForm k L).dualBasis hB b i, x⁆⁆) y =
    killingForm k L x y
  rw [map_sum, LinearMap.sum_apply]
  calc
    _ = ∑ i, killingForm k L ((killingForm k L).dualBasis hB b i) ⁅x, ⁅y, b i⁆⁆ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [LieModule.traceForm_comm k L L ⁅b i, ⁅(killingForm k L).dualBasis hB b i, x⁆⁆ y,
        ← LieModule.traceForm_apply_lie_apply,
        LieModule.traceForm_comm k L L ⁅y, b i⁆,
        LieModule.traceForm_apply_lie_apply]
    _ = LinearMap.trace k L (ad k L x ∘ₗ ad k L y) :=
      (trace_eq_dualBasis_sum (killingForm k L) hB b (ad k L x ∘ₗ ad k L y)).symm
    _ = _ := (killingForm_apply_apply k L x y).symm

end

/-! The dual-basis tensor of a nondegenerate bilinear form is fixed by
every skew-adjoint endomorphism. -/

open scoped Classical
open _root_.Module

theorem bilinear_dualBasis_skew_sum
    {k V M ι : Type*} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup M] [Module k M] [Fintype ι]
    (B : LinearMap.BilinForm k V) (hB : B.Nondegenerate) (b : Basis ι k V)
    (T : V →ₗ[k] V) (hT : ∀ x y, B (T x) y = -B x (T y))
    (F : V →ₗ[k] V →ₗ[k] M) :
    (∑ i, F (T (b i)) (B.dualBasis hB b i)) +
      (∑ i, F (b i) (T (B.dualBasis hB b i))) = 0 := by
  let d := B.dualBasis hB b
  have hcoeff (i j : ι) : d.repr (T (d i)) j = -b.repr (T (b j)) i := by
    rw [LinearMap.BilinForm.dualBasis_repr_apply, hT, bilinear_dualBasis_pair_repr]
  have hleft (i : ι) : F (T (b i)) (d i) =
      ∑ j, b.repr (T (b i)) j • F (b j) (d i) := by
    conv_lhs => rw [← b.sum_repr (T (b i))]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  have hright (i : ι) : F (b i) (T (d i)) =
      -∑ j, b.repr (T (b j)) i • F (b i) (d j) := by
    conv_lhs => rw [← d.sum_repr (T (d i))]
    simp only [map_sum, map_smul, map_neg, hcoeff, neg_smul, Finset.sum_neg_distrib]
  change (∑ i, F (T (b i)) (d i)) + (∑ i, F (b i) (T (d i))) = 0
  simp only [hleft, hright, Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  exact add_neg_cancel _

theorem killing_dualBasis_lie_sum
    {k L M ι : Type*} [Field k] [LieRing L] [LieAlgebra k L]
    [AddCommGroup M] [Module k M] [Fintype ι]
    (hB : (killingForm k L).Nondegenerate) (b : Basis ι k L)
    (x : L) (F : L →ₗ[k] L →ₗ[k] M) :
    (∑ i, F ⁅x, b i⁆ ((killingForm k L).dualBasis hB b i)) +
      (∑ i, F (b i) ⁅x, (killingForm k L).dualBasis hB b i⁆) = 0 := by
  let : FiniteDimensional k L := b.finiteDimensional_of_finite
  exact bilinear_dualBasis_skew_sum (killingForm k L) hB b (LieAlgebra.ad k L x)
    (fun y z => LieModule.traceForm_apply_lie_apply' k L L x y z) F

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantDualTensor.Construction
